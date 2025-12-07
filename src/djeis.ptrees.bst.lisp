(defpackage #:djeis.ptrees.bst.impl
  (:use #:cl #:djeis.ptrees.bst)
  (:import-from #:djeis.ptrees.common
                #:make-box #:box-val)
  (:local-nicknames (#:a #:alexandria) (#:s #:serapeum)))

(in-package #:djeis.ptrees.bst.impl)

(defstruct base-tree
  root
  cmp)

(defstruct (ptree (:include base-tree))
  transient-for)

(defstruct (ttree (:include base-tree))
  transient-box
  persistent!
  joiner)

(defstruct node
  transient-box
  key
  value
  left
  right)

(defun transient-for (tree)
  (check-type tree ptree)
  (funcall (ptree-transient-for tree) tree))
(defun persistent! (tree)
  (check-type tree ttree)
  (assert (eq (bt:current-thread) (box-val (ttree-transient-box tree))))
  (funcall (ttree-persistent! tree) tree))

(defun %inorder (f node)
  (when node
    (%inorder f (node-left node))
    (funcall f (node-key node) (node-value node))
    (%inorder f (node-right node))))

(defun mapkv (f tree)
  (check-type tree base-tree)
  (let ((l))
    (%inorder (lambda (k v) (push (funcall f k v) l)) (base-tree-root tree))
    (nreverse l)))

(defun reducekv (f init tree)
  (check-type tree base-tree)
  (%inorder (lambda (k v) (setf init (funcall f init k v))) (base-tree-root tree))
  init)

(defun lookup (tree key)
  (check-type tree base-tree)
  (let ((cmpfn (base-tree-cmp tree)))
    (labels ((recursor (node)
               (if node
                   (let ((nkey (node-key node)))
                     (cond
                       ((funcall cmpfn key nkey)
                        (recursor (node-left node)))
                       ((funcall cmpfn nkey key)
                        (recursor (node-right node)))
                       (t (values (node-value node) t))))
                   (values nil nil))))
      (recursor (base-tree-root tree)))))

(defun lookup-glb (tree key)
  "Find the greatest key in the tree strictly lesser than `key' (if it exists)."
  (check-type tree base-tree)
  (let ((cmpfn (base-tree-cmp tree)))
    (labels ((recursor (node closest)
               (if node
                   (if (funcall cmpfn (node-key node) key)
                       (recursor (node-right node) node)
                       (recursor (node-left node) closest))
                   closest)))
      (a:if-let ((closest (recursor (base-tree-root tree) nil))) 
        (values (node-key closest) t)
        (values nil nil)))))

(defun lookup-lub (tree key)
  "Find the least entry in the tree strictly greater than `key' (if it exists)."
  (check-type tree base-tree)
  (let ((cmpfn (base-tree-cmp tree)))
    (labels ((recursor (node closest)
               (if node
                   (if (funcall cmpfn key (node-key node))
                       (recursor (node-left node) node)
                       (recursor (node-right node) closest))
                   closest)))
      (a:if-let ((closest (recursor (base-tree-root tree) nil))) 
        (values (node-key closest) t)
        (values nil nil)))))

(defun %split! (tree node key)
  "Split subtree rooted at `node' into a subtree with noddes lesser than `key', the node whose key is equal to `key' (if one exists) and a subtree with nodes strictly greater than `key'."
  (let* ((joiner (ttree-joiner tree))
         (cmp (base-tree-cmp tree)))
    (when (null node)
      (return-from %split!
        (values nil nil nil)))
    (let* ((node-true-key (node-key node)))
      (cond
        ((funcall cmp key node-true-key)
         (multiple-value-bind (l returned-node r)
             (%split! tree (node-left node) key)
           (values l returned-node (funcall joiner tree
                                            r (node-key node) (node-value node) (node-right node)
                                            node))))
        ((funcall cmp node-true-key key)
         (multiple-value-bind (l returned-node r)
             (%split! tree (node-right node) key)
           (values (funcall joiner tree (node-left node) (node-key node) (node-value node) l node)
                   returned-node
                   r)))
        (t (values (node-left node) node (node-right node)))))))

(defun %split-last! (tree node)
  "Find the greatest entry in the subtree rooted at `node' and remove it. Returns the updated subtree and the removed node."
  (if (node-right node)
      (multiple-value-bind (split-tree split-node)
          (%split-last! tree (node-right node))
        (values (funcall (ttree-joiner tree) tree
                         (node-left node) (node-key node) (node-value node) split-tree
                         node)
                split-node))
      (values (node-left node) node)))

(defun %join2! (tree left right)
  "Combine two subtrees under the assumption that the greatest entry in `left' is strictly lesser than the least in `right'."
  (if left
      (multiple-value-bind (split-left split-node)
          (%split-last! tree left)
        (funcall (ttree-joiner tree) tree
                 split-left (node-key split-node) (node-value split-node) right
                 split-node))
      right))

(defun insert! (tree key value)
  (check-type tree ttree)
  (assert (eq (bt:current-thread) (box-val (ttree-transient-box tree))))
  (multiple-value-bind (left node right)
      (%split! tree (base-tree-root tree) key)
    (setf (base-tree-root tree) (funcall (ttree-joiner tree) tree left key value right node))
    tree))

(defun delete! (tree key)
  (check-type tree ttree)
  (assert (eq (bt:current-thread) (box-val (ttree-transient-box tree))))
  (multiple-value-bind (left node right)
      (%split! tree (base-tree-root tree) key)
    (declare (ignore node))
    (setf (base-tree-root tree) (%join2! tree left right))
    tree))

(defun merge! (tree1 tree2)
  "Merge the k/v pairs of the persistent `tree2' into the transient `tree1'. Matching keys take the value from `tree2'.

   Warining: Assumes that tree1's key and cmp are valid for the keys of tree2 and that tree2 is
   already in the order that would have been applied by tree1's key and cmp."
  (check-type tree1 ttree)
  (check-type tree2 ptree)
  (assert (eq (bt:current-thread) (box-val (ttree-transient-box tree1))))
  (let ((joiner (ttree-joiner tree1)))
    (setf (base-tree-root tree1)
          (labels ((merge-trees (t1 t2)
                     (cond
                       ((null t1) t2)
                       ((null t2) t1)
                       (t (multiple-value-bind (left node right)
                              (%split! tree1 t2 (node-key t1))
                            (funcall joiner tree1
                                     (merge-trees (node-left t1) left)
                                     (node-key node)
                                     (node-value node)
                                     (merge-trees (node-right t1) right)
                                     node))))))
            (merge-trees (base-tree-root tree1)
                         (base-tree-root tree2))))
    tree1))

(defun ub-join (tree left key value right &optional old-node)
  (let ((box (ttree-transient-box tree)))
    (unless (and old-node (eql (node-transient-box old-node) box))
      (setf old-node (make-node :transient-box box))))
  (setf (node-left old-node) left
        (node-key old-node) key
        (node-right old-node) right
        (node-value old-node) value)
  old-node)

(defun make-ub-tree (&optional (cmp #'<))
  (labels ((transient-for (tree)
             (make-ttree :transient-box (make-box :val (bt:current-thread))
                         :root (base-tree-root tree)
                         :cmp (base-tree-cmp tree)
                         :persistent! #'persistent!
                         :joiner #'ub-join))
           (persistent! (tree)
             (setf (box-val (ttree-transient-box tree)) nil)
             (make-ptree :root (base-tree-root tree)
                         :cmp (base-tree-cmp tree)
                         :transient-for #'transient-for)))
    (make-ptree :cmp cmp :transient-for #'transient-for)))


(defstruct (wbnode (:include node))
  size)

(defmethod print-object ((object wbnode) stream)
  (format stream
          "#<[~a] ~a ~a>"
          (not (null (box-val (node-transient-box object))))
          (wbnode-size object)
          (let ((l))
            (%inorder (lambda (k v) (push (cons k v) l)) object)
            (nreverse l))
          ))

(defun wb-join (tree left key value right &optional old-node)
  (let ((box (ttree-transient-box tree)))
    (labels ((get-node (node)
               (cond ((null node) (make-wbnode :transient-box box))
                     ((eql (node-transient-box node) box) node)
                     (t (s:lret ((node (copy-wbnode node)))
                          (setf (node-transient-box node) box))))))
      (s:callf #'get-node old-node)
      (labels ((consume-old-node (left right)
                 (setf (node-left old-node) left
                       (node-right old-node) right
                       (wbnode-size old-node) (+ 1
                                                 (size left)
                                                 (size right))
                       (node-key old-node) key
                       (node-value old-node) value)
                 old-node)
               (size (node)
                 (if node
                     (wbnode-size node)
                     0))
               (weight (node)
                 (1+ (size node))) 
               (balanced (a b) (<= 0.29 (/ (+ 1 a) (+ 2 a b)) (- 1 0.29)))
               (heavy (a b) (and a (or (not b) (> (weight a) (weight b)))))
               (recalc-size (node)
                 (when node
                   (setf (wbnode-size node) (+ 1
                                               (size (node-left node))
                                               (size (node-right node))))))
               (rotate-left (node)
                 (s:callf #'get-node node)
                 (s:callf #'get-node (node-right node))
                 (rotatef (node-left (node-right node)) node (node-right node))
                 (recalc-size (node-right node))
                 (recalc-size node)
                 node)
               (rotate-right (node)
                 (s:callf #'get-node node)
                 (s:callf #'get-node (node-left node))
                 (rotatef (node-right (node-left node)) node (node-left node))
                 (recalc-size (node-left node))
                 (recalc-size node)
                 node)
               (join-right (left right)
                 (if (balanced (size left) (size right))
                     (consume-old-node left right)
                     (let ((res (get-node left)))
                       (setf (node-right res) (join-right (node-right res) right))
                       (cond
                         ((balanced (size (node-left res)) (size (node-right res)))
                          (recalc-size res))

                         ((and (balanced (size (node-left res)) (size (node-left (node-right res))))
                               (balanced (+ (size (node-left res)) (size (node-left (node-right res))))
                                         (size (node-right (node-right res)))))
                          (s:callf #'rotate-left res))

                         (t
                          (s:callf #'rotate-right (node-right res))
                          (s:callf #'rotate-left res)))
                       
                       res)))
               (join-left (left right)
                 (if (balanced (size left) (size right))
                     (consume-old-node left right)
                     (let ((res (get-node right)))
                       (setf (node-left right) (join-left left (node-left right)))
                       (cond
                         ((balanced (size (node-left res)) (size (node-right res)))
                          (recalc-size res))

                         ((and (balanced (size (node-right (node-left res))) (size (node-right res)))
                               (balanced (+ (size (node-right (node-left res))) (size (node-right (node-left res))))
                                         (size (node-left (node-left res)))))
                          (s:callf #'rotate-right res))
                         (t
                          (s:callf #'rotate-left (node-left res))
                          (s:callf #'rotate-right res)))
                       (setf (wbnode-size res) (+ 1
                                                  (size (node-left res))
                                                  (size (node-right res))))
                       res))))
        (cond ((heavy left right) (join-right left right))
              ((heavy right left) (join-left left right))
              (t (consume-old-node left right)))))))


(defun make-wb-tree (&key (cmp #'<))
  (labels ((transient-for (tree)
             (make-ttree :transient-box (make-box :val (bt:current-thread))
                         :root (base-tree-root tree)
                         :cmp (base-tree-cmp tree)
                         :persistent! #'persistent!
                         :joiner #'wb-join))
           (persistent! (tree)
             (setf (box-val (ttree-transient-box tree)) nil)
             (make-ptree :root (base-tree-root tree)
                         :cmp (base-tree-cmp tree)
                         :transient-for #'transient-for)))
    (make-ptree :cmp cmp :transient-for #'transient-for)))
