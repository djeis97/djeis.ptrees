(in-package #:cl-user)

(defpackage #:djeis.ptrees.common
  (:export #:make-box #:box-val))

(defpackage #:djeis.ptrees.bst
  (:export #:lookup #:lookup-glb #:lookup-lub #:mapkv #:reducekv
           #:insert! #:delete! #:merge!
           #:make-wb-tree #:transient-for #:persistent!))

(defpackage #:djeis.ptrees.hamt
  (:export #:make-trie #:insert! #:delete!
           #:transient-for #:persistent!
           #:lookup))

