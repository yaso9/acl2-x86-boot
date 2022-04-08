; Functions to update a node-replacement-array (new version)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "node-replacement-array")
(include-book "dag-arrays")
(include-book "contexts")
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/alists-light/alistp" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

(local (in-theory (disable symbol-listp alistp member-equal natp)))

;; pairs of updates to be made to the node-replacement-array, to undo changes made to it for true and else branches
;; todo: add "bounded" to the name
(defund undo-pairsp (pairs dag-len)
  (declare (xargs :guard (natp dag-len)))
  (if (atom pairs)
      (null pairs)
    (let ((pair (first pairs)))
      (and (consp pair)
           (let* ((index (car pair))
                  (val (cdr pair)))
             (and (natp index)
                  ;; No bound needed on the index because we'll only apply undo-pairs whose indices are < node-replacement-array-num-valid-nodes
                  ;; (< index node-replacement-array-num-valid-nodes)
                  (bounded-node-replacement-valp val dag-len)
                  (undo-pairsp (rest pairs) dag-len)))))))

(defthm undo-pairsp-of-nil
  (undo-pairsp nil dag-len)
  :hints (("Goal" :in-theory (enable undo-pairsp))))

(defthm undo-pairsp-forward-to-alistp
  (implies (undo-pairsp pairs dag-len)
           (alistp pairs))
  :hints (("Goal" :in-theory (enable undo-pairsp)))
  :rule-classes :forward-chaining)

(defthm bounded-node-replacement-valp-of-cdr-of-car-when-undo-pairsp
  (implies (undo-pairsp undo-pairs dag-len)
           (bounded-node-replacement-valp (cdr (car undo-pairs)) dag-len))
  :hints (("Goal" :in-theory (enable undo-pairsp))))

(defthm natp-of-car-of-car-when-undo-pairsp
  (implies (undo-pairsp undo-pairs dag-len)
           (equal (natp (car (car undo-pairs)))
                  (consp undo-pairs)))
  :hints (("Goal" :in-theory (enable undo-pairsp))))

(defthm node-replacement-valp-of-cdr-of-car-when-undo-pairsp
  (implies (undo-pairsp undo-pairs dag-len)
           (node-replacement-valp (cdr (car undo-pairs))))
  :hints (("Goal" :in-theory (enable undo-pairsp))))

(defthm natp-of-car-of-car-when-undo-pairsp-forward
  (implies (and (undo-pairsp undo-pairs dag-len)
                (consp undo-pairs))
           (natp (car (car undo-pairs))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable undo-pairsp))))

(defthm undo-pairsp-monotone
  (implies (and (undo-pairsp pairs dag-len)
                (<= dag-len bound))
           (undo-pairsp pairs bound))
  :hints (("Goal" :in-theory (enable undo-pairsp))))

(defthm undo-pairsp-of-cdr
  (implies (undo-pairsp pairs dag-len)
           (undo-pairsp (cdr pairs) dag-len))
  :hints (("Goal" :in-theory (enable undo-pairsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv node-replacement-array node-replacement-array-num-valid-nodes undo-pairs).  The first elemend of the undo-pairs must be undone first, and so on.
;; The order of the undo-pairs returned may be crucial if we change the same array element twice (the array write that was done first needs to be undone last)
(defund update-node-replacement-array-for-assuming-possibly-negated-nodenums (possibly-negated-nodenums
                                                                              node-replacement-array node-replacement-array-num-valid-nodes
                                                                              dag-array dag-len
                                                                              known-booleans
                                                                              undo-pairs-acc)
  (declare (xargs :guard (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (possibly-negated-nodenumsp possibly-negated-nodenums)
                              (all-< (strip-nots-from-possibly-negated-nodenums possibly-negated-nodenums)
                                     dag-len)
                              (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                              (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                              (natp node-replacement-array-num-valid-nodes)
                              (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                              (symbol-listp known-booleans)
                              (undo-pairsp undo-pairs-acc dag-len))
                  :guard-hints (("Goal" :expand ((possibly-negated-nodenumsp possibly-negated-nodenums)
                                                 (strip-nots-from-possibly-negated-nodenums possibly-negated-nodenums)
                                                 (ALL-DARGP (DARGS (CAR POSSIBLY-NEGATED-NODENUMS)))
                                                 (ALL-DARGP (CDR (DARGS (CAR POSSIBLY-NEGATED-NODENUMS)))))
                                 :in-theory (enable (:d strip-nots-from-possibly-negated-nodenums)
                                                    undo-pairsp
                                                    strip-not-from-possibly-negated-nodenum
                                                    possibly-negated-nodenump
                                                    CONSP-OF-CDR)))))
  (if (endp possibly-negated-nodenums)
      (mv node-replacement-array node-replacement-array-num-valid-nodes undo-pairs-acc)
    (let ((pnn (first possibly-negated-nodenums)))
      (if (consp pnn) ; check for (not <nodenum>)
          ;; Since we are assuming (not <nodenum>), we can set <nodenum> to be replaced with 'nil:
          (let* ((negated-nodenum (darg1 pnn)) ; is darg1 the best idiom here?
                 (old-val (if (< negated-nodenum node-replacement-array-num-valid-nodes)
                              (aref1 'node-replacement-array node-replacement-array negated-nodenum)
                            nil)))
            (mv-let (node-replacement-array node-replacement-array-num-valid-nodes)
              (add-node-replacement-entry-and-maybe-expand negated-nodenum *nil* node-replacement-array node-replacement-array-num-valid-nodes)
              (update-node-replacement-array-for-assuming-possibly-negated-nodenums (rest possibly-negated-nodenums)
                                                                                    node-replacement-array node-replacement-array-num-valid-nodes
                                                                                    dag-array dag-len
                                                                                    known-booleans
                                                                                    (acons negated-nodenum old-val undo-pairs-acc))))
        ;; pnn is a nodenum, so look at its expression:
        (let ((expr (aref1 'dag-array dag-array pnn)))
          (if (atom expr)
              (prog2$ (cw "Warning: Variable assumption, ~x0, encountered.~%" expr) ;skip it
                      (update-node-replacement-array-for-assuming-possibly-negated-nodenums (rest possibly-negated-nodenums)
                                                                                            node-replacement-array node-replacement-array-num-valid-nodes
                                                                                            dag-array dag-len
                                                                                            known-booleans undo-pairs-acc))
            (if (quotep expr)
                (prog2$ (cw "Warning: Quotep assumption, ~x0, encountered.~%" expr) ;skip it
                        (update-node-replacement-array-for-assuming-possibly-negated-nodenums (rest possibly-negated-nodenums)
                                                                                              node-replacement-array node-replacement-array-num-valid-nodes
                                                                                              dag-array dag-len
                                                                                              known-booleans undo-pairs-acc))
              (if (and (eq 'equal (ffn-symb expr))
                       (consp (cdr (dargs expr))) ; for guards
                       )
                  ;; special case: assuming (equal <x> <y>)
                  (mv-let (nodenum replacement)
                    (let ((x (darg1 expr))
                          (y (darg2 expr)))
                      (if (and (consp x) (consp y)) ; check for 2 quoteps (unusual)
                          (prog2$ (cw "NOTE: update-node-replacement-array-for-assuming-possibly-negated-nodenums encountered unusual assumption ~x0.~%" expr)
                                  ;; just replace the whole equality with T:
                                  (mv pnn *t*))
                        (if (consp x)
                            (mv y x) ; x is a constant, so replace y with x
                          (if (consp y)
                              (mv x y) ; y is a constant, so replace x with y
                            ;; We're being conservative here and not replacing either term with the other in general (TODO: consider when one is a subterm of the other)
                            (mv pnn *t*) ; todo: maybe consider also adding the reverse equality, but that would mean adding nodes
                            ))))
                    ;; Now replace the chosen NODENUM with the chosen REPLACEMENT:
                    (let ((old-val (if (< nodenum node-replacement-array-num-valid-nodes)
                                       (aref1 'node-replacement-array node-replacement-array nodenum)
                                     nil)))
                      (mv-let (node-replacement-array node-replacement-array-num-valid-nodes)
                        (add-node-replacement-entry-and-maybe-expand nodenum replacement node-replacement-array node-replacement-array-num-valid-nodes)
                        (update-node-replacement-array-for-assuming-possibly-negated-nodenums (rest possibly-negated-nodenums)
                                                                                              node-replacement-array node-replacement-array-num-valid-nodes
                                                                                              dag-array dag-len known-booleans
                                                                                              (acons nodenum old-val undo-pairs-acc)))))
                ;; usual case (not a call of equal):
                (if (member-eq (ffn-symb expr) known-booleans)
                    ;; Since we are assuming <nodenum> and it's boolean, we can set it to be replaced with 't:
                    (let ((old-val (if (< pnn node-replacement-array-num-valid-nodes)
                                       (aref1 'node-replacement-array node-replacement-array pnn)
                                     nil)))
                      (mv-let (node-replacement-array node-replacement-array-num-valid-nodes)
                        (add-node-replacement-entry-and-maybe-expand pnn *t* node-replacement-array node-replacement-array-num-valid-nodes)
                        (update-node-replacement-array-for-assuming-possibly-negated-nodenums (rest possibly-negated-nodenums)
                                                                                              node-replacement-array node-replacement-array-num-valid-nodes
                                                                                              dag-array dag-len known-booleans
                                                                                              (acons pnn old-val undo-pairs-acc))))
                  ;; Since we are assuming <nodenum> and it's not known-boolean, we can only set it :non-nil.
                  (let ((old-val (if (< pnn node-replacement-array-num-valid-nodes)
                                     (aref1 'node-replacement-array node-replacement-array pnn)
                                   nil)))
                    (mv-let (node-replacement-array node-replacement-array-num-valid-nodes)
                      (add-node-replacement-entry-and-maybe-expand pnn *non-nil* node-replacement-array node-replacement-array-num-valid-nodes)
                      (update-node-replacement-array-for-assuming-possibly-negated-nodenums (rest possibly-negated-nodenums)
                                                                                            node-replacement-array node-replacement-array-num-valid-nodes
                                                                                            dag-array dag-len known-booleans
                                                                                            (acons pnn old-val undo-pairs-acc)))))))))))))

(defthm update-node-replacement-array-for-assuming-possibly-negated-nodenums-return-type
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (possibly-negated-nodenumsp possibly-negated-nodenums)
                (all-< (strip-nots-from-possibly-negated-nodenums possibly-negated-nodenums)
                       dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                ;(symbol-listp known-booleans)
                (undo-pairsp undo-pairs-acc dag-len))
           (mv-let (node-replacement-array node-replacement-array-num-valid-nodes undo-pairs)
             (update-node-replacement-array-for-assuming-possibly-negated-nodenums possibly-negated-nodenums
                                                                                   node-replacement-array node-replacement-array-num-valid-nodes
                                                                                   dag-array dag-len
                                                                                   known-booleans
                                                                                   undo-pairs-acc)
             (and (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                  (natp node-replacement-array-num-valid-nodes)
                  (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                  (undo-pairsp undo-pairs dag-len)
                  )))
  :hints (("Goal" :expand ((POSSIBLY-NEGATED-NODENUMSP POSSIBLY-NEGATED-NODENUMS)
                           (STRIP-NOTS-FROM-POSSIBLY-NEGATED-NODENUMS POSSIBLY-NEGATED-NODENUMS))
           :induct t
           :in-theory (enable UPDATE-NODE-REPLACEMENT-ARRAY-FOR-ASSUMING-POSSIBLY-NEGATED-NODENUMS
                              undo-pairsp
                              (:d STRIP-NOTS-FROM-POSSIBLY-NEGATED-NODENUMS)
                              STRIP-NOT-FROM-POSSIBLY-NEGATED-NODENUM
                              POSSIBLY-NEGATED-NODENUMP))))

(defthm update-node-replacement-array-for-assuming-possibly-negated-nodenums-return-type-alen1
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (possibly-negated-nodenumsp possibly-negated-nodenums)
                (all-< (strip-nots-from-possibly-negated-nodenums possibly-negated-nodenums)
                       dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
;(symbol-listp known-booleans)
                (undo-pairsp undo-pairs-acc dag-len))
           (<= (alen1 'node-replacement-array node-replacement-array)
               (alen1 'node-replacement-array (mv-nth 0
                                                      (update-node-replacement-array-for-assuming-possibly-negated-nodenums possibly-negated-nodenums
                                                                                                                            node-replacement-array node-replacement-array-num-valid-nodes
                                                                                                                            dag-array dag-len
                                                                                                                            known-booleans
                                                                                                                            undo-pairs-acc)))))
  :hints (("Goal" :expand ((POSSIBLY-NEGATED-NODENUMSP POSSIBLY-NEGATED-NODENUMS)
                           (STRIP-NOTS-FROM-POSSIBLY-NEGATED-NODENUMS POSSIBLY-NEGATED-NODENUMS))
           :induct t
           :in-theory (enable UPDATE-NODE-REPLACEMENT-ARRAY-FOR-ASSUMING-POSSIBLY-NEGATED-NODENUMS
                              undo-pairsp
                              (:d STRIP-NOTS-FROM-POSSIBLY-NEGATED-NODENUMS)
                              STRIP-NOT-FROM-POSSIBLY-NEGATED-NODENUM
                              POSSIBLY-NEGATED-NODENUMP))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Consider optimizing by doing things more directly
;; Returns (mv node-replacement-array node-replacement-array-num-valid-nodes undo-pairs).
(defund update-node-replacement-array-for-assuming-node (nodenum node-replacement-array node-replacement-array-num-valid-nodes dag-array dag-len known-booleans)
  (declare (xargs :guard (and (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (natp nodenum)
                              (< nodenum dag-len)
                              (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                              (natp node-replacement-array-num-valid-nodes)
                              (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                              (symbol-listp known-booleans))))
  (let ((conjunction (get-axe-conjunction-from-dag-item nodenum 'dag-array dag-array dag-len)))
    (if (quotep conjunction)
        (prog2$ (cw "Warning: Constant assumption, ~x0, encountered.~%" conjunction)
                (mv node-replacement-array node-replacement-array-num-valid-nodes nil))
      (update-node-replacement-array-for-assuming-possibly-negated-nodenums conjunction
                                                                            node-replacement-array node-replacement-array-num-valid-nodes
                                                                            dag-array dag-len
                                                                            known-booleans
                                                                            nil))))

(defthm update-node-replacement-array-for-assuming-node-return-type
  (implies (and (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                ;;(symbol-listp known-booleans)
                )
           (mv-let (node-replacement-array node-replacement-array-num-valid-nodes undo-pairs)
             (update-node-replacement-array-for-assuming-node nodenum node-replacement-array node-replacement-array-num-valid-nodes dag-array dag-len known-booleans)
             (and (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                  (natp node-replacement-array-num-valid-nodes)
                  (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                  (undo-pairsp undo-pairs dag-len)
                  )))
  :hints (("Goal" :in-theory (enable update-node-replacement-array-for-assuming-node))))

(defthm update-node-replacement-array-for-assuming-node-return-type-corollary
  (implies (and (<= dag-len bound)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                ;;(symbol-listp known-booleans)
                )
           (undo-pairsp (mv-nth 2 (update-node-replacement-array-for-assuming-node nodenum node-replacement-array node-replacement-array-num-valid-nodes dag-array dag-len known-booleans)) bound))
  :hints (("Goal" :use (:instance update-node-replacement-array-for-assuming-node-return-type)
           :in-theory (disable update-node-replacement-array-for-assuming-node-return-type))))

(defthm update-node-replacement-array-for-assuming-node-return-type-alen1
  (implies (and (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                ;;(symbol-listp known-booleans)
                )
           (<= (alen1 'node-replacement-array node-replacement-array)
               (alen1 'node-replacement-array (mv-nth 0 (update-node-replacement-array-for-assuming-node nodenum node-replacement-array node-replacement-array-num-valid-nodes dag-array dag-len known-booleans)))))
  :hints (("Goal" :in-theory (enable update-node-replacement-array-for-assuming-node
                                     ALL-<-OF-STRIP-NOTS-FROM-POSSIBLY-NEGATED-NODENUMS-WHEN-BOUNDED-AXE-CONJUNCTIONP))))

(defthm update-node-replacement-array-for-assuming-node-return-type-alen1-corollary
  (implies (and (<= bound (alen1 'node-replacement-array node-replacement-array))
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                ;;(symbol-listp known-booleans)
                )
           (<= bound
               (alen1 'node-replacement-array (mv-nth 0 (update-node-replacement-array-for-assuming-node nodenum node-replacement-array node-replacement-array-num-valid-nodes dag-array dag-len known-booleans)))))
  :hints (("Goal" :use update-node-replacement-array-for-assuming-node-return-type-alen1
           :in-theory (disable update-node-replacement-array-for-assuming-node-return-type-alen1))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Consider optimizing by doing things more directly
;; Returns (mv node-replacement-array node-replacement-array-num-valid-nodes undo-pairs).
(defund update-node-replacement-array-for-assuming-negation-of-node (nodenum node-replacement-array node-replacement-array-num-valid-nodes dag-array dag-len known-booleans)
  (declare (xargs :guard (and (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                              (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                              (natp nodenum)
                              (< nodenum dag-len)
                              (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                              (natp node-replacement-array-num-valid-nodes)
                              (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                              (symbol-listp known-booleans))
                  :guard-hints (("Goal" :in-theory (enable ALL-<-OF-STRIP-NOTS-FROM-POSSIBLY-NEGATED-NODENUMS-WHEN-BOUNDED-AXE-CONJUNCTIONP)))))
  (let* ((disjunction (get-axe-disjunction-from-dag-item nodenum 'dag-array dag-array dag-len)) ; assume (not (or a b c)) by assuming (not a) and (not b), etc.
         (conjunction (negate-axe-disjunction disjunction)))
    (if (quotep conjunction)
        (prog2$ (cw "Warning: Constant assumption, ~x0, encountered.~%" conjunction)
                (mv node-replacement-array node-replacement-array-num-valid-nodes nil))
      (update-node-replacement-array-for-assuming-possibly-negated-nodenums conjunction
                                                                            node-replacement-array node-replacement-array-num-valid-nodes
                                                                            dag-array dag-len
                                                                            known-booleans
                                                                            nil))))

(defthm update-node-replacement-array-for-assuming-negation-of-node-return-type
  (implies (and (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                ;;(symbol-listp known-booleans)
                )
           (mv-let (node-replacement-array node-replacement-array-num-valid-nodes undo-pairs)
             (update-node-replacement-array-for-assuming-negation-of-node nodenum node-replacement-array node-replacement-array-num-valid-nodes dag-array dag-len known-booleans)
             (and (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                  (natp node-replacement-array-num-valid-nodes)
                  (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                  (undo-pairsp undo-pairs dag-len)
                  )))
  :hints (("Goal" :in-theory (enable update-node-replacement-array-for-assuming-negation-of-node
                                     ALL-<-OF-STRIP-NOTS-FROM-POSSIBLY-NEGATED-NODENUMS-WHEN-BOUNDED-AXE-CONJUNCTIONP))))

(defthm update-node-replacement-array-for-assuming-negation-of-node-return-type-corollary
  (implies (and (<= dag-len bound)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                ;;(symbol-listp known-booleans)
                )
           (undo-pairsp (mv-nth 2 (update-node-replacement-array-for-assuming-negation-of-node nodenum node-replacement-array node-replacement-array-num-valid-nodes dag-array dag-len known-booleans)) bound))
  :hints (("Goal" :use (:instance update-node-replacement-array-for-assuming-negation-of-node-return-type)
           :in-theory (disable update-node-replacement-array-for-assuming-negation-of-node-return-type))))

(defthm update-node-replacement-array-for-assuming-negation-of-node-return-type-alen1
  (implies (and (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                ;;(symbol-listp known-booleans)
                )
           (<= (alen1 'node-replacement-array node-replacement-array)
               (alen1 'node-replacement-array (mv-nth 0 (update-node-replacement-array-for-assuming-negation-of-node nodenum node-replacement-array node-replacement-array-num-valid-nodes dag-array dag-len known-booleans)))))
  :hints (("Goal" :in-theory (enable update-node-replacement-array-for-assuming-negation-of-node
                                     ALL-<-OF-STRIP-NOTS-FROM-POSSIBLY-NEGATED-NODENUMS-WHEN-BOUNDED-AXE-CONJUNCTIONP))))

(defthm update-node-replacement-array-for-assuming-negation-of-node-return-type-alen1-corollary
  (implies (and (<= bound (alen1 'node-replacement-array node-replacement-array))
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                (natp nodenum)
                (< nodenum dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array))
                ;;(symbol-listp known-booleans)
                )
           (<= bound
               (alen1 'node-replacement-array (mv-nth 0 (update-node-replacement-array-for-assuming-negation-of-node nodenum node-replacement-array node-replacement-array-num-valid-nodes dag-array dag-len known-booleans)))))
  :hints (("Goal" :use update-node-replacement-array-for-assuming-negation-of-node-return-type-alen1
           :in-theory (disable update-node-replacement-array-for-assuming-negation-of-node-return-type-alen1))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns the node-replacement-array (node-replacement-array-num-valid-nodes is unchanged)
;; DAG-LEN is just passed so we can call undo-pairsp
;; The order of the undo-pairs may be critical.
(defund undo-writes-to-node-replacement-array (undo-pairs node-replacement-array node-replacement-array-num-valid-nodes dag-len)
  (declare (xargs :guard (and (natp dag-len)
                              (undo-pairsp undo-pairs dag-len)
                              (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                              (natp node-replacement-array-num-valid-nodes)
                              (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array)))
                  :guard-hints (("Goal" :in-theory (enable undo-pairsp)))))
  (if (endp undo-pairs)
      node-replacement-array
    (let* ((pair (first undo-pairs))
           (index (car pair))
           (val (cdr pair)))
      (if (<= node-replacement-array-num-valid-nodes index) ;todo: prove that this can't happen (strengthen the guard?)
          (prog2$ (er hard? 'undo-writes-to-node-replacement-array "Implementation error.")
                  (undo-writes-to-node-replacement-array (rest undo-pairs) node-replacement-array node-replacement-array-num-valid-nodes dag-len))
        (undo-writes-to-node-replacement-array (rest undo-pairs)
                                               (aset1 'node-replacement-array node-replacement-array index val)
                                               node-replacement-array-num-valid-nodes
                                               dag-len)))))

(defthm undo-writes-to-node-replacement-array-return-type
  (implies (and (undo-pairsp undo-pairs dag-len)
                (bounded-node-replacement-arrayp 'node-replacement-array node-replacement-array dag-len)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array)))
           (bounded-node-replacement-arrayp 'node-replacement-array
                                            (undo-writes-to-node-replacement-array undo-pairs node-replacement-array node-replacement-array-num-valid-nodes dag-len)
                                            dag-len))
  :hints (("Goal" :in-theory (e/d (undo-writes-to-node-replacement-array
                                   ;undo-pairsp
                                   )
                                  (BOUNDED-NODE-REPLACEMENT-VALP)))))

(defthm alen1-of-undo-writes-to-node-replacement-array
  (implies (and (natp dag-len)
                (undo-pairsp undo-pairs dag-len)
                (node-replacement-arrayp 'node-replacement-array node-replacement-array)
                (natp node-replacement-array-num-valid-nodes)
                (<= node-replacement-array-num-valid-nodes (alen1 'node-replacement-array node-replacement-array)))
           (equal (alen1 'node-replacement-array (undo-writes-to-node-replacement-array undo-pairs node-replacement-array node-replacement-array-num-valid-nodes dag-len))
                  (alen1 'node-replacement-array node-replacement-array)))
  :hints (("Goal" :in-theory (enable undo-writes-to-node-replacement-array
                                     ))))
