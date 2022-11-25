; A tool to try proof advice on each defthm in a book
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2") ; todo: change to HELP package

(include-book "replay-book")
(include-book "advice")
(include-book "kestrel/utilities/split-path" :dir :system)

;; TODO: Exclude theorems not in the testing set!
;; TODO: Try advice on defthms inside encapsulates (and perhaps other forms).
;; TODO: Consider excluding advice that uses different version of the same library (e.g., rtl/rel9).
;; TODO: Should this revert the world?

;; Example:
;; (replay-book-with-advice "../lists-light/append")

;; Determines whether the Proof Advice tool can find advice for DEFTHM.  Either way, this also submits the defthm.
;; Returns (mv erp result state) where result is :yes, :no, :maybe, or :trivial.
(defun submit-defthm-event-with-advice (defthm n book-to-avoid-absolute-path print server-url models state)
  (declare (xargs :mode :program
                  :guard (and (natp n)
                              (or (null book-to-avoid-absolute-path)
                                  (stringp book-to-avoid-absolute-path))
                              (acl2::print-levelp print)
                              (or (null server-url)
                                  (stringp server-url))
                              (help::rec-modelsp models))
                  :stobjs state))
  (b* ((defthm-variant (car defthm)) ; defthm or defthmd, etc.
       (theorem-name (cadr defthm))
       (theorem-body (caddr defthm))
       (rule-classes-result (assoc-keyword :rule-classes (cdddr defthm)))
       (rule-classes (if rule-classes-result
                         (cadr rule-classes-result)
                       ;; this really means don't put in any :rule-classes arg at all:
                       '(:rewrite)))
       (hints-presentp (if (assoc-keyword :hints (cdddr defthm)) t nil))
       (- (cw "(ADVICE: ~x0: " theorem-name))
       ((mv erp successp best-rec state)
        (help::get-and-try-advice-for-theorem theorem-name
                                              theorem-body
                                              nil ; don't use any hints
                                              nil ; theorem-otf-flg
                                              n ; number of recommendations from ML requested
                                              book-to-avoid-absolute-path
                                              print
                                              server-url
                                              nil ; debug
                                              100000 ; step-limit
                                              '(:add-hyp) ; disallow :add-hyp, because no hyps are needed for these theorems
                                              nil ; disallowed-rec-sources, todo: allow passing these in
                                              1      ; max-wins
                                              models
                                              t ; suppress warning about trivial rec, because below we ask if "original" is the best rec and handle trivial recs there
                                              state))
       ;; TODO: Maybe track errors separately?  Might be that a step limit was reached before checkpoints could even be generated, so perhaps that counts as a :no?
       ;; Would like to give time/steps proportional to what was needed for the original theorem.
       ((when erp) (mv erp :no state)))
    (if (not successp)
        (prog2$ (cw "NO)~%") ; close paren matches (ADVICE
                (b* (;; Submit the original defthm, so we can keep going:
                     ((mv erp state) (submit-event-helper-core defthm nil state))
                     ((when erp) (mv erp :no state)))
                  (mv nil :no state)))
      ;; We found advice that worked:
      (if (eq :add-hyp (help::successful-recommendationp-type best-rec))
          ;; Note that :add-hyp is now disallowed above!
          ;; TODO: Consider marking add-hyp as a failure, since we know the theorem is true without a hyp, but then
          ;; we should allow the tool to keep looking for more recs
          (prog2$ (cw "Maybe: hyp added: ~x0)~%" (help::successful-recommendationp-object best-rec)) ; close paren matches (ADVICE
                  (b* ( ;; Submit the original defthm (no extra hyp), so we can keep going:
                       ((mv erp state) (submit-event-helper-core defthm nil state))
                       ((when erp) (mv erp :no state)))
                    (mv nil :maybe state)))
        (b* (;; Since we passed nil for the hints, this means the theorem proved with no hints:
             (proved-with-no-hintsp (equal "original" (help::successful-recommendationp-name best-rec)))
             (- (if proved-with-no-hintsp
                    (if hints-presentp
                        (cw "TRIVIAL (no hints needed, though some were given))~%") ; close paren matches (ADVICE
                      (cw "TRIVIAL (no hints needed or given))~%") ; close paren matches (ADVICE
                      )
                  (progn$ (cw "YES: ~s0: " (help::successful-recommendationp-name best-rec))
                          (help::show-successful-recommendation best-rec)
                          (cw ")~%")))) ; close paren matches (ADVICE
             ((mv erp state)
              ;; We submit the event with the hints found by ML, to ensure it works:
              ;; TODO: Instead, have the advice tool check the rec and submit the original event here.
              (submit-event-helper-core (help::successful-rec-to-defthm defthm-variant theorem-name best-rec rule-classes) nil state))
             ((when erp)
              (er hard? 'submit-defthm-event-with-advice "The discovered advice for ~x0 did not work!" theorem-name)
              (mv :advice-didnt-work :no state)))
          (mv nil (if proved-with-no-hintsp :trivial :yes) state))))))

;; Determine whether EVENT is something for which we can try advice, given the list of THEOREMS-TO-TRY.
(defun advice-eventp (event theorems-to-try)
  (declare (xargs :guard (or (eq :all theorems-to-try)
                             (symbol-listp theorems-to-try))))
  (and (or (call-of 'defthm event) ; todo: maybe handle thm, defrule, rule, etc.  maybe handle defun and variants (termination and guard proof)
           (call-of 'defthmd event))
       (consp (cdr event))
       (or (eq :all theorems-to-try)
           (member-eq (cadr event) theorems-to-try))))

;Returns (mv erp yes-count no-count maybe-count trivial-count error-count state).
;throws an error if any event fails
; This uses :brief printing.
(defun submit-events-with-advice (events theorems-to-try n book-to-avoid-absolute-path print server-url models yes-count no-count maybe-count trivial-count error-count state)
  (declare (xargs :guard (and (true-listp events)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try))
                              (natp n)
                              (or (null book-to-avoid-absolute-path)
                                  (stringp book-to-avoid-absolute-path))
                              (acl2::print-levelp print)
                              (or (null server-url)
                                  (stringp server-url))
                              (help::rec-modelsp models))
                  :mode :program
                  :stobjs state))
  (if (endp events)
      (mv nil yes-count no-count maybe-count trivial-count error-count state)
    (let ((event (first events)))
      (if (advice-eventp event theorems-to-try)
          ;; It's a theorem for which we are to try advice:
          (b* ( ;; Try to prove it using advice:
               ((mv erp result state)
                (submit-defthm-event-with-advice event n book-to-avoid-absolute-path print server-url models state))
               (- (and erp
                       (cw "ERROR (~x0) with advice attempt for event ~X12 (continuing...).~%" erp event nil)
                       )))
            (if erp
                ;; If there is an error, the result is meaningless.  Now, to continue with this book, we need to get the event submitted, so we do it with skip-proofs:
                (b* ((error-count (+ 1 error-count)) ; count this error
                     ((mv erp state)
                      ;; We use skip-proofs (but see the attachment to always-do-proofs-during-make-event-expansion below):
                      ;; TODO: Don't wrap certain events in skip-proofs?
                      (submit-event-helper-core `(skip-proofs ,event) print state))
                     ((when erp)
                      (er hard? 'submit-events-with-advice "ERROR (~x0) with event ~X12 (trying to submit with skip-proofs after error trying to use advice).~%" erp event nil)
                      (mv erp yes-count no-count maybe-count trivial-count error-count state)))
                  (submit-events-with-advice (rest events) theorems-to-try n book-to-avoid-absolute-path print server-url models yes-count no-count maybe-count trivial-count error-count state))
              ;; No error, so count the result:
              (submit-events-with-advice (rest events) theorems-to-try n book-to-avoid-absolute-path print server-url models
                                         (if (eq :yes result) (+ 1 yes-count) yes-count)
                                         (if (eq :no result) (+ 1 no-count) no-count)
                                         (if (eq :maybe result) (+ 1 maybe-count) maybe-count)
                                         (if (eq :trivial result) (+ 1 trivial-count) trivial-count)
                                         error-count
                                         state)))
        ;; Not something for which we will try advice, so submit it and continue:
        (b* (((mv erp state)
              ;; We use skip-proofs for speed (but see the attachment to always-do-proofs-during-make-event-expansion below):
              (submit-event-helper-core `(skip-proofs ,event) print state))
             ;; FIXME: Anything that tries to read from a file will give an error since the current dir won't be right.
             ((when erp)
              (cw "ERROR (~x0) with event ~X12.~%" erp event nil)
              (mv erp yes-count no-count maybe-count trivial-count error-count state))
             (- (cw "Skip: ~x0~%" (shorten-event event))))
          (submit-events-with-advice (rest events) theorems-to-try n book-to-avoid-absolute-path print server-url models yes-count no-count maybe-count trivial-count error-count state))))))

(defun discard-events-before-first-advice-event (events theorems-to-try)
  (declare (xargs :guard (and (true-listp events)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try)))))
  (if (endp events)
      nil ; we've discarded everything, without finding an advice-event
    (let ((event (first events)))
      (if (advice-eventp event theorems-to-try)
          events ; stop discarding
        (discard-events-before-first-advice-event (rest events) theorems-to-try)))))

;; todo: can't a tool auto-generate this?
(local
 (defthm true-listp-of-discard-events-before-first-advice-event
   (implies (true-listp events)
            (true-listp (discard-events-before-first-advice-event events theorems-to-try)))))

(defun discard-events-after-last-advice-event (events theorems-to-try)
  (declare (xargs :guard (and (true-listp events)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try)))))
  (reverse (discard-events-before-first-advice-event (reverse events) theorems-to-try)))

;; Reads and then submits all the events in FILENAME, trying advice for the theorems.
;; Returns (mv erp counts state), where counts is (list yes-count no-count maybe-count trivial-count error-count).
;; Since this returns an error triple, it can be wrapped in revert-world.
(defun replay-book-with-advice-fn-aux (filename ; the book, with .lisp extension, we should have already checked that it exists
                                       theorems-to-try
                                       n
                                       print
                                       server-url
                                       models
                                       state)
  (declare (xargs :guard (and (stringp filename)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try))
                              (natp n)
                              (acl2::print-levelp print)
                              (or (null server-url)
                                  (stringp server-url))
                              (help::rec-modelsp models))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (b* ( ;; We must avoid including the current book (or an other book that includes it) when trying to find advice:
       (book-to-avoid-absolute-path (canonical-pathname filename nil state))
       ((when (member-equal book-to-avoid-absolute-path
                            (included-books-in-world (w state))))
        (cw "WARNING: Can't replay ~s0 because it is already included in the world.~%" filename)
        (mv :book-already-included (list 0 0 0 0 0) state))
       ((mv dir &) (split-path filename))
       (- (cw "REPLAYING ~s0 with advice:~%" filename))
       ;; May be necessary for resolving #. constants in read-objects-from-book:
       (state (load-port-file-if-exists (remove-lisp-suffix filename t) state))
       ;; Read all the forms from the file:
       ((mv erp events state)
        (read-objects-from-book filename state))
       (- (cw "(~x0 events.)~%" (len events)))
       (events (discard-events-after-last-advice-event events theorems-to-try))
       (- (cw "(~x0 events after discarding final events.)~%~%" (len events)))
       ((when (null events))
        (cw "~%SUMMARY for book ~s0: NO EVENTS TO TEST~%" filename)
        (mv nil ; no error, but nothing to do for this book
            (list 0 0 0 0 0) state))
       ((when erp) (cw "Error: ~x0.~%" erp) (mv erp (list 0 0 0 0 0) state))
       ;; Ensure we are working in the same dir as the book:
       ((mv erp & state)
        (set-cbd-fn dir state))
       ((when erp) (mv erp (list 0 0 0 0 0) state))
       ;; TODO: Also have to change the dir from which files are read.  How can we do that?
       ;; This didn't work: (- (sys-call "cd" (list dir)))
       ;; Make margins wider for nicer printing:
       (state (widen-margins state))
       ;; Ensure proofs are done during make-event expansion, even if we use skip-proofs:
       ((mv erp state) (submit-event-helper-core '(defattach (acl2::always-do-proofs-during-make-event-expansion acl2::constant-t-function-arity-0) :system-ok t) nil state))
       ((when erp) (mv erp (list 0 0 0 0 0) state))
       ;; Submit all the events, trying advice for each defthm in theorems-to-try:
       ((mv erp yes-count no-count maybe-count trivial-count error-count state)
        (submit-events-with-advice events theorems-to-try n book-to-avoid-absolute-path print server-url models 0 0 0 0 0 state))
       ((when erp) ; I suppose we could return partial results from this book instead
        (cw "Error: ~x0.~%" erp)
        (mv erp (list 0 0 0 0 0) state))
       ;; Print stats:
       (- (progn$ (cw "~%SUMMARY for book ~s0:~%" filename)
                  (cw "(Asked each model for ~x0 recommendations.)~%" n)
                  (cw "ADVICE FOUND    : ~x0~%" yes-count)
                  (cw "NO ADVICE FOUND : ~x0~%" no-count)
                  ;; (cw "ADD HYP ADVICE FOUND : ~x0~%" maybe-count)
                  (cw "NO HINTS NEEDED : ~x0~%" trivial-count)
                  (cw "ERROR           : ~x0~%" error-count)))
       ;; Undo margin widening:
       (state (unwiden-margins state)))
    (mv nil ; no error
        (list yes-count no-count maybe-count trivial-count error-count)
        state)))

;; Reads and then submits all the events in FILENAME, trying advice for the theorems.
;; Returns (mv erp event state).
(defun replay-book-with-advice-fn (filename ; the book, with .lisp extension
                                   theorems-to-try
                                   n
                                   print
                                   server-url
                                   models
                                   state)
  (declare (xargs :guard (and (stringp filename)
                              (or (eq :all theorems-to-try)
                                  (symbol-listp theorems-to-try))
                              (natp n)
                              (acl2::print-levelp print)
                              (or (null server-url)
                                  (stringp server-url)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (b* (((mv book-existsp state) (file-existsp filename state))
       ((when (not book-existsp))
        (er hard? 'replay-book-with-advice-fn "The book ~x0 does not exist." filename)
        (mv :book-does-not-exist nil state))
        ;; Elaborate options:
       (models (if (eq models :all)
                   help::*known-models*
                 (if (help::rec-modelp models)
                     (list models) ; single model stands for singleton list of that model
                   models)))
       ((mv erp
            & ; counts
            state)
        (replay-book-with-advice-fn-aux filename theorems-to-try n print server-url models state))
       ((when erp) (mv erp nil state)))
    ;; No error:
    (mv nil '(value-triple :replay-succeeded) state)))

;; TODO: Add timing info.
;; This has no effect on the world, because all the work is done in make-event
;; expansion and such changes do not persist.
;; Example: (replay-book-with-advice "../lists-light/append.lisp")
(defmacro replay-book-with-advice (filename ; the book, with .lisp extension
                                   &key
                                   (theorems-to-try ':all) ; gets evaluated
                                   (n '10) ; number of recommendations to use
                                   (print 'nil)
                                   (server-url 'nil) ; nil means get from environment var
                                   (models ':all)
                                   )
  `(make-event-quiet (replay-book-with-advice-fn ,filename ,theorems-to-try ,n ,print ,server-url ,models state)))
