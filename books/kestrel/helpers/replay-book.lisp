; Replaying the events in a book (perhaps with changes).
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/file-io-light/read-object-from-file" :dir :system)
(include-book "kestrel/file-io-light/read-objects-from-file" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)
(include-book "kestrel/utilities/widen-margins" :dir :system)
(include-book "kestrel/utilities/file-existsp" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)

;; Prints VAL, rounded to the hundredths place.
;; Returns nil
(defund print-rounded-val (val)
  (let* ((integer-part (floor val 1))
         (fraction-part (- val integer-part))
         (tenths (floor (* fraction-part 10) 1))
         (fraction-part-no-tenths (- fraction-part (/ tenths 10)))
         (hundredths (ceiling (* fraction-part-no-tenths 100) 1)) ; todo: do a proper rounding
         )
    (cw "~c0.~c1~c2" (cons integer-part 10) (cons tenths 1) (cons hundredths 1))))

;; Generate a short, printable thing that indicates an event (e.g., for a
;; defthm, this returns (defthm <name> :elided).
;; TODO: Handle more kinds of thing (see :doc events).
;; TODO: Maybe use ... instead of :elided.
(defun shorten-event (event)
  (if (not (consp event))
      event
    (case (car event)
      (local `(local ,(shorten-event (cadr event))))
      (in-package event)   ; no need to shorten
      (include-book event) ; no need to shorten
      ;; These have names, so we print the name:
      ((defun defund defun-nx defund-nx define defun-sk defund-sk define-sk defun-inline defun-notinline defund-inline defund-notinline defun$ defn

              defthm defthmd defthmg defthmr defrule defruled defrulel defruledl
              defaxiom
              defabbrev
              defmacro
              defstobj
              defcong
              defconst
              defret
              defchoose
              defequiv
              defxdoc
              ;; soft things like defun2?
              defexec
              defpun
              deflabel
              ;; defpkg ; no
              )
       `(,(car event) ,(cadr event) :elided))
      ;; defevaluator?
      ;; mutual-recursion?
      ;; skip-proofs?
      ((thm rule) `(,(car event) :elided))
      (theory-invariant '(theory-invariant :elided))
      (in-theory '(in-theory :elided))
      (deftheory `(deftheory ,(cadr event) :elided))
      (defsection `(defsection ,(cadr event) :elided))
      (encapsulate '(encapsulate :elided :elided)) ; todo: recur inside encapsulate?
      (progn '(progn :elided)) ; todo: recur inside progn?
      (t `(,(car event) :elided)))))

;Returns (mv erp state).
;throws an error if any event fails
; This uses :brief printing.
(defun submit-and-time-events (events print state)
  (declare (xargs :guard (member-eq print '(nil :brief :verbose))
                  :mode :program
                  :stobjs state))
  (if (endp events)
      (mv nil state)
    (let ((event (first events)))
      (mv-let (start-time state)
        (get-real-time state)
        (mv-let (erp state)
          (submit-event-helper-core event print state)
          (if erp
              (prog2$ (cw "ERROR (~x0) with event ~X12." erp event nil)
                      (mv erp state))
            ;; no error:
            (mv-let (end-time state)
              (get-real-time state)
              (let ((time (/ (ceiling (* (- end-time start-time) 100) 1) 100)))
                (progn$ (print-rounded-val time)
                        ;; The "s:" here is to label the time just printed with "seconds".
                        (cw "s: ~x0~%" (shorten-event event))
                        (submit-and-time-events (rest events) print state))))))))))

;; Read forms from FILENAME but require the first form to be an IN-PACKAGE form
;; used for interpreting symbols in the rest of the forms.  Returns (mv erp
;; forms state).
(defund read-objects-from-book (filename state)
  (declare (xargs :guard (stringp filename)
                  :mode :program ; because of in-package-fn
                  :stobjs state))
  ;; First read just the in-package form:
  (mv-let (erp first-form state)
    (read-object-from-file filename state)
    (if erp
        (mv erp nil state)
      (if (not (and (consp first-form)
                    (eq 'in-package (car first-form))))
          (prog2$ (er hard? 'read-objects-from-book "ERROR: Expected an in-package form but got ~x0." first-form)
                  (mv :missing-in-package nil state))
        (let ((original-package (current-package state))
              (book-package (cadr first-form)))
          ;; Temporarily set the package to the one for the book:
          (mv-let (erp value state)
            (in-package-fn book-package state)
            (declare (ignore value))
            (if erp
                (mv erp nil state)
              (mv-let (erp forms state)
                ;; This read uses the current package (i.e., book-package) for the symbols:
                (read-objects-from-file filename state)
                (if erp
                    (mv erp nil state)
                  ;; Undo the temporary in-package:
                  (mv-let (erp value state)
                    (in-package-fn original-package state)
                    (declare (ignore value))
                    (if erp
                        (mv erp nil state)
                      ;; No error:
                      (mv nil forms state))))))))))))


;; Returns state.
(defun load-port-file-if-exists (book-path ; no extension
                                 state)
  (declare (xargs :guard (stringp book-path)
                  :stobjs state
                  :mode :program))
  (let ((port-file-path (concatenate 'string book-path ".port")))
    (mv-let (existsp state)
      (file-existsp port-file-path state)
      (if (not existsp)
          (prog2$ (cw "NOTE: Not loading ~s0 (does not exist)~%." port-file-path)
                  state)
        (mv-let (erp val state)
          ;; TODO: Make this less noisy:
          (eval-port-file (concatenate 'string book-path ".lisp") 'load-port-file-if-exists state)
          (declare (ignore val))
          (if erp
              (prog2$ (er hard? 'load-port-file-if-exists "Error loading .port file for ~x0." book-path)
                      state)
            state))))))

;; Reads and then submits all the events in FILENAME.
;; Returns (mv erp event state).
;; TODO: Take just a filename
(defun replay-book-fn (dir      ; no trailing slash
                       bookname ; no extension
                       print state)
  (declare (xargs :guard (and (stringp dir)
                              (stringp bookname)
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple and in-package-fn
                  :stobjs state))
  (let* ((book-path-no-extension (concatenate 'string dir "/" bookname))
         (book-path (concatenate 'string book-path-no-extension ".lisp")))
    (mv-let (book-existsp state)
      (file-existsp book-path state)
      (if (not book-existsp)
          (prog2$ (er hard? 'replay-book-fn "The book ~x0 does not exist." book-path)
                  (mv :book-does-not-exist nil state))
        ;; We load the .port file mostly so that #. constants mentioned in the book are defined:
        (let ((state (load-port-file-if-exists book-path-no-extension state)))
          (mv-let (erp events state)
            (read-objects-from-book book-path state)
            (if erp
                (mv erp nil state)
              ;; We set the CBD so that the book is replayed in its own directory:
              (mv-let (erp val state)
                (set-cbd-fn dir state)
                (declare (ignore val))
                (if erp
                    (mv erp nil state)
                  (let ((state (widen-margins state)))
                    (mv-let (erp state)
                      (submit-and-time-events events print state)
                      (let ((state (unwiden-margins state)))
                        ;; No error:
                        (mv erp '(value-triple :replay-succeeded) state)))))))))))))

;; This has no effect on the world, because all the work is done in make-event
;; expansion and such changes do not persist.
;; Example: (replay-book "../lists-light" "append")
(defmacro replay-book (dir ; no trailing slash
                       bookname ; no extension
                       &key
                       (print 'nil))
  `(make-event-quiet (replay-book-fn ,dir ,bookname ,print state)))
