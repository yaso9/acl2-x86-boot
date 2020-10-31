; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/error-checking/ensure-symbol-is-fresh-event-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-function-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol-list" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-true-list" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-untranslated-term" :dir :system)
(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/event-macros/event-generation-soft" :dir :system)
(include-book "kestrel/event-macros/input-processing" :dir :system)
(include-book "kestrel/event-macros/proof-preparation" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/soft/defequal" :dir :system)
(include-book "kestrel/soft/defun-sk2" :dir :system)
(include-book "kestrel/soft/defund-sk2" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/std/system/if-tree-leaf-terms" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/runes" :dir :system)
(include-book "kestrel/utilities/trans-eval-error-triple" :dir :system)

(include-book "utilities/input-processing")
(include-book "utilities/transformation-table")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 solve

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  (xdoc::evmac-topic-implementation-item-input-untyped/typed "old")

  (xdoc::evmac-topic-implementation-item-input "method")

  (xdoc::evmac-topic-implementation-item-input "method-rules")

  (xdoc::evmac-topic-implementation-item-input "solution-name")

  (xdoc::evmac-topic-implementation-item-input "solution-enable")

  (xdoc::evmac-topic-implementation-item-input "solution-guard")

  (xdoc::evmac-topic-implementation-item-input "solution-guard-hints")

  (xdoc::evmac-topic-implementation-item-input "solution-body")

  (xdoc::evmac-topic-implementation-item-input "solution-hints")

  (xdoc::evmac-topic-implementation-item-input "new-name")

  (xdoc::evmac-topic-implementation-item-input-untyped/typed "new-enable")

  (xdoc::evmac-topic-implementation-item-input "old-if-new-name")

  (xdoc::evmac-topic-implementation-item-input-untyped/typed "old-if-new-enable")

  (xdoc::evmac-topic-implementation-item-input-untyped/typed "verify-guards")

  (xdoc::evmac-topic-implementation-item-input "print")

  (xdoc::evmac-topic-implementation-item-input "show-only")

  (xdoc::evmac-topic-implementation-item-fn-doc "?f")

  "@('x1...xn') is the list of variable symbols @('x1'), ..., @('xn')
   described in the user documentation."

  "@('matrix') is the term @('matrix<(?f x1 ... xn)>')
   described in the user documentation."

  (xdoc::evmac-topic-implementation-item-fn-doc "f")

  "@('f-existsp') is a boolean indicating whether @('f') already exists
   (as opposed to being generated)."

  "@('f-body') is the obtained body of the solution function @('f'),
   when this function is generated."

  "@('solution-correct') is the name of the locally generated theorem
   asserting the correctness of the solution."

  (xdoc::evmac-topic-implementation-item-fn-doc "new")

  (xdoc::evmac-topic-implementation-item-thm-doc "old-if-new")

  xdoc::*evmac-topic-implementation-item-names-to-avoid*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing solve)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-process-old (old verify-guards ctx state)
  :returns (mv erp
               (result "@('(tuple (old symbolp)
                                  (?f symbolp)
                                  (x1...xn symbol-listp)
                                  (matrix pseudo-termp))').")
               state)
  :mode :program
  :short "Process the @('old') input."
  (b* ((wrld (w state))
       ((er old) (ensure-function-name-or-numbered-wildcard$
                  old "The first input" t nil))
       ((when (and (eq verify-guards t)
                   (not (guard-verified-p old wrld))))
        (er-soft+ ctx t nil
                  "Since the :VERIFY-GUARDS input is T, ~
                   the target function ~x0 must be guard-verified, ~
                   but it is not."
                  old))
       ((unless (soft::quant-sofunp old wrld))
        (er-soft+ ctx t nil
                  "The target function ~x0 ~
                   must be a SOFT quantifier function."
                  old))
       (funvars (soft::sofun-funvars old wrld))
       ((unless (= (len funvars) 1))
        (er-soft+ ctx t nil
                  "The target function ~x0 ~
                   must depend on exactly one function variable, ~
                   but instead it depends on ~x1."
                  old funvars))
       (??f (car funvars))
       ((when (consp (formals old wrld)))
        (er-soft+ ctx t nil
                  "The target function ~x0 ~
                   must have no parameters, but instead it has parameters ~x1."
                  old (formals old wrld)))
       ((unless (eq (defun-sk-quantifier old wrld) 'forall))
        (er-soft+ ctx t nil
                  "The quantifier of the target function ~x0 ~
                   must be universal, but it is existential instead."
                  old))
       (x1...xn (defun-sk-bound-vars old wrld))
       (imatrix (defun-sk-imatrix old wrld))
       (matrix (defun-sk-matrix old wrld))
       (calls (all-calls (list ?f) matrix nil nil))
       ((unless (= (len calls) 1))
        (er-soft+ ctx t nil
                  "The matrix ~x0 of the target function ~x1, ~
                   after translation and LET expansion, ~
                   must contains exactly one call of ~x2, ~
                   but it contains ~@3 instead."
                  imatrix
                  old
                  ?f
                  (if (consp calls)
                      (msg "multiple calls ~&0" calls)
                    "no calls")))
       (call (car calls))
       ((unless (equal (fargs call) x1...xn))
        (er-soft+ ctx t nil
                  "The matrix ~x0 of the target function ~x1, ~
                   after translation and LET expansion, ~
                   must call ~x2 on the variables ~x3, ~
                   but it calls it on ~x4 instead."
                  imatrix old ?f x1...xn (fargs call))))
    (value (list old ?f x1...xn matrix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *solve-call-acl2-rewriter*
  :short "Name of the function (defined in a separate file)
          to call the ACL2 rewriter."
  'solve-call-acl2-rewriter)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *solve-call-axe-rewriter*
  :short "Name of the function (defined in a separate file)
          to call the Axe rewriter."
  'solve-call-axe-rewriter)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-process-method (method (method? booleanp) ctx state)
  :returns (mv erp (nothing null) state)
  :short "Process the @(':method') input."
  (cond ((eq method :acl2-rewriter)
         (if (function-symbolp *solve-call-acl2-rewriter* (w state))
             (value nil)
           (er-soft+
            ctx t nil
            "In order to use the ACL2 rewriter as the solving method ~
             it is necessary to include ~
             [books]/kestrel/apt/solve-method-acl2-rewriter.lisp.")))
        ((eq method :axe-rewriter)
         (if (function-symbolp *solve-call-axe-rewriter* (w state))
             (value nil)
           (er-soft+
            ctx t nil
            "In order to use the Axe rewriter as the solving method ~
             it is necessary to include ~
             kestrel-acl2/transformations/solve-method-axe-rewriter.lisp
             (available inside Kestrel).")))
        ((eq method :manual)
         (value nil))
        (method?
         (er-soft+ ctx t nil
                   "The :METHOD input must be ~
                    :ACL2-REWRITER, :AXE-REWRITER, or :MANUAL, ~
                    but it is ~x0 instead. ~
                    More methods will be supported in the future."
                   method))
        (t (er-soft+ ctx t nil "The :METHOD input must be supplied."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-process-method-rules (method-rules ctx state)
  :returns (mv erp (nothing null) state)
  :short "Process the @(':method-rules') input."
  :long
  (xdoc::topstring-p
   "For now we just check that it is a true list of symbols,
    but give this its own input processing function
    so that we may add further checks in the future.")
  (ensure-value-is-symbol-list$ method-rules "The :METHOD-RULES input" t nil)
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-symbol-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-process-solution-name (solution-name
                                     (method keywordp)
                                     (?f symbolp)
                                     (x1...xn symbol-listp)
                                     (verify-guards booleanp)
                                     (names-to-avoid symbol-listp)
                                     ctx
                                     state)
  :returns (mv erp
               (result "@('(tuple (f symbolp)
                                  (f-existsp booleanp)
                                  (updated-names-to-avoid symbol-listp))')")
               state)
  :mode :program
  :short "Process the @(':solution-name') input."
  (b* (((er &) (ensure-value-is-symbol$ solution-name
                                        "The :SOLUTION-NAME input"
                                        t
                                        nil)))
    (if (function-symbolp solution-name (w state))
        (b* (((unless (eq method :manual))
              (er-soft+ ctx t nil
                        "The :SOLUTION-NAME input specifies ~
                         an existing function, ~x0. ~
                         This is allowed only if ~
                         the :METHOD input is :MANUAL, ~
                         but it is ~x1 instead."
                        solution-name method))
             (desc (msg "The function ~x0 specified by the :SOLUTION-INPUT"
                        solution-name))
             ((er &) (ensure-function-logic-mode$ solution-name desc t nil))
             ((er &) (ensure-function-defined$ solution-name desc t nil))
             ((er &) (ensure-function-arity$ solution-name
                                             (len x1...xn)
                                             desc
                                             t
                                             nil))
             ((er &) (ensure-function-number-of-results$ solution-name
                                                         1
                                                         desc
                                                         t
                                                         nil))
             ((er &) (if verify-guards
                         (ensure-function-guard-verified$ solution-name
                                                          desc
                                                          t
                                                          nil)
                       (value nil))))
          (value (list solution-name t names-to-avoid)))
      (b* (((er f) (if (eq solution-name :auto)
                       (b* ((chars (explode (symbol-name ?f)))
                            ((unless (and (consp chars)
                                          (eql (car chars) #\?)))
                             (er-soft+ ctx t nil
                                       "The :SOLUTION-NAME input is :AUTO ~
                                        (perhaps by default). ~
                                        This is allowed only if ~
                                        the name of ~x0 starts with ?, ~
                                        but it does not."
                                       ?f)))
                         (value
                          (intern-in-package-of-symbol (implode (cdr chars))
                                                       ?f)))
                     (value solution-name)))
           ((er &)
            (ensure-symbol-is-fresh-event-name$ f
                                                (msg "The name ~x0 specified ~
                                                      (perhaps by default) ~
                                                      by :SOLUTION-NAME"
                                                     f)
                                                'function
                                                names-to-avoid
                                                t
                                                nil)))
        (value (list f nil names-to-avoid))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-process-solution-enable (solution-enable
                                       (solution-enable? booleanp)
                                       (f-existsp booleanp)
                                       ctx
                                       state)
  :returns (mv erp (nothing null) state)
  :short "Process the @(':solution-enable') input."
  (if (and solution-enable?
           f-existsp)
      (er-soft+ ctx t nil
                "Since the :SOLUTION-name input ~
                 specifies an existing function, ~
                 the :SOLUTION-ENABLE input must be absent.")
    (ensure-value-is-boolean$ solution-enable
                              "The :SOLUTION-ENABLE input"
                              t
                              nil))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-boolean)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-process-solution-guard (solution-guard
                                      (solution-guard? booleanp)
                                      (x1...xn symbol-listp)
                                      (f-existsp booleanp)
                                      ctx
                                      state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :mode :program
  :short "Process the @(':solution-guard') input."
  (b* (((when (and solution-guard?
                   f-existsp))
        (er-soft+ ctx t nil
                  "Since the :SOLUTION-NAME input ~
                   specifies an existing function, ~
                   the :SOLUTION-GUARD input must be absent."))
       ((er (list term stobjs-out))
        (ensure-value-is-untranslated-term$ solution-guard
                                            "The :SOLUTION-GUARD input"
                                            t
                                            nil))
       (description (msg "The :SOLUTION-GUARD term ~x0" solution-guard))
       ((er &) (ensure-function/lambda/term-number-of-results$ stobjs-out
                                                               1
                                                               description
                                                               t nil))
       ((er &) (ensure-term-free-vars-subset$ term
                                              x1...xn
                                              description
                                              t nil)))
    (value nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-process-solution-guard-hints (solution-guard-hints
                                            (solution-guard-hints? booleanp)
                                            (f-existsp booleanp)
                                            ctx
                                            state)
  :returns (mv erp (nothing null) state)
  :short "Process the @(':solution-guard-hints') input."
  :long
  (xdoc::topstring-p
   "For now we just check that this is a true list,
    which may be enough to catch simple mistakes.
    We may extend this input processor with more validity checks.")
  (if (and solution-guard-hints?
           f-existsp)
      (er-soft+ ctx t nil
                "Since the :SOLUTION-NAME input ~
                 specifies an existing function, ~
                 the :SOLUTION-GUARD-HINTS input must be absent.")
    (ensure-value-is-true-list$ solution-guard-hints
                                "The :SOLUTION-GUARD-HINTS input"
                                t
                                nil))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-true-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-process-solution-body (solution-body
                                     (solution-body? booleanp)
                                     (method keywordp)
                                     (x1...xn symbol-listp)
                                     (f-existsp booleanp)
                                     ctx
                                     state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :mode :program
  :short "Process the @(':solution-body') input."
  (if (eq method :manual)
      (if f-existsp
          (if solution-body?
              (er-soft+ ctx t nil
                        "Since the :SOLUTION-NAME input ~
                         specifies an existing function, ~
                         the :SOLUTION-BODY input must be absent, ~
                         but instead ~x0 has been supplied.")
            (value nil))
        (if (not solution-body?)
            (er-soft+ ctx t nil
                      "Since the :METHOD input is :MANUAL ~
                       and the :SOLUTION-NAME input specifies ~
                       the name of a function to be generated, ~
                       the :SOLUTION-BODY input must be supplied.")
          (b* (((er (list term stobjs-out))
                (ensure-value-is-untranslated-term$ solution-body
                                                    "The :SOLUTION-BODY input"
                                                    t
                                                    nil))
               (description (msg "The :SOLUTION-BODY term ~x0" solution-body))
               ((er &)
                (ensure-function/lambda/term-number-of-results$ stobjs-out
                                                                1
                                                                description
                                                                t
                                                                nil))
               ((er &) (ensure-term-free-vars-subset$ term
                                                      x1...xn
                                                      description
                                                      t nil)))
            (value nil))))
    (if solution-body?
        (er-soft+ ctx t nil
                  "Since the :METHOD input is not :MANUAL, ~
                   the :SOLUTION-BODY input must be absent, ~
                   but instead ~x0 has been supplied."
                  solution-body)
      (value nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-process-solution-hints (solution-hints
                                      (solution-hints? booleanp)
                                      (method keywordp)
                                      ctx
                                      state)
  :returns (mv erp (nothing null) state)
  :short "Process the @(':solution-hints') input."
  :long
  (xdoc::topstring-p
   "For now we just check that this is a true list,
    which may be enough to catch simple mistakes.
    We may extend this input processor with more validity checks.")
  (if (eq method :manual)
      (ensure-value-is-true-list$ solution-hints
                                  "The :SOLUTION-HINTS input"
                                  t nil)
    (if solution-hints?
        (er-soft+ ctx t nil
                  "Since the :METHOD input is not :MANUAL, ~
                   the :SOLUTION-HINTS input must be absent, ~
                   but instead ~x0 has been supplied."
                  solution-hints)
      (value nil)))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-true-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-process-inputs (old
                              method (method? booleanp)
                              method-rules
                              solution-name
                              solution-enable (solution-enable? booleanp)
                              solution-guard (solution-guard? booleanp)
                              solution-guard-hints (solution-guard-hints?
                                                    booleanp)
                              solution-body (solution-body? booleanp)
                              solution-hints (solution-hints? booleanp)
                              new-name
                              new-enable
                              old-if-new-name (old-if-new-name? booleanp)
                              old-if-new-enable (old-if-new-enable? booleanp)
                              verify-guards
                              print
                              show-only
                              ctx
                              state)
  :returns (mv erp
               (result "@('(tuple (old symbolp)
                                  (?f symbolp)
                                  (x1...xn symbol-listp)
                                  (matrix pseudo-termp)
                                  (f symbolp)
                                  (f-existsp symbolp)
                                  (new symbolp)
                                  (new-enable booleanp)
                                  (old-if-new symbolp)
                                  (old-if-new-enable booleanp)
                                  (verify-guards booleanp)
                                  (names-to-avoid symbol-listp))').")
               state)
  :mode :program
  :short "Process all the inputs."
  (b* ((names-to-avoid nil)
       ((er (list old ??f x1...xn matrix)) (solve-process-old old
                                                              verify-guards
                                                              ctx
                                                              state))
       ((er verify-guards) (process-input-verify-guards verify-guards
                                                        old
                                                        ctx
                                                        state))
       ((er &) (solve-process-method method method? ctx state))
       ((er &) (solve-process-method-rules method-rules ctx state))
       ((er (list f f-existsp names-to-avoid))
        (solve-process-solution-name solution-name
                                     method
                                     ?f
                                     x1...xn
                                     verify-guards
                                     names-to-avoid
                                     ctx
                                     state))
       ((er &) (solve-process-solution-enable solution-enable
                                              solution-enable?
                                              f-existsp
                                              ctx
                                              state))
       ((er &) (solve-process-solution-guard solution-guard
                                             solution-guard?
                                             x1...xn
                                             f-existsp
                                             ctx
                                             state))
       ((er &) (solve-process-solution-guard-hints solution-guard-hints
                                                   solution-guard-hints?
                                                   f-existsp
                                                   ctx
                                                   state))
       ((er &) (solve-process-solution-body solution-body
                                            solution-body?
                                            method
                                            x1...xn
                                            f-existsp
                                            ctx
                                            state))
       ((er &) (solve-process-solution-hints solution-hints
                                             solution-hints?
                                             method
                                             ctx
                                             state))
       ((er (list new names-to-avoid))
        (process-input-new-name new-name
                                old
                                names-to-avoid
                                ctx
                                state))
       ((er new-enable) (process-input-new-enable new-enable old ctx state))
       ((er (list old-if-new names-to-avoid))
        (process-input-old-if-new-name old-if-new-name
                                       old-if-new-name?
                                       old
                                       new
                                       names-to-avoid
                                       ctx
                                       state))
       ((er old-if-new-enable)
        (process-input-old-if-new-enable old-if-new-enable
                                         old-if-new-enable?
                                         ctx
                                         state))
       ((er &) (evmac-process-input-print print ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list old
                 ?f
                 x1...xn
                 matrix
                 f
                 f-existsp
                 new
                 new-enable
                 old-if-new
                 old-if-new-enable
                 verify-guards
                 names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation solve
                                    :some-local-nonlocal-p t
                                    :some-local-p t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-gen-solution-from-rewritten-term ((matrix pseudo-termp)
                                                (rewritten-term pseudo-termp)
                                                (?f symbolp)
                                                (x1...xn symbol-listp)
                                                ctx
                                                state)
  :returns (mv erp (f-body "A @(tsee pseudo-termp).") state)
  :short "Attempt to determine a solution from a rewritten term."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function is called after calling a rewriter
     (currently, the ACL2 and Axe rewriters are supported)
     on the matrix of the specification.
     The obtained rewritten term is passed to this function,
     which attempts to extract a solution from it.
     This extraction process does not depend on the particular rewriter,
     and thus it is factored in this function,
     which is always part of the transformation
     (unlike the functions to call the rewriters,
     which are in separately includable files.
     The matrix of the specification is passed to this function
     just for the purpose of being used in error messages.")
   (xdoc::p
    "The extraction process is as explained in the user documentation.
     We collect the leaves of the @(tsee if) tree,
     and remove all the @('t') ones from the list,
     since they do not contribute any constraints.
     If there are no more terms left, they were all @('t'),
     and thus we return @('nil') as the solution;
     anything else would be fine as well, but @('nil') is simple.
     If there is exactly one term left and it has the form
     @('(equal (?f x1 ... xn) term<x1,...,xn>)'),
     we return @('term<x1,...,xn>') as the solution.")
   (xdoc::p
    "The current strategy is somewhat restrictive;
     there are clearly (easy) ways to extract solutions
     from a wider range of forms of rewritten terms.
     There are plans to do that.")
   (xdoc::p
    "In the final error message, we use no evisceration
     so that the terms can always be seen in full.
     We do not expect these terms to be too large in the near future.
     If this changes, we may use some evisceration."))
  (b* ((leaf-terms (if-tree-leaf-terms rewritten-term))
       (leaf-terms (remove-equal *t* leaf-terms))
       ((when (not leaf-terms)) (value *nil*))
       (leaf-term (car leaf-terms))
       ((when (and (not (cdr leaf-terms)) ; LEAF-TERM is the only one remaining
                   (nvariablep leaf-term)
                   (not (fquotep leaf-term))
                   (eq (ffn-symb leaf-term) 'equal)
                   (= (len (fargs leaf-term)) 2)
                   (equal (fargn leaf-term 1) (fcons-term ?f x1...xn))))
        (value (fargn leaf-term 2))))
    (er-soft+ ctx t nil
              "The rewriter has rewritten the term ~X10 to ~X20, ~
               which does not determine a solution for ~x3 ~
               according to the user documentation. ~
               This transformation may be extended in the future ~
               to determine solutions in more cases than now."
              nil matrix rewritten-term ?f)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-gen-solution-acl2-rewriter ((matrix pseudo-termp)
                                          (?f symbolp)
                                          (x1...xn symbol-listp)
                                          (method-rules symbol-listp)
                                          ctx
                                          state)
  :returns (mv erp
               (result "A tuple @('(rewritten-term f-body used-rules)')
                        satisfying
                        @('(typed-tuplep pseudo-termp
                                         pseudo-termp
                                         symbol-listp
                                         result)').")
               state)
  :mode :program
  :short "Attempt to generate a solution,
          i.e. to solve @('old') for @('?f') using the ACL2 rewriter."
  :long
  (xdoc::topstring
   (xdoc::p
    "We reflectively call a function that calls the ACL2 rewriter.
     This function is in a separate file,
     which can be included, along with its dependency on @(tsee rewrite$),
     only if desired.
     The input validation performed by this transformation ensures that
     we call the function only if its file is included.")
   (xdoc::p
    "If the call is successful, we attempt to extract a solution,
     and we return it along with the rewritten term and the used rules."))
  (b* (((er (list rewritten-term used-rules))
        (trans-eval-error-triple `(,*solve-call-acl2-rewriter*
                                   ,@(kwote-lst (list matrix method-rules ctx))
                                   state)
                                 ctx
                                 state))
       ((er f-body) (solve-gen-solution-from-rewritten-term matrix
                                                            rewritten-term
                                                            ?f
                                                            x1...xn
                                                            ctx
                                                            state)))
    (value (list rewritten-term f-body used-rules))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-gen-solution-axe-rewriter ((matrix pseudo-termp)
                                         (?f symbolp)
                                         (x1...xn symbol-listp)
                                         (method-rules symbol-listp)
                                         ctx
                                         state)
  :returns (mv erp
               (result "A tuple @('(rewritten-term f-body)') satisfying
                        @('(typed-tuplep pseudo-termp pseudo-termp result)').")
               state)
  :mode :program
  :short "Attempt to generate a solution,
          i.e. to solve @('old') for @('?f') using the Axe rewriter."
  :long
  (xdoc::topstring-p
   "This is similar to @(tsee solve-gen-solution-acl2-rewriter).
    See its documentation.")
  (b* (((er rewritten-term)
        (trans-eval-error-triple `(,*solve-call-axe-rewriter*
                                   ,@(kwote-lst (list matrix method-rules ctx))
                                   state)
                                 ctx
                                 state))
       ((er f-body) (solve-gen-solution-from-rewritten-term matrix
                                                            rewritten-term
                                                            ?f
                                                            x1...xn
                                                            ctx
                                                            state)))
    (value (list rewritten-term f-body))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-gen-theorem-acl2-rewriter ((matrix pseudo-termp)
                                         (?f symbolp)
                                         (x1...xn symbol-listp)
                                         (rewritten-term pseudo-termp)
                                         (f-body pseudo-termp)
                                         (used-rules symbol-listp)
                                         (names-to-avoid symbol-listp)
                                         (wrld plist-worldp))
  :returns (mv (events "A @(tsee pseudo-event-form-listp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate a local theorem for
          the correctness of the solution found by the ACL2 rewriter."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @(tsee solve-gen-solution-acl2-rewriter) succeeds,
     it should be the case that
     the matrix of @('old') is equal to the rewritten term,
     but the ACL2 rewriter does not quite produce
     a replayable ACL2 proof of that.
     However, in order to prove the refinement theorem,
     we need an ACL2 theorem asserting that
     the matrix is equal to the rewritten term.")
   (xdoc::p
    "So here we attempt to generate a local theorem asserting that.
     The programmatic interface to the ACL2 rewriter returns
     the rules used by the rewriting.
     Thus, we attempt to prove the theorem
     in the theory consisting of these rules,
     assuming that ACL2 will perform the same rewrites in the theorem.
     Note, however, that the returned list of rules may include
     the ``fake'' rules for linear arithmetic and other proof methods.
     Thus, we use a utility to drop all of those.")
   (xdoc::p
    "For uniformity with other solving methods,
     we also generate a theorem of the form")
   (xdoc::codeblock
    "(implies (equal (?f x1 ... xn)"
    "                f-body)"
    "         term<(?f x1 ... xn)>)")
   (xdoc::p
    "(see the user documentation).
     This is why this function returns a list of events.
     The list has always length 2:
     the first event is a lemma about ACL2's rewriting;
     the second event is the main theorem @('matrix<f-body>')."))
  (b* (((mv lemma-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'acl2-rewriting-correct
                                           nil
                                           names-to-avoid
                                           wrld))
       (used-rules (acl2::drop-fake-runes used-rules))
       (lemma-event
        `(local
          (defthmd ,lemma-name
            (equal ,matrix ,rewritten-term)
            :hints (("Goal" :in-theory ',used-rules)))))
       ((mv main-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'solution-correct
                                           nil
                                           names-to-avoid
                                           wrld))
       (main-event
        `(local
          (defthmd ,main-name
            (implies (equal (,?f ,@x1...xn)
                            ,f-body)
                     ,matrix)
            :hints (("Goal" :in-theory nil :use ,lemma-name))))))
    (mv (list lemma-event main-event)
        main-name
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-gen-theorem-axe-rewriter ((matrix pseudo-termp)
                                        (?f symbolp)
                                        (x1...xn symbol-listp)
                                        (rewritten-term pseudo-termp)
                                        (f-body pseudo-termp)
                                        (method-rules symbol-listp)
                                        (names-to-avoid symbol-listp)
                                        (wrld plist-worldp))
  :returns (mv (events "A @(tsee pseudo-event-form-listp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate a local theorem for
          the correctness of the solution found by the Axe rewriter."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @(tsee solve-gen-solution-axe-rewriter) succeeds,
     it should be the case that
     the matrix of @('old') is equal to the rewritten term,
     but the Axe rewriter does not produce a replayable ACL2 proof of that.
     However, in order to prove the refinement theorem,
     we need an ACL2 theorem asserting that
     the matrix is equal to the rewritten term.")
   (xdoc::p
    "So here we attempt to generate a local theorem asserting that.
     Our proof strategy is fairly crude for now:
     we simply enable the rules passed to the Axe rewriter,
     hoping that ACL2 can perform the same rewritings.
     We add these to the current ACL2 theory,
     just in case we may need some other basic rules.
     Clearly, this strategy should be refined significantly.")
   (xdoc::p
    "For uniformity with other solving methods,
     we also generate a theorem of the form")
   (xdoc::codeblock
    "(implies (equal (?f x1 ... xn)"
    "                f-body)"
    "         term<(?f x1 ... xn)>)")
   (xdoc::p
    "(see the user documentation).
     This is why this function returns a list of events.
     The list has always length 2:
     the first event is a lemma about Axe's rewriting;
     the second event is the main theorem @('matrix<f-body>')."))
  (b* (((mv lemma-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'axe-rewriting-correct
                                           nil
                                           names-to-avoid
                                           wrld))
       (lemma-event
        `(local
          (defthmd ,lemma-name
            (equal ,matrix ,rewritten-term)
            :hints (("Goal" :in-theory (enable ,@method-rules))))))
       ((mv main-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'solution-correct
                                           nil
                                           names-to-avoid
                                           wrld))
       (main-event
        `(local
          (defthmd ,main-name
            (implies (equal (,?f ,@x1...xn)
                            ,f-body)
                     ,matrix)
            :hints (("Goal" :in-theory nil :use ,lemma-name))))))
    (mv (list lemma-event main-event)
        main-name
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-gen-solution-and-theorem ((matrix pseudo-termp)
                                        (?f symbolp)
                                        (x1...xn symbol-listp)
                                        (method keywordp)
                                        (method-rules symbol-listp)
                                        (solution-body "An untranslated term.")
                                        (solution-hints true-listp)
                                        (names-to-avoid symbol-listp)
                                        ctx
                                        state)
  :returns (mv erp
               (result "A tuple @('(f-body
                                    solution-correct-events
                                    solution-correct
                                    updated-names-to-avoid)')
                        satisfying @('(typed-tuplep pseudo-termp
                                                    pseudo-event-form-listp
                                                    symbolp
                                                    symbol-listp)').")
               state)
  :mode :program
  :short "Attempt to generate a solution, and a theorem for its correctness."
  :long
  (xdoc::topstring-p
   "This is used when @('f-existsp') is @('nil').")
  (cond ((eq method :acl2-rewriter)
         (b* (((er (list rewritten-term f-body used-rules))
               (solve-gen-solution-acl2-rewriter matrix
                                                 ?f
                                                 x1...xn
                                                 method-rules
                                                 ctx
                                                 state))
              ((mv solution-correct-events solution-correct names-to-avoid)
               (solve-gen-theorem-acl2-rewriter matrix
                                                ?f
                                                x1...xn
                                                rewritten-term
                                                f-body
                                                used-rules
                                                names-to-avoid
                                                (w state))))
           (value (list f-body
                        solution-correct-events
                        solution-correct
                        names-to-avoid))))
        ((eq method :axe-rewriter)
         (b* (((er (list rewritten-term f-body))
               (solve-gen-solution-axe-rewriter matrix
                                                ?f
                                                x1...xn
                                                method-rules
                                                ctx
                                                state))
              ((mv solution-correct-events solution-correct names-to-avoid)
               (solve-gen-theorem-axe-rewriter matrix
                                               ?f
                                               x1...xn
                                               rewritten-term
                                               f-body
                                               method-rules
                                               names-to-avoid
                                               (w state))))
           (value (list f-body
                        solution-correct-events
                        solution-correct
                        names-to-avoid))))
        ((eq method :manual)
         (b* ((f-body solution-body)
              ((mv thm-name names-to-avoid)
               (fresh-logical-name-with-$s-suffix 'solution-correct
                                                  nil
                                                  names-to-avoid
                                                  (w state)))
              (thm-event
               `(local
                 (defthmd ,thm-name
                   (implies (equal (,?f ,@x1...xn)
                                   ,f-body)
                            ,matrix)
                   :hints ,solution-hints))))
           (value (list f-body
                        (list thm-event)
                        thm-name
                        names-to-avoid))))
        (t (value (raise "Internal error: unknown method ~x0." method)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-gen-f ((f symbolp)
                     (x1...xn symbol-listp)
                     (f-body pseudo-termp)
                     (solution-guard "An untranslated term.")
                     (solution-guard-hints true-listp)
                     (solution-enable booleanp)
                     (verify-guards booleanp)
                     (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the @('f') function."
  (evmac-generate-defun f
                        :formals x1...xn
                        :body (untranslate f-body nil wrld)
                        :enable solution-enable
                        :guard solution-guard
                        :guard-hints solution-guard-hints
                        :verify-guards verify-guards))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-gen-theorem-for-solution ((matrix pseudo-termp)
                                        (?f symbolp)
                                        (x1...xn symbol-listp)
                                        (f symbolp)
                                        (solution-hints true-listp)
                                        (names-to-avoid symbol-listp)
                                        (wrld plist-worldp))
  :returns (mv (solution-correct-event "A @(tsee pseudo-event-formp).")
               (solution-correct "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Attempt to generate a theorem for the supplied solution."
  :long
  (xdoc::topstring-p
   "This is used when @('f-existsp') is @('t').
    In this case, @('f') is not generated (it already exists),
    so we only generate the theorem asserting its correctness
    (see the user documentation).")
  (b* (((mv thm-name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'solution-correct
                                           nil
                                           names-to-avoid
                                           wrld))
       (thm-event
        `(local
          (defthmd ,thm-name
            (implies (equal (,?f ,@x1...xn)
                            (,f ,@x1...xn))
                     ,matrix)
            :hints ,solution-hints))))
    (mv thm-event thm-name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-gen-solution ((?f symbolp)
                            (x1...xn symbol-listp)
                            (matrix pseudo-termp)
                            (method keywordp)
                            (method-rules symbol-listp)
                            (f symbolp)
                            (f-existsp booleanp)
                            (solution-enable booleanp)
                            (solution-guard "An untranslated term.")
                            (solution-guard-hints true-listp)
                            (solution-body "An untranslated term.")
                            (solution-hints true-listp)
                            (verify-guards booleanp)
                            (names-to-avoid symbol-listp)
                            ctx
                            state)
  :returns (mv erp
               (result "@('(tuple (local-events pseudo-form-listp)
                                  (exported-events pseudo-form-listp)
                                  (solution-correct symbolp))')")
               state)
  :mode :program
  :short "Attempt to generate the events that provide the solution."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are events that depend on the solving method.
     In contrast, the event for @('new') and @('old-if-new')
     are the same for every method."))
  (b* ((wrld (w state))
       ((er (list f-body? solution-correct-events solution-correct))
        (if f-existsp
            (b* (((mv solution-correct-event solution-correct &)
                  (solve-gen-theorem-for-solution matrix
                                                  ?f
                                                  x1...xn
                                                  f
                                                  solution-hints
                                                  names-to-avoid
                                                  wrld)))
              (value (list (list solution-correct-event) solution-correct)))
          (b* (((er (list f-body solution-correct-events solution-correct &))
                (solve-gen-solution-and-theorem matrix
                                                ?f
                                                x1...xn
                                                method
                                                method-rules
                                                solution-body
                                                solution-hints
                                                names-to-avoid
                                                ctx
                                                state)))
            (value (list f-body solution-correct-events solution-correct)))))
       ((mv f-local-event? f-exported-event?)
        (if f-existsp
            (mv nil nil)
          (solve-gen-f f
                       x1...xn
                       f-body?
                       solution-guard
                       solution-guard-hints
                       solution-enable
                       verify-guards
                       wrld))))
    (value (list (append solution-correct-events
                         (and f-local-event? (list f-local-event?)))
                 (and f-exported-event? (list f-exported-event?))
                 solution-correct))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-gen-new ((new symbolp)
                       (new-enable booleanp)
                       (x1...xn symbol-listp)
                       (?f symbolp)
                       (f symbolp)
                       (verify-guards booleanp))
  :returns (event pseudo-event-formp)
  :short "Generate the @('new') function."
  `(soft::defequal ,new
                   :left ,?f
                   :right ,f
                   :vars ,x1...xn
                   :enable ,new-enable
                   :verify-guards ,verify-guards))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-gen-old-if-new ((old-if-new symbolp)
                              (old-if-new-enable booleanp)
                              (old symbolp)
                              (?f symbolp)
                              (x1...xn symbol-listp)
                              (new symbolp)
                              (f-existsp booleanp)
                              (f symbolp)
                              (solution-correct symbolp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the @('old-if-new') theorem."
  :long
  (xdoc::topstring-p
   "In the generated hints, we enable @('f') (by including it in the theory)
    if @('f') is generated, because in that case
    the theorem @('solution-correct') mentions its body, not @('f').
    If instead @('f') already exists,
    the theorem @('solution-correct') mentions @('f'), as does @('new'),
    and so there is no need to enable it
    (and in fact, enabling it might even sabotage the proof).")
  (b* ((formula `(implies (,new) (,old)))
       (new-rwrule (packn-pos (list ?f '-to- f) new))
       (old-witness (add-suffix-to-fn old "-WITNESS"))
       (instantiation (if (>= (len x1...xn) 2)
                          (solve-gen-old-if-new-thm-aux x1...xn 0 old-witness)
                        `((,(car x1...xn) (,old-witness)))))
       (theory (if f-existsp
                   (list old new-rwrule)
                 (list old new-rwrule f)))
       (hints `(("Goal"
                 :in-theory ',theory
                 :use (:instance ,solution-correct ,@instantiation)))))
    (evmac-generate-defthm old-if-new
                           :enable old-if-new-enable
                           :formula formula
                           :hints hints))

  :prepwork
  ((define solve-gen-old-if-new-thm-aux ((vars symbol-listp)
                                         (index natp)
                                         (old-witness symbolp))
     :returns (instantiation doublet-listp)
     (cond ((endp vars) nil)
           (t (cons `(,(car vars) (mv-nth ,index (,old-witness)))
                    (solve-gen-old-if-new-thm-aux (cdr vars)
                                                  (1+ index)
                                                  old-witness)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-gen-everything ((old symbolp)
                              (?f symbolp)
                              (x1...xn symbol-listp)
                              (matrix pseudo-termp)
                              (method keywordp)
                              (method-rules symbol-listp)
                              (f symbolp)
                              (f-existsp booleanp)
                              (solution-enable booleanp)
                              (solution-guard "An untranslated term.")
                              (solution-guard-hints true-listp)
                              (solution-body "An untranslated term.")
                              (solution-hints true-listp)
                              (new symbolp)
                              (new-enable booleanp)
                              (old-if-new symbolp)
                              (old-if-new-enable booleanp)
                              (verify-guards booleanp)
                              (print evmac-input-print-p)
                              (show-only booleanp)
                              (call pseudo-event-formp)
                              (names-to-avoid symbol-listp)
                              ctx
                              state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :short "Generate the top-level event."
  (b* ((wrld (w state))
       ((er (list solution-local-events
                  solution-exported-events
                  solution-correct))
        (solve-gen-solution ?f
                            x1...xn
                            matrix
                            method
                            method-rules
                            f
                            f-existsp
                            solution-enable
                            solution-guard
                            solution-guard-hints
                            solution-body
                            solution-hints
                            verify-guards
                            names-to-avoid
                            ctx
                            state))
       (new-event (solve-gen-new new new-enable x1...xn ?f f verify-guards))
       ((mv old-if-new-local-event old-if-new-exported-event)
        (solve-gen-old-if-new old-if-new
                              old-if-new-enable
                              old
                              ?f
                              x1...xn
                              new
                              f-existsp
                              f
                              solution-correct))
       (encapsulate-events
        `((logic)
          (evmac-prepare-proofs)
          (set-ignore-ok t)
          (set-irrelevant-formals-ok t)
          ,@solution-local-events
          ,@solution-exported-events
          ,new-event
          ,old-if-new-local-event
          ,old-if-new-exported-event))
       (encapsulate `(encapsulate () ,@encapsulate-events))
       ((when show-only)
        (if (member-eq print '(:info :all))
            (cw "~%~x0~|" encapsulate)
          (cw "~x0~|" encapsulate))
        (value '(value-triple :invisible)))
       (encapsulate+ (restore-output? (eq print :all) encapsulate))
       (transformation-table-event (record-transformation-call-event
                                    call encapsulate wrld))
       (print-result (and
                      (member-eq print '(:result :info :all))
                      `(,@(and (member-eq print '(:info :all))
                               '((cw-event "~%")))
                        ,@(and (not f-existsp)
                               `((cw-event "~x0~|"
                                           ',(car solution-exported-events))))
                        (cw-event "~x0~|" ',new-event)
                        (cw-event "~x0~|" ',old-if-new-exported-event)))))
    (value
     `(progn
        ,encapsulate+
        ,transformation-table-event
        ,@print-result
        (value-triple :invisible)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define solve-fn (old
                  method (method? booleanp)
                  method-rules
                  solution-name
                  solution-enable (solution-enable? booleanp)
                  solution-guard (solution-guard? booleanp)
                  solution-guard-hints (solution-guard-hints? booleanp)
                  solution-body (solution-body? booleanp)
                  solution-hints (solution-hints? booleanp)
                  new-name
                  new-enable
                  old-if-new-name (old-if-new-name? booleanp)
                  old-if-new-enable (old-if-new-enable? booleanp)
                  verify-guards
                  print
                  show-only
                  (call pseudo-event-formp)
                  ctx
                  state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :parents (solve-implementation)
  :short "Check redundancy, process the inputs, and generate the event."
  (b* ((encapsulate? (previous-transformation-expansion call (w state)))
       ((when encapsulate?)
        (b* (((run-when show-only) (cw "~x0~|" encapsulate?)))
          (cw "~%The transformation ~x0 is redundant.~%" call)
          (value '(value-triple :invisible))))
       ((er (list old
                  ??f
                  x1...xn
                  matrix
                  f
                  f-existsp
                  new
                  new-enable
                  old-if-new
                  old-if-new-enable
                  verify-guards
                  names-to-avoid))
        (solve-process-inputs old
                              method method?
                              method-rules
                              solution-name
                              solution-enable solution-enable?
                              solution-guard solution-guard?
                              solution-guard-hints solution-guard-hints?
                              solution-body solution-body?
                              solution-hints solution-hints?
                              new-name
                              new-enable
                              old-if-new-name old-if-new-name?
                              old-if-new-enable old-if-new-enable?
                              verify-guards
                              print
                              show-only
                              ctx
                              state))
       ((er event) (solve-gen-everything old
                                         ?f
                                         x1...xn
                                         matrix
                                         method
                                         method-rules
                                         f
                                         f-existsp
                                         solution-enable
                                         solution-guard
                                         solution-guard-hints
                                         solution-body
                                         solution-hints
                                         new
                                         new-enable
                                         old-if-new
                                         old-if-new-enable
                                         verify-guards
                                         print
                                         show-only
                                         call
                                         names-to-avoid
                                         ctx
                                         state)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection solve-macro-definition
  :parents (solve-implementation)
  :short "Definition of the @(tsee solve) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Submit the event form generated by @(tsee solve-fn).")
   (xdoc::@def "solve"))
  (defmacro solve (&whole
                   call
                   ;; mandatory inputs:
                   old
                   ;; optional inputs:
                   &key
                   (method ':no-default method?)
                   (method-rules 'nil)
                   (solution-name ':auto)
                   (solution-enable 'nil solution-enable?)
                   (solution-guard 't solution-guard?)
                   (solution-guard-hints 'nil solution-guard-hints?)
                   (solution-body ':no-default solution-body?)
                   (solution-hints 'nil solution-hints?)
                   (new-name ':auto)
                   (new-enable ':auto)
                   (old-if-new-name ':irrelevant old-if-new-name?)
                   (old-if-new-enable ':irrelevant old-if-new-enable?)
                   (verify-guards ':auto)
                   (print ':result)
                   (show-only 'nil))
    `(make-event-terse (solve-fn ',old
                                 ',method
                                 ',method?
                                 ',method-rules
                                 ',solution-name
                                 ',solution-enable
                                 ',solution-enable?
                                 ',solution-guard
                                 ',solution-guard?
                                 ',solution-guard-hints
                                 ',solution-guard-hints?
                                 ',solution-body
                                 ',solution-body?
                                 ',solution-hints
                                 ',solution-hints?
                                 ',new-name
                                 ',new-enable
                                 ',old-if-new-name
                                 ',old-if-new-name?
                                 ',old-if-new-enable
                                 ',old-if-new-enable?
                                 ',verify-guards
                                 ',print
                                 ',show-only
                                 ',call
                                 (cons 'solve ',old)
                                 state)
                       :suppress-errors ,(not print))))
