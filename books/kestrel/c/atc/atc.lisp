; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")
(include-book "pretty-printer" :ttags ((:open-output-channel!)))
(include-book "static-semantics")
(include-book "dynamic-semantics")
(include-book "proof-support")
(include-book "proof-support-alternative")

(include-book "kestrel/error-checking/ensure-function-is-defined" :dir :system)
(include-book "kestrel/error-checking/ensure-function-is-guard-verified" :dir :system)
(include-book "kestrel/error-checking/ensure-function-is-logic-mode" :dir :system)
(include-book "kestrel/error-checking/ensure-symbol-is-fresh-event-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-function-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-string" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/std/system/check-mbt-call" :dir :system)
(include-book "kestrel/std/system/check-mbt-dollar-call" :dir :system)
(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "kestrel/std/system/maybe-pseudo-event-formp" :dir :system)
(include-book "kestrel/std/system/table-alist-plus" :dir :system)
(include-book "kestrel/std/system/ubody-plus" :dir :system)
(include-book "kestrel/std/system/uguard-plus" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)
(include-book "oslib/dirname" :dir :system)
(include-book "oslib/file-types" :dir :system)

(local (include-book "kestrel/std/system/flatten-ands-in-lit" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 atc

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  "@('fn1...fnp') is the list @('(fn1 ... fnp)') of inputs to @(tsee atc)."

  "@('fn') is one of the symbols in @('fn1...fnp')."

  "@('fns') is @('fn1...fnp') or a suffix of it."

  "@('vars') is an alist from ACL2 variable symbols to C types.
   These are the variables in scope
   for the ACL2 term whose code is being generated."

  "@('prec-fns') is an alist from ACL2 function symbols to C types.
   The function symbols are the ones in @('fn1...fnp') that precede,
   in the latter list,
   the symbol @('fn') in @('fn1...fnp') for which code is being generated;
   @('fn') is often also a parameter of
   the ATC function that has @('prec-fns') as parameter.
   According to the restrictions stated in the ATC user documentation,
   @('prec-fns') consists of the target function symbols
   that @('fn') is allowed to call.
   The type associated to each symbol is the C result type of the function."

  (xdoc::evmac-topic-implementation-item-input "const-name")

  (xdoc::evmac-topic-implementation-item-input "output-file")

  xdoc::*evmac-topic-implementation-item-call*

  "@('const') is the symbol specified by @('const-name')."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing atc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-function (fn ctx state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :short "Process a target function @('fni') among @('fn1'), ..., @('fnp')."
  (b* ((desc (msg "The target ~x0 input" fn))
       ((er &) (acl2::ensure-value-is-function-name$ fn desc t nil))
       (desc (msg "The target function ~x0" fn))
       ((er &) (acl2::ensure-function-is-logic-mode$ fn desc t nil))
       ((er &) (acl2::ensure-function-is-guard-verified$ fn desc t nil))
       ((er &) (acl2::ensure-function-is-defined$ fn desc t nil)))
    (value nil))
  :guard-hints (("Goal" :in-theory (enable
                                    acl2::ensure-value-is-function-name
                                    acl2::ensure-function-is-guard-verified
                                    acl2::ensure-function-is-logic-mode))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-function-list ((fns true-listp) ctx state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :short "Lift @(tsee atc-process-function) to lists."
  (b* (((when (endp fns)) (value nil))
       ((er &) (atc-process-function (car fns) ctx state)))
    (atc-process-function-list (cdr fns) ctx state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-fn1...fnp ((fn1...fnp true-listp) ctx state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :verify-guards nil
  :short "Process the target functions @('fn1'), ..., @('fnp')."
  (b* (((er &) (atc-process-function-list fn1...fnp ctx state))
       ((unless (consp fn1...fnp))
        (er-soft+ ctx t nil
                  "At least one target function must be supplied.")))
    (value nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-const-name (const-name ctx state)
  :returns (mv erp (const "A @(tsee symbolp).") state)
  :mode :program
  :short "Process the @(':const-name') input."
  (b* (((er &) (acl2::ensure-value-is-symbol$ const-name
                                              "The :CONST-NAME input"
                                              t
                                              nil))
       (name (if (eq const-name :auto)
                 'c::*program*
               const-name))
       ((er &) (acl2::ensure-symbol-is-fresh-event-name$
                name
                (msg "The constant name ~x0 ~
                      specified by the :CONST-NAME input"
                     name)
                'const
                nil
                t
                nil)))
    (value name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-output-file (output-file
                                 (output-file? booleanp)
                                 ctx
                                 state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :mode :program
  :short "Process the @(':output-file') input."
  (b* (((unless output-file?)
        (er-soft+ ctx t nil
                  "The :OUTPUT-FILE input must be present, ~
                   but it is absent instead."))
       ((er &) (acl2::ensure-value-is-string$ output-file
                                              "The :OUTPUT-FILE input"
                                              t
                                              nil))
       ((mv msg? dirname state) (oslib::dirname output-file))
       ((when msg?) (er-soft+ ctx t nil
                              "No directory path can be obtained ~
                               from the output file path ~x0. ~@1"
                              output-file msg?))
       ((er &)
        (if (equal dirname "")
            (value nil)
          (b* (((mv msg? kind state) (oslib::file-kind dirname))
               ((when msg?) (er-soft+ ctx t nil
                                      "The kind of ~
                                       the output directory path ~x0 ~
                                       cannot be tested. ~@1"
                                      dirname msg?))
               ((unless (eq kind :directory))
                (er-soft+ ctx t nil
                          "The output directory path ~x0 ~
                           is not a directory; it has kind ~x1 instead."
                          dirname kind)))
            (value nil))))
       ((mv msg? basename state) (oslib::basename output-file))
       ((when msg?) (er-soft+ ctx t nil
                              "No file name can be obtained ~
                               from the output file path ~x0. ~@1"
                              output-file msg?))
       ((unless (and (>= (length basename) 2)
                     (equal (subseq basename
                                    (- (length basename) 2)
                                    (length basename))
                            ".c")))
        (er-soft+ ctx t nil
                  "The file name ~x0 of the output path ~x1 ~
                   must have extension '.c', but it does not."
                  basename output-file))
       ((mv msg? existsp state) (oslib::path-exists-p output-file))
       ((when msg?) (er-soft+ ctx t nil
                              "The existence of the output path ~x0 ~
                               cannot be tested. ~@1"
                              output-file msg?))
       ((when (not existsp)) (value nil))
       ((mv msg? kind state) (oslib::file-kind output-file))
       ((when msg?) (er-soft+ ctx t nil
                              "The kind of output file path ~x0 ~
                               cannot be tested. ~@1"
                              output-file msg?))
       ((unless (eq kind :regular-file))
        (er-soft+ ctx t nil
                  "The output file path ~x0 ~
                   is not a regular file; it has kind ~x1 instead."
                  output-file kind)))
    (value nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-allowed-options*
  :short "Keyword options accepted by @(tsee atc)."
  (list :const-name
        :output-file
        :verbose)
  ///
  (assert-event (symbol-listp *atc-allowed-options*))
  (assert-event (no-duplicatesp-eq *atc-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-inputs ((args true-listp) ctx state)
  :returns (mv erp
               (val "A @('(tuple (fn1...fnp symbol-listp)
                                 (const symbolp)
                                 (output-file stringp)
                                 (verbose booleanp)
                                 val)').")
               state)
  :mode :program
  :short "Process all the inputs."
  (b* (((mv erp fn1...fnp options)
        (partition-rest-and-keyword-args args *atc-allowed-options*))
       ((when erp) (er-soft+ ctx t nil
                             "The inputs must be the names of ~
                              one or more target functions ~
                              followed by the options ~&0."
                             *atc-allowed-options*))
       (const-name-option (assoc-eq :const-name options))
       (const-name (if const-name-option
                       (cdr const-name-option)
                     :auto))
       (output-file-option (assoc-eq :output-file options))
       ((mv output-file output-file?)
        (if output-file-option
            (mv (cdr output-file-option) t)
          (mv :irrelevant nil)))
       (verbose-option (assoc-eq :verbose options))
       (verbose (if verbose-option
                    (cdr verbose-option)
                  t))
       ((er &) (atc-process-fn1...fnp fn1...fnp ctx state))
       ((er const) (atc-process-const-name const-name ctx state))
       ((er &) (atc-process-output-file output-file
                                        output-file?
                                        ctx
                                        state))
       ((er &) (acl2::ensure-value-is-boolean$ verbose
                                               "The :VERBOSE input"
                                               t
                                               nil)))
    (value (list fn1...fnp
                 const
                 output-file
                 verbose))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-table
  :parents (atc-implementation)
  :short "Table of @(tsee atc) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every successful call of @(tsee atc) is recorded in a table.
     This is used to support redundancy checking (see @(tsee atc-fn))."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-table*
  :short "Name of the table of @(tsee atc) calls."
  'atc-table)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate atc-call-info
  :short "Information associated to an @(tsee atc) call
          in the table of @(tsee atc) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only record the generated encapsulate.
     More information may be recorded in the future."))
  ((encapsulate pseudo-event-formp))
  :pred atc-call-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-maybe-call-infop (x)
  :short "Optional information associated to an @(tsee atc) call
          in the table of @(tsee atc) calls."
  (or (atc-call-infop x)
      (eq x nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-table-definition
  :short "Definition of the table of @(tsee atc) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "The keys of the table are calls of @(tsee atc).
     The values of the table are the associated information."))

  (make-event
   `(table ,*atc-table* nil nil
      :guard (and (pseudo-event-formp acl2::key)
                  (atc-call-infop acl2::val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-table-lookup ((call pseudo-event-formp) (wrld plist-worldp))
  :returns (info? atc-maybe-call-infop)
  :short "Look up an @(tsee atc) call in the table."
  (b* ((table (acl2::table-alist+ *atc-table* wrld))
       (info? (cdr (assoc-equal call table))))
    (if (atc-maybe-call-infop info?)
        info?
      (raise "Internal error: value ~x0 of key ~x1 in the ATC table.")))
  :prepwork ((local (include-book "std/alists/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-table-record-event ((call pseudo-event-formp) (info atc-call-infop))
  :returns (event pseudo-event-formp)
  :short "Event to update the table of @(tsee atc) calls."
  `(table ,*atc-table* ',call ',info))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-event-and-code-generation
  :parents (atc-implementation)
  :short "Event generation and code generation performed by @(tsee atc)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate C abstract syntax,
     which we pretty-print to a file
     and also assign to a named constant..")
   (xdoc::p
    "Given the restrictions on the target functions,
     the translation is straightforward -- intentionally so.")
   (xdoc::p
    "Some events are generated in two slightly different variants:
     one that is local to the generated @(tsee encapsulate),
     and one that is exported from the  @(tsee encapsulate).
     Proof hints are in the former but not in the latter,
     thus keeping the ACL2 history ``clean'';
     some proof hints may refer to events
     that are generated only locally to the @(tsee encapsulate)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist atc-symbol-tyspecseq-alistp (x)
  :short "Recognize alists from symbols to type specifier sequences."
  :key (symbolp x)
  :val (tyspecseqp x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  ///

  (defrule tyspecseqp-of-cdr-of-assoc-equal
    (implies (and (atc-symbol-tyspecseq-alistp x)
                  (assoc-equal k x))
             (tyspecseqp (cdr (assoc-equal k x)))))

  (defruled alistp-when-atc-symbol-tyspecseq-alistp-rewrite
    (implies (atc-symbol-tyspecseq-alistp x)
             (alistp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-sint-const ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (val acl2::sbyte32p))
  :short "Check if a term represents an @('int') constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of @(tsee sint-const) on a quoted integer constant
     whose value is non-negative and representable as an @('int'),
     we return the value.
     This way, the caller can generate the appropriate C integer constant."))
  (case-match term
    (('sint-const ('quote val))
     (if (and (natp val)
              (acl2::sbyte32p val))
         (mv t val)
       (mv nil 0)))
    (& (mv nil 0)))
  ///
  (defret natp-of-atc-check-sint-const
    (natp val)
    :rule-classes :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-sint-unop ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (op unopp)
               (arg pseudo-termp :hyp :guard)
               (type tyspecseqp))
  :short "Check if a term represents
          an @('int') unary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C unary operators,
     we return the operator and the argument term.
     This way, the caller can translate the argument term to a C expression
     and apply the operator to the expression.")
   (xdoc::p
    "We also return the result C type of the operator.
     This is always @('int') for now, but it will be generalized.")
   (xdoc::p
    "If the term does not have that form, we return an indication of failure.
     The term may represent some other kind of C expression."))
  (case-match term
    ((fn arg)
     (case fn
       (sint-plus (mv t (unop-plus) arg (tyspecseq-sint)))
       (sint-minus (mv t (unop-minus) arg (tyspecseq-sint)))
       (sint-bitnot (mv t (unop-bitnot) arg (tyspecseq-sint)))
       (sint-lognot (mv t (unop-lognot) arg (tyspecseq-sint)))
       (t (mv nil (irr-unop) nil (irr-tyspecseq)))))
    (& (mv nil (irr-unop) nil (irr-tyspecseq))))
  ///

  (defret acl2-count-of-atc-check-sint-unop-arg
    (implies yes/no
             (< (acl2-count arg)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-sint-binop ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (op binopp)
               (arg1 pseudo-termp :hyp :guard)
               (arg2 pseudo-termp :hyp :guard)
               (type tyspecseqp))
  :short "Check if a term represents
          an @('int') non-side-effecting binary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C non-side-effecting binary operators,
     we return the operator and the argument terms.
     This way, the caller can translate the argument terms to C expressions
     and apply the operator to the expressions.")
   (xdoc::p
    "Note that when @('&&') and @('||') are represented this way,
     their ACL2 representation is strict,
     which may be acceptable in some cases.")
   (xdoc::p
    "We also return the result C type of the operator.
     This is always @('int') for now, but it will be generalized.")
   (xdoc::p
    "If the term does not have that form, we return an indication of failure.
     The term may represent some other kind of C expression."))
  (case-match term
    ((fn arg1 arg2)
     (case fn
       (sint-add (mv t (binop-add) arg1 arg2 (tyspecseq-sint)))
       (sint-sub (mv t (binop-sub) arg1 arg2 (tyspecseq-sint)))
       (sint-mul (mv t (binop-mul) arg1 arg2 (tyspecseq-sint)))
       (sint-div (mv t (binop-div) arg1 arg2 (tyspecseq-sint)))
       (sint-rem (mv t (binop-rem) arg1 arg2 (tyspecseq-sint)))
       (sint-shl-sint (mv t (binop-shl) arg1 arg2 (tyspecseq-sint)))
       (sint-shr-sint (mv t (binop-shr) arg1 arg2 (tyspecseq-sint)))
       (sint-lt (mv t (binop-lt) arg1 arg2 (tyspecseq-sint)))
       (sint-le (mv t (binop-le) arg1 arg2 (tyspecseq-sint)))
       (sint-gt (mv t (binop-gt) arg1 arg2 (tyspecseq-sint)))
       (sint-ge (mv t (binop-ge) arg1 arg2 (tyspecseq-sint)))
       (sint-eq (mv t (binop-eq) arg1 arg2 (tyspecseq-sint)))
       (sint-ne (mv t (binop-ne) arg1 arg2 (tyspecseq-sint)))
       (sint-bitand (mv t (binop-bitand) arg1 arg2 (tyspecseq-sint)))
       (sint-bitxor (mv t (binop-bitxor) arg1 arg2 (tyspecseq-sint)))
       (sint-bitior (mv t (binop-bitior) arg1 arg2 (tyspecseq-sint)))
       (sint-logand (mv t (binop-logand) arg1 arg2 (tyspecseq-sint)))
       (sint-logor (mv t (binop-logor) arg1 arg2 (tyspecseq-sint)))
       (t (mv nil (irr-binop) nil nil (irr-tyspecseq)))))
    (& (mv nil (irr-binop) nil nil (irr-tyspecseq))))
  ///

  (defret acl2-count-of-atc-check-sint-binop-arg1
    (implies yes/no
             (< (acl2-count arg1)
                (acl2-count term)))
    :rule-classes :linear)

  (defret acl2-count-of-atc-check-sint-binop-arg2
    (implies yes/no
             (< (acl2-count arg2)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-callable-fn ((term pseudo-termp)
                               (prec-fns atc-symbol-tyspecseq-alistp))
  :returns (mv (yes/no booleanp)
               (fn symbolp :hyp (atc-symbol-tyspecseq-alistp prec-fns))
               (args pseudo-term-listp :hyp (pseudo-termp term))
               (type tyspecseqp))
  :short "Check if a term represents a call to a callable target function."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the check is successful, we return
     the called function along with the arguments.
     We also return the result type of the function."))
  (case-match term
    ((fn . args) (b* (((unless (symbolp fn))
                       (mv nil nil nil (irr-tyspecseq)))
                      ((when (eq fn 'quote))
                       (mv nil nil nil (irr-tyspecseq)))
                      (fn+type (assoc-eq fn prec-fns))
                      ((unless (consp fn+type))
                       (mv nil nil nil (irr-tyspecseq)))
                      (type (mbe :logic (tyspecseq-fix (cdr fn+type))
                                 :exec (cdr fn+type))))
                   (mv t fn args type)))
    (& (mv nil nil nil (irr-tyspecseq))))
  ///

  (defret acl2-count-of-atc-check-callable-fn-args
    (implies yes/no
             (< (acl2-count args)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atc-gen-expr-fns
  :short "Mutually recursive functions to
          generate C expressions from ACL2 terms."

  (define atc-gen-expr-nonbool ((term pseudo-termp)
                                (vars atc-symbol-tyspecseq-alistp)
                                (fn symbolp)
                                (prec-fns atc-symbol-tyspecseq-alistp)
                                ctx
                                state)
    :returns (mv erp
                 (val (tuple (expr exprp)
                             (type tyspecseqp)
                             val))
                 state)
    :parents (atc-event-and-code-generation atc-gen-expr-fns)
    :short "Generate a C expression from an ACL2 term
            that must be an allowed non-boolean term."
    :long
    (xdoc::topstring
     (xdoc::p
      "At the same time, we check that the term is an allowed non-boolean term,
       as described in the user documentation.")
     (xdoc::p
      "An ACL2 variable is translated to a C variable.
       Its type is looked up in an alist that is passed as input.")
     (xdoc::p
      "If the term fits the @(tsee sint-const) pattern,
       we translate it to a C integer constant.")
     (xdoc::p
      "If the term fits the pattern of a unary or binary operation,
       we translate it to the application of the operator
       to the recursively generated expressions.
       The type is the result type of the operator.")
     (xdoc::p
      "If the term is a call of a function that precedes @('fn')
       in the list of target functions @('fn1'), ..., @('fnp'),
       we translate it to a C function call on the translated arguments.
       The type of the expression is the result type of the function.")
     (xdoc::p
      "If the term is a call of @(tsee c::sint01),
       we call the mutually recursive function
       that translates the argument (which must be an allowed boolean term)
       to an expression, which we return.
       The type is always @('int') here.")
     (xdoc::p
      "If the term is an @(tsee if) call,
       first we check if the test is @(tsee mbt) or @(tsee mbt$);
       in that case, we discard test and `else' branch
       and recursively process the `then' branch.
       Otherwise,
       we call the mutually recursive function on the test,
       we call this function on the branches,
       and we construct a conditional expression.
       We ensure that the two branches have the same type.")
     (xdoc::p
      "In all other cases, we fail with an error.
       The term is not an allowed non-boolean term.
       We could extend this code to provide
       more information to the user at some point."))
    (b* (((when (acl2::variablep term))
          (b* ((var+type (assoc-eq term vars))
               ((when (not var+type))
                (raise "Internal error: the variable ~x0 in function ~x1 ~
                        has no associated type." term fn)
                (value (list (irr-expr) (irr-tyspecseq))))
               (type (tyspecseq-fix (cdr var+type))))
            (value (list (expr-ident (make-ident :name (symbol-name term)))
                         type))))
         ((mv okp val) (atc-check-sint-const term))
         ((when okp)
          (value
           (list
            (expr-const (const-int (make-iconst :value val
                                                :base (iconst-base-dec)
                                                :unsignedp nil
                                                :type (iconst-tysuffix-none))))
            (tyspecseq-sint))))
         ((mv okp op arg type) (atc-check-sint-unop term))
         ((when okp)
          (b* (((er (list arg-expr &)) (atc-gen-expr-nonbool arg
                                                             vars
                                                             fn
                                                             prec-fns
                                                             ctx
                                                             state)))
            (value (list (make-expr-unary :op op :arg arg-expr)
                         type))))
         ((mv okp op arg1 arg2 type) (atc-check-sint-binop term))
         ((when okp)
          (b* (((er (list arg1-expr &)) (atc-gen-expr-nonbool arg1
                                                              vars
                                                              fn
                                                              prec-fns
                                                              ctx
                                                              state))
               ((er (list arg2-expr &)) (atc-gen-expr-nonbool arg2
                                                              vars
                                                              fn
                                                              prec-fns
                                                              ctx
                                                              state)))
            (value (list (make-expr-binary :op op
                                           :arg1 arg1-expr
                                           :arg2 arg2-expr)
                         type))))
         ((mv okp fn args type) (atc-check-callable-fn term prec-fns))
         ((when okp)
          (b* (((mv erp arg-exprs state) (atc-gen-expr-nonbool-list args
                                                                    vars
                                                                    fn
                                                                    prec-fns
                                                                    ctx
                                                                    state))
               ((when erp) (mv erp (list (irr-expr) (irr-tyspecseq)) state)))
            (value (list
                    (make-expr-call :fun (make-ident :name (symbol-name fn))
                                    :args arg-exprs)
                    type)))))
      (case-match term
        (('c::sint01 arg)
         (b* (((mv erp expr state)
               (atc-gen-expr-bool arg vars fn prec-fns ctx state))
              ((when erp) (mv erp (list (irr-expr) (irr-tyspecseq)) state)))
           (mv nil (list expr (tyspecseq-sint)) state)))
        (('if test then else)
         (b* (((mv mbtp &) (acl2::check-mbt-call test))
              ((when mbtp) (atc-gen-expr-nonbool then
                                                 vars
                                                 fn
                                                 prec-fns
                                                 ctx
                                                 state))
              ((mv mbt$p &) (acl2::check-mbt$-call test))
              ((when mbt$p) (atc-gen-expr-nonbool then
                                                  vars
                                                  fn
                                                  prec-fns
                                                  ctx
                                                  state))
              ((mv erp test-expr state) (atc-gen-expr-bool test
                                                           vars
                                                           fn
                                                           prec-fns
                                                           ctx
                                                           state))
              ((when erp) (mv erp (list (irr-expr) (irr-tyspecseq)) state))
              ((er (list then-expr then-type)) (atc-gen-expr-nonbool then
                                                                     vars
                                                                     fn
                                                                     prec-fns
                                                                     ctx
                                                                     state))
              ((er (list else-expr else-type)) (atc-gen-expr-nonbool else
                                                                     vars
                                                                     fn
                                                                     prec-fns
                                                                     ctx
                                                                     state))
              ((unless (equal then-type else-type))
               (er-soft+ ctx t (list (irr-expr) (irr-tyspecseq))
                         "When generating C code for the function ~x0, ~
                          two branches ~x1 and ~x2 of a conditional term ~
                          have different types ~x3 and ~x4;
                          use conversion operations, if needed, ~
                          to make the branches of the same type."
                         fn then else then-type else-type)))
           (value
            (list
             (make-expr-cond :test test-expr :then then-expr :else else-expr)
             then-type))))
        (& (er-soft+ ctx t (list (irr-expr) (irr-tyspecseq))
                     "When generating C code for the function ~x0, ~
                      at a point where
                      an allowed non-boolean ACL2 term is expected, ~
                      the term ~x1 is encountered instead."
                     fn term)))))

  (define atc-gen-expr-nonbool-list ((terms pseudo-term-listp)
                                     (vars atc-symbol-tyspecseq-alistp)
                                     (fn symbolp)
                                     (prec-fns atc-symbol-tyspecseq-alistp)
                                     ctx
                                     state)
    :returns (mv erp (exprs expr-listp) state)
    :parents (atc-event-and-code-generation atc-gen-expr-fns)
    :short "Generate a list of C expressions from a list of ACL2 terms
            that must be allowed non-boolean terms."
    :long
    (xdoc::topstring
     (xdoc::p
      "We do not return the C types of the expressions."))
    (b* (((when (endp terms)) (value nil))
         ((mv erp (list expr &) state) (atc-gen-expr-nonbool (car terms)
                                                             vars
                                                             fn
                                                             prec-fns
                                                             ctx
                                                             state))
         ((when erp) (mv erp nil state))
         ((er exprs) (atc-gen-expr-nonbool-list (cdr terms)
                                                vars
                                                fn
                                                prec-fns
                                                ctx
                                                state)))
      (value (cons expr exprs))))

  (define atc-gen-expr-bool ((term pseudo-termp)
                             (vars atc-symbol-tyspecseq-alistp)
                             (fn symbolp)
                             (prec-fns atc-symbol-tyspecseq-alistp)
                             ctx
                             state)
    :returns (mv erp (expr exprp) state)
    :parents (atc-event-and-code-generation atc-gen-expr-fns)
    :short "Generate a C expression from an ACL2 term
            that must be an allowed boolean term."
    :long
    (xdoc::topstring
     (xdoc::p
      "At the same time, we check that the term is an allowed boolen term,
       as described in the user documentation.")
     (xdoc::p
      "If the term is a call of @(tsee not), @(tsee and), or @(tsee or),
       we recursively translate the arguments,
       which must be an allowed boolean terms,
       and we construct a logical expression
       with the corresponding C operators.")
     (xdoc::p
      "If the term is a call of @(tsee sint-nonzerop),
       we call the mutually recursive function
       that translates the argument, which must be an allowed non-boolean term,
       to an expression, which we return.")
     (xdoc::p
      "In all other cases, we fail with an error.
       The term is not an allowed non-boolean term.
       We could extend this code to provide
       more information to the user at some point."))
    (case-match term
      (('not arg)
       (b* (((er arg-expr) (atc-gen-expr-bool arg
                                              vars
                                              fn
                                              prec-fns
                                              ctx
                                              state)))
         (value (make-expr-unary :op (unop-lognot) :arg arg-expr))))
      (('if arg1 arg2 ''nil)
       (b* (((er arg1-expr) (atc-gen-expr-bool arg1
                                               vars
                                               fn
                                               prec-fns
                                               ctx
                                               state))
            ((er arg2-expr) (atc-gen-expr-bool arg2
                                               vars
                                               fn
                                               prec-fns
                                               ctx
                                               state)))
         (value (make-expr-binary :op (binop-logand)
                                  :arg1 arg1-expr
                                  :arg2 arg2-expr))))
      (('if arg1 arg1 arg2)
       (b* (((er arg1-expr) (atc-gen-expr-bool arg1
                                               vars
                                               fn
                                               prec-fns
                                               ctx
                                               state))
            ((er arg2-expr) (atc-gen-expr-bool arg2
                                               vars
                                               fn
                                               prec-fns
                                               ctx
                                               state)))
         (value (make-expr-binary :op (binop-logor)
                                  :arg1 arg1-expr
                                  :arg2 arg2-expr))))
      (('c::sint-nonzerop arg)
       (b* (((mv erp (list expr &) state)
             (atc-gen-expr-nonbool arg vars fn prec-fns ctx state)))
         (mv erp expr state)))
      (& (er-soft+ ctx t (irr-expr)
                   "When generating C code for the function ~x0, ~
                    at a point where
                    an allowed boolean ACL2 term is expected, ~
                    the term ~x1 is encountered instead."
                   fn term))))

  :prepwork ((set-state-ok t))

  :verify-guards nil ; done below

  ///

  (defret-mutual consp-of-atc-gen-expr-nonbool/bool
    (defret consp-of-atc-gen-expr-nonbool
      (and (consp val)
           (true-listp val))
      :rule-classes :type-prescription
      :fn atc-gen-expr-nonbool)
    (defret true-of-atc-gen-expr-nonbool-list
      t
      :rule-classes nil
      :fn atc-gen-expr-nonbool-list)
    (defret true-of-atc-gen-expr-bool
      t
      :rule-classes nil
      :fn atc-gen-expr-bool))

  (verify-guards atc-gen-expr-nonbool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-stmt ((term pseudo-termp)
                      (vars atc-symbol-tyspecseq-alistp)
                      (fn symbolp)
                      (prec-fns atc-symbol-tyspecseq-alistp)
                      ctx
                      state)
  :returns (mv erp
               (val (tuple (stmt stmtp)
                           (type tyspecseqp)
                           val))
               state)
  :short "Generate a C statement from an ACL2 term."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the generated statement,
     we also return the C type of the value it returns.
     This is always @('int') for now,
     but this will be generalized at some point.")
   (xdoc::p
    "This is called on the body term of an ACL2 function.
     If the term is not a conditional,
     we generate a C expression for the term
     and generate a @('return') statement with that expression.
     Otherwise, the term is a conditional and there are two cases.
     If the test is @(tsee mbt) or @(tsee mbt$),
     we discard test and `else' branch
     and recursively translate the `then' branch.
     Otherwise, we generate an @('if') statement,
     with recursively generated statements as branches;
     the test expression is generated from the test term;
     we ensure that the two branches have the same type."))
  (case-match term
    (('if test then else)
     (b* (((mv mbtp &) (acl2::check-mbt-call test))
          ((when mbtp) (atc-gen-stmt then vars fn prec-fns ctx state))
          ((mv mbt$p &) (acl2::check-mbt$-call test))
          ((when mbt$p) (atc-gen-stmt then vars fn prec-fns ctx state))
          ((mv erp test-expr state) (atc-gen-expr-bool test
                                                       vars
                                                       fn
                                                       prec-fns
                                                       ctx
                                                       state))
          ((when erp) (mv erp (list (irr-stmt) (irr-tyspecseq)) state))
          ((er (list then-stmt then-type)) (atc-gen-stmt then
                                                         vars
                                                         fn
                                                         prec-fns
                                                         ctx
                                                         state))
          ((er (list else-stmt else-type)) (atc-gen-stmt else
                                                         vars
                                                         fn
                                                         prec-fns
                                                         ctx
                                                         state))
          ((unless (equal then-type else-type))
           (er-soft+ ctx t (list (irr-stmt) (irr-tyspecseq))
                     "When generating C code for the function ~x0, ~
                      two branches ~x1 and ~x2 of a conditional term ~
                      have different types ~x3 and ~x4;
                      use conversion operations, if needed, ~
                      to make the branches of the same type."
                     fn then else then-type else-type)))
       (value
        (list
         (make-stmt-ifelse :test test-expr :then then-stmt :else else-stmt)
         then-type))))
    (& (b* (((mv erp (list expr type) state) (atc-gen-expr-nonbool term
                                                                   vars
                                                                   fn
                                                                   prec-fns
                                                                   ctx
                                                                   state))
            ((when erp) (mv erp (list (irr-stmt) (irr-tyspecseq)) state)))
         (value (list (make-stmt-return :value expr)
                      type)))))

  :verify-guards nil ; done below

  ///

  (more-returns
   (val (and (consp val)
             (true-listp val))
        :name cons-true-listp-of-atc-gen-stmt-val
        :rule-classes :type-prescription))

  (verify-guards atc-gen-stmt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-param-decl ((formal symbolp) (fn symbolp) ctx state)
  :returns (mv erp (param param-declp) state)
  :short "Generate a C parameter declaration from an ACL2 formal parameter."
  (b* ((name (symbol-name formal))
       ((unless (atc-ident-stringp name))
        (er-soft+ ctx t (irr-param-decl)
                  "The symbol name ~s0 of ~
                   the formal parameter ~x1 of the function ~x2 ~
                   must be a portable ASCII C identifier, but it is not."
                  name formal fn)))
    (value (make-param-decl :name (make-ident :name name)
                            :type (tyspecseq-sint)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-param-decl-list ((formals symbol-listp) (fn symbolp) ctx state)
  :returns (mv erp
               (val (tuple (params param-decl-listp)
                           (vars atc-symbol-tyspecseq-alistp)
                           val))
               state)
  :short "Generate a list of C parameter declarations
          from a list of ACL2 formal parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Also generate an alist from the formal parameters to their C types."))
  (b* (((when (endp formals)) (value (list nil nil)))
       (formal (mbe :logic (acl2::symbol-fix (car formals))
                    :exec (car formals)))
       ((when (member-equal (symbol-name formal)
                            (symbol-name-lst (cdr formals))))
        (er-soft+ ctx t (list nil nil)
                  "The formal parameter ~x0 of the function ~x1 ~
                   has the same symbol name as another formal parameters ~x2; ~
                   this is disallowed, even if the package names differ."
                  formal fn (cdr formals)))
       ((mv erp param state) (atc-gen-param-decl formal fn ctx state))
       ((when erp) (mv erp (list nil nil) state))
       ((er (list params vars)) (atc-gen-param-decl-list (cdr formals)
                                                              fn
                                                              ctx
                                                              state)))
    (value (list (cons param params)
                 (acons formal (tyspecseq-sint) vars))))

  :verify-guards nil ; done below
  ///
  (verify-guards atc-gen-param-decl-list
    :hints
    (("Goal"
      :in-theory (enable alistp-when-atc-symbol-tyspecseq-alistp-rewrite))))

  (more-returns
   (val true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-guard ((formals symbol-listp)
                         (fn symbolp)
                         (guard pseudo-termp)
                         (guard-conjuncts pseudo-term-listp)
                         ctx
                         state)
  :returns (mv erp (nothing null) state)
  :short "Check whether every formal parameter of a target function
          has an associated guard conjunct that requires the parameter
          to be (the ACL2 counterpart of) a C @('int') value."
  (b* (((when (endp formals)) (value nil))
       (formal (car formals))
       (conjunct (acl2::fcons-term* 'sintp formal))
       ((unless (member-equal conjunct guard-conjuncts))
        (er-soft+ ctx t nil
                  "The guard ~x0 of the ~x1 function does not have ~
                   a recognizable conjunct ~x2 that requires ~
                   the formal parameter ~x3 to be a C int value."
                  guard fn conjunct formal)))
    (atc-check-guard (cdr formals) fn guard guard-conjuncts ctx state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-ext-decl ((fn symbolp)
                          (prec-fns atc-symbol-tyspecseq-alistp)
                          ctx
                          state)
  :returns (mv erp
               (val (tuple (ext ext-declp)
                           (updated-prec-fns atc-symbol-tyspecseq-alistp)
                           val)
                    :hyp (atc-symbol-tyspecseq-alistp prec-fns))
               state)
  :short "Generate a C external declaration (a function definition)
          from an ACL2 function."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use the type of the value returned by the statement for the body
     as the result type of the C function.
     We also extend the alist @('prec-fns') with the function."))
  (b* ((name (symbol-name fn))
       ((unless (atc-ident-stringp name))
        (er-soft+ ctx t (list (irr-ext-decl) nil)
                  "The symbol name ~s0 of the function ~x1 ~
                   must be a portable ASCII C identifier, but it is not."
                  name fn))
       (wrld (w state))
       (formals (acl2::formals+ fn wrld))
       (guard (acl2::uguard+ fn wrld))
       (guard-conjuncts (flatten-ands-in-lit guard))
       ((mv erp & state) (atc-check-guard formals
                                          fn
                                          guard
                                          guard-conjuncts
                                          ctx
                                          state))
       ((when erp) (mv erp (list (irr-ext-decl) nil) state))
       ((mv erp (list params vars) state) (atc-gen-param-decl-list formals
                                                                   fn
                                                                   ctx
                                                                   state))
       ((when erp) (mv erp (list (irr-ext-decl) nil) state))
       (body (acl2::ubody+ fn wrld))
       ((mv erp (list stmt type) state) (atc-gen-stmt body
                                                      vars
                                                      fn
                                                      prec-fns
                                                      ctx
                                                      state))
       ((when erp) (mv erp (list (irr-ext-decl) nil) state)))
    (value
     (list
      (ext-decl-fundef
       (make-fundef :result type
                    :name (make-ident :name name)
                    :params params
                    :body (stmt-compound (list (block-item-stmt stmt)))))
      (acons fn type prec-fns))))
  ///

  (more-returns
   (val true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-ext-decl-list ((fns symbol-listp)
                               (prec-fns atc-symbol-tyspecseq-alistp)
                               ctx
                               state)
  :returns (mv erp
               (exts ext-decl-listp :hyp (atc-symbol-tyspecseq-alistp prec-fns))
               state)
  :short "Lift @(tsee atc-gen-ext-decl) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "After we process the first function @('fn') in @('fns'),
     we use the extended @('prec-fns') for the subsequent functions."))
  (b* (((when (endp fns)) (value nil))
       ((cons fn rest-fns) fns)
       (dup? (member-eq fn rest-fns))
       ((when dup?)
        (er-soft+ ctx t nil
                  "The target functions must have distinct symbol names ~
                   (i.e. they may not differ only in the package names), ~
                   but the functions ~x0 and ~x1 ~
                   have the same symbol name."
                  fn (car dup?)))
       ((mv erp (list ext prec-fns) state)
        (atc-gen-ext-decl fn prec-fns ctx state))
       ((when erp) (mv erp nil state))
       ((er exts) (atc-gen-ext-decl-list rest-fns prec-fns ctx state)))
    (value (cons ext exts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-transunit ((fn1...fnp symbol-listp) ctx state)
  :returns (mv erp (tunit transunitp) state)
  :short "Generate a C translation unit from the ACL2 target functions."
  (b* (((mv erp exts state) (atc-gen-ext-decl-list fn1...fnp nil ctx state))
       ((when erp) (mv erp (irr-transunit) state)))
    (value (make-transunit :decls exts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-const ((const symbolp) (tunit transunitp) (verbose booleanp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the named constant for the abstract syntax tree
          of the generated C code (i.e. translation unit)."
  (b* ((progress-start?
        (and verbose
             `((cw-event "~%Generating the named constant ~x0..." ',const))))
       (progress-end? (and verbose `((cw-event " done.~%"))))
       (defconst-event `(defconst ,const ',tunit))
       (local-event `(progn ,@progress-start?
                            (local ,defconst-event)
                            ,@progress-end?)))
    (mv local-event defconst-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-wf-thm ((const symbolp) (verbose booleanp) ctx state)
  :returns (mv erp
               (val "A @('(tuple (local-event pseudo-event-formp)
                                 (exported-event pseudo-event-formp)
                                 val)').")
               state)
  :mode :program
  :short "Generate the theorem asserting
          the static well-formedness of the generated C code
          (referenced as the named constant)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since this is a ground theorem,
     we expect that it should be easily provable
     using just the executable counterpart of @(tsee transunit-wfp),
     which is an executable function."))
  (b* ((name (add-suffix const "-WELL-FORMED"))
       ((er &) (acl2::ensure-symbol-is-fresh-event-name$
                name
                (msg "The constant name ~x0 ~
                      specified by the :CONST-NAME input ~
                      must be such that ~x1 is a fresh theorem name, ~
                      but it is not."
                     const name)
                nil
                nil
                t
                nil))
       ((mv local-event exported-event)
        (acl2::evmac-generate-defthm
         name
         :formula `(transunit-wfp ,const)
         :hints '(("Goal" :in-theory '((:e transunit-wfp))))
         :enable nil))
       (progress-start?
        (and verbose
             `((cw-event "~%Generating the theorem ~x0..." ',name))))
       (progress-end? (and verbose `((cw-event " done.~%"))))
       (local-event `(progn ,@progress-start?
                            ,local-event
                            ,@progress-end?)))
    (value (list local-event exported-event))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-thm ((fn symbolp)
                        (prec-fns symbol-listp)
                        (const symbolp)
                        (verbose booleanp)
                        ctx
                        state)
  :returns (mv erp
               (val "A @('(tuple (local-event pseudo-event-formp)
                                 (exported-event pseudo-event-formp)
                                 val)').")
               state)
  :mode :program
  :short "Generate the theorem asserting
          the dynamic functional correctness of the C function
          generated from the specified ACL2 function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The execution of the C function according to the dynamic semantics
     is expressed by calling @(tsee run-fun) on
     the name of @('fn'), the formals of @('fn'), and @('*const*').
     This is equated to a call of @('fn') on its formals.
     The guard of @('fn') is used as hypothesis.")
   (xdoc::p
    "The currently generated proof hints are relatively simple:
     we enable @(tsee run-fun) and all the functions that it calls
     in the dynamic execution;
     we also need to force the expansion of
     @(tsee exec-fun) and @(tsee exec-block-item),
     based on experimentation;
     we also use the guard theorem of @('fn').
     We also enable some opener rules;
     see @(see atc-proof-support-alternative).
     We also enable all the functions that may be called by @('fn');
     eventually, we will generate more compositional proofs.
     Given that the translation unit is a constant,
     this symbolically executes the C function.
     Since the generated C code currently has no loops,
     this strategy may be adequate,
     but eventually we will likely need more elaborate proof hints.
     The use of the guard theorem of @('fn') is critical
     to ensure that the symbolic execution of the C operators
     does not splits on the error case:
     the fact that @('fn') is guard-verified
     ensures that @(tsee sint-add) and similar functions are always called
     on values such that the exact result fit into the type,
     which is the same condition under which the dynamic semantics
     does not error on the corresponding operators."))
  (b* ((name (acl2::packn (list const "-" (symbol-name fn) "-CORRECT")))
       ((er &) (acl2::ensure-symbol-is-fresh-event-name$
                name
                (msg "The constant name ~x0 ~
                      specified by the :CONST-NAME input ~
                      must be such that ~x1 is a fresh theorem name, ~
                      but it is not."
                     const name)
                nil
                nil
                t
                nil))
       (wrld (w state))
       (formals (acl2::formals+ fn wrld))
       (guard (untranslate (acl2::uguard fn wrld) t wrld))
       (lhs `(run-fun (ident ,(symbol-name fn))
                      (list ,@formals)
                      ,const))
       (rhs `(value-result-ok (,fn ,@formals)))
       (hints `(("Goal"
                 :in-theory (enable* run-fun
                                     init-store
                                     exec-fun
                                     exec-stmt
                                     exec-block-item
                                     exec-block-item-list
                                     exec-expr
                                     exec-binary
                                     exec-binary-strict
                                     exec-binary-logand
                                     exec-binary-logor
                                     exec-unary
                                     exec-ident
                                     exec-const
                                     exec-iconst
                                     top-frame
                                     push-frame
                                     pop-frame
                                     store-result-kind
                                     store-result-ok->get
                                     value-result-kind
                                     value-result-ok->get
                                     value-option-result-kind
                                     value-option-result-ok->get
                                     exec-unfold-rules
                                     ;; rules from ATC-PROOF-SUPPORT:
                                     ;; exec-expr-of-call
                                     ;; exec-expr-list-of-cons
                                     ;; exec-expr-list-of-atom
                                     ;; exec-block-item-list-of-cons
                                     ;; exec-block-item-list-of-atom
                                     ;; exec-stmt-of-return
                                     ,@prec-fns)
                 :expand ((:free (fun args env limit)
                           (exec-fun fun args env limit))
                          (:free (item env limit)
                           (exec-block-item item env limit)))
                 :use (:guard-theorem ,fn))))
       ((mv local-event exported-event)
        (acl2::evmac-generate-defthm
         name
         :formula `(implies ,guard (equal ,lhs ,rhs))
         :hints hints
         :enable nil))
       (progress-start?
        (and verbose
             `((cw-event "~%Generating the theorem ~x0..." ',name))))
       (progress-end? (and verbose `((cw-event " done.~%"))))
       (local-event `(progn ,@progress-start?
                            ,local-event
                            ,@progress-end?)))
    (value (list local-event exported-event))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-thm-list ((fns symbol-listp)
                             (prec-fns symbol-listp)
                             (const symbolp)
                             (verbose booleanp)
                             ctx
                             state)
  :returns (mv erp
               (val "A @('(tuple (local-events pseudo-event-form-listp)
                                 (exported-events pseudo-event-form-listp)
                                 val)').")
               state)
  :mode :program
  :short "Lift @(tsee atc-gen-fn-thm) to lists."
  (b* (((when (endp fns)) (value (list nil nil nil)))
       ((er (list local-event exported-event))
        (atc-gen-fn-thm (car fns)
                        prec-fns
                        const
                        verbose
                        ctx
                        state))
       ((er (list local-events exported-events))
        (atc-gen-fn-thm-list (cdr fns)
                             (cons (car fns) prec-fns)
                             const
                             verbose
                             ctx
                             state)))
    (value (list (cons local-event local-events)
                 (cons exported-event exported-events)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-file ((tunit transunitp) (output-file stringp) state)
  :returns (mv erp val state)
  :mode :program
  :short "Pretty-print the generated C code (i.e. translation unit)
          to the output file."
  (b* ((lines (pprint-transunit tunit)))
    (pprinted-lines-to-file lines output-file state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-everything ((fn1...fnp symbol-listp)
                            (const symbolp)
                            (output-file stringp)
                            (verbose booleanp)
                            (call pseudo-event-formp)
                            ctx
                            state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :short "Generate the file and the events."
  (b* (((er tunit) (atc-gen-transunit fn1...fnp ctx state))
       ((mv local-const-event exported-const-event)
        (atc-gen-const const tunit verbose))
       ((er (list wf-thm-local-event wf-thm-exported-event))
        (atc-gen-wf-thm const verbose ctx state))
       ((er (list fn-thm-local-events fn-thm-exported-events))
        (atc-gen-fn-thm-list fn1...fnp nil const verbose ctx state))
       ((acl2::run-when verbose) (cw "~%Generating file ~x0..." output-file))
       ((er &) (atc-gen-file tunit output-file state))
       ((acl2::run-when verbose) (cw " done.~%"))
       (encapsulate
         `(encapsulate ()
            (evmac-prepare-proofs)
            ,local-const-event
            ,exported-const-event
            ,wf-thm-local-event
            ,wf-thm-exported-event
            ,@fn-thm-local-events
            ,@fn-thm-exported-events))
       (info (make-atc-call-info :encapsulate encapsulate))
       (table-event (atc-table-record-event call info)))
    (value `(progn ,encapsulate
                   ,table-event
                   (value-triple :invisible)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-fn ((args true-listp) (call pseudo-event-formp) ctx state)
  :returns (mv erp
               (result "Always @('(value-triple :invisible)').")
               state)
  :mode :program
  :parents (atc-implementation)
  :short "Process the inputs and
          generate the constant definition and the C file."
  (b* (((when (atc-table-lookup call (w state)))
        (value '(value-triple :redundant)))
       ((er (list fn1...fnp const output-file verbose))
        (atc-process-inputs args ctx state)))
    (atc-gen-everything fn1...fnp const output-file verbose call ctx state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-macro-definition
  :parents (atc-implementation)
  :short "Definition of the @(tsee atc) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "We suppress the extra output produced by @(tsee make-event)
     via @(tsee with-output) and @('(:on-behalf-of :quiet)').")
   (xdoc::@def "atc"))
  (defmacro atc (&whole call &rest args)
    `(make-event-terse (atc-fn ',args ',call 'atc state)
                       :suppress-errors nil)))
