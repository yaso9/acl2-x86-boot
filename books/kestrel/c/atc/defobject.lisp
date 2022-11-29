; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")
(include-book "arrays")
(include-book "term-checkers-common")

(include-book "fty-pseudo-terms")

(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-true-list" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-untranslated-term" :dir :system)
(include-book "kestrel/fty/pseudo-event-form" :dir :system)
(include-book "kestrel/std/system/table-alist-plus" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defobject-implementation
  :parents (defobject)
  :short "Implementation of @(tsee defobject)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *defobject-table*
  :short "Name of the table of shallowly embedded external objects."
  'defobject-table)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod defobject-info
  :short "Fixtype of information about shallowly embedded external objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each C external object defined via @(tsee defobject), we store:")
   (xdoc::ul
    (xdoc::li
     "The name, as an identifier.
      While currently @(tsee ident) is just a wrapper of @(tsee string),
      it may include invariants in the future.
      Thus, having the name stored as an identifier in the object information
      will spare us from having to double-check the invariants
      if we were to construct the identifier from the string.")
    (xdoc::li
     "The name, as a symbol.
      This is so we can ensure that ACL2 functions use the exact symbol
      to access the external object.
      The @(tsee defobject) table stores the name as key,
      but the name is only the @(tsee symbol-name),
      and loses the @(tsee symbol-package-name) information.")
    (xdoc::li
     "The type of the object.
      Currently this must be an array type with specified size,
      but in the future this may become more general.")
    (xdoc::li
     "The initializer of the object.
      This is currently a list of C expressions,
      because the object is always an array.
      In the future, this may be generalized to other kinds of initializers.
      This list is empty to represent an external object without initializer;
      otherwise, the length of the list matches the size of the array type,
      but this invariant is not captured in this fixtype currently.")
    (xdoc::li
     "The name of the recognizer of the possible values of the object.
      This recognizer is generated by @(tsee defobject).")
    (xdoc::li
     "The name of the initializer of the object,
      i.e. the nullary function generated by @(tsee defobject).")
    (xdoc::li
     "The call of @(tsee defobject),
      used for redundancy checking.")))
  ((name-ident ident)
   (name-symbol symbol)
   (type type)
   (init expr-list)
   (recognizer symbolp)
   (initializer symbolp)
   (call pseudo-event-form))
  :pred defobject-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption defobject-info-option
  defobject-info
  :short "Fixtype of optional information about
          shallowly embedded C external objects."
  :pred defobject-info-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defobject-table-definition
  :short "Definition of the table of shallowly embedded C external objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "The keys are strings that are the @(tsee symbol-name)s of
     symbols that represent the names of the objects.
     The name of each such symbol is a portable ASCII C identifier
     but this constraint is not enforced in the table's guard.
     The keys in the table are unique.")
   (xdoc::p
    "The values are the information about the objects
     See @(tsee defobject-info)."))

  (make-event
   `(table ,*defobject-table* nil nil
      :guard (and (stringp acl2::key)
                  (defobject-infop acl2::val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defobject-table-lookup ((name stringp) (wrld plist-worldp))
  :returns (info? defobject-info-optionp
                  :hints (("Goal" :in-theory (enable defobject-info-optionp))))
  :short "Retrieve information about a shallowly embedded C external object."
  (b* ((pair (assoc-equal name (table-alist+ *defobject-table* wrld)))
       ((when (not (consp pair))) nil)
       (info (cdr pair))
       ((unless (defobject-infop info))
        (raise "Internal error: malformed DEFOBJECT information ~x0." info)))
    info))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defobject-table-record-event ((name stringp) (info defobject-infop))
  :returns (event pseudo-event-formp)
  :short "Event to update the table of shallowly embedded C external objects
          by recording a new C external object in it."
  `(table ,*defobject-table* ,name ',info))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defobject-process-name (name (call pseudo-event-formp) (ctx ctxp) state)
  :returns (mv erp
               (val (tuple (name-string stringp)
                           (name-ident identp)
                           (redundantp booleanp)
                           val))
               state)
  :short "Process the @('name') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that it is a symbol
     whose name is a portable ASCII identifier.
     If its name is not a key of the @(tsee defobject) table,
     we return the name as a string and as an identifier,
     along with an indication that the call is not redundant.
     If its name is already in the @(tsee defobject) table,
     we ensure that the current call is identical to the one stored there,
     in which case we return an indication that the call is redundant."))
  (b* ((wrld (w state))
       ((acl2::fun (irrelevant)) (list "" (irr-ident) nil))
       ((er &) (ensure-value-is-symbol$ name
                                        (msg "The first input ~x0" name)
                                        t (irrelevant)))
       (name-string (symbol-name name))
       ((unless (paident-stringp name-string))
        (er-soft+ ctx t (irrelevant)
                  "The SYMBOL-NAME ~x0 of the first input ~x1 ~
                   must be a portable ASCII C identifier."
                  name-string name))
       (name-ident (ident name-string))
       (info (defobject-table-lookup name-string wrld))
       ((when info)
        (if (equal call (defobject-info->call info))
            (acl2::value (list name-string name-ident t))
          (er-soft+ ctx t (irrelevant)
                    "There is already an external object with name ~x0, ~
                     recorded in the table of shallowly embedded ~
                     C external objects, ~
                     but its call ~x1 differs from the current call ~x2, ~
                     and so the call is not redundant."
                    name-string (defobject-info->call info) call))))
    (acl2::value (list name-string name-ident nil)))
  :guard-hints (("Goal" :in-theory (enable acl2::ensure-value-is-symbol))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defobject-process-type (type (ctx ctxp) state)
  :returns (mv erp (val typep) state)
  :short "Process the @(':type') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "If successful, we return the C type specified by the input."))
  (b* (((unless (std::tuplep 2 type))
        (er-soft+ ctx t (irr-type)
                  "The :TYPE input ~x0 must be a list of two elements."
                  type))
       ((list elemfixtype pos) type)
       ((er &) (ensure-value-is-symbol$ elemfixtype
                                        (msg "The first element ~x0 ~
                                              of the :TYPE input"
                                             elemfixtype)
                                        t (irr-type)))
       (elemtype (fixtype-to-integer-type elemfixtype))
       ((unless elemtype)
        (er-soft+ ctx t (irr-type)
                  "The first element ~x0 of the :TYPE input ~
                   must be among ~&1."
                  elemfixtype
                  '(schar
                    uchar
                    sshort
                    ushort
                    sint
                    uint
                    slong
                    ulong
                    sllong
                    ullong)))
       ((unless (posp pos))
        (er-soft+ ctx t (irr-type)
                  "The second element ~x0 of the :TYPE input ~
                   must be a positive integer."
                  pos))
       ((unless (<= pos (ullong-max)))
        (er-soft+ ctx t (irr-type)
                  "The second element ~x0 of the :TYPE input ~
                   must not exceed ~x1."
                  pos (ullong-max))))
    (acl2::value (make-type-array :of elemtype :size pos)))
  :guard-hints (("Goal" :in-theory (enable acl2::ensure-value-is-symbol))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defobject-term-to-expr ((term pseudo-termp)
                                (ctx ctxp)
                                state)
  :returns (mv erp
               (val (tuple (expr exprp)
                           (type typep)
                           val))
               state)
  :short "Turn a constant expression term into the represented expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is not a constant expression term, stop with an error.
     If it is, also return the type of the expression.")
   (xdoc::p
    "In essence, this generates C code for
     a term used in the initializer of the external object."))
  (b* (((acl2::fun (irrelevant)) (list (irr-expr) (irr-type)))
       ((mv erp okp const out-type &) (atc-check-iconst term))
       ((when erp) (er-soft+ ctx t (irrelevant) "~@0" erp))
       ((when okp)
        (acl2::value
         (list (expr-const (const-int const))
               out-type)))
       ((mv okp op arg in-type out-type) (atc-check-unop term))
       ((when okp)
        (b* (((er (list arg-expr type)) (defobject-term-to-expr arg ctx state))
             ((unless (equal type in-type))
              (er-soft+ ctx t (irrelevant)
                        "The unary operator ~x0 ~
                         is applied to a term ~x1 returning ~x2, ~
                         but a ~x3 operand is expected."
                        op arg type in-type)))
          (acl2::value (list (make-expr-unary :op op
                                              :arg arg-expr)
                             out-type))))
       ((mv okp op arg1 arg2 in-type1 in-type2 out-type)
        (atc-check-binop term))
       ((when okp)
        (b* (((er (list arg1-expr type1)) (defobject-term-to-expr
                                            arg1 ctx state))
             ((er (list arg2-expr type2)) (defobject-term-to-expr
                                            arg2 ctx state))
             ((unless (and (equal type1 in-type1)
                           (equal type2 in-type2)))
              (er-soft+ ctx t (irrelevant)
                        "The binary operator ~x0 ~
                         is applied to a term ~x1 returning ~x2
                         and to a term ~x3 returning ~x4,
                         but a ~x5 and a ~x6 operand is expected."
                        op arg1 type1 arg2 type2 in-type1 in-type2)))
          (acl2::value (list (make-expr-binary :op op
                                               :arg1 arg1-expr
                                               :arg2 arg2-expr)
                             out-type))))
       ((mv okp tyname arg in-type out-type) (atc-check-conv term))
       ((when okp)
        (b* (((er (list arg-expr type)) (defobject-term-to-expr
                                          arg ctx state))
             ((unless (equal type in-type))
              (er-soft+ ctx t (irrelevant)
                        "The conversion from ~x0 to ~x1 ~
                         is applied to a term ~x2 returning ~x3, ~
                         but a ~x0 operand is expected."
                        in-type out-type arg type)))
          (acl2::value (list (make-expr-cast :type tyname
                                             :arg arg-expr)
                             out-type)))))
    (er-soft+ ctx t (irrelevant)
              "The term ~x0 used as an array element initializer ~
               does not have the required form."
              term))
  :measure (pseudo-term-count term)
  :verify-guards nil ; done below
  ///

  (more-returns
   (val true-listp :rule-classes :type-prescription))

  (verify-guards defobject-term-to-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defobject-process-init-term (term
                                     (elemtype typep)
                                     (ctx ctxp)
                                     state)
  :returns (mv erp (expr "An @(tsee exprp).") state)
  :mode :program
  :short "Process a term that is an element of the list @(':init')."
  :long
  (xdoc::topstring
   (xdoc::p
    "We translate the term.
     We check whether it has the form required in the user documentation,
     and whether it has the right type.
     We return the expression represented by the term,
     if all the checks succeed."))
  (b* (((er (list term stobjs-out))
        (acl2::ensure-value-is-untranslated-term$
         term (msg "The initializer term ~x0" term) t (irr-expr)))
       ((unless (equal stobjs-out (list nil)))
        (er-soft+ ctx t (irr-expr)
                  "The initializer term ~x0 must return ~
                   a single non-stobj value, ~
                   but it returns ~x1 instead."
                  term stobjs-out))
       ((er (list expr type) :iferr (irr-expr))
        (defobject-term-to-expr term ctx state))
       ((unless (equal type elemtype))
        (er-soft+ ctx t (irr-expr)
                  "The initializer term ~x0 has type ~x1, ~
                   which does not match the element type ~x2 of the array."
                  term type elemtype)))
    (acl2::value expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defobject-process-init-terms ((terms true-listp)
                                      (elemtype typep)
                                      (ctx ctxp)
                                      state)
  :returns (mv erp (exprs "An @(tsee expr-listp).") state)
  :mode :program
  :short "Process the list @(':init')."
  :long
  (xdoc::topstring
   (xdoc::p
    "We process each item,
     returning the corresponding list of expressions if successful."))
  (b* (((when (endp terms)) (acl2::value nil))
       ((er expr :iferr nil) (defobject-process-init-term
                               (car terms) elemtype ctx state))
       ((er exprs) (defobject-process-init-terms
                     (cdr terms) elemtype ctx state)))
    (acl2::value (cons expr exprs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defobject-process-init (init (type typep) (ctx ctxp) state)
  :returns (mv erp (exprs "An @(tsee expr-listp).") state)
  :mode :program
  :short "Process the @(':init') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that it is either @('nil'),
     or a list of terms that appropriately represent expressions,
     and that the length of the list (if not @('nil')) matches
     the (positive) size of the array type."))
  (b* (((er &)
        (acl2::ensure-value-is-true-list$ init
                                          (msg "The :INIT input ~x0" init)
                                          t
                                          nil))
       ((unless (type-case type :array))
        (acl2::value (raise "Internal error: not array type ~x0." type)))
       ((when (endp init)) (acl2::value nil))
       ((unless (equal (len init) (type-array->size type)))
        (er-soft+ ctx t nil
                  "The number ~x0 of elements of the :INIT input ~
                   must match the size ~x1 of the array ~
                   specified by the :TYPE input."
                  (len init) (type-array->size type))))
    (defobject-process-init-terms init (type-array->of type) ctx state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defobject-process-inputs (name
                                  type
                                  init
                                  (call pseudo-event-formp)
                                  (ctx ctxp)
                                  state)
  :returns (mv erp
               (val "A @('(tuple (name-string stringp)
                                 (name-ident identp)
                                 (type typep)
                                 (exprs expr-listp)
                                 (redundantp booleanp)
                                 val)').")
               state)
  :mode :program
  :short "Process the inputs of @(tsee defobject)."
  (b* (((acl2::fun (irrelevant)) (list "" (irr-ident) (irr-type) nil nil))
       ((er (list name-string name-ident redundantp):iferr (irrelevant))
        (defobject-process-name name call ctx state))
       ((when redundantp)
        (acl2::value (list name-string name-ident (irr-type) nil t)))
       ((er type :iferr (irrelevant))
        (defobject-process-type type ctx state))
       ((er exprs :iferr (irrelevant))
        (defobject-process-init init type ctx state)))
    (acl2::value (list name-string name-ident type exprs nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defobject-gen-everything ((name symbolp)
                                  (name-string stringp)
                                  (name-ident identp)
                                  (type typep)
                                  (init true-listp)
                                  (exprs expr-listp)
                                  (call pseudo-event-formp))
  :returns (event pseudo-event-formp)
  :short "Generate all the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the recognizer, initializer, and table event.
     They are put into one @(tsee progn) event.
     We conclude with a @(tsee deflabel) event
     that facilitates history manipulation."))
  (b* (((unless (and (type-case type :array)
                     (type-nonchar-integerp (type-array->of type))))
        (raise "Internal error: not integer array type ~x0." type)
        '(_))
       (fixtype (integer-type-to-fixtype (type-array->of type)))
       (size (type-array->size type))
       (recognizer-name (packn-pos (list 'object- name '-p) name))
       (initializer-name (packn-pos (list 'object- name '-init) name))
       (type-arrayp (pack fixtype '-arrayp))
       (type-array-length (pack fixtype '-array-length))
       (type-array-of (pack fixtype '-array-of))
       (recognizer-event
        `(define ,recognizer-name (x)
           :returns (yes/no booleanp)
           (and (,type-arrayp x)
                (equal (,type-array-length x) ,size))))
       (initializer-event
        `(define ,initializer-name ()
           :returns (object ,recognizer-name)
           (,type-array-of ,(if (consp init)
                                `(list ,@init)
                              `(repeat ,size (,fixtype 0))))))
       (info (make-defobject-info :name-ident name-ident
                                  :name-symbol name
                                  :type type
                                  :init exprs
                                  :recognizer recognizer-name
                                  :initializer initializer-name
                                  :call call))
       (table-event (defobject-table-record-event name-string info))
       (label-event `(deflabel ,name)))
    `(progn
       ,recognizer-event
       ,initializer-event
       ,table-event
       ,label-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defobject-fn (name
                      type
                      init
                      (call pseudo-event-formp)
                      (ctx ctxp)
                      state)
  :returns (mv erp
               (event "A @(tsee pseudo-event-formp).")
               state)
  :mode :program
  :short "Process the inputs and generate the events."
  (b* (((er (list name-string name-ident type exprs redundantp) :iferr '(_))
        (defobject-process-inputs name type init call ctx state))
       ((when redundantp) (acl2::value '(value-triple :redundant)))
       (event (defobject-gen-everything
                name name-string name-ident type init exprs call)))
    (acl2::value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defobject-macro-definition
  :short "Definition of @(tsee defobject)."
  (defmacro defobject (&whole call name &key type init)
    `(make-event (defobject-fn ',name ',type ',init ',call 'defobject state))))
