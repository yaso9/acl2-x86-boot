; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../language/abstract-syntax")

(include-book "kestrel/std/util/defirrelevant" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-abstract-syntax
  :parents (atc-implementation)
  :short "Abstract syntax of C for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "ATC generates C code by
     generating abstract syntax trees
     and pretty-printing them.
     For now we use the "
    (xdoc::seetopic "abstract-syntax" "abstract syntax")
    " from the C language formalization.
     In fact, that abstract syntax has been initially motivated by ATC.")
   (xdoc::p
    "However, in the future we may have a separate syntax for ATC,
     for the following reasons:")
   (xdoc::ol
    (xdoc::li
     "The abstract syntax from the C language formalization
      captures syntax after preprocessing,
      but at some point we may want ATC to generate code
      with at least some of the preprocessing constructs,
      such as @('#include')s, and possibly also some (simple) macros.
      This means that the ATC abstract syntax will have to mix
      preprocessing constructs with the preprocessed constructs:
      this is something that may not be part, in this mixed form,
      of the language formalization,
      which should differentiate between
      preprocessing translation units and
      (preprocessed) translation units.")
    (xdoc::li
     "We might want ATC to generate certain comments in the code,
      which would require the ATC abstract syntax to incorporate
      some information about comments.
      However, in the language formalization,
      comments, and their removal during one of C's translation phases,
      would be captured differently,
      not as part of the abstract syntax
      over which the language semantics is defined.")
    (xdoc::li
     "While the abstract syntax from the language formalization
      may be generalized to cover much more of the C language,
      the abstract syntax for ATC can incorporate restrictions
      that make it simpler and that fit the C code generated by ATC.
      In particular,
      the C syntax for declarations and related entities is quite complex,
      with significant mutual recursion,
      and with many constraints not directly captured by the C grammar.
      For instance, @('typedef') is classified as a storage class specifier,
      for syntactic convenience apparently [C:6.7.1/5],
      even though its role is very different from the others.
      Thus, by differentiating more explicitly, in our ATC abstract syntax,
      among different kinds of declarations and related entities,
      we make things more clear overall, as far as ATC is concerned."))
   (xdoc::p
    "Notwithstanding the above three reasons,
     in the short term, for expediency, we might actually
     incorporate preprocessing directives and comments,
     and impose restrictions,
     on the abstract syntax from the language formalization,
     rather than creating a separate abstract syntax for ATC.
     So long as the language formalization appropriately covers a subset of C,
     there is nothing inherently wrong with that approach.
     However, longer-term, as the language formalization is made more general,
     in particular covering the translation phases [C:5.1.12] explicitly,
     we will likely need to differentiate the abstract syntax for ATC
     from the one(s) from the language formalization.
     For proof generation,
     we would provide a mapping from the former to the latter,
     or in fact we may have the proof apply to the actual concrete syntax,
     if the language formalization includes parsing.")
   (xdoc::p
    "Some observations about some parts of the abstract syntax
     in relation to ATC:")
   (xdoc::ul
    (xdoc::li
     "The fixtype @(tsee ident) allows any ACL2 string,
      which may thus not be valid C identifiers.
      However, ATC always generates valid C identifiers.")
    (xdoc::li
     "The fixtype @(tsee ident) models only ASCII identifiers.
      For ATC, ASCII identifiers may be all that we need
      in the foreseeable future:
      we may not need to generate C programs with
      identifiers that include non-ASCII characters,
      some aspects of which may be
      implementation-dependent or locale-dependent.
      Since ASCII identifiers are portable,
      we plan for ATC to generate only ASCII identifiers,
      unless there will be reasons to support a broader range.")
    (xdoc::li
     "The fixtype @(tsee ident) allows identifiers of any length.
      In the interest of portability, it is our intention to have ATC
      generate identifiers of 31 characters or less
      (which is the minimum of significant characters in (external) identifiers
      [C:6.4.2.1/5] [C:6.4.2.1/6] [C:5.2.4.1]
      which may not be a significant limitation.")
    (xdoc::li
     "The fixtype @(tsee iconst) does not capture leading 0s
      in octal and hexadecimal constants.
      This is not a severe limitation,
      but at some point we may want ATC to generate
      something like @('0x0000ffff').")
    (xdoc::li
     "The fixtype @(tsee const) includes enuemration constants,
      which, as discussed there,
      cannot be differentiated from identifier expressions
      during parsing, but only after static semantic checking.
      This is not an issue for ATC, which generates, does not parse, C code:
      ATC can generate one or the other case in the code.")
    (xdoc::li
     "The fixtypes for declarations do not support function pointers.
      Most likely, this support will not be neded for ATC,
      given that ACL2 is first-order,
      and thus cannot readily represent C function pointers.
      (However, perhaps there is a way
      to represent function pointers with @(tsee apply$).)")
    (xdoc::li
     "The fixtype @(tsee block-item) only supports object declarations.
      This suffices for ATC currently.")
    (xdoc::li
     "The fixtype @(tsee fundef) could be alteratively defined as
      consisting of a function declaration and a body.
      However, even though this would work in abstract syntax,
      in concrete syntax a function declaration has to end with a semicolon
      (and that is why the grammar rule in [C:6.9.1/1]
      does not use a declaration, but rather its components):
      thus, for the ATC pretty-printer,
      we want to differentiate between
      the type specifier sequences and declarators
      that form a full function declaration,
      and the type specifier sequences and declarators
      that are part of a function definition.")))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-ident
  :short "An irrelevant identifier."
  :type identp
  :body (ident "_"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-iconst-length
  :short "An irrelevant length suffix."
  :type iconst-lengthp
  :body (iconst-length-none))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-iconst
  :short "An irrelevant integer constant."
  :type iconstp
  :body (make-iconst :value 0
                     :base (iconst-base-oct)
                     :unsignedp nil
                     :length (irr-iconst-length)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-tyspecseq
  :short "An irrelevant type specifier sequence."
  :type tyspecseqp
  :body (tyspecseq-void))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-tyname
  :short "An irrelevant type name."
  :type tynamep
  :body (make-tyname :tyspec (irr-tyspecseq)
                     :declor (obj-adeclor-none)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-unop
  :short "An irrelevant unary operator."
  :type unopp
  :body (unop-address))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-binop
  :short "An irrelevant binary operator."
  :type binopp
  :body (binop-asg))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-expr
  :short "An irrelevant expression."
  :type exprp
  :body (expr-const (const-int (irr-iconst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-tag-declon
  :short "An irrelevant structure/union/enumeration declaration."
  :type tag-declonp
  :body (make-tag-declon-struct :tag (irr-ident)
                                :members nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-param-declon
  :short "An irrelevant parameter declaration."
  :type param-declonp
  :body (make-param-declon :tyspec (irr-tyspecseq)
                           :declor (obj-declor-ident (irr-ident))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-initer
  :short "An irrelevant initializer."
  :type initerp
  :body (initer-single (irr-expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-stmt
  :short "An irrelevant statement."
  :type stmtp
  :body (stmt-null))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-block-item
  :short "An irrelevant block-item."
  :type block-itemp
  :body (block-item-stmt (irr-stmt)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-fundef
  :short "An irrelevant function definition."
  :type fundefp
  :body (make-fundef :tyspec (irr-tyspecseq)
                     :declor (make-fun-declor-base :name (irr-ident)
                                                   :params nil)
                     :body nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-ext-declon
  :short "An irrelevant external declaration."
  :type ext-declonp
  :body (ext-declon-fundef (irr-fundef)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-transunit
  :short "An irrelevant translation unit."
  :type transunitp
  :body (transunit nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-file
  :short "An irrelevant file."
  :type filep
  :body (file nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-fileset
  :short "An irrelevant file set."
  :type filesetp
  :body (make-fileset :path-wo-ext ""
                      :dot-h nil
                      :dot-c (irr-file)))
