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

(include-book "defstruct")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-tag-tables
  :parents (atc-event-and-code-generation)
  :short "Tables of @(tsee defstruct)s, and operations on these tables."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('tag') refers to the fact that C structure types,
     represented by @(tsee defstruct) in the shallow embedding,
     are identified by tags."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod atc-tag-info
  :short "Fixtype of information associated to
          an ACL2 @(tsee defstruct) symbol translated to a C structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of the information in the @(tsee defstruct) table
     plus some additional information that is more specific to ATC
     than to @(tsee defstruct), which is part of the shallow embedding.
     This additional information consists of:")
   (xdoc::ul
    (xdoc::li
     "The names of the theorems generated by ATC
      for rewriting calls of @(tsee exec-memberp)
      to calls of @(tsee defstruct) readers;
      see @(tsee atc-gen-tag-member-read-all-thms).")
    (xdoc::li
     "The names of the theorems generated by ATC
      for rewriting calls of @(tsee exec-expr-asg)
      with a @(':memberp') left expression
      to calls of @(tsee defstruct) writers;
      see @(tsee atc-gen-tag-member-write-all-thms)."))
   (xdoc::p
    "The latter theorems depend on
     @(tsee exec-memberp) and @(tsee exec-expr-asg),
     so they are not generated by @(tsee defstruct)
     to avoid having @(tsee defstruct) depend on
     those functions from the dynamic semantics."))
  ((defstruct defstruct-info)
   (member-read-thms symbol-list)
   (member-write-thms symbol-listp))
  :pred atc-tag-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist atc-string-taginfo-alist
  :short "Fixtype of alists from strings to tag information."
  :key-type string
  :val-type atc-tag-info
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred atc-string-taginfo-alistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-recognizers
  ((prec-tags atc-string-taginfo-alistp))
  :returns (recognizers symbol-listp)
  :short "Project the recognizers out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (recog (defstruct-info->recognizer (atc-tag-info->defstruct info)))
       (recogs (atc-string-taginfo-alist-to-recognizers (cdr prec-tags))))
    (cons recog recogs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-readers
  ((prec-tags atc-string-taginfo-alistp))
  :returns (readers symbol-listp)
  :short "Project the readers out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (readers (atc-string-taginfo-alist-to-readers-aux
                 (defstruct-info->members (atc-tag-info->defstruct info))))
       (more-readers (atc-string-taginfo-alist-to-readers (cdr prec-tags))))
    (append readers more-readers))
  :prepwork
  ((define atc-string-taginfo-alist-to-readers-aux
     ((members defstruct-member-info-listp))
     :returns (readers symbol-listp)
     :parents nil
     (b* (((when (endp members)) nil)
          (readers (defstruct-member-info->readers (car members)))
          (more-readers (atc-string-taginfo-alist-to-readers-aux
                         (cdr members))))
       (append readers more-readers)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-writers
  ((prec-tags atc-string-taginfo-alistp))
  :returns (writers symbol-listp)
  :short "Project the writers out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (writers (atc-string-taginfo-alist-to-writers-aux
                 (defstruct-info->members (atc-tag-info->defstruct info))))
       (more-writers (atc-string-taginfo-alist-to-writers (cdr prec-tags))))
    (append writers more-writers))
  :prepwork
  ((define atc-string-taginfo-alist-to-writers-aux
     ((members defstruct-member-info-listp))
     :returns (writers symbol-listp)
     :parents nil
     (b* (((when (endp members)) nil)
          (writers (defstruct-member-info->writers (car members)))
          (more-writers (atc-string-taginfo-alist-to-writers-aux
                         (cdr members))))
       (append writers more-writers)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-reader-return-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the return type theorems
          for structure readers
          out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thms (atc-string-taginfo-alist-to-reader-return-thms-aux
              (defstruct-info->members (atc-tag-info->defstruct info))))
       (more-thms
        (atc-string-taginfo-alist-to-reader-return-thms (cdr prec-tags))))
    (append thms more-thms))
  :prepwork
  ((define atc-string-taginfo-alist-to-reader-return-thms-aux
     ((members defstruct-member-info-listp))
     :returns (reader-return-thms symbol-listp)
     :parents nil
     (b* (((when (endp members)) nil)
          (thms (defstruct-member-info->reader-return-thms (car members)))
          (more-thms
           (atc-string-taginfo-alist-to-reader-return-thms-aux (cdr members))))
       (append thms more-thms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-writer-return-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the return type theorems
          for structure writers
          out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thms (atc-string-taginfo-alist-to-writer-return-thms-aux
              (defstruct-info->members (atc-tag-info->defstruct info))))
       (more-thms
        (atc-string-taginfo-alist-to-writer-return-thms (cdr prec-tags))))
    (append thms more-thms))
  :prepwork
  ((define atc-string-taginfo-alist-to-writer-return-thms-aux
     ((members defstruct-member-info-listp))
     :returns (writer-return-thms symbol-listp)
     :parents nil
     (b* (((when (endp members)) nil)
          (thms (defstruct-member-info->writer-return-thms (car members)))
          (more-thms
           (atc-string-taginfo-alist-to-writer-return-thms-aux (cdr members))))
       (append thms more-thms)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-not-error-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the non-error theorems out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thm (defstruct-info->not-error-thm (atc-tag-info->defstruct info)))
       (thms (atc-string-taginfo-alist-to-not-error-thms (cdr prec-tags))))
    (cons thm thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-valuep-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the @(tsee valuep) theorems out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thm (defstruct-info->valuep-thm (atc-tag-info->defstruct info)))
       (thms (atc-string-taginfo-alist-to-valuep-thms (cdr prec-tags))))
    (cons thm thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-value-kind-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the @(tsee value-kind) theorems
          out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thm (defstruct-info->value-kind-thm (atc-tag-info->defstruct info)))
       (thms (atc-string-taginfo-alist-to-value-kind-thms (cdr prec-tags))))
    (cons thm thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-type-of-value-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the @(tsee type-of-value) theorems
          out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thm (defstruct-info->type-of-value-thm (atc-tag-info->defstruct info)))
       (thms (atc-string-taginfo-alist-to-type-of-value-thms (cdr prec-tags))))
    (cons thm thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-flexiblep-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the @('flexiblep') flag theorems
          out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thm (defstruct-info->flexiblep-thm (atc-tag-info->defstruct info)))
       (thms (atc-string-taginfo-alist-to-flexiblep-thms (cdr prec-tags))))
    (cons thm thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-member-read-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the @(tsee exec-memberp) theorems
          out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thms (atc-tag-info->member-read-thms info))
       (more-thms
        (atc-string-taginfo-alist-to-member-read-thms (cdr prec-tags))))
    (append thms more-thms)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-string-taginfo-alist-to-member-write-thms
  ((prec-tags atc-string-taginfo-alistp))
  :returns (thms symbol-listp)
  :short "Project the @(tsee exec-expr-asg) with @(':memberp') theorems
          out of a tag information alist."
  (b* (((when (endp prec-tags)) nil)
       (info (cdar prec-tags))
       (thms (atc-tag-info->member-write-thms info))
       (more-thms
        (atc-string-taginfo-alist-to-member-write-thms (cdr prec-tags))))
    (append thms more-thms)))
