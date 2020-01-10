; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "aij-notions")

(include-book "../language/primitive-values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-java-types
  :parents (atj-implementation)
  :short "Java types generated by ATJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "ATJ generates certain Java types from corresponding ACL2 types.")
   (xdoc::p
    "The Java code generated by ATJ also uses some other Java types,
     but those are ``auxiliary'', in the sense that
     they are not the result of translating ACL2 types.
     We do not consider these auxiliary types here."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jtypep (x)
  :returns (yes/no booleanp)
  :short "Recognize the Java types generated by ATJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "This includes the types for
     all the AIJ public class types for ACL2 values
     (integers, rationals, numbers,
     characters, strings, symbols,
     @(tsee cons) pairs, and all values),
     all the Java primitive types except @('float') and @('double'),
     and all the Java primitive array types
     except @('float[]') and @('double[]').")
   (xdoc::p
    "For brevity, we call these types `ATJ Java types',
     instead of the longer `Java types generated by ATJ'."))
  (and (member-equal x (list *aij-type-int*
                             *aij-type-rational*
                             *aij-type-number*
                             *aij-type-char*
                             *aij-type-string*
                             *aij-type-symbol*
                             *aij-type-cons*
                             *aij-type-value*
                             (jtype-boolean)
                             (jtype-char)
                             (jtype-byte)
                             (jtype-short)
                             (jtype-int)
                             (jtype-long)
                             (jtype-array (jtype-boolean))
                             (jtype-array (jtype-char))
                             (jtype-array (jtype-byte))
                             (jtype-array (jtype-short))
                             (jtype-array (jtype-int))
                             (jtype-array (jtype-long))))
       t)
  ///

  (defrule jtypep-when-atj-jtypep
    (implies (atj-jtypep x)
             (jtypep x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist atj-jtype-listp (x)
  :short "Recognize true lists of ATJ Java types."
  (atj-jtypep x)
  :true-listp t
  :elementp-of-nil nil
  ///

  (defrule jtype-listp-when-atj-jtype-listp
    (implies (atj-jtype-listp x)
             (jtype-listp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist atj-jtype-list-listp (x)
  :short "Recognize true lists of true lists of ATJ Java types."
  (atj-jtype-listp x)
  :true-listp t
  :elementp-of-nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-maybe-jtypep (x)
  :returns (yes/no booleanp)
  :short "Recognize the ATJ Java types and @('nil')."
  (or (atj-jtypep x)
      (null x))
  ///

  (defrule atj-maybe-jtypep-when-atj-jtypep
    (implies (atj-jtypep x)
             (atj-maybe-jtypep x)))

  (defrule atj-jtype-iff-when-atj-maybe-jtypep
    (implies (atj-maybe-jtypep x)
             (iff (atj-jtypep x) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist atj-maybe-jtype-listp (x)
  :short "Recognize true lists of ATJ Java types and @('nil')s."
  (atj-maybe-jtypep x)
  :true-listp t
  :elementp-of-nil t
  ///

  (defrule atj-maybe-jtype-listp-when-atj-jtype-listp
    (implies (atj-jtype-listp x)
             (atj-maybe-jtype-listp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-jtype-<= ((sub atj-jtypep) (sup atj-jtypep))
  :returns (yes/no booleanp)
  :short "Partial order over the ATJ Java types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Java subtype relation [JLS:4.10]
     determines a partial order over the ATJ Java types.
     In general, whether a Java class type @('C')
     is a subtype of a Java class type @('D')
     depends on the declarations of the two class types;
     however, for the AIJ class types targeted by ATJ,
     those declarations are known,
     and thus we can define this partial order
     directly over @(tsee atj-jtypep).")
   (xdoc::p
    "The ordering over the AIJ class types is straightforward,
     according to the class hierarchy.
     The Java primitive types and the Java primitive array types
     are unrelated to class types:
     they are neither larger nor smaller than any class type.
     (Boxing conversions for the primitive types are not relevant here,
     because we consider the plain primitive types like @('int'),
     not the corresponding class types like @('java.lang.Integer').)
     The ordering over the primitive types is
     according to the subtype relation over primitive types [JLS:4.10.1].
     The primitive array types are unrelated to each other [JLS:4.10.3].")
   (xdoc::p
    "To validate this definition of partial order,
     we prove that the relation is indeed a partial order,
     i.e. reflexive, anti-symmetric, and transitive."))
  (cond ((equal sub *aij-type-int*)
         (and (member-equal sup (list *aij-type-int*
                                      *aij-type-rational*
                                      *aij-type-number*
                                      *aij-type-value*))
              t))
        ((equal sub *aij-type-rational*)
         (and (member-equal sup (list *aij-type-rational*
                                      *aij-type-number*
                                      *aij-type-value*))
              t))
        ((equal sub *aij-type-number*)
         (and (member-equal sup (list *aij-type-number*
                                      *aij-type-value*))
              t))
        ((equal sub *aij-type-char*)
         (and (member-equal sup (list *aij-type-char*
                                      *aij-type-value*))
              t))
        ((equal sub *aij-type-string*)
         (and (member-equal sup (list *aij-type-string*
                                      *aij-type-value*))
              t))
        ((equal sub *aij-type-symbol*)
         (and (member-equal sup (list *aij-type-symbol*
                                      *aij-type-value*))
              t))
        ((equal sub *aij-type-cons*)
         (and (member-equal sup (list *aij-type-cons*
                                      *aij-type-value*))
              t))
        ((equal sub *aij-type-value*) (equal sup *aij-type-value*))
        ((equal sub (jtype-boolean)) (equal sup (jtype-boolean)))
        ((equal sub (jtype-char)) (and (member-equal sup (list (jtype-char)
                                                               (jtype-int)
                                                               (jtype-long)))
                                       t))
        ((equal sub (jtype-byte)) (and (member-equal sup (list (jtype-byte)
                                                               (jtype-short)
                                                               (jtype-int)
                                                               (jtype-long)))
                                       t))
        ((equal sub (jtype-short)) (and (member-equal sup (list (jtype-short)
                                                                (jtype-int)
                                                                (jtype-long)))
                                        t))
        ((equal sub (jtype-int)) (and (member-equal sup (list (jtype-int)
                                                              (jtype-long)))
                                      t))
        ((equal sub (jtype-long)) (equal sup (jtype-long)))
        ((equal sub (jtype-array
                     (jtype-boolean))) (equal sup (jtype-array
                                                   (jtype-boolean))))
        ((equal sub (jtype-array
                     (jtype-char))) (equal sup (jtype-array
                                                (jtype-char))))
        ((equal sub (jtype-array
                     (jtype-byte))) (equal sup (jtype-array
                                                (jtype-byte))))
        ((equal sub (jtype-array
                     (jtype-short))) (equal sup (jtype-array
                                                 (jtype-short))))
        ((equal sub (jtype-array
                     (jtype-int))) (equal sup (jtype-array
                                               (jtype-int))))
        ((equal sub (jtype-array
                     (jtype-long))) (equal sup (jtype-array
                                                (jtype-long))))
        (t (impossible)))
  :guard-hints (("Goal" :in-theory (enable atj-jtypep)))
  ///

  (defrule atj-jtype-<=-reflexive
    (implies (atj-jtypep x)
             (atj-jtype-<= x x))
    :enable atj-jtypep)

  (defrule atj-jtype-<=-antisymmetric
    (implies (and (atj-jtypep x)
                  (atj-jtypep y)
                  (atj-jtype-<= x y)
                  (atj-jtype-<= y x))
             (equal x y))
    :rule-classes nil)

  (defrule atj-jtype-<=-transitive
    (implies (and (atj-jtypep x)
                  (atj-jtypep y)
                  (atj-jtypep z)
                  (atj-jtype-<= x y)
                  (atj-jtype-<= y z))
             (atj-jtype-<= x z))
    :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-maybe-jtype-<= ((sub atj-maybe-jtypep) (sup atj-maybe-jtypep))
  :returns (yes/no booleanp)
  :short "Extension of @(tsee atj-jtype-<=) to include @('nil') as bottom."
  :long
  (xdoc::topstring
   (xdoc::p
    "For certain purposes, we want to calculate
     the greatest lower bound of two ATJ Java types,
     with respect to the Java subtype relation @(tsee atj-jtype-<=).
     However, the ATJ Java types with this partial order
     do not quite form a meet semilattice,
     because there are no lower bounds, for instance,
     of both the primitive types and the AIJ class types.")
   (xdoc::p
    "Thus, we extend the partial order
     to the set of ATJ Java types plus @('nil'),
     where @('nil') is below every type.")
   (xdoc::p
    "We show that this extended relation is a partial order,
     i.e. reflexive, anti-symmetric, and transitive."))
  (if (atj-jtypep sub)
      (and (atj-jtypep sup)
           (atj-jtype-<= sub sup))
    t)
  ///

  (defrule atj-maybe-jtype-<=-reflexive
    (implies (atj-maybe-jtypep x)
             (atj-maybe-jtype-<= x x)))

  (defrule atj-maybe-jtype-<=-antisymmetric
    (implies (and (atj-maybe-jtypep x)
                  (atj-maybe-jtypep y)
                  (atj-maybe-jtype-<= x y)
                  (atj-maybe-jtype-<= y x))
             (equal x y))
    :rule-classes nil
    :use atj-jtype-<=-antisymmetric)

  (defrule atj-maybe-jtype-<=-transitive
    (implies (and (atj-maybe-jtypep x)
                  (atj-maybe-jtypep y)
                  (atj-maybe-jtypep z)
                  (atj-maybe-jtype-<= x y)
                  (atj-maybe-jtype-<= y z))
             (atj-maybe-jtype-<= x z))
    :rule-classes nil
    :use atj-jtype-<=-transitive))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-maybe-jtype-meet ((x atj-maybe-jtypep) (y atj-maybe-jtypep))
  :returns (glb atj-maybe-jtypep)
  :short "Greatest lower bound of two ATJ Java types or @('nil')s, according to
          the partial order over ATJ Java types extended to @('nil')."
  :long
  (xdoc::topstring
   (xdoc::p
    "As discussed in @(tsee atj-maybe-jtype-<=),
     the addition of @('nil') as bottom element to @(tsee atj-jtype-<=)
     results in a meet semilattice.")
   (xdoc::p
    "To validate this definition of greatest lower bound,
     we prove that this operation indeed returns a lower bound
     that is greater than or equal to any other lower bound,
     i.e. we prove that it returns the greatest lower bound.")
   (xdoc::p
    "The commutativity, idempotence, and associativity of this meet operation
     follows from these and the partial order properties,
     according to lattice theory.
     So we do not prove these properties explicitly here.")
   (xdoc::p
    "ATJ will use this greatest lower bound operation
     to ensure that generated overloaded methods
     can always be clearly selected based on the most specific argument types.
     ATJ will actually use the lifting of this operation to lists
     (since in general methods have multiple arguments),
     which we define later."))
  (b* ((x (if (mbt (atj-maybe-jtypep x)) x nil))
       (y (if (mbt (atj-maybe-jtypep y)) y nil)))
    (cond ((equal x *aij-type-char*)
           (cond ((member-equal y (list *aij-type-char*
                                        *aij-type-value*)) *aij-type-char*)
                 (t nil)))
          ((equal x *aij-type-string*)
           (cond ((member-equal y (list *aij-type-string*
                                        *aij-type-value*)) *aij-type-string*)
                 (t nil)))
          ((equal x *aij-type-symbol*)
           (cond ((member-equal y (list *aij-type-symbol*
                                        *aij-type-value*)) *aij-type-symbol*)
                 (t nil)))
          ((equal x *aij-type-int*)
           (cond ((member-equal y (list *aij-type-int*
                                        *aij-type-rational*
                                        *aij-type-number*
                                        *aij-type-value*)) *aij-type-int*)
                 (t nil)))
          ((equal x *aij-type-rational*)
           (cond ((equal y *aij-type-int*) *aij-type-int*)
                 ((member-equal y (list *aij-type-rational*
                                        *aij-type-number*
                                        *aij-type-value*)) *aij-type-rational*)
                 (t nil)))
          ((equal x *aij-type-number*)
           (cond ((equal y *aij-type-int*) *aij-type-int*)
                 ((equal y *aij-type-rational*) *aij-type-rational*)
                 ((member-equal y (list *aij-type-number*
                                        *aij-type-value*)) *aij-type-number*)
                 (t nil)))
          ((equal x *aij-type-cons*)
           (cond ((member-equal y (list *aij-type-cons*
                                        *aij-type-value*)) *aij-type-cons*)
                 (t nil)))
          ((equal x *aij-type-value*)
           (cond ((member-equal y (list (jtype-boolean)
                                        (jtype-char)
                                        (jtype-byte)
                                        (jtype-short)
                                        (jtype-int)
                                        (jtype-long)
                                        (jtype-array (jtype-boolean))
                                        (jtype-array (jtype-char))
                                        (jtype-array (jtype-byte))
                                        (jtype-array (jtype-short))
                                        (jtype-array (jtype-int))
                                        (jtype-array (jtype-long)))) nil)
                 (t y)))
          ((equal x (jtype-boolean))
           (cond ((equal y (jtype-boolean)) (jtype-boolean))
                 (t nil)))
          ((equal x (jtype-char))
           (cond ((member-equal y (list (jtype-char)
                                        (jtype-int)
                                        (jtype-long))) (jtype-char))
                 (t nil)))
          ((equal x (jtype-byte))
           (cond ((member-equal y (list (jtype-byte)
                                        (jtype-short)
                                        (jtype-int)
                                        (jtype-long))) (jtype-byte))
                 (t nil)))
          ((equal x (jtype-short))
           (cond ((member-equal y (list (jtype-short)
                                        (jtype-int)
                                        (jtype-long))) (jtype-short))
                 ((equal y (jtype-byte)) (jtype-byte))
                 (t nil)))
          ((equal x (jtype-int))
           (cond ((member-equal y (list (jtype-int)
                                        (jtype-long))) (jtype-int))
                 ((member-equal y (list (jtype-char)
                                        (jtype-byte)
                                        (jtype-short))) y)
                 (t nil)))
          ((equal x (jtype-long))
           (cond ((equal y (jtype-long)) (jtype-long))
                 ((member-equal y (list (jtype-char)
                                        (jtype-byte)
                                        (jtype-short)
                                        (jtype-int))) y)
                 (t nil)))
          ((equal x (jtype-array (jtype-boolean)))
           (cond ((equal y (jtype-array
                            (jtype-boolean))) (jtype-array (jtype-boolean)))
                 (t nil)))
          ((equal x (jtype-array (jtype-char)))
           (cond ((equal y (jtype-array
                            (jtype-char))) (jtype-array (jtype-char)))
                 (t nil)))
          ((equal x (jtype-array (jtype-byte)))
           (cond ((equal y (jtype-array
                            (jtype-byte))) (jtype-array (jtype-byte)))
                 (t nil)))
          ((equal x (jtype-array (jtype-short)))
           (cond ((equal y (jtype-array
                            (jtype-short))) (jtype-array (jtype-short)))
                 (t nil)))
          ((equal x (jtype-array (jtype-int)))
           (cond ((equal y (jtype-array
                            (jtype-int))) (jtype-array (jtype-int)))
                 (t nil)))
          ((equal x (jtype-array (jtype-long)))
           (cond ((equal y (jtype-array
                            (jtype-long))) (jtype-array (jtype-long)))
                 (t nil)))
          ((equal x nil) nil)
          (t (impossible))))
  :guard-hints (("Goal" :in-theory (enable atj-maybe-jtypep atj-jtypep)))
  ///

  (defrule atj-maybe-jtype-meet-lower-bound
    (implies (and (atj-maybe-jtypep x)
                  (atj-maybe-jtypep y))
             (and (atj-maybe-jtype-<= (atj-maybe-jtype-meet x y) x)
                  (atj-maybe-jtype-<= (atj-maybe-jtype-meet x y) y)))
    :enable (atj-maybe-jtype-<= atj-jtype-<= atj-jtypep))

  (defrule atj-maybe-jtype-meet-greatest
    (implies (and (atj-maybe-jtypep x)
                  (atj-maybe-jtypep y)
                  (atj-maybe-jtypep z)
                  (atj-maybe-jtype-<= z x)
                  (atj-maybe-jtype-<= z y))
             (atj-maybe-jtype-<= z (atj-maybe-jtype-meet x y)))
    :enable (atj-maybe-jtype-<= atj-jtype-<=)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-maybe-jtype-list-<= ((sub atj-maybe-jtype-listp)
                                 (sup atj-maybe-jtype-listp))
  :returns (yes/no booleanp)
  :short "Lift @(tsee atj-maybe-jtype-<=) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "Lists are ordered element-wise.
     Given two lists of different lengths
     such that the shorter one is a prefix of the longer one
     (i.e. the two lists cannot be ordered based on their initial elements),
     the shorter one is smaller than the longer one.")
   (xdoc::p
    "We show that the resulting relation is a partial order,
     i.e. reflexive, anti-symmetric, and transitive."))
  (cond ((endp sub) t)
        ((endp sup) nil)
        (t (and (atj-maybe-jtype-<= (car sub) (car sup))
                (atj-maybe-jtype-list-<= (cdr sub) (cdr sup)))))
  ///

  (defrule atj-maybe-jtype-list-<=-reflexive
    (implies (atj-maybe-jtype-listp x)
             (atj-maybe-jtype-list-<= x x)))

  (defrule atj-maybe-jtype-list-<=-antisymmetric
    (implies (and (atj-maybe-jtype-listp x)
                  (atj-maybe-jtype-listp y)
                  (atj-maybe-jtype-list-<= x y)
                  (atj-maybe-jtype-list-<= y x))
             (equal x y))
    :rule-classes nil
    :hints ('(:use (:instance atj-maybe-jtype-<=-antisymmetric
                    (x (car x)) (y (car y))))))

  (defrule atj-maybe-jtype-list-<=-transitive
    (implies (and (atj-maybe-jtype-listp x)
                  (atj-maybe-jtype-listp y)
                  (atj-maybe-jtype-listp z)
                  (atj-maybe-jtype-list-<= x y)
                  (atj-maybe-jtype-list-<= y z))
             (atj-maybe-jtype-list-<= x z))
    :rule-classes nil
    :hints ('(:use (:instance atj-maybe-jtype-<=-transitive
                    (x (car x)) (y (car y)) (z (car z)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-maybe-jtype-list-< ((sub atj-maybe-jtype-listp)
                                (sup atj-maybe-jtype-listp))
  :returns (yes/no booleanp)
  :short "Irreflexive kernel (i.e. strict version)
          of @(tsee atj-maybe-jtype-list-<=)."
  (and (atj-maybe-jtype-list-<= sub sup)
       (not (equal sub sup))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-maybe-jtype-list-meet ((x atj-maybe-jtype-listp)
                                   (y atj-maybe-jtype-listp))
  :returns (glb atj-maybe-jtype-listp)
  :short "Lift @(tsee atj-maybe-jtype-meet) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done element-wise,
     stopping when the shorter list is exhausted,
     and thus discarding the rest of the longer list.")
   (xdoc::p
    "We show that this indeed returns the greatest lower bound
     of the order relation lifted to lists."))
  (cond ((endp x) nil)
        ((endp y) nil)
        (t (cons (atj-maybe-jtype-meet (car x) (car y))
                 (atj-maybe-jtype-list-meet (cdr x) (cdr y)))))
  ///

  (defrule atj-maybe-jtype-list-meet-lower-bound
    (implies (and (atj-maybe-jtype-listp x)
                  (atj-maybe-jtype-listp y))
             (and (atj-maybe-jtype-list-<= (atj-maybe-jtype-list-meet x y) x)
                  (atj-maybe-jtype-list-<= (atj-maybe-jtype-list-meet x y) y)))
    :enable atj-maybe-jtype-list-<=)

  (defrule atj-maybe-jtype-list-meet-greatest
    (implies (and (atj-maybe-jtype-listp x)
                  (atj-maybe-jtype-listp y)
                  (atj-maybe-jtype-listp z)
                  (atj-maybe-jtype-list-<= z x)
                  (atj-maybe-jtype-list-<= z y))
             (atj-maybe-jtype-list-<= z (atj-maybe-jtype-list-meet x y)))
    :enable atj-maybe-jtype-list-<=))
