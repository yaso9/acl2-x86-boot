; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)

(include-book "std/util/defprojection" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule r1cs::sparse-vectorp-of-append
  (equal (r1cs::sparse-vectorp (append x y))
         (and (r1cs::sparse-vectorp (true-list-fix x))
              (r1cs::sparse-vectorp y)))
  :enable r1cs::sparse-vectorp)

(defrule r1cs::sparse-vectorp-of-rev
  (equal (r1cs::sparse-vectorp (rev x))
         (r1cs::sparse-vectorp (true-list-fix x)))
  :enable (r1cs::sparse-vectorp
           rev))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ r1cs-bridge
  :parents (prime-field-constraint-systems)
  :short "Bridge between PFCSes and R1CSes."
  :long
  (xdoc::topstring
   (xdoc::p
    "PFCSes are a generalization of R1CSes.
     Thus, there is an embedding of R1CSes into PFCSes,
     which we reify by providing a mapping from R1CSes and PFCSes."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define r1cs-pseudo-var-to-pfcs ((pvar r1cs::pseudo-varp))
  :returns (expr expressionp)
  :short "Translate an R1CS pseudo-variable to a PFCS expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "An R1CS pseudo-variable is either a symbol or the number 1.
     We translate the latter to the PFCS onstant 1,
     and a symbol to a PFCS variable with the same symbol."))
  (if (eql pvar 1)
      (expression-const 1)
    (expression-var pvar)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define r1cs-vec-elem-to-pfcs (elem)
  :guard (and (true-listp elem)
              (equal (len elem) 2)
              (integerp (first elem))
              (r1cs::pseudo-varp (second elem)))
  :returns (expr expressionp)
  :short "Translate an R1CS vector element to a PFCS expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "An element of an R1CS (sparse) vector is
     a list of two elements:
     an integer coefficient and a pseudo-variable.
     We translate this into a PFCS multiplication
     of the PFCS integer constant corresponding to the coefficient
     and of the PFCS expression for the pseudo-variable."))
  (make-expression-mul :arg1 (expression-const (first elem))
                       :arg2 (r1cs-pseudo-var-to-pfcs (second elem))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define r1cs-vector-to-pfcs ((vec r1cs::sparse-vectorp))
  :returns (expr expressionp)
  :short "Translate an R1CS (sparse) vector to a PFCS expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "We translate the empty vector to the PFCS constant 0.
     We translate a singleton vector to
     the element's corresponding PFCS expression.
     We translate vectors of two or more elements
     to (nested) PFCS additions;
     these are nested to the left,
     so we reverse the vector before the recursion."))
  (r1cs-vector-to-pfcs-aux (rev vec))

  :prepwork
  ((define r1cs-vector-to-pfcs-aux ((rev-vec r1cs::sparse-vectorp))
     :returns (expr expressionp)
     :parents nil
     (cond ((endp rev-vec) (expression-const 0))
           ((endp (cdr rev-vec)) (r1cs-vec-elem-to-pfcs (car rev-vec)))
           (t (make-expression-add
               :arg1 (r1cs-vector-to-pfcs-aux (cdr rev-vec))
               :arg2 (r1cs-vec-elem-to-pfcs (car rev-vec))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define r1cs-constraint-to-pfcs ((rconstr r1cs::r1cs-constraintp))
  :returns (pconstr constraintp)
  :short "Translate an R1CS constraint to a PFCS constraint."
  :long
  (xdoc::topstring
   (xdoc::p
    "We translate this to an equality constraint between
     (i) the product of @('a') and @('b') and (ii) @('c')."))
  (b* ((a-expr (r1cs-vector-to-pfcs (r1cs::r1cs-constraint->a rconstr)))
       (b-expr (r1cs-vector-to-pfcs (r1cs::r1cs-constraint->b rconstr)))
       (c-expr (r1cs-vector-to-pfcs (r1cs::r1cs-constraint->c rconstr))))
    (make-constraint-equal
     :left (make-expression-mul :arg1 a-expr :arg2 b-expr)
     :right c-expr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defprojection r1cs-constraints-to-pfcs (x)
  :guard (r1cs::r1cs-constraint-listp x)
  :returns (pconstrs constraint-listp)
  :short "Translate a list of R1CS constraints to a list of PFCS constraints."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are translated element-wise."))
  (r1cs-constraint-to-pfcs x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define r1cs-to-pfcs ((r1cs r1cs::r1csp) (name symbolp))
  :returns (def definitionp)
  :short "Translate an R1CS to a PFCS definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "An R!CS is formalized as consisting of
     a prime, a list of variables, and a list of constraints.
     It seems natural to translate this to a PFCS definition,
     whose parameters are the variables
     and whose body are the constraints.
     We ignore the prime,
     because PFCSes do not include primes in their syntax.
     In order to create a PFCS definition, we need a name for it;
     we pass that as an additional parameter to this ACL2 function."))
  (make-definition :name name
                   :para (r1cs::r1cs->vars r1cs)
                   :body (r1cs-constraints-to-pfcs
                          (r1cs::r1cs->constraints r1cs))))
