(APPLY-FOR-DEFEVALUATOR)
(REPL-EV)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(REPL-EV-OF-FNCALL-ARGS)
(REPL-EV-OF-VARIABLE)
(REPL-EV-OF-QUOTE)
(REPL-EV-OF-LAMBDA)
(REPL-EV-LST-OF-ATOM)
(REPL-EV-LST-OF-CONS)
(REPL-EV-OF-NONSYMBOL-ATOM)
(REPL-EV-OF-BAD-FNCALL)
(REPL-EV-OF-TYPESPEC-CHECK-CALL)
(REPL-EV-OF-IF-CALL)
(REPL-EV-OF-EQUAL-CALL)
(REPL-EV-OF-NOT-CALL)
(REPL-EV-OF-IFF-CALL)
(REPL-EV-OF-IMPLIES-CALL)
(REPL-EV-OF-CONS-CALL)
(REPL-EV-OF-BINARY-+-CALL)
(REPL-EV-DISJOIN-CONS)
(REPL-EV-DISJOIN-WHEN-CONSP)
(REPL-EV-DISJOIN-ATOM
 (1 1 (:REWRITE REPL-EV-OF-IF-CALL))
 )
(REPL-EV-DISJOIN-APPEND
 (23 23 (:REWRITE REPL-EV-OF-QUOTE))
 (23 23 (:REWRITE REPL-EV-OF-IF-CALL))
 )
(REPL-EV-CONJOIN-CONS)
(REPL-EV-CONJOIN-WHEN-CONSP)
(REPL-EV-CONJOIN-ATOM
 (1 1 (:REWRITE REPL-EV-OF-IF-CALL))
 )
(REPL-EV-CONJOIN-APPEND
 (23 23 (:REWRITE REPL-EV-OF-QUOTE))
 (23 23 (:REWRITE REPL-EV-OF-IF-CALL))
 )
(REPL-EV-CONJOIN-CLAUSES-CONS
 (100 50 (:DEFINITION DISJOIN))
 (50 50 (:DEFINITION DISJOIN2))
 (7 7 (:REWRITE REPL-EV-DISJOIN-ATOM))
 (5 5 (:REWRITE REPL-EV-CONJOIN-ATOM))
 )
(REPL-EV-CONJOIN-CLAUSES-WHEN-CONSP
 (24 24 (:REWRITE REPL-EV-OF-QUOTE))
 (24 24 (:REWRITE REPL-EV-OF-IF-CALL))
 (18 9 (:DEFINITION DISJOIN))
 (9 9 (:REWRITE REPL-EV-DISJOIN-ATOM))
 (9 9 (:DEFINITION DISJOIN2))
 )
(REPL-EV-CONJOIN-CLAUSES-ATOM
 (1 1 (:REWRITE REPL-EV-OF-IF-CALL))
 )
(REPL-EV-CONJOIN-CLAUSES-APPEND
 (65 65 (:REWRITE REPL-EV-OF-QUOTE))
 (65 65 (:REWRITE REPL-EV-OF-IF-CALL))
 (24 12 (:DEFINITION DISJOIN))
 (12 12 (:REWRITE REPL-EV-DISJOIN-ATOM))
 (12 12 (:DEFINITION DISJOIN2))
 )
(REPL-EV-THEOREMP-CONJOIN-CONS
 (53 53 (:REWRITE REPL-EV-CONJOIN-ATOM))
 )
(REPL-EV-THEOREMP-CONJOIN-APPEND)
(REPL-EV-THEOREMP-CONJOIN-CLAUSES-CONS
 (3 3 (:REWRITE REPL-EV-DISJOIN-ATOM))
 (3 3 (:REWRITE REPL-EV-CONJOIN-ATOM))
 )
(REPL-EV-THEOREMP-CONJOIN-CLAUSES-APPEND
 (15 15 (:REWRITE REPL-EV-DISJOIN-ATOM))
 )
(REPL-EV-THEOREMP-DISJOIN-CONS-UNLESS-THEOREMP
 (4 4 (:REWRITE REPL-EV-DISJOIN-ATOM))
 )
(REPL-EV-THEOREMP-DISJOIN-WHEN-CONSP-UNLESS-THEOREMP
 (4 4 (:REWRITE REPL-EV-DISJOIN-ATOM))
 )
(REPL-EV-FALSIFY-SUFFICIENT)
(REPL-EV-META-EXTRACT-CONTEXTUAL-BADGUY-SUFFICIENT)
(REPL-EV-META-EXTRACT-GLOBAL-BADGUY-SUFFICIENT)
(REPL-EV-META-EXTRACT-GLOBAL-BADGUY-TRUE-LISTP)
(REPL-EV-META-EXTRACT-TYPESET)
(REPL-EV-META-EXTRACT-RW+-EQUAL)
(REPL-EV-META-EXTRACT-RW+-IFF)
(REPL-EV-META-EXTRACT-RW+-EQUIV)
(REPL-EV-META-EXTRACT-RW-EQUAL)
(REPL-EV-META-EXTRACT-RW-IFF)
(REPL-EV-META-EXTRACT-RW-EQUIV)
(REPL-EV-META-EXTRACT-MFC-AP)
(REPL-EV-META-EXTRACT-RELIEVE-HYP)
(REPL-EV-META-EXTRACT-FORMULA
 (9 9 (:REWRITE REPL-EV-OF-VARIABLE))
 (9 9 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (9 9 (:REWRITE REPL-EV-OF-QUOTE))
 (9 9 (:REWRITE REPL-EV-OF-NOT-CALL))
 (9 9 (:REWRITE REPL-EV-OF-LAMBDA))
 (9 9 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (9 9 (:REWRITE REPL-EV-OF-IFF-CALL))
 (9 9 (:REWRITE REPL-EV-OF-IF-CALL))
 (9 9 (:REWRITE REPL-EV-OF-EQUAL-CALL))
 (8 8 (:REWRITE REPL-EV-OF-NONSYMBOL-ATOM))
 (8 8 (:REWRITE REPL-EV-OF-BAD-FNCALL))
 )
(REPL-EV-META-EXTRACT-LEMMA-TERM)
(REPL-EV-META-EXTRACT-LEMMA)
(REPL-EV-META-EXTRACT-FNCALL-LOGIC)
(REPL-EV-META-EXTRACT-FNCALL)
(REPL-EV-META-EXTRACT-MAGIC-EV)
(REPL-EV-META-EXTRACT-MAGIC-EV-LST)
(REPL-EV-META-EXTRACT-FN-CHECK-DEF)
(REPL-EV-LST-OF-PAIRLIS)
(REPL-EV-LST-OF-PAIRLIS-APPEND-REST)
(REPL-EV-LST-OF-PAIRLIS-APPEND-HEAD-REST)
(REPL-EV-ALIST)
(SIMPLE-ONE-WAY-UNIFY-CORRECT-FOR-REPL-EV
 (39 30 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (39 30 (:REWRITE REPL-EV-OF-NOT-CALL))
 (39 30 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (39 30 (:REWRITE REPL-EV-OF-IFF-CALL))
 (39 30 (:REWRITE REPL-EV-OF-IF-CALL))
 (39 30 (:REWRITE REPL-EV-OF-EQUAL-CALL))
 (30 30 (:REWRITE CAR-CONS))
 (8 8 (:REWRITE REPL-EV-LST-OF-ATOM))
 (8 4 (:DEFINITION KWOTE-LST))
 (4 4 (:REWRITE REPL-EV-META-EXTRACT-FN-CHECK-DEF))
 (4 4 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (4 4 (:DEFINITION KWOTE))
 (3 2 (:REWRITE DEFAULT-+-2))
 (3 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:DEFINITION PAIRLIS$))
 (2 2 (:DEFINITION ASSOC-EQUAL))
 )
(SIMPLE-ONE-WAY-UNIFY-LST-CORRECT-FOR-REPL-EV)
(SUBSTITUTE-INTO-TERM-CORRECT-FOR-REPL-EV)
(SUBSTITUTE-INTO-LIST-CORRECT-FOR-REPL-EV)
(REPL-EV-SIMPLE-ONE-WAY-UNIFY-EQUALITIES)
(SIMPLE-ONE-WAY-UNIFY-WITH-REPL-EV
 (36 3 (:DEFINITION REPL-EV-ALIST))
 (14 14 (:REWRITE SIMPLE-ONE-WAY-UNIFY-USAGE))
 (9 9 (:REWRITE REPL-EV-OF-VARIABLE))
 (9 9 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (9 9 (:REWRITE REPL-EV-OF-QUOTE))
 (9 9 (:REWRITE REPL-EV-OF-NOT-CALL))
 (9 9 (:REWRITE REPL-EV-OF-LAMBDA))
 (9 9 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (9 9 (:REWRITE REPL-EV-OF-IFF-CALL))
 (9 9 (:REWRITE REPL-EV-OF-IF-CALL))
 (9 9 (:REWRITE REPL-EV-OF-EQUAL-CALL))
 (9 9 (:REWRITE REPL-EV-OF-CONS-CALL))
 (9 9 (:REWRITE REPL-EV-OF-BINARY-+-CALL))
 )
(REPL-EV-SIMPLE-ONE-WAY-UNIFY-EQUALITIES-OF-NIL)
(REPL-EV-SIMPLE-ONE-WAY-UNIFY-EQUALITIES-OF-CONS
 (60 5 (:DEFINITION REPL-EV-ALIST))
 (15 15 (:REWRITE REPL-EV-OF-VARIABLE))
 (15 15 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (15 15 (:REWRITE REPL-EV-OF-QUOTE))
 (15 15 (:REWRITE REPL-EV-OF-NOT-CALL))
 (15 15 (:REWRITE REPL-EV-OF-LAMBDA))
 (15 15 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (15 15 (:REWRITE REPL-EV-OF-IFF-CALL))
 (15 15 (:REWRITE REPL-EV-OF-IF-CALL))
 (15 15 (:REWRITE REPL-EV-OF-EQUAL-CALL))
 (15 15 (:REWRITE REPL-EV-OF-CONS-CALL))
 (15 15 (:REWRITE REPL-EV-OF-BINARY-+-CALL))
 )
(REPL-EV-LST-SIMPLE-ONE-WAY-UNIFY-EQUALITIES)
(SIMPLE-ONE-WAY-UNIFY-LST-WITH-REPL-EV
 (56 11 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (56 11 (:REWRITE PSEUDO-TERMP-CAR))
 (55 11 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (40 40 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (40 40 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (36 3 (:DEFINITION REPL-EV-ALIST))
 (22 22 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (22 22 (:REWRITE PSEUDO-TERMP-OPENER))
 (14 14 (:REWRITE SIMPLE-ONE-WAY-UNIFY-LST-USAGE))
 (6 6 (:REWRITE REPL-EV-LST-OF-CONS))
 (6 6 (:REWRITE REPL-EV-LST-OF-ATOM))
 (3 3 (:REWRITE REPL-EV-OF-VARIABLE))
 (3 3 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (3 3 (:REWRITE REPL-EV-OF-QUOTE))
 (3 3 (:REWRITE REPL-EV-OF-NOT-CALL))
 (3 3 (:REWRITE REPL-EV-OF-LAMBDA))
 (3 3 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (3 3 (:REWRITE REPL-EV-OF-IFF-CALL))
 (3 3 (:REWRITE REPL-EV-OF-IF-CALL))
 (3 3 (:REWRITE REPL-EV-OF-EQUAL-CALL))
 (3 3 (:REWRITE REPL-EV-OF-CONS-CALL))
 (3 3 (:REWRITE REPL-EV-OF-BINARY-+-CALL))
 )
(REPL-EV-LST-SIMPLE-ONE-WAY-UNIFY-EQUALITIES-OF-NIL)
(REPL-EV-LST-SIMPLE-ONE-WAY-UNIFY-EQUALITIES-OF-CONS
 (60 5 (:DEFINITION REPL-EV-ALIST))
 (10 10 (:REWRITE REPL-EV-LST-OF-CONS))
 (10 10 (:REWRITE REPL-EV-LST-OF-ATOM))
 (5 5 (:REWRITE REPL-EV-OF-VARIABLE))
 (5 5 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (5 5 (:REWRITE REPL-EV-OF-QUOTE))
 (5 5 (:REWRITE REPL-EV-OF-NOT-CALL))
 (5 5 (:REWRITE REPL-EV-OF-LAMBDA))
 (5 5 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (5 5 (:REWRITE REPL-EV-OF-IFF-CALL))
 (5 5 (:REWRITE REPL-EV-OF-IF-CALL))
 (5 5 (:REWRITE REPL-EV-OF-EQUAL-CALL))
 (5 5 (:REWRITE REPL-EV-OF-CONS-CALL))
 (5 5 (:REWRITE REPL-EV-OF-BINARY-+-CALL))
 )
(REPL-EV-EQUALITY-ALIST-P
 (4 4 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE DEFAULT-CDR))
 )
(ASSOC-IN-REPL-EV-EQUALITY-ALIST
 (57 57 (:REWRITE DEFAULT-CAR))
 (24 24 (:REWRITE REPL-EV-OF-VARIABLE))
 (24 24 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (24 24 (:REWRITE REPL-EV-OF-QUOTE))
 (24 24 (:REWRITE REPL-EV-OF-NOT-CALL))
 (24 24 (:REWRITE REPL-EV-OF-LAMBDA))
 (24 24 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (24 24 (:REWRITE REPL-EV-OF-IFF-CALL))
 (24 24 (:REWRITE REPL-EV-OF-IF-CALL))
 (24 24 (:REWRITE REPL-EV-OF-EQUAL-CALL))
 (24 24 (:REWRITE REPL-EV-OF-CONS-CALL))
 (24 24 (:REWRITE REPL-EV-OF-BINARY-+-CALL))
 (18 18 (:REWRITE DEFAULT-CDR))
 )
(SUBST-SUBTERMS
 (131 1 (:DEFINITION PSEUDO-TERMP))
 (66 32 (:REWRITE DEFAULT-+-2))
 (49 6 (:DEFINITION LENGTH))
 (48 7 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (43 32 (:REWRITE DEFAULT-+-1))
 (35 7 (:DEFINITION LEN))
 (32 32 (:REWRITE DEFAULT-CDR))
 (32 32 (:REWRITE DEFAULT-CAR))
 (30 4 (:REWRITE PSEUDO-TERMP-CAR))
 (29 1 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (24 6 (:REWRITE COMMUTATIVITY-OF-+))
 (24 6 (:DEFINITION INTEGER-ABS))
 (22 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (16 7 (:REWRITE PSEUDO-TERMP-OPENER))
 (12 12 (:TYPE-PRESCRIPTION LEN))
 (11 11 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (10 2 (:DEFINITION ASSOC-EQUAL))
 (9 9 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (9 7 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 7 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 (4 2 (:DEFINITION TRUE-LISTP))
 (4 1 (:DEFINITION SYMBOL-LISTP))
 (3 3 (:REWRITE DEFAULT-REALPART))
 (3 3 (:REWRITE DEFAULT-NUMERATOR))
 (3 3 (:REWRITE DEFAULT-IMAGPART))
 (3 3 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE FN-CHECK-DEF-FORMALS))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 )
(SUBST-SUBTERMS-FLAG
 (4 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(SUBST-SUBTERMS-FLAG-EQUIVALENCES)
(LEN-SUBST-SUBTERMS-LIST
 (48 24 (:REWRITE DEFAULT-+-2))
 (41 40 (:REWRITE DEFAULT-CDR))
 (24 24 (:REWRITE DEFAULT-+-1))
 (16 16 (:REWRITE DEFAULT-CAR))
 (11 1 (:DEFINITION SUBST-SUBTERMS))
 (5 1 (:DEFINITION ASSOC-EQUAL))
 (1 1 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 )
(FLAG-LEMMA-FOR-PSEUDO-TERMP-SUBST-SUBTERMS
 (661 26 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (520 476 (:REWRITE DEFAULT-CAR))
 (471 461 (:REWRITE DEFAULT-CDR))
 (382 137 (:REWRITE PSEUDO-TERMP-OPENER))
 (235 235 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (180 90 (:REWRITE DEFAULT-+-2))
 (116 116 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (90 90 (:REWRITE DEFAULT-+-1))
 (43 43 (:REWRITE FN-CHECK-DEF-FORMALS))
 (30 30 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (18 18 (:REWRITE DEFAULT-COERCE-2))
 (18 18 (:REWRITE DEFAULT-COERCE-1))
 (16 16 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (12 12 (:REWRITE PSEUDO-TERM-VAL-ALISTP-OF-ATOM))
 )
(PSEUDO-TERMP-SUBST-SUBTERMS)
(PSEUDO-TERM-LISTP-SUBST-SUBTERMS-LIST)
(FLAG-LEMMA-FOR-SUBST-SUBTERMS-CORRECT
 (163 140 (:REWRITE DEFAULT-CAR))
 (66 64 (:REWRITE DEFAULT-CDR))
 (43 32 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (43 32 (:REWRITE REPL-EV-OF-NOT-CALL))
 (43 32 (:REWRITE REPL-EV-OF-LAMBDA))
 (43 32 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (43 32 (:REWRITE REPL-EV-OF-IFF-CALL))
 (43 32 (:REWRITE REPL-EV-OF-IF-CALL))
 (43 32 (:REWRITE REPL-EV-OF-EQUAL-CALL))
 (43 32 (:REWRITE REPL-EV-OF-CONS-CALL))
 (43 32 (:REWRITE REPL-EV-OF-BINARY-+-CALL))
 (33 33 (:TYPE-PRESCRIPTION KWOTE-LST))
 (33 30 (:REWRITE REPL-EV-OF-VARIABLE))
 (8 2 (:DEFINITION KWOTE-LST))
 (4 4 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (3 3 (:REWRITE REPL-EV-META-EXTRACT-FN-CHECK-DEF))
 (2 2 (:DEFINITION KWOTE))
 )
(SUBST-SUBTERMS-CORRECT)
(SUBST-SUBTERMS-LIST-CORRECT)
(DISJOIN-SUBST-SUBTERMS-LIST-CORRECT
 (220 57 (:REWRITE ASSOC-IN-REPL-EV-EQUALITY-ALIST))
 (178 44 (:DEFINITION ASSOC-EQUAL))
 (146 146 (:REWRITE DEFAULT-CAR))
 (100 100 (:REWRITE DEFAULT-CDR))
 (49 49 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (49 49 (:REWRITE REPL-EV-OF-NOT-CALL))
 (49 49 (:REWRITE REPL-EV-OF-LAMBDA))
 (49 49 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (49 49 (:REWRITE REPL-EV-OF-IFF-CALL))
 (49 49 (:REWRITE REPL-EV-OF-IF-CALL))
 (49 49 (:REWRITE REPL-EV-OF-EQUAL-CALL))
 (49 49 (:REWRITE REPL-EV-OF-CONS-CALL))
 (49 49 (:REWRITE REPL-EV-OF-BINARY-+-CALL))
 (48 48 (:TYPE-PRESCRIPTION SUBST-SUBTERMS-LIST))
 (48 48 (:REWRITE REPL-EV-OF-VARIABLE))
 (33 3 (:DEFINITION SUBST-SUBTERMS))
 (3 3 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (1 1 (:REWRITE REPL-EV-META-EXTRACT-FN-CHECK-DEF))
 )
(MATCH-TREE-PSEUDO-TERMP
 (262 2 (:DEFINITION PSEUDO-TERMP))
 (62 10 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (58 2 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (52 4 (:REWRITE PSEUDO-TERMP-CAR))
 (50 6 (:DEFINITION LENGTH))
 (42 42 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (42 10 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (40 8 (:DEFINITION LEN))
 (34 34 (:REWRITE DEFAULT-CDR))
 (28 28 (:REWRITE DEFAULT-CAR))
 (28 10 (:REWRITE PSEUDO-TERMP-OPENER))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (16 16 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (16 16 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (16 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (8 8 (:REWRITE DEFAULT-+-1))
 (8 4 (:DEFINITION TRUE-LISTP))
 (8 2 (:DEFINITION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION MATCH-TREE-MATCHEDP))
 (4 4 (:REWRITE FN-CHECK-DEF-FORMALS))
 (4 1 (:REWRITE MATCH-TREE-ALIST-RW-WHEN-MATCHED))
 (3 1 (:REWRITE MATCH-TREE-WHEN-MATCHEDP))
 (3 1 (:REWRITE MATCH-TREE-ALIST-RW-WHEN-MATCH-TREE-MATCHEDP))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE SUBST-TREE-OPEN))
 )
(UNIFY-LIT-WITH-EQUALITY-RULE
 (8665 294 (:REWRITE PSEUDO-TERMP-CAR))
 (7204 89 (:DEFINITION PSEUDO-TERM-LISTP))
 (6821 221 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (4573 504 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (2116 2107 (:REWRITE DEFAULT-CDR))
 (1934 1925 (:REWRITE DEFAULT-CAR))
 (1874 358 (:DEFINITION LEN))
 (781 775 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (774 774 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (736 368 (:REWRITE DEFAULT-+-2))
 (485 86 (:DEFINITION SYMBOL-LISTP))
 (468 468 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (368 368 (:REWRITE DEFAULT-+-1))
 (344 344 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (172 172 (:REWRITE FN-CHECK-DEF-FORMALS))
 (143 143 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (141 6 (:REWRITE PSEUDO-TERMP-CDR-ASSOC-EQUAL))
 (90 90 (:REWRITE DEFAULT-COERCE-2))
 (90 90 (:REWRITE DEFAULT-COERCE-1))
 (24 6 (:REWRITE PSEUDO-TERMP-OF-LOOKUP-IN-SUBST))
 (24 6 (:REWRITE PSEUDO-TERMP-OF-LOOKUP-IN-PSEUDO-TERM-VAL-ALISTP))
 (24 6 (:DEFINITION STRIP-CDRS))
 (12 12 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (12 12 (:TYPE-PRESCRIPTION PSEUDO-TERM-VAL-ALISTP))
 (12 12 (:TYPE-PRESCRIPTION PSEUDO-TERM-SUBSTP))
 (12 4 (:REWRITE MATCH-TREE-WHEN-MATCHEDP))
 (6 6 (:REWRITE UNIFY-SUCCEEDED-IMPLIES))
 (6 6 (:REWRITE SIMPLE-ONE-WAY-UNIFY-WITH-REPL-EV))
 (6 6 (:REWRITE SIMPLE-ONE-WAY-UNIFY-USAGE))
 (6 6 (:REWRITE PSEUDO-TERM-VAL-ALISTP-OF-ATOM))
 (6 6 (:REWRITE PSEUDO-TERM-SUBSTP-OF-ATOM))
 (6 6 (:REWRITE ASSOC-IN-MATCH-TREE))
 (5 1 (:REWRITE MATCH-TREE-ALIST-RW-WHEN-MATCHED))
 (4 2 (:REWRITE SYMBOLP-BY-MATCH-TREE-RESTRICTIONS))
 (2 2 (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
 )
(UNIFY-LIT-WITH-EQUALITY-RULE-CDR-PSEUDO-TERMP
 (6059 45 (:DEFINITION PSEUDO-TERMP))
 (4846 262 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (4576 113 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (3629 40 (:DEFINITION PSEUDO-TERM-LISTP))
 (3595 142 (:REWRITE PSEUDO-TERMP-CAR))
 (2743 262 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (1228 1228 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1195 135 (:DEFINITION LENGTH))
 (1072 1063 (:REWRITE DEFAULT-CDR))
 (966 186 (:DEFINITION LEN))
 (940 940 (:REWRITE DEFAULT-CAR))
 (843 843 (:TYPE-PRESCRIPTION LEN))
 (424 92 (:DEFINITION TRUE-LISTP))
 (389 389 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (389 389 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (380 190 (:REWRITE DEFAULT-+-2))
 (264 45 (:DEFINITION SYMBOL-LISTP))
 (241 241 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (216 216 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (190 190 (:REWRITE DEFAULT-+-1))
 (157 157 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (90 90 (:REWRITE FN-CHECK-DEF-FORMALS))
 (70 70 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (47 47 (:REWRITE DEFAULT-COERCE-2))
 (47 47 (:REWRITE DEFAULT-COERCE-1))
 (18 6 (:REWRITE SUBSTITUTE-INTO-ONE-WAY-UNIFY-REDUCE))
 (12 12 (:TYPE-PRESCRIPTION ALL-KEYS-BOUND))
 (9 3 (:REWRITE MATCH-TREE-BINDERS-BOUND))
 (6 2 (:REWRITE MATCH-TREE-WHEN-MATCHEDP))
 (5 1 (:REWRITE MATCH-TREE-ALIST-RW-WHEN-MATCHED))
 (4 4 (:REWRITE UNIFY-SUCCEEDED-IMPLIES))
 (4 4 (:REWRITE SIMPLE-ONE-WAY-UNIFY-WITH-REPL-EV))
 (4 4 (:REWRITE SIMPLE-ONE-WAY-UNIFY-USAGE))
 (3 3 (:TYPE-PRESCRIPTION SYMBOL-ALISTP))
 (3 3 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (3 3 (:REWRITE ASSOC-IN-MATCH-TREE))
 )
(MATCH-TREE-REPL-EV
 (5 1 (:REWRITE MATCH-TREE-ALIST-RW-WHEN-MATCHED))
 (4 4 (:TYPE-PRESCRIPTION MATCH-TREE-MATCHEDP))
 (3 1 (:REWRITE MATCH-TREE-WHEN-MATCHEDP))
 (3 1 (:REWRITE MATCH-TREE-ALIST-RW-WHEN-MATCH-TREE-MATCHEDP))
 (2 2 (:REWRITE REPL-EV-OF-VARIABLE))
 (2 2 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (2 2 (:REWRITE REPL-EV-OF-QUOTE))
 (2 2 (:REWRITE REPL-EV-OF-NOT-CALL))
 (2 2 (:REWRITE REPL-EV-OF-LAMBDA))
 (2 2 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (2 2 (:REWRITE REPL-EV-OF-IFF-CALL))
 (2 2 (:REWRITE REPL-EV-OF-IF-CALL))
 (2 2 (:REWRITE REPL-EV-OF-EQUAL-CALL))
 (2 2 (:REWRITE REPL-EV-OF-CONS-CALL))
 (2 2 (:REWRITE REPL-EV-OF-BINARY-+-CALL))
 (2 2 (:REWRITE ASSOC-IN-REPL-EV-EQUALITY-ALIST))
 (1 1 (:REWRITE SUBST-TREE-OPEN))
 (1 1 (:REWRITE MATCH-TREE-OBJ-EQUALS-SUBST-WHEN-SUCCESSFUL))
 )
(UNIFY-LIT-WITH-EQUALITY-RULE-CONSP
 (185 185 (:REWRITE DEFAULT-CAR))
 (171 162 (:REWRITE DEFAULT-CDR))
 (12 4 (:REWRITE SUBSTITUTE-INTO-ONE-WAY-UNIFY-REDUCE))
 (9 3 (:REWRITE MATCH-TREE-BINDERS-BOUND))
 (8 8 (:TYPE-PRESCRIPTION ALL-KEYS-BOUND))
 (6 2 (:REWRITE MATCH-TREE-WHEN-MATCHEDP))
 (5 1 (:REWRITE MATCH-TREE-ALIST-RW-WHEN-MATCHED))
 (3 3 (:TYPE-PRESCRIPTION SYMBOL-ALISTP))
 (3 3 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (3 3 (:REWRITE ASSOC-IN-MATCH-TREE))
 (1 1 (:REWRITE UNIFY-SUCCEEDED-IMPLIES))
 (1 1 (:REWRITE SIMPLE-ONE-WAY-UNIFY-WITH-REPL-EV))
 (1 1 (:REWRITE SIMPLE-ONE-WAY-UNIFY-USAGE))
 )
(UNIFY-LIT-WITH-EQUALITY-RULE-CORRECT
 (569 569 (:REWRITE DEFAULT-CAR))
 (520 4 (:DEFINITION PSEUDO-TERMP))
 (486 468 (:REWRITE DEFAULT-CDR))
 (171 9 (:DEFINITION REPL-EV-ALIST))
 (124 20 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (116 4 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (104 8 (:REWRITE PSEUDO-TERMP-CAR))
 (100 12 (:DEFINITION LENGTH))
 (84 84 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (84 20 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (80 16 (:DEFINITION LEN))
 (58 20 (:REWRITE PSEUDO-TERMP-OPENER))
 (38 29 (:REWRITE REPL-EV-OF-CONS-CALL))
 (38 29 (:REWRITE REPL-EV-OF-BINARY-+-CALL))
 (36 36 (:TYPE-PRESCRIPTION LEN))
 (35 28 (:REWRITE REPL-EV-OF-NOT-CALL))
 (35 28 (:REWRITE REPL-EV-OF-IFF-CALL))
 (33 33 (:REWRITE ASSOC-IN-REPL-EV-EQUALITY-ALIST))
 (32 32 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (32 32 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (32 27 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (32 27 (:REWRITE REPL-EV-OF-QUOTE))
 (32 27 (:REWRITE REPL-EV-OF-LAMBDA))
 (32 16 (:REWRITE DEFAULT-+-2))
 (29 27 (:REWRITE REPL-EV-OF-IF-CALL))
 (27 27 (:REWRITE REPL-EV-OF-VARIABLE))
 (24 8 (:REWRITE SUBSTITUTE-INTO-ONE-WAY-UNIFY-REDUCE))
 (18 6 (:REWRITE MATCH-TREE-BINDERS-BOUND))
 (16 16 (:TYPE-PRESCRIPTION ALL-KEYS-BOUND))
 (16 16 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (16 16 (:REWRITE DEFAULT-+-1))
 (16 4 (:DEFINITION SYMBOL-LISTP))
 (12 6 (:DEFINITION TRUE-LISTP))
 (12 4 (:REWRITE MATCH-TREE-WHEN-MATCHEDP))
 (8 8 (:REWRITE FN-CHECK-DEF-FORMALS))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL-ALISTP))
 (6 6 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6 6 (:REWRITE ASSOC-IN-MATCH-TREE))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:REWRITE UNIFY-SUCCEEDED-IMPLIES))
 (2 2 (:REWRITE SIMPLE-ONE-WAY-UNIFY-USAGE))
 (2 2 (:REWRITE REPL-EV-META-EXTRACT-FN-CHECK-DEF))
 )
(LIT-GET-EQUALITY-RULES
 (319 11 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (286 22 (:REWRITE PSEUDO-TERMP-CAR))
 (231 55 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (227 227 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (220 44 (:DEFINITION LEN))
 (216 216 (:REWRITE DEFAULT-CDR))
 (199 199 (:REWRITE DEFAULT-CAR))
 (146 51 (:REWRITE PSEUDO-TERMP-OPENER))
 (88 88 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (88 44 (:REWRITE DEFAULT-+-2))
 (84 84 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (44 44 (:REWRITE DEFAULT-+-1))
 (44 22 (:DEFINITION TRUE-LISTP))
 (40 40 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (33 33 (:REWRITE FN-CHECK-DEF-FORMALS))
 (11 11 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (11 11 (:REWRITE DEFAULT-COERCE-2))
 (11 11 (:REWRITE DEFAULT-COERCE-1))
 )
(ALISTP-LIT-GET-EQUALITY-RULES
 (232 8 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (208 16 (:REWRITE PSEUDO-TERMP-CAR))
 (168 40 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (160 32 (:DEFINITION LEN))
 (151 150 (:REWRITE DEFAULT-CDR))
 (128 127 (:REWRITE DEFAULT-CAR))
 (106 37 (:REWRITE PSEUDO-TERMP-OPENER))
 (64 64 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (64 32 (:REWRITE DEFAULT-+-2))
 (62 62 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (32 32 (:REWRITE DEFAULT-+-1))
 (32 16 (:DEFINITION TRUE-LISTP))
 (32 8 (:DEFINITION SYMBOL-LISTP))
 (29 29 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (16 16 (:REWRITE FN-CHECK-DEF-FORMALS))
 (8 8 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (8 8 (:REWRITE DEFAULT-COERCE-2))
 (8 8 (:REWRITE DEFAULT-COERCE-1))
 )
(PSEUDO-TERM-VAL-ALISTP-LIT-GET-EQUALITY-RULES
 (784 28 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (721 56 (:REWRITE PSEUDO-TERMP-CAR))
 (616 119 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (420 84 (:DEFINITION LEN))
 (381 379 (:REWRITE DEFAULT-CDR))
 (333 331 (:REWRITE DEFAULT-CAR))
 (316 116 (:REWRITE PSEUDO-TERMP-OPENER))
 (203 203 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (201 201 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (168 84 (:REWRITE DEFAULT-+-2))
 (95 95 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (84 84 (:REWRITE DEFAULT-+-1))
 (84 42 (:DEFINITION TRUE-LISTP))
 (84 21 (:DEFINITION SYMBOL-LISTP))
 (42 42 (:REWRITE FN-CHECK-DEF-FORMALS))
 (25 16 (:REWRITE PSEUDO-TERM-VAL-ALISTP-OF-ATOM))
 (21 21 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (21 21 (:REWRITE DEFAULT-COERCE-2))
 (21 21 (:REWRITE DEFAULT-COERCE-1))
 )
(REPL-EV-EQUALITY-ALIST-P-LIT-GET-EQUALITY-RULES
 (667 23 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (598 46 (:REWRITE PSEUDO-TERMP-CAR))
 (483 115 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (460 92 (:DEFINITION LEN))
 (437 435 (:REWRITE DEFAULT-CDR))
 (381 378 (:REWRITE DEFAULT-CAR))
 (310 109 (:REWRITE PSEUDO-TERMP-OPENER))
 (184 184 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (184 92 (:REWRITE DEFAULT-+-2))
 (179 179 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (97 47 (:REWRITE ASSOC-IN-REPL-EV-EQUALITY-ALIST))
 (92 92 (:REWRITE DEFAULT-+-1))
 (92 46 (:DEFINITION TRUE-LISTP))
 (92 23 (:DEFINITION SYMBOL-LISTP))
 (86 86 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (50 8 (:DEFINITION ASSOC-EQUAL))
 (46 46 (:REWRITE REPL-EV-OF-VARIABLE))
 (46 46 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (46 46 (:REWRITE REPL-EV-OF-QUOTE))
 (46 46 (:REWRITE REPL-EV-OF-NOT-CALL))
 (46 46 (:REWRITE REPL-EV-OF-LAMBDA))
 (46 46 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (46 46 (:REWRITE REPL-EV-OF-IFF-CALL))
 (46 46 (:REWRITE REPL-EV-OF-IF-CALL))
 (46 46 (:REWRITE REPL-EV-OF-EQUAL-CALL))
 (46 46 (:REWRITE REPL-EV-OF-CONS-CALL))
 (46 46 (:REWRITE REPL-EV-OF-BINARY-+-CALL))
 (46 46 (:REWRITE FN-CHECK-DEF-FORMALS))
 (23 23 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (23 23 (:REWRITE DEFAULT-COERCE-2))
 (23 23 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:REWRITE UNIFY-LIT-WITH-EQUALITY-RULE-CONSP))
 )
(REPL-EV-OF-DISJOIN-REVAPPEND
 (83 83 (:REWRITE ASSOC-IN-REPL-EV-EQUALITY-ALIST))
 (76 76 (:REWRITE REPL-EV-OF-VARIABLE))
 (76 76 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (76 76 (:REWRITE REPL-EV-OF-QUOTE))
 (76 76 (:REWRITE REPL-EV-OF-NOT-CALL))
 (76 76 (:REWRITE REPL-EV-OF-LAMBDA))
 (76 76 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (76 76 (:REWRITE REPL-EV-OF-IFF-CALL))
 (76 76 (:REWRITE REPL-EV-OF-IF-CALL))
 (76 76 (:REWRITE REPL-EV-OF-EQUAL-CALL))
 (76 76 (:REWRITE REPL-EV-OF-CONS-CALL))
 (76 76 (:REWRITE REPL-EV-OF-BINARY-+-CALL))
 (38 19 (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
 (26 26 (:REWRITE DEFAULT-CDR))
 (26 26 (:REWRITE DEFAULT-CAR))
 (19 19 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (19 19 (:TYPE-PRESCRIPTION REVAPPEND))
 )
(REPL-EV-DUMB-NEGATE-LIT
 (6267 495 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (5103 495 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (1196 96 (:REWRITE PSEUDO-TERMP-CAR))
 (1105 1105 (:REWRITE DEFAULT-CDR))
 (949 93 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (723 723 (:REWRITE DEFAULT-CAR))
 (675 81 (:DEFINITION LENGTH))
 (650 650 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (646 646 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (639 639 (:TYPE-PRESCRIPTION LEN))
 (620 124 (:DEFINITION LEN))
 (248 124 (:REWRITE DEFAULT-+-2))
 (232 232 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (196 31 (:DEFINITION SYMBOL-LISTP))
 (154 154 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (127 127 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (124 124 (:REWRITE DEFAULT-+-1))
 (83 67 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (83 67 (:REWRITE REPL-EV-OF-IFF-CALL))
 (83 67 (:REWRITE REPL-EV-OF-CONS-CALL))
 (83 67 (:REWRITE REPL-EV-OF-BINARY-+-CALL))
 (67 67 (:REWRITE ASSOC-IN-REPL-EV-EQUALITY-ALIST))
 (62 62 (:REWRITE FN-CHECK-DEF-FORMALS))
 (46 46 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (46 46 (:REWRITE REPL-EV-OF-LAMBDA))
 (46 46 (:REWRITE REPL-EV-OF-IF-CALL))
 (35 35 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (31 31 (:REWRITE DEFAULT-COERCE-2))
 (31 31 (:REWRITE DEFAULT-COERCE-1))
 (20 4 (:DEFINITION ASSOC-EQUAL))
 (17 17 (:REWRITE REPL-EV-META-EXTRACT-FN-CHECK-DEF))
 )
(PSEUDO-TERMP-DUMB-NEGATE-LIT
 (376 30 (:REWRITE PSEUDO-TERMP-CAR))
 (337 26 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (303 303 (:REWRITE DEFAULT-CDR))
 (220 44 (:DEFINITION LEN))
 (207 207 (:REWRITE DEFAULT-CAR))
 (164 164 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (161 161 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (88 44 (:REWRITE DEFAULT-+-2))
 (62 11 (:DEFINITION SYMBOL-LISTP))
 (52 52 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (48 48 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (44 44 (:REWRITE DEFAULT-+-1))
 (22 22 (:REWRITE FN-CHECK-DEF-FORMALS))
 (11 11 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (11 11 (:REWRITE DEFAULT-COERCE-2))
 (11 11 (:REWRITE DEFAULT-COERCE-1))
 )
(REMOVE-NON-SYMBOLS)
(SYMBOL-LISTP-REMOVE-NON-SYMBOLS
 (16 15 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE FN-CHECK-DEF-FORMALS))
 (11 10 (:REWRITE DEFAULT-CDR))
 )
(REMOVE-NON-SYMBOLS-WHEN-SYMBOL-LISTP
 (16 16 (:REWRITE DEFAULT-CAR))
 (9 9 (:REWRITE FN-CHECK-DEF-FORMALS))
 (8 8 (:REWRITE DEFAULT-CDR))
 )
(REMOVE-NON-SYMBOL-PAIRS)
(SYMBOL-ALISTP-REMOVE-NON-SYMBOL-PAIRS
 (48 46 (:REWRITE DEFAULT-CAR))
 (15 14 (:REWRITE DEFAULT-CDR))
 )
(REMOVE-NON-SYMBOL-PAIRS-WHEN-SYMBOL-ALISTP
 (44 44 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE DEFAULT-CDR))
 )
(REPLACE-EQUALITIES-ITER
 (123 123 (:REWRITE DEFAULT-CAR))
 (68 68 (:REWRITE DEFAULT-CDR))
 (58 4 (:REWRITE SYMBOL-LISTP-CDR-ASSOC-EQUAL))
 (48 3 (:DEFINITION SYMBOL-LIST-LISTP))
 (43 7 (:DEFINITION SYMBOL-LISTP))
 (34 17 (:REWRITE DEFAULT-+-2))
 (30 6 (:DEFINITION ASSOC-EQUAL))
 (28 4 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (18 18 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (18 18 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (17 17 (:REWRITE DEFAULT-+-1))
 (15 15 (:TYPE-PRESCRIPTION SYMBOL-LIST-LISTP))
 (14 14 (:REWRITE FN-CHECK-DEF-FORMALS))
 (12 8 (:REWRITE PSEUDO-TERMP-OPENER))
 (11 11 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 )
(PSEUDO-TERM-LISTP-REVAPPEND
 (411 25 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (405 2 (:DEFINITION PSEUDO-TERMP))
 (79 75 (:REWRITE DEFAULT-CAR))
 (72 72 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (72 70 (:REWRITE DEFAULT-CDR))
 (70 31 (:REWRITE PSEUDO-TERMP-OPENER))
 (60 12 (:DEFINITION LEN))
 (57 57 (:TYPE-PRESCRIPTION LEN))
 (51 4 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (50 6 (:DEFINITION LENGTH))
 (30 30 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (30 7 (:DEFINITION TRUE-LISTP))
 (24 12 (:REWRITE DEFAULT-+-2))
 (18 3 (:DEFINITION SYMBOL-LISTP))
 (12 12 (:REWRITE DEFAULT-+-1))
 (11 11 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (6 6 (:REWRITE FN-CHECK-DEF-FORMALS))
 (3 3 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 )
(PSEUDO-TERM-LISTP-REPLACE-EQUALITIES-ITER
 (1620 8 (:DEFINITION PSEUDO-TERMP))
 (1457 79 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (313 313 (:REWRITE DEFAULT-CAR))
 (275 275 (:REWRITE DEFAULT-CDR))
 (240 48 (:DEFINITION LEN))
 (228 228 (:TYPE-PRESCRIPTION LEN))
 (204 16 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (200 24 (:DEFINITION LENGTH))
 (199 199 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (153 82 (:REWRITE PSEUDO-TERMP-OPENER))
 (128 20 (:DEFINITION SYMBOL-LISTP))
 (120 28 (:DEFINITION TRUE-LISTP))
 (120 4 (:REWRITE REMOVE-NON-SYMBOLS-WHEN-SYMBOL-LISTP))
 (96 48 (:REWRITE DEFAULT-+-2))
 (84 84 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (78 78 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (76 4 (:REWRITE SYMBOL-LISTP-CDR-ASSOC-EQUAL))
 (72 72 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (64 4 (:DEFINITION SYMBOL-LIST-LISTP))
 (48 48 (:REWRITE DEFAULT-+-1))
 (40 40 (:REWRITE FN-CHECK-DEF-FORMALS))
 (20 20 (:TYPE-PRESCRIPTION SYMBOL-LIST-LISTP))
 (20 4 (:DEFINITION ASSOC-EQUAL))
 (18 18 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (12 12 (:REWRITE DEFAULT-COERCE-2))
 (12 12 (:REWRITE DEFAULT-COERCE-1))
 (9 3 (:DEFINITION REVAPPEND))
 )
(REPLACE-EQUALITIES-ITER-CORRECT
 (2025 10 (:DEFINITION PSEUDO-TERMP))
 (1725 85 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (417 417 (:REWRITE DEFAULT-CAR))
 (375 375 (:REWRITE DEFAULT-CDR))
 (330 11 (:REWRITE REMOVE-NON-SYMBOLS-WHEN-SYMBOL-LISTP))
 (300 60 (:DEFINITION LEN))
 (285 285 (:TYPE-PRESCRIPTION LEN))
 (255 20 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (250 30 (:DEFINITION LENGTH))
 (244 37 (:DEFINITION SYMBOL-LISTP))
 (209 11 (:REWRITE SYMBOL-LISTP-CDR-ASSOC-EQUAL))
 (185 185 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (176 11 (:DEFINITION SYMBOL-LIST-LISTP))
 (165 165 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (150 75 (:REWRITE PSEUDO-TERMP-OPENER))
 (150 35 (:DEFINITION TRUE-LISTP))
 (120 60 (:REWRITE DEFAULT-+-2))
 (110 110 (:REWRITE ASSOC-IN-REPL-EV-EQUALITY-ALIST))
 (94 94 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (94 94 (:REWRITE REPL-EV-OF-NOT-CALL))
 (94 94 (:REWRITE REPL-EV-OF-LAMBDA))
 (94 94 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (94 94 (:REWRITE REPL-EV-OF-IFF-CALL))
 (94 94 (:REWRITE REPL-EV-OF-IF-CALL))
 (94 94 (:REWRITE REPL-EV-OF-EQUAL-CALL))
 (94 94 (:REWRITE REPL-EV-OF-CONS-CALL))
 (94 94 (:REWRITE REPL-EV-OF-BINARY-+-CALL))
 (92 92 (:REWRITE REPL-EV-OF-VARIABLE))
 (90 90 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (75 60 (:REWRITE REPL-EV-DISJOIN-ATOM))
 (74 74 (:REWRITE FN-CHECK-DEF-FORMALS))
 (70 70 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (60 60 (:REWRITE DEFAULT-+-1))
 (56 56 (:TYPE-PRESCRIPTION REPLACE-EQUALITIES-ITER))
 (55 55 (:TYPE-PRESCRIPTION SYMBOL-LIST-LISTP))
 (55 11 (:DEFINITION ASSOC-EQUAL))
 (36 1 (:DEFINITION REPL-EV-EQUALITY-ALIST-P))
 (23 23 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (18 6 (:DEFINITION REVAPPEND))
 (15 15 (:REWRITE DEFAULT-COERCE-2))
 (15 15 (:REWRITE DEFAULT-COERCE-1))
 (4 4 (:TYPE-PRESCRIPTION SUBST-SUBTERMS-LIST))
 (3 3 (:TYPE-PRESCRIPTION LIT-GET-EQUALITY-RULES))
 (2 2 (:REWRITE REPL-EV-META-EXTRACT-FN-CHECK-DEF))
 )
(REPLACE-EQUALITIES-CP
 (61 61 (:REWRITE DEFAULT-CAR))
 (45 45 (:REWRITE DEFAULT-CDR))
 (44 4 (:DEFINITION FGETPROP))
 (26 4 (:DEFINITION SYMBOL-ALISTP))
 (20 4 (:DEFINITION ASSOC-EQUAL))
 (14 2 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (12 4 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (9 9 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (9 9 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (8 8 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (8 4 (:DEFINITION NTH))
 (6 4 (:REWRITE PSEUDO-TERMP-OPENER))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(REPLACE-EQUALITIES-CP-CORRECT
 (27 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (13 13 (:REWRITE DEFAULT-CAR))
 (11 1 (:REWRITE REMOVE-NON-SYMBOL-PAIRS-WHEN-SYMBOL-ALISTP))
 (11 1 (:DEFINITION FGETPROP))
 (9 9 (:REWRITE DEFAULT-CDR))
 (8 1 (:DEFINITION SYMBOL-ALISTP))
 (7 1 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (6 1 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (6 1 (:REWRITE PSEUDO-TERMP-CAR))
 (5 5 (:TYPE-PRESCRIPTION SYMBOL-ALISTP))
 (4 4 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (4 4 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (4 4 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (3 2 (:REWRITE PSEUDO-TERMP-OPENER))
 (3 1 (:DEFINITION ALISTP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2 2 (:REWRITE REPL-EV-OF-TYPESPEC-CHECK-CALL))
 (2 2 (:REWRITE REPL-EV-OF-NOT-CALL))
 (2 2 (:REWRITE REPL-EV-OF-LAMBDA))
 (2 2 (:REWRITE REPL-EV-OF-IMPLIES-CALL))
 (2 2 (:REWRITE REPL-EV-OF-IFF-CALL))
 (2 2 (:REWRITE REPL-EV-OF-IF-CALL))
 (2 2 (:REWRITE REPL-EV-OF-EQUAL-CALL))
 (2 2 (:REWRITE REPL-EV-OF-CONS-CALL))
 (2 2 (:REWRITE REPL-EV-OF-BINARY-+-CALL))
 (2 2 (:REWRITE ASSOC-IN-REPL-EV-EQUALITY-ALIST))
 (1 1 (:REWRITE REPL-EV-OF-VARIABLE))
 (1 1 (:REWRITE REPL-EV-META-EXTRACT-FN-CHECK-DEF))
 )
(MATCH-TREE-REPLACE-EQUALITIES
 (3 1 (:REWRITE MATCH-TREE-WHEN-MATCHEDP))
 (2 2 (:REWRITE SUBST-TREE-OPEN))
 (2 2 (:REWRITE MATCH-TREE-ALIST-EXPAND-CONS))
 (2 2 (:REWRITE MATCH-TREE-ALIST-EXPAND-BINDER))
 (2 2 (:REWRITE MATCH-TREE-ALIST-EXPAND-ATOM))
 )
(MATCH-TREE-BLOCK-SELF-SUBST)
(FOO
 (1314 62 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (899 797 (:REWRITE DEFAULT-CDR))
 (897 786 (:REWRITE DEFAULT-CAR))
 (819 39 (:REWRITE PSEUDO-TERMP-CDR-ASSOC-EQUAL))
 (700 140 (:DEFINITION LEN))
 (513 171 (:REWRITE MATCH-TREE-BINDERS-BOUND))
 (487 449 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (447 447 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (301 76 (:DEFINITION TRUE-LISTP))
 (280 140 (:REWRITE DEFAULT-+-2))
 (240 240 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (195 39 (:DEFINITION ASSOC-EQUAL))
 (171 171 (:TYPE-PRESCRIPTION SYMBOL-ALISTP))
 (171 171 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (167 35 (:DEFINITION SYMBOL-LISTP))
 (153 39 (:REWRITE PSEUDO-TERMP-OF-LOOKUP-IN-SUBST))
 (153 39 (:REWRITE PSEUDO-TERMP-OF-LOOKUP-IN-PSEUDO-TERM-VAL-ALISTP))
 (152 38 (:DEFINITION STRIP-CDRS))
 (140 140 (:REWRITE DEFAULT-+-1))
 (82 82 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (76 76 (:TYPE-PRESCRIPTION PSEUDO-TERM-VAL-ALISTP))
 (76 76 (:TYPE-PRESCRIPTION PSEUDO-TERM-SUBSTP))
 (70 70 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (70 70 (:REWRITE FN-CHECK-DEF-FORMALS))
 (68 68 (:TYPE-PRESCRIPTION MATCH-TREE-MATCHEDP))
 (66 22 (:REWRITE MATCH-TREE-ALIST-RW-WHEN-MATCH-TREE-MATCHEDP))
 (40 40 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (39 39 (:REWRITE ASSOC-IN-MATCH-TREE))
 (38 38 (:REWRITE PSEUDO-TERM-VAL-ALISTP-OF-ATOM))
 (38 38 (:REWRITE PSEUDO-TERM-SUBSTP-OF-ATOM))
 (36 12 (:REWRITE MATCH-TREE-WHEN-MATCHEDP))
 (35 35 (:REWRITE DEFAULT-COERCE-2))
 (35 35 (:REWRITE DEFAULT-COERCE-1))
 )
