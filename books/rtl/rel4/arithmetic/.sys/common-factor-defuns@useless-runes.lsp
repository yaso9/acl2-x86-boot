(MY-INTERSECTION-EQUAL)
(ADJOIN-EQUAL)
(REMOVE-ONE)
(REMOVE-ONE-PRESERVES-TRUE-LISTP
 (10 10 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE DEFAULT-CAR))
 )
(GET-FACTORS-OF-PRODUCT
 (399 191 (:REWRITE DEFAULT-+-2))
 (395 79 (:DEFINITION LEN))
 (235 191 (:REWRITE DEFAULT-+-1))
 (167 167 (:TYPE-PRESCRIPTION LEN))
 (104 26 (:REWRITE COMMUTATIVITY-OF-+))
 (104 26 (:DEFINITION INTEGER-ABS))
 (104 13 (:DEFINITION LENGTH))
 (87 87 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (85 29 (:DEFINITION TRUE-LISTP))
 (77 77 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (66 22 (:DEFINITION SYMBOL-LISTP))
 (41 32 (:REWRITE DEFAULT-<-2))
 (36 32 (:REWRITE DEFAULT-<-1))
 (26 26 (:REWRITE DEFAULT-UNARY-MINUS))
 (22 22 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (13 13 (:REWRITE DEFAULT-REALPART))
 (13 13 (:REWRITE DEFAULT-NUMERATOR))
 (13 13 (:REWRITE DEFAULT-IMAGPART))
 (13 13 (:REWRITE DEFAULT-DENOMINATOR))
 (13 13 (:REWRITE DEFAULT-COERCE-2))
 (13 13 (:REWRITE DEFAULT-COERCE-1))
 (4 4 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(GET-FACTORS-OF-PRODUCT-TRUE-LISTP
 (19 3 (:DEFINITION MEMBER-EQUAL))
 (18 13 (:REWRITE DEFAULT-CDR))
 (16 14 (:REWRITE DEFAULT-CAR))
 (15 3 (:DEFINITION TRUE-LISTP))
 )
(FIND-INVERTED-FACTORS-IN-LIST)
(REMOVE-CANCELLING-FACTOR-PAIRS-HELPER
 (24 8 (:DEFINITION MEMBER-EQUAL))
 (12 12 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 )
(REMOVE-CANCELLING-FACTOR-PAIRS-HELPER-PRESERVES-TRUE-LISTP
 (55 55 (:REWRITE DEFAULT-CDR))
 (46 46 (:REWRITE DEFAULT-CAR))
 )
(REMOVE-CANCELLING-FACTOR-PAIRS)
(REMOVE-CANCELLING-FACTOR-PAIRS-PRESERVES-TRUE-LISTP)
(FIND-COMMON-FACTORS-IN-SUM-OF-PRODUCTS-AUX
 (410 82 (:DEFINITION LEN))
 (405 194 (:REWRITE DEFAULT-+-2))
 (238 194 (:REWRITE DEFAULT-+-1))
 (104 26 (:REWRITE COMMUTATIVITY-OF-+))
 (104 26 (:DEFINITION INTEGER-ABS))
 (104 13 (:DEFINITION LENGTH))
 (85 85 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (77 77 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (69 23 (:DEFINITION SYMBOL-LISTP))
 (41 32 (:REWRITE DEFAULT-<-2))
 (36 32 (:REWRITE DEFAULT-<-1))
 (26 26 (:REWRITE DEFAULT-UNARY-MINUS))
 (13 13 (:REWRITE DEFAULT-REALPART))
 (13 13 (:REWRITE DEFAULT-NUMERATOR))
 (13 13 (:REWRITE DEFAULT-IMAGPART))
 (13 13 (:REWRITE DEFAULT-DENOMINATOR))
 (13 13 (:REWRITE DEFAULT-COERCE-2))
 (13 13 (:REWRITE DEFAULT-COERCE-1))
 (4 4 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(FIND-COMMON-FACTORS-IN-SUM-OF-PRODUCTS-AUX-TRUE-LISTP
 (11 11 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE DEFAULT-CDR))
 )
(FIND-COMMON-FACTORS-IN-SUM-OF-PRODUCTS)
(FIND-COMMON-FACTORS-IN-SUM-OF-PRODUCTS-TRUE-LISTP)
(MAKE-PRODUCT-FROM-LIST-OF-FACTORS)
(FIND-COMMON-FACTORS-TO-CANCEL)
(BIND-K-TO-COMMON-FACTORS)
