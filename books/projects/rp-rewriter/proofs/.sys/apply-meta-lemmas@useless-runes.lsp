(RP::RP-RW-META-RULE-MAIN-VALID-EVAL
 (900 8 (:DEFINITION RP::EVAL-AND-ALL))
 (680 17 (:DEFINITION RP::RP-TRANS))
 (374 323 (:REWRITE DEFAULT-CDR))
 (359 257 (:REWRITE DEFAULT-CAR))
 (306 17 (:DEFINITION RP::TRANS-LIST))
 (255 3 (:DEFINITION RP::RP-TERMP))
 (244 26 (:DEFINITION RP::INCLUDE-FNC))
 (207 17 (:REWRITE RP::RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT))
 (158 49 (:DEFINITION QUOTEP))
 (153 153 (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
 (153 17 (:DEFINITION RP::IS-FALIST))
 (120 120 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (114 11 (:REWRITE RP::NOT-INCLUDE-RP))
 (72 72 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
 (68 68 (:REWRITE RP::CONSP-RP-TRANS-LST))
 (64 4 (:DEFINITION RP::EX-FROM-RP))
 (62 62 (:TYPE-PRESCRIPTION RP::RP-STAT-ADD-TO-RULES-USED))
 (53 19 (:REWRITE RP::RP-EVL-OF-VARIABLE))
 (48 12 (:REWRITE RP::IS-IF-RP-TERMP))
 (46 46 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
 (42 3 (:DEFINITION RP::RP-TERM-LISTP))
 (40 40 (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
 (39 6 (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
 (32 23 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (27 27 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (24 6 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (24 6 (:REWRITE RP::RP-TERMP-CADR))
 (24 6 (:REWRITE RP::RP-TERMP-CADDR))
 (23 23 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (21 6 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (20 20 (:TYPE-PRESCRIPTION RP::CONTEXT-FROM-RP))
 (20 12 (:REWRITE RP::VALID-SC-CADR))
 (19 19 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-RP-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-QUOTE))
 (19 19 (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-LAMBDA))
 (19 19 (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-IF-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-DONT-RW-CONTEXT-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-CASESPLIT-FROM-CONTEXT-TRIG-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
 (19 19 (:REWRITE RP::RP-EVL-OF-<-CALL))
 (16 8 (:REWRITE RP::VALID-SC-CADDR))
 (12 4 (:REWRITE RP::VALID-SC-CADDDR))
 (12 3 (:REWRITE RP::VALID-SC-OF-EX-FROM-RP))
 (12 3 (:DEFINITION RP::VALID-SC-SUBTERMS))
 (6 6 (:TYPE-PRESCRIPTION QUOTEP))
 (3 3 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 (3 3 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-ALISTP))
 )
(RP::RP-RW-META-RULE-MAIN-VALID-RP-TERMP
 (78 20 (:REWRITE RP::IS-IF-RP-TERMP))
 (66 66 (:REWRITE DEFAULT-CAR))
 (62 62 (:REWRITE DEFAULT-CDR))
 (42 3 (:DEFINITION RP::RP-TERM-LISTP))
 (37 9 (:REWRITE RP::RP-TERMP-CADDR))
 (36 9 (:REWRITE RP::RP-TERMP-CADR))
 (31 6 (:REWRITE RP::NOT-INCLUDE-RP))
 (28 7 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (25 25 (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
 (21 21 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (20 5 (:DEFINITION RP::INCLUDE-FNC))
 (15 3 (:REWRITE RP::VALID-RP-STATEP-AND-RP-STATEP-IMPLIES-VALID-RP-STATE-SYNTAXP))
 (9 9 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (8 8 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (5 5 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
 (4 4 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
 (3 3 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-VALID-RP-STATE-SYNTAXP))
 (3 3 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 (3 3 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-ALISTP))
 )
(RP::RP-RW-META-RULE-MAIN-VALID-DONT-RW-SYNTAXP)
(RP::RP-RW-META-RULE-MAIN-RETURNS-VALID-RP-STATE
 (22 22 (:TYPE-PRESCRIPTION RP::RP-STAT-ADD-TO-RULES-USED))
 (18 18 (:REWRITE DEFAULT-CDR))
 (12 12 (:TYPE-PRESCRIPTION RP::RP-STATE-PRESERVEDP))
 (12 8 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 (11 11 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-ALISTP))
 (10 2 (:REWRITE RP::VALID-RP-STATEP-AND-RP-STATEP-IMPLIES-VALID-RP-STATE-SYNTAXP))
 (9 9 (:REWRITE DEFAULT-CAR))
 (8 4 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-VALID-RP-STATEP))
 (8 4 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-VALID-RP-STATE-SYNTAXP))
 (3 3 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (2 2 (:REWRITE RP::VALID-RP-STATEP-NECC))
 )
