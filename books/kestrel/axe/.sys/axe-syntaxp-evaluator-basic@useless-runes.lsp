(EVAL-AXE-SYNTAXP-FUNCTION-APPLICATION-BASIC
 (129430 64715 (:TYPE-PRESCRIPTION ALEN1-TYPE))
 (103914 51957 (:TYPE-PRESCRIPTION NATP-OF-LARGEST-NON-QUOTEP))
 (93351 20697 (:REWRITE DEFAULT-CDR))
 (89540 12336 (:REWRITE DEFAULT-CAR))
 (64715 64715 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (64715 64715 (:TYPE-PRESCRIPTION ARRAY1P))
 (53000 500 (:LINEAR LARGEST-NON-QUOTEP-BOUND))
 (51407 51407 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (50830 26309 (:REWRITE DEFAULT-+-2))
 (48900 44316 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (44316 44316 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (44316 44316 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (44316 44316 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (41645 1405 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (37225 905 (:DEFINITION NAT-LISTP))
 (35830 4428 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (26309 26309 (:REWRITE DEFAULT-+-1))
 (21310 905 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (19440 405 (:REWRITE ACL2-NUMBERP-OF-LOOKUP-EQUAL))
 (18000 500 (:LINEAR LARGEST-NON-QUOTEP-BOUND-ALT))
 (16602 919 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (15600 10349 (:REWRITE DEFAULT-<-2))
 (14574 808 (:REWRITE SUBSETP-EQUAL-OF-FREE-VARS-IN-TERMS-OF-CAR-CHAIN))
 (14405 905 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (14000 500 (:DEFINITION NTH))
 (10960 401 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (10712 10712 (:REWRITE USE-ALL-CONSP-2))
 (10712 10712 (:REWRITE USE-ALL-CONSP))
 (10712 10712 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (10709 10349 (:REWRITE DEFAULT-<-1))
 (10556 248 (:REWRITE PERM-OF-UNION-EQUAL-WHEN-DISJOINT))
 (10349 10349 (:REWRITE USE-ALL-<-2))
 (10349 10349 (:REWRITE USE-ALL-<))
 (10349 10349 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (10010 149 (:DEFINITION INTERSECTION-EQUAL))
 (8933 8933 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (8933 8933 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (8221 2095 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (6638 1177 (:REWRITE ALL-CONSP-OF-CDR))
 (6308 6308 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (5835 5835 (:TYPE-PRESCRIPTION NAT-LISTP))
 (5551 5551 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (5442 5442 (:TYPE-PRESCRIPTION ALL-CONSP))
 (4032 136 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-<))
 (3751 3751 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (3751 3751 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (3731 3731 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (3731 3731 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (3672 72 (:REWRITE <-OF-LARGEST-NON-QUOTEP))
 (3596 1798 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (2944 136 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (2755 919 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (2522 1261 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (2504 1252 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-MYQUOTEP-CHEAP))
 (2504 1252 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-CONSP-CHEAP))
 (2310 2310 (:TYPE-PRESCRIPTION ALL-NATP))
 (2144 1039 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (2095 2095 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (2018 1039 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (1993 1993 (:REWRITE USE-ALL-NATP-2))
 (1993 1993 (:REWRITE USE-ALL-NATP))
 (1993 1993 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (1838 919 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (1836 1836 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (1810 905 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (1769 1742 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-ALT))
 (1696 32 (:REWRITE <=-OF-LARGEST-NON-QUOTEP-WHEN-BOUNDED-DARG-LISTP))
 (1623 1623 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (1615 1615 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (1503 549 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1481 1481 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (1428 42 (:REWRITE SUBSETP-EQUAL-OF-NIL-ARG2))
 (1405 905 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (1124 562 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (968 136 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (919 919 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (919 919 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (919 919 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (894 894 (:TYPE-PRESCRIPTION INTERSECTION-EQUAL))
 (802 401 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (790 401 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (608 7 (:REWRITE SUBSETP-EQUAL-OF-FREE-VARS-IN-TERMS-OF-CDR-CHAIN))
 (588 14 (:REWRITE SUBSETP-EQUAL-OF-CONS-ARG2))
 (512 32 (:REWRITE <=-OF-LARGEST-NON-QUOTEP))
 (509 509 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (500 500 (:LINEAR <-OF-LARGEST-NON-QUOTEP))
 (477 477 (:REWRITE USE-ALL-RATIONALP-2))
 (477 477 (:REWRITE USE-ALL-RATIONALP))
 (401 401 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (272 272 (:TYPE-PRESCRIPTION BOUNDED-DARG-LISTP))
 (272 272 (:TYPE-PRESCRIPTION ALL-<))
 (272 136 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (272 136 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (226 226 (:REWRITE ALISTP-WHEN-PSEUDO-DAGP-AUX))
 (226 226 (:REWRITE ALISTP-WHEN-BOUNDED-NATP-ALISTP))
 (152 8 (:REWRITE USE-ALL-DARGP-FOR-CAR))
 (136 136 (:REWRITE BOUNDED-DARG-LISTP-MONOTONE))
 (136 136 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (136 136 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (136 136 (:REWRITE ALL-<-TRANSITIVE))
 (104 104 (:REWRITE USE-ALL-<=-2))
 (104 104 (:REWRITE USE-ALL-<=))
 (65 65 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (48 16 (:REWRITE USE-ALL-DARGP))
 (36 4 (:REWRITE ALL-DARGP-OF-CDR))
 (32 32 (:TYPE-PRESCRIPTION MEMBERP))
 (16 16 (:REWRITE USE-ALL-DARGP-2))
 (16 16 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (16 8 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (16 8 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (5 5 (:REWRITE EQUAL-OF-LEN-AND-0))
 (3 3 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (3 3 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 )
(EVAL-AXE-SYNTAXP-EXPR-BASIC
 (13417 100 (:DEFINITION INTEGER-ABS))
 (12381 12 (:REWRITE USE-ALL-<-FOR-CAR))
 (10278 117 (:DEFINITION NAT-LISTP))
 (7050 111 (:REWRITE ALL-NATP-OF-CDR))
 (6171 33 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (5727 33 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (5511 192 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (4932 21 (:REWRITE ALL-<-OF-CDR))
 (4566 126 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (4299 120 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (3696 192 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (3338 307 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (2369 2369 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (2369 2369 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (2369 2369 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (2348 1163 (:REWRITE DEFAULT-+-2))
 (1990 118 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (1892 946 (:TYPE-PRESCRIPTION ALEN1-TYPE))
 (1738 181 (:REWRITE ALL-CONSP-OF-CDR))
 (1677 12 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (1573 18 (:DEFINITION SYMBOL-LISTP))
 (1552 776 (:TYPE-PRESCRIPTION NATP-OF-LARGEST-NON-QUOTEP))
 (1545 33 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 (1415 742 (:REWRITE DEFAULT-<-2))
 (1320 1163 (:REWRITE DEFAULT-+-1))
 (1272 12 (:LINEAR LARGEST-NON-QUOTEP-BOUND))
 (1086 1086 (:REWRITE USE-ALL-CONSP-2))
 (1086 1086 (:REWRITE USE-ALL-CONSP))
 (1086 1086 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (946 946 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (946 946 (:TYPE-PRESCRIPTION ARRAY1P))
 (908 104 (:DEFINITION LENGTH))
 (804 21 (:REWRITE ALL-RATIONALP-OF-CDR))
 (794 794 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (768 768 (:TYPE-PRESCRIPTION NAT-LISTP))
 (758 742 (:REWRITE DEFAULT-<-1))
 (742 742 (:REWRITE USE-ALL-<-2))
 (742 742 (:REWRITE USE-ALL-<))
 (742 742 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (661 661 (:TYPE-PRESCRIPTION ALL-CONSP))
 (588 21 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (459 459 (:TYPE-PRESCRIPTION ALL-NATP))
 (447 447 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (434 434 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (434 434 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (432 12 (:LINEAR LARGEST-NON-QUOTEP-BOUND-ALT))
 (400 100 (:REWRITE COMMUTATIVITY-OF-+))
 (384 192 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (378 126 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (373 373 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (336 12 (:DEFINITION NTH))
 (316 158 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (307 307 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (298 149 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (296 148 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (296 148 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (252 252 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (252 126 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (252 33 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (204 192 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (198 154 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-ALT))
 (175 175 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (156 156 (:TYPE-PRESCRIPTION NATP))
 (147 147 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (132 132 (:REWRITE USE-ALL-NATP-2))
 (132 132 (:REWRITE USE-ALL-NATP))
 (132 132 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (126 126 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (126 126 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (126 126 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (123 123 (:REWRITE USE-ALL-<=-2))
 (123 123 (:REWRITE USE-ALL-<=))
 (122 122 (:REWRITE FOLD-CONSTS-IN-+))
 (100 100 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (100 100 (:REWRITE DEFAULT-UNARY-MINUS))
 (94 47 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-MYQUOTEP-CHEAP))
 (94 47 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-CONSP-CHEAP))
 (88 88 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (88 88 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (78 78 (:TYPE-PRESCRIPTION ALL-<))
 (75 75 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (72 72 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (68 68 (:REWRITE DEFAULT-COERCE-2))
 (68 68 (:REWRITE DEFAULT-COERCE-1))
 (66 66 (:TYPE-PRESCRIPTION ALL-RATIONALP))
 (65 65 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (56 56 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (50 50 (:REWRITE USE-ALL-RATIONALP-2))
 (50 50 (:REWRITE USE-ALL-RATIONALP))
 (50 50 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (50 50 (:REWRITE DEFAULT-REALPART))
 (50 50 (:REWRITE DEFAULT-NUMERATOR))
 (50 50 (:REWRITE DEFAULT-IMAGPART))
 (50 50 (:REWRITE DEFAULT-DENOMINATOR))
 (42 21 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (42 21 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (42 21 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (36 36 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (35 35 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (34 34 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (34 34 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (33 33 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (33 33 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (33 33 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (33 33 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (33 33 (:REWRITE ALL-<-TRANSITIVE))
 (31 1 (:DEFINITION MEMBER-EQUAL))
 (24 12 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (24 12 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (24 12 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (21 21 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (12 12 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (12 12 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (12 12 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (12 12 (:LINEAR <-OF-LARGEST-NON-QUOTEP))
 (2 2 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-2))
 (2 2 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-1))
 )
