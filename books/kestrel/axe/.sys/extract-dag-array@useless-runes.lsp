(EXTRACT-DAG-ARRAY-AUX
 (963 963 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (353 353 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (67 35 (:REWRITE DEFAULT-<-2))
 (49 35 (:REWRITE DEFAULT-<-1))
 (38 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-<))
 (35 35 (:REWRITE USE-ALL-<-2))
 (35 35 (:REWRITE USE-ALL-<))
 (35 35 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (33 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (33 1 (:REWRITE BOUNDED-DARG-LISTP-OF-DARGS-WHEN-<-SIMPLE))
 (32 32 (:REWRITE USE-ALL-<=-2))
 (32 32 (:REWRITE USE-ALL-<=))
 (32 4 (:REWRITE NOT-EQUAL-OF-CAR-AND-QUOTE-WHEN-LEN-WRONG-AND-PSEUDO-DAG-ARRAYP-AUX))
 (30 30 (:LINEAR ARRAY2P-LINEAR))
 (28 24 (:REWRITE DEFAULT-+-2))
 (27 24 (:REWRITE DEFAULT-+-1))
 (25 3 (:REWRITE BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (24 12 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE))
 (23 1 (:REWRITE ALL-DARGP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE))
 (22 1 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (20 5 (:REWRITE NOT-<-OF-ALEN1-WHEN-PSEUDO-DAG-ARRAYP))
 (16 16 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (16 8 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1))
 (16 4 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-WHEN-PSEUDO-DAGP-AUX))
 (13 7 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (13 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (11 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DAG-EXPRP))
 (11 1 (:REWRITE BOUNDED-DARG-LISTP-OF-DARGS-WHEN-BOUNDED-DAG-EXPRP))
 (9 9 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (8 8 (:TYPE-PRESCRIPTION PSEUDO-DAGP-AUX))
 (8 8 (:REWRITE USE-ALL-RATIONALP-2))
 (8 8 (:REWRITE USE-ALL-RATIONALP))
 (7 7 (:REWRITE USE-ALL-CONSP-2))
 (7 7 (:REWRITE USE-ALL-CONSP))
 (7 7 (:REWRITE DEFAULT-CAR))
 (7 2 (:REWRITE CONSP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE-IFF))
 (6 6 (:TYPE-PRESCRIPTION BOUNDED-DAG-EXPRP))
 (6 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 3 (:REWRITE BOUNDED-DAG-EXPRP-WHEN-MYQUOTEP-CHEAP))
 (6 1 (:REWRITE ALL-<-OF-ALEN1-WHEN-PSEUDO-DAG-ARRAYP-LIST))
 (5 5 (:REWRITE TRANSLATION-ARRAYP-AUX-WHEN-BOUNDED-TRANSLATION-ARRAYP-AUX))
 (5 3 (:REWRITE TRANSLATION-ARRAYP-AUX-WHEN-NEGATIVE))
 (4 4 (:REWRITE USE-ALL-NATP-2))
 (4 4 (:REWRITE USE-ALL-NATP))
 (4 4 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (4 4 (:REWRITE PSEUDO-DAGP-AUX-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-MONOTONE))
 (4 4 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (4 2 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DARG-LISTP-OF-CDR-CHEAP))
 (4 1 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION MYQUOTEP))
 (3 3 (:REWRITE BOUNDED-DAG-EXPRP-WHEN-SYMBOLP-CHEAP))
 (3 3 (:REWRITE BOUNDED-DAG-EXPRP-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE BOUNDED-DAG-EXPRP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (3 3 (:REWRITE BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-GEN))
 (3 3 (:REWRITE BOUNDED-DAG-EXPRP-MONOTONE))
 (3 3 (:REWRITE <-OF-+-OF-1-STRENGTHEN))
 (3 1 (:REWRITE RATIONALP-OF-ALEN1-WHEN-ARRAY1P))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP-LIST))
 (2 2 (:TYPE-PRESCRIPTION ALL-<))
 (2 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (1 1 (:REWRITE USE-ALL-DARGP-2))
 (1 1 (:REWRITE USE-ALL-DARGP))
 (1 1 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP-SPECIAL-ALT))
 (1 1 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP-SPECIAL))
 (1 1 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (1 1 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (1 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DAG-EXPRP-GEN))
 (1 1 (:REWRITE BOUNDED-DARG-LISTP-OF-DARGS-OF-AREF1))
 (1 1 (:REWRITE BOUNDED-DARG-LISTP-MONOTONE))
 (1 1 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (1 1 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (1 1 (:REWRITE ALL-<-TRANSITIVE))
 )
(EXTRACT-DAG-ARRAY
 (1188 1188 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (609 553 (:TYPE-PRESCRIPTION RATIONALP-OF-MAXELEM))
 (536 18 (:REWRITE USE-ALL-<-FOR-CAR))
 (445 30 (:REWRITE DEFAULT-+-2))
 (231 13 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (211 18 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (209 81 (:REWRITE DEFAULT-<-2))
 (130 81 (:REWRITE DEFAULT-<-1))
 (130 12 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (120 3 (:LINEAR MAXELEM-OF-CDR-LINEAR))
 (113 81 (:REWRITE USE-ALL-<))
 (102 12 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (99 27 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (86 86 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (83 27 (:REWRITE ALL-<-TRANSITIVE))
 (81 81 (:REWRITE USE-ALL-<-2))
 (79 79 (:REWRITE USE-ALL-CONSP-2))
 (79 79 (:REWRITE USE-ALL-CONSP))
 (78 78 (:REWRITE USE-ALL-<=-2))
 (78 78 (:REWRITE USE-ALL-<=))
 (75 9 (:REWRITE RATIONALP-OF-MAXELEM))
 (75 6 (:DEFINITION LEN))
 (64 9 (:REWRITE ACL2-NUMBERP-OF-MAXELEM))
 (62 62 (:REWRITE DEFAULT-CDR))
 (54 54 (:REWRITE DEFAULT-CAR))
 (54 27 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (47 5 (:REWRITE ALL-NATP-OF-CDR))
 (45 4 (:DEFINITION RATIONAL-LISTP))
 (39 4 (:REWRITE INTEGER-LISTP-WHEN-ALL-NATP))
 (36 18 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (32 32 (:TYPE-PRESCRIPTION MEMBERP))
 (31 25 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (30 30 (:REWRITE DEFAULT-+-1))
 (28 14 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (28 14 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (26 26 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (26 26 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (25 25 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (24 24 (:TYPE-PRESCRIPTION LEN))
 (22 22 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (20 2 (:REWRITE <=-OF-MAXELEM-WHEN-MEMBER-EQUAL))
 (18 18 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (18 18 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (16 8 (:REWRITE RATIONAL-LISTP-WHEN-ALL-NATP-CHEAP))
 (14 14 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (14 14 (:REWRITE USE-ALL-RATIONALP-2))
 (14 14 (:REWRITE USE-ALL-RATIONALP))
 (14 14 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (14 2 (:DEFINITION MEMBER-EQUAL))
 (13 13 (:REWRITE USE-ALL-NATP-2))
 (13 13 (:REWRITE USE-ALL-NATP))
 (13 13 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (13 13 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (13 13 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (12 12 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (12 12 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (12 12 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (12 12 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 1 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (7 7 (:REWRITE ARRAY1P-WHEN-PSEUDO-DAG-ARRAYP))
 (5 1 (:REWRITE ALL-RATIONALP-OF-CDR))
 (4 4 (:TYPE-PRESCRIPTION ALL-RATIONALP))
 (4 2 (:REWRITE <-OF-MAXELEM-WHEN-ALL-<-CHEAP))
 (4 1 (:REWRITE TRANSLATION-ARRAYP-AUX-WHEN-NEGATIVE))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE TRANSLATION-ARRAYP-AUX-WHEN-BOUNDED-TRANSLATION-ARRAYP-AUX))
 (1 1 (:REWRITE TRANSLATION-ARRAYP-AUX-MONOTONE))
 )
