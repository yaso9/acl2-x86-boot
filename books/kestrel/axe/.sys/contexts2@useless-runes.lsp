(GET-NOT-DONE-NODES
 (172 10 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (160 4 (:DEFINITION NAT-LISTP))
 (100 67 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-AREF1-WHEN-DAG-PARENT-ARRAYP))
 (82 2 (:DEFINITION NATP))
 (67 67 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (43 3 (:REWRITE USE-ALL-<-FOR-CAR))
 (41 41 (:TYPE-PRESCRIPTION NAT-LISTP))
 (32 4 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (30 3 (:REWRITE ALL-<-OF-ALEN1-WHEN-PSEUDO-DAG-ARRAYP-LIST))
 (20 10 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (19 3 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (14 14 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP-LIST))
 (12 2 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-OF-CDR))
 (11 3 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (10 10 (:REWRITE DEFAULT-CDR))
 (8 6 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (8 4 (:REWRITE USE-ALL-NATP))
 (8 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (7 7 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP-SPECIAL-ALT))
 (7 7 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP-SPECIAL))
 (7 7 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP))
 (6 6 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (6 5 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (6 5 (:REWRITE ALL-<-TRANSITIVE))
 (6 3 (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP-CHEAP))
 (6 1 (:REWRITE <-OF-CAR-AND-ALEN1-WHEN-PSEUDO-DAG-ARRAYP-LIST))
 (6 1 (:REWRITE <-OF-CAR-AND-ALEN1))
 (5 5 (:REWRITE USE-ALL-CONSP-2))
 (5 5 (:REWRITE USE-ALL-CONSP))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE ARRAY1P-WHEN-PSEUDO-DAG-ARRAYP))
 (5 5 (:REWRITE ARRAY1P-WHEN-CONTEXT-ARRAYP))
 (5 5 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (5 1 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (4 4 (:TYPE-PRESCRIPTION MEMBERP))
 (4 4 (:REWRITE USE-ALL-NATP-2))
 (4 4 (:REWRITE USE-ALL-<=-2))
 (4 4 (:REWRITE USE-ALL-<=))
 (4 4 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (4 4 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (4 4 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (4 4 (:LINEAR ARRAY2P-LINEAR))
 (4 2 (:REWRITE TRUE-LISTP-WHEN-POSSIBLY-NEGATED-NODENUMSP))
 (4 2 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (4 2 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (3 3 (:REWRITE USE-ALL-<-2))
 (3 3 (:REWRITE USE-ALL-<))
 (3 3 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (3 3 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (3 3 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (3 3 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (3 3 (:REWRITE INTEGERP-OF-CAR-WHEN-POSSIBLY-NEGATED-NODENUMSP-WEAKEN-CHEAP))
 (3 3 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION POSSIBLY-NEGATED-NODENUMSP))
 (2 2 (:TYPE-PRESCRIPTION ALL-RATIONALP))
 (2 2 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (2 1 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (1 1 (:REWRITE USE-ALL-RATIONALP-2))
 (1 1 (:REWRITE USE-ALL-RATIONALP))
 (1 1 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 )
(ALL-NATP-OF-GET-NOT-DONE-NODES
 (934 44 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (896 17 (:DEFINITION NAT-LISTP))
 (460 10 (:DEFINITION NATP))
 (284 12 (:REWRITE USE-ALL-<-FOR-CAR))
 (196 98 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-AREF1-WHEN-DAG-PARENT-ARRAYP))
 (172 172 (:TYPE-PRESCRIPTION NAT-LISTP))
 (144 14 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (108 39 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (98 98 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (88 44 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (57 17 (:REWRITE USE-ALL-NATP))
 (47 47 (:TYPE-PRESCRIPTION GET-NOT-DONE-NODES))
 (40 40 (:TYPE-PRESCRIPTION MEMBERP))
 (40 40 (:TYPE-PRESCRIPTION ALL-<))
 (40 10 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (38 2 (:REWRITE ALL-<-OF-CDR))
 (31 30 (:REWRITE DEFAULT-CAR))
 (30 30 (:REWRITE USE-ALL-CONSP-2))
 (30 30 (:REWRITE USE-ALL-CONSP))
 (29 28 (:REWRITE DEFAULT-CDR))
 (28 14 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (24 12 (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP-CHEAP))
 (24 12 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (24 12 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (24 12 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (20 10 (:TYPE-PRESCRIPTION ALEN1-TYPE))
 (17 17 (:REWRITE USE-ALL-NATP-2))
 (17 17 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (14 14 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (14 14 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (14 14 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (14 14 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (14 14 (:REWRITE ALL-<-TRANSITIVE))
 (12 12 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (12 12 (:REWRITE USE-ALL-<=-2))
 (12 12 (:REWRITE USE-ALL-<=))
 (12 12 (:REWRITE USE-ALL-<-2))
 (12 12 (:REWRITE USE-ALL-<))
 (12 12 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (12 12 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (12 12 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (12 12 (:REWRITE INTEGERP-OF-CAR-WHEN-POSSIBLY-NEGATED-NODENUMSP-WEAKEN-CHEAP))
 (12 12 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (10 10 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (10 10 (:TYPE-PRESCRIPTION ARRAY1P))
 (8 8 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE CDR-CONS))
 (1 1 (:REWRITE CAR-CONS))
 )
(ALL-<-OF-GET-NOT-DONE-NODES
 (196 98 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-AREF1-WHEN-DAG-PARENT-ARRAYP))
 (98 98 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (98 98 (:TYPE-PRESCRIPTION DAG-PARENT-ARRAYP))
 (68 9 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (40 10 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (20 10 (:TYPE-PRESCRIPTION ALEN1-TYPE))
 (19 15 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (15 15 (:REWRITE USE-ALL-CONSP-2))
 (15 15 (:REWRITE USE-ALL-CONSP))
 (15 15 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (13 13 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (13 13 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (10 10 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (10 10 (:TYPE-PRESCRIPTION ARRAY1P))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:REWRITE USE-ALL-RATIONALP-2))
 (2 2 (:REWRITE USE-ALL-RATIONALP))
 (1 1 (:REWRITE USE-ALL-<=-2))
 (1 1 (:REWRITE USE-ALL-<=))
 (1 1 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (1 1 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 )
(MAKE-CONTEXT-ARRAY-FOR-ANCESTORS
 (1559 1559 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (416 282 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-AREF1-WHEN-DAG-PARENT-ARRAYP))
 (407 22 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (380 9 (:DEFINITION NAT-LISTP))
 (282 282 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (96 96 (:TYPE-PRESCRIPTION NAT-LISTP))
 (60 60 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (58 38 (:REWRITE DEFAULT-+-2))
 (56 26 (:REWRITE USE-ALL-NATP))
 (44 22 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (38 38 (:REWRITE USE-ALL-<-2))
 (38 38 (:REWRITE USE-ALL-<))
 (38 38 (:REWRITE DEFAULT-+-1))
 (38 38 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (37 37 (:REWRITE USE-ALL-<=-2))
 (37 37 (:REWRITE USE-ALL-<=))
 (37 5 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (34 34 (:REWRITE DEFAULT-<-2))
 (34 17 (:REWRITE DEFAULT-WHEN-DAG-PARENT-ARRAYP))
 (30 30 (:TYPE-PRESCRIPTION MEMBERP))
 (26 26 (:REWRITE USE-ALL-NATP-2))
 (26 26 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (26 16 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (26 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (23 21 (:REWRITE DEFAULT-CDR))
 (21 21 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (21 12 (:REWRITE ALL-<-TRANSITIVE))
 (20 16 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (20 10 (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP-CHEAP))
 (20 10 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (19 19 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (19 17 (:REWRITE DEFAULT-CAR))
 (17 3 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (16 4 (:REWRITE ALL-<-OF-AREF1-WHEN-BOUNDED-DAG-PARENT-ARRAYP))
 (15 9 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (14 1 (:REWRITE CONTEXT-ARRAYP-OF-ASET1-AT-END-GEN))
 (13 13 (:REWRITE USE-ALL-CONSP-2))
 (13 13 (:REWRITE USE-ALL-CONSP))
 (12 12 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP-LIST))
 (12 2 (:REWRITE ALL-<-OF-ALEN1-WHEN-PSEUDO-DAG-ARRAYP-LIST))
 (12 2 (:REWRITE <-OF-CAR-AND-ALEN1-WHEN-PSEUDO-DAG-ARRAYP-LIST))
 (12 2 (:REWRITE <-OF-CAR-AND-ALEN1))
 (11 9 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (10 10 (:REWRITE INTEGERP-OF-CAR-WHEN-POSSIBLY-NEGATED-NODENUMSP-WEAKEN-CHEAP))
 (10 10 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (10 2 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (9 9 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (9 3 (:DEFINITION BINARY-APPEND))
 (8 8 (:TYPE-PRESCRIPTION BOUNDED-DAG-PARENT-ARRAYP))
 (8 8 (:LINEAR ARRAY2P-LINEAR))
 (8 4 (:REWRITE TRUE-LISTP-WHEN-POSSIBLY-NEGATED-NODENUMSP))
 (8 4 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (8 4 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (7 7 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (7 7 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (6 6 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP-SPECIAL-ALT))
 (6 6 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP-SPECIAL))
 (6 6 (:REWRITE PSEUDO-DAG-ARRAYP-LIST-WHEN-BOUNDED-DARG-LISTP))
 (5 5 (:REWRITE USE-ALL-RATIONALP-2))
 (5 5 (:REWRITE USE-ALL-RATIONALP))
 (4 4 (:TYPE-PRESCRIPTION POSSIBLY-NEGATED-NODENUMSP))
 (4 4 (:TYPE-PRESCRIPTION ALL-RATIONALP))
 (4 4 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (4 4 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (4 4 (:REWRITE PERM-OF-APPEND-WHEN-NOT-CONSP))
 (4 4 (:REWRITE BOUNDED-DAG-PARENT-ARRAYP-MONOTONE))
 (3 3 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (3 3 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (3 2 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (2 2 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE BOUNDED-DAG-PARENT-ENTRIESP-MONOTONE))
 )
(GET-CONTEXT-FOR-NODENUM
 (10 5 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-AREF1-WHEN-DAG-PARENT-ARRAYP))
 (5 5 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (5 5 (:TYPE-PRESCRIPTION DAG-PARENT-ARRAYP))
 )
