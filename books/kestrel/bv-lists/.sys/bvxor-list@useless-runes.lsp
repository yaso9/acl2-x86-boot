(BVXOR-LIST
 (33 18 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE DEFAULT-+-1))
 (18 14 (:REWRITE DEFAULT-<-2))
 (17 17 (:REWRITE DEFAULT-CDR))
 (17 14 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE ALL-UNSIGNED-BYTE-P-IMPLIES-ALL-INTEGERP))
 (5 5 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(BVXOR-LIST-OF-NIL)
(LEN-OF-BVXOR-LIST
 (14 7 (:REWRITE DEFAULT-+-2))
 (12 6 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (12 3 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-POSITIVE))
 (11 10 (:REWRITE DEFAULT-CDR))
 (9 3 (:REWRITE BVXOR-WHEN-Y-IS-NOT-AN-INTEGER))
 (9 3 (:REWRITE BVXOR-WHEN-X-IS-NOT-AN-INTEGER))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-AN-INTEGER))
 (3 3 (:REWRITE BVXOR-SUBST-ARG3))
 (3 3 (:REWRITE BVXOR-SUBST-ARG2))
 (3 3 (:REWRITE BVXOR-OF-CONSTANT-TRIM-ARG1))
 )
(CONSP-OF-BVXOR-LIST
 (12 6 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (12 3 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-POSITIVE))
 (9 3 (:REWRITE BVXOR-WHEN-Y-IS-NOT-AN-INTEGER))
 (9 3 (:REWRITE BVXOR-WHEN-X-IS-NOT-AN-INTEGER))
 (6 6 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-AN-INTEGER))
 (3 3 (:REWRITE BVXOR-SUBST-ARG3))
 (3 3 (:REWRITE BVXOR-SUBST-ARG2))
 (3 3 (:REWRITE BVXOR-OF-CONSTANT-TRIM-ARG1))
 )
(NTH-OF-BVXOR-LIST
 (150 22 (:REWRITE INTEGERP-OF-NTH-WHEN-ALL-INTEGERP))
 (147 32 (:REWRITE BVXOR-WHEN-Y-IS-NOT-AN-INTEGER))
 (147 32 (:REWRITE BVXOR-WHEN-X-IS-NOT-AN-INTEGER))
 (136 81 (:REWRITE DEFAULT-+-2))
 (104 32 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-POSITIVE))
 (101 92 (:REWRITE DEFAULT-CDR))
 (100 100 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (84 48 (:REWRITE DEFAULT-<-2))
 (81 81 (:REWRITE DEFAULT-+-1))
 (80 40 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (69 63 (:REWRITE DEFAULT-CAR))
 (48 48 (:REWRITE DEFAULT-<-1))
 (40 8 (:REWRITE ALL-INTEGERP-OF-CDR))
 (32 32 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-AN-INTEGER))
 (32 32 (:REWRITE BVXOR-SUBST-ARG3))
 (32 32 (:REWRITE BVXOR-SUBST-ARG2))
 (32 32 (:REWRITE BVXOR-OF-CONSTANT-TRIM-ARG1))
 (30 30 (:REWRITE ALL-UNSIGNED-BYTE-P-IMPLIES-ALL-INTEGERP))
 (30 30 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (24 24 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (22 22 (:REWRITE ZP-OPEN))
 (22 22 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (10 10 (:REWRITE EQUAL-OF-CONSTANT-AND-BVXOR-OF-CONSTANT))
 (6 6 (:REWRITE CAR-CONS))
 )
(ALL-UNSIGNED-BYTE-P-OF-BVXOR-LIST
 (54 1 (:REWRITE UNSIGNED-BYTE-P-OF-BVXOR-ALT))
 (52 6 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (40 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (37 1 (:DEFINITION MEMBER-EQUAL))
 (24 12 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (18 6 (:REWRITE BVXOR-WHEN-Y-IS-NOT-AN-INTEGER))
 (18 6 (:REWRITE BVXOR-WHEN-X-IS-NOT-AN-INTEGER))
 (18 6 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-POSITIVE))
 (16 13 (:REWRITE DEFAULT-CAR))
 (14 11 (:REWRITE DEFAULT-CDR))
 (12 12 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE CONSP-OF-BVXOR-LIST))
 (6 6 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-AN-INTEGER))
 (6 6 (:REWRITE BVXOR-SUBST-ARG3))
 (6 6 (:REWRITE BVXOR-SUBST-ARG2))
 (6 6 (:REWRITE BVXOR-OF-CONSTANT-TRIM-ARG1))
 (5 5 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (5 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (5 1 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(ALL-INTEGERP-OF-BVXOR-LIST
 (12 6 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (12 3 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-POSITIVE))
 (10 5 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (9 3 (:REWRITE BVXOR-WHEN-Y-IS-NOT-AN-INTEGER))
 (9 3 (:REWRITE BVXOR-WHEN-X-IS-NOT-AN-INTEGER))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE DEFAULT-<-2))
 (5 5 (:TYPE-PRESCRIPTION BVXOR-LIST))
 (5 5 (:REWRITE ALL-UNSIGNED-BYTE-P-IMPLIES-ALL-INTEGERP))
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-AN-INTEGER))
 (3 3 (:REWRITE BVXOR-SUBST-ARG3))
 (3 3 (:REWRITE BVXOR-SUBST-ARG2))
 (3 3 (:REWRITE BVXOR-OF-CONSTANT-TRIM-ARG1))
 )
(BVXOR-LIST-IFF
 (24 12 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (24 6 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-POSITIVE))
 (18 6 (:REWRITE BVXOR-WHEN-Y-IS-NOT-AN-INTEGER))
 (18 6 (:REWRITE BVXOR-WHEN-X-IS-NOT-AN-INTEGER))
 (12 12 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (12 12 (:REWRITE DEFAULT-CAR))
 (12 6 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-AN-INTEGER))
 (6 6 (:REWRITE BVXOR-SUBST-ARG3))
 (6 6 (:REWRITE BVXOR-SUBST-ARG2))
 (6 6 (:REWRITE BVXOR-OF-CONSTANT-TRIM-ARG1))
 )
(TAKE-OF-BVXOR-LIST
 (45 27 (:REWRITE DEFAULT-CAR))
 (39 21 (:REWRITE DEFAULT-CDR))
 (36 18 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (36 9 (:REWRITE BVXOR-WHEN-Y-IS-NOT-AN-INTEGER))
 (36 9 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-POSITIVE))
 (28 19 (:REWRITE DEFAULT-<-2))
 (27 9 (:REWRITE BVXOR-WHEN-X-IS-NOT-AN-INTEGER))
 (25 19 (:REWRITE DEFAULT-<-1))
 (20 14 (:REWRITE DEFAULT-+-2))
 (18 18 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (14 14 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 9 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-AN-INTEGER))
 (9 9 (:REWRITE BVXOR-SUBST-ARG3))
 (9 9 (:REWRITE BVXOR-SUBST-ARG2))
 (9 9 (:REWRITE BVXOR-OF-CONSTANT-TRIM-ARG1))
 (8 8 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE CONSP-OF-BVXOR-LIST))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(NTHCDR-OF-BVXOR-LIST
 (142 75 (:REWRITE DEFAULT-CDR))
 (117 25 (:REWRITE BVXOR-WHEN-Y-IS-NOT-AN-INTEGER))
 (100 50 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (100 25 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-POSITIVE))
 (92 50 (:REWRITE DEFAULT-CAR))
 (82 72 (:REWRITE DEFAULT-+-2))
 (75 25 (:REWRITE BVXOR-WHEN-X-IS-NOT-AN-INTEGER))
 (73 48 (:REWRITE DEFAULT-<-2))
 (72 72 (:REWRITE DEFAULT-+-1))
 (56 48 (:REWRITE DEFAULT-<-1))
 (50 50 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (46 19 (:REWRITE ZP-OPEN))
 (27 9 (:REWRITE FOLD-CONSTS-IN-+))
 (25 25 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (25 25 (:REWRITE BVXOR-WHEN-SIZE-IS-NOT-AN-INTEGER))
 (25 25 (:REWRITE BVXOR-SUBST-ARG3))
 (25 25 (:REWRITE BVXOR-SUBST-ARG2))
 (25 25 (:REWRITE BVXOR-OF-CONSTANT-TRIM-ARG1))
 (8 8 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (7 7 (:REWRITE CONSP-OF-BVXOR-LIST))
 )
