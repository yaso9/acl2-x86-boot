(REMOVE1-EQUAL-OF-NIL)
(REMOVE1-EQUAL-WHEN-NOT-CONSP
 (10 1 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (5 5 (:TYPE-PRESCRIPTION LEN))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (1 1 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (1 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(REMOVE1-EQUAL-WHEN-NOT-CONSP-CHEAP)
(CONSP-OF-REMOVE1-EQUAL
 (54 54 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (40 20 (:REWRITE DEFAULT-<-2))
 (33 32 (:REWRITE DEFAULT-CAR))
 (22 22 (:REWRITE REMOVE1-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (22 22 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (20 20 (:REWRITE DEFAULT-<-1))
 (20 19 (:REWRITE DEFAULT-CDR))
 (10 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (8 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (7 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 )
(REMOVE1-EQUAL-OF-CONS
 (20 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE REMOVE1-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (4 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(REMOVE1-EQUAL-OF-CAR-SAME
 (26 3 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (13 13 (:TYPE-PRESCRIPTION LEN))
 (11 2 (:REWRITE DEFAULT-CDR))
 (11 2 (:REWRITE DEFAULT-CAR))
 (7 3 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (5 5 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE REMOVE1-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
 )
(LEN-OF-REMOVE1-EQUAL-LINEAR
 (48 5 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (19 10 (:REWRITE DEFAULT-<-2))
 (14 12 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (12 10 (:REWRITE DEFAULT-<-1))
 (10 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (7 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (5 5 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 )
(LEN-OF-REMOVE1-EQUAL-LINEAR-2
 (22 22 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (22 14 (:REWRITE DEFAULT-+-2))
 (18 16 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (18 9 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE DEFAULT-+-1))
 (14 9 (:REWRITE DEFAULT-<-1))
 (11 2 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (6 6 (:REWRITE CONSP-WHEN-LEN-GREATER))
 )
(LEN-OF-REMOVE1-EQUAL
 (321 37 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (74 69 (:REWRITE DEFAULT-CAR))
 (70 60 (:REWRITE DEFAULT-CDR))
 (66 33 (:REWRITE DEFAULT-<-2))
 (51 35 (:REWRITE DEFAULT-+-2))
 (37 37 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (35 35 (:REWRITE DEFAULT-+-1))
 (33 33 (:REWRITE DEFAULT-<-1))
 (33 33 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (28 26 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(TRUE-LISTP-OF-REMOVE1-EQUAL
 (181 18 (:REWRITE CONSP-OF-REMOVE1-EQUAL))
 (135 14 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (66 19 (:REWRITE DEFAULT-CDR))
 (55 11 (:REWRITE LEN-OF-CDR))
 (48 48 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (23 14 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE DEFAULT-<-1))
 (14 14 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (14 14 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (13 12 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE REMOVE1-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (5 5 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(TRUE-LIST-FIX-OF-REMOVE1-EQUAL
 (254 30 (:REWRITE CONSP-OF-REMOVE1-EQUAL))
 (232 24 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (115 23 (:REWRITE LEN-OF-CDR))
 (103 61 (:REWRITE DEFAULT-CAR))
 (86 34 (:REWRITE DEFAULT-CDR))
 (83 83 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (37 24 (:REWRITE DEFAULT-<-2))
 (25 24 (:REWRITE DEFAULT-+-2))
 (24 24 (:REWRITE DEFAULT-<-1))
 (24 24 (:REWRITE DEFAULT-+-1))
 (24 24 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (24 24 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (11 11 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(REMOVE1-EQUAL-OF-APPEND
 (1012 506 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (506 506 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (506 506 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (373 42 (:REWRITE CONSP-OF-REMOVE1-EQUAL))
 (351 36 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (153 93 (:REWRITE DEFAULT-CAR))
 (125 25 (:REWRITE LEN-OF-CDR))
 (119 45 (:REWRITE DEFAULT-CDR))
 (109 109 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (65 32 (:REWRITE REMOVE1-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (62 36 (:REWRITE DEFAULT-<-2))
 (36 36 (:REWRITE DEFAULT-<-1))
 (36 36 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (36 36 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (27 26 (:REWRITE DEFAULT-+-2))
 (26 26 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(NOT-MEMBER-EQUAL-OF-REMOVE1-EQUAL
 (117 12 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (93 9 (:REWRITE CONSP-OF-REMOVE1-EQUAL))
 (43 29 (:REWRITE DEFAULT-CAR))
 (29 29 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (29 12 (:REWRITE DEFAULT-CDR))
 (25 5 (:REWRITE LEN-OF-CDR))
 (22 12 (:REWRITE DEFAULT-<-2))
 (13 10 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (12 12 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (12 12 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(MEMBER-EQUAL-OF-REMOVE1-EQUAL-WHEN-NOT-EQUAL-IFF
 (316 45 (:REWRITE CONSP-OF-REMOVE1-EQUAL))
 (241 25 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (141 89 (:REWRITE DEFAULT-CAR))
 (99 32 (:REWRITE DEFAULT-CDR))
 (95 95 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (70 14 (:REWRITE LEN-OF-CDR))
 (45 25 (:REWRITE DEFAULT-<-2))
 (25 25 (:REWRITE DEFAULT-<-1))
 (25 25 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (25 25 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (18 16 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(NO-DUPLICATESP-EQUAL-OF-REMOVE1-EQUAL
 (343 22 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (167 22 (:REWRITE LEN-OF-CDR))
 (93 9 (:REWRITE CONSP-OF-REMOVE1-EQUAL))
 (64 64 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (62 6 (:REWRITE LEN-OF-REMOVE1-EQUAL))
 (54 40 (:REWRITE DEFAULT-CAR))
 (51 34 (:REWRITE DEFAULT-CDR))
 (40 22 (:REWRITE DEFAULT-<-2))
 (37 31 (:REWRITE DEFAULT-+-2))
 (31 31 (:REWRITE DEFAULT-+-1))
 (22 22 (:REWRITE DEFAULT-<-1))
 (22 22 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (22 22 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (20 11 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (13 13 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (9 3 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE REMOVE1-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE EQUAL-OF-LEN-AND-0))
 (1 1 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 )
(REMOVE1-EQUAL-OF-REMOVE1-EQUAL
 (286 29 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (196 58 (:REWRITE DEFAULT-CDR))
 (168 110 (:REWRITE DEFAULT-CAR))
 (119 119 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (44 29 (:REWRITE DEFAULT-<-2))
 (42 42 (:REWRITE DEFAULT-+-2))
 (42 42 (:REWRITE DEFAULT-+-1))
 (29 29 (:REWRITE DEFAULT-<-1))
 (29 29 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (29 29 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (19 15 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (14 14 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(REMOVE1-EQUAL-WHEN-NOT-MEMBER-EQUAL
 (173 18 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (30 30 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (30 18 (:REWRITE DEFAULT-<-2))
 (30 6 (:REWRITE LEN-OF-CDR))
 (22 22 (:REWRITE DEFAULT-CDR))
 (20 20 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE DEFAULT-<-1))
 (18 18 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (18 18 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (8 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
