(UPDATE-NTH-OF-UPDATE-NTH-SAME
 (73 22 (:REWRITE DEFAULT-CDR))
 (60 15 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 )
(CAR-OF-UPDATE-NTH
 (9 9 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(UPDATE-NTH-OF-UPDATE-NTH-DIFF
 (222 123 (:REWRITE DEFAULT-CAR))
 (106 103 (:REWRITE DEFAULT-+-2))
 (103 103 (:REWRITE DEFAULT-+-1))
 (58 57 (:REWRITE DEFAULT-<-1))
 (57 57 (:REWRITE DEFAULT-<-2))
 (54 18 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(UPDATE-NTH-OF-UPDATE-NTH-SAME-VAL
 (283 100 (:REWRITE DEFAULT-CDR))
 (79 52 (:REWRITE DEFAULT-CAR))
 (68 67 (:REWRITE DEFAULT-+-2))
 (67 67 (:REWRITE DEFAULT-+-1))
 (51 17 (:REWRITE FOLD-CONSTS-IN-+))
 (38 38 (:REWRITE DEFAULT-<-2))
 (38 38 (:REWRITE DEFAULT-<-1))
 (36 4 (:REWRITE UPDATE-NTH-OF-UPDATE-NTH-DIFF))
 (24 8 (:DEFINITION NFIX))
 (8 8 (:TYPE-PRESCRIPTION NFIX))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(UPDATE-NTH-WHEN-EQUAL-OF-NTH
 (21 14 (:REWRITE DEFAULT-<-2))
 (21 14 (:REWRITE DEFAULT-+-2))
 (14 14 (:REWRITE DEFAULT-CDR))
 (14 14 (:REWRITE DEFAULT-<-1))
 (14 14 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE DEFAULT-CAR))
 )
(CDR-OF-UPDATE-NTH-0
 (22 11 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (11 11 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:REWRITE DEFAULT-CDR))
 )
(CDR-OF-UPDATE-NTH
 (14 11 (:REWRITE DEFAULT-CDR))
 (11 5 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:DEFINITION NOT))
 )
(UPDATE-NTH-OF-CONS
 (13 7 (:REWRITE DEFAULT-CDR))
 (11 5 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(TRUE-LIST-FIX-OF-UPDATE-NTH-2
 (214 10 (:REWRITE CDR-OF-UPDATE-NTH))
 (174 63 (:REWRITE ZP-OPEN))
 (92 30 (:REWRITE FOLD-CONSTS-IN-+))
 (88 85 (:REWRITE DEFAULT-+-2))
 (85 85 (:REWRITE DEFAULT-+-1))
 (47 10 (:REWRITE CAR-OF-UPDATE-NTH))
 (39 39 (:REWRITE DEFAULT-<-2))
 (39 39 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(TAKE-UPDATE-NTH
 (195 9 (:REWRITE CDR-OF-UPDATE-NTH))
 (191 77 (:REWRITE ZP-OPEN))
 (156 114 (:REWRITE DEFAULT-CDR))
 (131 131 (:REWRITE DEFAULT-+-2))
 (131 131 (:REWRITE DEFAULT-+-1))
 (102 34 (:REWRITE FOLD-CONSTS-IN-+))
 (100 73 (:REWRITE DEFAULT-CAR))
 (80 80 (:REWRITE DEFAULT-<-2))
 (80 80 (:REWRITE DEFAULT-<-1))
 (39 9 (:REWRITE CAR-OF-UPDATE-NTH))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(TRUE-LISTP-OF-UPDATE-NTH-2
 (179 9 (:REWRITE CDR-OF-UPDATE-NTH))
 (70 53 (:REWRITE DEFAULT-+-2))
 (60 30 (:REWRITE ZP-OPEN))
 (53 53 (:REWRITE DEFAULT-+-1))
 (52 41 (:REWRITE DEFAULT-<-2))
 (43 41 (:REWRITE DEFAULT-<-1))
 (32 10 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(UPDATE-NTH-0-EQUAL-REWRITE
 (100 50 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (50 50 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (8 8 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 )
(EQUAL-OF-UPDATE-NTH-SAME
 (68 65 (:REWRITE DEFAULT-CDR))
 (56 46 (:REWRITE DEFAULT-+-2))
 (48 35 (:REWRITE DEFAULT-<-2))
 (46 46 (:REWRITE DEFAULT-+-1))
 (45 30 (:REWRITE ZP-OPEN))
 (38 35 (:REWRITE DEFAULT-CAR))
 (36 35 (:REWRITE DEFAULT-<-1))
 (15 5 (:REWRITE FOLD-CONSTS-IN-+))
 )
(NTH-UPDATE-NTH-SAFE
 (12 2 (:DEFINITION NTH))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(NTHCDR-OF-UPDATE-NTH-SIMPLER
 (290 274 (:REWRITE DEFAULT-+-2))
 (280 274 (:REWRITE DEFAULT-+-1))
 (108 101 (:REWRITE DEFAULT-<-1))
 (101 101 (:REWRITE DEFAULT-<-2))
 (84 39 (:REWRITE DEFAULT-CAR))
 (34 34 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(NTHCDR-OF-UPDATE-NTH-WHEN-<
 (58 29 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (16 2 (:DEFINITION NTHCDR))
 (7 1 (:DEFINITION UPDATE-NTH))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
