(APPLY$-BADGEP-PROPERTIES
 (47 47 (:REWRITE DEFAULT-CDR))
 (31 1 (:DEFINITION SUBSETP-EQUAL))
 (28 4 (:DEFINITION MEMBER-EQUAL))
 (14 14 (:REWRITE DEFAULT-CAR))
 (5 1 (:DEFINITION LEN))
 (3 1 (:DEFINITION ALL-NILS))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE DEFAULT-+-2))
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(META-APPLY$-PRIM
 (4507 4507 (:REWRITE DEFAULT-CDR))
 (306 6 (:DEFINITION APPLY$-BADGEP))
 (240 6 (:DEFINITION NATP))
 (169 7 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (165 7 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (72 72 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (42 9 (:REWRITE O-P-O-INFP-CAR))
 (30 6 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (28 28 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (28 8 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (24 12 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (20 10 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (18 18 (:TYPE-PRESCRIPTION WEAK-APPLY$-BADGE-P))
 (17 17 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (15 9 (:REWRITE O-P-DEF-O-FINP-1))
 (6 6 (:TYPE-PRESCRIPTION O-FINP))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 )
(N-CAR-CADR-CADDR-ETC-OPENER
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(SUITABLY-TAMEP-LISTP-INDUCTION)
(SUITABLY-TAMEP-LISTP-IMPLICANT-1
 (32 8 (:REWRITE O-P-O-INFP-CAR))
 (24 24 (:REWRITE DEFAULT-CAR))
 (15 14 (:REWRITE DEFAULT-+-2))
 (14 14 (:REWRITE DEFAULT-+-1))
 (11 5 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE O-P-DEF-O-FINP-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE O-INFP->NEQ-0))
 )
(TAMEP-IMPLICANT-1
 (496 496 (:REWRITE DEFAULT-CDR))
 (140 140 (:REWRITE DEFAULT-CAR))
 (135 19 (:DEFINITION LEN))
 (116 29 (:REWRITE O-P-O-INFP-CAR))
 (116 5 (:DEFINITION SUITABLY-TAMEP-LISTP))
 (63 9 (:DEFINITION SYMBOL-LISTP))
 (44 5 (:REWRITE ZP-OPEN))
 (43 24 (:REWRITE DEFAULT-+-2))
 (37 1 (:DEFINITION SUBSETP-EQUAL))
 (34 15 (:DEFINITION TRUE-LISTP))
 (34 4 (:DEFINITION MEMBER-EQUAL))
 (29 29 (:REWRITE O-P-DEF-O-FINP-1))
 (24 24 (:REWRITE DEFAULT-+-1))
 (16 4 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (13 7 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-COERCE-2))
 (9 9 (:REWRITE DEFAULT-COERCE-1))
 (8 2 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (7 7 (:REWRITE DEFAULT-<-1))
 (4 1 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (3 1 (:DEFINITION ALL-NILS))
 (1 1 (:TYPE-PRESCRIPTION TAMEP-FUNCTIONP))
 )
(APPLY$-LAMBDA-OPENER
 (190 190 (:REWRITE DEFAULT-CDR))
 (61 61 (:REWRITE DEFAULT-CAR))
 (60 15 (:REWRITE O-P-O-INFP-CAR))
 (30 30 (:TYPE-PRESCRIPTION O-P))
 (15 15 (:REWRITE O-P-DEF-O-FINP-1))
 )
(EV$-DEF-FACT
 (30712 23556 (:REWRITE DEFAULT-CDR))
 (11534 9226 (:REWRITE DEFAULT-CAR))
 (10176 2255 (:REWRITE O-P-O-INFP-CAR))
 (4053 579 (:DEFINITION LEN))
 (3507 2207 (:REWRITE O-P-DEF-O-FINP-1))
 (2646 378 (:DEFINITION SYMBOL-LISTP))
 (2265 257 (:DEFINITION ASSOC-EQUAL))
 (1264 1264 (:TYPE-PRESCRIPTION O-FINP))
 (1179 600 (:REWRITE DEFAULT-+-2))
 (973 21 (:REWRITE ZP-OPEN))
 (885 15 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (875 5 (:DEFINITION APPLY$-BADGEP))
 (837 27 (:REWRITE APPLY$-LAMBDA-OPENER))
 (609 609 (:TYPE-PRESCRIPTION LEN))
 (600 600 (:REWRITE DEFAULT-+-1))
 (470 5 (:DEFINITION SUBSETP-EQUAL))
 (440 20 (:DEFINITION MEMBER-EQUAL))
 (287 287 (:REWRITE DEFAULT-COERCE-2))
 (287 287 (:REWRITE DEFAULT-COERCE-1))
 (210 210 (:TYPE-PRESCRIPTION EV$-LIST))
 (135 27 (:DEFINITION PAIRLIS$))
 (108 108 (:REWRITE UNTAME-APPLY$-TAKES-ARITY-ARGS))
 (90 10 (:DEFINITION NATP))
 (60 60 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (40 20 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (35 5 (:DEFINITION TRUE-LISTP))
 (31 31 (:REWRITE DEFAULT-<-2))
 (31 31 (:REWRITE DEFAULT-<-1))
 (30 30 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (30 15 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (30 5 (:DEFINITION ALL-NILS))
 (27 27 (:META APPLY$-PRIM-META-FN-CORRECT))
 (25 25 (:TYPE-PRESCRIPTION ALL-NILS))
 (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (20 20 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (20 5 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (10 5 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (10 5 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 )
(EV$-DEF)
(EV$-OPENER
 (5436 9 (:DEFINITION EV$))
 (3667 3068 (:REWRITE DEFAULT-CDR))
 (1382 2 (:DEFINITION APPLY$))
 (1280 264 (:REWRITE O-P-O-INFP-CAR))
 (1218 58 (:DEFINITION LAMBDA-OBJECT-BODY))
 (1211 943 (:REWRITE DEFAULT-CAR))
 (884 52 (:DEFINITION LENGTH))
 (840 56 (:DEFINITION LAMBDA-OBJECT-SHAPEP))
 (728 104 (:DEFINITION LEN))
 (723 723 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (506 56 (:DEFINITION SYMBOL-LISTP))
 (488 264 (:REWRITE O-P-DEF-O-FINP-1))
 (288 4 (:DEFINITION TAMEP-FUNCTIONP))
 (238 238 (:TYPE-PRESCRIPTION EV$-LIST))
 (232 58 (:DEFINITION LAMBDA-OBJECT-FORMALS))
 (210 106 (:REWRITE DEFAULT-+-2))
 (208 208 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (206 2 (:REWRITE APPLY$-LAMBDA-OPENER))
 (176 176 (:TYPE-PRESCRIPTION O-FINP))
 (164 3 (:DEFINITION SUITABLY-TAMEP-LISTP))
 (142 2 (:DEFINITION EV$-LIST))
 (140 58 (:DEFINITION BADGE))
 (119 12 (:DEFINITION ASSOC-EQUAL))
 (106 106 (:REWRITE DEFAULT-+-1))
 (52 52 (:REWRITE DEFAULT-COERCE-2))
 (52 52 (:REWRITE DEFAULT-COERCE-1))
 (22 2 (:DEFINITION PAIRLIS$))
 (12 2 (:REWRITE ZP-OPEN))
 (4 4 (:TYPE-PRESCRIPTION TAMEP-FUNCTIONP))
 (4 4 (:REWRITE UNTAME-APPLY$-TAKES-ARITY-ARGS))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META APPLY$-PRIM-META-FN-CORRECT))
 )
(EV$-LIST-DEF
 (350 2 (:DEFINITION EV$))
 (222 2 (:DEFINITION TAMEP))
 (181 143 (:REWRITE DEFAULT-CDR))
 (79 67 (:REWRITE DEFAULT-CAR))
 (72 16 (:REWRITE O-P-O-INFP-CAR))
 (42 2 (:DEFINITION LAMBDA-OBJECT-BODY))
 (34 2 (:DEFINITION LENGTH))
 (32 32 (:TYPE-PRESCRIPTION O-P))
 (30 2 (:DEFINITION LAMBDA-OBJECT-SHAPEP))
 (28 4 (:DEFINITION LEN))
 (24 24 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (24 16 (:REWRITE O-P-DEF-O-FINP-1))
 (18 2 (:DEFINITION ASSOC-EQUAL))
 (15 15 (:REWRITE EV$-OPENER))
 (14 2 (:DEFINITION SYMBOL-LISTP))
 (8 8 (:TYPE-PRESCRIPTION O-FINP))
 (8 4 (:REWRITE DEFAULT-+-2))
 (8 2 (:DEFINITION LAMBDA-OBJECT-FORMALS))
 (4 4 (:TYPE-PRESCRIPTION TAMEP))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 2 (:DEFINITION BADGE))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(BETA-REDUCTION
 (40 40 (:REWRITE DEFAULT-CDR))
 (30 6 (:DEFINITION PAIRLIS$))
 (16 16 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE EV$-OPENER))
 )
(APPLY$-PRIMP-BADGE)
(BADGE-BADGE)
(BADGE-TAMEP)
(BADGE-TAMEP-FUNCTIONP)
(BADGE-SUITABLY-TAMEP-LISTP)
(BADGE-APPLY$)
(BADGE-EV$)
(APPLY$-PRIMITIVE
 (2 2 (:META APPLY$-PRIM-META-FN-CORRECT))
 )
(APPLY$-BADGE
 (6 2 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(APPLY$-TAMEP
 (250 2 (:DEFINITION TAMEP))
 (130 102 (:REWRITE DEFAULT-CDR))
 (47 47 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (42 2 (:DEFINITION LAMBDA-OBJECT-BODY))
 (36 28 (:REWRITE DEFAULT-CAR))
 (36 8 (:REWRITE O-P-O-INFP-CAR))
 (34 2 (:DEFINITION LENGTH))
 (30 2 (:DEFINITION LAMBDA-OBJECT-SHAPEP))
 (28 4 (:DEFINITION LEN))
 (16 16 (:TYPE-PRESCRIPTION O-P))
 (14 2 (:DEFINITION SYMBOL-LISTP))
 (12 8 (:REWRITE O-P-DEF-O-FINP-1))
 (8 4 (:REWRITE DEFAULT-+-2))
 (8 2 (:DEFINITION LAMBDA-OBJECT-FORMALS))
 (6 2 (:REWRITE APPLY$-PRIMP-BADGE))
 (4 4 (:TYPE-PRESCRIPTION O-FINP))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 2 (:DEFINITION BADGE))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(APPLY$-TAMEP-FUNCTIONP
 (140 2 (:DEFINITION TAMEP-FUNCTIONP))
 (86 74 (:REWRITE DEFAULT-CDR))
 (42 2 (:DEFINITION LAMBDA-OBJECT-BODY))
 (30 2 (:DEFINITION LAMBDA-OBJECT-SHAPEP))
 (21 21 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (20 4 (:REWRITE O-P-O-INFP-CAR))
 (14 2 (:DEFINITION SYMBOL-LISTP))
 (12 12 (:REWRITE DEFAULT-CAR))
 (8 8 (:TYPE-PRESCRIPTION O-P))
 (8 4 (:REWRITE O-P-DEF-O-FINP-1))
 (8 2 (:DEFINITION LAMBDA-OBJECT-FORMALS))
 (6 2 (:REWRITE APPLY$-PRIMP-BADGE))
 (4 4 (:TYPE-PRESCRIPTION O-FINP))
 (4 2 (:DEFINITION BADGE))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(APPLY$-SUITABLY-TAMEP-LISTP
 (104 2 (:DEFINITION SUITABLY-TAMEP-LISTP))
 (52 10 (:REWRITE O-P-O-INFP-CAR))
 (38 26 (:REWRITE DEFAULT-CDR))
 (30 18 (:REWRITE DEFAULT-CAR))
 (22 10 (:REWRITE O-P-DEF-O-FINP-1))
 (20 20 (:TYPE-PRESCRIPTION O-P))
 (12 12 (:TYPE-PRESCRIPTION O-FINP))
 (8 2 (:REWRITE ZP-OPEN))
 (4 4 (:TYPE-PRESCRIPTION TAMEP))
 (2 2 (:TYPE-PRESCRIPTION TAMEP-FUNCTIONP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:DEFINITION NOT))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 (1 1 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 )
(APPLY$-APPLY$
 (615 503 (:REWRITE DEFAULT-CDR))
 (500 4 (:DEFINITION TAMEP))
 (312 66 (:REWRITE O-P-O-INFP-CAR))
 (272 136 (:REWRITE DEFAULT-CAR))
 (130 58 (:REWRITE O-P-DEF-O-FINP-1))
 (116 116 (:TYPE-PRESCRIPTION O-P))
 (104 2 (:DEFINITION SUITABLY-TAMEP-LISTP))
 (78 2 (:REWRITE APPLY$-LAMBDA-OPENER))
 (72 72 (:TYPE-PRESCRIPTION O-FINP))
 (70 10 (:DEFINITION SYMBOL-LISTP))
 (68 4 (:DEFINITION LENGTH))
 (56 8 (:DEFINITION LEN))
 (36 12 (:REWRITE APPLY$-PRIMP-BADGE))
 (24 2 (:DEFINITION PAIRLIS$))
 (18 10 (:REWRITE DEFAULT-+-2))
 (17 6 (:REWRITE APPLY$-PRIMITIVE))
 (10 10 (:TYPE-PRESCRIPTION TAMEP))
 (10 10 (:REWRITE DEFAULT-+-1))
 (8 8 (:TYPE-PRESCRIPTION LEN))
 (8 2 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE UNTAME-APPLY$-TAKES-ARITY-ARGS))
 (4 4 (:REWRITE EV$-OPENER))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META APPLY$-PRIM-META-FN-CORRECT))
 )
(APPLY$-EV$
 (133 105 (:REWRITE DEFAULT-CDR))
 (42 34 (:REWRITE DEFAULT-CAR))
 (36 8 (:REWRITE O-P-O-INFP-CAR))
 (28 4 (:DEFINITION LEN))
 (16 16 (:TYPE-PRESCRIPTION O-P))
 (14 2 (:DEFINITION SYMBOL-LISTP))
 (12 8 (:REWRITE O-P-DEF-O-FINP-1))
 (8 4 (:REWRITE DEFAULT-+-2))
 (6 2 (:REWRITE APPLY$-PRIMP-BADGE))
 (4 4 (:TYPE-PRESCRIPTION O-FINP))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE EV$-OPENER))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(TAKE1)
(TAKE1-TAKE-GEN
 (16 16 (:REWRITE DEFAULT-CAR))
 (13 13 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(ALTERNATIVE-TAKE
 (11 5 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:DEFINITION NOT))
 )
(TAKE-OPENER
 (11 5 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:DEFINITION NOT))
 )
(PAIRLIS$-TAKES-ARITY-ARGS
 (24 17 (:REWRITE DEFAULT-CDR))
 (24 17 (:REWRITE DEFAULT-CAR))
 (24 3 (:REWRITE ZP-OPEN))
 (14 14 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (13 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (6 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 )
(APPLY$-LAMBDA-TAKES-ARITY-ARGS
 (52 49 (:REWRITE DEFAULT-CDR))
 (16 1 (:DEFINITION ALTERNATIVE-TAKE))
 (11 1 (:DEFINITION LEN))
 (8 8 (:TYPE-PRESCRIPTION LEN))
 (8 1 (:REWRITE ZP-OPEN))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (6 1 (:REWRITE O-P-O-INFP-CAR))
 (3 2 (:REWRITE DEFAULT-+-2))
 (3 1 (:REWRITE O-P-DEF-O-FINP-1))
 (2 2 (:TYPE-PRESCRIPTION O-P))
 (2 2 (:TYPE-PRESCRIPTION O-FINP))
 (2 2 (:REWRITE EV$-OPENER))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(APPLY$-LAMBDA-ARITY-1
 (248 248 (:REWRITE DEFAULT-CDR))
 (172 18 (:DEFINITION PAIRLIS$))
 (132 33 (:REWRITE O-P-O-INFP-CAR))
 (132 12 (:DEFINITION ASSOC-EQUAL))
 (45 5 (:DEFINITION LEN))
 (33 33 (:REWRITE O-P-DEF-O-FINP-1))
 (24 24 (:TYPE-PRESCRIPTION PAIRLIS$))
 (10 5 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE CDR-CONS))
 (9 9 (:REWRITE CAR-CONS))
 (5 5 (:REWRITE DEFAULT-+-1))
 )
(HIDE-IS-IDENTITY)
(APPLY$-PRIM-TAKES-ARITY-ARGS)
(APPLY$-PRIM-ARITY-1
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:META APPLY$-PRIM-META-FN-CORRECT))
 )
(APPLY$-USERFN-ARITY-1
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(APPLY$-SYMBOL-ARITY-1
 (750 6 (:DEFINITION TAMEP))
 (651 531 (:REWRITE DEFAULT-CDR))
 (420 6 (:DEFINITION TAMEP-FUNCTIONP))
 (252 12 (:DEFINITION LAMBDA-OBJECT-BODY))
 (180 12 (:DEFINITION LAMBDA-OBJECT-SHAPEP))
 (168 36 (:REWRITE O-P-O-INFP-CAR))
 (161 137 (:REWRITE DEFAULT-CAR))
 (102 6 (:DEFINITION LENGTH))
 (84 12 (:DEFINITION SYMBOL-LISTP))
 (84 12 (:DEFINITION LEN))
 (60 36 (:REWRITE O-P-DEF-O-FINP-1))
 (48 12 (:DEFINITION LAMBDA-OBJECT-FORMALS))
 (24 24 (:TYPE-PRESCRIPTION O-FINP))
 (24 12 (:REWRITE DEFAULT-+-2))
 (12 12 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (12 12 (:TYPE-PRESCRIPTION LEN))
 (12 12 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION TAMEP))
 (6 6 (:REWRITE DEFAULT-COERCE-2))
 (6 6 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:META APPLY$-PRIM-META-FN-CORRECT))
 )
(EQUAL-LEN-0
 (9 5 (:REWRITE DEFAULT-+-2))
 (8 4 (:REWRITE O-INFP->NEQ-0))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(EQUAL-LEN-1
 (116 4 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (114 1 (:DEFINITION APPLY$-BADGEP))
 (69 69 (:REWRITE DEFAULT-CDR))
 (40 1 (:DEFINITION SUBSETP-EQUAL))
 (34 4 (:DEFINITION MEMBER-EQUAL))
 (32 16 (:REWRITE DEFAULT-+-2))
 (18 2 (:DEFINITION NATP))
 (16 16 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE DEFAULT-CAR))
 (11 11 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (7 1 (:DEFINITION TRUE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6 3 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (6 1 (:DEFINITION ALL-NILS))
 (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (4 2 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (4 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (2 1 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 )
(APPLY$-CONSP-ARITY-1
 (235 235 (:REWRITE DEFAULT-CDR))
 (113 89 (:REWRITE DEFAULT-CAR))
 (77 15 (:DEFINITION PAIRLIS$))
 (66 6 (:DEFINITION ASSOC-EQUAL))
 (44 11 (:REWRITE O-P-O-INFP-CAR))
 (19 7 (:REWRITE APPLY$-PRIMITIVE))
 (12 12 (:TYPE-PRESCRIPTION PAIRLIS$))
 (12 12 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (11 11 (:REWRITE O-P-DEF-O-FINP-1))
 (5 1 (:DEFINITION LEN))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE CDR-CONS))
 (1 1 (:REWRITE CAR-CONS))
 (1 1 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 )
(LAMB)
(APPLY$-WARRANT-LAMB)
(APPLY$-WARRANT-LAMB-DEFINITION)
(APPLY$-WARRANT-LAMB-NECC)
(APPLY$-LAMB
 (4 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(CONSP-LAMB)
(CONSP-CDR-LAMB)
(CONSP-CDDR-LAMB)
(CDDDR-LAMB)
(CAR-LAMB)
(LAMBDA-FORMALS-LAMB)
(LAMBDA-BODY-LAMB)
(LAMB-REDUCTION)
(LAMB-V-V-IS-IDENTITY
 (37 21 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE APPLY$-EQUIVALENCE-NECC))
 )
(LAMBDA-V-FN-V-IS-FN
 (842 815 (:REWRITE DEFAULT-CAR))
 (480 16 (:REWRITE APPLY$-LAMBDA-OPENER))
 (384 97 (:REWRITE O-P-O-INFP-CAR))
 (132 72 (:REWRITE DEFAULT-+-2))
 (101 93 (:REWRITE O-P-DEF-O-FINP-1))
 (72 72 (:REWRITE DEFAULT-+-1))
 (19 11 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE DEFAULT-COERCE-2))
 (18 18 (:REWRITE DEFAULT-COERCE-1))
 (11 11 (:REWRITE DEFAULT-<-1))
 (11 1 (:REWRITE APPLY$-APPLY$))
 (10 10 (:REWRITE APPLY$-EQUIVALENCE-NECC))
 (8 8 (:TYPE-PRESCRIPTION O-FINP))
 (8 4 (:DEFINITION TRUE-LISTP))
 (6 6 (:META APPLY$-PRIM-META-FN-CORRECT))
 (2 2 (:REWRITE UNTAME-APPLY$-TAKES-ARITY-ARGS))
 (1 1 (:TYPE-PRESCRIPTION WEAK-APPLY$-BADGE-P))
 )
(OK-FNP)
(APPLY$-WARRANT-OK-FNP)
(APPLY$-WARRANT-OK-FNP-DEFINITION)
(APPLY$-WARRANT-OK-FNP-NECC)
(APPLY$-OK-FNP
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(COMPOSE)
(APPLY$-WARRANT-COMPOSE)
(APPLY$-WARRANT-COMPOSE-DEFINITION)
(APPLY$-WARRANT-COMPOSE-NECC)
(APPLY$-COMPOSE
 (4 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(OK-FNP-COMPOSE
 (15746 15746 (:REWRITE DEFAULT-CDR))
 (6070 105 (:DEFINITION APPLY$-BADGEP))
 (5354 5354 (:REWRITE DEFAULT-CAR))
 (4348 262 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (3628 488 (:DEFINITION LEN))
 (3584 823 (:REWRITE O-P-O-INFP-CAR))
 (2044 758 (:REWRITE APPLY$-PRIMP-BADGE))
 (1506 168 (:DEFINITION NATP))
 (1401 35 (:DEFINITION SUBSETP-EQUAL))
 (1286 1286 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (1191 108 (:DEFINITION MEMBER-EQUAL))
 (1158 628 (:REWRITE DEFAULT-+-2))
 (1115 823 (:REWRITE O-P-DEF-O-FINP-1))
 (860 860 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (628 628 (:REWRITE DEFAULT-+-1))
 (532 105 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (420 105 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (397 299 (:REWRITE DEFAULT-<-2))
 (336 168 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (299 299 (:REWRITE DEFAULT-<-1))
 (294 42 (:DEFINITION TRUE-LISTP))
 (292 292 (:TYPE-PRESCRIPTION O-FINP))
 (210 91 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (178 35 (:DEFINITION ALL-NILS))
 (168 168 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (162 162 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (140 140 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (135 135 (:TYPE-PRESCRIPTION ALL-NILS))
 (135 135 (:REWRITE DEFAULT-COERCE-2))
 (135 135 (:REWRITE DEFAULT-COERCE-1))
 )
(APPLY$-COMPOSITION
 (33785 33473 (:REWRITE DEFAULT-CDR))
 (8767 8263 (:REWRITE DEFAULT-CAR))
 (8000 284 (:REWRITE APPLY$-LAMBDA-OPENER))
 (6308 1477 (:REWRITE O-P-O-INFP-CAR))
 (4968 688 (:DEFINITION LEN))
 (3404 1290 (:REWRITE APPLY$-PRIMP-BADGE))
 (2380 84 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (2324 28 (:DEFINITION APPLY$-BADGEP))
 (1877 1477 (:REWRITE O-P-DEF-O-FINP-1))
 (1523 835 (:REWRITE DEFAULT-+-2))
 (1280 484 (:REWRITE APPLY$-PRIMITIVE))
 (1040 1040 (:TYPE-PRESCRIPTION EV$-LIST))
 (835 835 (:REWRITE DEFAULT-+-1))
 (756 14 (:DEFINITION SUBSETP-EQUAL))
 (672 56 (:DEFINITION MEMBER-EQUAL))
 (504 56 (:DEFINITION NATP))
 (348 348 (:REWRITE UNTAME-APPLY$-TAKES-ARITY-ARGS))
 (299 299 (:REWRITE DEFAULT-COERCE-2))
 (299 299 (:REWRITE DEFAULT-COERCE-1))
 (266 266 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (232 232 (:META APPLY$-PRIM-META-FN-CORRECT))
 (207 179 (:REWRITE DEFAULT-<-2))
 (200 20 (:REWRITE APPLY$-APPLY$))
 (179 179 (:REWRITE DEFAULT-<-1))
 (160 160 (:TYPE-PRESCRIPTION O-FINP))
 (140 70 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (112 56 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (112 28 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (98 14 (:DEFINITION TRUE-LISTP))
 (84 84 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (84 14 (:DEFINITION ALL-NILS))
 (70 70 (:TYPE-PRESCRIPTION ALL-NILS))
 (56 56 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (56 56 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (56 28 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (56 28 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (24 24 (:DEFINITION EQ))
 )
