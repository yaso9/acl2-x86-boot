(EQUAL-LOG=-0)
(EQUAL-LOG=-1)
(EQUAL-LNOT-0
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE BITS-EXPT-CONSTANT))
 )
(EQUAL-LNOT-1
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE BITS-EXPT-CONSTANT))
 )
(BITS-IF)
(BITN-IF)
(BITS-IF1
 (21 10 (:REWRITE DEFAULT-<-1))
 (17 6 (:REWRITE BITS-WITH-INDICES-IN-THE-WRONG-ORDER))
 (17 6 (:REWRITE BITS-IGNORE-NEGATIVE-BITS-OF-INTEGER))
 (16 13 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (14 10 (:REWRITE DEFAULT-<-2))
 (14 1 (:LINEAR BITS-LESS-THAN-X-GEN))
 (12 6 (:REWRITE BITS-WITH-X-NOT-RATIONAL))
 (9 7 (:REWRITE DEFAULT-+-2))
 (9 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE BITS-WITH-J-NOT-AN-INTEGER))
 (6 6 (:REWRITE BITS-WITH-I-NOT-AN-INTEGER))
 (6 6 (:REWRITE BITS-EXPT-CONSTANT))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE IF1-NON-0))
 )
(BITN-IF1
 (2 2 (:REWRITE IF1-NON-0))
 )
(LOG=-0-REWRITE
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE BITS-EXPT-CONSTANT))
 )
(LOG=-1-REWRITE
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(LOG<>-IS-LNOT-LOG=
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(BVECP-IF)
