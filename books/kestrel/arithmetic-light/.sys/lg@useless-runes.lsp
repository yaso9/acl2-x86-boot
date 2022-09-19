(LG)
(LG-OF-EXPT
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(LG-OF-BOTH-SIDES)
(EQUAL-OF-EXPT-AND-CONSTANT
 (39 39 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(EQUAL-OF-0-AND-LG
 (21 1 (:DEFINITION INTEGER-LENGTH))
 (9 2 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 1 (:REWRITE FLOOR-WHEN-<))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:TYPE-PRESCRIPTION FLOOR))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (1 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (1 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (1 1 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (1 1 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (1 1 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 )
(NATP-OF-LG
 (5 1 (:REWRITE <-OF-INTEGER-LENGTH-ARG1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE NATP-OF-+-WHEN-NATP-AND-NATP))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(POSP-OF-LG
 (10 3 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (5 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (2 2 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (2 2 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (2 2 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (1 1 (:TYPE-PRESCRIPTION FLOOR))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (1 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 )
(NATP-OF-LG-TYPE
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(EXPT-OF-LG-WHEN-POWER-OF-2P
 (8 4 (:TYPE-PRESCRIPTION NATP-OF-LG-TYPE))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (4 4 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 )
(<=-OF-EXPT-2-OF-LG-LINEAR
 (21 21 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (9 5 (:REWRITE DEFAULT-+-2))
 (8 4 (:REWRITE EXPT-2-OF-+-OF--1-AND-INTEGER-LENGTH-WHEN-POWER-OF-2P-CHEAP))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:TYPE-PRESCRIPTION POWER-OF-2P))
 (3 3 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR-2))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(<=-OF-EXPT-2-OF-+-OF-1-AND-LG-LINEAR
 (36 36 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 3 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:LINEAR EXPT-BOUND-LINEAR-2))
 )
(<-OF-EXPT-2-OF-LG-SAME
 (18 18 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (2 1 (:REWRITE EXPT-2-OF-+-OF--1-AND-INTEGER-LENGTH-WHEN-POWER-OF-2P-CHEAP))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE <-OF-EXPT-2-AND-CONSTANT))
 )
(<-OF-EXPT-2-OF-LG-SAME-LINEAR
 (185 185 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (67 33 (:REWRITE DEFAULT-+-2))
 (39 33 (:REWRITE DEFAULT-+-1))
 (32 26 (:REWRITE EXPT-2-OF-+-OF--1-AND-INTEGER-LENGTH-WHEN-POWER-OF-2P-CHEAP))
 (24 24 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (24 24 (:LINEAR EXPT-BOUND-LINEAR))
 (17 17 (:LINEAR EXPT-BOUND-LINEAR-2))
 (15 9 (:REWRITE DEFAULT-*-2))
 (15 3 (:REWRITE <-OF-INTEGER-LENGTH-ARG1))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-*-1))
 (7 7 (:TYPE-PRESCRIPTION POSP))
 (7 7 (:REWRITE EQUAL-OF-EXPT-AND-CONSTANT))
 )
(<-OF-LG-AND-0
 (6 3 (:TYPE-PRESCRIPTION NATP-OF-LG-TYPE))
 (5 1 (:REWRITE <-OF-INTEGER-LENGTH-ARG1))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (3 1 (:DEFINITION POSP))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(LG-OF-*-OF-1/2
 (10 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (2 2 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 )
(<-OF-LG-WHEN-UNSIGNED-BYTE-P
 (12 6 (:REWRITE EXPT-2-OF-+-OF--1-AND-INTEGER-LENGTH-WHEN-POWER-OF-2P-CHEAP))
 (12 5 (:REWRITE DEFAULT-+-2))
 (8 5 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION POWER-OF-2P))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR))
 (4 1 (:REWRITE DEFAULT-*-2))
 (3 3 (:LINEAR EXPT-BOUND-LINEAR-2))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(<-OF-LG-WHEN-UNSIGNED-BYTE-P-CHEAP
 (12 6 (:REWRITE EXPT-2-OF-+-OF--1-AND-INTEGER-LENGTH-WHEN-POWER-OF-2P-CHEAP))
 (12 5 (:REWRITE DEFAULT-+-2))
 (8 5 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION POWER-OF-2P))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR))
 (4 1 (:REWRITE DEFAULT-*-2))
 (3 3 (:LINEAR EXPT-BOUND-LINEAR-2))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
