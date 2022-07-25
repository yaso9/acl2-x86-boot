(MOD-THEOREM-ONE
 (4724 964 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (3478 30 (:LINEAR MOD-BOUNDS-3))
 (2348 188 (:META META-INTEGERP-CORRECT))
 (1682 40 (:REWRITE MOD-ZERO . 2))
 (1484 964 (:TYPE-PRESCRIPTION INTEGERP-MOD))
 (1291 1291 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1291 1291 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1291 1291 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1238 40 (:REWRITE MOD-ZERO . 3))
 (1103 983 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (1087 983 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (1046 40 (:REWRITE MOD-X-Y-=-X . 4))
 (1046 40 (:REWRITE MOD-X-Y-=-X . 3))
 (1031 231 (:REWRITE DEFAULT-*-2))
 (983 983 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (983 983 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (714 10 (:REWRITE |(equal (* x y) 0)|))
 (648 60 (:LINEAR MOD-BOUNDS-2))
 (648 60 (:LINEAR MOD-BOUNDS-1))
 (622 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
 (395 115 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (393 57 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (393 57 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (393 57 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (231 231 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (231 231 (:REWRITE DEFAULT-*-1))
 (208 152 (:REWRITE DEFAULT-<-2))
 (208 152 (:REWRITE DEFAULT-<-1))
 (188 188 (:REWRITE INTEGERP-MINUS-X))
 (173 173 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (169 169 (:REWRITE |(< (- x) (- y))|))
 (152 152 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (152 152 (:REWRITE DEFAULT-UNARY-/))
 (136 80 (:REWRITE MOD-COMPLETION))
 (120 8 (:REWRITE MOD-+-CANCEL-0-WEAK))
 (117 117 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (115 115 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (96 40 (:REWRITE MOD-NEG))
 (96 40 (:REWRITE MOD-CANCEL-*))
 (89 89 (:REWRITE |(integerp (* c x))|))
 (81 57 (:REWRITE DEFAULT-+-2))
 (77 77 (:REWRITE |(< (- x) 0)|))
 (75 75 (:REWRITE |(< 0 (- x))|))
 (73 73 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (73 73 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (68 20 (:REWRITE INTEGERP-MOD))
 (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (62 62 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (61 61 (:REWRITE |(* c (* d x))|))
 (57 57 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (57 57 (:REWRITE DEFAULT-+-1))
 (57 57 (:REWRITE |(equal (- x) (- y))|))
 (53 53 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (53 53 (:REWRITE |(equal (- x) 0)|))
 (43 43 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (43 43 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (40 40 (:REWRITE MOD-X-Y-=-X . 2))
 (40 40 (:REWRITE MOD-MINUS-2))
 (18 18 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (16 16 (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (7 7 (:REWRITE |(< (+ c x) d)|))
 (5 5 (:REWRITE |(< d (+ c x))|))
 (4 4 (:REWRITE MOD-ZERO . 1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (3 3 (:REWRITE |(- (* c x))|))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(< (+ d x) (+ c y))|))
 (2 2 (:REWRITE |(< (+ c x) (+ d y))|))
 (2 2 (:REWRITE |(< (+ c x y) d)|))
 )
(IND-FN)
(MOD-THEOREM-TWO-HELPER-HELPER
 (87318 21934 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (47784 684 (:REWRITE MOD-ZERO . 3))
 (45738 21934 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (41716 684 (:REWRITE MOD-X-Y-=-X . 3))
 (41658 21934 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (41275 684 (:REWRITE MOD-ZERO . 2))
 (39738 684 (:REWRITE MOD-X-Y-=-X . 4))
 (31233 31233 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (30492 2556 (:META META-INTEGERP-CORRECT))
 (30095 342 (:LINEAR MOD-BOUNDS-3))
 (21934 21934 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (21934 21934 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (19764 4075 (:REWRITE DEFAULT-*-2))
 (7860 1916 (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
 (7551 1803 (:REWRITE DEFAULT-+-2))
 (6958 1116 (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
 (6236 1040 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5700 2556 (:REWRITE INTEGERP-MINUS-X))
 (4710 4710 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4710 4710 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4710 4710 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (4231 4075 (:REWRITE DEFAULT-*-1))
 (4075 4075 (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (4060 1704 (:REWRITE DEFAULT-<-1))
 (4032 1704 (:REWRITE DEFAULT-<-2))
 (3912 1368 (:REWRITE MOD-COMPLETION))
 (3359 3359 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (3228 1803 (:REWRITE DEFAULT-+-1))
 (3228 684 (:REWRITE MOD-CANCEL-*))
 (3187 592 (:REWRITE DEFAULT-UNARY-MINUS))
 (3044 684 (:REWRITE MOD-NEG))
 (3026 1542 (:REWRITE DEFAULT-EXPT-1))
 (2763 139 (:REWRITE MOD-+-CANCEL-0-WEAK))
 (2656 2656 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2656 2656 (:REWRITE DEFAULT-UNARY-/))
 (2574 1202 (:LINEAR EXPT-X->=-X))
 (2574 1202 (:LINEAR EXPT-X->-X))
 (2574 1202 (:LINEAR EXPT->-1-TWO))
 (2574 1202 (:LINEAR EXPT->-1-ONE))
 (2574 1202 (:LINEAR EXPT-<-1-TWO))
 (2574 1202 (:LINEAR EXPT-<-1-ONE))
 (2404 2404 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (2404 2404 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (2404 2404 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (2404 2404 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2112 684 (:REWRITE MOD-MINUS-2))
 (1960 1960 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (1936 1936 (:REWRITE |(< (- x) (- y))|))
 (1918 1636 (:REWRITE |(expt 2^i n)|))
 (1803 1803 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1636 1636 (:REWRITE |(expt x c)|))
 (1636 1636 (:REWRITE |(expt x (- n))|))
 (1636 1636 (:REWRITE |(expt 1/c n)|))
 (1636 1636 (:REWRITE |(expt (- x) n)|))
 (1542 1542 (:REWRITE DEFAULT-EXPT-2))
 (1508 1508 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (1508 1508 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (1508 1508 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (1484 1484 (:REWRITE |(integerp (* c x))|))
 (1398 1398 (:REWRITE |(equal (- x) (- y))|))
 (1237 1237 (:REWRITE |(equal (- x) 0)|))
 (924 924 (:REWRITE |(* c (* d x))|))
 (879 879 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (808 808 (:REWRITE |(< (- x) 0)|))
 (797 797 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (788 684 (:REWRITE MOD-X-Y-=-X . 2))
 (780 780 (:REWRITE |(< 0 (- x))|))
 (723 723 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (697 697 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (554 554 (:REWRITE |(equal (+ c x) d)|))
 (330 330 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (330 330 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (330 330 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (330 330 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (321 321 (:REWRITE |arith (expt x c)|))
 (321 321 (:REWRITE |arith (expt x (- n))|))
 (321 321 (:REWRITE |arith (expt 1/c n)|))
 (278 278 (:REWRITE |(- (* c x))|))
 (212 212 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (171 171 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (109 109 (:REWRITE |(< (+ c x) d)|))
 (105 105 (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
 (105 105 (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
 (105 105 (:TYPE-PRESCRIPTION NOT-INTEGERP-1C))
 (105 105 (:REWRITE |(< d (+ c x))|))
 (99 99 (:REWRITE |arith (* c (* d x))|))
 (95 95 (:REWRITE ZP-OPEN))
 (66 66 (:REWRITE FOLD-CONSTS-IN-+))
 (48 48 (:REWRITE |arith (* (- x) y)|))
 (33 33 (:TYPE-PRESCRIPTION NOT-INTEGERP-3J))
 (33 33 (:TYPE-PRESCRIPTION NOT-INTEGERP-2J))
 (33 33 (:TYPE-PRESCRIPTION NOT-INTEGERP-1J))
 (32 32 (:REWRITE |arith (- (* c x))|))
 (18 18 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (18 18 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (18 18 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (18 18 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (18 18 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (18 18 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
 (18 18 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
 (18 18 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
 (18 18 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (18 18 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (10 10 (:REWRITE MOD-NEGATIVE . 3))
 (10 10 (:REWRITE MOD-NEGATIVE . 2))
 (8 8 (:REWRITE MOD-POSITIVE . 3))
 (8 8 (:REWRITE MOD-POSITIVE . 2))
 (8 8 (:REWRITE |(< (+ d x) (+ c y))|))
 (8 8 (:REWRITE |(< (+ c x) (+ d y))|))
 (8 8 (:REWRITE |(< (+ c x y) d)|))
 )
(MOD-THEOREM-TWO-HELPER
 (1521 357 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (748 7 (:REWRITE MOD-ZERO . 3))
 (414 7 (:REWRITE MOD-X-Y-=-X . 4))
 (414 7 (:REWRITE MOD-X-Y-=-X . 3))
 (409 7 (:REWRITE CANCEL-MOD-+))
 (381 8 (:LINEAR MOD-BOUNDS-3))
 (357 357 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (357 357 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (357 357 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (357 357 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (357 357 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (357 357 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (331 331 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (331 331 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (331 331 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (318 2 (:REWRITE |(equal (expt x n) 0)|))
 (314 314 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (314 314 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (303 7 (:REWRITE MOD-ZERO . 2))
 (231 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (208 26 (:REWRITE DEFAULT-*-2))
 (196 16 (:LINEAR MOD-BOUNDS-2))
 (196 16 (:LINEAR MOD-BOUNDS-1))
 (190 2 (:REWRITE |(expt x (+ m n)) non-zero x|))
 (105 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (105 13 (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-EQUAL))
 (105 13 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (80 28 (:REWRITE SIMPLIFY-SUMS-<))
 (80 28 (:REWRITE SIMPLIFY-PRODUCTS-SCATTER-EXPONENTS-<))
 (80 28 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (67 22 (:META META-INTEGERP-CORRECT))
 (64 8 (:LINEAR EXPT-X->=-X))
 (64 8 (:LINEAR EXPT-X->-X))
 (64 8 (:LINEAR EXPT->-1-TWO))
 (64 8 (:LINEAR EXPT->-1-ONE))
 (64 8 (:LINEAR EXPT-<-1-TWO))
 (64 8 (:LINEAR EXPT-<-1-ONE))
 (63 3 (:REWRITE |(* (* x y) z)|))
 (54 28 (:REWRITE DEFAULT-<-2))
 (54 28 (:REWRITE DEFAULT-<-1))
 (54 12 (:REWRITE DEFAULT-EXPT-1))
 (44 26 (:REWRITE DEFAULT-*-1))
 (44 14 (:REWRITE MOD-COMPLETION))
 (40 4 (:REWRITE MOD-+-CANCEL-0-WEAK))
 (37 7 (:REWRITE MOD-CANCEL-*))
 (33 7 (:REWRITE MOD-NEG))
 (30 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
 (28 28 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (28 28 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (28 28 (:REWRITE |(< (- x) (- y))|))
 (26 26 (:REWRITE NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (23 23 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (22 22 (:REWRITE REDUCE-INTEGERP-+))
 (22 22 (:REWRITE INTEGERP-MINUS-X))
 (21 1 (:REWRITE |(equal (* x y) 0)|))
 (20 20 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (20 20 (:REWRITE DEFAULT-UNARY-/))
 (17 17 (:REWRITE |(integerp (* c x))|))
 (16 16 (:REWRITE |(expt x (- n))|))
 (16 16 (:REWRITE |(expt 2^i n)|))
 (16 16 (:REWRITE |(expt 1/c n)|))
 (16 16 (:REWRITE |(expt (- x) n)|))
 (16 16 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (16 16 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (15 15 (:REWRITE |(equal (- x) (- y))|))
 (14 14 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (14 14 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (14 14 (:REWRITE |(equal (- x) 0)|))
 (14 14 (:REWRITE |(< 0 (- x))|))
 (14 14 (:REWRITE |(< (- x) 0)|))
 (12 12 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (12 12 (:REWRITE DEFAULT-EXPT-2))
 (11 7 (:REWRITE MOD-MINUS-2))
 (7 7 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (7 7 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (7 7 (:REWRITE MOD-X-Y-=-X . 2))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (4 4 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:REWRITE NORMALIZE-ADDENDS))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE MOD-ZERO . 1))
 (3 3 (:REWRITE |(* c (* d x))|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 )
(MOD-THEOREM-TWO
 (4018 878 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2667 23 (:REWRITE MOD-ZERO . 3))
 (1440 23 (:REWRITE MOD-X-Y-=-X . 3))
 (1433 23 (:REWRITE MOD-X-Y-=-X . 4))
 (1426 26 (:LINEAR MOD-BOUNDS-3))
 (1150 8 (:REWRITE |(equal (expt x n) 0)|))
 (1020 23 (:REWRITE CANCEL-MOD-+))
 (892 892 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (892 892 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (892 892 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (878 878 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (878 878 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (878 878 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (878 878 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (878 878 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (878 878 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (840 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (838 23 (:REWRITE MOD-ZERO . 2))
 (700 52 (:LINEAR MOD-BOUNDS-2))
 (700 52 (:LINEAR MOD-BOUNDS-1))
 (697 697 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (697 697 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (504 28 (:REWRITE |(* y x)|))
 (442 50 (:REWRITE DEFAULT-*-2))
 (261 85 (:REWRITE SIMPLIFY-SUMS-<))
 (261 85 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (261 85 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (256 32 (:LINEAR EXPT-X->=-X))
 (256 32 (:LINEAR EXPT-X->-X))
 (256 32 (:LINEAR EXPT->-1-TWO))
 (256 32 (:LINEAR EXPT->-1-ONE))
 (256 32 (:LINEAR EXPT-<-1-TWO))
 (256 32 (:LINEAR EXPT-<-1-ONE))
 (229 31 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (229 31 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (229 31 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (173 85 (:REWRITE DEFAULT-<-2))
 (173 85 (:REWRITE DEFAULT-<-1))
 (134 46 (:REWRITE MOD-COMPLETION))
 (128 16 (:REWRITE DEFAULT-EXPT-1))
 (111 23 (:REWRITE MOD-NEG))
 (111 23 (:REWRITE MOD-CANCEL-*))
 (88 88 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (85 85 (:REWRITE |(< (- x) (- y))|))
 (81 9 (:REWRITE MOD-+-CANCEL-0-WEAK))
 (64 64 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (64 64 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (64 64 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (64 64 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (57 57 (:REWRITE REDUCE-INTEGERP-+))
 (57 57 (:REWRITE INTEGERP-MINUS-X))
 (57 57 (:META META-INTEGERP-CORRECT))
 (56 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (56 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (56 56 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (55 55 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (55 55 (:REWRITE DEFAULT-UNARY-/))
 (50 50 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (50 50 (:REWRITE DEFAULT-*-1))
 (50 50 (:REWRITE |(integerp (* c x))|))
 (41 41 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (41 41 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (41 41 (:REWRITE |(< 0 (- x))|))
 (41 41 (:REWRITE |(< (- x) 0)|))
 (39 39 (:REWRITE |(equal (- x) (- y))|))
 (38 38 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (33 33 (:REWRITE |(equal (- x) 0)|))
 (28 14 (:REWRITE DEFAULT-+-2))
 (27 23 (:REWRITE MOD-MINUS-2))
 (25 25 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (24 24 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (23 23 (:REWRITE MOD-X-Y-=-X . 2))
 (20 20 (:REWRITE |(expt x (- n))|))
 (20 20 (:REWRITE |(expt 2^i n)|))
 (20 20 (:REWRITE |(expt 1/c n)|))
 (20 20 (:REWRITE |(expt (- x) n)|))
 (16 16 (:REWRITE DEFAULT-EXPT-2))
 (15 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (14 14 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14 14 (:REWRITE DEFAULT-+-1))
 (12 4 (:REWRITE |(equal (+ c x) d)|))
 (7 7 (:REWRITE MOD-ZERO . 1))
 (3 3 (:REWRITE |(* 1 x)|))
 )
(MOD-THEOREM-THREE
 (2276 20 (:REWRITE CANCEL-MOD-+))
 (1960 20 (:REWRITE MOD-ZERO . 3))
 (1829 373 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (1419 47 (:META META-INTEGERP-CORRECT))
 (1300 20 (:REWRITE MOD-ZERO . 2))
 (1102 4 (:REWRITE |(equal (* x y) 0)|))
 (1012 20 (:REWRITE MOD-X-Y-=-X . 4))
 (1012 20 (:REWRITE MOD-X-Y-=-X . 3))
 (693 65 (:REWRITE DEFAULT-*-2))
 (636 8 (:LINEAR MOD-BOUNDS-3))
 (596 10 (:REWRITE |(* (* x y) z)|))
 (594 594 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (594 594 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (442 442 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (442 442 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (442 442 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (384 10 (:REWRITE |(* y (* x z))|))
 (373 373 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (373 373 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (373 373 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (373 373 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (373 373 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (373 373 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (324 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-4C))
 (320 8 (:REWRITE |(equal (expt x n) 0)|))
 (202 38 (:REWRITE SIMPLIFY-SUMS-<))
 (202 38 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (202 38 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (160 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (156 16 (:LINEAR MOD-BOUNDS-2))
 (156 16 (:LINEAR MOD-BOUNDS-1))
 (150 36 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (150 36 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (150 36 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (141 29 (:REWRITE DEFAULT-EXPT-1))
 (130 40 (:REWRITE MOD-COMPLETION))
 (120 38 (:REWRITE DEFAULT-<-2))
 (120 38 (:REWRITE DEFAULT-<-1))
 (110 20 (:REWRITE MOD-NEG))
 (110 20 (:REWRITE MOD-CANCEL-*))
 (84 56 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (84 56 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (65 65 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (65 65 (:REWRITE DEFAULT-*-1))
 (62 4 (:REWRITE MOD-+-CANCEL-0-WEAK))
 (56 56 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (56 56 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (56 28 (:LINEAR EXPT-X->=-X))
 (56 28 (:LINEAR EXPT-X->-X))
 (56 28 (:LINEAR EXPT->-1-TWO))
 (56 28 (:LINEAR EXPT->-1-ONE))
 (56 28 (:LINEAR EXPT-<-1-TWO))
 (56 28 (:LINEAR EXPT-<-1-ONE))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (48 20 (:REWRITE MOD-MINUS-2))
 (47 47 (:REWRITE REDUCE-INTEGERP-+))
 (47 47 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (47 47 (:REWRITE INTEGERP-MINUS-X))
 (47 47 (:REWRITE DEFAULT-UNARY-/))
 (44 44 (:REWRITE |(equal (- x) (- y))|))
 (43 43 (:REWRITE |(equal (- x) 0)|))
 (38 38 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (38 38 (:REWRITE |(< (- x) (- y))|))
 (37 37 (:REWRITE |(integerp (* c x))|))
 (35 35 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (30 30 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (29 29 (:REWRITE DEFAULT-EXPT-2))
 (29 29 (:REWRITE |(expt x (- n))|))
 (29 29 (:REWRITE |(expt 2^i n)|))
 (29 29 (:REWRITE |(expt 1/c n)|))
 (29 29 (:REWRITE |(expt (- x) n)|))
 (28 20 (:REWRITE MOD-X-Y-=-X . 2))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
 (20 20 (:TYPE-PRESCRIPTION NOT-INTEGERP-1C))
 (20 20 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (20 20 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (20 20 (:REWRITE |(* c (* d x))|))
 (19 19 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (19 19 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (19 19 (:REWRITE |(< 0 (- x))|))
 (19 19 (:REWRITE |(< (- x) 0)|))
 (13 13 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (13 13 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (4 4 (:REWRITE |(< 0 (* x y))|))
 (4 4 (:REWRITE |(< (* x y) 0)|))
 (3 3 (:REWRITE MOD-ZERO . 1))
 )
(MOD-EXPT-FAST-1
 (150 3 (:REWRITE MOD-ZERO . 3))
 (134 3 (:REWRITE MOD-X-Y-=-X . 4))
 (134 3 (:REWRITE MOD-X-Y-=-X . 3))
 (130 3 (:REWRITE MOD-ZERO . 2))
 (126 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (120 108 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (120 108 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (117 3 (:REWRITE CANCEL-MOD-+))
 (108 108 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (108 108 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (108 108 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (108 108 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (76 76 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (76 76 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (76 76 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (57 57 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (57 33 (:REWRITE DEFAULT-*-2))
 (52 44 (:META META-INTEGERP-CORRECT))
 (44 44 (:REWRITE REDUCE-INTEGERP-+))
 (44 44 (:REWRITE INTEGERP-MINUS-X))
 (39 39 (:REWRITE |(integerp (* c x))|))
 (34 2 (:REWRITE CANCEL-FLOOR-+))
 (33 33 (:REWRITE DEFAULT-*-1))
 (31 15 (:REWRITE SIMPLIFY-SUMS-<))
 (31 15 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (31 15 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (26 2 (:REWRITE |(equal (expt x n) 0)|))
 (24 2 (:REWRITE |(* (* x y) z)|))
 (23 15 (:REWRITE DEFAULT-<-2))
 (23 15 (:REWRITE DEFAULT-<-1))
 (16 16 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (16 16 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (16 16 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (16 16 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (16 2 (:REWRITE FLOOR-ZERO . 3))
 (15 15 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (15 15 (:REWRITE |(< (- x) (- y))|))
 (14 6 (:REWRITE MOD-COMPLETION))
 (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (13 1 (:REWRITE |(equal (* x y) 0)|))
 (11 3 (:REWRITE MOD-NEG))
 (11 3 (:REWRITE MOD-MINUS-2))
 (11 3 (:REWRITE MOD-CANCEL-*))
 (8 8 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (8 8 (:REWRITE DEFAULT-UNARY-/))
 (8 8 (:REWRITE |(equal (- x) 0)|))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
 (8 8 (:LINEAR EXPT-X->=-X))
 (8 8 (:LINEAR EXPT-X->-X))
 (8 8 (:LINEAR EXPT->-1-TWO))
 (8 8 (:LINEAR EXPT->-1-ONE))
 (8 8 (:LINEAR EXPT-<-1-TWO))
 (8 8 (:LINEAR EXPT-<-1-ONE))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (7 7 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (7 7 (:REWRITE |(< 0 (- x))|))
 (6 6 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (6 6 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 6 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 6 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt x (- n))|))
 (6 6 (:REWRITE |(expt 2^i n)|))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE |(< (- x) 0)|))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (3 3 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (3 3 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (3 3 (:REWRITE MOD-X-Y-=-X . 2))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE FLOOR-ZERO . 4))
 (2 2 (:REWRITE FLOOR-ZERO . 2))
 (2 2 (:REWRITE FLOOR-MINUS-WEAK))
 (2 2 (:REWRITE FLOOR-MINUS-2))
 (2 2 (:REWRITE FLOOR-COMPLETION))
 (2 2 (:REWRITE FLOOR-CANCEL-*-WEAK))
 (2 2 (:REWRITE |(* c (* d x))|))
 (1 1 (:REWRITE FLOOR-NEGATIVE . 3))
 (1 1 (:REWRITE FLOOR-NEGATIVE . 2))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 )
(MOD-EXPT-FAST-1-AS-MOD-AND-EXPT
 (24638 223 (:REWRITE CANCEL-MOD-+))
 (19757 222 (:REWRITE MOD-ZERO . 3))
 (18214 222 (:REWRITE MOD-ZERO . 2))
 (15045 3388 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (14905 3360 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (14848 851 (:META META-INTEGERP-CORRECT))
 (14258 223 (:REWRITE MOD-X-Y-=-X . 4))
 (12231 124 (:REWRITE |(equal (* x y) 0)|))
 (10939 1313 (:REWRITE DEFAULT-*-2))
 (9562 9562 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (8471 75 (:LINEAR MOD-BOUNDS-3))
 (6550 6550 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (6550 6550 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (6550 6550 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (3878 486 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
 (3388 3388 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (3388 3388 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (3388 3388 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (3360 3360 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (2474 70 (:REWRITE |(equal (expt x n) 0)|))
 (1848 1848 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (1848 1848 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (1848 1848 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (1848 1848 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (1848 1848 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
 (1848 1848 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
 (1848 1848 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (1848 1848 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (1794 1794 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
 (1652 540 (:REWRITE DEFAULT-<-1))
 (1649 1313 (:REWRITE DEFAULT-*-1))
 (1648 540 (:REWRITE DEFAULT-<-2))
 (1648 444 (:REWRITE MOD-COMPLETION))
 (1629 537 (:REWRITE DEFAULT-EXPT-2))
 (1559 548 (:REWRITE |(expt 2^i n)|))
 (1525 370 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1525 370 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1525 370 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1502 1502 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1502 1502 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1427 223 (:REWRITE MOD-NEG))
 (1427 223 (:REWRITE MOD-CANCEL-*))
 (1329 537 (:REWRITE DEFAULT-EXPT-1))
 (1069 161 (:REWRITE DEFAULT-+-2))
 (1011 223 (:REWRITE MOD-MINUS-2))
 (994 150 (:LINEAR MOD-BOUNDS-2))
 (884 34 (:REWRITE MOD-+-CANCEL-0-WEAK))
 (851 851 (:REWRITE INTEGERP-MINUS-X))
 (747 747 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (747 747 (:REWRITE DEFAULT-UNARY-/))
 (736 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-4K))
 (712 109 (:REWRITE FLOOR-ZERO . 3))
 (560 560 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (548 548 (:REWRITE |(expt x (- n))|))
 (548 548 (:REWRITE |(expt 1/c n)|))
 (548 548 (:REWRITE |(expt (- x) n)|))
 (547 547 (:REWRITE |(< (- x) (- y))|))
 (536 536 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (536 536 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (536 536 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (536 536 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (516 516 (:REWRITE |(integerp (* c x))|))
 (516 5 (:REWRITE |(* y (* x z))|))
 (486 486 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (486 486 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (486 486 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (486 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-4C))
 (440 440 (:REWRITE |(equal (- x) (- y))|))
 (420 420 (:REWRITE |(equal (- x) 0)|))
 (350 350 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (340 268 (:LINEAR EXPT-X->=-X))
 (340 268 (:LINEAR EXPT-X->-X))
 (340 268 (:LINEAR EXPT->-1-TWO))
 (340 268 (:LINEAR EXPT->-1-ONE))
 (340 268 (:LINEAR EXPT-<-1-TWO))
 (340 268 (:LINEAR EXPT-<-1-ONE))
 (326 222 (:REWRITE MOD-X-Y-=-X . 2))
 (223 223 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (223 223 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (204 204 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (204 204 (:REWRITE |(< (- x) 0)|))
 (203 203 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (203 203 (:REWRITE |(< 0 (- x))|))
 (180 180 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (168 168 (:REWRITE ARITH-NORMALIZE-FACTORS-SCATTER-EXPONENTS))
 (161 161 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (161 161 (:REWRITE DEFAULT-+-1))
 (124 1 (:REWRITE |(< x (if a b c))|))
 (124 1 (:REWRITE |(< (if a b c) x)|))
 (110 1 (:REWRITE |(equal (if a b c) x)|))
 (109 109 (:REWRITE FLOOR-ZERO . 4))
 (109 109 (:REWRITE FLOOR-ZERO . 2))
 (109 109 (:REWRITE FLOOR-MINUS-WEAK))
 (109 109 (:REWRITE FLOOR-MINUS-2))
 (109 109 (:REWRITE FLOOR-COMPLETION))
 (109 109 (:REWRITE FLOOR-CANCEL-*-WEAK))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-4E))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-3E))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-2E))
 (94 94 (:TYPE-PRESCRIPTION NOT-INTEGERP-1E))
 (94 94 (:REWRITE |arith (expt x (- n))|))
 (94 94 (:REWRITE |arith (expt 1/c n)|))
 (94 2 (:REWRITE |(* (if a b c) x)|))
 (54 54 (:REWRITE |arith (* c (* d x))|))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-3K))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-2K))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-1K))
 (17 17 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (16 16 (:REWRITE ARITH-NORMALIZE-ADDENDS))
 (14 14 (:REWRITE MOD-ZERO . 1))
 (14 14 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
 (10 10 (:TYPE-PRESCRIPTION NOT-INTEGERP-1C))
 (9 9 (:REWRITE FLOOR-POSITIVE . 3))
 (9 9 (:REWRITE FLOOR-POSITIVE . 2))
 (4 4 (:REWRITE |(< (+ c x) d)|))
 (3 3 (:REWRITE |(< d (+ c x))|))
 (1 1 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE FLOOR-NEGATIVE . 3))
 (1 1 (:REWRITE FLOOR-NEGATIVE . 2))
 (1 1 (:REWRITE |(< (+ d x) (+ c y))|))
 (1 1 (:REWRITE |(< (+ c x) (+ d y))|))
 (1 1 (:REWRITE |(< (+ c x y) d)|))
 )
(MOD-EXPT-FAST-IS-MOD-EXPT
 (376 6 (:REWRITE MOD-ZERO . 3))
 (306 6 (:REWRITE MOD-X-Y-=-X . 4))
 (306 6 (:REWRITE MOD-X-Y-=-X . 3))
 (246 246 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (246 246 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (246 246 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (222 6 (:REWRITE CANCEL-MOD-+))
 (216 6 (:REWRITE MOD-ZERO . 2))
 (156 36 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (156 36 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (130 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (104 13 (:REWRITE |(* y x)|))
 (100 5 (:REWRITE |(equal (expt x n) 0)|))
 (86 2 (:LINEAR MOD-BOUNDS-3))
 (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (73 73 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (65 13 (:REWRITE DEFAULT-*-2))
 (52 12 (:REWRITE SIMPLIFY-SUMS-<))
 (52 12 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (52 12 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (40 40 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (40 40 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (40 40 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (40 40 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (36 36 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (36 36 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (36 36 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (36 36 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (36 12 (:REWRITE MOD-COMPLETION))
 (32 12 (:REWRITE DEFAULT-<-2))
 (32 12 (:REWRITE DEFAULT-<-1))
 (30 6 (:REWRITE MOD-CANCEL-*))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (26 6 (:REWRITE MOD-NEG))
 (26 6 (:REWRITE MOD-MINUS-2))
 (20 20 (:REWRITE |(equal (- x) 0)|))
 (20 20 (:REWRITE |(equal (- x) (- y))|))
 (20 20 (:LINEAR EXPT-X->=-X))
 (20 20 (:LINEAR EXPT-X->-X))
 (20 20 (:LINEAR EXPT->-1-TWO))
 (20 20 (:LINEAR EXPT->-1-ONE))
 (20 20 (:LINEAR EXPT-<-1-TWO))
 (20 20 (:LINEAR EXPT-<-1-ONE))
 (20 4 (:LINEAR MOD-BOUNDS-2))
 (16 16 (:REWRITE REDUCE-INTEGERP-+))
 (16 16 (:REWRITE INTEGERP-MINUS-X))
 (16 16 (:META META-INTEGERP-CORRECT))
 (15 15 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (15 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (15 15 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (15 15 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (13 13 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (13 13 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (13 13 (:REWRITE DEFAULT-UNARY-/))
 (13 13 (:REWRITE DEFAULT-*-1))
 (13 13 (:REWRITE |(integerp (* c x))|))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (12 12 (:REWRITE |(< (- x) (- y))|))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE |(expt x (- n))|))
 (8 8 (:REWRITE |(expt 2^i n)|))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (6 6 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (6 6 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (6 6 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (6 6 (:REWRITE MOD-X-Y-=-X . 2))
 (6 6 (:REWRITE |(< (- x) 0)|))
 (5 5 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (5 5 (:REWRITE |(< 0 (- x))|))
 (2 2 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 )
(MOD-EXPT-FAST
 (271 271 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (271 271 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (262 4 (:REWRITE MOD-X-Y-=-X . 4))
 (262 4 (:REWRITE MOD-X-Y-=-X . 3))
 (242 4 (:REWRITE MOD-ZERO . 3))
 (192 4 (:REWRITE MOD-ZERO . 2))
 (164 4 (:REWRITE CANCEL-MOD-+))
 (143 123 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (133 3 (:REWRITE MOD-+-CANCEL-0-WEAK))
 (123 123 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (123 123 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (123 123 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (122 122 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (117 117 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (117 117 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (117 117 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (88 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (68 8 (:REWRITE |(* y x)|))
 (60 3 (:REWRITE |(equal (expt x n) 0)|))
 (46 10 (:REWRITE SIMPLIFY-SUMS-<))
 (46 10 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (46 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (44 8 (:REWRITE DEFAULT-*-2))
 (28 28 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (28 28 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (28 28 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (28 28 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (28 10 (:REWRITE DEFAULT-<-2))
 (28 10 (:REWRITE DEFAULT-<-1))
 (26 8 (:REWRITE MOD-COMPLETION))
 (22 4 (:REWRITE MOD-CANCEL-*))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (16 16 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (14 14 (:REWRITE |(equal (- x) (- y))|))
 (14 14 (:LINEAR EXPT-X->=-X))
 (14 14 (:LINEAR EXPT-X->-X))
 (14 14 (:LINEAR EXPT->-1-TWO))
 (14 14 (:LINEAR EXPT->-1-ONE))
 (14 14 (:LINEAR EXPT-<-1-TWO))
 (14 14 (:LINEAR EXPT-<-1-ONE))
 (13 13 (:REWRITE |(equal (- x) 0)|))
 (11 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (11 11 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (11 11 (:REWRITE REDUCE-INTEGERP-+))
 (11 11 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (11 11 (:REWRITE INTEGERP-MINUS-X))
 (11 11 (:META META-INTEGERP-CORRECT))
 (10 10 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (10 10 (:REWRITE |(< (- x) (- y))|))
 (9 4 (:REWRITE MOD-NEG))
 (9 4 (:REWRITE MOD-MINUS-2))
 (8 8 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (8 8 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (8 8 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (8 8 (:REWRITE DEFAULT-UNARY-/))
 (8 8 (:REWRITE DEFAULT-EXPT-2))
 (8 8 (:REWRITE DEFAULT-EXPT-1))
 (8 8 (:REWRITE DEFAULT-*-1))
 (8 8 (:REWRITE |(integerp (* c x))|))
 (8 8 (:REWRITE |(expt x (- n))|))
 (8 8 (:REWRITE |(expt 2^i n)|))
 (8 8 (:REWRITE |(expt 1/c n)|))
 (8 8 (:REWRITE |(expt (- x) n)|))
 (5 5 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (5 5 (:REWRITE |(< (- x) 0)|))
 (4 4 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (4 4 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (4 4 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (4 4 (:REWRITE MOD-X-Y-=-X . 2))
 (4 4 (:REWRITE |(< 0 (- x))|))
 )
