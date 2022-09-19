(YUL::UBYTE16-TO-UTF8
 (19194 3 (:DEFINITION LOGMASKP))
 (12593 3 (:DEFINITION INTEGER-LENGTH))
 (5726 16 (:LINEAR LINEAR-FLOOR-BOUNDS-1))
 (5179 5179 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (5179 5179 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (5179 5179 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (3638 164 (:REWRITE THE-FLOOR-ABOVE))
 (3457 8 (:REWRITE |(equal (+ (- c) x) y)|))
 (3342 282 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (3195 27 (:REWRITE CANCEL-FLOOR-+))
 (2989 27 (:REWRITE FLOOR-ZERO . 3))
 (2560 8 (:REWRITE |(* 1/2 (floor x y))| . 3))
 (2517 6 (:REWRITE UGLY-UNHIDE-HACK-THM-1))
 (2322 282 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (2322 282 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (2036 3 (:REWRITE LOGHEAD-IDENTITY))
 (2030 67 (:REWRITE |(* (- x) y)|))
 (1927 6 (:REWRITE MOD-X-Y-=-X . 3))
 (1921 27 (:REWRITE FLOOR-ZERO . 4))
 (1918 520 (:REWRITE DEFAULT-TIMES-2))
 (1873 27 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (1804 6 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (1644 132 (:REWRITE INTEGERP-MINUS-X))
 (1636 27 (:REWRITE FLOOR-=-X/Y . 3))
 (1555 131 (:REWRITE DEFAULT-PLUS-2))
 (1415 131 (:REWRITE DEFAULT-PLUS-1))
 (1385 27 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1356 520 (:REWRITE DEFAULT-TIMES-1))
 (1306 6 (:REWRITE CANCEL-MOD-+))
 (1302 282 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (1302 282 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (1302 282 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (1302 282 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (1302 282 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (1302 282 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (1302 282 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (1302 282 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (933 1 (:REWRITE FLOOR-=-X/Y . 4))
 (831 27 (:REWRITE FLOOR-=-X/Y . 2))
 (786 786 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (786 786 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (786 786 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (726 67 (:REWRITE DEFAULT-MINUS))
 (624 624 (:TYPE-PRESCRIPTION INTEGER-LENGTH))
 (608 16 (:LINEAR EXPT-<=-1-TWO))
 (592 16 (:LINEAR EXPT->-1-ONE))
 (528 16 (:LINEAR EXPT-X->=-X))
 (528 16 (:LINEAR EXPT-X->-X))
 (528 1 (:REWRITE |(floor (floor x y) z)| . 5))
 (512 6 (:REWRITE MOD-ZERO . 3))
 (450 3 (:REWRITE |(floor x 2)| . 2))
 (431 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (431 8 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (431 8 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (392 12 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (376 157 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (376 157 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (336 16 (:LINEAR EXPT->=-1-ONE))
 (318 159 (:REWRITE DEFAULT-LESS-THAN-1))
 (294 6 (:REWRITE DEFAULT-MOD-RATIO))
 (291 291 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (287 27 (:REWRITE FLOOR-ZERO . 5))
 (287 27 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (258 6 (:REWRITE MOD-X-Y-=-X . 4))
 (255 51 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (255 51 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (239 51 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (239 51 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (239 51 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (237 1 (:REWRITE |(floor (floor x y) z)| . 3))
 (223 159 (:REWRITE DEFAULT-LESS-THAN-2))
 (217 159 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (211 27 (:REWRITE FLOOR-ZERO . 2))
 (211 27 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (211 27 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (191 27 (:REWRITE FLOOR-CANCEL-*-CONST))
 (187 27 (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (182 6 (:REWRITE MOD-ZERO . 4))
 (182 6 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (182 6 (:REWRITE MOD-X-Y-=-X . 2))
 (182 6 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (182 6 (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (180 158 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (168 16 (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (164 164 (:REWRITE THE-FLOOR-BELOW))
 (158 158 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (158 158 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (158 158 (:REWRITE INTEGERP-<-CONSTANT))
 (158 158 (:REWRITE CONSTANT-<-INTEGERP))
 (158 158 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (158 158 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (158 158 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (158 158 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (158 158 (:REWRITE |(< c (- x))|))
 (158 158 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (158 158 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (158 158 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (158 158 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (158 158 (:REWRITE |(< (/ x) (/ y))|))
 (158 158 (:REWRITE |(< (- x) c)|))
 (158 158 (:REWRITE |(< (- x) (- y))|))
 (144 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (135 3 (:DEFINITION EXPT2$INLINE))
 (126 38 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (123 8 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (108 3 (:DEFINITION NFIX))
 (106 26 (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (106 6 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (106 6 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (106 6 (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (106 6 (:REWRITE MOD-CANCEL-*-CONST))
 (103 27 (:REWRITE DEFAULT-FLOOR-1))
 (98 98 (:META META-INTEGERP-CORRECT))
 (92 16 (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (91 8 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (82 38 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (82 6 (:REWRITE DEFAULT-MOD-1))
 (78 78 (:TYPE-PRESCRIPTION |(< (logand x y) 0)| . 1))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (57 57 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (57 38 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (51 51 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (51 51 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (51 51 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (51 51 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (51 51 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (51 27 (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (50 26 (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (49 8 (:REWRITE |(* 1/2 (floor x y))| . 2))
 (46 46 (:TYPE-PRESCRIPTION ABS))
 (38 19 (:REWRITE DEFAULT-EXPT-2))
 (33 33 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (33 33 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (33 33 (:REWRITE |(< 0 (/ x))|))
 (33 33 (:REWRITE |(< 0 (* x y))|))
 (32 32 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (32 32 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (32 32 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (32 32 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (32 16 (:LINEAR EXPT-<-1-TWO))
 (29 1 (:REWRITE FLOOR-UNSIGNED-BYTE-P))
 (27 27 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (27 27 (:TYPE-PRESCRIPTION FLOOR))
 (27 27 (:REWRITE DEFAULT-FLOOR-2))
 (26 26 (:REWRITE |(floor x (- y))| . 2))
 (26 26 (:REWRITE |(floor x (- y))| . 1))
 (26 26 (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (26 26 (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (26 26 (:REWRITE |(floor (- x) y)| . 2))
 (26 26 (:REWRITE |(floor (- x) y)| . 1))
 (25 5 (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (22 1 (:REWRITE |(floor (floor x y) z)| . 4))
 (20 20 (:TYPE-PRESCRIPTION UGLY-UNHIDE-HACK))
 (19 19 (:REWRITE DEFAULT-EXPT-1))
 (19 19 (:REWRITE |(expt 1/c n)|))
 (19 19 (:REWRITE |(expt (- x) n)|))
 (16 16 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (16 16 (:LINEAR EXPT-LINEAR-UPPER-<))
 (16 16 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (16 16 (:LINEAR EXPT-LINEAR-LOWER-<))
 (16 16 (:LINEAR EXPT->=-1-TWO))
 (16 16 (:LINEAR EXPT->-1-TWO))
 (16 16 (:LINEAR EXPT-<=-1-ONE))
 (16 16 (:LINEAR EXPT-<-1-ONE))
 (14 14 (:REWRITE |(< (/ x) 0)|))
 (14 14 (:REWRITE |(< (* x y) 0)|))
 (13 13 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (13 13 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (13 12 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (12 12 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (8 8 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (8 8 (:REWRITE |(equal c (/ x))|))
 (8 8 (:REWRITE |(equal c (- x))|))
 (8 8 (:REWRITE |(equal (/ x) c)|))
 (8 8 (:REWRITE |(equal (/ x) (/ y))|))
 (8 8 (:REWRITE |(equal (- x) c)|))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
 (8 8 (:REWRITE |(* 1/2 (floor x y))| . 1))
 (6 6 (:REWRITE UGLY-UNHIDE-HACK-THM-2))
 (6 6 (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (6 6 (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (6 6 (:REWRITE DEFAULT-MOD-2))
 (6 6 (:REWRITE |(< (+ c/d x) y)|))
 (6 6 (:REWRITE |(< (+ (- c) x) y)|))
 (5 5 (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (5 5 (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (5 5 (:REWRITE |(mod x (- y))| . 3))
 (5 5 (:REWRITE |(mod x (- y))| . 2))
 (5 5 (:REWRITE |(mod x (- y))| . 1))
 (5 5 (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (5 5 (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (5 5 (:REWRITE |(mod (- x) y)| . 3))
 (5 5 (:REWRITE |(mod (- x) y)| . 2))
 (5 5 (:REWRITE |(mod (- x) y)| . 1))
 (5 5 (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (5 5 (:REWRITE |(+ c (+ d x))|))
 (5 1 (:REWRITE |(equal (floor (+ x y) z) x)|))
 (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (4 4 (:REWRITE ASH-GOES-TO-0))
 (4 4 (:REWRITE ASH-0))
 (4 4 (:REWRITE |(equal (expt 2 n) c)|))
 (3 3 (:REWRITE |(floor x 2)| . 1))
 (3 3 (:REWRITE |(< y (+ (- c) x))|))
 (3 3 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE UBYTE16P-WHEN-MEMBER-EQUAL-OF-UBYTE16-LISTP))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 5))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 4))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 3))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 2))
 (1 1 (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (1 1 (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 )
(YUL::UBYTE8-LISTP-OF-UBYTE16-TO-UTF8
 (19194 3 (:DEFINITION LOGMASKP))
 (12593 3 (:DEFINITION INTEGER-LENGTH))
 (11141 9401 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (9401 9401 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (9401 9401 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (9401 9401 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (6270 122 (:REWRITE DEFAULT-PLUS-2))
 (6043 491 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (5129 122 (:REWRITE DEFAULT-PLUS-1))
 (4195 491 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (4195 491 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (3695 37 (:REWRITE CANCEL-FLOOR-+))
 (3570 37 (:REWRITE FLOOR-ZERO . 3))
 (3457 8 (:REWRITE |(equal (+ (- c) x) y)|))
 (2560 8 (:REWRITE |(* 1/2 (floor x y))| . 3))
 (2517 6 (:REWRITE UGLY-UNHIDE-HACK-THM-1))
 (2347 491 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (2347 491 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (2347 491 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (2347 491 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (2347 491 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (2347 491 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (2347 491 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (2347 491 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (2288 101 (:REWRITE |(* (- x) y)|))
 (2238 662 (:REWRITE DEFAULT-TIMES-2))
 (2142 37 (:REWRITE FLOOR-ZERO . 4))
 (2124 37 (:REWRITE FLOOR-X-Y-=-1 . 2))
 (2036 3 (:REWRITE LOGHEAD-IDENTITY))
 (2026 186 (:REWRITE INTEGERP-MINUS-X))
 (2007 12 (:REWRITE MOD-X-Y-=-X . 3))
 (1946 14 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (1813 37 (:REWRITE FLOOR-=-X/Y . 3))
 (1594 12 (:REWRITE CANCEL-MOD-+))
 (1513 193 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (1498 662 (:REWRITE DEFAULT-TIMES-1))
 (1487 37 (:REWRITE DEFAULT-FLOOR-RATIO))
 (1461 17 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (1000 37 (:REWRITE FLOOR-=-X/Y . 2))
 (987 987 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (987 987 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (987 987 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (975 184 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (933 1 (:REWRITE FLOOR-=-X/Y . 4))
 (870 99 (:REWRITE DEFAULT-MINUS))
 (857 193 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (732 191 (:REWRITE DEFAULT-LESS-THAN-1))
 (624 624 (:TYPE-PRESCRIPTION INTEGER-LENGTH))
 (608 16 (:LINEAR EXPT-<=-1-TWO))
 (592 16 (:LINEAR EXPT->-1-ONE))
 (528 16 (:LINEAR EXPT-X->=-X))
 (528 16 (:LINEAR EXPT-X->-X))
 (528 1 (:REWRITE |(floor (floor x y) z)| . 5))
 (515 103 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (515 103 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (499 103 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (499 103 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (499 103 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (450 3 (:REWRITE |(floor x 2)| . 2))
 (445 191 (:REWRITE DEFAULT-LESS-THAN-2))
 (430 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (430 7 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (430 7 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (372 182 (:REWRITE SIMPLIFY-SUMS-<))
 (366 14 (:REWRITE DEFAULT-MOD-RATIO))
 (362 362 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (337 37 (:REWRITE FLOOR-ZERO . 5))
 (337 37 (:REWRITE FLOOR-X-Y-=--1 . 2))
 (336 16 (:LINEAR EXPT->=-1-ONE))
 (288 12 (:REWRITE MOD-X-Y-=-X . 4))
 (269 191 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (261 37 (:REWRITE FLOOR-ZERO . 2))
 (261 37 (:REWRITE FLOOR-X-Y-=-1 . 3))
 (261 37 (:REWRITE FLOOR-X-Y-=--1 . 3))
 (237 1 (:REWRITE |(floor (floor x y) z)| . 3))
 (233 37 (:REWRITE FLOOR-CANCEL-*-CONST))
 (232 190 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (222 14 (:REWRITE MOD-ZERO . 4))
 (222 14 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (212 12 (:REWRITE MOD-X-Y-=-X . 2))
 (212 12 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (212 12 (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (208 208 (:REWRITE THE-FLOOR-BELOW))
 (197 37 (:REWRITE FLOOR-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (190 190 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (190 190 (:REWRITE INTEGERP-<-CONSTANT))
 (190 190 (:REWRITE CONSTANT-<-INTEGERP))
 (190 190 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (190 190 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (190 190 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (190 190 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (190 190 (:REWRITE |(< c (- x))|))
 (190 190 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (190 190 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (190 190 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (190 190 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (190 190 (:REWRITE |(< (/ x) (/ y))|))
 (190 190 (:REWRITE |(< (- x) c)|))
 (190 190 (:REWRITE |(< (- x) (- y))|))
 (177 25 (:REWRITE |(< (* (/ x) y) 1) with (< 0 x)|))
 (175 10 (:LINEAR LINEAR-FLOOR-BOUNDS-3))
 (146 14 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (146 14 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (145 5 (:REWRITE FLOOR-UNSIGNED-BYTE-P))
 (144 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (137 137 (:REWRITE REDUCE-INTEGERP-+))
 (137 137 (:META META-INTEGERP-CORRECT))
 (136 12 (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (136 12 (:REWRITE MOD-CANCEL-*-CONST))
 (135 10 (:LINEAR LINEAR-FLOOR-BOUNDS-2))
 (135 3 (:DEFINITION EXPT2$INLINE))
 (116 36 (:REWRITE |(floor (* x (/ y)) z) not rewriting-goal-literal|))
 (113 37 (:REWRITE DEFAULT-FLOOR-1))
 (108 3 (:DEFINITION NFIX))
 (103 103 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (103 103 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (103 103 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (103 103 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (103 103 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (101 37 (:REWRITE FLOOR-CANCEL-*-REWRITING-GOAL-LITERAL))
 (101 25 (:REWRITE |(< (* (/ x) y) 1) with (< x 0)|))
 (100 36 (:REWRITE |(floor (* x (/ y)) z) rewriting-goal-literal|))
 (90 14 (:REWRITE DEFAULT-MOD-1))
 (86 86 (:TYPE-PRESCRIPTION ABS))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (72 72 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (65 1 (:REWRITE UBYTE16-FIX-WHEN-UBYTE16P))
 (57 38 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (55 11 (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (55 3 (:LINEAR MOD-BOUNDS-3))
 (49 8 (:REWRITE |(* 1/2 (floor x y))| . 2))
 (38 19 (:REWRITE DEFAULT-EXPT-2))
 (37 37 (:REWRITE DEFAULT-FLOOR-2))
 (37 29 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (36 36 (:REWRITE |(floor x (- y))| . 2))
 (36 36 (:REWRITE |(floor x (- y))| . 1))
 (36 36 (:REWRITE |(floor x (* y (/ z))) rewriting-goal-literal|))
 (36 36 (:REWRITE |(floor x (* y (/ z))) not rewriting-goal-literal|))
 (36 36 (:REWRITE |(floor (- x) y)| . 2))
 (36 36 (:REWRITE |(floor (- x) y)| . 1))
 (32 32 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (32 32 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (32 32 (:REWRITE |(< 0 (/ x))|))
 (32 32 (:REWRITE |(< 0 (* x y))|))
 (32 32 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (32 32 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (32 32 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (32 32 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (32 16 (:LINEAR EXPT-<-1-TWO))
 (30 6 (:LINEAR MOD-BOUNDS-2))
 (27 27 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (22 22 (:REWRITE UBYTE8-LISTP-WHEN-SUBSETP-EQUAL))
 (22 1 (:REWRITE |(floor (floor x y) z)| . 4))
 (20 20 (:TYPE-PRESCRIPTION UGLY-UNHIDE-HACK))
 (19 19 (:REWRITE DEFAULT-EXPT-1))
 (19 19 (:REWRITE |(expt 1/c n)|))
 (19 19 (:REWRITE |(expt (- x) n)|))
 (18 18 (:REWRITE UBYTE8P-WHEN-MEMBER-EQUAL-OF-UBYTE8-LISTP))
 (18 18 (:REWRITE |(< (/ x) 0)|))
 (18 18 (:REWRITE |(< (* x y) 0)|))
 (16 16 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (16 16 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (16 16 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (16 16 (:LINEAR EXPT-LINEAR-UPPER-<))
 (16 16 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (16 16 (:LINEAR EXPT-LINEAR-LOWER-<))
 (16 16 (:LINEAR EXPT->=-1-TWO))
 (16 16 (:LINEAR EXPT->-1-TWO))
 (16 16 (:LINEAR EXPT-<=-1-ONE))
 (16 16 (:LINEAR EXPT-<-1-ONE))
 (14 14 (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (14 14 (:REWRITE DEFAULT-MOD-2))
 (13 13 (:REWRITE DEFAULT-LOGIOR-1))
 (12 12 (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (12 11 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (11 11 (:REWRITE UBYTE8-LISTP-WHEN-NOT-CONSP))
 (11 11 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (11 11 (:REWRITE |(mod x (- y))| . 3))
 (11 11 (:REWRITE |(mod x (- y))| . 2))
 (11 11 (:REWRITE |(mod x (- y))| . 1))
 (11 11 (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (11 11 (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (11 11 (:REWRITE |(mod (- x) y)| . 3))
 (11 11 (:REWRITE |(mod (- x) y)| . 2))
 (11 11 (:REWRITE |(mod (- x) y)| . 1))
 (11 11 (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (8 8 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (8 8 (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 2))
 (8 8 (:TYPE-PRESCRIPTION |(< (logior x y) 0)| . 1))
 (8 8 (:REWRITE |(* 1/2 (floor x y))| . 1))
 (7 7 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (7 7 (:REWRITE |(equal c (/ x))|))
 (7 7 (:REWRITE |(equal c (- x))|))
 (7 7 (:REWRITE |(equal (/ x) c)|))
 (7 7 (:REWRITE |(equal (/ x) (/ y))|))
 (7 7 (:REWRITE |(equal (- x) c)|))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (6 6 (:REWRITE UGLY-UNHIDE-HACK-THM-2))
 (5 5 (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (5 1 (:REWRITE |(equal (floor (+ x y) z) x)|))
 (4 4 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (4 4 (:REWRITE UBYTE16P-WHEN-MEMBER-EQUAL-OF-UBYTE16-LISTP))
 (4 4 (:REWRITE |(equal (expt 2 n) c)|))
 (3 3 (:REWRITE ASH-GOES-TO-0))
 (3 3 (:REWRITE ASH-0))
 (3 3 (:REWRITE |(floor x 2)| . 1))
 (2 2 (:REWRITE MOD-NEGATIVE . 3))
 (2 2 (:REWRITE MOD-NEGATIVE . 2))
 (2 2 (:REWRITE |(< (+ c/d x) y)|))
 (2 2 (:REWRITE |(< (+ (- c) x) y)|))
 (2 2 (:REWRITE |(+ c (+ d x))|))
 (1 1 (:TYPE-PRESCRIPTION UBYTE16P))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 5))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 4))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 3))
 (1 1 (:REWRITE |(mod (floor x y) z)| . 2))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(* a (/ a) b)|))
 )
(YUL::UBYTE16-TO-UTF8-OF-UBYTE16-FIX-CODEPOINT)
(YUL::UBYTE16-TO-UTF8-UBYTE16-EQUIV-CONGRUENCE-ON-CODEPOINT)
(YUL::EVAL-HEX-PAIR
 (4 4 (:REWRITE YUL::HEX-PAIRP-WHEN-MEMBER-EQUAL-OF-HEX-PAIR-LISTP))
 (4 4 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 )
(YUL::UBYTE8P-OF-EVAL-HEX-PAIR
 (14 9 (:REWRITE DEFAULT-*-2))
 (13 9 (:REWRITE DEFAULT-*-1))
 (11 6 (:REWRITE DEFAULT-+-2))
 (10 6 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-CDR))
 (3 1 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:TYPE-PRESCRIPTION LEN))
 (1 1 (:REWRITE DEFAULT-<-2))
 )
(YUL::EVAL-HEX-PAIR-OF-HEX-PAIR-FIX-HP)
(YUL::EVAL-HEX-PAIR-HEX-PAIR-EQUIV-CONGRUENCE-ON-HP)
(YUL::EVAL-HEX-QUAD
 (8 8 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE STR::HEX-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 )
(YUL::UBYTE16P-OF-EVAL-HEX-QUAD
 (53 23 (:REWRITE DEFAULT-+-2))
 (39 23 (:REWRITE DEFAULT-+-1))
 (30 19 (:REWRITE DEFAULT-*-2))
 (27 19 (:REWRITE DEFAULT-*-1))
 (14 14 (:REWRITE DEFAULT-CDR))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (5 1 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-2))
 )
(YUL::EVAL-HEX-QUAD-OF-HEX-QUAD-FIX-HQ
 (3 1 (:REWRITE YUL::HEX-QUAD-FIX-WHEN-HEX-QUADP))
 (2 2 (:TYPE-PRESCRIPTION YUL::HEX-QUADP))
 )
(YUL::EVAL-HEX-QUAD-HEX-QUAD-EQUIV-CONGRUENCE-ON-HQ)
(YUL::EVAL-ESCAPE)
(YUL::UBYTE8-LISTP-OF-EVAL-ESCAPE
 (32 2 (:REWRITE UBYTE8-LISTP-WHEN-NOT-CONSP))
 (4 4 (:REWRITE UBYTE8-LISTP-WHEN-SUBSETP-EQUAL))
 )
(YUL::EVAL-ESCAPE-OF-ESCAPE-FIX-ESC
 (3 1 (:REWRITE YUL::ESCAPE-FIX-WHEN-ESCAPEP))
 (2 2 (:TYPE-PRESCRIPTION YUL::ESCAPEP))
 (2 1 (:REWRITE YUL::ESCAPE-FIX-WHEN-SINGLE-QUOTE))
 (2 1 (:REWRITE YUL::ESCAPE-FIX-WHEN-LINE-FEED))
 (2 1 (:REWRITE YUL::ESCAPE-FIX-WHEN-LETTER-T))
 (2 1 (:REWRITE YUL::ESCAPE-FIX-WHEN-LETTER-R))
 (2 1 (:REWRITE YUL::ESCAPE-FIX-WHEN-LETTER-N))
 (2 1 (:REWRITE YUL::ESCAPE-FIX-WHEN-DOUBLE-QUOTE))
 (2 1 (:REWRITE YUL::ESCAPE-FIX-WHEN-CARRIAGE-RETURN))
 (2 1 (:REWRITE YUL::ESCAPE-FIX-WHEN-BACKSLASH))
 )
(YUL::EVAL-ESCAPE-ESCAPE-EQUIV-CONGRUENCE-ON-ESC)
(YUL::EVAL-STRING-ELEMENT
 (8 8 (:REWRITE YUL::STRING-ELEMENTP-WHEN-MEMBER-EQUAL-OF-STRING-ELEMENT-LISTP))
 )
(YUL::UBYTE8-LISTP-OF-EVAL-STRING-ELEMENT
 (8 2 (:REWRITE UBYTE8-LISTP-WHEN-NOT-CONSP))
 (6 3 (:REWRITE DEFAULT-CHAR-CODE))
 (6 3 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE UBYTE8-LISTP-WHEN-SUBSETP-EQUAL))
 (3 3 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE UBYTE8P-WHEN-MEMBER-EQUAL-OF-UBYTE8-LISTP))
 )
(YUL::EVAL-STRING-ELEMENT-OF-STRING-ELEMENT-FIX-ELEM
 (5 1 (:REWRITE YUL::STRING-ELEMENT-FIX-WHEN-STRING-ELEMENTP))
 (4 2 (:REWRITE DEFAULT-CHAR-CODE))
 (2 2 (:TYPE-PRESCRIPTION YUL::STRING-ELEMENTP))
 (2 2 (:TYPE-PRESCRIPTION YUL::STRING-ELEMENT-CHAR->GET$INLINE))
 (2 2 (:REWRITE YUL::STRING-ELEMENTP-WHEN-MEMBER-EQUAL-OF-STRING-ELEMENT-LISTP))
 )
(YUL::EVAL-STRING-ELEMENT-STRING-ELEMENT-EQUIV-CONGRUENCE-ON-ELEM)
(YUL::EVAL-STRING-ELEMENT-LIST
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE YUL::STRING-ELEMENT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(YUL::UBYTE8-LISTP-OF-EVAL-STRING-ELEMENT-LIST
 (32 1 (:REWRITE SUBSETP-APPEND1))
 (28 7 (:REWRITE UBYTE8-LISTP-WHEN-NOT-CONSP))
 (17 7 (:REWRITE SUBSETP-TRANS2))
 (16 5 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (14 5 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (7 7 (:REWRITE SUBSETP-TRANS))
 (6 1 (:DEFINITION BINARY-APPEND))
 (5 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(YUL::EVAL-STRING-ELEMENT-LIST-OF-STRING-ELEMENT-LIST-FIX-ELEMS
 (168 28 (:DEFINITION BINARY-APPEND))
 (137 56 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (114 13 (:REWRITE YUL::STRING-ELEMENT-LIST-FIX-WHEN-STRING-ELEMENT-LISTP))
 (109 70 (:REWRITE DEFAULT-CDR))
 (56 56 (:REWRITE DEFAULT-CAR))
 (38 38 (:REWRITE YUL::STRING-ELEMENT-LISTP-WHEN-SUBSETP-EQUAL))
 (36 6 (:REWRITE YUL::STRING-ELEMENT-LISTP-OF-CDR-WHEN-STRING-ELEMENT-LISTP))
 (20 19 (:REWRITE YUL::STRING-ELEMENT-LISTP-WHEN-NOT-CONSP))
 )
(YUL::EVAL-STRING-ELEMENT-LIST-STRING-ELEMENT-LIST-EQUIV-CONGRUENCE-ON-ELEMS)
(YUL::LEMMA1)
(YUL::LEMMA2
 (43 8 (:REWRITE UBYTE8P-OF-CAR-WHEN-UBYTE8-LISTP))
 (26 26 (:REWRITE UBYTE8-LISTP-WHEN-SUBSETP-EQUAL))
 (24 4 (:REWRITE BYTEP-WHEN-MEMBER-EQUAL-OF-BYTE-LISTP))
 (20 14 (:REWRITE BYTE-LISTP-WHEN-SUBSETP-EQUAL))
 (15 1 (:DEFINITION MEMBER-EQUAL))
 (14 2 (:REWRITE UBYTE8-LISTP-OF-CDR-WHEN-UBYTE8-LISTP))
 (14 2 (:REWRITE BYTE-LISTP-OF-CDR-WHEN-BYTE-LISTP))
 (13 13 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE SUBSETP-TRANS2))
 (7 7 (:REWRITE SUBSETP-TRANS))
 (7 7 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (5 5 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (2 2 (:REWRITE MEMBER-OF-CAR))
 (2 2 (:REWRITE BYTEP-OF-CAR-WHEN-BYTE-LISTP))
 )
(YUL::EVAL-PLAIN-STRING-LITERAL
 (161 23 (:DEFINITION LEN))
 (64 33 (:REWRITE DEFAULT-+-2))
 (39 22 (:REWRITE DEFAULT-<-2))
 (36 33 (:REWRITE DEFAULT-+-1))
 (28 2 (:REWRITE REPEAT-WHEN-ZP))
 (26 22 (:REWRITE DEFAULT-<-1))
 (26 1 (:DEFINITION EXPT))
 (25 25 (:REWRITE DEFAULT-CDR))
 (22 2 (:REWRITE ZP-OPEN))
 (14 7 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 2 (:DEFINITION BINARY-APPEND))
 (10 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (7 1 (:REWRITE ZIP-OPEN))
 (4 1 (:REWRITE COMMUTATIVITY-OF-+))
 (3 3 (:REWRITE BENDIAN=>NAT-OF-DAB-DIGIT-LIST-FIX-DIGITS-NORMALIZE-CONST))
 (3 3 (:REWRITE BENDIAN=>NAT-OF-ALL-ZEROS-CONSTANT))
 (3 1 (:REWRITE DEFAULT-*-2))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:REWRITE-QUOTED-CONSTANT DAB-BASE-FIX-UNDER-DAB-BASE-EQUIV))
 (2 2 (:REWRITE UBYTE8-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(YUL::VALUE-RESULTP-OF-EVAL-PLAIN-STRING-LITERAL)
(YUL::ERROR-INFO-WFP-OF-EVAL-PLAIN-STRING-LITERAL
 (92 4 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (80 4 (:REWRITE CONSP-OF-REPEAT))
 (60 6 (:REWRITE ZP-OPEN))
 (58 2 (:DEFINITION BINARY-APPEND))
 (36 2 (:REWRITE REPEAT-WHEN-ZP))
 (35 5 (:DEFINITION LEN))
 (29 15 (:REWRITE DEFAULT-<-2))
 (23 2 (:REWRITE FTY::RESULTERRP-WHEN-RESULTERR-OPTIONP))
 (20 1 (:REWRITE FTY::RESULTERR-OPTIONP-WHEN-RESULTERRP))
 (15 15 (:REWRITE DEFAULT-<-1))
 (14 7 (:REWRITE DEFAULT-+-2))
 (10 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (8 8 (:TYPE-PRESCRIPTION REPEAT))
 (7 7 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:TYPE-PRESCRIPTION FTY::RESULTERR-OPTIONP))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(YUL::EVAL-PLAIN-STRING-LITERAL-OF-PLAIN-STRING-FIX-PSTRING)
(YUL::EVAL-PLAIN-STRING-LITERAL-PLAIN-STRING-EQUIV-CONGRUENCE-ON-PSTRING)
(YUL::EVAL-HEX-PAIR-LIST
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE YUL::HEX-PAIR-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(YUL::UBYTE8-LISTP-OF-EVAL-HEX-PAIR-LIST
 (30 8 (:REWRITE UBYTE8-LISTP-WHEN-NOT-CONSP))
 (21 1 (:REWRITE SUBSETP-OF-CONS))
 (12 1 (:DEFINITION MEMBER-EQUAL))
 (8 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (6 6 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (5 5 (:REWRITE SUBSETP-TRANS2))
 (5 5 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE SUBSETP-MEMBER . 2))
 (2 2 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(YUL::EVAL-HEX-PAIR-LIST-OF-HEX-PAIR-LIST-FIX-HPS
 (114 13 (:REWRITE YUL::HEX-PAIR-LIST-FIX-WHEN-HEX-PAIR-LISTP))
 (85 44 (:REWRITE DEFAULT-CDR))
 (38 38 (:REWRITE YUL::HEX-PAIR-LISTP-WHEN-SUBSETP-EQUAL))
 (36 6 (:REWRITE YUL::HEX-PAIR-LISTP-OF-CDR-WHEN-HEX-PAIR-LISTP))
 (32 30 (:REWRITE DEFAULT-CAR))
 (20 19 (:REWRITE YUL::HEX-PAIR-LISTP-WHEN-NOT-CONSP))
 )
(YUL::EVAL-HEX-PAIR-LIST-HEX-PAIR-LIST-EQUIV-CONGRUENCE-ON-HPS)
(YUL::LEMMA1)
(YUL::LEMMA2
 (43 8 (:REWRITE UBYTE8P-OF-CAR-WHEN-UBYTE8-LISTP))
 (26 26 (:REWRITE UBYTE8-LISTP-WHEN-SUBSETP-EQUAL))
 (24 4 (:REWRITE BYTEP-WHEN-MEMBER-EQUAL-OF-BYTE-LISTP))
 (20 14 (:REWRITE BYTE-LISTP-WHEN-SUBSETP-EQUAL))
 (15 1 (:DEFINITION MEMBER-EQUAL))
 (14 2 (:REWRITE UBYTE8-LISTP-OF-CDR-WHEN-UBYTE8-LISTP))
 (14 2 (:REWRITE BYTE-LISTP-OF-CDR-WHEN-BYTE-LISTP))
 (13 13 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE SUBSETP-TRANS2))
 (7 7 (:REWRITE SUBSETP-TRANS))
 (7 7 (:REWRITE BYTE-LISTP-WHEN-NOT-CONSP))
 (5 5 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (2 2 (:REWRITE MEMBER-OF-CAR))
 (2 2 (:REWRITE BYTEP-OF-CAR-WHEN-BYTE-LISTP))
 )
(YUL::EVAL-HEX-STRING-LITERAL
 (161 23 (:DEFINITION LEN))
 (64 33 (:REWRITE DEFAULT-+-2))
 (39 22 (:REWRITE DEFAULT-<-2))
 (36 33 (:REWRITE DEFAULT-+-1))
 (28 2 (:REWRITE REPEAT-WHEN-ZP))
 (26 22 (:REWRITE DEFAULT-<-1))
 (26 1 (:DEFINITION EXPT))
 (25 25 (:REWRITE DEFAULT-CDR))
 (22 2 (:REWRITE ZP-OPEN))
 (14 7 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 2 (:DEFINITION BINARY-APPEND))
 (10 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (7 1 (:REWRITE ZIP-OPEN))
 (4 1 (:REWRITE COMMUTATIVITY-OF-+))
 (3 3 (:REWRITE BENDIAN=>NAT-OF-DAB-DIGIT-LIST-FIX-DIGITS-NORMALIZE-CONST))
 (3 3 (:REWRITE BENDIAN=>NAT-OF-ALL-ZEROS-CONSTANT))
 (3 1 (:REWRITE DEFAULT-*-2))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:REWRITE-QUOTED-CONSTANT DAB-BASE-FIX-UNDER-DAB-BASE-EQUIV))
 (2 2 (:REWRITE UBYTE8-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(YUL::VALUE-RESULTP-OF-EVAL-HEX-STRING-LITERAL)
(YUL::ERROR-INFO-WFP-OF-EVAL-HEX-STRING-LITERAL
 (92 4 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (80 4 (:REWRITE CONSP-OF-REPEAT))
 (60 6 (:REWRITE ZP-OPEN))
 (58 2 (:DEFINITION BINARY-APPEND))
 (36 2 (:REWRITE REPEAT-WHEN-ZP))
 (35 5 (:DEFINITION LEN))
 (29 15 (:REWRITE DEFAULT-<-2))
 (23 2 (:REWRITE FTY::RESULTERRP-WHEN-RESULTERR-OPTIONP))
 (20 1 (:REWRITE FTY::RESULTERR-OPTIONP-WHEN-RESULTERRP))
 (15 15 (:REWRITE DEFAULT-<-1))
 (14 7 (:REWRITE DEFAULT-+-2))
 (10 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (8 8 (:TYPE-PRESCRIPTION REPEAT))
 (7 7 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:TYPE-PRESCRIPTION FTY::RESULTERR-OPTIONP))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(YUL::EVAL-HEX-STRING-LITERAL-OF-HEX-STRING-FIX-HSTRING)
(YUL::EVAL-HEX-STRING-LITERAL-HEX-STRING-EQUIV-CONGRUENCE-ON-HSTRING)
(YUL::EVAL-LITERAL
 (16 16 (:REWRITE YUL::LITERALP-WHEN-MEMBER-EQUAL-OF-LITERAL-LISTP))
 )
(YUL::VALUE-RESULTP-OF-EVAL-LITERAL
 (60 1 (:REWRITE YUL::VALUE-RESULTP-WHEN-RESULTERRP))
 (42 1 (:REWRITE YUL::VALUE-RESULTP-WHEN-VALUEP))
 (18 1 (:REWRITE FTY::RESULTERRP-WHEN-RESULTERR-OPTIONP))
 (15 1 (:REWRITE FTY::RESULTERR-OPTIONP-WHEN-RESULTERRP))
 (4 1 (:REWRITE YUL::HEX-DIGIT-LIST->CHARS-WHEN-NOT-CONSP))
 (3 3 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (2 2 (:TYPE-PRESCRIPTION YUL::VALUEP))
 (2 2 (:TYPE-PRESCRIPTION FTY::RESULTERR-OPTIONP))
 )
(YUL::ERROR-INFO-WFP-OF-EVAL-LITERAL
 (47 2 (:REWRITE FTY::RESULTERRP-WHEN-RESULTERR-OPTIONP))
 (44 1 (:REWRITE FTY::RESULTERR-OPTIONP-WHEN-RESULTERRP))
 (12 3 (:REWRITE YUL::HEX-DIGIT-LIST->CHARS-WHEN-NOT-CONSP))
 (3 3 (:TYPE-PRESCRIPTION FTY::RESULTERR-OPTIONP))
 )
(YUL::EVAL-LITERAL-OF-LITERAL-FIX-LIT
 (10 1 (:REWRITE YUL::LITERAL-FIX-WHEN-LITERALP))
 (8 2 (:REWRITE YUL::HEX-DIGIT-LIST->CHARS-WHEN-NOT-CONSP))
 (5 1 (:REWRITE YUL::LITERALP-WHEN-LITERAL-OPTIONP))
 (3 3 (:TYPE-PRESCRIPTION YUL::LITERALP))
 (2 2 (:TYPE-PRESCRIPTION YUL::LITERAL-OPTIONP))
 (2 2 (:REWRITE YUL::LITERALP-WHEN-MEMBER-EQUAL-OF-LITERAL-LISTP))
 (2 1 (:REWRITE YUL::LITERAL-OPTIONP-WHEN-LITERALP))
 )
(YUL::EVAL-LITERAL-LITERAL-EQUIV-CONGRUENCE-ON-LIT)
