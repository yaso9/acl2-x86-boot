(RP::BINARY-SUM)
(RP::INTEGERP-OF-BINARY-SUM)
(RP::--)
(RP::SUM-LIST)
(RP::INTEGERP-OF-SUM-LIST)
(RP::S)
(RP::INTEGERP-OF-S (54 2
                       (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
                   (20 9 (:REWRITE DEFAULT-+-2))
                   (14 5 (:REWRITE DEFAULT-UNARY-MINUS))
                   (13 9 (:REWRITE DEFAULT-+-1))
                   (12 2 (:DEFINITION NFIX))
                   (11 4 (:REWRITE DEFAULT-*-2))
                   (11 4 (:REWRITE DEFAULT-*-1))
                   (8 5 (:REWRITE DEFAULT-<-1))
                   (7 5 (:REWRITE DEFAULT-<-2))
                   (5 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                   (5 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                   (2 2
                      (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                   (2 2 (:DEFINITION IFIX))
                   (2 1 (:REWRITE DEFAULT-NUMERATOR))
                   (2 1 (:REWRITE DEFAULT-DENOMINATOR)))
(RP::C)
(RP::INTEGERP-OF-C)
(RP::D-SUM)
(RP::INTEGERP-OF-D-SUM)
(RP::D)
(RP::INTEGERP-OF-D)
(RP::S-SPEC)
(RP::INTEGERP-OF-S-SPEC (54 2
                            (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
                        (20 9 (:REWRITE DEFAULT-+-2))
                        (14 5 (:REWRITE DEFAULT-UNARY-MINUS))
                        (13 9 (:REWRITE DEFAULT-+-1))
                        (12 2 (:DEFINITION NFIX))
                        (11 4 (:REWRITE DEFAULT-*-2))
                        (11 4 (:REWRITE DEFAULT-*-1))
                        (8 5 (:REWRITE DEFAULT-<-1))
                        (7 5 (:REWRITE DEFAULT-<-2))
                        (5 1 (:REWRITE INTEGERP==>NUMERATOR-=-X))
                        (5 1 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
                        (2 2
                           (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                        (2 2 (:DEFINITION IFIX))
                        (2 1 (:REWRITE DEFAULT-NUMERATOR))
                        (2 1 (:REWRITE DEFAULT-DENOMINATOR)))
(RP::C-SPEC)
(RP::INTEGERP-OF-C-SPEC)
(RP::S-C-SPEC)
(RP::C-S-SPEC)
(RP::C-RES)
(RP::INTEGERP-OF-C-RES)
(RP::BIT-FIX)
(RP::BIT-FIX-OPENER)
(RP::BINARY-NOT)
(RP::NATP-BITP-BINARY-NOT)
(RP::BINARY-AND)
(RP::BITP-BINARY-AND)
(RP::AND-LIST)
(RP::BINARY-OR)
(RP::BITP-BINARY-OR)
(RP::BINARY-XOR)
(RP::BITP-BINARY-XOR)
(RP::BINARY-?)
(RP::NATP-BITP-BINARY-?*)
(RP::BINARY-COND-MACRO (8 2 (:REWRITE O-P-O-INFP-CAR))
                       (6 6 (:REWRITE DEFAULT-CAR))
                       (5 1 (:DEFINITION LEN))
                       (4 4 (:REWRITE DEFAULT-CDR))
                       (3 3
                          (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
                       (2 2 (:REWRITE O-P-DEF-O-FINP-1))
                       (2 1 (:REWRITE DEFAULT-<-1))
                       (2 1 (:REWRITE DEFAULT-+-2))
                       (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
                       (1 1 (:REWRITE DEFAULT-<-2))
                       (1 1 (:REWRITE DEFAULT-+-1)))
(RP::SORT-SUM)
(RP::S-OF-C-TRIG (1 1 (:TYPE-PRESCRIPTION RP::S-OF-C-TRIG)))
(RP::EVENPI)
(RP::SMALL-ALPHORDER)
(RP::SMALL-ALPHORDER-SANITY (20 6 (:REWRITE SYMBOL-<-TRICHOTOMY))
                            (6 6 (:REWRITE SYMBOL-<-TRANSITIVE))
                            (3 3
                               (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
                            (2 2
                               (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
                            (2 2 (:REWRITE DEFAULT-<-2))
                            (2 2 (:REWRITE DEFAULT-<-1)))
(RP::LEXORDER2 (296 5 (:REWRITE O<=-O-FINP-DEF))
               (242 152 (:REWRITE RP::MEASURE-LEMMA1))
               (150 10 (:DEFINITION RP::EX-FROM-RP))
               (84 24 (:REWRITE DEFAULT-CDR))
               (68 4 (:REWRITE RP::MEASURE-LEMMA6-5))
               (68 4 (:REWRITE RP::MEASURE-LEMMA6))
               (60 20 (:REWRITE DEFAULT-CAR))
               (48 48 (:REWRITE RP::MEASURE-LEMMA1-2))
               (44 22 (:REWRITE DEFAULT-<-2))
               (44 22 (:REWRITE DEFAULT-<-1))
               (23 12 (:REWRITE DEFAULT-+-2))
               (23 5 (:REWRITE AC-<))
               (22 22
                   (:REWRITE RP::EQUALITY-MEASURE-LEMMA3))
               (22 22
                   (:REWRITE RP::EQUALITY-MEASURE-LEMMA1))
               (22 12 (:REWRITE DEFAULT-+-1))
               (16 4 (:REWRITE O-P-O-INFP-CAR))
               (14 14
                   (:REWRITE RP::EQUALITY-MEASURE-LEMMA2))
               (13 5 (:REWRITE O-INFP-O-FINP-O<=))
               (10 10
                   (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
               (5 5
                  (:REWRITE |a < b & b < c  =>  a < c|)))
(RP::LEXORDER2-SANITY-LEMMA1 (84 48 (:REWRITE RP::MEASURE-LEMMA1))
                             (60 4 (:DEFINITION RP::EX-FROM-RP))
                             (42 18 (:REWRITE DEFAULT-CDR))
                             (26 10 (:REWRITE DEFAULT-CAR))
                             (16 16 (:REWRITE RP::MEASURE-LEMMA1-2))
                             (4 4
                                (:TYPE-PRESCRIPTION RP::IS-RP$INLINE)))
(RP::LEXORDER2-SANITY-LEMMA2 (672 384 (:REWRITE RP::MEASURE-LEMMA1))
                             (480 32 (:DEFINITION RP::EX-FROM-RP))
                             (272 80 (:REWRITE DEFAULT-CDR))
                             (208 80 (:REWRITE DEFAULT-CAR))
                             (128 128 (:REWRITE RP::MEASURE-LEMMA1-2))
                             (32 32
                                 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                             (15 5 (:REWRITE RP::SMALL-ALPHORDER-SANITY))
                             (10 10
                                 (:TYPE-PRESCRIPTION RP::SMALL-ALPHORDER)))
(RP::LEXORDER2-SANITY-LEMMA3 (672 384 (:REWRITE RP::MEASURE-LEMMA1))
                             (480 32 (:DEFINITION RP::EX-FROM-RP))
                             (272 80 (:REWRITE DEFAULT-CDR))
                             (208 80 (:REWRITE DEFAULT-CAR))
                             (128 128 (:REWRITE RP::MEASURE-LEMMA1-2))
                             (32 32
                                 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
                             (15 5 (:REWRITE RP::SMALL-ALPHORDER-SANITY))
                             (10 10
                                 (:TYPE-PRESCRIPTION RP::SMALL-ALPHORDER)))
(RP::LEXORDER2-SANITY (9566 3804 (:REWRITE RP::MEASURE-LEMMA1))
                      (7437 67 (:DEFINITION RP::EX-FROM-RP))
                      (7169 67 (:DEFINITION RP::IS-RP$INLINE))
                      (5210 2396 (:REWRITE RP::MEASURE-LEMMA1-2))
                      (4526 2188 (:REWRITE DEFAULT-CDR))
                      (2723 1131 (:REWRITE DEFAULT-CAR))
                      (276 69 (:REWRITE O-P-O-INFP-CAR))
                      (134 134 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
                      (73 73
                          (:REWRITE RP::LEXORDER2-SANITY-LEMMA1))
                      (69 69 (:REWRITE O-P-DEF-O-FINP-1))
                      (67 67
                          (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP)))
(RP::ADDER-B+)
(RP::BIT-OF)
(RP::BITP-OF-BIT-OF)
(RP::S-SPEC-OPENER-ERROR)
(RP::C-SPEC-OPENER-ERROR)
(RP::S-C-SPEC-OPENER-ERROR)
(RP::C-S-SPEC-OPENER-ERROR)
(RP::SORT-SUM-OPENER-ERROR)
(RP::M2)
(RP::F2)
(RP::D2)
(RP::TIMES2)
(RP::QUARTERNARYP$INLINE)
(RP::BA2)
(RP::BITP-BA2)
(RP::BA3)
(RP::BITP-BA3)
(RP::BA4)
(RP::BITP-BA4)
