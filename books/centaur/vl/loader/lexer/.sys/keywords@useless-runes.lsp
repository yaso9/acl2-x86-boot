(VL::VL-MAKE-KEYWORD-TABLE
 (100 1 (:REWRITE VL::STRINGP-WHEN-TRUE-LISTP))
 (34 1 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (31 2 (:REWRITE VL::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (22 1 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (18 1 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (15 1 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE))
 (14 14 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (14 14 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (13 1 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (12 1 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (9 9 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (9 2 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (8 1 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (8 1 (:REWRITE MEMBER-WHEN-ATOM))
 (6 2 (:REWRITE VL::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (6 1 (:REWRITE VL::TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (5 5 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (5 1 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (5 1 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (4 4 (:REWRITE VL::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (4 1 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (3 3 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE CONSP-BY-LEN))
 (3 3 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (3 2 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (2 2 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (2 2 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (2 2 (:TYPE-PRESCRIPTION ALISTP))
 (2 2 (:REWRITE VL::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (2 2 (:REWRITE VL::TRUE-LIST-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE VL::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (2 2 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (2 2 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (2 2 (:REWRITE FN-CHECK-DEF-FORMALS))
 (2 2 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (2 1 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (2 1 (:REWRITE VL::SYMBOL-LISTP-OF-CAR-WHEN-SYMBOL-LIST-LISTP))
 (2 1 (:REWRITE VL::STRING-LISTP-OF-CAR-WHEN-STRING-LIST-LISTP))
 (2 1 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (2 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 1 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (2 1 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (2 1 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (2 1 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LISTP))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LISTP))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (1 1 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL::MAYBE-STRING-FIX-UNDER-MAYBE-STRING-EQUIV))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (1 1 (:REWRITE VL::TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (1 1 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (1 1 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE SUBSETP-MEMBER . 4))
 (1 1 (:REWRITE SUBSETP-MEMBER . 3))
 (1 1 (:REWRITE SUBSETP-MEMBER . 2))
 (1 1 (:REWRITE SUBSETP-MEMBER . 1))
 (1 1 (:REWRITE INTERSECTP-MEMBER . 3))
 (1 1 (:REWRITE INTERSECTP-MEMBER . 2))
 (1 1 (:REWRITE SET::IN-SET))
 (1 1 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE ALISTP-WHEN-ATOM))
 (1 1 (:REWRITE VL::ALISTP-WHEN-ALL-HAVE-LEN))
 )
(VL::VL-FULL-KEYWORD-TABLE)
(VL::SYMBOL-LISTP-OF-ALIST-VALS-OF-VL-FULL-KEYWORD-TABLE)
(VL::SYMBOLP-OF-LOOKUP-IN-VL-FULL-KEYWORD-TABLE
 (1984 248 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (496 496 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (496 248 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (496 248 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (248 248 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (248 248 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (248 248 (:REWRITE SET::IN-SET))
 (248 248 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (248 248 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (11 2 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LISTP))
 (8 1 (:REWRITE DEFAULT-CDR))
 (3 1 (:REWRITE VL::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-VALS))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (2 1 (:REWRITE MEMBER-EQUAL-OF-ALIST-VALS-UNDER-IFF))
 (2 1 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION HONS-RASSOC-EQUAL-TYPE))
 (1 1 (:REWRITE VL::SYMBOL-LISTP-OF-ALIST-VALS-OF-VL-FULL-KEYWORD-TABLE))
 (1 1 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (1 1 (:REWRITE CONSP-BY-LEN))
 )
(VL::VL-KEYWORD-TABLE-P)
(VL::VL-KEYWORD-TABLE-P-OF-VL-FULL-KEYWORD-TABLE)
(VL::SYMBOL-LISTP-OF-ALIST-VALS-WHEN-VL-KEYWORD-TABLE-P
 (328 152 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (286 11 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (282 76 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (243 25 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (171 9 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (169 13 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (153 25 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (152 152 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (105 2 (:REWRITE SUBSETP-OF-CONS))
 (101 10 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (99 9 (:REWRITE BOOLEAN-LISTP-WHEN-NOT-CONSP))
 (95 29 (:REWRITE MEMBER-EQUAL-OF-ALIST-VALS-UNDER-IFF))
 (90 9 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (88 11 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (84 31 (:REWRITE VL::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (65 13 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (65 13 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (63 63 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (54 54 (:REWRITE DEFAULT-CAR))
 (54 54 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (52 13 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (44 2 (:REWRITE ALISTP-OF-CDR))
 (39 1 (:REWRITE HONS-RASSOC-EQUAL-OF-CDR-WHEN-HONS-ASSOC-EQUAL-AND-NO-DUPLICATES))
 (33 33 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (33 33 (:REWRITE CONSP-BY-LEN))
 (31 31 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (30 30 (:TYPE-PRESCRIPTION HONS-RASSOC-EQUAL-TYPE))
 (29 29 (:REWRITE SUBSETP-TRANS2))
 (29 29 (:REWRITE SUBSETP-TRANS))
 (28 14 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (27 27 (:TYPE-PRESCRIPTION VL::VL-FULL-KEYWORD-TABLE))
 (26 26 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (26 26 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (26 26 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (26 26 (:TYPE-PRESCRIPTION ALISTP))
 (26 13 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (26 13 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (22 22 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (22 11 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (22 11 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (22 11 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (22 11 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (20 1 (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-ATOM))
 (19 19 (:REWRITE VL::SYMBOL-LISTP-OF-ALIST-VALS-OF-VL-FULL-KEYWORD-TABLE))
 (18 18 (:REWRITE VL::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (18 18 (:REWRITE BOOLEAN-LISTP-WHEN-SUBSETP-EQUAL))
 (15 13 (:REWRITE DEFAULT-CDR))
 (13 13 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (13 13 (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
 (13 13 (:REWRITE ALISTP-WHEN-ATOM))
 (13 13 (:REWRITE VL::ALISTP-WHEN-ALL-HAVE-LEN))
 (12 1 (:REWRITE NO-DUPLICATESP-EQUAL-NON-CONS))
 (11 11 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (11 11 (:REWRITE SET::IN-SET))
 (11 11 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (11 11 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (10 10 (:REWRITE FN-CHECK-DEF-FORMALS))
 (9 9 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (8 8 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (2 2 (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
 (2 2 (:REWRITE SUBSETP-MEMBER . 2))
 (2 2 (:REWRITE SUBSETP-MEMBER . 1))
 (1 1 (:REWRITE NO-DUPLICATESP-EQUAL-WHEN-DUPLICITY-BADGUY1))
 (1 1 (:REWRITE HONS-RASSOC-EQUAL-OF-CDR-WHEN-HONS-ASSOC-EQUAL))
 )
(VL::SYMBOLP-OF-LOOKUP-WHEN-VL-KEYWORD-TABLE-P
 (891 9 (:REWRITE VL::SYMBOLP-OF-CDR-HONS-ASSOC-EQUAL-WHEN-SYMBOL-LISTP-OF-STRIP-CDRS))
 (390 100 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (315 18 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (286 11 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (216 9 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (200 200 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (200 200 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (169 13 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (166 20 (:REWRITE DEFAULT-CDR))
 (162 162 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (162 27 (:REWRITE STRIP-CDRS-UNDER-IFF))
 (153 18 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (144 9 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (144 9 (:REWRITE BOOLEAN-LISTP-WHEN-NOT-CONSP))
 (130 20 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LISTP))
 (117 18 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (96 12 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (72 9 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (65 13 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (65 13 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (64 64 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (64 64 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (64 64 (:REWRITE CONSP-BY-LEN))
 (56 56 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-VALS))
 (55 55 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (54 54 (:REWRITE DEFAULT-CAR))
 (54 9 (:REWRITE STRIP-CDRS-WHEN-ATOM))
 (52 13 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (45 9 (:REWRITE CONSP-OF-HONS-ASSOC-EQUAL))
 (44 2 (:REWRITE ALISTP-OF-CDR))
 (40 10 (:REWRITE VL::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (36 36 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (28 28 (:REWRITE VL::SYMBOL-LISTP-OF-ALIST-VALS-OF-VL-FULL-KEYWORD-TABLE))
 (26 26 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (26 26 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (26 26 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (26 26 (:TYPE-PRESCRIPTION ALISTP))
 (26 13 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (26 13 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (24 24 (:TYPE-PRESCRIPTION VL::VL-FULL-KEYWORD-TABLE))
 (24 24 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (24 12 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (24 12 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (22 11 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (22 11 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (20 10 (:REWRITE MEMBER-EQUAL-OF-ALIST-VALS-UNDER-IFF))
 (18 18 (:REWRITE VL::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (18 18 (:REWRITE SUBSETP-TRANS2))
 (18 18 (:REWRITE SUBSETP-TRANS))
 (18 18 (:REWRITE BOOLEAN-LISTP-WHEN-SUBSETP-EQUAL))
 (18 9 (:REWRITE ALIST-VALS-WHEN-ATOM))
 (17 17 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (13 13 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (13 13 (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
 (13 13 (:REWRITE ALISTP-WHEN-ATOM))
 (13 13 (:REWRITE VL::ALISTP-WHEN-ALL-HAVE-LEN))
 (12 12 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (12 12 (:REWRITE SET::IN-SET))
 (12 12 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (12 12 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (10 10 (:TYPE-PRESCRIPTION HONS-RASSOC-EQUAL-TYPE))
 (10 10 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (9 9 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (9 9 (:REWRITE FN-CHECK-DEF-FORMALS))
 )
(VL::VL-KEYWORD-LOOKUP$INLINE)
(VL::SYMBOLP-OF-VL-KEYWORD-LOOKUP
 (16 1 (:REWRITE DEFAULT-CDR))
 (9 2 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (5 2 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (5 1 (:REWRITE CONSP-OF-HONS-ASSOC-EQUAL))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:REWRITE CONSP-BY-LEN))
 )
