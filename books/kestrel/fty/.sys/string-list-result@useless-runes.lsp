(STRING-LIST-RESULTP)
(CONSP-WHEN-STRING-LIST-RESULTP)
(STRING-LIST-RESULT-KIND$INLINE)
(STRING-LIST-RESULT-KIND-POSSIBILITIES)
(STRING-LIST-RESULT-FIX$INLINE)
(STRING-LIST-RESULTP-OF-STRING-LIST-RESULT-FIX
 (24 8 (:REWRITE STR::STRING-LIST-FIX-WHEN-STRING-LISTP))
 (16 4 (:DEFINITION STR::STRING-LIST-FIX))
 (13 1 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (13 1 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (6 6 (:TYPE-PRESCRIPTION STRIP-CARS))
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 1 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (5 1 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 1 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (2 2 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (2 1 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (2 1 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 )
(STRING-LIST-RESULT-FIX-WHEN-STRING-LIST-RESULTP
 (39 3 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (17 17 (:REWRITE DEFAULT-CDR))
 (15 3 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (15 3 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (13 13 (:REWRITE DEFAULT-CAR))
 (12 12 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (6 6 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (6 6 (:TYPE-PRESCRIPTION IDENTITY))
 (6 6 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (6 3 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (6 3 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (4 1 (:DEFINITION STR::STRING-LIST-FIX))
 )
(STRING-LIST-RESULT-FIX$INLINE
 (39 3 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (17 17 (:REWRITE DEFAULT-CDR))
 (15 3 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (15 3 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (13 13 (:REWRITE DEFAULT-CAR))
 (12 12 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (6 6 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (6 6 (:TYPE-PRESCRIPTION IDENTITY))
 (6 6 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (6 3 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (6 3 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (4 1 (:DEFINITION STR::STRING-LIST-FIX))
 (2 2 (:DEFINITION STRIP-CARS))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(STRING-LIST-RESULT-EQUIV$INLINE)
(STRING-LIST-RESULT-EQUIV-IS-AN-EQUIVALENCE)
(STRING-LIST-RESULT-EQUIV-IMPLIES-EQUAL-STRING-LIST-RESULT-FIX-1)
(STRING-LIST-RESULT-FIX-UNDER-STRING-LIST-RESULT-EQUIV)
(EQUAL-OF-STRING-LIST-RESULT-FIX-1-FORWARD-TO-STRING-LIST-RESULT-EQUIV)
(EQUAL-OF-STRING-LIST-RESULT-FIX-2-FORWARD-TO-STRING-LIST-RESULT-EQUIV)
(STRING-LIST-RESULT-EQUIV-OF-STRING-LIST-RESULT-FIX-1-FORWARD)
(STRING-LIST-RESULT-EQUIV-OF-STRING-LIST-RESULT-FIX-2-FORWARD)
(STRING-LIST-RESULT-KIND$INLINE-OF-STRING-LIST-RESULT-FIX-X
 (7 7 (:REWRITE DEFAULT-CAR))
 (5 1 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (4 1 (:DEFINITION FTY::RESULTERRP))
 (2 2 (:DEFINITION STRIP-CARS))
 (2 1 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (2 1 (:DEFINITION STR::STRING-LIST-FIX))
 (1 1 (:REWRITE STRING-LIST-RESULT-FIX-WHEN-STRING-LIST-RESULTP))
 )
(STRING-LIST-RESULT-KIND$INLINE-STRING-LIST-RESULT-EQUIV-CONGRUENCE-ON-X)
(STRING-LIST-RESULT-OK->GET$INLINE)
(STRING-LISTP-OF-STRING-LIST-RESULT-OK->GET
 (6 2 (:REWRITE STR::STRING-LIST-FIX-WHEN-STRING-LISTP))
 (6 1 (:DEFINITION STR::STRING-LIST-FIX))
 )
(STRING-LIST-RESULT-OK->GET$INLINE-OF-STRING-LIST-RESULT-FIX-X
 (34 6 (:DEFINITION STR::STRING-LIST-FIX))
 (12 4 (:REWRITE STRING-LIST-RESULT-FIX-WHEN-STRING-LIST-RESULTP))
 (8 8 (:TYPE-PRESCRIPTION STRING-LIST-RESULTP))
 (6 6 (:TYPE-PRESCRIPTION STRING-LIST-RESULT-FIX$INLINE))
 )
(STRING-LIST-RESULT-OK->GET$INLINE-STRING-LIST-RESULT-EQUIV-CONGRUENCE-ON-X)
(STRING-LIST-RESULT-OK->GET-WHEN-WRONG-KIND
 (6 2 (:REWRITE STR::STRING-LIST-FIX-WHEN-STRING-LISTP))
 (4 4 (:TYPE-PRESCRIPTION STRING-LISTP))
 )
(STRING-LIST-RESULT-OK)
(RETURN-TYPE-OF-STRING-LIST-RESULT-OK
 (12 4 (:REWRITE STR::STRING-LIST-FIX-WHEN-STRING-LISTP))
 (8 2 (:DEFINITION STR::STRING-LIST-FIX))
 )
(STRING-LIST-RESULT-OK->GET-OF-STRING-LIST-RESULT-OK
 (38 8 (:DEFINITION STR::STRING-LIST-FIX))
 (6 6 (:TYPE-PRESCRIPTION STRING-LIST-RESULT-OK))
 )
(STRING-LIST-RESULT-OK-OF-FIELDS
 (8 2 (:DEFINITION STR::STRING-LIST-FIX))
 (3 1 (:REWRITE STRING-LIST-RESULT-FIX-WHEN-STRING-LIST-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION STRING-LIST-RESULTP))
 )
(STRING-LIST-RESULT-FIX-WHEN-OK
 (8 2 (:DEFINITION STR::STRING-LIST-FIX))
 (3 1 (:REWRITE STRING-LIST-RESULT-FIX-WHEN-STRING-LIST-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION STRING-LIST-RESULTP))
 )
(EQUAL-OF-STRING-LIST-RESULT-OK
 (32 16 (:DEFINITION STR::STRING-LIST-FIX))
 )
(STRING-LIST-RESULT-OK-OF-STRING-LIST-FIX-GET
 (8 2 (:DEFINITION STR::STRING-LIST-FIX))
 )
(STRING-LIST-RESULT-OK-STRING-LIST-EQUIV-CONGRUENCE-ON-GET)
(STRING-LIST-RESULT-ERR->GET$INLINE
 (39 3 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (17 17 (:REWRITE DEFAULT-CDR))
 (15 3 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (15 3 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (13 13 (:REWRITE DEFAULT-CAR))
 (12 12 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (6 6 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (6 6 (:TYPE-PRESCRIPTION IDENTITY))
 (6 6 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (6 3 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (6 3 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (2 2 (:DEFINITION STRIP-CARS))
 )
(RESULTERRP-OF-STRING-LIST-RESULT-ERR->GET
 (63 3 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (15 3 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (13 1 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (5 1 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (5 1 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (2 2 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (2 1 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 )
(STRING-LIST-RESULT-ERR->GET$INLINE-OF-STRING-LIST-RESULT-FIX-X
 (62 3 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (56 3 (:DEFINITION FTY::RESULTERRP))
 (40 30 (:TYPE-PRESCRIPTION IDENTITY))
 (20 20 (:TYPE-PRESCRIPTION STRIP-CARS))
 (15 3 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (13 13 (:TYPE-PRESCRIPTION STRING-LIST-RESULT-FIX$INLINE))
 (12 4 (:REWRITE STRING-LIST-RESULT-FIX-WHEN-STRING-LIST-RESULTP))
 (8 8 (:TYPE-PRESCRIPTION STRING-LIST-RESULTP))
 (6 6 (:DEFINITION STRIP-CARS))
 (3 3 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (3 3 (:TYPE-PRESCRIPTION ALISTP))
 )
(STRING-LIST-RESULT-ERR->GET$INLINE-STRING-LIST-RESULT-EQUIV-CONGRUENCE-ON-X)
(STRING-LIST-RESULT-ERR->GET-WHEN-WRONG-KIND
 (3 1 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (1 1 (:DEFINITION FTY::RESULTERRP))
 )
(STRING-LIST-RESULT-ERR
 (39 3 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (17 17 (:REWRITE DEFAULT-CDR))
 (15 3 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (15 3 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (12 12 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (12 12 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (6 6 (:TYPE-PRESCRIPTION IDENTITY))
 (6 6 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (6 3 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (6 3 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (2 2 (:DEFINITION STRIP-CARS))
 )
(RETURN-TYPE-OF-STRING-LIST-RESULT-ERR
 (13 1 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (7 7 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (5 1 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (5 1 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (2 2 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (2 1 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (2 1 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 )
(STRING-LIST-RESULT-ERR->GET-OF-STRING-LIST-RESULT-ERR
 (30 24 (:TYPE-PRESCRIPTION IDENTITY))
 (23 1 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (21 1 (:DEFINITION FTY::RESULTERRP))
 (16 16 (:TYPE-PRESCRIPTION STRING-LIST-RESULT-ERR))
 (6 6 (:TYPE-PRESCRIPTION STRIP-CARS))
 (6 1 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (2 2 (:DEFINITION STRIP-CARS))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (1 1 (:TYPE-PRESCRIPTION ALISTP))
 )
(STRING-LIST-RESULT-ERR-OF-FIELDS
 (26 2 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (22 2 (:DEFINITION FTY::RESULTERRP))
 (18 18 (:TYPE-PRESCRIPTION IDENTITY))
 (12 12 (:TYPE-PRESCRIPTION STRIP-CARS))
 (8 2 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (4 4 (:DEFINITION STRIP-CARS))
 (3 1 (:REWRITE STRING-LIST-RESULT-FIX-WHEN-STRING-LIST-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION STRING-LIST-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (2 2 (:TYPE-PRESCRIPTION ALISTP))
 )
(STRING-LIST-RESULT-FIX-WHEN-ERR
 (18 18 (:TYPE-PRESCRIPTION IDENTITY))
 (14 2 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (11 1 (:DEFINITION FTY::RESULTERRP))
 (6 6 (:TYPE-PRESCRIPTION STRIP-CARS))
 (4 1 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (3 1 (:REWRITE STRING-LIST-RESULT-FIX-WHEN-STRING-LIST-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION STRING-LIST-RESULTP))
 (2 2 (:DEFINITION STRIP-CARS))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (1 1 (:TYPE-PRESCRIPTION ALISTP))
 )
(EQUAL-OF-STRING-LIST-RESULT-ERR
 (152 6 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (134 6 (:DEFINITION FTY::RESULTERRP))
 (52 4 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (38 2 (:DEFINITION ALISTP))
 (30 6 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (24 12 (:DEFINITION STRIP-CARS))
 (23 23 (:REWRITE DEFAULT-CAR))
 (22 22 (:REWRITE DEFAULT-CDR))
 (20 4 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (20 4 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (16 16 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (12 12 (:TYPE-PRESCRIPTION STRIP-CARS))
 (10 2 (:REWRITE FTY::RESULTERRP-WHEN-RESULTERR-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (8 8 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (8 4 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (8 4 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (4 4 (:TYPE-PRESCRIPTION FTY::RESULTERR-OPTIONP))
 (4 2 (:REWRITE FTY::RESULTERR-OPTIONP-WHEN-RESULTERRP))
 )
(STRING-LIST-RESULT-ERR-OF-RESULTERR-FIX-GET
 (12 12 (:TYPE-PRESCRIPTION IDENTITY))
 )
(STRING-LIST-RESULT-ERR-RESULTERR-EQUIV-CONGRUENCE-ON-GET)
(STRING-LIST-RESULT-FIX-REDEF
 (9 3 (:REWRITE STRING-LIST-RESULT-FIX-WHEN-STRING-LIST-RESULTP))
 (6 6 (:TYPE-PRESCRIPTION STRING-LIST-RESULTP))
 )
(STRING-LIST-RESULTP-WHEN-STRING-LISTP)
(STRING-LIST-RESULTP-WHEN-RESULTERRP)
(STRING-LISTP-WHEN-STRING-LIST-RESULTP-AND-NOT-RESULTERRP)
