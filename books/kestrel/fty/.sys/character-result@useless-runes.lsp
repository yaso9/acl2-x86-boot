(TMP-DEFTYPES-CHARACTERP-OF-CHAR-FIX$INLINE)
(CHARACTER-RESULTP)
(CONSP-WHEN-CHARACTER-RESULTP)
(CHARACTER-RESULT-KIND$INLINE)
(CHARACTER-RESULT-KIND-POSSIBILITIES)
(CHARACTER-RESULT-FIX$INLINE)
(CHARACTER-RESULTP-OF-CHARACTER-RESULT-FIX
 (13 1 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (13 1 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (6 6 (:TYPE-PRESCRIPTION STRIP-CARS))
 (5 1 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (5 1 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (4 1 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (2 2 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (2 1 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (1 1 (:REWRITE CHAR-FIX-WHEN-CHARACTERP))
 )
(CHARACTER-RESULT-FIX-WHEN-CHARACTER-RESULTP)
(CHARACTER-RESULT-FIX$INLINE
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
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(CHARACTER-RESULT-EQUIV$INLINE)
(CHARACTER-RESULT-EQUIV-IS-AN-EQUIVALENCE)
(CHARACTER-RESULT-EQUIV-IMPLIES-EQUAL-CHARACTER-RESULT-FIX-1)
(CHARACTER-RESULT-FIX-UNDER-CHARACTER-RESULT-EQUIV)
(EQUAL-OF-CHARACTER-RESULT-FIX-1-FORWARD-TO-CHARACTER-RESULT-EQUIV)
(EQUAL-OF-CHARACTER-RESULT-FIX-2-FORWARD-TO-CHARACTER-RESULT-EQUIV)
(CHARACTER-RESULT-EQUIV-OF-CHARACTER-RESULT-FIX-1-FORWARD)
(CHARACTER-RESULT-EQUIV-OF-CHARACTER-RESULT-FIX-2-FORWARD)
(CHARACTER-RESULT-KIND$INLINE-OF-CHARACTER-RESULT-FIX-X
 (5 1 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (4 1 (:DEFINITION FTY::RESULTERRP))
 (2 2 (:DEFINITION STRIP-CARS))
 (2 1 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (1 1 (:REWRITE CHARACTER-RESULT-FIX-WHEN-CHARACTER-RESULTP))
 )
(CHARACTER-RESULT-KIND$INLINE-CHARACTER-RESULT-EQUIV-CONGRUENCE-ON-X)
(CHARACTER-RESULT-OK->GET$INLINE)
(CHARACTERP-OF-CHARACTER-RESULT-OK->GET)
(CHARACTER-RESULT-OK->GET$INLINE-OF-CHARACTER-RESULT-FIX-X
 (45 15 (:REWRITE CHARACTER-RESULT-FIX-WHEN-CHARACTER-RESULTP))
 (30 30 (:TYPE-PRESCRIPTION CHARACTER-RESULTP))
 )
(CHARACTER-RESULT-OK->GET$INLINE-CHARACTER-RESULT-EQUIV-CONGRUENCE-ON-X)
(CHARACTER-RESULT-OK->GET-WHEN-WRONG-KIND
 (2 2 (:REWRITE CHAR-FIX-WHEN-CHARACTERP))
 )
(CHARACTER-RESULT-OK)
(RETURN-TYPE-OF-CHARACTER-RESULT-OK
 (1 1 (:REWRITE CHAR-FIX-WHEN-CHARACTERP))
 )
(CHARACTER-RESULT-OK->GET-OF-CHARACTER-RESULT-OK)
(CHARACTER-RESULT-OK-OF-FIELDS
 (3 1 (:REWRITE CHARACTER-RESULT-FIX-WHEN-CHARACTER-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION CHARACTER-RESULTP))
 )
(CHARACTER-RESULT-FIX-WHEN-OK
 (3 1 (:REWRITE CHARACTER-RESULT-FIX-WHEN-CHARACTER-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION CHARACTER-RESULTP))
 )
(EQUAL-OF-CHARACTER-RESULT-OK)
(CHARACTER-RESULT-OK-OF-CHAR-FIX-GET)
(CHARACTER-RESULT-OK-CHAREQV-CONGRUENCE-ON-GET)
(CHARACTER-RESULT-ERR->GET$INLINE
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
(RESULTERRP-OF-CHARACTER-RESULT-ERR->GET
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
(CHARACTER-RESULT-ERR->GET$INLINE-OF-CHARACTER-RESULT-FIX-X
 (62 3 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (56 3 (:DEFINITION FTY::RESULTERRP))
 (40 30 (:TYPE-PRESCRIPTION IDENTITY))
 (20 20 (:TYPE-PRESCRIPTION STRIP-CARS))
 (15 3 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (13 13 (:TYPE-PRESCRIPTION CHARACTER-RESULT-FIX$INLINE))
 (12 4 (:REWRITE CHARACTER-RESULT-FIX-WHEN-CHARACTER-RESULTP))
 (8 8 (:TYPE-PRESCRIPTION CHARACTER-RESULTP))
 (6 6 (:DEFINITION STRIP-CARS))
 (3 3 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (3 3 (:TYPE-PRESCRIPTION ALISTP))
 )
(CHARACTER-RESULT-ERR->GET$INLINE-CHARACTER-RESULT-EQUIV-CONGRUENCE-ON-X)
(CHARACTER-RESULT-ERR->GET-WHEN-WRONG-KIND
 (3 1 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (1 1 (:DEFINITION FTY::RESULTERRP))
 )
(CHARACTER-RESULT-ERR
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
(RETURN-TYPE-OF-CHARACTER-RESULT-ERR
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
(CHARACTER-RESULT-ERR->GET-OF-CHARACTER-RESULT-ERR
 (30 24 (:TYPE-PRESCRIPTION IDENTITY))
 (23 1 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (21 1 (:DEFINITION FTY::RESULTERRP))
 (16 16 (:TYPE-PRESCRIPTION CHARACTER-RESULT-ERR))
 (6 6 (:TYPE-PRESCRIPTION STRIP-CARS))
 (6 1 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (2 2 (:DEFINITION STRIP-CARS))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (1 1 (:TYPE-PRESCRIPTION ALISTP))
 )
(CHARACTER-RESULT-ERR-OF-FIELDS
 (26 2 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (22 2 (:DEFINITION FTY::RESULTERRP))
 (18 18 (:TYPE-PRESCRIPTION IDENTITY))
 (12 12 (:TYPE-PRESCRIPTION STRIP-CARS))
 (8 2 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (4 4 (:DEFINITION STRIP-CARS))
 (3 1 (:REWRITE CHARACTER-RESULT-FIX-WHEN-CHARACTER-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (2 2 (:TYPE-PRESCRIPTION CHARACTER-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION ALISTP))
 )
(CHARACTER-RESULT-FIX-WHEN-ERR
 (18 18 (:TYPE-PRESCRIPTION IDENTITY))
 (14 2 (:REWRITE FTY::RESULTERR-FIX-WHEN-RESULTERRP))
 (11 1 (:DEFINITION FTY::RESULTERRP))
 (6 6 (:TYPE-PRESCRIPTION STRIP-CARS))
 (4 1 (:REWRITE FTY::EQUAL-OF-STRIP-CARS))
 (3 1 (:REWRITE CHARACTER-RESULT-FIX-WHEN-CHARACTER-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION CHARACTER-RESULTP))
 (2 2 (:DEFINITION STRIP-CARS))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESULTERRP))
 (1 1 (:TYPE-PRESCRIPTION ALISTP))
 )
(EQUAL-OF-CHARACTER-RESULT-ERR
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
(CHARACTER-RESULT-ERR-OF-RESULTERR-FIX-GET
 (12 12 (:TYPE-PRESCRIPTION IDENTITY))
 )
(CHARACTER-RESULT-ERR-RESULTERR-EQUIV-CONGRUENCE-ON-GET)
(CHARACTER-RESULT-FIX-REDEF
 (9 3 (:REWRITE CHARACTER-RESULT-FIX-WHEN-CHARACTER-RESULTP))
 (6 6 (:TYPE-PRESCRIPTION CHARACTER-RESULTP))
 )
(CHARACTER-RESULTP-WHEN-CHARACTERP)
(CHARACTER-RESULTP-WHEN-RESULTERRP)
(CHARACTERP-WHEN-CHARACTER-RESULTP-AND-NOT-RESULTERRP)
