(|f|)
(C::*PROGRAM*-WELL-FORMED)
(|f-RETURNS-VALUE|)
(C::|*PROGRAM*-f-CORRECT|
 (1372 1 (:REWRITE C::EXEC-BLOCK-ITEM-LIST-UNROLL))
 (93 90 (:REWRITE C::VALUEP-WHEN-ULONGP))
 (93 90 (:REWRITE C::VALUEP-WHEN-ULLONGP))
 (93 90 (:REWRITE C::VALUEP-WHEN-SLONGP))
 (93 90 (:REWRITE C::VALUEP-WHEN-SLLONGP))
 (93 90 (:REWRITE C::VALUEP-WHEN-SINTP))
 (90 90 (:REWRITE C::VALUEP-WHEN-POINTERP))
 (55 25 (:REWRITE C::NOT-SLONGP-WHEN-ULONGP))
 (55 25 (:REWRITE C::NOT-SLONGP-WHEN-ULLONGP))
 (55 25 (:REWRITE C::NOT-SLONGP-WHEN-SLLONGP))
 (55 25 (:REWRITE C::NOT-SLLONGP-WHEN-ULONGP))
 (55 25 (:REWRITE C::NOT-SLLONGP-WHEN-ULLONGP))
 (55 25 (:REWRITE C::NOT-SLLONGP-WHEN-SLONGP))
 (55 25 (:REWRITE C::NOT-SINTP-WHEN-ULONGP))
 (55 25 (:REWRITE C::NOT-SINTP-WHEN-ULLONGP))
 (55 25 (:REWRITE C::NOT-SINTP-WHEN-SLONGP))
 (55 25 (:REWRITE C::NOT-SINTP-WHEN-SLLONGP))
 (44 44 (:REWRITE C::VALUEP-WHEN-USHORTP))
 (44 44 (:REWRITE C::VALUEP-WHEN-SSHORTP))
 (44 44 (:REWRITE C::VALUEP-WHEN-SCHARP))
 (27 24 (:REWRITE C::NOT-UCHARP-WHEN-ULONGP))
 (27 24 (:REWRITE C::NOT-UCHARP-WHEN-ULLONGP))
 (27 24 (:REWRITE C::NOT-UCHARP-WHEN-SLONGP))
 (27 24 (:REWRITE C::NOT-UCHARP-WHEN-SLLONGP))
 (27 24 (:REWRITE C::NOT-UCHARP-WHEN-SINTP))
 (25 25 (:REWRITE C::NOT-SLONGP-WHEN-POINTERP))
 (25 25 (:REWRITE C::NOT-SLLONGP-WHEN-POINTERP))
 (25 25 (:REWRITE C::NOT-SINTP-WHEN-POINTERP))
 (25 10 (:REWRITE C::NOT-ULONGP-WHEN-ULLONGP))
 (25 10 (:REWRITE C::NOT-ULONGP-WHEN-SLONGP))
 (25 10 (:REWRITE C::NOT-ULONGP-WHEN-SLLONGP))
 (25 10 (:REWRITE C::NOT-ULONGP-WHEN-SINTP))
 (25 10 (:REWRITE C::NOT-ULLONGP-WHEN-ULONGP))
 (25 10 (:REWRITE C::NOT-ULLONGP-WHEN-SLONGP))
 (25 10 (:REWRITE C::NOT-ULLONGP-WHEN-SLLONGP))
 (25 10 (:REWRITE C::NOT-ULLONGP-WHEN-SINTP))
 (25 10 (:REWRITE C::NOT-SINTP-WHEN-USHORTP))
 (25 10 (:REWRITE C::NOT-SINTP-WHEN-SSHORTP))
 (25 10 (:REWRITE C::NOT-SINTP-WHEN-SCHARP))
 (24 24 (:REWRITE C::NOT-UCHARP-WHEN-POINTERP))
 (21 18 (:REWRITE C::NOT-UINTP-WHEN-USHORTP))
 (21 18 (:REWRITE C::NOT-UINTP-WHEN-ULONGP))
 (21 18 (:REWRITE C::NOT-UINTP-WHEN-ULLONGP))
 (21 18 (:REWRITE C::NOT-UINTP-WHEN-UCHARP))
 (21 18 (:REWRITE C::NOT-UINTP-WHEN-SSHORTP))
 (21 18 (:REWRITE C::NOT-UINTP-WHEN-SLONGP))
 (21 18 (:REWRITE C::NOT-UINTP-WHEN-SLLONGP))
 (21 18 (:REWRITE C::NOT-UINTP-WHEN-SINTP))
 (21 18 (:REWRITE C::NOT-UINTP-WHEN-SCHARP))
 (20 17 (:REWRITE C::NOT-SSHORTP-WHEN-ULONGP))
 (20 17 (:REWRITE C::NOT-SSHORTP-WHEN-ULLONGP))
 (20 17 (:REWRITE C::NOT-SSHORTP-WHEN-SLONGP))
 (20 17 (:REWRITE C::NOT-SSHORTP-WHEN-SLLONGP))
 (20 17 (:REWRITE C::NOT-SSHORTP-WHEN-SINTP))
 (20 17 (:REWRITE C::NOT-SCHARP-WHEN-ULONGP))
 (20 17 (:REWRITE C::NOT-SCHARP-WHEN-ULLONGP))
 (20 17 (:REWRITE C::NOT-SCHARP-WHEN-SLONGP))
 (20 17 (:REWRITE C::NOT-SCHARP-WHEN-SLLONGP))
 (20 17 (:REWRITE C::NOT-SCHARP-WHEN-SINTP))
 (18 18 (:REWRITE C::NOT-UINTP-WHEN-POINTERP))
 (17 17 (:REWRITE C::NOT-SSHORTP-WHEN-POINTERP))
 (17 17 (:REWRITE C::NOT-SCHARP-WHEN-POINTERP))
 (15 15 (:REWRITE C::NOT-ERRORP-WHEN-USHORT-ARRAYP))
 (15 15 (:REWRITE C::NOT-ERRORP-WHEN-ULONG-ARRAYP))
 (15 15 (:REWRITE C::NOT-ERRORP-WHEN-ULLONG-ARRAYP))
 (15 15 (:REWRITE C::NOT-ERRORP-WHEN-UINT-ARRAYP))
 (15 15 (:REWRITE C::NOT-ERRORP-WHEN-UCHAR-ARRAYP))
 (15 15 (:REWRITE C::NOT-ERRORP-WHEN-SSHORT-ARRAYP))
 (15 15 (:REWRITE C::NOT-ERRORP-WHEN-SLONG-ARRAYP))
 (15 15 (:REWRITE C::NOT-ERRORP-WHEN-SLLONG-ARRAYP))
 (15 15 (:REWRITE C::NOT-ERRORP-WHEN-SINT-ARRAYP))
 (15 15 (:REWRITE C::NOT-ERRORP-WHEN-SCOPE-LISTP))
 (15 15 (:REWRITE C::NOT-ERRORP-WHEN-SCHAR-ARRAYP))
 (15 15 (:REWRITE C::EXEC-EXPR-PURE-UNROLL-5))
 (15 12 (:REWRITE C::NOT-USHORTP-WHEN-ULONGP))
 (15 12 (:REWRITE C::NOT-USHORTP-WHEN-ULLONGP))
 (15 12 (:REWRITE C::NOT-USHORTP-WHEN-SLONGP))
 (15 12 (:REWRITE C::NOT-USHORTP-WHEN-SLLONGP))
 (15 12 (:REWRITE C::NOT-USHORTP-WHEN-SINTP))
 (13 13 (:REWRITE C::NOT-ERRORP-WHEN-VALUE-LISTP))
 (12 12 (:REWRITE C::NOT-USHORTP-WHEN-POINTERP))
 (12 12 (:REWRITE C::NOT-UCHARP-WHEN-USHORTP))
 (12 12 (:REWRITE C::NOT-UCHARP-WHEN-SSHORTP))
 (12 12 (:REWRITE C::NOT-UCHARP-WHEN-SCHARP))
 (10 10 (:REWRITE C::NOT-ULONGP-WHEN-POINTERP))
 (10 10 (:REWRITE C::NOT-ULLONGP-WHEN-POINTERP))
 (10 10 (:REWRITE C::EXEC-EXPR-PURE-UNROLL-3))
 (10 10 (:REWRITE C::EXEC-EXPR-PURE-UNROLL-2))
 (10 10 (:REWRITE C::EXEC-EXPR-PURE-UNROLL-1))
 (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-5))
 (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-4))
 (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-3))
 (10 10 (:REWRITE C::EXEC-EXPR-PURE-BASE-2))
 (8 6 (:REWRITE C::EXEC-STMT-UNROLL-2))
 (8 6 (:REWRITE C::EXEC-STMT-UNROLL-1))
 (5 5 (:REWRITE C::NOT-SSHORTP-WHEN-USHORTP))
 (5 5 (:REWRITE C::NOT-SSHORTP-WHEN-SCHARP))
 (5 5 (:REWRITE C::NOT-SLONGP-WHEN-USHORTP))
 (5 5 (:REWRITE C::NOT-SLONGP-WHEN-SSHORTP))
 (5 5 (:REWRITE C::NOT-SLONGP-WHEN-SCHARP))
 (5 5 (:REWRITE C::NOT-SLLONGP-WHEN-USHORTP))
 (5 5 (:REWRITE C::NOT-SLLONGP-WHEN-SSHORTP))
 (5 5 (:REWRITE C::NOT-SLLONGP-WHEN-SCHARP))
 (5 5 (:REWRITE C::NOT-SCHARP-WHEN-USHORTP))
 (5 5 (:REWRITE C::NOT-SCHARP-WHEN-SSHORTP))
 (4 2 (:REWRITE OMAP::IN-UNROLL))
 (2 1 (:REWRITE C::EXEC-STMT-BASE-7))
 (2 1 (:REWRITE C::EXEC-STMT-BASE-5))
 (2 1 (:REWRITE C::EXEC-STMT-BASE-4))
 (1 1 (:REWRITE OMAP::IN-BASE-1))
 (1 1 (:REWRITE C::EXEC-FUN-OF-CONST-IDENTIFIER))
 (1 1 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-RESULTP-AND-NOT-ERRORP))
 )
