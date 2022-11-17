; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   http://www.russinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(include-book "log")
(include-book "logn")

(local (include-book "logn2log-proofs"))

(local (include-book "../../arithmetic/top"))

;;;;
;;;;


(defthm land-logand
  (implies (and (bvecp x n)
                (bvecp y n)
                (natp n))
           (equal (land x y n)
                  (logand x y))))

(defthm lior-logior
  (implies (and (bvecp x n)
                (bvecp y n)
                (natp n))
           (equal (lior x y n)
                  (logior x y))))


(defthm lxor-logxor
  (implies (and (bvecp x n)
                (bvecp y n)
                (natp n))
           (equal (lxor x y n)
                  (logxor x y))))

(defthm logior-bvecp
  (implies (and (bvecp x n) (bvecp y n))
           (bvecp (logior x y) n)))



(defthm logand-bvecp
  (implies (and (natp n) (bvecp x n) (integerp y))
           (bvecp (logand x y) n)))

(defthm logxor-bvecp
  (implies (and (bvecp x n)
                (bvecp y n)
                (natp n))
           (bvecp (logxor x y) n)))

(defthm lnot-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (lnot x n) k)))









