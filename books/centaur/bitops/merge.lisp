; Centaur Bitops Library
; Copyright (C) 2010-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "std/util/define" :dir :system)
(include-book "centaur/misc/arith-equivs" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)
(local (include-book "ihsext-basics"))
(local (include-book "signed-byte-p"))
(local (include-book "equal-by-logbitp"))

(local (defthm ash-of-logior-of-ash
         (implies (natp amt)
                  (equal (ash (logior a b) amt)
                         (logior (ash a amt)
                                 (ash b amt))))
         :hints((acl2::equal-by-logbitp-hammer))))

;; Speed hint
(local (in-theory (disable ACL2::LOGIOR-<-0-LINEAR-2)))

(defxdoc bitops/merge
  :parents (bitops)
  :short "Various common operations for concatenating bytes/words."

  :long "<p>These merge operations may be useful for describing SIMD style
operations, byte swapping operations, and so forth.</p>

<p>Each function here is logically simple, but we go to some lengths to make
them execute more efficiently.  For instance,</p>

@({
 (let ((a7 1)
       (a6 2)
       (a5 3)
       (a4 4)
       (a3 5)
       (a2 6)
       (a1 7)
       (a0 8))
   ;; logic mode version: 11.112 seconds
   ;; exec mode version:   1.404 seconds
   (time (loop for i fixnum from 1 to 100000000 do
               (merge-8-u8s a7 a6 a5 a4 a3 a2 a1 a0))))
})")

(local (xdoc::set-default-parents bitops/merge))


;; Merging Bytes --------------------------------------------------------------

(define merge-2-u8s (a1 a0)
  (declare (type (unsigned-byte 8) a1 a0))
  :returns (result natp :rule-classes :type-prescription)
  :short "Concatenate two bytes together to form a single 16-bit result."
  :inline t ;; This one is nice and small
  (mbe :logic
       (logior (ash (nfix a1) (* 1 8))
               (nfix a0))
       :exec
       (the (unsigned-byte 16)
         (logior (the (unsigned-byte 16) (ash a1 8))
                 (the (unsigned-byte 16) a0))))
  ///
  (defcong nat-equiv equal (merge-2-u8s a1 a0) 1)
  (defcong nat-equiv equal (merge-2-u8s a1 a0) 2)
  (defthm unsigned-byte-p-16-of-merge-2-u8s
    (implies (and (unsigned-byte-p 8 a1)
                  (unsigned-byte-p 8 a0))
             (unsigned-byte-p 16 (merge-2-u8s a1 a0)))))

(define merge-4-u8s (a3 a2 a1 a0)
  (declare (type (unsigned-byte 8) a3 a2 a1 a0))
  :returns (result natp :rule-classes :type-prescription)
  :short "Concatenate four bytes together to form a single 32-bit result."
  :inline t ;; This one is nice and small
  (mbe :logic
       (logior (ash (nfix a3) (* 3 8))
               (ash (nfix a2) (* 2 8))
               (ash (nfix a1) (* 1 8))
               (nfix a0))
       :exec
       (let* ((a3 (the (unsigned-byte 32) (ash a3 24)))
              (a2 (the (unsigned-byte 32) (ash a2 16)))
              (a1 (the (unsigned-byte 32) (ash a1 8)))
              ;; Ugly series of LOGIORs because CCL won't optimize multi-arg
              ;; LOGIORs into fixnum computations...
              (ans (the (unsigned-byte 32)
                     (logior (the (unsigned-byte 32) a1)
                             (the (unsigned-byte 32) a0))))
              (ans (the (unsigned-byte 32)
                     (logior (the (unsigned-byte 32) a2)
                             (the (unsigned-byte 32) ans)))))
         (the (unsigned-byte 32)
           (logior (the (unsigned-byte 32) a3)
                   (the (unsigned-byte 32) ans)))))
  ///
  (defcong nat-equiv equal (merge-4-u8s a3 a2 a1 a0) 1)
  (defcong nat-equiv equal (merge-4-u8s a3 a2 a1 a0) 2)
  (defcong nat-equiv equal (merge-4-u8s a3 a2 a1 a0) 3)
  (defcong nat-equiv equal (merge-4-u8s a3 a2 a1 a0) 4)
  (defthm unsigned-byte-p-32-of-merge-4-u8s
    (implies (and (unsigned-byte-p 8 a3)
                  (unsigned-byte-p 8 a2)
                  (unsigned-byte-p 8 a1)
                  (unsigned-byte-p 8 a0))
             (unsigned-byte-p 32 (merge-4-u8s a3 a2 a1 a0)))))

(define merge-8-u8s (a7 a6 a5 a4 a3 a2 a1 a0)
  (declare (type (unsigned-byte 8) a7 a6 a5 a4 a3 a2 a1 a0))
  :returns (result natp :rule-classes :type-prescription)
  :short "Concatenate eight bytes together to form a single 64-bit result."
  ;; Not inline because we can't really avoid some non-fixnum operations, so it
  ;; ends up being pretty large.
  (mbe :logic
       (logior (ash (nfix a7) (* 7 8))
               (ash (nfix a6) (* 6 8))
               (ash (nfix a5) (* 5 8))
               (ash (nfix a4) (* 4 8))
               (ash (nfix a3) (* 3 8))
               (ash (nfix a2) (* 2 8))
               (ash (nfix a1) (* 1 8))
               (nfix a0))
       :exec
       (let* ((a7 (the (unsigned-byte 64) (ash a7 56)))
              ;; On 64-bit CCL fixnums are 61 bits, so (unsigned-byte 56) is a
              ;; fixnum while (unsigned-byte 64) is not
              (a6 (the (unsigned-byte 56) (ash a6 48)))
              (a5 (the (unsigned-byte 56) (ash a5 40)))
              (a4 (the (unsigned-byte 56) (ash a4 32)))
              (a3 (the (unsigned-byte 56) (ash a3 24)))
              (a2 (the (unsigned-byte 56) (ash a2 16)))
              (a1 (the (unsigned-byte 56) (ash a1 8)))
              ;; Ugly series of LOGIORs because CCL won't optimize multi-arg
              ;; LOGIORs into fixnum computations...
              (ans (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) a1)
                             (the (unsigned-byte 56) a0))))
              (ans (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) a2)
                             (the (unsigned-byte 56) ans))))
              (ans (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) a3)
                             (the (unsigned-byte 56) ans))))
              (ans (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) a4)
                             (the (unsigned-byte 56) ans))))
              (ans (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) a5)
                             (the (unsigned-byte 56) ans))))
              (ans (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) a6)
                             (the (unsigned-byte 56) ans)))))
         (the (unsigned-byte 64)
           (logior (the (unsigned-byte 64) a7)
                   (the (unsigned-byte 56) ans)))))
  ///
  (defcong nat-equiv equal (merge-8-u8s a7 a6 a5 a4 a3 a2 a1 a0) 1)
  (defcong nat-equiv equal (merge-8-u8s a7 a6 a5 a4 a3 a2 a1 a0) 2)
  (defcong nat-equiv equal (merge-8-u8s a7 a6 a5 a4 a3 a2 a1 a0) 3)
  (defcong nat-equiv equal (merge-8-u8s a7 a6 a5 a4 a3 a2 a1 a0) 4)
  (defcong nat-equiv equal (merge-8-u8s a7 a6 a5 a4 a3 a2 a1 a0) 5)
  (defcong nat-equiv equal (merge-8-u8s a7 a6 a5 a4 a3 a2 a1 a0) 6)
  (defcong nat-equiv equal (merge-8-u8s a7 a6 a5 a4 a3 a2 a1 a0) 7)
  (defcong nat-equiv equal (merge-8-u8s a7 a6 a5 a4 a3 a2 a1 a0) 8)
  (defthm unsigned-byte-p-64-of-merge-8-u8s
    (implies (and (unsigned-byte-p 8 a7)
                  (unsigned-byte-p 8 a6)
                  (unsigned-byte-p 8 a5)
                  (unsigned-byte-p 8 a4)
                  (unsigned-byte-p 8 a3)
                  (unsigned-byte-p 8 a2)
                  (unsigned-byte-p 8 a1)
                  (unsigned-byte-p 8 a0))
             (unsigned-byte-p 64 (merge-8-u8s a7 a6 a5 a4 a3 a2 a1 a0)))))

(define merge-16-u8s (h7 h6 h5 h4 h3 h2 h1 h0
                      l7 l6 l5 l4 l3 l2 l1 l0)
  (declare (type (unsigned-byte 8)
                 h7 h6 h5 h4 h3 h2 h1 h0
                 l7 l6 l5 l4 l3 l2 l1 l0))
  :returns (result natp :rule-classes :type-prescription)
  :short "Concatenate sixteen bytes together to form a single 128-bit result."
  :long "<p>The efficiency improvement here is especially pronounced.</p>

@({ (let ((h7 15)   ;; The 'H' bytes are for the 'High' half
          (h6 14)
          (h5 13)
          (h4 12)
          (h3 11)
          (h2 10)
          (h1  9)
          (h0  8)
          (l7  7)   ;; The 'L' bytes are for the 'Low' half
          (l6  6)
          (l5  5)
          (l4  4)
          (l3  3)
          (l2  2)
          (l1  1)
          (l0  0))
      ;; logic mode version: 272 sec (excluding gc),  70 GB alloc
      ;; exec mode version:  17.53 sec (no gc),      6.4 GB alloc
      (gc$)
      (time (loop for i fixnum from 1 to #u100_000_000 do
              (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                            l7 l6 l5 l4 l3 l2 l1 l0)))) })"

  (mbe :logic
       (logior (ash (nfix h7) (* 15 8))
               (ash (nfix h6) (* 14 8))
               (ash (nfix h5) (* 13 8))
               (ash (nfix h4) (* 12 8))
               (ash (nfix h3) (* 11 8))
               (ash (nfix h2) (* 10 8))
               (ash (nfix h1) (* 9 8))
               (ash (nfix h0) (* 8 8))
               (ash (nfix l7) (* 7 8))
               (ash (nfix l6) (* 6 8))
               (ash (nfix l5) (* 5 8))
               (ash (nfix l4) (* 4 8))
               (ash (nfix l3) (* 3 8))
               (ash (nfix l2) (* 2 8))
               (ash (nfix l1) (* 1 8))
               (nfix l0))
       :exec
       (let* ((l7 (the (unsigned-byte 64) (ash l7 56)))
              (l6 (the (unsigned-byte 56) (ash l6 48)))
              (l5 (the (unsigned-byte 56) (ash l5 40)))
              (l4 (the (unsigned-byte 56) (ash l4 32)))
              (l3 (the (unsigned-byte 56) (ash l3 24)))
              (l2 (the (unsigned-byte 56) (ash l2 16)))
              (l1 (the (unsigned-byte 56) (ash l1 8)))
              ;; Ugly series of LOGIORs because CCL won't optimize multi-arg
              ;; LOGIORs into fixnum computations...
              (low (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) l1)
                             (the (unsigned-byte 56) l0))))
              (low (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) l2)
                             (the (unsigned-byte 56) low))))
              (low (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) l3)
                             (the (unsigned-byte 56) low))))
              (low (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) l4)
                             (the (unsigned-byte 56) low))))
              (low (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) l5)
                             (the (unsigned-byte 56) low))))
              (low (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) l6)
                             (the (unsigned-byte 56) low))))
              (low (the (unsigned-byte 64)
                     (logior (the (unsigned-byte 64) l7)
                             (the (unsigned-byte 56) low))))
              ;; Same on the high side...
              (h7 (the (unsigned-byte 64) (ash h7 56)))
              (h6 (the (unsigned-byte 56) (ash h6 48)))
              (h5 (the (unsigned-byte 56) (ash h5 40)))
              (h4 (the (unsigned-byte 56) (ash h4 32)))
              (h3 (the (unsigned-byte 56) (ash h3 24)))
              (h2 (the (unsigned-byte 56) (ash h2 16)))
              (h1 (the (unsigned-byte 56) (ash h1 8)))
              (high (the (unsigned-byte 56)
                      (logior (the (unsigned-byte 56) h1)
                              (the (unsigned-byte 56) h0))))
              (high (the (unsigned-byte 56)
                      (logior (the (unsigned-byte 56) h2)
                              (the (unsigned-byte 56) high))))
              (high (the (unsigned-byte 56)
                      (logior (the (unsigned-byte 56) h3)
                              (the (unsigned-byte 56) high))))
              (high (the (unsigned-byte 56)
                      (logior (the (unsigned-byte 56) h4)
                              (the (unsigned-byte 56) high))))
              (high (the (unsigned-byte 56)
                      (logior (the (unsigned-byte 56) h5)
                              (the (unsigned-byte 56) high))))
              (high (the (unsigned-byte 56)
                      (logior (the (unsigned-byte 56) h6)
                              (the (unsigned-byte 56) high))))
              (high (the (unsigned-byte 64)
                      (logior (the (unsigned-byte 64) h7)
                              (the (unsigned-byte 56) high))))
              (high (the (unsigned-byte 128)
                      (ash high 64))))
         (the (unsigned-byte 128)
           (logior (the (unsigned-byte 128) high)
                   (the (unsigned-byte 64) low)))))
  ///
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 1)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 2)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 3)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 4)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 5)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 6)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 7)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 8)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 9)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 10)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 11)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 12)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 13)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 14)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 15)
  (defcong nat-equiv equal (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                         l7 l6 l5 l4 l3 l2 l1 l0) 16)
  (defthm unsigned-byte-p-128-of-merge-16-u8s
    (implies (and (unsigned-byte-p 8 h7)
                  (unsigned-byte-p 8 h6)
                  (unsigned-byte-p 8 h5)
                  (unsigned-byte-p 8 h4)
                  (unsigned-byte-p 8 h3)
                  (unsigned-byte-p 8 h2)
                  (unsigned-byte-p 8 h1)
                  (unsigned-byte-p 8 h0)
                  (unsigned-byte-p 8 l7)
                  (unsigned-byte-p 8 l6)
                  (unsigned-byte-p 8 l5)
                  (unsigned-byte-p 8 l4)
                  (unsigned-byte-p 8 l3)
                  (unsigned-byte-p 8 l2)
                  (unsigned-byte-p 8 l1)
                  (unsigned-byte-p 8 l0))
             (unsigned-byte-p 128 (merge-16-u8s h7 h6 h5 h4 h3 h2 h1 h0
                                                l7 l6 l5 l4 l3 l2 l1 l0)))))


(define merge-32-u8s (a7 a6 a5 a4 a3 a2 a1 a0
                      b7 b6 b5 b4 b3 b2 b1 b0
                      c7 c6 c5 c4 c3 c2 c1 c0
                      d7 d6 d5 d4 d3 d2 d1 d0)
  (declare (type (unsigned-byte 8)
                 a7 a6 a5 a4 a3 a2 a1 a0
                 b7 b6 b5 b4 b3 b2 b1 b0
                 c7 c6 c5 c4 c3 c2 c1 c0
                 d7 d6 d5 d4 d3 d2 d1 d0))
  :returns (result natp :rule-classes :type-prescription)
  :short "Concatenate 32 bytes together to form a single 256-bit result."
  :guard-hints(("Goal" :in-theory (enable merge-16-u8s)))

  :long "<p>The efficiency improvement here is especially pronounced.</p>

@({ (let ((a0  0)  ;; The 'A' bytes are the most significant
          (a1  1)
          (a2  2)
          (a3  3)
          (a4  4)
          (a5  5)
          (a6  6)
          (a7  7)
          (b0  8)  ;; The 'B' bytes are the next most significant
          (b1  9)
          (b2 10)
          (b3 11)
          (b4 12)
          (b5 13)
          (b6 14)
          (b7 15)
          (c0 16)  ;; The 'C' cytes are the next most significant
          (c1 17)
          (c2 18)
          (c3 19)
          (c4 20)
          (c5 21)
          (c6 22)
          (c7 23)
          (d0 24)  ;; The 'D' dytes are the least most significant
          (d1 25)
          (d2 26)
          (d3 27)
          (d4 28)
          (d5 29)
          (d6 30)
          (d7 31))
      ;; logic mode version: 43.8 seconds, 23 GB allocated
      ;; exec mode version:  3.8 seconds, 2.8 GB allocated
      (gc$)
      (time (loop for i fixnum from 1 to 10000000 do
                  (merge-32-u8s a7 a6 a5 a4 a3 a2 a1 a0
                                b7 b6 b5 b4 b3 b2 b1 b0
                                c7 c6 c5 c4 c3 c2 c1 c0
                                d7 d6 d5 d4 d3 d2 d1 d0)))) })"
  (mbe :logic
       (logior (ash (lnfix a7) (* 31 8))
               (ash (lnfix a6) (* 30 8))
               (ash (lnfix a5) (* 29 8))
               (ash (lnfix a4) (* 28 8))
               (ash (lnfix a3) (* 27 8))
               (ash (lnfix a2) (* 26 8))
               (ash (lnfix a1) (* 25 8))
               (ash (lnfix a0) (* 24 8))
               (ash (lnfix b7) (* 23 8))
               (ash (lnfix b6) (* 22 8))
               (ash (lnfix b5) (* 21 8))
               (ash (lnfix b4) (* 20 8))
               (ash (lnfix b3) (* 19 8))
               (ash (lnfix b2) (* 18 8))
               (ash (lnfix b1) (* 17 8))
               (ash (lnfix b0) (* 16 8))
               (ash (lnfix c7) (* 15 8))
               (ash (lnfix c6) (* 14 8))
               (ash (lnfix c5) (* 13 8))
               (ash (lnfix c4) (* 12 8))
               (ash (lnfix c3) (* 11 8))
               (ash (lnfix c2) (* 10 8))
               (ash (lnfix c1) (* 9 8))
               (ash (lnfix c0) (* 8 8))
               (ash (lnfix d7) (* 7 8))
               (ash (lnfix d6) (* 6 8))
               (ash (lnfix d5) (* 5 8))
               (ash (lnfix d4) (* 4 8))
               (ash (lnfix d3) (* 3 8))
               (ash (lnfix d2) (* 2 8))
               (ash (lnfix d1) (* 1 8))
               (lnfix d0))
       :exec
       (b* (((the (unsigned-byte 128) high)
             (merge-16-u8s a7 a6 a5 a4 a3 a2 a1 a0
                           b7 b6 b5 b4 b3 b2 b1 b0))
            ((the (unsigned-byte 128) low)
             (merge-16-u8s c7 c6 c5 c4 c3 c2 c1 c0
                           d7 d6 d5 d4 d3 d2 d1 d0)))
         (the (unsigned-byte 256)
              (logior
               (the (unsigned-byte 256) (ash (the (unsigned-byte 128) high) 128))
               (the (unsigned-byte 128) low)))))
  ///
  (defun congruences-for-merge-32-u8s (n)
    (declare (xargs :mode :program))
    (if (zp n)
        nil
      (cons
       `(defcong nat-equiv equal (merge-32-u8s a7 a6 a5 a4 a3 a2 a1 a0
                                               b7 b6 b5 b4 b3 b2 b1 b0
                                               c7 c6 c5 c4 c3 c2 c1 c0
                                               d7 d6 d5 d4 d3 d2 d1 d0)
          ,n)
       (congruences-for-merge-32-u8s (- n 1)))))

  (make-event
   (cons 'progn (congruences-for-merge-32-u8s 32)))

  (defthm unsigned-byte-p-256-of-merge-16-u8s
    (implies (and (unsigned-byte-p 8 a7)
                  (unsigned-byte-p 8 a6)
                  (unsigned-byte-p 8 a5)
                  (unsigned-byte-p 8 a4)
                  (unsigned-byte-p 8 a3)
                  (unsigned-byte-p 8 a2)
                  (unsigned-byte-p 8 a1)
                  (unsigned-byte-p 8 a0)
                  (unsigned-byte-p 8 b7)
                  (unsigned-byte-p 8 b6)
                  (unsigned-byte-p 8 b5)
                  (unsigned-byte-p 8 b4)
                  (unsigned-byte-p 8 b3)
                  (unsigned-byte-p 8 b2)
                  (unsigned-byte-p 8 b1)
                  (unsigned-byte-p 8 b0)
                  (unsigned-byte-p 8 c7)
                  (unsigned-byte-p 8 c6)
                  (unsigned-byte-p 8 c5)
                  (unsigned-byte-p 8 c4)
                  (unsigned-byte-p 8 c3)
                  (unsigned-byte-p 8 c2)
                  (unsigned-byte-p 8 c1)
                  (unsigned-byte-p 8 c0)
                  (unsigned-byte-p 8 d7)
                  (unsigned-byte-p 8 d6)
                  (unsigned-byte-p 8 d5)
                  (unsigned-byte-p 8 d4)
                  (unsigned-byte-p 8 d3)
                  (unsigned-byte-p 8 d2)
                  (unsigned-byte-p 8 d1)
                  (unsigned-byte-p 8 d0))
             (unsigned-byte-p 256 (merge-32-u8s a7 a6 a5 a4 a3 a2 a1 a0
                                                b7 b6 b5 b4 b3 b2 b1 b0
                                                c7 c6 c5 c4 c3 c2 c1 c0
                                                d7 d6 d5 d4 d3 d2 d1 d0)))))


;; Merging Words --------------------------------------------------------------

(define merge-2-u16s (a1 a0)
  (declare (type (unsigned-byte 16) a1 a0))
  :returns (result natp :rule-classes :type-prescription)
  :short "Concatenate two 16-bit values together to form a single 32-bit
result."
  :inline t
  (mbe :logic
       (logior (ash (nfix a1) (* 1 16))
               (nfix a0))
       :exec
       (the (unsigned-byte 32)
         (logior (the (unsigned-byte 32) (ash a1 16))
                 a0)))
  ///
  (defcong nat-equiv equal (merge-2-u16s a1 a0) 1)
  (defcong nat-equiv equal (merge-2-u16s a1 a0) 2)
  (defthm unsigned-byte-p-32-of-merge-2-u16s
    (implies (and (unsigned-byte-p 16 a1)
                  (unsigned-byte-p 16 a0))
             (unsigned-byte-p 32 (merge-2-u16s a1 a0)))))

(define merge-4-u16s (a3 a2 a1 a0)
  (declare (type (unsigned-byte 16) a3 a2 a1 a0))
  :returns (result natp :rule-classes :type-prescription)
  :short "Concatenate four 16-bit values together to form a single 64-bit
result."
  (mbe :logic
       (logior (ash (nfix a3) (* 3 16))
               (ash (nfix a2) (* 2 16))
               (ash (nfix a1) (* 1 16))
               (nfix a0))
       :exec
       (let* ((a3 (the (unsigned-byte 64) (ash a3 48)))
              (a2 (the (unsigned-byte 56) (ash a2 32)))
              (a1 (the (unsigned-byte 56) (ash a1 16)))
              ;; Ugly series of LOGIORs because CCL won't optimize multi-arg
              ;; LOGIORs into fixnum computations...
              (ans (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) a1)
                             (the (unsigned-byte 56) a0))))
              (ans (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) a2)
                             (the (unsigned-byte 56) ans)))))
         (the (unsigned-byte 64)
           (logior (the (unsigned-byte 64) a3)
                   (the (unsigned-byte 56) ans)))))
  ///
  (defcong nat-equiv equal (merge-4-u16s a3 a2 a1 a0) 1)
  (defcong nat-equiv equal (merge-4-u16s a3 a2 a1 a0) 2)
  (defcong nat-equiv equal (merge-4-u16s a3 a2 a1 a0) 3)
  (defcong nat-equiv equal (merge-4-u16s a3 a2 a1 a0) 4)
  (defthm unsigned-byte-p-64-of-merge-4-u16s
    (implies (and (unsigned-byte-p 16 a3)
                  (unsigned-byte-p 16 a2)
                  (unsigned-byte-p 16 a1)
                  (unsigned-byte-p 16 a0))
             (unsigned-byte-p 64 (merge-4-u16s a3 a2 a1 a0)))))

(define merge-8-u16s (h3 h2 h1 h0 l3 l2 l1 l0)
  (declare (type (unsigned-byte 16) h3 h2 h1 h0 l3 l2 l1 l0))
  :returns (result natp :rule-classes :type-prescription)
  :short "Concatenate eight 16-bit values together to form a single 128-bit
  result."
  :long "<p>The executable version is considerably more efficient than the
logic-mode definition.</p>

@({
 (let ((l0 0)     ;; The 'L' words are for the 'Low' half
       (l1 1)
       (l2 2)
       (l3 3)
       (h0 0)     ;; The 'H' words are for the 'High' half
       (h1 1)
       (h2 2)
       (h3 3))
   ;; logic mode version: 110 sec (without gc), 25.6 GB alloc
   ;; exec mode version:  16.6 sec (no gc),     6.4 GB alloc
   (gc$)
   (time (loop for i fixnum from 1 to 100000000 do
               (merge-8-u16s h3 h2 h1 h0 l3 l2 l1 l0))))
})"
  (mbe :logic
       (logior (ash (nfix h3) (* 7 16))
               (ash (nfix h2) (* 6 16))
               (ash (nfix h1) (* 5 16))
               (ash (nfix h0) (* 4 16))
               (ash (nfix l3) (* 3 16))
               (ash (nfix l2) (* 2 16))
               (ash (nfix l1) (* 1 16))
               (nfix l0))
       :exec
       (let* ((l3 (the (unsigned-byte 64) (ash l3 48)))
              (l2 (the (unsigned-byte 56) (ash l2 32)))
              (l1 (the (unsigned-byte 56) (ash l1 16)))
              ;; Ugly series of LOGIORs because CCL won't optimize multi-arg
              ;; LOGIORs into fixnum computations...
              (low (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) l1)
                             (the (unsigned-byte 56) l0))))
              (low (the (unsigned-byte 56)
                     (logior (the (unsigned-byte 56) l2)
                             (the (unsigned-byte 56) low))))
              (low (the (unsigned-byte 64)
                     (logior (the (unsigned-byte 64) l3)
                             (the (unsigned-byte 56) low))))
              ;; same thing on the high side
              (h3 (the (unsigned-byte 64) (ash h3 48)))
              (h2 (the (unsigned-byte 56) (ash h2 32)))
              (h1 (the (unsigned-byte 56) (ash h1 16)))
              ;; Ugly series of LOGIORs because CCL won't optimize multi-arg
              ;; LOGIORs into fixnum computations...
              (high (the (unsigned-byte 56)
                      (logior (the (unsigned-byte 56) h1)
                              (the (unsigned-byte 56) h0))))
              (high (the (unsigned-byte 56)
                      (logior (the (unsigned-byte 56) h2)
                              (the (unsigned-byte 56) high))))
              (high (the (unsigned-byte 64)
                      (logior (the (unsigned-byte 64) h3)
                              (the (unsigned-byte 56) high))))
              (high (the (unsigned-byte 128)
                      (ash (the (unsigned-byte 64) high) 64))))
         (the (unsigned-byte 128)
           (logior (the (unsigned-byte 128) high)
                   (the (unsigned-byte 64) low)))))
  ///
  (defcong nat-equiv equal (merge-8-u16s h3 h2 h1 h0 l3 l2 l1 l0) 1)
  (defcong nat-equiv equal (merge-8-u16s h3 h2 h1 h0 l3 l2 l1 l0) 2)
  (defcong nat-equiv equal (merge-8-u16s h3 h2 h1 h0 l3 l2 l1 l0) 3)
  (defcong nat-equiv equal (merge-8-u16s h3 h2 h1 h0 l3 l2 l1 l0) 4)
  (defcong nat-equiv equal (merge-8-u16s h3 h2 h1 h0 l3 l2 l1 l0) 5)
  (defcong nat-equiv equal (merge-8-u16s h3 h2 h1 h0 l3 l2 l1 l0) 6)
  (defcong nat-equiv equal (merge-8-u16s h3 h2 h1 h0 l3 l2 l1 l0) 7)
  (defcong nat-equiv equal (merge-8-u16s h3 h2 h1 h0 l3 l2 l1 l0) 8)
  (defthm unsigned-byte-p-128-of-merge-8-u16s
    (implies (and (unsigned-byte-p 16 h3)
                  (unsigned-byte-p 16 h2)
                  (unsigned-byte-p 16 h1)
                  (unsigned-byte-p 16 h0)
                  (unsigned-byte-p 16 l3)
                  (unsigned-byte-p 16 l2)
                  (unsigned-byte-p 16 l1)
                  (unsigned-byte-p 16 l0))
             (unsigned-byte-p 128 (merge-8-u16s h3 h2 h1 h0 l3 l2 l1 l0)))))


(define merge-16-u16s (h7 h6 h5 h4 h3 h2 h1 h0
                       l7 l6 l5 l4 l3 l2 l1 l0)
  (declare (type (unsigned-byte 16)
                 h7 h6 h5 h4 h3 h2 h1 h0
                 l7 l6 l5 l4 l3 l2 l1 l0))
  :returns (result natp :rule-classes :type-prescription)
  :short "Concatenate sixteen 16-bit values together to form a single 256-bit
result."
  :long "<p>The executable version is considerably more efficient than the
logic-mode definition.</p>"
  :guard-hints(("Goal" :in-theory (enable merge-8-u16s)))
  (mbe :logic
       (logior (ash (nfix h7) (* 15 16))
               (ash (nfix h6) (* 14 16))
               (ash (nfix h5) (* 13 16))
               (ash (nfix h4) (* 12 16))
               (ash (nfix h3) (* 11 16))
               (ash (nfix h2) (* 10 16))
               (ash (nfix h1) (* 9 16))
               (ash (nfix h0) (* 8 16))
               (ash (nfix l7) (* 7 16))
               (ash (nfix l6) (* 6 16))
               (ash (nfix l5) (* 5 16))
               (ash (nfix l4) (* 4 16))
               (ash (nfix l3) (* 3 16))
               (ash (nfix l2) (* 2 16))
               (ash (nfix l1) (* 1 16))
               (nfix l0))
       :exec
       (b* (((the (unsigned-byte 128) high) (merge-8-u16s h7 h6 h5 h4 h3 h2 h1 h0))
            ((the (unsigned-byte 128) low)  (merge-8-u16s l7 l6 l5 l4 l3 l2 l1 l0)))
         (the (unsigned-byte 256)
              (logior
               (the (unsigned-byte 256) (ash (the (unsigned-byte 128) high) 128))
               (the (unsigned-byte 128) low)))))
  ///
  (defun congruences-for-merge-16-u16s (n)
    (declare (xargs :mode :program))
    (if (zp n)
        nil
      (cons
       `(defcong nat-equiv equal (merge-16-u16s h7 h6 h5 h4 h3 h2 h1 h0
                                                l7 l6 l5 l4 l3 l2 l1 l0)
          ,n)
       (congruences-for-merge-16-u16s (- n 1)))))

  (make-event
   (cons 'progn (congruences-for-merge-16-u16s 16)))

  (defthm unsigned-byte-p-256-of-merge-16-u16s
    (implies (and (unsigned-byte-p 16 h7)
                  (unsigned-byte-p 16 h6)
                  (unsigned-byte-p 16 h5)
                  (unsigned-byte-p 16 h4)
                  (unsigned-byte-p 16 h3)
                  (unsigned-byte-p 16 h2)
                  (unsigned-byte-p 16 h1)
                  (unsigned-byte-p 16 h0)
                  (unsigned-byte-p 16 l7)
                  (unsigned-byte-p 16 l6)
                  (unsigned-byte-p 16 l5)
                  (unsigned-byte-p 16 l4)
                  (unsigned-byte-p 16 l3)
                  (unsigned-byte-p 16 l2)
                  (unsigned-byte-p 16 l1)
                  (unsigned-byte-p 16 l0))
             (unsigned-byte-p 256
                              (merge-16-u16s h7 h6 h5 h4 h3 h2 h1 h0
                                             l7 l6 l5 l4 l3 l2 l1 l0)))))




;; Merging Dwords -------------------------------------------------------------

(define merge-2-u32s (a1 a0)
  (declare (type (unsigned-byte 32) a1 a0))
  :returns (result natp :rule-classes :type-prescription)
  :short "Concatenate two 32-bit values together to form a single 64-bit
result."
  (mbe :logic
       (logior (ash (nfix a1) 32)
               (nfix a0))
       :exec
       (the (unsigned-byte 64)
         (logior (the (unsigned-byte 64) (ash a1 32))
                 a0)))
  ///
  (defcong nat-equiv equal (merge-2-u32s a1 a0) 1)
  (defcong nat-equiv equal (merge-2-u32s a1 a0) 2)
  (defthm unsigned-byte-p-64-of-merge-2-u32s
    (implies (and (unsigned-byte-p 32 a1)
                  (unsigned-byte-p 32 a0))
             (unsigned-byte-p 64 (merge-2-u32s a1 a0)))))

(define merge-4-u32s (h1 h0 l1 l0)
  (declare (type (unsigned-byte 32) h1 h0 l1 l0))
  :returns (result natp :rule-classes :type-prescription)
  :short "Concatenate four 32-bit values together to form a single 128-bit
result."
  (mbe :logic
       (logior (ash (nfix h1) 96)
               (ash (nfix h0) 64)
               (ash (nfix l1) 32)
               (nfix l0))
       :exec
       (let* ((low (the (unsigned-byte 64)
                     (logior (the (unsigned-byte 64) (ash l1 32))
                             l0)))
              (high (the (unsigned-byte 64)
                      (logior (the (unsigned-byte 64) (ash h1 32))
                              h0)))
              (high (the (unsigned-byte 128)
                      (ash (the (unsigned-byte 64) high)
                           64))))
         (the (unsigned-byte 128)
           (logior (the (unsigned-byte 128) high)
                   (the (unsigned-byte 64) low)))))
  ///
  (defcong nat-equiv equal (merge-4-u32s h1 h0 l1 l0) 1)
  (defcong nat-equiv equal (merge-4-u32s h1 h0 l1 l0) 2)
  (defcong nat-equiv equal (merge-4-u32s h1 h0 l1 l0) 3)
  (defcong nat-equiv equal (merge-4-u32s h1 h0 l1 l0) 4)
  (defthm unsigned-byte-p-128-of-merge-4-u32s
    (implies (and (unsigned-byte-p 32 h1)
                  (unsigned-byte-p 32 h0)
                  (unsigned-byte-p 32 l1)
                  (unsigned-byte-p 32 l0))
             (unsigned-byte-p 128 (merge-4-u32s h1 h0 l1 l0)))))

(define merge-8-u32s (h3 h2 h1 h0 l3 l2 l1 l0)
  (declare (type (unsigned-byte 32) h3 h2 h1 h0 l3 l2 l1 l0))
  :returns (result natp :rule-classes :type-prescription)
  :short "Concatenate eight 32-bit values together to form a single 256-bit
result."
  :guard-hints(("Goal" :in-theory (enable merge-4-u32s)))
  (mbe :logic
       (logior (ash (nfix h3) (* 7 32))
               (ash (nfix h2) (* 6 32))
               (ash (nfix h1) (* 5 32))
               (ash (nfix h0) (* 4 32))
               (ash (nfix l3) (* 3 32))
               (ash (nfix l2) (* 2 32))
               (ash (nfix l1) (* 1 32))
               (nfix l0))
       :exec
       (b* (((the (unsigned-byte 128) high) (merge-4-u32s h3 h2 h1 h0))
            ((the (unsigned-byte 128) low)  (merge-4-u32s l3 l2 l1 l0)))
         (the (unsigned-byte 256)
              (logior
               (the (unsigned-byte 256) (ash (the (unsigned-byte 128) high) 128))
               (the (unsigned-byte 128) low)))))
  ///
  (defcong nat-equiv equal (merge-8-u32s h3 h2 h1 h0 l3 l2 l1 l0) 1)
  (defcong nat-equiv equal (merge-8-u32s h3 h2 h1 h0 l3 l2 l1 l0) 2)
  (defcong nat-equiv equal (merge-8-u32s h3 h2 h1 h0 l3 l2 l1 l0) 3)
  (defcong nat-equiv equal (merge-8-u32s h3 h2 h1 h0 l3 l2 l1 l0) 4)
  (defcong nat-equiv equal (merge-8-u32s h3 h2 h1 h0 l3 l2 l1 l0) 5)
  (defcong nat-equiv equal (merge-8-u32s h3 h2 h1 h0 l3 l2 l1 l0) 6)
  (defcong nat-equiv equal (merge-8-u32s h3 h2 h1 h0 l3 l2 l1 l0) 7)
  (defcong nat-equiv equal (merge-8-u32s h3 h2 h1 h0 l3 l2 l1 l0) 8)

  (defthm unsigned-byte-p-256-of-merge-8-u32s
    (implies (and (unsigned-byte-p 32 h3)
                  (unsigned-byte-p 32 h2)
                  (unsigned-byte-p 32 h1)
                  (unsigned-byte-p 32 h0)
                  (unsigned-byte-p 32 l3)
                  (unsigned-byte-p 32 l2)
                  (unsigned-byte-p 32 l1)
                  (unsigned-byte-p 32 l0))
             (unsigned-byte-p 256 (merge-8-u32s h3 h2 h1 h0 l3 l2 l1 l0)))))


;; Merging Qwords -------------------------------------------------------------

(define merge-2-u64s (h l)
  (declare (type (unsigned-byte 64) h l))
  :returns (result natp :rule-classes :type-prescription)
  :short "Concatenate two 64-bit values together to form a single 128-bit
result."
  :inline t
  (mbe :logic
       (logior (ash (nfix h) 64)
               (nfix l))
       :exec
       (the (unsigned-byte 128)
         (logior (the (unsigned-byte 128)
                   (ash (the (unsigned-byte 64) h)
                        64))
                 (the (unsigned-byte 64)
                   l))))

  ///
  (defcong nat-equiv equal (merge-2-u64s h l) 1)
  (defcong nat-equiv equal (merge-2-u64s h l) 2)
  (defthm unsigned-byte-p-128-of-merge-2-u64s
    (implies (and (unsigned-byte-p 64 h)
                  (unsigned-byte-p 64 l))
             (unsigned-byte-p 128 (merge-2-u64s h l)))))

(define merge-4-u64s (h1 h0 l1 l0)
  (declare (type (unsigned-byte 64) h1 h0 l1 l0))
  :returns (result natp :rule-classes :type-prescription)
  :short "Concatenate four 64-bit values together to form a single 256-bit
result."
  :guard-hints(("Goal" :in-theory (enable merge-2-u64s)))
  (mbe :logic
       (logior (ash (nfix h1) (* 3 64))
               (ash (nfix h0) (* 2 64))
               (ash (nfix l1) (* 1 64))
               (nfix l0))
       :exec
       (b* (((the (unsigned-byte 128) high) (merge-2-u64s h1 h0))
            ((the (unsigned-byte 128) low)  (merge-2-u64s l1 l0)))
         (the (unsigned-byte 256)
              (logior
               (the (unsigned-byte 256) (ash (the (unsigned-byte 128) high) 128))
               (the (unsigned-byte 128) low)))))
  ///
  (defcong nat-equiv equal (merge-4-u64s h1 h0 l1 l0) 1)
  (defcong nat-equiv equal (merge-4-u64s h1 h0 l1 l0) 2)
  (defcong nat-equiv equal (merge-4-u64s h1 h0 l1 l0) 3)
  (defcong nat-equiv equal (merge-4-u64s h1 h0 l1 l0) 4)
  (defthm unsigned-byte-p-256-of-merge-4-u64s
    (implies (and (unsigned-byte-p 64 h1)
                  (unsigned-byte-p 64 h0)
                  (unsigned-byte-p 64 l1)
                  (unsigned-byte-p 64 l0))
             (unsigned-byte-p 256 (merge-4-u64s h1 h0 l1 l0)))))
