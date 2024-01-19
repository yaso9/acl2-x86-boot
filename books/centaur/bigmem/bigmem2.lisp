; Big Memory, Model 2
; Copyright (C) 2024, Intel Corporation

; Contact
;   Intel Corporation, ACL2 Formal Verification Group
;   1300 South MoPac Expy,  Austin, TX  78746, USA
;   https://www.intel.com/

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

;   Original Author(s): Warren A. Hunt, Jr <warren.hunt@intel.com>

; For development:
; (ld "bigmem2.lisp" :ld-pre-eval-print t)

(in-package "BIGMEM")
; (include-book "misc/disassemble" :dir :system :ttags (:disassemble$))
(include-book "std/util/define"  :dir :system)
(include-book "xdoc/top"         :dir :system)

(defxdoc bigmem2
  :pkg "BIGMEM"
  :parents (acl2::projects)
  :short "A byte memory model that is logically a record but provides array-like
  performance for a (low-address) region of memory and hash
  table lookup and update for memory modeled above a certain address limit."

  :long "<p>The @('bigmem2') library takes its inspriation from the @('bigmem')
   library, but provides a simpler implementation that operates faster than
   @('bigmem') when addresses are below some limit and operates more slowly
   when equal to or above this same address limit.  The intended use of this
   memory model is to provide a physical-memory model for the ACL2 x86-ISA
   model.</p>

  <p>This books define an abstract STOBJ called @('mem') that exports an
  accessor function @('read-mem') and an updater function @('write-mem') --
  just like @('bigmem'), library @('mem') models a byte memory of arbitrary
  size.  The corresponding concrete STOBJ for the @('bigmem2') @('mem') is
  composed of two fields: an array of bytes addressed by natural numbers
  smaller than a threshold and a hashtable that writes-and-reads bytes on
  demand.</p>

  <p>An obvious application of @('bigmem2') is to model a byte-wide memory;
  @('mem2') can be used as a child STOBJ to define a field representing a byte
  memory in a parent stobj that models some machine's state.  See
  @('projects/x86isa/machine/state.lisp') for one such@('bigmem') example.</p>")

;; ----------------------------------------------------------------------



; (include-book "std/lists/repeat" :dir :system)
; (local (include-book "centaur/bitops/signed-byte-p" :dir :system))
; (local (include-book "centaur/bitops/ihs-extensions" :dir :system))

; !!! Figure out next line...

; (local (xdoc::set-default-parents bigmem))

(defun formal-force-list (x)
 (if (atom x)
     nil
   (cons `(force ,(car x))
         (formal-force-list (cdr x)))))

(defmacro fand (&rest x)
 `(and ,@(formal-force-list x)))

; (defn ubp8-fix (x) (acl2::loghead 8 (ifix x)))

(defmacro !nth (key val l)
 `(update-nth ,key ,val ,l))

(add-macro-fn !nth update-nth)  ;; UPDATE-NTH shown as !NTH


;; Rules about NTH and !NTH

(defthm !nth-nth
  (implies (< (nfix ma) (len l))
           (equal (!nth ma (nth ma l) l)
                  l)))

(defthm nth-!nth
  ;; Redundant with NTH-UPDATE-NTH
  (equal (nth ma1 (!nth ma2 v l))
         (if (equal (nfix ma1) (nfix ma2))
             v
           (nth ma1 l))))

; (in-theory (disable update-nth))

(defthm !nth-!nth-same-address
  (implies (equal a1 a2)
           (equal (!nth a1 v (!nth a2 w st))
                  (!nth a1 v st))))

(defthm !nth-!nth-different-addresses
  (implies (not (equal (nfix a1) (nfix a2)))
           (equal (!nth a1 v1 (!nth a2 v2 st))
                  (!nth a2 v2 (!nth a1 v1 st)))))

(defthm yet-another-fact-about-!nth
  (equal (!nth @i e (cons x a))
         (if (zp @i)
             (cons e a)
           (cons x (!nth (- @i 1) e a))))
  :hints
  (("Goal"
    :in-theory (enable !nth))))

;; Rules about HONS-ASSOC-EQUAL
(defthm hons-assoc-equal-fact
  (implies (and (natp a1)
                (natp a2))
           (equal (hons-assoc-equal a1 (cons (cons a2 v) l))
                  (if (equal a1 a2)
                      (cons a2 v)
                    (hons-assoc-equal a1 l)))))

(defconst *mem-size* (expt 2 20)) ; For MEM just below
(defconst *htb-size* (expt 2 10)) ; For MEM just below

(defstobj mem
  (m :type (array (unsigned-byte 8)  ; array of bytes (8-bit natural numbers)
                  (*mem-size*))      ; with this length
     :initially 0
     :resizable nil)

  (mh :type (hash-table eql
                        10000 ;; (expt 2 10) ;; *htb-size*
                        (unsigned-byte 8))
      :initially 0)

  :inline t
  :non-memoizable t
  :renaming
  ((update-mi !mi)
   (m-length ml)
   (mh-get mhi)
   (mh-put !mhi)))


(encapsulate
  ()

  ;; MEM field read type lemmas

  (local
   (defthm natp-nth-of-m ; Needed when TAU system engaged?
     (implies (and (mp x)
                   ;; Want (NATP a) because :type-prescription rules relieved
                   ;; by type reasoning alone.
                   (natp a)
                   ;; Want (FORCE (< a (len x))) because we may eventually want
                   ;; rewriting to assist with relieving this next hypothesis.
                   (force (< a (len x))))
              (natp (nth a x)))
     :hints (("Goal" :induct (nth a x)))
     :rule-classes ((:type-prescription
                     ;; Explicit designation of typed term
                     :typed-term (nth a x))
                    ;; Won't be used for rewriting unless NATP disabled.
                    :rewrite)))

  (local
   (defthm nth-of-m-is-n08p ; Needed when TAU system engaged?
     (implies (and (mp x)
                   (force (< a (len x))))
              (and (<= 0 (nth a x))
                   (< (nth a x) 256)))
     :hints (("Goal" :induct (nth a x)))
     :rule-classes :linear))

  (defthm mi-type-forced
    (implies (fand (memp mem)
                   (natp a)
                   (< a (ml mem)))
             (natp (mi a mem)))
    :hints (("Goal" :in-theory (e/d (mi) ())))
   :rule-classes (:rewrite :type-prescription))

  (defthm mi-of-m-is-n08p
    (implies (and (memp mem)
                  (natp a)
                  (< a (ml mem)))
             (and (<= 0 (mi a mem))
                  (< (mi a mem) 256)))
    :hints (("Goal" :cases ((< (nfix a) (ml mem)))))
    ;; :rule-classes (:linear :rewrite)
    :rule-classes :linear)

;; I need all of the read-over-read, and read-over-write lemmas
;; see:  ~/f/research/Big-Memory/mem15.lisp

;; And, then I need to prove the read-over-read for different fields.
;; Shilpi has a general macro, but I need to get things straight in
;; my head.


  (local
   (defthm val-of-alist-is-natp
     (implies (and (mhp alst)
                   (hons-assoc-equal key alst))
              (natp (cdr (hons-assoc-equal key alst))))
     :rule-classes :type-prescription))

  (local
   (defthm val-of-alist-is-byte
     (implies (and (mhp alst)
                   (hons-assoc-equal key alst))
              (and (<= 0 (cdr (hons-assoc-equal key alst)))
                   (< (cdr (hons-assoc-equal key alst)) 256)))
     :rule-classes :linear))

  (defthm val-of-mh-get-natp
    (implies
     ;; FORCE in case rewriter is needed to relieve this hypothesis
     (force (memp mem))
     (natp (mhi a mem)))
    :rule-classes :type-prescription)

  (defthm val-of-mh-get-linear
    (implies (memp mem)
             (and (<= 0 (mhi a mem))
                  (< (mhi a mem) 256)))
    :rule-classes :linear)


  ;; Read-over-read lemmas


  ;; Read-over-write lemmas

  (defthm mi-!mi-same-or-different-addresses
    ;; I don't understand the ``ACL2 Warning [Subsume] in''
    (equal (mi a1 (!mi a2 v mem))
           (if (equal (nfix a1) (nfix a2))
               v
             (mi a1 mem))))

  (defthm mhi-!mhi-same-or-different-addresses
    ;; I don't understand the ``ACL2 Warning [Subsume] in''
    (equal (mhi a1 (!mhi a2 v mem))
           (if (equal a1 a2)
               v
             (mhi a1 mem))))

  (defthm mi-!mhi
    (equal (mi a1 (!mhi a2 v mem))
           (mi a1 mem)))

  (defthm mhi-!mi
    (equal (mhi a1 (!mi a2 v mem))
           (mhi a1 mem)))


  ;; Write lemmas type lemmas

  (local
   (defthm mp-!nth-of-m ; Needed when TAU system engaged?
     (implies (and (mp x)
                   (natp v)
                   (< v 256)
                   ;; Need FORCE so next lemma is proven
                   (force (< (nfix a) (len x))))
              (mp (!nth a v x)))
     :hints
     (("Goal"
       :induct (!nth a v x)
       :in-theory (enable update-nth)))))

  (defthm memp-!mi
    (implies (and (memp mem)
                  (natp v)
                  (< v 256)
                  ;; Should I use FORCE on the next hypothesis?
                  (< (nfix a) (ml mem)))
             (memp (!mi a v mem))))

  (defthm memp-!mhi
    ;; Don't need helper lemma.
    (implies (and (memp mem)
                  (natp a)
                  (natp v)
                  (< v 256))
             (memp (!mhi a v mem))))


  ;; Write-over-write lemmas

  (defthm !mi-!mi-same-addresses
    (implies (equal a1 a2)
             (equal (!mi a1 v (!mi a2 w mem))
                    (!mi a1 v mem))))

  (defthm !mi-!mi-different-addresses
    (implies (not (equal (nfix a1) (nfix a2)))
             (equal (!mi a1 v1 (!mi a2 v2 mem))
                    (!mi a2 v2 (!mi a1 v1 mem)))))


  ;; M update lemmas

  ; MI field


  (defthm mi-!mi-same-addresses
    ;; Redundant with MI-!MI-SAME-OR-DIFFERENT-ADDRESSES (above)
    ;; Uses :rewrite NTH-UPDATE-NTH
    (implies (equal a1 a2)
             (equal (mi a1 (!mi a2 v mem))
                    v)))

  (defthm mi-!mi-different-addresses
    ;; Redundant with MI-!MI-SAME-OR-DIFFERENT-ADDRESSES (above)
    ;; Uses :rewrite NTH-UPDATE-NTH
    (implies (not (equal (nfix a1) (nfix a2)))
             (equal (mi a1 (!mi a2 v mem))
                    (mi a1 mem)))
    :hints
    (("Goal" :in-theory (disable mi !mi))))


  (defthm !mi-mi
    (implies (and (memp mem)
                  (< (nfix a) (ml mem))
                  (equal v (mi a mem)))
             (equal (!mi a v mem)
                    mem))
    :hints
    (("Goal" :in-theory (e/d () (!nth-!nth-same-address))
             :use ((:instance !nth-nth
                              (ma a)
                              (l (car mem)))))))

  ; MH field

  (defthm mhi-!mhi-same-address
    (implies (equal a1 a2)
             (equal (mhi a1 (!mhi a2 v mem))
                    v)))

  (defthm mhi-!mhi-different-addresses
    (implies (not (equal (nfix a1) (nfix a2)))
             (equal (mhi a1 (!mhi a2 v mem))
                    (mhi a1 mem))))

#|
  (defthm !mhi-mhi
    ;; Invalid because of new CONS pair at front of MH field
    (implies (and (memp mem)
                  (equal v (mhi a mem)))
             (equal (!mhi a v mem)
                    mem)))

  (defthm !mhi-!mhi-different-address
    ;; This isn't true because the MH field of MEM is extended.
    (implies (not (equal (nfix a1) (nfix a2)))
             (equal (!mi a1 v1 (!mi a2 v2 mem))
                    (!mi a2 v2 (!mi a1 v1 mem)))))
|#

)

(in-theory (disable mhp mi !mi mhi !mhi))


(define read-mem ((a natp)
                  (mem memp))
  :inline t
  (if (< a (ml mem))
      (mi a mem)
    (mhi a mem))
  ///
  (defthm natp-read-mem
      (implies (and (natp a)
                    (memp mem))
               (natp (read-mem a mem)))
    :rule-classes :type-prescription)

  (defthm read-mem-in-range
    (implies (and (natp a)
                  (memp mem))
             (and (<= 0 (read-mem a mem))
                  (< (read-mem a mem) 256)))))

; Run down why I don't need the two lemmas above.  It appears that the lemma
; below is proved directly from the lemmas in the encapsulate above.

; !!! Now I do need the two lemmas above!!!

(defthm unsigned-byte-p-8-read-mem
  (implies (and (natp a)
                (memp mem))
           (unsigned-byte-p 8 (read-mem a mem)))
  :hints
  (("Goal" :in-theory (e/d () ; (read-mem)
                           (memp mp mi)))))


(define write-mem ((a natp)
                   (v (unsigned-byte-p 8 v))
                   (mem memp))
  :inline t
  (if (< a (ml mem)) ; For ``#.*mem-size*'' define constant before this file processed
      (!mi a v mem)
    (!mhi a v mem))
  ///
  (defthm memp-write-mem
    (implies (and (natp a)
                  (natp v)
                  (< v 256)
                  (memp mem))
             (memp (write-mem a v mem)))))

(defthm read-mem-write-mem-same-address
  (implies (equal a1 a2)
           (equal (read-mem a1 (write-mem a2 v mem))
                  v))
  :hints
  (("Goal" :in-theory (e/d (read-mem write-mem) ()))))


(defthm read-mem-write-mem-different-address
  (implies (not (equal (nfix a1) (nfix a2)))
           (equal (read-mem a1 (write-mem a2 v mem))
                  (read-mem a1 mem)))
  :hints
  (("Goal" :in-theory (e/d (read-mem write-mem) ()))))


(in-theory (disable memp))

(defthm read-mem-over-write-mem
  ;; This lemma is redundant with the two lemmas just above.
  (implies (and (natp a1) (natp a2))
           (equal (read-mem a1 (write-mem a2 val mem))
                  (if (equal a1 a2)
                      val
                    (read-mem a1 mem))))
  :hints
  (("Goal" :in-theory (e/d (read-mem write-mem) ()))))


:i-am-here



;!!! BIG Problem!!!

; Here, because of our attempt to use an ACL2 STOBJ Hash Table, we find
; ourselves not being able to prove the lemmas below.  We need to prove all of
; the read-over-write lemmas for the STOBJ.

; But, this is where using a hash-table memory makes us "crazy."  Because of
; the semantics that ACL2 provides for a hash table, we find that even writing
; the same value to the same memory causes the memory to change.  So, we are
; going to back up and start over with a different formalization for the
; high-address memory.


(defthm write-mem-shadow-writes
  (equal (write-mem a v1 (write-mem a v2 mem))
         (write-mem a v1 mem))
  :hints (("Goal" :in-theory (e/d (write-mem) ()))))

(defthm write-mem-commute-safely
  (implies (not (equal a2 a1))
           (equal (write-mem a2 val-2 (write-mem a1 val-1 mem))
                  (write-mem a1 val-1 (write-mem a2 val-2 mem)))))

(defthm write-the-read
  (equal (write-mem addr (read-mem addr mem) mem)
         mem))


; Minor irritation lemmas

; This next conjecture, proven in the "bigmem.lisp" isn't true with the memory
; we have defined above.  In any event, this seems like a degenerative case,
; which we hope we can avoid needing to address.

#|
(defthm read-mem-from-nil
  (equal (read-mem i nil) 0))
|#

; This
(include-book "ihs/basic-definitions" :dir :system)

(encapsulate
  ()

  (local (include-book "arithmetic-5/top"      :dir :system))

  (defthmd loghead-identity-alt
   (implies (unsigned-byte-p n val)
            (equal (acl2::loghead n (ifix val))
                   val))))

(in-theory (e/d () (read-mem write-mem create-mem)))


(encapsulate
 ()

 ;; Some arithmetic facts...

 (local (include-book "arithmetic-5/top" :dir :system))

 (local
  (defun ind-hint-2 (x y)
    (if (or (zp x) (zp y))
        42
      (ind-hint-2 (floor x 2) (floor y 2)))))

 (defthm logxor-greater-or-equal-to-zero
   ;; (NATP (LOGXOR x y))
   (implies (and (natp x) (natp y))
            (and (integerp (logxor x y))
                 (<= 0 (logxor x y))
                 ;; (integerp (logxor y x))
                 ;; (<= 0 (logxor y x))
                 ))

   :hints (("Goal" :induct (ind-hint-2 x y)))
   :rule-classes :type-prescription)

 (local
  (defun ind-hint-3 (x y n)
    (if (or (zp x) (zp y) (zp n))
        42
      (ind-hint-3 (floor x 2) (floor y 2) (+ -1 n)))))

 (local
  (defthm break-logxor-apart
    (implies (and (natp x)
                  (natp y))
             (equal (logxor x y)
                    (+ (* 2 (logxor (floor x 2)
                                    (floor y 2)))
                       (logxor (mod x 2)
                               (mod y 2)))))
    :rule-classes nil))

 ;; This next rule would be a weird rewrite rule because of the (EXPT
 ;; 2 N) in the conclusion.  As a linear rule, then entire conclusion
 ;; doesn't need to match.

 (local
  (defthm logxor-<=-expt-2-to-n
      (implies (and (natp x) (natp y)
                    (< x (expt 2 n))
                    (< y (expt 2 n)))
               (< (logxor x y) (expt 2 n)))

    :hints (("Goal" :induct (ind-hint-3 x y n))
            ("Subgoal *1/2.6'4'" :use ((:instance break-logxor-apart)))
            ("Subgoal *1/2.10'4'" :use ((:instance break-logxor-apart))))
    :rule-classes :linear))

 ;; Yahya notes that the "ihs-extensions.lisp" book provides a better (or, at
 ;; least, supported) method for doing the kind of thing this code does
 ;; crudely.

  (defthm logxor-two-bytes
      (implies (and (natp x)
                    (< x 256)
                    (natp y)
                    (< y 256))
               (and (<= 0 (logxor x y))
                    (< (logxor x y) 256)))
    :hints
    (("Goal"
      :use ((:instance logxor-<=-expt-2-to-n
                       (x x) (y y) (n 8))))))
  )

(define xor-mem-region ((n   :type (unsigned-byte 50))
                        (sum :type (unsigned-byte 8))
                        (mem memp))
  :prepwork ((local (in-theory (e/d (unsigned-byte-p) (logxor)))))
  (if (mbe :logic (zp n)
           :exec (= n 0))
      mem
    (b* ((val (the (unsigned-byte 8) (read-mem n mem)))
         (xor-sum (logxor (the (unsigned-byte 8) val)
                          (the (unsigned-byte 8) sum))))
      (xor-mem-region (the (unsigned-byte 50) (1- n))
                      (the (unsigned-byte  8) xor-sum)
                      mem))))

; (include-book "misc/disassemble" :dir :system :ttags (:disassemble$))
; (time$ (xor-mem-region (1- (expt 2 30)) 0 mem))
