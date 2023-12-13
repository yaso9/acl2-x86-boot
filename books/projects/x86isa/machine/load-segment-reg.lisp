(in-package "X86ISA")

(include-book "state")
(include-book "linear-memory")
(include-book "segmentation")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

;; ----------------------------------------------------------------------

;; This guard proof obligation is false.
;; (local
;;  (defthm-using-gl load-segment-reg-guard-helper-1
;;      :hyp (and (< selector 65536)                   
;;                (natp selector)                   
;;                (unsigned-byte-p 64 base-addr))
;;      :concl (<= -140737488355328
;;                 (+ (logand 65528 selector)
;;                    (logext 64 base-addr)))
;;      :g-bindings
;;      (gl::auto-bindings
;;       (:mix (:seq (:nat selector 16) (:skip 48)) (:nat base-addr 64)))
;;      :rule-classes :linear))

;; TODO make this throw the proper exceptions when you go past the limit on the GDT
;; TODO make it behave properly when the selector is 0
;; TODO add support for the other bits in the selector
;; Note: This is copied for system segment registers below. If this is updated
;; update that too. Also:
;; TODO unify normal and system segment registers
;; TODO handle failure reading descriptor
;; TODO check limits on the gdtr/ldtr
(skip-proofs (define load-segment-reg ((seg-reg natp)
                                       (selector natp)
                                       x86)
               :returns (x86 x86p)
               :guard (and (< seg-reg *segment-register-names-len*)              
                           (< selector #x10000))
               (b* ((cs (seg-visiblei *cs* x86))
                    (x86 (!seg-visiblei *cs* (!segment-selectorBits->rpl 0 cs) x86))
                    ((mv & descriptor x86)
                     (rml128 (+ (i64 (gdtr/idtrBits->base-addr
                                       (stri (if (logtest selector #x4)
                                               *ldtr*
                                               *gdtr*)
                                             x86)))
                                (logand selector #xFFF8))
                             :r x86))
                    (x86 (!seg-visiblei *cs* cs x86))
                    (x86 (!seg-visiblei seg-reg selector x86))
                    (limit (logior (logand descriptor #xFFFF)
                                   (logand (ash descriptor (- 16 48)) #xF0000)))
                    (x86 (!seg-hidden-limiti seg-reg limit x86))
                    (base (logior (logand (ash descriptor -16) #xFFFFFF)
                                  (logand (ash descriptor (- 24 56)) #xFFFFFFFFFF000000)))
                    (x86 (!seg-hidden-basei seg-reg base x86))
                    (attr (make-code-segment-attr-field (logand #xFFFFFFFFFFFFFFFF descriptor)))
                    (x86 (!seg-hidden-attri seg-reg attr x86)))
                   x86)))

 (skip-proofs
  (defun load-system-segment-reg (seg-reg selector x86)
    (declare (xargs :stobjs (x86)
                    :returns (x86 x86p)
                    :guard (and (integerp seg-reg)
                                (>= seg-reg 0)
                                (< seg-reg *segment-register-names-len*)
                                (integerp selector)
                                (>= selector 0)
                                (< selector #x10000))))
    (b* ((cs (seg-visiblei *cs* x86))
         (x86 (!seg-visiblei *cs* (!segment-selectorBits->rpl 0 cs) x86))
         (x86 (!ssr-visiblei seg-reg selector x86))
         ((mv & descriptor x86) (rml128 (+ (i64 (gdtr/idtrBits->base-addr (stri (if (logtest selector #x4)
                                                                                  *ldtr*
                                                                                  *gdtr*)
                                                                                x86)))
                                           (logand selector #xFFF8))
                                        :r x86))
         (x86 (!seg-visiblei *cs* cs x86))
         (limit (logior (logand descriptor #xFFFF)
                        (logand (ash descriptor (- 16 48)) #xF0000)))
         (x86 (!ssr-hidden-limiti seg-reg limit x86))
         (base (logior (logand (ash descriptor -16) #xFFFFFF)
                       (logand (ash descriptor (- 24 56)) #xFFFFFFFFFF000000)))
         (x86 (!ssr-hidden-basei seg-reg base x86))
         (attr (make-code-segment-attr-field (logand #xFFFFFFFFFFFFFFFF descriptor)))
         (x86 (!ssr-hidden-attri seg-reg attr x86)))
        x86)))
