(in-package "X86ISA")

;; ======================================================================

(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

;; ======================================================================

;; ======================================================================
;; INSTRUCTION: RDMSR
;; ======================================================================

(def-inst x86-rdmsr

          ;; Op/En: ZO
          ;; 0F 32

          :parents (two-byte-opcodes)

          :returns (x86 x86p :hyp (x86p x86))

          ;; Why do we need to enable msra? Why doesn't ACL2 appeal to
          ;; n64p-of-msra? We should ask Shilpi
          :guard-hints (("Goal" :in-theory (e/d* (msra) ())))

          :body

          (b* ((msr-addr (rr32 *ecx* x86))
               ((unless (valid-msr-addr-p msr-addr)) (!!fault-fresh :gp 0 :invalid-msr msr-addr))
               (msr-val (msra msr-addr x86))
               (x86 (wr32 *eax* (loghead 32 msr-val) x86))
               (x86 (wr32 *edx* (logtail 32 msr-val) x86))
               (x86 (write-*ip proc-mode temp-rip x86)))
              x86))

(def-inst x86-wrmsr

          ;; Op/En: ZO
          ;; 0F 30

          :parents (two-byte-opcodes)

          :returns (x86 x86p :hyp (x86p x86))

          :body

          (b* ((msr-addr (rr32 *ecx* x86))
               ((when (not (valid-msr-addr-p msr-addr))) (!!fault-fresh :gp 0 :invalid-msr msr-addr))
               (lower (rr32 *eax* x86))
               (upper (rr32 *edx* x86))
               (msr-val (logapp 32 lower upper))
               (x86 (!msra msr-addr msr-val x86))
               (x86 (write-*ip proc-mode temp-rip x86)))
              x86))
