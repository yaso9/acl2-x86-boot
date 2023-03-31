; A lightweight book about the built-in function print-object$
;
; Copyright (C) 2017-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "channels"))

(in-theory (disable print-object$))

(defthm open-output-channel-p-of-print-object$
  (implies (open-output-channel-p channel typ state)
           (open-output-channel-p channel typ (print-object$ x channel2 state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p
                                     print-object$
                                     open-output-channel-p1
                                 ;    open-output-channels
                                     open-output-channel-p))))

(defthm open-output-channel-p1-of-print-object$-gen
  (implies (open-output-channel-p1 channel typ state)
           (open-output-channel-p1 channel typ (print-object$ object channel2 state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p
                                     print-object$
                                     open-output-channel-p1
                                  ;   open-output-channels
                                     open-output-channel-p))))

;; Avoids name clash with std
(defthm state-p1-of-print-object$-alt
  (implies (and (state-p1 state)
                (open-output-channel-p channel :object state))
           (equal (state-p1 (print-object$ x channel state))
                  (symbolp channel)))
  :hints (("Goal" :in-theory (enable print-object$))))

(defthm state-p-of-print-object$
  (implies (and (state-p state)
                (open-output-channel-p channel :object state))
           (equal (state-p (print-object$ x channel state))
                  (symbolp channel)))
  :hints (("Goal" :in-theory (enable state-p))))

(defthm global-table-of-print-object$
  (equal (global-table (print-object$ x channel state))
         (global-table state))
  :hints (("Goal" :in-theory (enable print-object$))))
