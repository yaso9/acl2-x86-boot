; A lightweight book about the built-in function prin1-with-slashes1
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "princ-dollar"))
(local (include-book "kestrel/utilities/channels" :dir :system))

(in-theory (disable prin1-with-slashes1
                    ;; So the rules in this file will fire:
                    open-output-channel-p
                    open-output-channel-p1))

(defthm state-p1-of-prin1-with-slashes1
  (implies (and (state-p1 state)
                (symbolp channel)
                (open-output-channel-p channel :character state))
           (state-p1 (prin1-with-slashes1 l slash-char channel state)))
  :hints (("Goal" :in-theory (enable prin1-with-slashes1))))

(defthm state-p-of-prin1-with-slashes1
  (implies (and (state-p state)
                (symbolp channel)
                (open-output-channel-p channel :character state))
           (state-p (prin1-with-slashes1 l slash-char channel state)))
  :hints (("Goal" :in-theory (enable state-p))))

(defthm open-output-channel-p1-of-prin1-with-slashes1
  (implies (and (symbolp channel)
                (open-output-channel-p1 channel :character state))
           (open-output-channel-p1 channel :character (prin1-with-slashes1 l slash-char channel state)))
  :hints (("Goal" :in-theory (enable prin1-with-slashes1))))

(defthm open-output-channel-p-of-prin1-with-slashes1
  (implies (and (symbolp channel)
                (open-output-channel-p channel :character state))
           (open-output-channel-p channel :character (prin1-with-slashes1 l slash-char channel state)))
  :hints (("Goal" :in-theory (enable open-output-channel-p))))
