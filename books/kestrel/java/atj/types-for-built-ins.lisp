; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "types-for-natives")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file proves and records ATJ types (see the file types.lisp)
; for some ACL2 (non-primitive) built-in functions;
; more can be added as needed.
; ATJ types for the ACL2 primitive functions are in types-for-natives.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-atj-function-type mv-nth (:integer :value) :value)

(def-atj-function-type not (:value) :symbol)

(def-atj-function-type zp (:integer) :symbol)