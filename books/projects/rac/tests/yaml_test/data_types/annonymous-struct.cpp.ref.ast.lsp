

(funcdef foo () (block (declare a ()) (assign a (as (quote w) (as (quote a) 3 (ag (quote w) a)) a)) (assign a (as (quote w) (as (quote b) 4 (ag (quote w) a)) a)) (return (+ (ag (quote a) (ag (quote w) a)) (ag (quote b) (ag (quote w) a))))))
