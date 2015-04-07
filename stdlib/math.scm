(define exact? integer?)
(define (inexact? x) "is inexact number" (and (real? x) (not (integer? x))))
(define (even? n) "is even" (= (remainder n 2) 0))
(define (odd? n) "is odd" (not (= (remainder n 2) 0)))
(define (zero? n) "is zero" (= n 0))
(define (positive? n) "is positive" (> n 0))
(define (negative? n) "is negative" (< n 0))
(define complex? number?)
(define (abs n) "absolute value of number" (if (>= n 0) n (- n)))
(define (exact->inexact n) "make inexact number from exact" (* n 1.0))
(define (hyper n) "get the nth hyper operator" 
  (curry (hyper_ n)))
(define (hyper_ n a b) "internal"
                  (if (= n 0)
                    (+ b 1)
                    (if (= b 0)
                      (if (= n 1)
                        a
                        (if (= n 2)
                          0
                          1))
                      ((hyper (- n 1)) a (hyper_ a (- b 1))))))
(define (<> n1 n2) "not equal" (not (= n1 n2)))

(define (succ x) "next number" (+ x 1))

(define (pred x) "previous number" (- x 1))

(define (gcd a b) "Greatest Common Divisor"
  (let ((aa (abs a))
    (bb (abs b)))
     (if (= bb 0)
          aa
          (gcd bb (remainder aa bb)))))

(define (lcm a b) "Least Common Multiple"
     (if (or (= a 0) (= b 0))
          0
          (abs (* (quotient a (gcd a b)) b))))
