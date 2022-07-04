#lang plait
(print-only-errors #t)

; Fancy macro to add generators to Plait interpretation

(define-syntax-rule
  (generator (my-yield x) expr)
  (let ([caller-k (lambda (v) (error 'generator "not called yet"))]) ; declared only to be re-assigned 
    (letrec ( [generator-k 
                (lambda (v) 
                  (let ([x v])
                    (begin
                      expr
                      (error 'generator "generator exhausted"))))]
              [my-yield 
                (lambda (v) 
                  (let/cc k
                      (begin
                        (set! generator-k k)
                        (caller-k v))))])
      (lambda (v) 
        (let/cc k
          (begin
            (set! caller-k k)
            (generator-k v)))))))

(test ((generator (yield x) (yield 10)) 1) 10)
(test ((generator (yield x) (yield x)) 1) 1)
(test ((generator (yield x) (yield (+ x 1))) 1) 2)

(test (let ([f (generator (yield x)
                (yield x))])
        (f 2))
      2)

(test (let ([f (generator (yield x)
                 (begin
                   (yield (+ x 0))
                   (yield (+ x 1))
                   (yield (+ x 2))))])
        (list (f 42) (f 42) (f 42)))
      (list 42 43 44))

(test/exn (let ([f (generator (yield x)
                     (begin
                       (yield (+ x 0))
                       (yield (+ x 1))
                       (yield (+ x 2))))])
            (list (f 42) (f 42) (f 42) (f 42)))
          "")

(define-syntax-rule
  (forever [x init-value] expr)
  (letrec ([loop (λ (x) (loop expr))])
    (loop init-value)))

(test (let ([count-from (generator (yield x)
                          (forever [y x]
                            (begin
                              (yield y)
                              (+ y 1))))])
        (list (count-from 42) (count-from 42) (count-from 42)))
      (list 42 43 44))

(define (f yield x)
  (begin
    (yield (+ x 0))
    (yield (+ x 1))
    (yield (+ x 2))
    (+ x 3)))

(test (let ([g (generator (yield x)
                 (begin
                   (yield x)
                   (let ([x (f yield (+ x 1))])
                     (yield x))))])
        (list (g 42) (g 42) (g 42) (g 42) (g 42)))
      (list 42 43 44 45 46))
