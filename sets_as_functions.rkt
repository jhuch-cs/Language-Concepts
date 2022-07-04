#lang plait

; Implementation of Sets as functions

(print-only-errors #t)

(define-type-alias (Set 'a) ('a -> Boolean))

(set-empty : (Set 'a))
(define set-empty (lambda (x) #f))

(set-member? : ('a (Set 'a) -> Boolean))
(define (set-member? x s) (s x))

(set-add : ('a (Set 'a) -> (Set 'a)))
(define (set-add x s) 
    (lambda (member?) 
        (or 
            (set-member? member? s) 
            (equal? x member?))))

(set-remove : ('a (Set 'a) -> (Set 'a)))
(define (set-remove x s) 
    (lambda (member?) 
        (and 
            (set-member? member? s) 
            (not (equal? x member?)))))

(set-union : ((Set 'a) (Set 'a) -> (Set 'a)))
(define (set-union s_0 s_1) 
    (lambda (member?)
        (or
            (set-member? member? s_0)
            (set-member? member? s_1))))

(set-intersect : ((Set 'a) (Set 'a) -> (Set 'a)))
(define (set-intersect s_0 s_1) 
    (lambda (member?)
        (and
            (set-member? member? s_0)
            (set-member? member? s_1))))

(set-difference : ((Set 'a) (Set 'a) -> (Set 'a)))
(define (set-difference s_0 s_1) 
    (lambda (member?)
        (and
            (set-member? member? s_1)
            (not (set-member? member? s_0)))))





; set-empty tests
(test (set-member? 1 set-empty) #f)
(test (set-member? "hello" set-empty) #f)


; set-add tests
(test (set-member? 1 (set-add 1 set-empty)) #t)
(test (set-member? 2 (set-add 1 set-empty)) #f)
(test (set-member? 1 (set-add 2 (set-add 1 set-empty))) #t)
(test (set-member? 2 (set-add 2 (set-add 1 set-empty))) #t)
(test (set-member? 2 (set-add 2 (set-add 2 set-empty))) #t)


; set-remove tests 
(test (set-member? 1 (set-remove 1 (set-add 1 set-empty))) #f)
(test (set-member? 2 (set-remove 1 (set-add 2 (set-add 1 set-empty)))) #t)
(test (set-member? 2 (set-remove 2(set-add 2 (set-add 2 set-empty)))) #f)


; set-union tests
(test (set-member? 1 (set-union (set-add 1 set-empty) set-empty)) #t)
(test (set-member? 1 (set-union (set-add 1 set-empty) (set-add 2 set-empty))) #t)
(test (set-member? 2 (set-union (set-add 1 set-empty) (set-add 2 set-empty))) #t)
(test (set-member? 1 (set-union (set-remove 1 (set-add 1 set-empty)) (set-add 2 set-empty))) #f)
(test (set-member? 2 (set-union (set-remove 1 (set-add 1 set-empty)) (set-add 2 set-empty))) #t)

; set-intersect tests
(test (set-member? 1 (set-intersect (set-add 1 set-empty) set-empty)) #f)
(test (set-member? 1 (set-intersect (set-add 1 set-empty) (set-add 2 set-empty))) #f)
(test (set-member? 1 (set-intersect (set-add 1 set-empty) (set-add 1 set-empty))) #t)
(test (set-member? 1 (set-intersect (set-remove 1 (set-add 1 set-empty)) (set-add 1 set-empty))) #f)
(test (set-member? 2 (set-intersect (set-remove 1 (set-add 1 set-empty)) (set-add 2 set-empty))) #f)


; set-difference tests
(test (set-member? 1 (set-difference set-empty (set-add 1 set-empty))) #t)
(test (set-member? 1 (set-difference (set-add 1 set-empty) (set-add 2 set-empty))) #f)
(test (set-member? 2 (set-difference (set-add 1 set-empty) (set-add 2 set-empty))) #t)
(test (set-member? 1 (set-difference (set-add 1 set-empty) (set-add 1 set-empty))) #f)
(test (set-member? 2 (set-difference (set-add 1 set-empty) (set-add 1 set-empty))) #f)
(test (set-member? 1 (set-difference (set-remove 1 (set-add 1 set-empty)) (set-add 1 set-empty))) #t)
(test (set-member? 1 (set-difference (set-remove 1 (set-add 1 set-empty)) (set-add 2 set-empty))) #f)
