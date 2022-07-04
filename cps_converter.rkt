#lang plait #:untyped
(print-only-errors #t)

; Fancy macros to convert Plait interpretation to Continuation-Passing Style (CPS)

(define-syntax cpser
  (syntax-rules (λ lambda let letrec set! begin if quote)
    ; λ (first-class functions)
    [(cpser (λ (x) body-e))
     (λ (passed-callback) 
      (passed-callback
        (λ (x new-passed-callback) 
          ((cpser body-e) new-passed-callback))))]
    ; let
    [(cpser (let ([identifier expr-0]) expr-1))
     (λ (passed-callback)
       ((cpser expr-0)
        (λ (identifier) ((cpser expr-1) passed-callback))))]
    ; letrec, done for you, assume you do let, set!, and begin correctly
    [(cpser (letrec ([f expr-0]) expr-1))
     (cpser (let ([f #f])
              (begin
                (set! f expr-0)
                expr-1)))]
    ; set!
    [(cpser (set! identifier expr))
     (λ (passed-callback)
      ((cpser expr)
        (λ (expr-val)
          (passed-callback (set! identifier expr-val)))))]
    ; begin
    [(cpser (begin expr-0 expr-1))
      (λ (passed-callback)
        (begin
          ((cpser expr-0) identity)
          ((cpser expr-1) passed-callback)))] 
    ; if
    [(cpser (if tst thn els))
     (λ (passed-callback)
       ((cpser tst)
        (λ (tst-val)
          (if tst-val
            ((cpser thn) passed-callback)
            ((cpser els) passed-callback)))))]
    ; quoted literals, done for you
    [(cpser 'e)
     (λ (passed-callback) (passed-callback 'e))]
    ; binary operations (like +, *, =
    [(cpser (operation expr-0 expr-1))
     (λ (passed-callback)
       ((cpser expr-0)
        (λ (val-0)
          ((cpser expr-1)
           (λ (val-1)
             (passed-callback (operation val-0 val-1)))))))] ; op/and-then
    ; unary function calls (that's all we handle with this)
    [(cpser (fun-expr param-e))
     (λ (passed-callback)
       ((cpser fun-expr)
        (λ (fun-val)
          ((cpser param-e)
           (λ (param-v)
             (fun-val param-v passed-callback))))))] ; mirror of (lambda) above
    ; atoms, such as variables and literals
    [(cpser x)
     (λ (passed-callback) (passed-callback x))])) 
(define (run cpsed)
  (cpsed (λ (x) x)))
(test (run (cpser 42)) 42)
(test (run (cpser "hello")) "hello")
(test (run (cpser #true)) #true)
(test (run (cpser (let ([x 42]) x))) 42)
(test (run (cpser (+ 10 12))) 22)
(test (run (cpser ((λ (x) x) 42))) 42)
(test (run (cpser (if #true 10 12))) 10)
(test (run (cpser (if ((λ (x) x) #true) 10 12))) 10)
(test (run (cpser (if ((λ (x) x) #true) (+ 4 6) 12))) 10)
(test (run (cpser (if ((λ (x) x) #true) (+ 4 6) (error 'oops "this shouldn't evaluate")))) 10)
(test/exn (run (cpser (if ((λ (x) x) #false) (+ 4 6) (error 'good "this should evaluate")))) "good")
(test (run (cpser (letrec ([fact (λ (n)
                                   (if (= n 0)
                                     1
                                     (* n (fact (- n 1)))))])
                    (fact 5))))
      120)