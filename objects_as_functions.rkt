#lang plait #:untyped
(print-only-errors #t)

; Basic parser with objects implemented using functions

(define-syntax-rule
  (object%
    self
    [name value] ...)
  (λ (self)
    (λ (msg)
      (cond
        [(eq? msg 'name)
         value]
        ...
        [else
         (error 'object/self "message not recognized")]))))

(define-syntax-rule
  (dot o-exp msg)
  (let ([o o-exp])
    ((o o) 'msg)))

(define (addO%) 
  (object%
    self
    [interp +]))

(define (subO%)
  (object%
    self
    [interp -]))

(define (mulO%)
  (object%
    self
    [interp *]))

(define (numE% value)
  (object%
    self
    [subst
      (lambda (id exp) 
        self)]
    [interp
      value]))

(define (ideE% id₀)
  (object%
    self
    [subst 
      (lambda (id exp) 
        (if (eq? id id₀)
          exp
          self))]
    [interp
      (error 'ideE% "Unbound identifier")])) ; something went wrong with substitution

(define (binE% op lhs rhs)
  (object% 
    self 
    [subst
      (lambda (id exp) 
        (binE% 
          op 
          ((dot lhs subst) id exp) 
          ((dot rhs subst) id exp)))]
    [interp 
      ((dot op interp) 
        (dot lhs interp) 
        (dot rhs interp))]))

(define (if0E% tst thn els)
  (object% 
    self 
    [subst
      (lambda (id exp) 
        (if0E% 
          ((dot tst subst) id exp) 
          ((dot thn subst) id exp) 
          ((dot els subst) id exp)))]
    [interp 
      (if (zero? (dot tst interp))     
        (dot thn interp)
        (dot els interp))]))

(define (letE% id₀ bind-exp body-exp)
  (object% 
    self 
    [subst
      (lambda (id exp) 
        (letE% 
          id₀
          ((dot bind-exp subst) id exp) 
          ((dot body-exp subst) id exp)))]
    [interp 
      (dot ((dot body-exp subst) id₀ bind-exp) interp)]))

(define (parse-op s)
  (cond
    [(s-exp-match? `+ s)
      (addO%)]
    [(s-exp-match? `- s)
      (subO%)]
    [(s-exp-match? `* s)
      (mulO%)]
    [else
      (error 'parse "unrecognized operator")]))

(define (seref* pp ss fail)
  (type-case (Listof S-Exp) pp
    [empty
     (type-case (Listof S-Exp) ss
        [empty (none)]
        [(cons _₀ _₁) (fail)])]
    [(cons p pp)
     (type-case (Listof S-Exp) ss
        [empty (fail)]
        [(cons s ss)
          (type-case (Optionof S-Exp) (seref p s fail)
            [(some s) (some s)]
            [(none) (seref* pp ss fail)])])]))

(seref : (S-Exp S-Exp (-> 'a) -> (Optionof S-Exp)))
(define (seref p s fail)
  (cond
    [(s-exp-match? `• p)
      (some s)]
    [(s-exp-match? `_ p)
      (none)]
    [(equal? p s)
      (none)]
    [(s-exp-list? p)
      (if (s-exp-list? s)
        (let ([pp (s-exp->list p)]
              [ss (s-exp->list s)])
          (seref* pp ss fail))
        (fail))]
    [else
      (fail)]))

(define (s-exp-ref p s)
  (let ([fail (λ ()
                (error
                 's-exp-ref
                 (string-append
                  "bad reference "
                  (string-append
                   (to-string p)
                   (string-append
                    " in "
                    (to-string s))))))])
    (type-case (Optionof S-Exp) (seref p s fail)
    [(some s) s]
    [(none) (fail)])))


(parse : (S-Exp -> Expr))
(define (parse s)
  (cond
    [(s-exp-match? `NUMBER s)
      (numE% (s-exp->number s))]
    [(s-exp-match? `SYMBOL s)
      (ideE% (s-exp->symbol s))]
    [(s-exp-match? `(if0 ANY ANY ANY) s)
      (if0E% (parse (s-exp-ref `(if0 • _ _) s))
            (parse (s-exp-ref `(if0 _ • _) s))
            (parse (s-exp-ref `(if0 _ _ •) s)))]
    [(s-exp-match? `(let ([SYMBOL ANY]) ANY) s)
      (letE% (s-exp->symbol (s-exp-ref `(let ([• _]) _) s))
            (parse         (s-exp-ref `(let ([_ •]) _) s))
            (parse         (s-exp-ref `(let ([_ _]) •) s)))]
    [(s-exp-match? `(ANY ANY ANY) s)
      (binE% (parse-op (s-exp-ref `(• _ _) s))
            (parse    (s-exp-ref `(_ • _) s))
            (parse    (s-exp-ref `(_ _ •) s)))]
    [else
      (error 'parse "unrecognized expression")]))

(define (interp* s)
  (dot (parse s) interp))

(test (interp* `5) 5)
(test (interp* `(+ 2 2)) 4)
(test (interp* `(- 3 1)) 2)
(test (interp* `(if0 (- 4 4) 10 7)) 10)
(test (interp* `(if0 (- 4 2) 10 7)) 7)
(test (interp* `(let ([x 12]) x)) 12)
(test (interp* `(let ([x 12])
                  (if0 (- x x) 10 7)))
      10)
(test (interp* `(let ([x 12])
                  (let ([x x])
                    (if0 (- x x) 10 7))))
      10)
(test/exn (interp* `y) "")
(test (interp* `(let ([x 12])
                  (let ([y x])  
                    (let ([z 2]) 
                      (- x z))))) 10)
(test (interp* `(let ([x 12])
                  (let ([y x])  
                    (let ([z 2]) 
                      (+ 
                        (- x z) 
                        (- y x)))))) 
      10)
