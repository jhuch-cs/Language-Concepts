#lang plait
(print-only-errors #t)

; Basic language implementation with exceptions and try-catch in CPS

#|
expr ::= number
       | x
       | (+ expr expr)
       | (/ expr expr) 
       | (if0 expr expr expr)
       | (let ([x expr]) expr)
       | (app expr expr)
       | (throw)
       | (try e e) 
|#

(define-type Expr
  (numE [value : Number])
  (ideE [name : Symbol])
  (addE [lhs : Expr]
        [rhs : Expr])
  (divE [lhs : Expr]
        [rhs : Expr])
  (if0E [tst : Expr]
        [thn : Expr]
        [els : Expr])
  (letE [name : Symbol]
        [bound-expr : Expr]
        [body-expr : Expr])
  (appE [function : Expr]
        [argument : Expr])
  (funE [param : Symbol]
        [body : Expr])
  (throwE)
  (tryE [body-exp : Expr]
        [handle-exp : Expr]))

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


(define (parse s)
  (cond
    [(s-exp-match? `NUMBER s)
     (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s)
     (ideE (s-exp->symbol s))]
    [(s-exp-match? `(+ ANY ANY) s)
     (addE (parse (s-exp-ref    `(+ • _) s))
           (parse (s-exp-ref    `(+ _ •) s)))]
    [(s-exp-match? `(/ ANY ANY) s)
     (divE (parse (s-exp-ref    `(/ • _) s))
           (parse (s-exp-ref    `(/ _ •) s)))]
    [(s-exp-match? `(if0 ANY ANY ANY) s)
     (if0E (parse (s-exp-ref `(if0 • _ _) s))
           (parse (s-exp-ref `(if0 _ • _) s))
           (parse (s-exp-ref `(if0 _ _ •) s)))]
    [(s-exp-match? `(app ANY ANY) s)
     (appE (parse (s-exp-ref `(app • _) s))
           (parse (s-exp-ref `(app _ •) s)))]
    [(s-exp-match? `(let ([SYMBOL ANY]) ANY) s)
     (letE (s-exp->symbol (s-exp-ref `(let ([• _]) _) s))
           (parse (s-exp-ref         `(let ([_ •]) _) s))
           (parse (s-exp-ref         `(let ([_ _]) •) s)))]
    [(s-exp-match? `(fun (SYMBOL) ANY) s)
     (funE (s-exp->symbol (s-exp-ref `(fun (•) _) s))
           (parse         (s-exp-ref `(fun (_) •) s)))]
    [(s-exp-match? `(throw) s)
     (throwE)]
    [(s-exp-match? `(try ANY ANY) s)
     (tryE (parse (s-exp-ref `(try • _) s))
           (parse (s-exp-ref `(try _ •) s)))]
    [else
     (error 'parse (string-append "not in language" (to-string s)))]))

(define-type-alias Env (Hashof Symbol Value))

(env-empty : Env)
(define env-empty (hash empty))

(env-extend : (Symbol Value Env -> Env))
(define (env-extend x l env)
  (hash-set env x l))

(env-lookup : (Symbol Env -> Value))
(define (env-lookup x env)
  (type-case (Optionof Value) (hash-ref env x)
    [(some l)
     l]
    [(none)
     (error 'interp "unbound identifier")]))

(define-type Value
  (numV [value : Number])
  (funV [f : (Value (Value -> 'a) ( -> 'a) -> 'a)]))

(wrap-op : (Symbol (Number Number (Number -> 'a) ( -> 'a) -> 'a) ( -> 'a) -> (Value Value (Value -> 'a) -> 'a)))
(define (wrap-op who val-k err-k)
  (λ (v₀ v₁ k)
    (type-case Value v₀
      [(numV n₀)
       (type-case Value v₁
         [(numV n₁)
          (val-k n₀ n₁ (λ (n) (k (numV n))) err-k)]
         [else
          (err-k)])]
      [else
       (err-k)])))

(interp : (Expr Env (Value -> 'a) ( -> 'a) -> 'a))
(define (interp exp env k err-k)
  (type-case Expr exp
    [(numE n)
     (k (numV n))]
    [(ideE x)
     (k (env-lookup x env))]
    [(addE lhs rhs)
      (interp lhs env
        (λ (v₀)
          (interp rhs env
            (λ (v₁)
              ((wrap-op 
                '+ 
                (λ (n₀ n₁ k err-k) (k (+ n₀ n₁))) 
                err-k)
              v₀ v₁ k)) 
            err-k)) 
        err-k)]
    [(divE lhs rhs)
      (interp lhs env
        (λ (v₀)
          (interp rhs env
            (λ (v₁)
              ((wrap-op 
                '/ 
                (λ (n₀ n₁ k err-k)
                  (if (zero? n₁)
                    (err-k) ; division by zero
                    (k (/ n₀ n₁)))) 
                err-k)
              v₀ v₁ k)) 
            err-k)) 
        err-k)]
    [(if0E tst thn els)
      (interp tst env
        (λ (tst-v)
          (type-case Value tst-v
            [(numV n)
              (interp (if (zero? n) thn els) env k err-k)]
            [else
              (err-k)])) ; non-number in if test
        err-k)]
    [(letE x bound-e body-e)
      (interp bound-e env 
        (λ (v) 
          (interp body-e (env-extend x v env) k err-k))
      err-k)]
    [(appE fun arg)
      (interp fun env
        (λ (fun-v)
          (type-case Value fun-v
            [(funV f)
              (interp arg env 
                (λ (v) (f v k err-k)) 
                err-k)]
            [else
              (err-k)])) ; not a function
        err-k)]
    [(funE x body)
      (k (funV (λ (v k err-k) (interp body (env-extend x v env) k err-k))))]
    [(throwE)
     (err-k)]
    [(tryE body-e handle-e)
     (interp body-e env 
      (lambda (body-v) 
        (k body-v))
      (lambda () ; if the interpretation of body-v errors, then interpret handle-v instead
        (interp handle-e env 
          (lambda (handle-v) 
            (k handle-v))
          err-k)))]))

(interp* : (S-Exp -> Value))
(define (interp* s)
  (interp (parse s) env-empty identity (lambda () (error 'interp "Generic Error"))))




(test/exn (interp* `(/ 1 0))
          "")

(test (interp* `(try (/ 1 0) 42))
      (numV 42))

(test (interp* `(try (+ (/ 1 0) 4) 42))
      (numV 42))

(test (interp* `(try (+ 4 (/ 1 0)) 42))
      (numV 42))

(test (interp* `(try (/ 1 (/ 1 0)) 42))
      (numV 42))

(test (interp* `(try (if0 (/ 1 0) 12 13) 42))
      (numV 42))

(test (interp* `(try (app (/ 1 0) 10) 42))
      (numV 42))

(test (interp* `(try (app 12 10) 42))
      (numV 42))

(test (interp* `(try (let ([x (/ 1 0)]) 25) 42))
      (numV 42))

(test (interp* `(try (let ([x (/ 1 0)]) 25) 42))
      (numV 42))

(test (interp* `(try (throw) 42))
      (numV 42))

(test (interp* `(try (app (fun (x) x) (throw)) 42))
      (numV 42))

(test (interp* `(try (if0 0 35 (throw)) 42))
      (numV 35))

(test (interp* `(try (if0 1 35 (throw)) 42))
      (numV 42))

(test (interp* `(try (if0 (fun (x) x) 10 12) 42))
      (numV 42))