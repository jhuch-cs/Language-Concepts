#lang plait
(print-only-errors #t)

; Basic language implementation including mutability

#|
expr ::= number
       | x
       | (+ expr expr)
       | (* expr expr)
       | (/ expr expr)
       | (if0 expr expr expr)
       | (let ([x expr]) expr)
       | (app expr expr)
|#

(define-type Expr
  (numE [value : Number])
  (ideE [name : Symbol])
  (addE [lhs : Expr]
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
        [body : Expr]))

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
    [else
     (error 'parse (string-append "not in language" (to-string s)))]))

(define-type-alias Location Number)

(define-type-alias Env (Hashof Symbol Location))

(env-empty : Env)
(define env-empty (hash empty))

(env-extend : (Symbol Location Env -> Env))
(define (env-extend id loc env)
  (hash-set env id loc))

(env-lookup : (Symbol Env -> Location))
(define (env-lookup id env)
  (type-case (Optionof Location) (hash-ref env id)
    [(some l)
     l]
    [(none)
     (error 'interp "unbound identifier")]))

(define-type-alias Store (Hashof Location Value))

(store-empty : Store)
(define store-empty (hash empty))

(store-extend : (Location Value Store -> Store))
(define (store-extend loc val store)
  (hash-set store loc val))

(store-lookup : (Location Store -> Value))
(define (store-lookup loc store)
  (type-case (Optionof Value) (hash-ref store loc)
    [(some v)
     v]
    [(none)
     (error 'interp "SEGMENTATION FAULT!")]))


(store-next-free : (Store -> Location))
(define (store-next-free sto)
  (length (hash-keys sto)))

; XXX end of section

(define-type Value
  (numV [value : Number])
  (funV [param : Symbol]
        [body : Expr]
        [env : Env]))

; INTERPRETATION

(wrap-op : (Symbol (Number Number -> Number) -> (Value Value -> Value)))
(define (wrap-op who f)
  (λ (v₀ v₁)
    (type-case Value v₀
      [(numV n₀)
       (type-case Value v₁
         [(numV n₁)
          (numV (f n₀ n₁))]
         [else
          (error who "not a number")])]
      [else
       (error who "not a number")])))

; XXX change this definition
(interp : (Expr Env Store -> (Value * Store)))
(define (interp exp env sto)
  (type-case Expr exp
    [(numE n)
     (values (numV n) sto)]
    [(ideE x)
     (values (store-lookup (env-lookup x env) sto) sto)]
    [(addE lhs rhs)
     (values 
      ((wrap-op '+ +)
        (fst (interp lhs env sto))
        (fst (interp rhs env sto))) 
      sto)]
    [(if0E tst thn els)
     (type-case Value (fst (interp tst env sto))
       [(numV n)
        (if (zero? n)
          (interp thn env sto)
          (interp els env sto))]
       [else
        (error 'interp "not a number")])]
    [(letE x bound-e body-e)
      (let ([bound-v  (fst (interp bound-e env sto))]) ; interpret the expression associated with the id
        (let ([new-env (env-extend x (store-next-free env) env)]) ; in the environment, associate the id with the next Location
          (let ([new-sto (store-extend (env-lookup x new-env) bound-v sto)]) ; in the store, associate the Location with the interpreted value of the id
            (interp body-e new-env new-sto))))] ; interpret the body with the updated env and sto
    [(appE fun-e arg-e)
      (local [(define-values (fun-v fun-sto) (interp fun-e env sto))] ; interpret the function, including the (possibly) altered Store
        (type-case Value fun-v
          [(funV id body clo-env)
            (let ([arg-v (fst (interp arg-e env sto))]) 
              (let ([body-env (env-extend id (store-next-free fun-sto) clo-env)])
                (let ([body-sto (store-extend (env-lookup id body-env) arg-v fun-sto)])
                  (interp body body-env body-sto))))]
          [else
            (error 'interp "not a function")]))]
    [(funE x body)
     (values (funV x body env) sto)]))

(interp* : (S-Exp -> Value))
(define (interp* s)
  (fst (interp (parse s) env-empty store-empty)))

(test (interp* `5) (numV 5))
(test (interp* `(+ 1 2)) (numV 3))
(test (interp* `(let ([x 10])
                  (+ x x)))
      (numV 20))
(test (interp* `(let ([x (+ 5 5)]) 
                  (+ x x)))
      (numV 20))
(test (interp* `(let ([x (+ 5 5)])
                  (let ([y (+ 2 2)])
                    (+ x y))))
      (numV 14))

(test (interp* `(let ([x (+ 5 5)])
                  (let ([x x])
                    (+ x x))))
      (numV 20))
(test (interp* `(let ([x (+ 5 5)])
                  (let ([x (+ x 1)])
                    (+ x x))))
      (numV 22))
(test (interp* `(let ([x 10])
                  (+ (let ([x 12])
                       x)
                     x)))
      (numV 22))

(test (interp* `(if0 0 1 2))
      (numV 1))

(test (interp* `(app (fun (x) x) 42)) (numV 42))

(test (interp* `(app (if0 0
                       (fun (x) (+ x 1))
                       (fun (y) (+ y 2)))
                     10))
      (numV 11))
(test (interp* `(app (let ([f (fun (x) (+ x 1))]) f)
                     10))
      (numV 11))
(test (interp* `(app (let ([f (fun (x) (+ x 1))]) f)
                     10))
      (numV 11))

(test/exn (interp* `(app 1 2)) "not a function")

(test (interp* `(app (let ([x 12])
                       (fun (y) x))
                     10))
      (numV 12))

