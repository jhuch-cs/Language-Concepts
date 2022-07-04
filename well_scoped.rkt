#lang plait
(print-only-errors #t)

; Basic type checker for variable scope

#|
expr ::= number
       | x
       | (+ expr expr)
       | (if0 expr expr expr)
       | (let ([x expr]) expr)
       | (app expr expr)
       | (fun (x) expr)
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
  (lamE [param : Symbol]
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

(parse : (S-Exp -> Expr))
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
     (lamE (s-exp->symbol (s-exp-ref `(fun (•) _) s))
           (parse         (s-exp-ref `(fun (_) •) s)))]
    [else
     (error 'parse (string-append "not in language" (to-string s)))]))

(define-type-alias Env (Hashof Symbol Boolean))

(env-empty : Env)
(define env-empty (hash empty))

(env-extend : (Symbol Env -> Env))
(define (env-extend x env)
  (hash-set env x #t))

(env-lookup : (Symbol Env -> Boolean))
(define (env-lookup x env)
  (type-case (Optionof Boolean) (hash-ref env x)
  [(some v)
   v]
  [(none)
   #f]))

(well-scoped?/env : (Expr Env -> Boolean))
(define (well-scoped?/env e env)
  (type-case Expr e
    [(numE n)
      #t]
    [(ideE x)
      (env-lookup x env)]
    [(addE lhs  rhs)
      (and 
        (well-scoped?/env lhs env) 
        (well-scoped?/env rhs env))]
    [(if0E tst thn els)
      (and 
        (well-scoped?/env tst env) 
        (well-scoped?/env thn env) 
        (well-scoped?/env els env))]
    [(letE x bound-e body-e)
      (let ([new-env (env-extend x env)])
        (and 
          (well-scoped?/env bound-e env)
          (well-scoped?/env body-e new-env)))]
    [(appE fun arg)
      (and 
        (well-scoped?/env fun env) 
        (well-scoped?/env arg env))]
    [(lamE x body)
      (let ([new-env (env-extend x env)])
        (well-scoped?/env body new-env))]))

(well-scoped? : (Expr -> Boolean))
(define (well-scoped? pr)
  (well-scoped?/env pr env-empty))

(test (well-scoped? (parse `x)) #f)

(test (well-scoped? (parse `1)) #t)

(test (well-scoped? (parse `(+ 1 3))) #t)
(test (well-scoped? (parse `(+ 1 x))) #f)

(test (well-scoped? (parse `(if0 1 3 4))) #t)
(test (well-scoped? (parse `(if0 (+ 1 x) 3 4))) #f)
(test (well-scoped? (parse `(if0 1 (+ 1 x) 4))) #f)
(test (well-scoped? (parse `(if0 1 3 (+ 1 x)))) #f)

(test (well-scoped? (parse `(let ([x 42]) 1))) #t)
(test (well-scoped? (parse `(let ([x 42]) x))) #t)
(test (well-scoped? (parse `(let ([x 42]) y))) #f)
(test (well-scoped? (parse `(let ([x y]) y))) #f)
(test (well-scoped? (parse `(let ([x (+ 2 x)]) x))) #f)
(test (well-scoped? (parse `(let ([x 42]) (+ x x)))) #t)
(test (well-scoped? (parse `(let ([x 42]) (+ y x)))) #f)

(test (well-scoped? (parse `(fun (x) x))) #t)
(test (well-scoped? (parse `(fun (y) (+ y (+ y 3))))) #t)
(test (well-scoped? (parse `(fun (y) x))) #f)
(test (well-scoped? (parse `(fun (y) (+ y (+ x 3))))) #f)

(test (well-scoped? (parse `(app (fun (x) x) 1))) #t)
(test (well-scoped? (parse `(app (fun (y) (+ y (+ y 3))) 2))) #t)
(test (well-scoped? (parse `(app (fun (y) x) 31))) #f)
(test (well-scoped? (parse `(app (fun (y) (+ y (+ x 3))) 39))) #f)
(test (well-scoped? (parse `(app (fun (x) x) x))) #f)
(test (well-scoped? (parse `(app (fun (y) (+ y (+ y 3))) y))) #f)

(test (well-scoped? 
  (parse 
  `(let ([f (fun (x) (+ 3 x))])
    (let ([x 42])
      (app f x))))) 
  #t)

(test (well-scoped? 
  (parse 
  `(let ([f (fun (x) (+ 3 y))])
    (let ([x 42])
      (app f x)))))
  #f)

(test (well-scoped? 
  (parse 
  `(let ([f (fun (x) (+ 3 x))])
    (let ([x 42])
      (app g x)))))
  #f)

(test (well-scoped? 
  (parse 
  `(let ([f (fun (x) (+ 3 x))])
    (let ([x 42])
      (app f y)))))
  #f)