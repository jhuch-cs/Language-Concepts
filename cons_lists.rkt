#lang plait
(print-only-errors #t)

; Basic language implementation, including cons-lists

#|
expr ::= number
     | x
     | (+ expr expr)
     | (* expr expr)
     | (/ expr expr)
     | (if0 expr expr expr)
     | (let ([x expr]) expr)
     | (app expr expr)
     | (fun (x) expr)
     | (empty)
     | (cons expr expr)
     | (list-case e
       [(empty) expr]
       [(cons x y) expr])
|#

(define-type Op
  (addO)
  (subO)
  (mulO)
  (divO))

(define-type Expr
  (numE [value : Number])
  (ideE [name : Symbol])
  (binE [op : Op]
        [lhs : Expr]
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
  (emptyE)
  (consE [fst : Expr]
         [rst : Expr])
  (list-caseE [list-of-elems : Expr]
              [if-empty : Expr] 
              [fst : Symbol]  ; Use environment to bind `elem` and `list-of-elems` in `body`
              [rst : Symbol]
              [if-not-empty : Expr]))

(define (parse-op s)
  (cond
    [(s-exp-match? `+ s)
      (addO)]
    [(s-exp-match? `- s)
      (subO)]
    [(s-exp-match? `* s)
      (mulO)]
    [(s-exp-match? `/ s)
      (divO)]
    [else
      (error 'parse "bad operator")]))

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
    [(s-exp-match? `(if0 ANY ANY ANY) s)
      (if0E (parse (s-exp-ref `(if0 • _ _) s))
        (parse (s-exp-ref `(if0 _ • _) s))
        (parse (s-exp-ref `(if0 _ _ •) s)))]
    [(s-exp-match? `(app ANY ANY) s)
      (appE (parse (s-exp-ref `(app • _) s))
        (parse (s-exp-ref `(app _ •) s)))]
    [(s-exp-match? `(let ([SYMBOL ANY]) ANY) s)
      (letE 
        (s-exp->symbol (s-exp-ref `(let ([• _]) _) s))
        (parse         (s-exp-ref `(let ([_ •]) _) s))
        (parse         (s-exp-ref `(let ([_ _]) •) s)))]
    [(s-exp-match? `(fun (SYMBOL) ANY) s)
      (funE 
        (s-exp->symbol (s-exp-ref `(fun (•) _) s))
        (parse         (s-exp-ref `(fun (_) •) s)))]
    [(s-exp-match? `(empty) s)
      (emptyE)]
    [(s-exp-match? `(cons ANY ANY) s)
      (consE 
        (parse (s-exp-ref `(cons • _) s))
        (parse (s-exp-ref `(cons _ •) s)))]
    [(s-exp-match? `(list-case ANY [(empty) ANY] [(cons SYMBOL SYMBOL) ANY]) s) 
      (list-caseE 
        (parse (s-exp-ref `(list-case • [(empty) _ ] [(cons _ _ ) _ ]) s)) ; `list` that we're list-case-ing
        (parse (s-exp-ref `(list-case _ [(empty) • ] [(cons _ _ ) _ ]) s)) ; empty clause
        (s-exp->symbol (s-exp-ref `(list-case _ [(empty) _ ] [(cons • _ ) _ ]) s))  ; fst identifier
        (s-exp->symbol (s-exp-ref `(list-case _ [(empty) _ ] [(cons _ • ) _ ]) s))  ; rst identifier    
        (parse         (s-exp-ref `(list-case _ [(empty) _ ] [(cons _ _ ) • ]) s)))] ; if-not-empty
    [(s-exp-match? `(ANY ANY ANY) s)
      (binE 
        (parse-op (s-exp-ref `(• _ _) s))
        (parse    (s-exp-ref  `(_ • _) s))
        (parse    (s-exp-ref  `(_ _ •) s)))]
    [else
      (error 'parse (string-append "not in language" (to-string s)))]))

(define-type Value
  (numV [value : Number])
  (funV [param : Symbol]
        [body : Expr]
        [env : Env])
  (empV)
  (consV [fst : Value]
        [rst : Value]))

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

(interp-op : (Op -> (Value Value -> Value)))
(define (interp-op op)
  (type-case Op op
    [(addO) (wrap-op '+ +)]
    [(subO) (wrap-op '- -)]
    [(mulO) (wrap-op '* *)]
    [(divO)
      (wrap-op
        '/
        (λ (numer denom)
        (if (zero? denom)
          (error 'divide "divide by zero XXX")
          (/ numer denom))))]))

(define-type-alias Env (Hashof Symbol Value))

(env-empty : Env)
(define env-empty (hash empty))

(env-extend : (Symbol Value Env -> Env))
(define (env-extend x v env)
  (hash-set env x v))

(env-lookup : (Symbol Env -> Value))
(define (env-lookup x env)
  (type-case (Optionof Value) (hash-ref env x)
  [(some v)
   v]
  [(none)
   (error 'interp "unbound identifier")]))

(interp/env : (Expr Env -> Value))
(define (interp/env e env)
  (type-case Expr e
    [(numE n)
      (numV n)]
    [(ideE x)
      (env-lookup x env)]
    [(binE op
           lhs
           rhs)
      ((interp-op op)
        (interp/env lhs env)
        (interp/env rhs env))]
    [(if0E tst thn els)
      (type-case Value (interp/env tst env)
        [(numV n)
          (if (zero? n)
            (interp/env thn env)
            (interp/env els env))]
        [else
          (error 'interp "not a number")])]
    [(letE x bound-e body-e)
      (let ([v-x (interp/env bound-e env)])
        (let ([new-env (env-extend x v-x env)])
        (interp/env body-e new-env)))]
    [(appE fun arg)
      (type-case Value (interp/env fun env)
        [(funV x body clo-env)
          (interp/env body (env-extend x (interp/env arg env) clo-env))]
        [else
          (error 'interp "not a function")])]
    [(funE x body)
      (funV x body env)]
    [(emptyE)
      (empV)]
    [(consE fst rst)
      (consV 
        (let ([possible-elem  (interp/env fst env)])
          (type-case Value possible-elem 
            [(numV _) possible-elem]
            [(funV _0 _1 _2) possible-elem]
            [else (error 'interp "cannot prepend lists")]))
        (let ([possible-list  (interp/env rst env)])
          (type-case Value possible-list 
            [(empV) possible-list]
            [(consV _0 _1) possible-list]
            [else (error 'interp "not a list")])))]
    [(list-caseE 
       list-of-elems 
       if-empty 
       fst-id 
       rst-id
       if-not-empty)   
        (let ([possible-list  (interp/env list-of-elems env)])
          (type-case Value possible-list 
            [(empV) 
              (interp/env if-empty env)]
            [(consV fst-val rst-val) 
              (let ([new-env (env-extend rst-id rst-val (env-extend fst-id fst-val env))]) 
                (interp/env if-not-empty new-env))]
            [else (error 'interp "not a list")]))]))

(define (interp* s)
  (interp/env (parse s) env-empty))








(test (interp* `5) (numV 5))
(test (interp* `(+ 1 2)) (numV 3))
(test (interp* `(* 5 2)) (numV 10))
(test (interp* `(* 5 (+ 2 3))) (numV 25))
(test (interp* `(/ 6 2)) (numV 3))
(test/exn (interp* `(/ 6 0)) "divide by zero XXX")
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
             (fun (y) (- y 1)))
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

(test (interp* `(empty)) (empV))

(test (interp* `(cons 1 (empty))) (consV (numV 1) (empV)))

(test/exn (interp* `(cons 1 2)) "not a list")
(test/exn (interp* `(cons 1 (cons 3 2))) "not a list")
(test/exn (interp* `(cons (empty) (empty))) "cannot prepend lists")
(test/exn (interp* `(cons (cons 2 (empty)) (empty))) "cannot prepend lists")


(test (interp* `(list-case (empty)
          [(empty) 42]
          [(cons fst rst) 35]))
    (numV 42))

(test (interp* `(list-case (cons 1 (empty))
          [(empty) 42]
          [(cons fst rst) 35]))
    (numV 35))

(test (interp* `(let ([x (empty)])
          (list-case x
          [(empty) 42]
          [(cons fst rst) 35])) )
    (numV 42))

(test (interp* `(list-case (cons 35 (empty))
          [(empty) 42]
          [(cons fst rst) fst]))
    (numV 35))
(test (interp* `(list-case (cons 35 (empty))
          [(empty) 42]
          [(cons fst rst)
           (+ fst
            (list-case rst
            [(empty) 10]
            [(cons fst rst) 12]))]))
    (numV 45))

(test/exn (interp* `(list-case 35
            [(empty) 42]
            [(cons fst rst) fst]))
      "not a list")
