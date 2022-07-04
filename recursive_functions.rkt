#lang plait
(print-only-errors #t)

; Basic language implementation with recursive functions

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
       | (rec f (x) expr)
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
  (conE [first : Expr]
        [rest : Expr])
  (list-caseE 
        [list-to-decompose : Expr]
        [if-empty : Expr]
        [fst : Symbol]
        [rst : Symbol]
        [if-not-empty : Expr])
  (recE [funct-name : Symbol]
        [param-name : Symbol]
        [body : Expr]))

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
     (letE (s-exp->symbol (s-exp-ref `(let ([• _]) _) s))
           (parse (s-exp-ref         `(let ([_ •]) _) s))
           (parse (s-exp-ref         `(let ([_ _]) •) s)))]
    [(s-exp-match? `(fun (SYMBOL) ANY) s)
     (funE (s-exp->symbol (s-exp-ref `(fun (•) _) s))
           (parse         (s-exp-ref `(fun (_) •) s)))]
    [(s-exp-match? `(rec SYMBOL (SYMBOL) ANY) s)
     (recE (s-exp->symbol (s-exp-ref `(rec • (_) _) s))
           (s-exp->symbol (s-exp-ref `(rec _ (•) _) s))
           (parse         (s-exp-ref `(rec _ (_) •) s)))]
    [(s-exp-match? `(empty) s)
     (emptyE)]
    [(s-exp-match? `(cons ANY ANY) s)
     (conE (parse (s-exp-ref `(cons • _) s))
           (parse (s-exp-ref `(cons _ •) s)))]
    [(s-exp-match? `(list-case ANY
                      [(empty) ANY]
                      [(cons SYMBOL SYMBOL) ANY])
                   s)
     (list-caseE (parse (s-exp-ref         `(list-case •
                                        [(empty) _]
                                        [(cons _ _) _])
                             s))
           (parse (s-exp-ref         `(list-case _
                                        [(empty) •]
                                        [(cons _ _) _])
                             s))
           (s-exp->symbol (s-exp-ref `(list-case _
                                        [(empty) _]
                                        [(cons • _) _])
                                     s))
           (s-exp->symbol (s-exp-ref `(list-case _
                                        [(empty) _]
                                        [(cons _ •) _])
                                     s))
           (parse (s-exp-ref         `(list-case _
                                        [(empty) _]
                                        [(cons _ _) •])
                                     s)))]
    [(s-exp-match? `(ANY ANY ANY) s)
     (binE (parse-op (s-exp-ref `(• _ _) s))
           (parse (s-exp-ref    `(_ • _) s))
           (parse (s-exp-ref    `(_ _ •) s)))]
    [else
     (error 'parse (string-append "not in language" (to-string s)))]))

(define-type Value
  (numV [value : Number])
  (funV [param : Symbol]
        [body : Expr]
        [env : Env])
  (recV [func : Symbol]
        [param : Symbol]
        [body : Expr]
        [env : Env])
  (empV)
  (conV [fst : Value]
        [rst : Value]))

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

(interp : (Expr Env -> Value))
(define (interp e env)
  (type-case Expr e
    [(numE n)
     (numV n)]
    [(ideE x)
     (env-lookup x env)]
    [(binE op   
           lhs 
           rhs)
     ((interp-op op)
      (interp lhs env)
      (interp rhs env))]
    [(if0E tst thn els)
     (type-case Value (interp tst env)
       [(numV n)
        (if (zero? n)
          (interp thn env)
          (interp els env))]
       [else
        (error 'interp "not a number")])]
    [(letE x bound-e
           body-e)
     (let ([v-x (interp bound-e env)])
       (let ([new-env (env-extend x v-x env)])
         (interp body-e new-env)))]
    [(appE fun arg)
     (type-case Value (interp fun env)
       [(funV x body clo-env)
        (interp body (env-extend x (interp arg env) clo-env))]
       [(recV func param body clo-env)
        (let ([clo-env-extended (env-extend param (interp arg env) clo-env)])
         (let ([clo-env-extended-recursive (env-extend func (recV func param body clo-env-extended) clo-env-extended)])
          (interp body clo-env-extended-recursive)))]
       [else
        (error 'interp "not a function")])]
    [(funE x body)
     (funV x body env)]
    [(recE func param body)
     (recV func param body env)]
    [(emptyE)
     (empV)]
    [(conE fst snd)
     (conV (interp fst env)
           (type-case Value (interp snd env)
             [(empV)
              (empV)]
             [(conV v₀ v₁)
              (conV v₀ v₁)]
             [else
              (error 'interp "not a list")]))]
    [(list-caseE disc-e emp-e x₀ x₁ con-e)
     (type-case Value (interp disc-e env)
       [(empV)
        (interp emp-e env)]
       [(conV v₀ v₁)
        (interp con-e (env-extend x₁ v₁ (env-extend x₀ v₀ env)))]
       [else
        (error 'interp "not a list")])]))

(define (interp* s)
  (interp (parse s) env-empty))

(test (interp* `(rec f (x) x))
      (recV 'f 'x (ideE 'x) env-empty))

(test (interp* `(app (rec f (x) x) 42))
      (numV 42))

(test (interp* `(app (rec fact (n)
                          (if0 n
                            1
                            (* n (app fact (- n 1)))))
                     5))
      (numV 120))

(test (interp* `(app (app (fun (x)
                               (rec repeat (n)
                                    (if0 n
                                      (empty)
                                      (cons x (app repeat (- n 1))))))
                          10)
                     3))
      (conV (numV 10) (conV (numV 10) (conV (numV 10) (empV)))))

(test (interp* `(app (rec length (xs)
                       (list-case xs
                         [(empty)
                          0]
                         [(cons _ rest-xs)
                          (+ 1 (app length rest-xs))]))
                     (cons 1 (cons 2 (cons 3 (empty))))))
      (numV 3))

(test (interp* `(let ([make-repeat (fun (x)
                                     (rec self (n)
                                       (if0 n
                                         (empty)
                                         (cons x (app self (- n 1))))))])
                  (let ([repeat (app make-repeat 3)])
                    (let ([length (rec len (xs)
                                    (list-case xs
                                      [(empty)
                                       0]
                                      [(cons _ rest-xs)
                                       (+ 1 (app len rest-xs))]))])
                      (app length (app repeat 10))))))
      (numV 10))
