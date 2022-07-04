#lang plait
(print-only-errors #t)

; Basic type-checker with support for typing recursive functions

#|
expr ::= number
       | x, f
       | (- expr expr)              
       | (* expr expr)                
       | (if0 expr expr expr)
       | (let ([x expr]) expr)
       | (app expr expr)
       | (fun (x : type) expr)
       | (rec f (x : type) type expr)

type ::= num
         (→ type type)
|#

(define-type Expr
  (numE [value : Number])
  (ideE [name : Symbol])
  (minE [lhs : Expr]
        [rhs : Expr])
  (mulE [lhs : Expr]
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
        [param-type : Type]
        [body : Expr])
  (recE [self : Symbol]
        [param : Symbol]
        [param-type : Type]
        [body-type : Type]
        [body : Expr]))

(define-type Type
  (numT)
  (arrT [dom : Type]
        [cod : Type]))

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
    [(s-exp-match? `(- ANY ANY) s)
     (minE (parse (s-exp-ref    `(- • _) s))
           (parse (s-exp-ref    `(- _ •) s)))]
    [(s-exp-match? `(* ANY ANY) s)
     (mulE (parse (s-exp-ref    `(* • _) s))
           (parse (s-exp-ref    `(* _ •) s)))]
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
    [(s-exp-match? `(fun (SYMBOL : ANY) ANY) s)
     (lamE (s-exp->symbol (s-exp-ref `(fun (• : _) _) s))
           (parse-type    (s-exp-ref `(fun (_ : •) _) s))
           (parse         (s-exp-ref `(fun (_ : _) •) s)))]
    [(s-exp-match? `(rec SYMBOL (SYMBOL : ANY) ANY ANY) s)
     (recE (s-exp->symbol (s-exp-ref `(rec • (_ : _) _) s))
           (s-exp->symbol (s-exp-ref `(rec _ (• : _) _) s))
           (parse-type    (s-exp-ref `(rec _ (_ : •) _ _) s))
           (parse-type    (s-exp-ref `(rec _ (_ : _) • _) s))
           (parse         (s-exp-ref `(rec _ (_ : _) _ •) s)))]
    [else
     (error 'parse (string-append "not in language" (to-string s)))]))

(define (parse-type s)
  (cond
    [(s-exp-match? `num s)
     (numT)]
    [(s-exp-match? `(→ ANY ANY) s)
     (arrT (parse-type (s-exp-ref `(→ • _) s))
           (parse-type (s-exp-ref `(→ _ •) s)))]
    [else
     (error 'parse-type (string-append "not in language" (to-string s)))]))

(define-type-alias Env (Hashof Symbol Type))

(env-empty : Env)
(define env-empty (hash empty))

(env-extend : (Symbol Type Env -> Env))
(define (env-extend x τ env)
  (hash-set env x τ))

(env-lookup : (Symbol Env -> Type))
(define (env-lookup x env)
  (type-case (Optionof Type) (hash-ref env x)
  [(some v)
   v]
  [(none)
   (error 'env-lookup "Unbound identifier")]))

(typeof/env : (Expr Env -> Type))
(define (typeof/env e env) 
  (type-case Expr e
    [(numE n)
      (numT)]
    [(ideE x)
      (env-lookup x env)]
    [(minE lhs rhs)
      (if 
        (and 
          (equal? (typeof/env lhs env) (numT))
          (equal? (typeof/env rhs env) (numT)))
        (numT)
        (error 'typeof "Unsupported operand(s) in -"))]
    [(mulE lhs rhs)
      (if 
        (and 
          (equal? (typeof/env lhs env) (numT))
          (equal? (typeof/env rhs env) (numT)))
        (numT)
        (error 'typeof "Unsupported operand(s) in *"))]
    [(if0E tst thn els)
      (let ([thn-type (typeof/env thn env)])
        (if 
          (and 
            (equal? (typeof/env tst env) (numT))
            (equal? thn-type (typeof/env els env)))
          thn-type
          (error 'typeof "Type mismatch in if")))]
    [(letE x bound-e body-e)
      (let ([new-env (env-extend x (typeof/env bound-e env) env)])
        (typeof/env body-e new-env))]
    [(appE fun arg)
      (let ([fun-type (typeof/env fun env)]
            [arg-type (typeof/env arg env)])
        (type-case Type fun-type 
            [(arrT dom cod) 
              (if (equal? dom arg-type)
                cod
                (error 'typeof "Type mismatch between argument and function"))]
            [else (error 'typeof "Attempt to call non-function")]))]
    [(lamE x type body)
      (let ([new-env (env-extend x type env)])
        (arrT type (typeof/env body new-env)))]
    [(recE self param param-type body-type body) 
      (letrec ([self-type (arrT param-type body-type)]
               [new-env (env-extend self self-type env)]
               [newer-env (env-extend param param-type new-env)]
               [body-checked-type (typeof/env body newer-env)])
        (if (equal? body-type body-checked-type)
          (arrT param-type body-checked-type)
          (error 'typeof "Body's declared type did not match body's checked type")))]))

(typeof : (Expr -> Type))
(define (typeof pr)
  (typeof/env pr env-empty))

(define-syntax-rule
  (test-typeof pr τ)
  (test (typeof (parse pr)) (parse-type τ)))

(define-syntax-rule
  (test/exn-typeof pr msg)
  (test/exn (typeof (parse pr)) msg))

; these are new
(test-typeof `(rec loop (x : num) num
                (app loop x))
             `(→ num num))

(test/exn-typeof `(rec loop (n : num) num
                    (if0 (app loop n)
                      (fun (x : num) x)
                      (fun (y : num) y)))
                 "")

(test-typeof `(rec fact (n : num) num
                (if0 n
                  1
                  (* n (app fact (- n 1)))))
             `(→ num num))

(test/exn-typeof `(rec fact (n : num) num
                    fact)
                 "")
