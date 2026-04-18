#lang typed/racket

(define-type Expr (U Real App Var Fix Prim If))

(define-struct Var ([val : Symbol]))
(define-struct App ([fun : Expr] [args : (Listof Expr)]))
(define-struct Fix ([params : (Pairof Symbol (Listof Symbol))] [body : Expr]))
(define-struct Prim ([op : Binop] [lhs : Expr] [rhs : Expr]))
(define-struct If ([guard : Expr] [thn : Expr] [els : Expr]))

(define-type Binop (U '+ '- '* '/ '<=))

(define-type Value (U Real Closure))
(define-type Env (Immutable-HashTable Symbol Value))
(define-type Closure (-> (Listof Value) Value))

(: ap (-> Value (Listof Value) Value))
(define (ap fun args)
  (cond
    [(procedure? fun)
     (fun args)]
    [else
     (error "trying to apply a non-function")]))

(: denote-op (-> Binop Value Value Real))
(define (denote-op op lhs rhs)
  (cond [(and (number? lhs) (number? rhs))
         (case op
           ['+ (+ lhs rhs)]
           ['- (- lhs rhs)]
           ['* (* lhs rhs)]
           ['/ (/ lhs rhs)]
           ['<= (if (<= lhs rhs) 1 0)])]
        [else (error "trying to apply binary arithmetic on non-numbers")]))

(: denote (-> Env Expr Value))
(define (denote env e)
  (cond
    [(Var? e) (hash-ref env (Var-val e))]
    [(App? e) (let ([fun (App-fun e)] [args (App-args e)])
                (ap (denote env fun) (for/list ([arg args]) (denote env arg))))]
    [(Fix? e) (let ([params (Fix-params e)] [body (Fix-body e)])
                (: self Closure)
                (define self
                  (lambda ([vals : (Listof Value)])
                    (let ([env (for/fold ([env : Env env])
                                         ([param params]
                                          [val (cons self vals)])
                                 (hash-set env param val))])
                      (denote env body))))
                self)]
    [(Prim? e) (let ([op (Prim-op e)] [lhs (Prim-lhs e)] [rhs (Prim-rhs e)])
                 (denote-op op (denote env lhs) (denote env rhs)))]
    [(If? e) (let ([guard (If-guard e)] [thn (If-thn e)] [els (If-els e)])
               (let ([guard (denote env guard)])
                 (if (and (number? guard) (zero? guard))
                     (denote env els)
                     (denote env thn))))]
    [else e]))

(: denote-fast (-> Expr (-> Env Value)))
(define (denote-fast e)
  (cond
    [(Var? e) (lambda ([env : Env])
                (hash-ref (Var-val e)))]
    []))



(: fib-expr Expr)
(define fib-expr
  (Fix '(self x)
       (If (Prim '<= (Var 'x) 1)
           1
           (Prim '+
                 (App (Var 'self) (list (Prim '- (Var 'x) 1)))
                 (App (Var 'self) (list (Prim '- (Var 'x) 2)))))))

(: fib (-> Real Real))
(define (fib n)
  (if (<= n 1)
      1
      (+ (fib (- n 1))
         (fib (- n 2)))))


(module+ main
  (println "-----------------native---------------")
  (println (time (fib 30)))
  (println "------------interpreted---------------")
  (println (time (denote (hash) (App fib-expr '(30))))))
