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

(: denote-op (-> Binop (-> Value Value Real)))
(define (denote-op op)
  (define resolved-op
    (case op
      ['+ +]
      ['- -]
      ['* *]
      ['/ /]
      ['<= (lambda ([lhs : Real] [rhs : Real])
             (if (<= lhs rhs) 1 0))]))
  (lambda (lhs rhs)
    (cond [(and (number? lhs) (number? rhs))
           (resolved-op lhs rhs)]
          [else (error "trying to apply binary arithmetic on non-numbers")])))

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
                 ((denote-op op) (denote env lhs) (denote env rhs)))]
    [(If? e) (let ([guard (If-guard e)] [thn (If-thn e)] [els (If-els e)])
               (let ([guard (denote env guard)])
                 (if (and (number? guard) (zero? guard))
                     (denote env els)
                     (denote env thn))))]
    [else e]))


;; Curried version of denote
(: denote-fast (-> Expr (-> Env Value)))
(define (denote-fast e)
  (cond
    [(Var? e) (lambda ([env : Env])
                (hash-ref env (Var-val e)))]
    [(App? e) (let ([fun-clos (denote-fast (App-fun e))]
                    [arg-closs (for/list : (Listof (-> Env Value)) ([arg (App-args e)])
                                 (denote-fast arg))])
                (lambda ([env : Env])
                  (ap (fun-clos env)
                      (for/list ([arg-clos arg-closs])
                        (arg-clos env)))))]
    [(Fix? e) (let ([params (Fix-params e)]
                    [body-clos (denote-fast (Fix-body e))])
                (lambda ([env : Env])
                  (: self Closure)
                  (define self
                    (lambda ([vals : (Listof Value)])
                      (let ([env (for/fold ([env : Env env])
                                           ([param params]
                                            [val (cons self vals)])
                                   (hash-set env param val))])
                        (body-clos env))))
                  self))]
    [(Prim? e)
     (let ([op (Prim-op e)]
           [lhs-clos (denote-fast (Prim-lhs e))]
           [rhs-clos (denote-fast (Prim-rhs e))])
       (lambda ([env : Env])
         ((denote-op op) (lhs-clos env) (rhs-clos env))))]
    [(If? e)
     (let ([guard-clos (denote-fast (If-guard e))]
           [thn-clos (denote-fast (If-thn e))]
           [els-clos (denote-fast (If-els e))])
       (lambda ([env : Env])
         (let ([guard (guard-clos env)])
           (if (and (number? guard) (zero? guard))
               (els-clos env)
               (thn-clos env)))))]
    [e (lambda ([env : Env]) e)]))


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


(define-type CEnv (-> Symbol Natural))

(: cenv-empty CEnv)
(define (cenv-empty s)
  (error (format "unmapped symbol ~a" s)))

(: cenv-extend (-> CEnv Symbol CEnv))
(define (cenv-extend cenv s-new)
  (lambda ([s : Symbol])
    (if (symbol=? s s-new)
        0
        (add1 (cenv s)))))

(: cenv-extend-mult (-> CEnv (Listof Symbol) CEnv))
(define (cenv-extend-mult cenv params)
  (for/fold
      ([cenv cenv])
      ([param params])
    (cenv-extend cenv param)))

(define-struct Stack
  ([data : (Mutable-Vectorof (U Value #f))]
   [top : (Boxof Integer)]))

(: make-stack (-> Integer Stack))
(define (make-stack size)
  (Stack (make-vector size #f) (box 0)))

(: stack-push! (-> Stack Value Void))
(define (stack-push! stack val)
  (let* ([data (Stack-data stack)]
         [btop (Stack-top stack)]
         [top (unbox btop)]
         [size (vector-length data)])
    (cond
      [(>= top size)
       (error "stack overflow!")]
      [else
       (vector-set! data top val)
       (set-box! btop (add1 top))])))

(: stack-ref (-> Stack Integer Value))
(define (stack-ref stack idx)
  (or (vector-ref (Stack-data stack) (- (unbox (Stack-top stack)) idx 1))
      (error "broken invariant in stack")))

(: stack-pop! (-> Stack Void))
(define (stack-pop! stack)
  (let* ([btop (Stack-top stack)]
         [top (unbox btop)]
         [data (Stack-data stack)])
    (vector-set! data top #f)
    (set-box! btop (sub1 top))))


(define-type DValue (U Real DClosure))
(define-type DClosure (-> (Listof DValue) DValue))

(: dap (-> DValue (Listof DValue) DValue))
(define (dap fun args)
  (cond
    [(procedure? fun)
     (fun args)]
    [else
     (error "trying to apply a non-function")]))


(: collect-free (-> (Setof Symbol) Expr (Setof Symbol)))
(define (collect-free bounded e)
  (: collected (Setof Symbol))
  (define collected (set))
  (let go! : Void
      ([bounded : (Setof Symbol) bounded]
       [e : Expr e])
    (cond
      [(Var? e)
       (define s (Var-val e))
       (when (not (set-member? bounded s))
         (set! collected (set-add collected s)))]
      [(App? e)
       (go! bounded (App-fun e))
       (for ([arg (App-args e)])
         (go! bounded arg))]
      [(Fix? e)
       (go! (set-union bounded (list->set (Fix-params e)))
            (Fix-body e))]
      [(Prim? e)
       (go! bounded (Prim-lhs e))
       (go! bounded (Prim-rhs e))]
      [(If? e)
       (go! bounded (If-guard e))
       (go! bounded (If-thn e))
       (go! bounded (If-els e))]
      [(real? e)
       (void)]
      ;; making sure the branches are fully covered
      [else 1]))
  collected)

(: collect-captured (-> CEnv Expr (Listof (Pairof Symbol Natural))))
(define (collect-captured cenv e)
  (define free-vars (collect-free (set) e))
  ((inst sort (Pairof Symbol Natural) Natural)
   (for/list : (Listof (Pairof Symbol Natural)) ([var free-vars])
     (cons var (cenv var)))
   >
   #:key cdr))

;; Curried version of denote, faster with stack

;; Note that this version is wrong because it doesn't handle
;; closures properly unless you perform a deep copy of the stack
;; every time you evaluate Fix.
;; Would closure conversion be necessary ;; for the imperative stack
;; to work?
(: denote-faster (-> CEnv Expr (-> Stack Value)))
(define (denote-faster cenv e)
  (cond
    [(Var? e)
     (let* ([var (Var-val e)]
            [dvar (cenv var)])
       (lambda ([stack : Stack])
         (stack-ref stack dvar)))]
    [(App? e) (let ([fun-clos (denote-faster cenv (App-fun e))]
                    [arg-closs (for/list : (Listof (-> Stack Value))
                                         ([arg (App-args e)])
                                 (denote-faster cenv arg))])
                (lambda ([stack : Stack])
                  (dap (fun-clos stack)
                      (for/list ([arg-clos arg-closs])
                        (arg-clos stack)))))]
    [(Fix? e) (let* ([params (Fix-params e)]
                     [body-clos (denote-faster
                                 (cenv-extend-mult cenv params)
                                 (Fix-body e))]
                     [len (length params)])
                (lambda ([stack : Stack])
                  (: self DClosure)
                  (define self
                    (lambda ([vals : (Listof DValue)])
                      (for ([val (cons self vals)])
                        (stack-push! stack val))
                      (define retval (body-clos stack))
                      (for ([_ (in-range len)])
                        (stack-pop! stack))
                      retval))
                  self))]
    [(Prim? e)
     (let ([op (denote-op (Prim-op e))]
           [lhs-clos (denote-faster cenv (Prim-lhs e))]
           [rhs-clos (denote-faster cenv (Prim-rhs e))])
       (lambda ([stack : Stack])
         (op (lhs-clos stack) (rhs-clos stack))))]
    [(If? e)
     (let ([guard-clos (denote-faster cenv (If-guard e))]
           [thn-clos (denote-faster cenv (If-thn e))]
           [els-clos (denote-faster cenv (If-els e))])
       (lambda ([stack : Stack])
         (let ([guard (guard-clos stack)])
           (if (and (number? guard) (zero? guard))
               (els-clos stack)
               (thn-clos stack)))))]
    [e (lambda ([_ : Stack]) e)]))


(module+ main

  (println "-----------------native---------------")
  (println (time (fib 35)))
  (println "------------interpreted---------------")
  (println (time (denote (hash) (App fib-expr '(35)))))
  (println "----------------closure---------------")
  (println (let ([compiled (denote-fast (App fib-expr '(35)))])
             (time (compiled (hash)))))
  (println "----------------debruijn--------------")
  (println (let ([compiled (denote-faster cenv-empty (App fib-expr '(35)))]
                 [stack (make-stack 1024)])
             (time (compiled stack)))))

(provide (all-defined-out))
