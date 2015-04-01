#lang racket

;; grammar

(struct var (x))
(struct hvar var ())
(struct svar var ())

(struct exp ())
(struct lte exp (x e0 e1))
(struct app exp (f e))

(struct aexp exp ())
(struct lam aexp (x e))
(struct num aexp (n))
(struct ref aexp (x))
(struct href ref ())
(struct sref ref ())

;; parsing

(begin-for-syntax
 (define (in-ρ x ρ)
   (ormap (λ (y) (bound-identifier=? x y)) ρ))
 
 (define (AE stx ρ)
   (syntax-case stx (λ)
     [(λ (x) e)
      (identifier? #'x)
      (let-values ([(e hrefs) (E #'e (list #'x))])
	(values #`(lam #,(if (in-ρ #'x hrefs) #'(hvar 'x) #'(svar 'x)) #,e) hrefs))]
     [x
      (identifier? #'x)
      (if (in-ρ #'x ρ)
	(values #'(sref 'x) null)
	(values #'(href 'x) (list #'x)))]
     [n
      (number? (syntax->datum #'n))
      (values #'(num n) null)]
     [e
      (raise-syntax-error #f "expected atomic expression" #'e)]))
 
 (define (C stx ρ)
   (syntax-case stx ()
     [(f e)
      (let-values ([(f f-hrefs) (AE #'f ρ)]
		   [(e e-hrefs) (AE #'e ρ)])
	(values #`(app #,f #,e) (append f-hrefs e-hrefs)))]
     [e
      (AE #'e ρ)]))
  
 (define (E stx ρ)
   (syntax-case stx (let)
     [(let ([x e0]) e1)
      (identifier? #'x)
      (let-values ([(e0 e0-hrefs) (E #'e0 ρ)] ; change to C to constrain grammar
		   [(e1 e1-hrefs) (E #'e1 (cons #'x ρ))])
	(let ([hrefs (append e0-hrefs e1-hrefs)])
	  (values #`(lte #,(if (in-ρ #'x hrefs) #'(hvar 'x) #'(svar 'x)) #,e0 #,e1) hrefs)))]
     [e
      (C #'e ρ)])))

(define-syntax (P stx)
  (syntax-case stx ()
    [(_ p)
     (let-values ([(p p-hrefs) (E #'p null)])
       p)]))

(define unP
  (match-lambda
    [(app f e)
     `(,(unP f) ,(unP e))]
    [(lam (or (hvar x) (svar x)) e)
     `(λ (,x) ,(unP e))]
    [(lte (or (hvar x) (svar x)) e0 e1)
     `(let ([,x ,(unP e0)])
	,(unP e1))]
    [(num n) n]
    [(ref x) x]))

;; concrete evaluation

(struct clos (ρ x e) #:transparent)
(struct Γ (ρ x e) #:transparent)

(define (A e ρ)
  (match e
    [(lam (or (hvar x) (svar x)) e) (clos ρ x e)] ; var is taken by match
    [(num n) n]
    [(ref x) (hash-ref ρ x)]))

(define (eval p)
  (define (appl κ v)
    (match κ
      [(list) v]
      [(cons (Γ ρ x e) κ)
       (eval e (hash-set ρ x v) κ)]))
  (define (eval e ρ κ)
    (if (or (lam? e)
	    (num? e)
	    (ref? e))
      (appl κ (A e ρ))
      (match e
	[(lte (or (hvar x) (svar x)) e0 e1)
	 (eval e0 ρ (cons (Γ ρ x e1) κ))]
	[(app f e)
	 (match-let ([(clos ρ x e) (A f ρ)]
		     [v (A e ρ)])
	   (eval e (hash-set ρ x v) κ))])))
  (eval p (hasheq) empty))

(module+ main
  (eval (P (let ([f (λ (x) x)])
	     (f 42)))))

;; abstract evaluation

(define (ρ-update ρ x v)
  (hash-set ρ (var-x x) v))

(define (σ-update σ x v)
  (if (hvar? x)
    (hash-update σ (var-x x) (λ (vs) (set-union vs v)) (set))
    σ))

(struct αΓ (x e))

(struct ς-call (σ ρ κ f e) #:transparent)
(struct ς-tail (σ ρ f e) #:transparent)
(struct ς-entr (σ f v) #:transparent)
(struct ς-exit (σ v) #:transparent)

(define (ς-eval σ ρ κ e)
  (if (or (lam? e)
	  (num? e)
	  (ref? e))
    (let ([v (αA e ρ σ)])
      (match κ
	[(list)
	 (ς-exit σ v)]
	[(cons (αΓ x e1) κ)
	 (let ([σ (σ-update σ x v)]
	       [ρ (ρ-update ρ x v)])
	   (ς-eval σ ρ κ e1))]))
    (match e
      [(app f e)
       (if (empty? κ)
	 (ς-tail σ ρ f e)
	 (ς-call σ ρ κ f e))]
      [(lte x e0 e1)
       (ς-eval σ ρ (cons (αΓ x e1) κ) e0)])))

(define (inject p)
  (ς-eval (hasheq) (hasheq) empty p))

(define (αA e ρ σ)
  (if (lam? e)
    (set e)
    (match e
      [(num n) (set n)]
      [(href x) (hash-ref σ x)]
      [(sref x) (hash-ref ρ x)])))

(define succs
  (match-lambda
    [(or (ς-call σ ρ _ f e)
	 (ς-tail σ ρ f e))
     (let ([v (αA e ρ σ)])
       (for/list ([f (in-set (αA f ρ σ))])
	 (ς-entr σ f v)))]
    [(ς-entr σ (lam x e) v)
     (let ([ρ (hasheq)]
	   [κ empty])
       (let ([σ (σ-update σ x v)]
	     [ρ (ρ-update ρ x v)])
	 (list (ς-eval σ ρ κ e))))]))

(define (analyze p)
  (define (propagate seen work ς0 ς1)
    (let ([ς0×ς1 (cons ς0 ς1)])
      (if (set-member? seen ς0×ς1)
	work
	(set-add work ς0×ς1))))

  (define (propagate* seen work ς0 ς1s)
    (foldl (λ (ς1 work) (propagate seen work ς0 ς1)) work ς1s))

  (define (update seen work ς0 ς1 ς2 ς3)
    (match-let ([(ς-call ς1 ρ1 (cons (αΓ x e) κ) f1 e1) ς1]
		[(ς-entr σ2 f2 v2) ς2]
		[(ς-exit σ3 v3) ς3])
      (let ([σ σ3]
	    [ρ (if (href? f1) (ρ-update ρ1 f1 (set f2)) ρ1)]) ; not what CFA2 dictates, but I think this is right...
	(let ([σ (σ-update σ x v3)]
	      [ρ (ρ-update ρ x v3)])
	  (propagate seen work ς0 (ς-eval σ ρ κ e))))))

  (define (call seen work calls summaries ς0×ς1 ς2s f)
    (for/fold ([work work]
	       [calls calls])
	([ς2 (in-list ς2s)])
      (values (for/fold ([work (propagate seen work ς2 ς2)])
                  ([ς3 (in-set (hash-ref summaries ς2))])
                (f work ς2 ς3))
              (hash-update calls ς2 (λ (cs) (set-add cs ς0×ς1)) (set)))))

  (define (retr seen work ς0×ς1s f)
    (for/fold ([work work])
	([ς0×ς1 (in-set ς0×ς1s)])
      (match-let ([(cons ς0 ς1) ς0×ς1])
	(f seen work ς0 ς1))))
  
  (let ([init (inject p)])
    (let loop ([seen (set)]
	       [work (list (cons init init))]
	       [calls (hash)]
	       [tails (hash)]
	       [summaries (hash)]
	       [finals (set)])
      (match work
	[(list)
	 (values calls tails summaries finals)]
	[(cons (and ς0×ς1 (cons ς0 ς1)) work)
	 (let ([seen (set-add seen ς0×ς1)])
	   (cond
	     [(ς-call? ς1)
	      (let-values ([(work calls) (call seen work calls summaries ς0×ς1 (succs ς1)
					       (λ (work ς2 ς3) (update seen work ς0 ς1 ς2 ς3)))])
		(loop seen work calls tails summaries finals))]
	     [(ς-tail? ς1)
	      (let-values ([(work tails) (call seen work tails summaries ς0×ς1 (succs ς1)
					       (λ (work ς2 ς3) (propagate seen work ς0 ς3)))])
		(loop seen work calls tails summaries finals))]
	     [(ς-entr? ς1)
	      (let ([work (propagate* seen work ς0 (succs ς1))])
		(loop seen work calls tails summaries finals))]
	     [(ς-exit? ς1)
	      (let ([summaries (hash-update summaries ς0 (λ (ss) (set-add ss ς1)) (set))])
		(if (equal? init ς0)
		  (loop seen work calls tails summaries (set-add finals ς1))
		  (let* ([work (retr seen work (hash-ref calls ς0 (set))
				       (λ (seen work ς2 ς3) (update seen work ς2 ς3 ς0 ς1)))]
			 [work (retr seen work (hash-ref tails ς0 (set))
				       (λ (seen work ς2 ς3) (propagate seen work ς2 ς1)))])
		    (loop seen work calls tails summaries finals))))]
	     [else
	      (error 'analyze "unhandled state: ~a" ς1)]))]))))

(module+ main
  (analyze (P 42))
  (analyze (P (let ([f (λ (x) ((λ (y) y) x))])
		(let ([z (f 24)])
		  z))))
  (analyze (P ((λ (x) (x x)) (λ (y) (y y))))))
