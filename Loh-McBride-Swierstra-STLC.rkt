#lang plai
#|
This file implements Löh, McBride and Swierstra's
"A tutorial implementation of a dependently typed lambda calculus"
Chapter 2: STLC
|#

(define-type Term↑
  [Ann (term Term↓?) (type Type?)]
  [Bound (debrujin number?)]
  [Free (name Name?)]
  [App (t1 Term↑?) (t2 Term↓?)])

(define-type Term↓
  [Inf (t Term↑?)]
  [Lam (body Term↓?)])

(define-type Name
  [Global (s string?)]
  [Local (debrujin number?)]
  [Quote (debrujin number?)])

(define-type Type
  [TFree (n Name?)]
  [Fun (dom Type?) (cod Type?)])

(define-type Value
  [VLam (f procedure?)]
  [VNeutral (n Neutral?)])

(define-type Neutral
  [NFree (n Name?)]
  [NApp (e1 Neutral?) (e2 Value?)])

;; vfree :: Name -> Value
(define (vfree n)
  (VNeutral (NFree n)))

;; type Env = [Value]
(define Env? 
  (listof Value?))

;; eval↑ :: Term↑ -> Env -> Value
(define (eval↑ term env)
  (type-case Term↑ term
    [Ann (e t) (eval↓ e env)]
    [Free (x) (vfree x)]
    [Bound (i) (list-ref env i)]
    [App (e1 e2) (vapp (eval↑ e1 env)
                       (eval↓ e2 env))]))

;; vapp :: Value -> Value -> Value
(define (vapp v1 v2)
  (type-case Value v1
    [VLam (f) (f v2)]
    [VNeutral (n) (VNeutral (NApp n v2))]))

;; eval↓ :: Term↓ -> Env -> Value
(define (eval↓ term env)
  (type-case Term↓ term
    [Inf (i) (eval↑ i env)]
    [Lam (e) (VLam (lambda (x) (eval↓ e (cons x env))))]))

(define-type Kind
  (Star))

(define-type Info
  [HasKind (k Kind?)]
  [HasType (t Type?)])

;; type Context = [ (Name, Info) ]
(define Context?
  (listof (cons/c Name? Info?)))

;; kind↓ :: Context -> Type -> Kind -> Void
(define (kind↓ context type kind)
  (type-case Type type
    [TFree (x)
           (if (HasKind? (cdr (assoc x context)))
               (void)
               (error (format "unknown identifier ~s in context ~s" x context)))]
    [Fun (kdom kcod)
         (begin
           (kind↓ context kdom kind)
           (kind↓ context kcod kind))]))

;; type↑0 :: Context -> Term↑ -> Type
(define (type↑0 context term)
  (type↑ 0 context term))

;; type↑ :: Int -> Context -> Term↑ -> Type
(define (type↑ i Γ term)
  (type-case Term↑ term
    [Ann (e τ)
         (begin
           (kind↓ Γ τ (Star))
           (type↓ i Γ e τ)
           τ)]
    [Free (x)
          (if (HasType? (cdr (assoc x Γ)))
              (HasType-t (cdr (assoc x Γ)))
              (error "unknown identifier - Free (x) ~s in ~s" x Γ))]
    [App (e1 e2)
         (type-case Type (type↑ i Γ e1)
           [Fun (τdom τcod)
                (begin (type↓ i Γ e2 τdom)
                       τcod)]
           [else (error "illegal application")])]
                
    [else (error "type↑ undefined for bound")]))

(define (type↓ i Γ term τ)
  (type-case Term↓ term
    [Inf (e)
         (if (equal? τ (type↑ i Γ e))
             (void)
             (error (format "type mismatch between checked ~s and inferred ~s" τ (type↑ i Γ e))))]
    [Lam (e)
         (type-case Type τ
           [Fun (τdom τcod)
                (type↓ (add1 i) (cons (cons (Local i)
                                            (HasType τdom))
                                      Γ)
                       (subst↓ 0 (Free (Local i)) e) τcod)]
           [else (error "type mismatch")])]))

;; subst↑ :: Int -> Term↑ -> Term↑ -> Term↑
(define (subst↑ i r t)
  (type-case Term↑ t
    [Ann (e τ) (Ann (subst↓ i r e) τ)]
    [Bound (j) (if (equal? i j)
                   r
                   (Bound j))]
    [Free (y) (Free y)]
    [App (e1 e2) (App (subst↑ i r e1)
                      (subst↓ i r e2))]))

;; subst↓ :: Int -> Term↑ -> Term↓ -> Term↑
(define (subst↓ i r t)
  (type-case Term↓ t
    [Inf (e) (Inf (subst↑ i r e))]
    [Lam (e) (Lam (subst↓ (add1 i) r e))])
  )

;; quote0 :: Value -> Term↓
(define (quote0 v)
  (quote 0 v))

;; quote :: Int -> Value -> Term↓
(define (quote i v)
  (type-case Value v
    [VLam (f) (Lam (quote (add1 i) (f (vfree (Quote i)))))]
    [VNeutral (n) (Inf (neutralQuote i n))]))

;; neutralQuote :: Int -> Neutral -> Term↑
(define (neutralQuote i neutral)
  (type-case Neutral neutral
    [NFree (x) (boundfree i x)]
    [NApp (n v) (App (neutralQuote i n)
                     (quote i v))]))

;;boundfree :: Int -> Name -> Term↑
(define (boundfree i x)
  (type-case Name x
    [Quote (k) (Bound (- i k 1))]
    [else (Free x)]))

(test (quote 0 (VLam (lambda (x) (VLam (lambda (y) x)))))
      (Lam (Lam (Inf (Bound 1)))))

; Tests in page 1012

(let* ([id^ (Lam (Inf (Bound 0)))]
       [const^ (Lam (Lam (Inf (Bound 1))))]
       [tfree (lambda (α) (TFree (Global α)))]
       [free (lambda (x) (Inf (Free (Global x))))]
       [term1 (App (Ann id^ (Fun (tfree "a") (tfree "a")))
                   (free "y"))]
       [term2 (App (App (Ann const^ (Fun (Fun (tfree "b") (tfree "b"))
                                         (Fun (tfree "a")
                                              (Fun (tfree "b") (tfree "b")))))
                        id^)
                   (free "y"))]
       [env1 (list (cons (Global "y")
                         (HasType (tfree "a")))
                   (cons (Global "a")
                         (HasKind (Star))))]
       [env2 (cons (cons (Global "b")
                         (HasKind (Star)))
                   env1)])
  (test (quote0 (eval↑ term1 empty)) (Inf (Free (Global "y"))))
  (test (quote0 (eval↑ term2 empty)) (Lam (Inf (Bound 0))))
  (test (type↑0 env1 term1) (TFree (Global "a")))
  (test (type↑0 env2 term2) (Fun (TFree (Global "b")) (TFree (Global "b"))))
  )
                  