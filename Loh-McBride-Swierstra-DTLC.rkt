#lang plai
#|
This file implements Löh, McBride and Swierstra's
"A tutorial implementation of a dependently typed lambda calculus"
Including Naturals and Vectors, with their test examples.
|#


(print-only-errors #t)

(define-type Term↑
  [Ann (term Term↓?) (type Term↓?)]
  [Star]
  [Pi (dom Term↓?) (cod Term↓?)]
  [Bound (debrujin number?)]
  [Free (name Name?)]
  [App (t1 Term↑?) (t2 Term↓?)]
  ;naturals
  [Nat]
  [NatElim (n Term↓?) (mz Term↓?) (ms Term↓?) (d Term↓?)]
  [Zero]
  [Succ (n Term↓?)]
  ; vectors
  [Vec (type Term↓?) (k Term↓?)]
  [Nil (type Term↓?)]
  [Cons (type Term↓?) (length Term↓?) (head Term↓?) (tail Term↓?)]
  [VecElim (type Term↓?) (m Term↓?) (mn Term↓?) (mc Term↓?) (k Term↓?) (vs Term↓?)]                                                                   
  )

(define-type Term↓
  [Inf (t Term↑?)]
  [Lam (body Term↓?)])

(define-type Name
  [Global (s string?)]
  [Local (debrujin number?)]
  [Quote (debrujin number?)])

(define-type Value
  [VLam (f procedure?)]
  [VStar]
  [VPi (arg Value?) (f procedure?)]
  [VNeutral (n Neutral?)]
  ;natural number values
  [VNat]
  [VZero]
  [VSucc (n Value?)]
  ;vector values
  [VNil (t Value?)]
  [VCons (t Value?) (len Value?) (head Value?) (tail Value?)]
  [VVec (t Value?) (k Value?)]
  )

           

(define-type Neutral
  [NFree (n Name?)]
  [NApp (e1 Neutral?) (e2 Value?)]
  [NNatElim (m Value?) (mz Value?) (ms Value?) (k Neutral?)]
  [NVecElim (t Value?) (m Value?) (mn Value?) (mc Value?) (k Value?) (vs Neutral?)])

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
                       (eval↓ e2 env))]
    [Star () (VStar)]
    [Pi (tdom tcod) (VPi (eval↓ tdom env)
                         (lambda (x) (eval↓ tcod (cons x env))))]
    ;Natural Numbers
    [Nat () (VNat)]
    [Zero () (VZero)]
    [Succ (k) (VSucc (eval↓ k env))]
    [NatElim (m mz ms k)
             (let ([mzVal (eval↓ mz env)]
                   [msVal (eval↓ ms env)])
               (letrec ([rec (lambda (kVal)
                               (type-case Value kVal
                                 [VZero () mzVal]
                                 [VSucc (l) (vapp (vapp msVal l)
                                                  (rec l))]
                                 [VNeutral (k)(begin
                                                (VNeutral
                                                 (NNatElim (eval↓ m env) mzVal msVal k))
                                                )]
                                 [else (error "internal: eval natElim")]))])
                 (rec (eval↓ k env))))]
    ;Vectors
    [Nil (t) (VNil (eval↓ t env))]
    [Vec (t k) (VVec (eval↓ t env)
                     (eval↓ k env))]
    [Cons (t k hd tl)
          (VCons (eval↓ t env)
                 (eval↓ k env)
                 (eval↓ hd env)
                 (eval↓ tl env))]
    [VecElim (t m mn mc k xs)
             (let ([mnVal (eval↓ mn env)]
                   [mcVal (eval↓ mc env)])
               (letrec ([rec (lambda (kVal xsVal)
                               (type-case Value xsVal
                                 [VNil (t) mnVal]
                                 [VCons (t l x xs)
                                        (foldl (λ (x acc) (vapp acc x)) mcVal
                                               (list l x xs (rec l xs)))]
                                 [VNeutral (n)
                                           (VNeutral
                                            (NVecElim (eval↓ t env)
                                                      (eval↓ m env)
                                                      mnVal
                                                      mcVal
                                                      kVal
                                                      n))]
                                 [else (error "internal: eval vecElim")]))])
                 (rec (eval↓ k env) (eval↓ xs env))))]))

;; vapp :: Value -> Value -> Value
(define (vapp v1 v2)
  (type-case Value v1
    [VLam (f) (f v2)]
    [VNeutral (n) (VNeutral (NApp n v2))]
    [VPi (t f) (f v2)]
    [else (error (format "Vapp something that is not appliable! an ~s" v1))]))

;; eval↓ :: Term↓ -> Env -> Value
(define (eval↓ term env)
  (type-case Term↓ term
    [Inf (i) (eval↑ i env)]
    [Lam (e) (VLam (lambda (x) (eval↓ e (cons x env))))]))

(define Type? Value?)

;; type Context = [ (Name, Type) ]
(define Context?
  (listof (cons/c Name? Type?)))

;; type↑0 :: Context -> Term↑ -> Type
(define (type↑0 context term)
  (type↑ 0 context term))

;; type↑ :: Int -> Context -> Term↑ -> Type (Value)
(define (type↑ i Γ term)
  (type-case Term↑ term
    [Ann (e ρ)
         (begin
           (type↓ i Γ ρ (VStar))
           (let ((τ (eval↓ ρ empty)))
             (type↓ i Γ e τ)
             τ))]
    [Star ()
          (VStar)]
    [Pi (ρ ρ^)
        (begin
          (type↓ i Γ ρ (VStar))
          (let ((τ (eval↓ ρ empty)))
            (type↓ (add1 i)
                   (cons (cons (Local i) τ) Γ)
                   (subst↓ 0 (Free (Local i)) ρ^)
                   (VStar)))
          (VStar))]
                   
    [Free (x)
          (if (assoc x Γ)
              (cdr (assoc x Γ))
              (error "unknown identifier - Free (x) ~s in ~s" x Γ))]
    [App (e1 e2)
         (type-case Value (type↑ i Γ e1)
           [VPi (τdom τcod)
                (begin (type↓ i Γ e2 τdom)
                       (τcod (eval↓ e2 empty)))]
           [else (error "illegal application")])]
    ; Natural Numbers
    [Nat () (VStar)]
    [Zero () (VNat)]
    [Succ (k)
          (begin
            (type↓ i Γ k (VNat))
            (VNat))]
    [NatElim (m mz ms k)
             (begin
               (type↓ i Γ m (VPi (VNat) (lambda (x) (VStar))))
               (let ([mVal (eval↓ m empty)])
                 (type↓ i Γ mz (vapp mVal (VZero)))
                 (type↓ i Γ ms (VPi (VNat)
                                    (lambda (l)
                                      (VPi (vapp mVal l)
                                           (lambda (x) (vapp mVal (VSucc l)))))))
                 (type↓ i Γ k (VNat))
                 (let ([kVal (eval↓ k empty)])
                   (vapp mVal kVal))))]
    ; Vectors
    [Vec (t k) (begin
                 (type↓ i Γ t (VStar))
                 (type↓ i Γ k (VNat))
                 (VStar))]
    [Nil (t) (begin
               (type↓ i Γ t (VStar))
               (let ([tVal (eval↓ t empty)])
                 (VVec tVal (VZero))))]
    [Cons (t k x xs)
          (begin
            (type↓ i Γ t (VStar))
            (let ([tVal (eval↓ t empty)])
              (type↓ i Γ k (VNat))
              (let ([kVal (eval↓ k empty)])
                (type↓ i Γ x tVal)
                (type↓ i Γ xs (VVec tVal kVal))
                (VVec tVal (VSucc kVal)))))]
    [VecElim (t m mn mc k vs)
             (begin
               (type↓ i Γ t (VStar))
               (let ([tVal (eval↓ t empty)]
                     [mVal (eval↓ m empty)]
                     [kVal (eval↓ k empty)]
                     [vsVal (eval↓ vs empty)])
                 (type↓ i Γ m
                        (VPi (VNat) (λ (k) (VPi (VVec tVal k)
                                                (λ (x) (VStar))))))
                 (type↓ i Γ mn (vapp (vapp mVal (VZero)) (VNil tVal)))
                 (type↓ i Γ mc
                        (VPi
                         (VNat)
                         (λ (l)
                           (VPi tVal
                                (λ (y)
                                  (VPi (VVec tVal l)
                                       (λ (ys)
                                         (VPi (vapp (vapp mVal l) ys)
                                              (λ (x)
                                                (vapp (vapp mVal (VSucc l))
                                                      (VCons tVal l y ys)))))))))))
                 (type↓ i Γ k (VNat))
                 (type↓ i Γ vs (VVec tVal kVal))
                 (vapp (vapp mVal kVal) vsVal)))]
                                                  
    [else (error "type↑ undefined for bound")]))
             

(define (type↓ i Γ term v)
  (type-case Term↓ term
    [Inf (e)
         (if (Value? v)
             (if (equal? (quotev0 v)
                         (quotev0 (type↑ i Γ e)))
                 (void)
                 (error (format "type mismatch between checked ~s and inferred ~s for exp ~s, under env ~s" v (type↑ i Γ e) e Γ)))
             (error (format "type ~s is not a value" v)))]
    [Lam (e)
         (type-case Value v
           [VPi (τdom τcod)
                (type↓ (add1 i) (cons (cons (Local i)
                                            τdom)
                                      Γ)
                       (subst↓ 0 (Free (Local i)) e) (τcod (vfree (Local i))))]
           [else (error "type mismatch")])]))

;; subst↑ :: Int -> Term↑ -> Term↑ -> Term↑
(define (subst↑ i r t)
  (type-case Term↑ t
    [Ann (e τ) (Ann (subst↓ i r e) τ)]
    [Bound (j) (if (equal? i j)
                   r
                   (Bound j))]
    [Free (y) (Free y)]
    [Star () (Star)]
    [Pi (tdom tcod) (Pi (subst↓ i r tdom)
                        (subst↓ (add1 i) r tcod))]
    [App (e1 e2) (App (subst↑ i r e1)
                      (subst↓ i r e2))]
    [Nat () (Nat)]
    [Zero () (Zero)]
    [Succ (k) (Succ (subst↓ i r k))]
    [NatElim (m mz ms k)
             (NatElim (subst↓ i r m)
                      (subst↓ i r mz)
                      (subst↓ i r ms)
                      (subst↓ i r k))]
    [Vec (t k) (Vec (subst↓ i r t)
                    (subst↓ i r k))]
    [Nil (t) (Nil (subst↓ i r t))]
    [Cons (t k x xs) (Cons (subst↓ i r t)
                           (subst↓ i r k)
                           (subst↓ i r x)
                           (subst↓ i r xs))]
    [VecElim (t m mn mc k vs) (VecElim (subst↓ i r t)
                                       (subst↓ i r m)
                                       (subst↓ i r mn)
                                       (subst↓ i r mc)
                                       (subst↓ i r k)
                                       (subst↓ i r vs))]
    ))

;; subst↓ :: Int -> Term↑ -> Term↓ -> Term↑
(define (subst↓ i r t)
  (type-case Term↓ t
    [Inf (e) (Inf (subst↑ i r e))]
    [Lam (e) (Lam (subst↓ (add1 i) r e))])
  )

;; quotev0 :: Value -> Term↓
(define (quotev0 v)
  (quotev 0 v))

;; quotev :: Int -> Value -> Term↓
(define (quotev i v)
  (type-case Value v
    [VLam (f) (Lam (quotev (add1 i) (f (vfree (Quote i)))))]
    [VNeutral (n) (Inf (neutralQuote i n))]
    [VStar () (Inf (Star))]
    [VNat () (Inf (Nat))]
    [VZero () (Inf (Zero))]
    [VSucc (k) (Inf (Succ (quotev i k)))]
    [VPi (v f) (Inf (Pi (quotev i v)
                        (quotev (add1 i) (f (vfree (Quote i))))))]
    [VNil (t) (Inf (Nil (quotev i t)))]
    [VCons (t l hd tl) (Inf (Cons (quotev i t)
                                  (quotev i l)
                                  (quotev i hd)
                                  (quotev i tl)))]
    [VVec (t l) (Inf (Vec (quotev i t)
                          (quotev i l)))]
    ))

;; neutralQuote :: Int -> Neutral -> Term↑
(define (neutralQuote i neutral)
  (type-case Neutral neutral
    [NFree (x) (boundfree i x)]
    [NApp (n v) (App (neutralQuote i n)
                     (quotev i v))]
    [NNatElim (m mz ms k)
              (NatElim (quotev i m)
                       (quotev i mz)
                       (quotev i ms)
                       (Inf (neutralQuote i k)))]
    [NVecElim (t m mn mc k vs)
              (VecElim (quotev i t)
                       (quotev i m)
                       (quotev i mn)
                       (quotev i mc)
                       (quotev i k)
                       (Inf (neutralQuote i vs)))]
    ))

;;boundfree :: Int -> Name -> Term↑
(define (boundfree i x)
  (type-case Name x
    [Quote (k) (Bound (- i k 1))]
    [else (Free x)]))

(test (quotev 0 (VLam (lambda (x) (VLam (lambda (y) x)))))
      (Lam (Lam (Inf (Bound 1)))))

;; vpi-equal-thunk: VPi Term procedure -> boolean
;; Compares two VPis by unwrapping the lambdas and applying them
;; to dummy values.
;; This function assumes that the lambdas in the compared VPis
;; do not depend on their argument.  Useful to test.

(define (vpi-equal-thunk-f v1 v2-arg v2-f)
  (type-case Value v1
    [VPi (arg f1)
         (let* ([vf1 (f1 (VZero))]
                [simple-vf2 (v2-f (VZero))]
                [v2-arg-checked (if (Value? v2-arg)
                                    v2-arg
                                    (eval↓ v2-arg empty))]
                [vf2 (if (Value? simple-vf2) simple-vf2 (eval↑ simple-vf2 empty))])
           (and (equal? arg v2-arg-checked)
                (if (and (VPi? vf1) (VPi? vf2))
                    (vpi-equal-thunk-f vf1 (VPi-arg vf2) (VPi-f vf2))
                    (equal? vf1 vf2))))]
    [else (error "expected VPi on v1")]))

; gen-nat generates natural values in the language encoding, useful to write tests with big numbers
(define (gen-nat n)
  (if (zero? n)
      (Zero)
      (Succ (Inf (gen-nat (sub1 n))))))

; tests and all the associated terms.
(let* ([id^ (Lam (Inf (Bound 0)))]
       [const^ (Lam (Lam (Inf (Bound 1))))]
       [tfree (lambda (α) (Inf (Free (Global α))))]
       [free (lambda (x) (Inf (Free (Global x))))]
       [term1 (App (Ann id^ (Inf (Pi (tfree "a") (tfree "a"))))
                   (free "y"))]
       [term2 (App (App (Ann const^ (Inf (Pi (Inf (Pi (tfree "b") (tfree "b")))
                                             (Inf (Pi (tfree "a")
                                                      (Inf (Pi (tfree "b") (tfree "b"))))))))
                        id^)
                   (free "y"))]
       [env1 (list (cons (Global "y")
                         (eval↓ (tfree "a") empty))
                   (cons (Global "a")
                         (VStar)))]
       [env2 (cons (cons (Global "b")
                         (VStar))
                   env1)]
       [env3 (list
              (cons (Global "y")
                    (eval↓ (tfree "α") empty))
              (cons (Global "x")
                    (eval↓ (tfree "α") empty))
              (cons (Global "α")
                    (VStar)))]
       [plus (Ann
              (Lam
               (Inf
                (NatElim
                 (Lam (Inf (Pi (Inf (Nat)) (Inf (Nat)))))
                 id^
                 (Lam (Lam (Lam (Inf (Succ (Inf (App (Bound 1) (Inf (Bound 0)))))))))
                 (Inf (Bound 0)))
                ))
              (Inf (Pi (Inf (Nat)) (Inf (Pi (Inf (Nat)) (Inf (Nat)))))))]
       [append (Ann
                (Lam ;The α
                 (Lam ;The m for the first vector's length
                  (Lam ; The first vector (v)
                   (Inf
                    (VecElim (Inf (Bound 2))
                             (Lam
                              (Lam
                               (Inf (Pi (Inf (Nat))
                                        (Inf (Pi (Inf (Vec (Inf (Bound 5)) ;; λα
                                                           (Inf (Bound 0)))) ; n
                                                  (Inf (Vec (Inf (Bound 6)) ;; α
                                                            (Inf (App (App plus (Inf (Bound 3))) ; m
                                                                 (Inf (Bound 1)))))))))))) ; n 
                           (Lam (Lam (Inf (Bound 0))))
                           (Lam ;m
                            (Lam ;v
                             (Lam ;vs
                              (Lam ;rec
                               (Lam ;n
                                (Lam ;w
                                 (Inf
                                  (Cons (Inf (Bound 8)) ;t/α
                                        (Inf (App (App plus (Inf (Bound 5))) ;m
                                                  (Inf (Bound 1)))) ;n
                                        (Inf (Bound 4)) ; v
                                        (Inf (App (App (Bound 2) ; rec
                                                       (Inf (Bound 1))) ; n
                                                  (Inf (Bound 0)))) ; w
                                        ))))))))
                           (Inf (Bound 1)) ;the length of the other vector
                           (Inf (Bound 0)) ;the other vector itself.
                           )))))
                (Inf (Pi (Inf (Star))
                         (Inf (Pi (Inf (Nat))
                                  (Inf (Pi (Inf (Vec (Inf (Bound 1)); α :: * 
                                                     (Inf (Bound 0)))); m :: Nat
                                           (Inf (Pi (Inf (Nat))
                                                    (Inf (Pi (Inf (Vec (Inf (Bound 3)) ;; α :: *
                                                                       (Inf (Bound 0)))) ;; n :: Nat
                                                             (Inf (Vec (Inf (Bound 4)) ;; α :: *
                                                                       (Inf (App (App plus (Inf (Bound 3))) ;; m :: Nat
                                                                                 (Inf (Bound 1)))))))))))))))))]
       )
  (test (quotev0 (eval↑ term1 empty)) (Inf (Free (Global "y"))))
  (test (quotev0 (eval↑ term2 empty)) (Lam (Inf (Bound 0))))
  (test (type↑0 env1 term1) (VNeutral (NFree (Global "a"))))
  (test true
        (vpi-equal-thunk-f (type↑0 env2 term2)
                           (VNeutral (NFree (Global "b")))
                           (lambda (x) (VNeutral (NFree (Global "b"))))))
  (test true
        (vpi-equal-thunk-f (type↑0 env1 plus)
                           (Inf (Nat))
                           (lambda (x) (Pi (Inf (Nat)) (Inf (Nat))))))
  (test (eval↑ (App (App plus (Inf (gen-nat 40))) (Inf (gen-nat 2))) empty)
        (eval↑ (gen-nat 42) empty))
  (test/pred (type↑0 empty append) VPi?)
  
  (test
   (eval↑ (App (App (App (App (App append (Inf (Free (Global "α"))))
                                   (Inf (gen-nat 2)))
                              (Inf (Cons (Inf (Free (Global "α")))
                                         (Inf (gen-nat 1))
                                         (Inf (Free (Global "x")))
                                         (Inf (Cons (Inf (Free (Global "α")))
                                                    (Inf (Zero))
                                                    (Inf (Free (Global "x")))
                                                    (Inf (Nil (Inf (Free (Global "α"))))))))))
                         (Inf (gen-nat 1)))
                    (Inf (Cons (Inf (Free (Global "α")))
                               (Inf (Zero))
                               (Inf (Free (Global "y")))
                               (Inf (Nil (Inf (Free (Global "α"))))))))
               empty)
        (eval↑ (Cons (Inf (Free (Global "α")))
                     (Inf (gen-nat 2))
                     (Inf (Free (Global "x")))
                     (Inf (Cons (Inf (Free (Global "α")))
                                (Inf (gen-nat 1))
                                (Inf (Free (Global "x")))
                                (Inf (Cons (Inf (Free (Global "α")))
                                           (Inf (Zero))
                                           (Inf (Free (Global "y")))
                                           (Inf (Nil (Inf (Free (Global "α"))))))))))
               empty))
  )