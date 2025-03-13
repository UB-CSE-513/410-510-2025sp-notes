module Lambda where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s)

data Expr : Set where
  ‵_ : ℕ → Expr
  ƛ⇒_ : Expr → Expr
  _·_ : Expr → Expr → Expr

Renaming : Set
Renaming = ℕ → ℕ

↑ᵣ : Renaming → Renaming
↑ᵣ ξ zero = zero
↑ᵣ ξ (suc x) = suc (ξ x)

_⟨_⟩ : Expr → Renaming → Expr
(‵ x) ⟨ ξ ⟩ = ‵ (ξ x)
(ƛ⇒ e) ⟨ ξ ⟩ = ƛ⇒ (e ⟨ ↑ᵣ ξ ⟩)
(e₁ · e₂) ⟨ ξ ⟩ = (e₁ ⟨ ξ ⟩) · (e₂ ⟨ ξ ⟩)

Substitution : Set
Substitution = ℕ → Expr

↑ : Substitution → Substitution
↑ σ zero = ‵ zero
↑ σ (suc x) = (σ x) ⟨ suc ⟩

_[_] : Expr → Substitution → Expr
(‵ x) [ σ ] = σ x
(ƛ⇒ e) [ σ ] = ƛ⇒ (e [ ↑ σ ])
(e₁ · e₂) [ σ ] = (e₁ [ σ ]) · (e₂ [ σ ])

zsubst : Expr → Substitution
zsubst e zero = e
zsubst e (suc n) = ‵ n

_[0↦_] : Expr → Expr → Expr
e [0↦ e' ] = e [ (zsubst e') ]

infixr 4 _→β_
data _→β_ : Expr → Expr → Set where
  in-app₁ : ∀ {e₁ e₁′ e₂ : Expr} →
            e₁ →β e₁′ →
    ---------------------------
     (e₁ · e₂) →β (e₁′ · e₂)
  in-app₂ : ∀ {e₁ e₂ e₂′ : Expr} →
            e₂ →β e₂′ →
    ---------------------------
     (e₁ · e₂) →β (e₁ · e₂′)
  in-abs : ∀ {e e′ : Expr} →
          e →β e′ →
    ------------------------
     (ƛ⇒ e) →β (ƛ⇒ e′)
  β : ∀ {e e′ : Expr} →
    ((ƛ⇒ e) · e′) →β (e [0↦ e′ ])

infixr 4 _→β*_
data _→β*_ : Expr → Expr → Set where
  refl : ∀ {e : Expr} → e →β* e
  step : ∀ {e₁ e₂ e₃ : Expr} → e₁ →β e₂ → e₂ →β* e₃ → e₁ →β* e₃

β*-trans : ∀ {e₁ e₂ e₃ : Expr} → e₁ →β* e₂ → e₂ →β* e₃ → e₁ →β* e₃
β*-trans refl stps2 = stps2
β*-trans (step stp stps1) stps2 = step stp (β*-trans stps1 stps2)

β-β* : ∀ {e₁ e₂ : Expr} → e₁ →β e₂ → e₁ →β* e₂
β-β* stp = step stp refl

in-app₁* : ∀ {e₁ e₁′ e₂ : Expr} →
  e₁ →β* e₁′ →
  (e₁ · e₂) →β* (e₁′ · e₂)
in-app₁* refl = refl
in-app₁* (step stp stps) = step (in-app₁ stp) (in-app₁* stps)

in-app₂* : ∀ {e₁ e₂ e₂′ : Expr} →
  e₂ →β* e₂′ →
  (e₁ · e₂) →β* (e₁ · e₂′)
in-app₂* refl = refl
in-app₂* (step stp stps) = step (in-app₂ stp) (in-app₂* stps)

in-abs* : ∀ {e e′ : Expr} →
  e →β* e′ →
  (ƛ⇒ e) →β* (ƛ⇒ e′)
in-abs* refl = refl
in-abs* (step stp stps) = step (in-abs stp) (in-abs* stps)

{- Renaming is extensional -}
upren-ext : ∀ {ξ₁ ξ₂ : Renaming} → (∀ {n} → ξ₁ n ≡ ξ₂ n) → ∀ {n} → (↑ᵣ ξ₁) n ≡ (↑ᵣ ξ₂) n
upren-ext eq {zero} = refl
upren-ext eq {suc n} = cong suc eq

ren-ext : ∀ {ξ₁ ξ₂ : Renaming} → (∀ {n : ℕ} → ξ₁ n ≡ ξ₂ n) → ∀ (e : Expr) → e ⟨ ξ₁ ⟩ ≡ e ⟨ ξ₂ ⟩
ren-ext eq (‵ x) = cong (‵_) eq
ren-ext {ξ₁} {ξ₂} eq (ƛ⇒ e) rewrite ren-ext  {↑ᵣ ξ₁} {↑ᵣ ξ₂} (upren-ext eq) e = refl
ren-ext {ξ₁} {ξ₂} eq (e₁ · e₂) rewrite ren-ext {ξ₁} {ξ₂} eq e₁ | ren-ext {ξ₁} {ξ₂} eq e₂ = refl

{- Substitution is extensional -}
upsubst-ext : ∀ {σ₁ σ₂ : Substitution} → (∀ {n} → σ₁ n ≡ σ₂ n) → ∀ {n} → (↑ σ₁) n ≡ (↑ σ₂) n
upsubst-ext eq {zero} = refl
upsubst-ext eq {suc n} = cong (_⟨ suc ⟩) eq

subst-ext : ∀ {σ₁ σ₂ : Substitution} → (∀ {n} → σ₁ n ≡ σ₂ n) → ∀ e → e [ σ₁ ] ≡ e [ σ₂ ]
subst-ext eq (‵ x) = eq
subst-ext {σ₁} {σ₂} eq (ƛ⇒ e) = cong ƛ⇒_ (subst-ext {↑ σ₁} {↑ σ₂} (λ {n} → upsubst-ext {σ₁} {σ₂} eq {n}) e)
subst-ext {σ₁} {σ₂} eq (e₁ · e₂) rewrite subst-ext {σ₁} {σ₂} eq e₁ | subst-ext {σ₁} {σ₂} eq e₂ = refl

{- Renaming with the identity function does not change the term -}
id-upren : ∀ {n : ℕ} → (↑ᵣ (λ x → x)) n ≡ (λ x → x) n
id-upren {zero} = refl
id-upren {suc n} = refl

id-ren : ∀ {e : Expr} → (e ⟨ (λ x → x) ⟩) ≡ e
id-ren {‵ x} = refl
id-ren {ƛ⇒ e} rewrite ren-ext {↑ᵣ (λ x → x)} {λ x → x} id-upren e | id-ren {e} = refl 
id-ren {e₁ · e₂} rewrite id-ren {e₁} | id-ren {e₂} = refl

{- Renaming with the identity substitution does not change the term -}
id-substitution : Substitution
id-substitution = ‵_

id-substitution-up : ∀ {n} → (↑ id-substitution) n ≡ id-substitution n
id-substitution-up {zero} = refl
id-substitution-up {suc n} = refl

id-subst : ∀ {e : Expr} → (e [ id-substitution ]) ≡ e
id-subst {‵ x} = refl
id-subst {ƛ⇒ e} rewrite subst-ext {↑ id-substitution} {id-substitution} id-substitution-up e | id-subst {e} = refl
id-subst {e₁ · e₂} rewrite id-subst {e₁} | id-subst {e₂} = refl

{- Renaming is a form of substitution -}
ren-subst-up : ∀ {ξ} {n} → (‵ ↑ᵣ ξ n) ≡ ↑ (λ x → ‵ ξ x) n
ren-subst-up {ξ} {zero} = refl
ren-subst-up {ξ} {suc n} = refl

ren-subst : ∀ {e : Expr} {ξ : Renaming} →
  e ⟨ ξ ⟩ ≡ e [ (λ x → ‵ ξ x) ]
ren-subst {‵ x} {ξ} = refl
ren-subst {ƛ⇒ e} {ξ} = cong (ƛ⇒_) (trans (ren-subst {e} {↑ᵣ ξ}) (subst-ext {λ x → (‵ ((↑ᵣ ξ) x))} {↑ (λ x → ‵ ξ x)} ren-subst-up e))
ren-subst {e₁ · e₂} {ξ} rewrite ren-subst {e₁} {ξ} | ren-subst {e₂} {ξ} = refl

{- Closure -}
data ClosedAbove : Expr → ℕ → Set where
  closed-var : ∀ {k n} → k < n → ClosedAbove (‵ k) n
  closed-abs : ∀ {n e} → ClosedAbove e (suc n) → ClosedAbove (ƛ⇒ e) n
  closed-app : ∀ {n e₁ e₂} → ClosedAbove e₁ n → ClosedAbove e₂ n → ClosedAbove (e₁ · e₂) n

Closed : Expr → Set
Closed e = ClosedAbove e 0

up-nonfree : ∀ {σ : Substitution} {n : ℕ} → 
  (∀ m → m < n → σ m ≡ ‵ m) →
  ∀ m → m < suc n → (↑ σ) m ≡ ‵ m
up-nonfree {σ} {n} bd zero m<sn = refl
up-nonfree {σ} {n} bd (suc m) (s≤s m<sn) rewrite bd m m<sn = refl

subst-nonfree : ∀ {σ : Substitution} {n : ℕ} {e : Expr} →
  ClosedAbove e n →
  (∀ m → m < n → σ m ≡ ‵ m) →
  e [ σ ] ≡ e
subst-nonfree {σ} {n} {‵ x} (closed-var x<n) bd = bd x x<n
subst-nonfree {σ} {n} {ƛ⇒ e} (closed-abs clsd) bd rewrite subst-nonfree {↑ σ} {suc n} {e} clsd (up-nonfree bd) = refl
subst-nonfree {σ} {n} {e₁ · e₂} (closed-app clsd₁ clsd₂) bd rewrite subst-nonfree {σ} {n} {e₁} clsd₁ bd | subst-nonfree {σ} {n} {e₂} clsd₂ bd = refl

subst-closed : ∀ (e : Expr) → Closed e → ∀ (σ : Substitution) → e [ σ ] ≡ e
subst-closed e clsd σ = subst-nonfree {σ} {0} {e} clsd (λ m → λ ())

data val : Expr → Set where
  abs : ∀ {e : Expr} → val (ƛ⇒ e)

infixr 4 _→CBV_
data _→CBV_ : Expr → Expr → Set where
  in-app₁ : ∀ {e₁ e₁′ e₂} →
    e₁ →CBV e₁′ →
    --------------
    e₁ · e₂ →CBV e₁′ · e₂
  in-app₂ : ∀ {v e₂ e₂′} →
    val v →
    e₂ →CBV e₂′ →
    ----------------
    v · e₂ →CBV v · e₂′
  β : ∀ {e v : Expr} →
    val v → 
    ((ƛ⇒ e) · v) →CBV (e [0↦ v ])
