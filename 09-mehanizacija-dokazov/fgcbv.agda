data Ty : Set where
    BOOL : Ty
    _⇒_ : Ty → Ty → Ty
    _×_ : Ty → Ty → Ty

data Ctx : Set where
    ∅ : Ctx
    _,_ : Ctx → Ty → Ctx

data _∈_ : Ty → Ctx → Set where
    Z : {A : Ty} {Γ : Ctx} → A ∈ (Γ , A)
    S : {A B : Ty} {Γ : Ctx} → A ∈ Γ → A ∈ (Γ , B)

mutual
    data _⊢v_ : Ctx → Ty → Set where

        VAR : {Γ : Ctx} {A : Ty} →
            A ∈ Γ →
            -----
            Γ ⊢v A

        TRUE : {Γ : Ctx} →
            --------
            Γ ⊢v BOOL

        FALSE : {Γ : Ctx} →
            --------
            Γ ⊢v BOOL

        ƛ : {Γ : Ctx} {A B : Ty} →
            (Γ , A) ⊢c B →
            -----------
            Γ ⊢v (A ⇒ B)

        ⟨_,_⟩ : {Γ : Ctx} {A B : Ty} →
            Γ ⊢v A →
            Γ ⊢v B →
            -----------
            Γ ⊢v (A × B)
        
    data _⊢c_ : Ctx → Ty → Set where

        IF_THEN_ELSE_ : {Γ : Ctx} {A : Ty} →
            Γ ⊢v BOOL →
            Γ ⊢c A →
            Γ ⊢c A →
            -----
            Γ ⊢c A

        _∙_ : {Γ : Ctx} {A B : Ty} →
            Γ ⊢v (A ⇒ B) →
            Γ ⊢v A →
            -----
            Γ ⊢c B

        FST : {Γ : Ctx} {A B : Ty} →
            Γ ⊢v (A × B) →
            -----
            Γ ⊢c A

        SND : {Γ : Ctx} {A B : Ty} →
            Γ ⊢v (A × B) →
            -----
            Γ ⊢c B
        
        RETURN : {Γ : Ctx} {A : Ty} →
            Γ ⊢v A →
            ------
            Γ ⊢c A

extend-renaming : {Γ Δ : Ctx}
  → ({A : Ty} → A ∈ Γ → A ∈ Δ)
    --------------------------------------
  → {A B : Ty} → A ∈ (Γ , B) → A ∈ (Δ , B)
extend-renaming ρ Z = Z
extend-renaming ρ (S x) = S (ρ x)

rename-v : {Γ Δ : Ctx}
  → ({A : Ty} → A ∈ Γ → A ∈ Δ)
    ---------------------------
  → {A : Ty} → Γ ⊢v A → Δ ⊢v A
rename-c : {Γ Δ : Ctx}
  → ({A : Ty} → A ∈ Γ → A ∈ Δ)
    ---------------------------
  → {A : Ty} → Γ ⊢c A → Δ ⊢c A
rename-v ρ (VAR x) = VAR (ρ x)
rename-v ρ TRUE = TRUE
rename-v ρ FALSE = FALSE
rename-v ρ (ƛ M) = ƛ (rename-c (extend-renaming ρ) M)
rename-v ρ ⟨ V , W ⟩ = ⟨ rename-v ρ V , rename-v ρ W ⟩
rename-c ρ (IF V THEN M₁ ELSE M₂) = 
    IF (rename-v ρ V) THEN (rename-c ρ M₁) ELSE (rename-c ρ M₂)
rename-c ρ (V ∙ W) = rename-v ρ V ∙ rename-v ρ W
rename-c ρ (FST V) = FST (rename-v ρ V)
rename-c ρ (SND V) = SND (rename-v ρ V)
rename-c ρ (RETURN V) = RETURN (rename-v ρ V)

extend-subst : {Γ Δ : Ctx}
  → ({A : Ty} → A ∈ Γ → Δ ⊢v A)
    ---------------------------------------
  → {A B : Ty} → A ∈ (Γ , B) → (Δ , B) ⊢v A
extend-subst σ Z = VAR Z
extend-subst σ (S x) = rename-v S (σ x)

subst-v : {Γ Δ : Ctx}
  → ({A : Ty} → A ∈ Γ → Δ ⊢v A)
    -------------------------
  → {A : Ty} → Γ ⊢v A → Δ ⊢v A
subst-c : {Γ Δ : Ctx}
  → ({A : Ty} → A ∈ Γ → Δ ⊢v A)
    -------------------------
  → {A : Ty} → Γ ⊢c A → Δ ⊢c A
subst-v σ (VAR x) = σ x
subst-v σ TRUE = TRUE
subst-v σ FALSE = TRUE
subst-v σ (ƛ M) = ƛ (subst-c (extend-subst σ) M)
subst-v σ ⟨ V , W ⟩ = ⟨ subst-v σ V , subst-v σ W ⟩
subst-c σ (IF V THEN M₁ ELSE M₂) = 
    IF (subst-v σ V) THEN (subst-c σ M₁) ELSE (subst-c σ M₂)
subst-c σ (V ∙ W) = subst-v σ V ∙ subst-v σ W
subst-c σ (FST V) = FST (subst-v σ V)
subst-c σ (SND V) = SND (subst-v σ V)
subst-c σ (RETURN V) = RETURN (subst-v σ V)

_[_] : {Γ : Ctx} {A B : Ty}
  → (Γ , B) ⊢c A
  → Γ ⊢v B
    -----
  → Γ ⊢c A
_[_] {Γ} {B = B} M V = subst-c σ M
  where
  σ : ∀ {A : Ty} → A ∈ (Γ , B) → Γ ⊢v A
  σ Z = V
  σ (S x) = VAR x


data _↝_ : {A : Ty} → ∅ ⊢c A → ∅ ⊢c A → Set where
    IF-TRUE : {A : Ty} {M₁ M₂ : ∅ ⊢c A} →
        ------------------------------
        (IF TRUE THEN M₁ ELSE M₂) ↝ M₁
    IF-FALSE : {A : Ty} {M₁ M₂ : ∅ ⊢c A} →
        ------------------------------
        (IF FALSE THEN M₁ ELSE M₂) ↝ M₂
    APP-BETA : {A B : Ty} {M : (∅ , A) ⊢c B} {V : ∅ ⊢v A} →
        ------------------------------------------------
        ((ƛ M) ∙ V) ↝ ( M [ V ])
    FST-BETA : {A B : Ty} {V : ∅ ⊢v A} {W : ∅ ⊢v B} →
        ------------------------------------------------
        FST ⟨ V , W ⟩ ↝ (RETURN V)
    SND-BETA : {A B : Ty} {V : ∅ ⊢v A} {W : ∅ ⊢v B} →
        ------------------------------------------------
        SND ⟨ V , W ⟩ ↝ (RETURN W)


data progresses : {A : Ty} → ∅ ⊢c A → Set where
    is-value : {A : Ty} {V : ∅ ⊢v A} →
        ---------------------
        progresses (RETURN V)
    steps : {A : Ty} {M M' : ∅ ⊢c A} →
        M ↝ M' →
        ------------
        progresses M

progress : {A : Ty} → (M : ∅ ⊢c A) → progresses M

progress (IF TRUE THEN M ELSE N) = steps IF-TRUE
progress (IF FALSE THEN M ELSE N) = steps IF-FALSE
progress (ƛ M ∙ V) = steps APP-BETA
progress (FST ⟨ V , W ⟩) = steps FST-BETA
progress (SND ⟨ V , W ⟩) = steps SND-BETA
progress (RETURN V) = is-value
