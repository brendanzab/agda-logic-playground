module LogicPlayground where


open import Algebra using (Semigroup; CommutativeMonoid; CommutativeSemiring; DistributiveLattice)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (Setoid)


data ⊤ : Set where
  ⊤-intro : ⊤


data ⊥ : Set where


⊥-elim : ∀ {P : Set} → ⊥ → P
⊥-elim ()


¬ : Set → Set
¬ P = P → ⊥


¬-⊥ : ¬ ⊥
¬-⊥ p = p


data _∧_ : Set → Set → Set where
  ∧-intro : ∀ {P Q : Set} → P → Q → P ∧ Q


∧-left : ∀ {P Q} → P ∧ Q → P
∧-left (∧-intro p q) = p


∧-right : ∀ {P Q} → P ∧ Q → Q
∧-right (∧-intro p q) = q


data _∨_ : Set → Set → Set where
  ∨-inl : ∀ {P Q : Set} → P → P ∨ Q
  ∨-inr : ∀ {P Q : Set} → Q → P ∨ Q


infix 4 _↔_


_↔_ : Set → Set → Set
P ↔ Q = (P → Q) ∧ (Q → P)


↔-intro : ∀ {P Q} → (P → Q) → (Q → P) → P ↔ Q
↔-intro p→q q→p = ∧-intro p→q q→p

↔-sym : ∀ {P Q} → (P ↔ Q) → (Q ↔ P)
↔-sym (∧-intro p→q q→p) =
  ∧-intro q→p p→q


↔-refl : ∀ {P : Set} → P ↔ P
↔-refl = ∧-intro (λ p → p) (λ p → p)


↔-trans : ∀ {P Q R} → (P ↔ Q) → (Q ↔ R) → (P ↔ R)
↔-trans (∧-intro p→q q→p) (∧-intro q→r r→q) =
  ∧-intro (λ p → q→r (p→q p))
          (λ r → q→p (r→q r))


instance
  ↔-setoid : Setoid _ _
  ↔-setoid = record
    { Carrier = Set
    ; _≈_     = _↔_
    ; isEquivalence = record
      { refl  = ↔-refl
      ; sym   = ↔-sym
      ; trans = ↔-trans
      }
    }


open import Relation.Binary.PreorderReasoning (Setoid.preorder ↔-setoid)
  renaming (_∼⟨_⟩_ to _↔⟨_⟩_; _≈⟨⟩_ to _↔⟨⟩_)


∨-comm : ∀ P Q → P ∨ Q ↔ Q ∨ P
∨-comm P Q = ↔-intro comm comm
  where
    comm : ∀ {P Q} → P ∨ Q → Q ∨ P
    comm (∨-inl p) = ∨-inr p
    comm (∨-inr q) = ∨-inl q


∨-assoc : ∀ P Q R → (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R)
∨-assoc P Q R = ↔-intro assocˡ assocʳ
  where
    assocˡ : (P ∨ Q) ∨ R → P ∨ (Q ∨ R)
    assocˡ (∨-inl (∨-inl p)) = ∨-inl p
    assocˡ (∨-inl (∨-inr q)) = ∨-inr (∨-inl q)
    assocˡ (∨-inr r)         = ∨-inr (∨-inr r)

    assocʳ : P ∨ (Q ∨ R) → (P ∨ Q) ∨ R
    assocʳ (∨-inl p)         = ∨-inl (∨-inl p)
    assocʳ (∨-inr (∨-inl q)) = ∨-inl (∨-inr q)
    assocʳ (∨-inr (∨-inr r)) = ∨-inr r


∧-comm : ∀ (P Q : Set) → P ∧ Q ↔ Q ∧ P
∧-comm P Q = ↔-intro comm comm
  where
    comm : ∀ {P Q} → P ∧ Q → Q ∧ P
    comm (∧-intro p q) = ∧-intro q p


∧-assoc : ∀ P Q R → (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R)
∧-assoc P Q R = ↔-intro assocˡ assocʳ
  where
    assocˡ : (P ∧ Q) ∧ R → P ∧ (Q ∧ R)
    assocˡ (∧-intro (∧-intro p q) r) = ∧-intro p (∧-intro q r)

    assocʳ : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R
    assocʳ (∧-intro p (∧-intro q r)) = ∧-intro (∧-intro p q) r


∨-cong : ∀ {P Q R S} → (P ↔ Q) → (R ↔ S) → (P ∨ R ↔ Q ∨ S)
∨-cong {P} {Q} {R} {S} (∧-intro p→q q→p) (∧-intro r→s s→r) =
  ↔-intro congˡ congʳ
  where
    congˡ : (P ∨ R) → Q ∨ S
    congˡ (∨-inl p) = ∨-inl (p→q p)
    congˡ (∨-inr r) = ∨-inr (r→s r)

    congʳ : (Q ∨ S) → P ∨ R
    congʳ (∨-inl q) = ∨-inl (q→p q)
    congʳ (∨-inr s) = ∨-inr (s→r s)


∧-cong : ∀ {P Q R S} → (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S)
∧-cong {P} {Q} {R} {S} (∧-intro p→q q→p) (∧-intro r→s s→r) =
  ↔-intro congˡ congʳ
  where
    congˡ : (P ∧ R) → Q ∧ S
    congˡ (∧-intro p r) = ∧-intro (p→q p) (r→s r)

    congʳ : (Q ∧ S) → P ∧ R
    congʳ (∧-intro q s) = ∧-intro (q→p q) (s→r s)


∨-∧-absorptive : (∀ P Q → (P ∨ (P ∧ Q)) ↔ P) × (∀ P Q → (P ∧ (P ∨ Q)) ↔ P)
∨-∧-absorptive = absorptiveˡ , absorptiveʳ
  where
    absorptiveˡ : ∀ P Q → (P ∨ (P ∧ Q)) ↔ P
    absorptiveˡ P Q = ∧-intro absorptiveˡˡ ∨-inl
      where
        absorptiveˡˡ : P ∨ (P ∧ Q) → P
        absorptiveˡˡ (∨-inl p) = p
        absorptiveˡˡ (∨-inr (∧-intro p q)) = p

    absorptiveʳ : ∀ P Q → (P ∧ (P ∨ Q)) ↔ P
    absorptiveʳ P Q = ∧-intro ∧-left absorptiveʳʳ
      where
        absorptiveʳʳ : P → P ∧ (P ∨ Q)
        absorptiveʳʳ p = ∧-intro p (∨-inl p)


∨-∧-distribʳ : ∀ P Q R → (Q ∧ R) ∨ P ↔ (Q ∨ P) ∧ (R ∨ P)
∨-∧-distribʳ P Q R = ∧-intro distribˡ distribʳ
  where
    distribˡ : (Q ∧ R) ∨ P → (Q ∨ P) ∧ (R ∨ P)
    distribˡ (∨-inl (∧-intro q r)) = ∧-intro (∨-inl q) (∨-inl r)
    distribˡ (∨-inr p)             = ∧-intro (∨-inr p) (∨-inr p)

    distribʳ : (Q ∨ P) ∧ (R ∨ P) → (Q ∧ R) ∨ P
    distribʳ (∧-intro (∨-inl q) (∨-inr p)) = ∨-inr p
    distribʳ (∧-intro (∨-inl q) (∨-inl r)) = ∨-inl (∧-intro q r)
    distribʳ (∧-intro (∨-inr p) r∨p)       = ∨-inr p


∧-∨-distribʳ : ∀ P Q R → (Q ∨ R) ∧ P ↔ (Q ∧ P) ∨ (R ∧ P)
∧-∨-distribʳ P Q R = ∧-intro distribˡ distribʳ
  where
    distribˡ : (Q ∨ R) ∧ P → (Q ∧ P) ∨ (R ∧ P)
    distribˡ (∧-intro (∨-inl q) p) = ∨-inl (∧-intro q p)
    distribˡ (∧-intro (∨-inr q) p) = ∨-inr (∧-intro q p)

    distribʳ : (Q ∧ P) ∨ (R ∧ P) → (Q ∨ R) ∧ P
    distribʳ (∨-inl (∧-intro q p)) = ∧-intro (∨-inl q) p
    distribʳ (∨-inr (∧-intro r p)) = ∧-intro (∨-inr r) p


∧-complementʳ : ∀ P → (P ∧ ¬ P) ↔ ⊥
∧-complementʳ P = ↔-intro complementʳˡ ⊥-elim
  where
    complementʳˡ : (P ∧ ¬ P) → ⊥
    complementʳˡ (∧-intro p ¬p) = ¬p p


¬-cong : ∀ {P Q} → (P ↔ Q) → (¬ P ↔ ¬ Q)
¬-cong {P} {Q} (∧-intro p→q q→p) = ∧-intro congˡ congʳ
  where
    congˡ : ¬ P → ¬ Q
    congˡ ¬p p = ¬p (q→p p)

    congʳ : ¬ Q → ¬ P
    congʳ ¬q p = ¬q (p→q p)


∨-identityˡ : ∀ P → (⊥ ∨ P) ↔ P
∨-identityˡ P = ∧-intro identityˡˡ ∨-inr
  where
    identityˡˡ : ⊥ ∨ P → P
    identityˡˡ (∨-inl p) = ⊥-elim p
    identityˡˡ (∨-inr p) = p


∧-identityˡ : ∀ P → (⊤ ∧ P) ↔ P
∧-identityˡ P = ∧-intro ∧-right (∧-intro ⊤-intro)


∧-zeroˡ : ∀ P → ⊥ ∧ P ↔ ⊥
∧-zeroˡ P = ∧-intro ∧-left ⊥-elim


instance
  distributiveLattice : DistributiveLattice _ _
  distributiveLattice = record
    { Carrier = Set
    ; _≈_     = _↔_
    ; _∨_     = _∨_
    ; _∧_     = _∧_
    ; isDistributiveLattice = record
      { ∨-∧-distribʳ = ∨-∧-distribʳ
      ; isLattice = record
        { isEquivalence = Setoid.isEquivalence ↔-setoid
        ; ∨-comm        = ∨-comm
        ; ∨-assoc       = ∨-assoc
        ; ∨-cong        = ∨-cong
        ; ∧-comm        = ∧-comm
        ; ∧-assoc       = ∧-assoc
        ; ∧-cong        = ∧-cong
        ; absorptive    = ∨-∧-absorptive
        }
      }
    }

  ∨-commutativeMonoid : CommutativeMonoid _ _
  ∨-commutativeMonoid = record
    { Carrier  = Set
    ; _≈_      = _↔_
    ; _∙_      = _∨_
    ; ε        = ⊥
    ; isCommutativeMonoid = record
      { identityˡ = ∨-identityˡ
      ; comm      = ∨-comm
      ; isSemigroup = record
        { isEquivalence = Setoid.isEquivalence ↔-setoid
        ; assoc         = ∨-assoc
        ; ∙-cong        = ∨-cong
        }
      }
    }


  ∧-commutativeMonoid : CommutativeMonoid _ _
  ∧-commutativeMonoid = record
    { Carrier  = Set
    ; _≈_      = _↔_
    ; _∙_      = _∧_
    ; ε        = ⊤
    ; isCommutativeMonoid = record
      { identityˡ = ∧-identityˡ
      ; comm      = ∧-comm
      ; isSemigroup = record
        { isEquivalence = Setoid.isEquivalence ↔-setoid
        ; assoc         = ∧-assoc
        ; ∙-cong        = ∧-cong
        }
      }
    }

  ∨-∧-commutativeSemiring : CommutativeSemiring _ _
  ∨-∧-commutativeSemiring = record
    { Carrier = Set
    ; _≈_     = _↔_
    ; _+_     = _∨_
    ; _*_     = _∧_
    ; 0#      = ⊥
    ; 1#      = ⊤
    ; isCommutativeSemiring = record
      { distribʳ              = ∧-∨-distribʳ
      ; zeroˡ                 = ∧-zeroˡ
      ; +-isCommutativeMonoid = isCommutativeMonoid ∨-commutativeMonoid
      ; *-isCommutativeMonoid = isCommutativeMonoid ∧-commutativeMonoid
      }
    }
    where
      open CommutativeMonoid using (isCommutativeMonoid)


modus-ponens : ∀ {P Q} → P ∧ (P → Q) → Q
modus-ponens (∧-intro p p→q) = p→q p


modus-tollens : ∀ {P Q} → ¬ Q ∧ (P → Q) → ¬ P
modus-tollens (∧-intro ¬q p→q) p = ¬q (p→q p)


∧-compose : ∀ {P Q R} → (P → Q) ∧ (P → R) → (P → (Q ∧ R))
∧-compose (∧-intro p→q p→r) p = ∧-intro (p→q p) (p→r p)


∨-compose : ∀ {P Q R} → (P → Q) ∨ (P → R) → (P → (Q ∨ R))
∨-compose (∨-inl p→q) p = ∨-inl (p→q p)
∨-compose (∨-inr p→r) p = ∨-inr (p→r p)


double-¬ : ∀ {P : Set} → P → ¬ (¬ P)
double-¬ p ¬p = ¬p p


∧-tautology : ∀ P → P ↔ P ∧ P
∧-tautology P = ↔-intro tautˡ ∧-left
  where
    tautˡ : P → P ∧ P
    tautˡ p = ∧-intro p p


∨-tautology : ∀ P → P ↔ P ∨ P
∨-tautology P = ↔-intro ∨-inl tautʳ
  where
    tautʳ : P ∨ P → P
    tautʳ (∨-inl p) = p
    tautʳ (∨-inr p) = p
