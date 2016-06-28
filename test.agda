open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat hiding (_⊔_)
open import Data.Unit using (⊤; tt)
open import Data.String hiding (_≟_)
open import Data.Empty using (⊥)
open import Function using (_∘_; id; flip; const)
open import Relation.Unary hiding (Decidable)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (¬_)

Nat : Pred ℕ lzero
Nat = const ⊤

Str : Pred String lzero
Str = const ⊤

module _ where

  foo : 42 ∈ Nat
  foo = tt

  bar : "Hello" ∈ Str
  bar = tt

  buz : ∀ (n : ℕ) → n ∉ ∅
  buz = const id

  quz : ∀ (s : String) → s ∈ U
  quz = const tt

  test : ｛ 42 ｝ ⊆ U
  test = const tt

  test2 : ｛ "Hello" ｝ ⊆ U
  test2 = const tt

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd  : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(suc (k * 2))) | odd k = even (suc k)

Odd : ℕ → Set
Odd n with parity n
Odd .(k * 2) | even k = ⊥
Odd .(suc (k * 2)) | odd k = ⊤

Even : ℕ → Set
Even n with parity n
Even .(k * 2) | even k = ⊤
Even .(suc (k * 2)) | odd k = ⊥

Evenℕ : Pred ℕ lzero
Evenℕ = Even

Oddℕ : Pred ℕ lzero
Oddℕ = Odd

module _ where

  test3 : 3 ∈ Oddℕ
  test3 = tt

  test4 : 3 ∉ Evenℕ
  test4 = id

  test5 : 8 ∈ Evenℕ
  test5 = tt

  test6 : 21 ∉ Evenℕ
  test6 = id


-- data _≈_ {a ℓ} {S : Set a} : (A : Pred S ℓ) → (B : Pred S ℓ) → Set (a ⊔ lsuc ℓ) where
--   eql :  ∀ {A B} → A ⊆ B × A ⊇ B → A ≈ B

infix 3 _≈_

record _≈_ {a ℓ} {S : Set a} (A : Pred S ℓ) (B : Pred S ℓ) : Set (a ⊔ lsuc ℓ) where
  field
    eql : A ⊆ B × A ⊇ B

module _  where
  open import Data.Fin hiding (_<_)
  open import Data.Nat.Primality using (Prime)
  open import Data.Empty using (⊥-elim)
  open import Data.Fin hiding (_<_; _≤_)
  open import Data.Nat.Divisibility using (divides; _∣_)
  open import Relation.Binary.PropositionalEquality using (cong)


  A : Pred ℕ lzero
  A n = 2 < n × n < 10 × Prime n

  B : Pred ℕ lzero
  B n = 1 < n × n < 8 × Odd n

  help : ∀ k → 2 < (k * 2) → ¬ Prime (k * 2)
  help zero 2<k*2 x = x
  help (suc zero) (s≤s (s≤s ())) x
  help (suc (suc k)) (s≤s (s≤s (s≤s z≤n))) x = x zero (divides (suc (suc k)) refl)

  A≈B : A ≈ B
  A≈B = record { eql = A⊆B , A⊇B }
    where
      A⊆B : A ⊆ B
      A⊆B {n} prf with parity n
      A⊆B (proj₁ , proj₂ , proj₃) | even k = ⊥-elim (help k proj₁ proj₃)
      A⊆B (s≤s () , prf) | odd zero
      A⊆B prf | odd (suc zero) = s≤s (s≤s z≤n) , (s≤s (s≤s (s≤s (s≤s z≤n))) , tt)
      A⊆B prf | odd (suc (suc zero)) = s≤s (s≤s z≤n) , s≤s (s≤s (s≤s (proj₁ prf))) , tt
      A⊆B prf | odd (suc (suc (suc zero))) = s≤s (s≤s z≤n) , s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))), tt
      A⊆B (proj₁ , proj₂ , proj₃) | odd (suc (suc (suc (suc zero))))
        = ⊥-elim (proj₃ (suc zero) (divides (suc (suc (suc zero))) refl))
      A⊆B (proj₁ , s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))) , proj₃) | odd (suc (suc (suc (suc (suc k)))))

      A⊇B : A ⊇ B
      A⊇B {n} prf with parity n
      A⊇B (proj₁ , proj₂ , ()) | even k
      A⊇B (s≤s () , prf) | odd zero
      A⊇B prf | odd (suc zero) = (s≤s (s≤s (s≤s z≤n))) , ((s≤s (s≤s (s≤s (s≤s z≤n)))) , help₁)
        where
          3≢q*2 : ∀ q → 3 ≡ q * 2 → ⊥
          3≢q*2 zero ()
          3≢q*2 (suc zero) ()
          3≢q*2 (suc (suc q)) ()
          help₁ : ∀ i → suc (suc (toℕ i)) ∣ 3 → ⊥
          help₁ zero (divides q eq) = ⊥-elim (3≢q*2 q eq)
          help₁ (suc ()) x
      A⊇B prf | odd (suc (suc zero))
        = (s≤s (s≤s (s≤s z≤n))) , ((s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) , help₁)
        where
          5≢q*2 : ∀ q → 5 ≡ q * 2 → ⊥
          5≢q*2 zero ()
          5≢q*2 (suc zero) ()
          5≢q*2 (suc (suc zero)) ()
          5≢q*2 (suc (suc (suc q))) ()
          5≢q*3 : ∀ q → 5 ≡ q * 3 → ⊥
          5≢q*3 zero ()
          5≢q*3 (suc zero) ()
          5≢q*3 (suc (suc q)) ()
          5≢q*4 : ∀ q → 5 ≡ q * 4 → ⊥
          5≢q*4 zero ()
          5≢q*4 (suc zero) ()
          5≢q*4 (suc (suc q)) ()
          help₁ : ∀ i → suc (suc (toℕ i)) ∣ 5 → ⊥
          help₁ zero (divides q eq) = ⊥-elim (5≢q*2 q eq)
          help₁ (suc zero) (divides q eq) = ⊥-elim (5≢q*3 q eq)
          help₁ (suc (suc zero)) (divides q eq) = ⊥-elim (5≢q*4 q eq)
          help₁ (suc (suc (suc ()))) x
      A⊇B prf | odd (suc (suc (suc zero)))
        = (s≤s (s≤s (s≤s z≤n))) , ((s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) , help₁)
        where
          7≢q*2 : ∀ q → 7 ≡ q * 2 → ⊥
          7≢q*2 zero ()
          7≢q*2 (suc zero) ()
          7≢q*2 (suc (suc zero)) ()
          7≢q*2 (suc (suc (suc zero))) ()
          7≢q*2 (suc (suc (suc (suc q)))) ()
          7≢q*3 : ∀ q → 7 ≡ q * 3 → ⊥
          7≢q*3 zero ()
          7≢q*3 (suc zero) ()
          7≢q*3 (suc (suc zero)) ()
          7≢q*3 (suc (suc (suc q))) ()
          7≢q*4 : ∀ q → 7 ≡ q * 4 → ⊥
          7≢q*4 zero ()
          7≢q*4 (suc zero) ()
          7≢q*4 (suc (suc q)) ()
          7≢q*5 : ∀ q → 7 ≡ q * 5 → ⊥
          7≢q*5 zero ()
          7≢q*5 (suc zero) ()
          7≢q*5 (suc (suc q)) ()
          7≢q*6 : ∀ q → 7 ≡ q * 6 → ⊥
          7≢q*6 zero ()
          7≢q*6 (suc zero) ()
          7≢q*6 (suc (suc q)) ()
          help₁ : ∀ i → suc (suc (toℕ i)) ∣ 7 → ⊥
          help₁ zero (divides q eq) = ⊥-elim (7≢q*2 q eq)
          help₁ (suc zero) (divides q eq) = ⊥-elim (7≢q*3 q eq)
          help₁ (suc (suc zero)) (divides q eq) = ⊥-elim (7≢q*4 q eq)
          help₁ (suc (suc (suc zero))) (divides q eq) = ⊥-elim (7≢q*5 q eq)
          help₁ (suc (suc (suc (suc zero)))) (divides q eq) = ⊥-elim (7≢q*6 q eq)
          help₁ (suc (suc (suc (suc (suc ()))))) x
      A⊇B (proj₁ , s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))) , proj₃) | odd (suc (suc (suc (suc k))))

  A⊇B×B⊇C⇒A⊇C : ∀ {ℓ ℓ₀ ℓ₁ ℓ₂} {X : Set ℓ} {A : Pred X ℓ₀} {B : Pred X ℓ₁} {C : Pred X ℓ₂} →
                  A ⊇ B × B ⊇ C → A ⊇ C
  A⊇B×B⊇C⇒A⊇C (B⊆A , C⊆B) x∈C = B⊆A (C⊆B x∈C)
  A⊆B×B⊆C⇒A⊆C : ∀ {ℓ ℓ₀ ℓ₁ ℓ₂} {X : Set ℓ} {A : Pred X ℓ₀} {B : Pred X ℓ₁} {C : Pred X ℓ₂} →
                  A ⊆ B × B ⊆ C → A ⊆ C
  A⊆B×B⊆C⇒A⊆C (A⊆B , B⊆C) x∈A = B⊆C (A⊆B x∈A)

module _ where
  open import Data.Sum using (_⊎_; inj₁; inj₂)

  ∅⊆A : ∀ {ℓ} {X : Set ℓ} {A : Pred X lzero} → ∅ ⊆ A
  ∅⊆A ()

  even∪odd≡nat : Oddℕ ∪ Evenℕ ≈ Nat
  even∪odd≡nat = record { eql = helpₗ , helpᵣ }
    where
      helpₗ : Oddℕ ∪ Evenℕ ⊆ Nat
      helpₗ prf = tt
      helpᵣ : Oddℕ ∪ Evenℕ ⊇ Nat
      helpᵣ {x} prf with parity x
      helpᵣ prf | even k = inj₂ tt
      helpᵣ prf | odd k = inj₁ tt

  A⊆A∪B : ∀ {ℓ₀ ℓ₁ ℓ}{X : Set ℓ}{A : Pred X ℓ₀}{B : Pred X ℓ₁} → A ⊆ A ∪ B
  A⊆A∪B = inj₁

  B⊆A∪B : ∀ {ℓ₀ ℓ₁ ℓ}{X : Set ℓ}{A : Pred X ℓ₀}{B : Pred X ℓ₁} → B ⊆ A ∪ B
  B⊆A∪B = inj₂

  A⊆C×B⊆C⇒A∪B⊆C : ∀ {ℓ ℓ₀ ℓ₁ ℓ₂}{X : Set ℓ}{A : Pred X ℓ₀}{B : Pred X ℓ₁}{C : Pred X ℓ₂} →
                  A ⊆ C × B ⊆ C → A ∪ B ⊆ C
  A⊆C×B⊆C⇒A∪B⊆C (A⊆C , B⊆C) (inj₁ x∈A) = A⊆C x∈A
  A⊆C×B⊆C⇒A∪B⊆C (A⊆C , B⊆C) (inj₂ x∈B) = B⊆C x∈B

  A∪A≈A : ∀ {ℓ ℓ₀}{X : Set ℓ}{A : Pred X ℓ₀} → A ∪ A ≈ A
  A∪A≈A {A = A} = record { eql =  A∪A⊆A A  , A∪A⊇A A }
    where
      A∪A⊆A : ∀ {ℓ ℓ₀} {X : Set ℓ} (A : Pred X ℓ₀) → A ∪ A ⊆ A
      A∪A⊆A _ (inj₁ x∈A) = x∈A
      A∪A⊆A _ (inj₂ x∈A) = x∈A
      A∪A⊇A : ∀ {ℓ ℓ₀} {X : Set ℓ} (A : Pred X ℓ₀) → A ∪ A ⊇ A
      A∪A⊇A _ x∈A = inj₁ x∈A

  A∪B≈B∪A : ∀ {ℓ ℓ₀ ℓ₁}{X : Set ℓ}{A : Pred X ℓ₀}{B : Pred X ℓ₁} → A ∪ B ≈ B ∪ A
  A∪B≈B∪A {A = A} {B} = record { eql = A∪B⊆B∪A A B , A∪B⊇B∪A B A }
    where
      A∪B⊆B∪A : ∀ {ℓ ℓ₀ ℓ₁} {X : Set ℓ} (A : Pred X ℓ₀) (B : Pred X ℓ₁) → A ∪ B ⊆ B ∪ A
      A∪B⊆B∪A _ _ (inj₁ x∈A) = inj₂ x∈A
      A∪B⊆B∪A _ _ (inj₂ x∈B) = inj₁ x∈B

      A∪B⊇B∪A : ∀ {ℓ ℓ₀ ℓ₁} {X : Set ℓ} (A : Pred X ℓ₀) (B : Pred X ℓ₁) → B ∪ A ⊇ A ∪ B
      A∪B⊇B∪A _ _ (inj₁ x∈A) = inj₂ x∈A
      A∪B⊇B∪A _ _ (inj₂ x∈B) = inj₁ x∈B

  [A∪B]∪C≈A∪[B∪C] : ∀ {ℓ ℓ₀ ℓ₁ ℓ₂}{X : Set ℓ}{A : Pred X ℓ₀}{B : Pred X ℓ₁}{C : Pred X ℓ₂} →
                    (A ∪ B) ∪ C ≈ A ∪ (B ∪ C)
  [A∪B]∪C≈A∪[B∪C] {A = A} {B} {C} = record { eql = [A∪B]∪C⊆A∪[B∪C] A B C , [A∪B]∪C⊇A∪[B∪C] A B C }
    where
      [A∪B]∪C⊆A∪[B∪C] : ∀ {ℓ ℓ₀ ℓ₁ ℓ₂} {X : Set ℓ}
                          (A : Pred X ℓ₀) (B : Pred X ℓ₁) (C : Pred X ℓ₂) →
                          (A ∪ B) ∪ C ⊆ A ∪ (B ∪ C)
      [A∪B]∪C⊆A∪[B∪C] _ _ _ (inj₁ (inj₁ x∈A)) = inj₁ x∈A
      [A∪B]∪C⊆A∪[B∪C] _ _ _ (inj₁ (inj₂ x∈B)) = inj₂ (inj₁ x∈B)
      [A∪B]∪C⊆A∪[B∪C] _ _ _ (inj₂ x∈C) = inj₂ (inj₂ x∈C)

      [A∪B]∪C⊇A∪[B∪C] : ∀ {ℓ ℓ₀ ℓ₁ ℓ₂} {X : Set ℓ}
                          (A : Pred X ℓ₀) (B : Pred X ℓ₁) (C : Pred X ℓ₂) →
                          A ∪ (B ∪ C) ⊆ (A ∪ B) ∪ C
      [A∪B]∪C⊇A∪[B∪C] _ _ _ (inj₁ x∈A) = inj₁ (inj₁ x∈A)
      [A∪B]∪C⊇A∪[B∪C] _ _ _ (inj₂ (inj₁ x∈B)) = inj₁ (inj₂ x∈B)
      [A∪B]∪C⊇A∪[B∪C] _ _ _ (inj₂ (inj₂ x∈C)) = inj₂ x∈C


infix 2 _⇔_

data _⇔_ {ℓ₀ ℓ₁} : (P : Set ℓ₀) → (Q : Set ℓ₁) → Set (ℓ₀ ⊔ ℓ₁) where
    _,_ : {P : Set ℓ₀}{Q : Set ℓ₁} → (P → Q) → (Q → P) → P ⇔ Q

module _ where
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Empty using (⊥-elim)

  A⊆B⇔A∪B≈B : ∀ {ℓ ℓ₀}{X : Set ℓ}{A : Pred X ℓ₀}{B : Pred X ℓ₀} → A ⊆ B ⇔ A ∪ B ≈ B
  A⊆B⇔A∪B≈B {A = A} {B} = A⊆B→A∪B≈B A B , A∪B≈B→A⊆B A B
    where
      A⊆B→A∪B≈B : ∀ {ℓ ℓ₀} {X : Set ℓ} (A B : X → Set ℓ₀) → A ⊆ B → A ∪ B ≈ B
      A⊆B→A∪B≈B A B A⊆B = record { eql = A∪B⊆B A B A⊆B , A∪B⊇B A B A⊆B }
        where
          A∪B⊆B : ∀ {ℓ ℓ₀} {X : Set ℓ} (A B : Pred X ℓ₀) → A ⊆ B → A ∪ B ⊆ B
          A∪B⊆B A B A⊆B = A⊆C×B⊆C⇒A∪B⊆C {A = A} {B} {B} (A⊆B , B⊆B B)
            where
              B⊆B : ∀ {ℓ ℓ₀} {X : Set ℓ} (B : Pred X ℓ₀) → B ⊆ B
              B⊆B B = id
          A∪B⊇B : ∀ {ℓ ℓ₀} {X : Set ℓ} (A B : Pred X ℓ₀) → A ⊆ B → A ∪ B ⊇ B
          A∪B⊇B A B A⊆B = B⊆A∪B {A = A} {B}
      A∪B≈B→A⊆B : ∀ {ℓ ℓ₀} {X : Set ℓ} (A B : Pred X ℓ₀) → A ∪ B ≈ B → A ⊆ B
      A∪B≈B→A⊆B A B record { eql = (A∪B⊆B , B⊆A∪B) } x∈A = A∪B⊆B (inj₁ x∈A)

  A⊆B⇒A∪C⊆B∪C : ∀ {ℓ ℓ₀}{X : Set ℓ}{A B C : Pred X ℓ₀} → A ⊆ B → A ∪ C ⊆ B ∪ C
  A⊆B⇒A∪C⊆B∪C {A = A} {B} {C} A⊆B (inj₁ x∈A) = A⊆A∪B {A = B} {C} (A⊆B x∈A)
  A⊆B⇒A∪C⊆B∪C {A = A} {B} {C} A⊆B (inj₂ x∈C) = B⊆A∪B {A = B} {C} x∈C

  ∅∪A≈A : ∀ {ℓ ℓ₀}{X : Set ℓ}{A : Pred X ℓ₀} → ∅ ∪ A ≈ A
  ∅∪A≈A {A = A} = record { eql = ∅∪A⊆A A , ∅∪A⊇A A }
    where
      ∅∪A⊆A : ∀ {ℓ ℓ₀} {X : Set ℓ} (A : Pred X ℓ₀) → ∅ ∪ A ⊆ A
      ∅∪A⊆A A (inj₁ x∈∅) = ∅-⊆ A (⊥-elim x∈∅)
      ∅∪A⊆A A (inj₂ x∈A) = x∈A

      ∅∪A⊇A : ∀ {ℓ ℓ₀} {X : Set ℓ} (A : Pred X ℓ₀) → A ⊆ ∅ ∪ A
      ∅∪A⊇A _ x∈A = inj₂ x∈A

module _ where
  open import Data.Nat.Divisibility using (_∣_)
  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  open import Relation.Nullary using (¬_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)

  even∩odd≈∅ : Evenℕ ∩ Oddℕ ≈ ∅
  even∩odd≈∅ = record { eql = even∩odd⊆∅ , even∩odd⊇∅ }
    where
      even∩odd⊆∅ : Evenℕ ∩ Oddℕ ⊆ ∅
      even∩odd⊆∅ {x} (e , o) with parity x
      even∩odd⊆∅ (e , o) | even k = o
      even∩odd⊆∅ (e , o) | odd k = e
      even∩odd⊇∅ : Evenℕ ∩ Oddℕ ⊇ ∅
      even∩odd⊇∅ ()

  A⊇A∩B : ∀ {ℓ₀ ℓ₁ ℓ}{X : Set ℓ}{A : Pred X ℓ₀}{B : Pred X ℓ₁} → A ⊇ A ∩ B
  A⊇A∩B = proj₁

  B⊇A∩B : ∀ {ℓ₀ ℓ₁ ℓ}{X : Set ℓ}{A : Pred X ℓ₀}{B : Pred X ℓ₁} → B ⊇ A ∩ B
  B⊇A∩B = proj₂

  A⊇C×B⊇C⇒A∩B⊇C : ∀ {ℓ ℓ₀ ℓ₁ ℓ₂}{X : Set ℓ}{A : Pred X ℓ₀}{B : Pred X ℓ₁}{C : Pred X ℓ₂} →
                  A ⊇ C × B ⊇ C → A ∩ B ⊇ C
  A⊇C×B⊇C⇒A∩B⊇C (A⊇C , B⊇C) x∈C = (A⊇C x∈C) , (B⊇C x∈C)

  A∩A≈A : ∀ {ℓ ℓ₀}{X : Set ℓ}{A : Pred X ℓ₀} → A ∩ A ≈ A
  A∩A≈A {A = A} = record { eql = A∩A⊆A A , A∩A⊇A A }
    where
      A∩A⊆A : ∀ {ℓ ℓ₀} {X : Set ℓ} (A : Pred X ℓ₀) → A ∩ A ⊆ A
      A∩A⊆A _ (_ , x∈A) = x∈A
      A∩A⊇A : ∀ {ℓ ℓ₀} {X : Set ℓ} (A : Pred X ℓ₀) → A ∩ A ⊇ A
      A∩A⊇A _ x∈A = x∈A , x∈A

  A∩B≈B∩A : ∀ {ℓ ℓ₀ ℓ₁}{X : Set ℓ}{A : Pred X ℓ₀}{B : Pred X ℓ₁} → A ∩ B ≈ B ∩ A
  A∩B≈B∩A {A = A} {B} = record { eql = A∩B⊆B∩A A B , A∩B⊇B∩A B A }
    where
      A∩B⊆B∩A : ∀ {ℓ ℓ₀ ℓ₁} {X : Set ℓ} (A : Pred X ℓ₀) (B : Pred X ℓ₁) → A ∩ B ⊆ B ∩ A
      A∩B⊆B∩A _ _ (x∈A , x∈B) = x∈B , x∈A
      A∩B⊇B∩A : ∀ {ℓ ℓ₀ ℓ₁} {X : Set ℓ} (A : Pred X ℓ₀) (B : Pred X ℓ₁) → B ∩ A ⊇ A ∩ B
      A∩B⊇B∩A A B (x∈A , x∈B) = x∈B , x∈A

  [A∩B]∩C≈A∩[B∩C] : ∀ {ℓ ℓ₀ ℓ₁ ℓ₂}{X : Set ℓ}{A : Pred X ℓ₀}{B : Pred X ℓ₁}{C : Pred X ℓ₂} →
                    (A ∩ B) ∩ C ≈ A ∩ (B ∩ C)
  [A∩B]∩C≈A∩[B∩C]{A = A} {B} {C} = record { eql = [A∩B]∩C⊆A∩[B∩C] A B C , [A∩B]∩C⊇A∩[B∩C] A B C }
    where
      [A∩B]∩C⊆A∩[B∩C] : ∀ {ℓ ℓ₀ ℓ₁ ℓ₂} {X : Set ℓ}
                          (A : Pred X ℓ₀) (B : Pred X ℓ₁) (C : Pred X ℓ₂) →
                          (A ∩ B) ∩ C ⊆ A ∩ (B ∩ C)
      [A∩B]∩C⊆A∩[B∩C] A B C ((x∈A , x∈B) , x∈C) = x∈A , x∈B , x∈C

      [A∩B]∩C⊇A∩[B∩C] : ∀ {ℓ ℓ₀ ℓ₁ ℓ₂} {X : Set ℓ}
                          (A : Pred X ℓ₀) (B : Pred X ℓ₁) (C : Pred X ℓ₂) →
                          A ∩ (B ∩ C) ⊆ (A ∩ B) ∩ C
      [A∩B]∩C⊇A∩[B∩C] A B C (x∈A , x∈B , x∈C) = (x∈A , x∈B) , x∈C

  A⊆B⇔A∩B≈A : ∀ {ℓ ℓ₀}{X : Set ℓ}{A : Pred X ℓ₀}{B : Pred X ℓ₀} → A ⊆ B ⇔ A ∩ B ≈ A
  A⊆B⇔A∩B≈A {A = A} {B} = A⊆B→A∩B≈A A B , A∩B≈A→A⊆B A B
    where
      A⊆B→A∩B≈A : ∀ {ℓ ℓ₀} {X : Set ℓ} (A B : Pred X ℓ₀) → A ⊆ B → A ∩ B ≈ A
      A⊆B→A∩B≈A A B A⊆B = record { eql = A∩B⊆A A B A⊆B , A∩B⊇A A B A⊆B }
        where
          A∩B⊆A : ∀ {ℓ ℓ₀} {X : Set ℓ} (A B : Pred X ℓ₀) → A ⊆ B → A ∩ B ⊆ A
          A∩B⊆A A B A⊆B (x∈A , x∈B) = x∈A
          A∩B⊇A : ∀ {ℓ ℓ₀} {X : Set ℓ} (A B : Pred X ℓ₀) → A ⊆ B → A ∩ B ⊇ A
          A∩B⊇A A B A⊆B = A⊇C×B⊇C⇒A∩B⊇C {A = A} {B} {A} (A⊇A A , A⊆B)
            where
              A⊇A : ∀ {ℓ ℓ₀} {X : Set ℓ} (A : Pred X ℓ₀) → A ⊇ A
              A⊇A A = id
      A∩B≈A→A⊆B : ∀ {ℓ ℓ₀} {X : Set ℓ} (A B : Pred X ℓ₀) → A ∩ B ≈ A → A ⊆ B
      A∩B≈A→A⊆B A B record { eql = (A∩B⊆A , A⊆A∩B) } = A⊆B×B⊆C⇒A⊆C {A = A} (A⊆A∩B , B⊇A∩B {A = A} {B})

  A⊆B⇒A∩C⊆B∩C : ∀ {ℓ ℓ₀}{X : Set ℓ}{A B C : Pred X ℓ₀} → A ⊆ B → A ∩ C ⊆ B ∩ C
  A⊆B⇒A∩C⊆B∩C A⊆B (x∈A , x∈C) = A⊆B x∈A , x∈C

  ∅∩A≈∅ : ∀ {ℓ}{X : Set ℓ}{A : Pred X lzero} → ∅ ∩ A ≈ ∅
  ∅∩A≈∅ {A = A} = record { eql = ∅∩A⊆∅ A , ∅∩A⊇∅ A }
    where
      ∅∩A⊆∅ : ∀ {ℓ} {X : Set ℓ} (A : Pred X lzero) → ∅ ∩ A ⊆ ∅
      ∅∩A⊆∅ A x∈∅∩A = proj₁ x∈∅∩A
      ∅∩A⊇∅ : ∀ {ℓ} {X : Set ℓ} (A : Pred X lzero) → ∅ ∩ A ⊇ ∅
      ∅∩A⊇∅ A x∈∅ = x∈∅ , ∅-⊆ A x∈∅

  [A∪B]∩C≈[A∩C]∪[B∩C] : ∀ {ℓ ℓ₀ ℓ₁ ℓ₂}{X : Set ℓ}{A : Pred X ℓ₀}{B : Pred X ℓ₁}{C : Pred X ℓ₂} →
                          (A ∪ B) ∩ C ≈ (A ∩ C) ∪ (B ∩ C)
  [A∪B]∩C≈[A∩C]∪[B∩C] {A = A} {B} {C} = record { eql = [A∪B]∩C⊆[A∩C]∪[B∩C] A B C , [A∪B]∩C⊇[A∩C]∪[B∩C] A B C }
    where
      [A∪B]∩C⊆[A∩C]∪[B∩C] : ∀ {ℓ ℓ₀ ℓ₁ ℓ₂}{X : Set ℓ}
                              (A : Pred X ℓ₀)(B : Pred X ℓ₁)(C : Pred X ℓ₂) →
                              (A ∪ B) ∩ C ⊆ (A ∩ C) ∪ (B ∩ C)
      [A∪B]∩C⊆[A∩C]∪[B∩C] A B C (inj₁ x∈A , x∈C) = inj₁ (x∈A , x∈C)
      [A∪B]∩C⊆[A∩C]∪[B∩C] A B C (inj₂ x∈B , x∈C) = inj₂ (x∈B , x∈C)
      [A∪B]∩C⊇[A∩C]∪[B∩C] : ∀ {ℓ ℓ₀ ℓ₁ ℓ₂}{X : Set ℓ}
                              (A : Pred X ℓ₀)(B : Pred X ℓ₁)(C : Pred X ℓ₂) →
                              (A ∪ B) ∩ C ⊇ (A ∩ C) ∪ (B ∩ C)
      [A∪B]∩C⊇[A∩C]∪[B∩C] A B C (inj₁ (x∈A , x∈C)) = inj₁ x∈A , x∈C
      [A∪B]∩C⊇[A∩C]∪[B∩C] A B C (inj₂ (x∈B , x∈C)) = inj₂ x∈B , x∈C

  [A∩B]∪C≈[A∪C]∩[B∪C] : ∀ {ℓ ℓ₀ ℓ₁ ℓ₂}{X : Set ℓ}{A : Pred X ℓ₀}{B : Pred X ℓ₁}{C : Pred X ℓ₂} →
                          (A ∩ B) ∪ C ≈ (A ∪ C) ∩ (B ∪ C)
  [A∩B]∪C≈[A∪C]∩[B∪C] {A = A} {B} {C} = record { eql = [A∩B]∪C⊆[A∪C]∩[B∪C] A B C , [A∩B]∪C⊇[A∪C]∩[B∪C] A B C }
    where
      [A∩B]∪C⊆[A∪C]∩[B∪C] :  ∀ {ℓ ℓ₀ ℓ₁ ℓ₂}{X : Set ℓ}
                               (A : Pred X ℓ₀)(B : Pred X ℓ₁)(C : Pred X ℓ₂) →
                               (A ∩ B) ∪ C ⊆ (A ∪ C) ∩ (B ∪ C)
      [A∩B]∪C⊆[A∪C]∩[B∪C] A B C (inj₁ (x∈A , x∈B)) = inj₁ x∈A , inj₁ x∈B
      [A∩B]∪C⊆[A∪C]∩[B∪C] A B C (inj₂ x∈C) = inj₂ x∈C , inj₂ x∈C

      [A∩B]∪C⊇[A∪C]∩[B∪C] :  ∀ {ℓ ℓ₀ ℓ₁ ℓ₂}{X : Set ℓ}
                               (A : Pred X ℓ₀)(B : Pred X ℓ₁)(C : Pred X ℓ₂) →
                               (A ∩ B) ∪ C ⊇ (A ∪ C) ∩ (B ∪ C)
      [A∩B]∪C⊇[A∪C]∩[B∪C] A B C (inj₁ x∈A , inj₁ x∈B) = inj₁ (x∈A , x∈B)
      [A∩B]∪C⊇[A∪C]∩[B∪C] A B C (inj₁ _   , inj₂ x∈C) = inj₂ x∈C
      [A∩B]∪C⊇[A∪C]∩[B∪C] A B C (inj₂ x∈C , inj₁ _  ) = inj₂ x∈C
      [A∩B]∪C⊇[A∪C]∩[B∪C] A B C (inj₂ _   , inj₂ x∈C) = inj₂ x∈C

  [A∪B]∩A≈A : ∀ {ℓ ℓ₀}{X : Set ℓ}{A B : Pred X ℓ₀} → (A ∪ B) ∩ A ≈ A
  [A∪B]∩A≈A {A = A} {B} = record { eql = [A∪B]∩A⊆A A B , [A∪B]∩A⊇A A B }
    where
      [A∪B]∩A⊆A : ∀ {ℓ ℓ₀} {X : Set ℓ} (A B : Pred X ℓ₀) → (A ∪ B) ∩ A ⊆ A
      [A∪B]∩A⊆A A B (A∪B , x∈A) = x∈A

      [A∪B]∩A⊇A : ∀ {ℓ ℓ₀} {X : Set ℓ} (A B : Pred X ℓ₀) → (A ∪ B) ∩ A ⊇ A
      [A∪B]∩A⊇A A B x∈A = inj₁ x∈A , x∈A


_⟨⊝⟩_ : ∀ {ℓ ℓ₀ ℓ₁} {X : Set ℓ} → (P : Pred X ℓ₀) → (Q : Pred X ℓ₁) → Pred X (ℓ₀ ⊔ ℓ₁)
(P ⟨⊝⟩ Q) x = x ∈ P × x ∉ Q

module _ where

  A⟨⊝⟩A⇒∅ : ∀ {ℓ} {X : Set ℓ} (A : Pred X lzero) → A ⟨⊝⟩ A ≈ ∅
  A⟨⊝⟩A⇒∅ A = record { eql = A⟨⊝⟩A⊆∅ A , A⟨⊝⟩A⊇∅ A }
    where
      A⟨⊝⟩A⊆∅ : ∀ {ℓ} {X : Set ℓ} (A : X → Set) → A ⟨⊝⟩ A ⊆ ∅
      A⟨⊝⟩A⊆∅ A (x∈A , x∉A) = x∉A x∈A

      A⟨⊝⟩A⊇∅ : ∀ {ℓ} {X : Set ℓ} (A : X → Set) → A ⟨⊝⟩ A ⊇ ∅
      A⟨⊝⟩A⊇∅ A ()

  A⊆B⇒A⟨⊝⟩B≈ø : ∀ {ℓ} {X : Set ℓ} {A B : Pred X lzero} → A ⊆ B → A ⟨⊝⟩ B ≈ ∅
  A⊆B⇒A⟨⊝⟩B≈ø {A = A} {B} A⊆B = record { eql = A⟨⊝⟩B⊆∅ {A = A} {B} A⊆B , A⟨⊝⟩B⊇∅ {A = A} {B} A⊆B }
    where
      A⟨⊝⟩B⊆∅ : ∀ {ℓ} {X : Set ℓ} {A B : Pred X lzero} → A ⊆ B → A ⟨⊝⟩ B ⊆ ∅
      A⟨⊝⟩B⊆∅ A⊆B (x∈A , x∉B) = x∉B (A⊆B x∈A)

      A⟨⊝⟩B⊇∅ : ∀ {ℓ} {X : Set ℓ} {A B : Pred X lzero} → A ⊆ B → A ⟨⊝⟩ B ⊇ ∅
      A⟨⊝⟩B⊇∅ A⊆B ()

_ᶜ : ∀ {ℓ ℓ₀} {X : Set ℓ} → Pred X ℓ₀ → Pred X ℓ₀
A ᶜ = λ x → x ∉ A

module _ where
  open import Data.Sum using (_⊎_)
  open import Relation.Binary.Core
  open import Relation.Nullary using (yes; no)
  open import Data.Empty using (⊥-elim)
  open import Data.Sum using (inj₁; inj₂)

  A∪Aᶜ≈U : ∀ {ℓ} {X : Set ℓ} {A : Pred X lzero} → A ∪ A ᶜ ≈ U
  A∪Aᶜ≈U {A = A} = record { eql = A∪Aᶜ⊆U A , A∪Aᶜ⊇U A }
    where
      A∪Aᶜ⊆U : ∀ {ℓ} {X : Set ℓ} (A : Pred X lzero) → A ∪ A ᶜ ⊆ U
      A∪Aᶜ⊆U A x∈A∪Aᶜ = tt

      A∪Aᶜ⊇U : ∀ {ℓ} {X : Set ℓ} (A : Pred X lzero) → A ∪ A ᶜ ⊇ U
      A∪Aᶜ⊇U A {x} tt = excluded-middle
        where
          postulate
            excluded-middle : ∀ {a} {P : Set a} → P ⊎ ¬ P

𝒫 : ∀ {ℓ ℓ₀} {X : Set ℓ} → (A : Pred X ℓ₀) → Pred (Pred X ℓ₀) (ℓ₀ ⊔ ℓ)
𝒫 A = λ x → x ⊆ A


module _ where
  open import Relation.Nullary using (yes; no)
  open import Data.Sum using (inj₁; inj₂)
  open import Data.Empty using (⊥-elim)
  open import Relation.Binary.PropositionalEquality using (sym)

  ∅⊆Oddℕ : ∅ ⊆ 𝒫 Oddℕ
  ∅⊆Oddℕ () y
  ∅∈𝒫Oddℕ :  ∅  ∈ 𝒫 Oddℕ
  ∅∈𝒫Oddℕ ()
  ｛3｝∈𝒫Oddℕ : ｛ 3 ｝ ∈ 𝒫 Oddℕ
  ｛3｝∈𝒫Oddℕ refl = tt

  3Or5 : ℕ → Set
  3Or5 3 = ⊤
  3Or5 5 = ⊤
  3Or5 n = ⊥

  3Or5ℕ : Pred ℕ lzero
  3Or5ℕ = 3Or5

  ｛3｝∈𝒫3Or5ℕ : ｛ 3 ｝ ∈ 𝒫 3Or5ℕ
  ｛3｝∈𝒫3Or5ℕ refl = tt

  ｛5｝∈𝒫3Or5ℕ : ｛ 5 ｝ ∈ 𝒫 3Or5ℕ
  ｛5｝∈𝒫3Or5ℕ refl = tt

  ｛4｝∉𝒫3Or5ℕ : ｛ 4 ｝ ∉ 𝒫 3Or5ℕ
  ｛4｝∉𝒫3Or5ℕ ｛4｝∈𝒫3Or5ℕ = ｛4｝∈𝒫3Or5ℕ refl

  ｛3，5｝∈𝒫3Or5ℕ : ｛ 3 ｝ ∪ ｛ 5 ｝ ∈ 𝒫 3Or5ℕ
  ｛3，5｝∈𝒫3Or5ℕ {x} ｛3，5｝∈3Or5ℕ  with x ≟ 3
  ｛3，5｝∈𝒫3Or5ℕ ｛3，5｝∈3Or5ℕ | yes refl = tt
  ｛3，5｝∈𝒫3Or5ℕ {x} ｛3，5｝∈3Or5ℕ | no ¬p with x ≟ 5
  ｛3，5｝∈𝒫3Or5ℕ ｛3，5｝∈3Or5ℕ | no ¬p | yes refl = tt
  ｛3，5｝∈𝒫3Or5ℕ (inj₁ x₁) | no ¬p₁ | no ¬p = ⊥-elim (¬p₁ (sym x₁))
  ｛3，5｝∈𝒫3Or5ℕ (inj₂ y) | no ¬p₁ | no ¬p = ⊥-elim (¬p (sym y))

  ｛3，4，5｝∉𝒫3Or5ℕ : ｛ 3 ｝ ∪ ｛ 4 ｝ ∪ ｛ 5 ｝ ∉ 𝒫 3Or5ℕ
  ｛3，4，5｝∉𝒫3Or5ℕ ｛3，4，5｝∉3Or5ℕ = ｛3，4，5｝∉3Or5ℕ (inj₂ (inj₁ refl))

