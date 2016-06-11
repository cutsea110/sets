open import Agda.Primitive using (lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat hiding (_⊔_)
open import Data.Unit using (⊤; tt)
open import Data.String
open import Data.Empty using (⊥)
open import Function using (_∘_; id; flip; const)
open import Relation.Unary
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)

Nat : Pred ℕ lzero
Nat = const ⊤

Str : Pred String lzero
Str = const ⊤

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

record _≈_ {a ℓ} {S : Set a} (A : Pred S ℓ) (B : Pred S ℓ) : Set (a ⊔ lsuc ℓ) where
  field
    eql : A ⊆ B × A ⊇ B

module _  where
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
      A⊆B prf | odd k = {!!}

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
