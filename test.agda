open import Agda.Primitive using (lzero)
open import Relation.Unary
open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.String
open import Data.Empty using (⊥)

Nat : Pred ℕ lzero
Nat = λ _ → ⊤

Str : Pred String lzero
Str = λ _ → ⊤

foo : 42 ∈ Nat
foo = tt

bar : "Hello" ∈ Str
bar = tt

buz : ∀ (n : ℕ) → n ∉ ∅
buz = λ n z → z

quz : ∀ (s : String) → s ∈ U
quz = λ s → tt

test : ｛ 42 ｝ ⊆ U
test = λ {x} _ → tt

test2 : ｛ "Hello" ｝ ⊆ U
test2 = λ {x} _ → tt

open import Relation.Binary.PropositionalEquality
open import Data.Product

data Evenℕ : Set where
  even : (n : ℕ) → (p : ∃ λ k → n ≡ k * 2) → Evenℕ

data Oddℕ : Set where
  odd : (n : ℕ) → (p : ∃ λ k → n ≡ 1 + k * 2) → Oddℕ

x : Evenℕ
x = even 4 (2 , refl)

y : Oddℕ
y = odd 9 (4 , refl)

EvenNat : Pred Evenℕ lzero
EvenNat = λ _ → ⊤

OddNat : Pred Oddℕ lzero
OddNat = λ _ → ⊤

test3 : odd 3 (1 , refl) ∈ OddNat
test3 = tt

test4 : even 8 (4 , refl) ∈ EvenNat
test4 = tt


data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd  : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(suc (k * 2))) | odd k = even (suc k)

EvenNat' : Pred ℕ lzero
EvenNat' n with parity n
EvenNat' .(k * 2) | even k = ⊤
EvenNat' .(suc (k * 2)) | odd k = ⊥
OddNat' : Pred ℕ lzero
OddNat' n with parity n
OddNat' .(k * 2) | even k = ⊥
OddNat' .(suc (k * 2)) | odd k = ⊤

test5 : 3 ∈ OddNat'
test5 = tt
test6 : 3 ∉ EvenNat'
test6 = λ z → z
test7 : 8 ∈ EvenNat'
test7 = tt
test8 : 21 ∉ EvenNat'
test8 = λ z → z
