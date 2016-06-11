open import Agda.Primitive using (lzero)
open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.String
open import Data.Empty using (⊥)
open import Function using (_∘_; id; flip; const)
open import Relation.Unary

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

Evenℕ : Pred ℕ lzero
Evenℕ n with parity n
Evenℕ .(k * 2) | even k = ⊤
Evenℕ .(suc (k * 2)) | odd k = ⊥

Oddℕ : Pred ℕ lzero
Oddℕ n with parity n
Oddℕ .(k * 2) | even k = ⊥
Oddℕ .(suc (k * 2)) | odd k = ⊤

test3 : 3 ∈ Oddℕ
test3 = tt

test4 : 3 ∉ Evenℕ
test4 = id

test5 : 8 ∈ Evenℕ
test5 = tt

test6 : 21 ∉ Evenℕ
test6 = id
