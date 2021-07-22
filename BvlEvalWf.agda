{-# OPTIONS --without-K #-}
module BvlEvalWf where

open import Data.AVL
open import Agda.Primitive
open import Data.Nat
open import Relation.Binary
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Vec
open import Relation.Nullary
open import Data.List hiding ([_])
open import Data.Bool
open import Induction.WellFounded

open import Level hiding (suc)
open import Relation.Binary.PropositionalEquality
-- Exps

data Exp : Set where
   Var : ℕ → Exp

-- Code
releq : Rel ℕ lzero
releq zero zero = ⊤
releq zero (suc x₁) = ⊥
releq (suc x) zero = ⊥
releq (suc x) (suc y) = releq x y

rellt : Rel ℕ lzero
rellt zero zero = ⊥
rellt zero (suc x₁) = ⊤
rellt (suc x) zero = ⊥
rellt (suc x) (suc x₁) = rellt x x₁

reflreleq : {x : _} → releq x x
reflreleq {ℕ.zero} = tt
reflreleq {ℕ.suc x} = reflreleq {x}

symreleq : {x y : _} → releq x y → releq y x
symreleq {ℕ.zero} {ℕ.zero} r = tt
symreleq {ℕ.suc x} {ℕ.suc y} r = symreleq {x} {y} r

transreleq : {x y z : ℕ} → releq x y → releq y z → releq x z
transreleq {x = ℕ.zero} {y} {ℕ.zero} rxy ryz = tt
transreleq {x = ℕ.zero} {ℕ.zero} {ℕ.suc z} rxy ryz = ⊥-elim ryz
transreleq {x = ℕ.zero} {ℕ.suc y} {ℕ.suc z} rxy ryz = ⊥-elim rxy
transreleq {x = ℕ.suc x} {ℕ.suc y} {ℕ.suc z} rxy ryz = transreleq {x = x} {y = y} {z = z} rxy ryz


transrellt : {i j k : ℕ} → rellt i j → rellt j k → rellt i k
transrellt {i = ℕ.zero} {ℕ.zero} {ℕ.zero} x x₁ = ⊥-elim x
transrellt {i = ℕ.zero} {ℕ.suc j} {ℕ.zero} x x₁ = ⊥-elim x₁
transrellt {i = ℕ.zero} {ℕ.suc j} {ℕ.suc k} x x₁ = x
transrellt {i = ℕ.suc i} {ℕ.suc j} {ℕ.suc k} x x₁ = transrellt {i = i} x x₁

trichlt : Trichotomous  releq rellt
trichlt ℕ.zero ℕ.zero = tri≈ ⊥-elim tt λ{()}
trichlt ℕ.zero (ℕ.suc y) = tri< tt (λ{()}) λ{()}
trichlt (ℕ.suc x) ℕ.zero = tri> (λ{()}) (λ{()}) tt
trichlt (ℕ.suc x) (ℕ.suc y) = trichlt x y

stLtEq : IsStrictTotalOrder releq rellt
IsEquivalence.refl (IsStrictTotalOrder.isEquivalence stLtEq) {x} = reflreleq {x = x}
IsEquivalence.sym (IsStrictTotalOrder.isEquivalence stLtEq) {x} {y} = symreleq {x = x} {y = y}
IsEquivalence.trans (IsStrictTotalOrder.isEquivalence stLtEq) {x} {y} {z} = transreleq {x = x} {y = y} {z = z}
IsStrictTotalOrder.trans stLtEq {i} {j} {k} = transrellt {i = i} {j = j} {k = k}
IsStrictTotalOrder.compare stLtEq = trichlt


CodeValue : Value
      (record
       { Carrier = ℕ
       ; _≈_ = releq
       ; _<_ = rellt
       ; isStrictTotalOrder = stLtEq
       })
      lzero
Value.family CodeValue x = ℕ × Exp
Value.respects CodeValue x y = y


Code : Set -- Code is a map from ℕ -> (ℕ , Exp)
Code = Tree {ℓ₂ = lzero} (record
 { Carrier = ℕ ; _≈_ = releq ; _<_ = rellt ; isStrictTotalOrder = stLtEq })
    CodeValue
record BState : Set where
    field
      clock : ℕ
      code : Code
open BState


data Abort : Set where
    RtypeError : Abort
    Rtimeout : Abort

data ErrResult (exn : Set) : Set where
    Rabort : Abort → ErrResult exn    
    Rraise : exn → ErrResult exn

data Result (A : Set) (exn : Set) : Set where
    Rval : A → Result A exn
    Rerr : ErrResult exn → Result A exn

data BValue : Set where
    BoolV : Bool → BValue
    IntV : ℕ → BValue
    CodePtr :  ℕ → BValue

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x


HD : {l : _} {A : Set l} {n : _} → Vec A (suc n) → A
HD (x ∷ x₁) = x

ifPrf_then_else_ : {l l1 : _} {A : Set l} {B : Set l1} → Dec A → ((prf : A)  → B) → ((prf : ¬ A) → B) → B
ifPrf (yes p) then x else y = x p
ifPrf (no p) then x else y = y p
lesuc : {x y : _} → ℕ.suc x Data.Nat.≤ ℕ.suc y → x Data.Nat.≤ y
lesuc (s≤s x) = x

lookupVar : (env : List BValue) → (x : ℕ) → x Data.Nat.< length env → BValue
lookupVar (fe ∷ env) ℕ.zero prf = fe
lookupVar (fe ∷ env) (ℕ.suc x) prf = lookupVar env x (lesuc prf)

allaccwf : {l1 l2 : _} {A : Set l1} (_<_ : A → A → Set l2) → WellFounded _<_ → (z :  A) → Acc _<_ z
allaccwf _<₁_ x z = x z


acc-fold : {l1 l2 l3 : _} {a : Set l1} (_<_ : a -> a -> Set l2) {P : a -> Set l3} ->
  ((x : a) -> (forall y -> y < x -> P y) -> P x) ->
    (z : a) -> Acc _<_ z -> P z
acc-fold _<_ phi z (acc rs) = phi z λ y y<z → acc-fold _<_ phi y (rs _ y<z)

rec-wf : {l1 l2 l3 : _} {A : Set l1}{_<_ : A → A → Set l2} {P : A → Set l3}
   → WellFounded _<_
   → ((x : A) → ((y : A) → y < x → P y) → P x)
   → (x : A) → P x
rec-wf {A = A} {_<_} {P} wf f x = acc-fold _<_ {P = P} f x (wf x)

expSize : Exp → ℕ
expSize (Var x) = 1

expSizes : ∀{m} → Vec Exp m → ℕ
expSizes {m} x = Data.Vec.foldl (λ x₁ → ℕ) (λ new old → new + expSize old) 0 x

eq-vecexp : ∀{m}{l} → Rel (Vec Exp m) l
eq-vecexp {l = l} [] [] = Lift l ⊤
eq-vecexp (x ∷ xs) (y ∷ ys) = x ≡ y × eq-vecexp xs ys

eq-vecexp-sizes : ∀{m} → Rel (Vec Exp m) lzero
eq-vecexp-sizes x y = expSizes x ≡ expSizes y

lt-vecexp-sizes : ∀{m} → Rel (Vec Exp m) lzero
lt-vecexp-sizes x y = expSizes x Data.Nat.< expSizes y

lt-clocks-bstate : Rel BState lzero
lt-clocks-bstate s1 s2 = clock s1 Data.Nat.< clock s2


open Induction.WellFounded.Lexicographic

{-
measureE : ∀{m} →  Vec Exp m × List BValue × BState → Vec Exp m × List BValue × BState → Set
measureE {m} (exp1 , env1 , s1) (exp2 , env2 , s2) = ×-Lex eq-vecexp-sizes lt-vecexp-sizes lt-clocks-bstate (exp1 , s1) (exp2 , s2)
-}

measureE : ∀{m} →  Vec Exp m × List BValue × BState → Vec Exp m × List BValue × BState → Set
measureE = lt-vecexp-sizes Lexicographic.< λ _ → λ{(_ , s1) (_ , s2) → lt-clocks-bstate s1 s2}

postulate
    expsizeGE1 : ∀{t} → expSize t ≥ 1

hnat : ∀ n → n Data.Nat.≤ 0 → ¬(n ≥ 1)
hnat ℕ.zero z≤n ()
hnat (suc n) () y

absurdVar : ∀ m → (suc (expSize m) Data.Nat.≤ 1) → ⊥
absurdVar m (s≤s x) = ⊥-elim (hnat _ x expsizeGE1)

wellFoundedExpSize : ∀ m → WellFounded (lt-vecexp-sizes {m})
wellFoundedExpSize .0 [] = acc λ y → λ{()}
wellFoundedExpSize .1 (Var x ∷ []) = acc λ{(m ∷ []) → λ x₁ → ⊥-elim (absurdVar m x₁)}
wellFoundedExpSize .(suc (suc _)) (x ∷ y ∷ xs) = {!   !}

measureEWF : ∀{m} → WellFounded (measureE {m})
measureEWF = {!   !}
{-
module _ {a b l1 l2 : _}{A : Set a} {B : Set b}{_<₁_ : Rel A l1} {_<₂_ : Rel B l2} where

  -- Currently only proven for propositional equality
  -- (unsure how to satisfy the termination checker for arbitrary equalities)

  private
    _<ₗₑₓ_ = ×-Lex _≡_ _<₁_ _<₂_

  ×-wellFounded : WellFounded _<₁_ →
                  WellFounded _<₂_ →
                  WellFounded _<ₗₑₓ_
  ×-wellFounded wf₁ wf₂ (x , y) = acc (×-acc (wf₁ x) (wf₂ y))
    where
    ×-acc : ∀ {x y} →
            Acc _<₁_ x → Acc _<₂_ y →
            WfRec _<ₗₑₓ_ (Acc _<ₗₑₓ_) (x , y)
    ×-acc = ?

measureEhelp-WellFounded : ∀{m} → WellFounded (measureE {m})
measureEhelp-WellFounded = {! ×-wellFounded  !}
-}
{-
{- evaluate recurse on Lex -}
evaluate : ∀{n} → Vec Exp n × List BValue × BState → Result (Vec BValue n) BValue
evaluate {n} x = rec-wf well-found-measureE body x
    where
      body : 
        (z : Vec Exp n × List BValue × BState)
        →
        ((y : _) → measureE y z → Result (Vec BValue n) BValue)
        →
        Result (Vec BValue n) BValue
      body ([] , env , state) eval' = Rval []
      body (x ∷ [] , env , state) eval' = {!   !}
      body (x ∷ x₁ ∷ exps , env , state) eval' = case eval' ({!   !} , {!   !}) {!   !} of
          {!   !}
-}
