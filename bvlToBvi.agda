{-# OPTIONS --without-K #-}
module bvlToBvi where

{- this file does part of bvl_to_bvi
  implementation and proof -}

open import Data.Nat
open import Data.List
data op : Set where
   Add : op
{-
(* --- Syntax of BVL --- *)
val _ = Datatype `
  exp = Var num
      | If exp exp exp
      | Let (exp list) exp
      | Raise exp
      | Handle exp exp
      | Tick exp
      | Call num (num option) (exp list)
      | Op op (exp list) `
-}

data BvlExp : Set where
   Var : ℕ → BvlExp
   If : BvlExp → BvlExp → BvlExp → BvlExp
   Let : List BvlExp → BvlExp → BvlExp
   Tick : BvlExp → BvlExp
   Op : op → List BvlExp → BvlExp
{-
(* --- Syntax of BVI --- *)

val _ = Datatype `
  exp = Var num
      | If exp exp exp
      | Let (exp list) exp
      | Raise exp
      | Tick exp
      | Call num (num option) (exp list) (exp option)
      | Op op (exp list) `
-}
open import Data.Maybe
data BviExp : Set where
   Var : ℕ → BviExp
   If : BviExp → BviExp → BviExp → BviExp
   Let : List BviExp → BviExp → BviExp
   Tick : BviExp → BviExp
   Op : op → List BviExp → BviExp
   Call : ℕ → Maybe ℕ → List BviExp → Maybe BviExp → BviExp
open import Data.Product


{- TODO switch to vector -}
unsafeHD : List BviExp → BviExp
unsafeHD = {!   !}

compileOp : op → List BviExp → BviExp
compileOp x x₁ = Op x x₁


destLet : BvlExp → List BvlExp × BvlExp
destLet (Let xs b) = xs , b
destLet _ = [] , Var 0

stackNumStubs : ℕ
stackNumStubs = 4

wordNumStubs : ℕ
wordNumStubs = stackNumStubs + 1

dataNumStubs : ℕ
dataNumStubs = wordNumStubs + 30 + 0 + 23

numStubs : ℕ
numStubs = dataNumStubs + 8 + 0

bvlToBviNamespaces : ℕ
bvlToBviNamespaces = 3

nss = bvlToBviNamespaces

open import Data.Bool



case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x


maybeLookup : {l : _} {A : Set l} → List A → ℕ → Maybe A
maybeLookup [] zero = nothing
maybeLookup (x ∷ x₁) zero = just x
maybeLookup [] (suc n) = nothing
maybeLookup (x ∷ x₁) (suc n) = maybeLookup x₁ n

{-# TERMINATING #-}
letCompile : (env : List ℕ) → ℕ → List BviExp → List BviExp
letCompile env d [] = []
letCompile env d (Var v ∷ []) = case maybeLookup env v of
   λ{nothing → [ Var (v + d) ]
   ; (just n) → [ Var (v + n) ]}
letCompile env d (If x1 x2 x3 ∷ []) = [ If (unsafeHD (letCompile env d [ x1 ])) (unsafeHD (letCompile env d [ x2 ])) (unsafeHD (letCompile env d [ x3 ])) ]
letCompile env d (Let x x₁ ∷ []) = {!   !}
letCompile env d (Tick x ∷ []) = [ Tick (unsafeHD (letCompile env d [ x ])) ]
letCompile env d (Op op xs ∷ []) = [ Op op (letCompile env d xs) ]
letCompile env d (Call t dest xs h ∷ []) = [ Call t dest (letCompile env d xs) (case h of λ{nothing → nothing
                                                                                          ; (just e) → just (unsafeHD (letCompile (0 ∷ env) d [ e ]))}) ]
letCompile env d (x ∷ y ∷ xs) = letCompile env d [ x ] ++ letCompile env d (y ∷ xs)

letCompileExp : BviExp → BviExp
letCompileExp x = case letCompile [] 0 [ x ] of λ{[] → Var 0
                                                ; (x ∷ z) → x}

compileAux : ℕ × ℕ × BviExp → List (ℕ × ℕ × BviExp)
compileAux (k , args , p) = [ numStubs + nss * k + 1 , args , letCompileExp p ]

{-# TERMINATING #-}
compileExps : ℕ → List BvlExp → List BviExp ×  List (ℕ × ℕ × BviExp) × ℕ
compileExps n [] = [] , [] , n
compileExps n (Var x ∷ []) = [ Var x ] , [] , n
compileExps n (If x y z ∷ []) =
  let
     ( c1 , aux1 , n1 ) = compileExps n [ x ]
     ( c2 , aux2 , n2 ) = compileExps n1 [ y ]
     ( c3 , aux3 , n3 ) = compileExps n2 [ z ]
  in
   [ If (unsafeHD c1) (unsafeHD c2) (unsafeHD c3) ] , aux1 ++ aux2 ++ aux3 , n3
compileExps n (Let [] x2 ∷ []) =
  let
     (args , x0) = destLet x2
     (c1 , aux1 , n1) = compileExps n args
     (c2 , aux2 , n2) = compileExps n1 [ x0 ]
     n3 = n2 + 1
  in
    [ Call 0 (just (numStubs + nss * n2 + 1)) c1 nothing ] , aux1 ++ aux2 ++ compileAux (n2 , length args , unsafeHD c2) , n3
compileExps n (Let xs@(_ ∷ _) x2 ∷ []) =
 let
    ( c1 , aux1 , n1 ) = compileExps n xs
    ( c2 , aux2 , n2 ) = compileExps n1 [ x2 ]
 in
    [ Let c1 (unsafeHD c2) ] , aux1 ++ aux2 , n2
compileExps n (Tick x ∷ []) =
   let
      (c1 , aux1 , n1) = compileExps n [ x ]
   in
     [ Tick (unsafeHD c1) ] , aux1 , n1
compileExps n (Op op exps ∷ []) =
   let
      (c1 , aux1 , n1) = compileExps n exps
   in
       [ compileOp op c1 ] , aux1 , n1
compileExps n (x ∷ y ∷ xs) =
  let
    (c1 , aux1 , n1) = compileExps n [ x ]
    (c2 , aux2 , n2) = compileExps n1 [ y ]
  in
    c1 ++ c2 , aux1 ++ aux2 , n2