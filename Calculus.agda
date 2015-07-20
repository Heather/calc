{-# OPTIONS --universe-polymorphism #-}
module Calculus where

open import Data.Char hiding (show)
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Show
open import Data.String hiding (show)

open import Relation.Binary.PropositionalEquality

open import Function

isDigit : Char → Maybe ℕ
isDigit '0' = just 0
isDigit '1' = just 1
isDigit '2' = just 2
isDigit '3' = just 3
isDigit '4' = just 4
isDigit '5' = just 5
isDigit '6' = just 6
isDigit '7' = just 7
isDigit '8' = just 8
isDigit '9' = just 9
isDigit _   = nothing

attach : Maybe ℕ → ℕ → ℕ
attach nothing  n = n
attach (just m) n = 10 * m + n

Quote : List Char → Maybe (List ℕ)
Quote xs = parse xs nothing []
  where
    parse : List Char → Maybe ℕ → List ℕ → Maybe (List ℕ)
    parse []         nothing  ns = just ns
    parse []         (just n) ns = just (n ∷ ns)
    parse ('+' ∷ tl) (just n) ns = parse tl nothing (n ∷ ns)
    parse (hd ∷ tl)  m        ns with isDigit hd
    ... | nothing = nothing
    ... | just n  = parse tl (just (attach m n)) ns

stringListToℕ : String → Maybe (List ℕ)
stringListToℕ xs with Quote (toList xs)
... | nothing = nothing
... | just ns = just (reverse ns)

maybeSum : Maybe (List ℕ) → Maybe ℕ
maybeSum nothing   = nothing
maybeSum (just xs) = just (sum xs)

ℕ? : Maybe ℕ -> ℕ
ℕ? (just x) = x
ℕ? nothing  = 0

{-
data Operator : Set where
  plus minus times eq : Operator

eval : ℕ → Operator → ℕ → ℕ
eval m plus  n = m + n
eval m minus n = m ∸ n
eval m times n = m * n
eval m eq    n = n
-}

testParse : stringListToℕ ("12+3") ≡ just (12 ∷ 3 ∷ [])
testParse = refl

testSum : maybeSum (stringListToℕ ("12+3")) ≡ (just 15)
testSum = refl
