{-# OPTIONS --universe-polymorphism #-}
module calc where

open import Calculus

open import Data.Char hiding (show)
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Show
open import Data.String hiding (show)

open import Foreign.Haskell using (Unit)
open import IO.Primitive

open import Coinduction using (♯_)
open import Data.Unit using (⊤)

postulate
  _getLine : IO String

{-# COMPILED _getLine getLine #-}

parseInt : String → Maybe ℕ
parseInt s =
  then? (unwrap (parseDigits s)) (λ s' →
  just (digitsToℕ s'))
  where
    parseDigits : String → List (Maybe ℕ)
    parseDigits s = Data.List.map toDigit (toList s) where
      toDigit : Char → Maybe ℕ
      toDigit '0' = just 0
      toDigit '1' = just 1
      toDigit '2' = just 2
      toDigit '3' = just 3
      toDigit '4' = just 4
      toDigit '5' = just 5
      toDigit '6' = just 6
      toDigit '7' = just 7
      toDigit '8' = just 8
      toDigit '9' = just 9
      toDigit _   = nothing

    unwrap : List (Maybe ℕ) → Maybe (List ℕ)
    unwrap xs = unwrap' (just []) xs where
      unwrap' : Maybe (List ℕ) → List (Maybe ℕ) → Maybe (List ℕ)
      unwrap' (just xs) (just y ∷ ys) = unwrap' (just (Data.List._++_ xs [ y ])) ys  -- makes unwrap O(N^2)!
      unwrap' (just xs) (nothing ∷ _) = nothing
      unwrap' (just xs) []            = just xs
      unwrap' nothing   _             = nothing

    then? : {A : Set} → {B : Set} → Maybe A → (A → Maybe B) → Maybe B
    then? nothing _ = nothing
    then? (just r1) op2 = op2 r1

    digitsToℕ : List ℕ → ℕ
    digitsToℕ xs = digitsToℕ' (reverse xs) where
      digitsToℕ' : List ℕ → ℕ
      digitsToℕ' []       = 0
      digitsToℕ' (x ∷ xs) = x + (10 * (digitsToℕ' xs))

-- (needs Agda IO)
-- echo : IO ⊤
-- echo = ♯ getLine∞ >>= (λ x → ♯ (putStrLn∞ x))

{-
main : IO Unit
main =
  _getLine >>= (λ s →
  return (show (ℕ? (parseInt s))) >>= (λ s' →
  putStrLn (toCostring s')))
-}

main : IO Unit
main =
  _getLine >>= (λ s →
    return (show (ℕ? (maybeSum (stringListToℕ s))))
      >>= (λ s' → putStrLn (toCostring s')))
