module natural_numbers.properties.addition.associativity where

open import natural_numbers.definition
open import natural_numbers.operations

open import predicate_logic.definitions
open import predicate_logic.properties

{- Property: Associativity over ℕ Addition -}
associativityℕ+ : {l m n : ℕ} → ((l + m) + n) ≡ (l + (m + n))
associativityℕ+ {zero} {m} {n} = refl
associativityℕ+ {suc l} {m} {n} = congruence suc (associativityℕ+ {l} {m} {n})
