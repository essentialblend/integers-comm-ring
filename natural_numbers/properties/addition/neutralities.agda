module natural_numbers.properties.addition.neutralities where

open import natural_numbers.definition
open import natural_numbers.operations

open import predicate_logic.definitions
open import predicate_logic.properties

-- Left neutrality: 0 + n ≡ n 
leftNeutralityℕ+ : {n : ℕ} → (0 + n) ≡ n
leftNeutralityℕ+ {n} = refl

-- Right neutrality: n + 0 ≡ n
rightNeutralityℕ+ : {n : ℕ} → (n + 0) ≡ n
rightNeutralityℕ+ {zero}  = refl
rightNeutralityℕ+ {suc n} = congruence suc (rightNeutralityℕ+ {n})
