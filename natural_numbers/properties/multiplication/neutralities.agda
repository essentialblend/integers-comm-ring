module natural_numbers.properties.multiplication.neutralities where

open import natural_numbers.definition
open import natural_numbers.operations

open import natural_numbers.properties.addition.neutralities

open import predicate_logic.definitions
open import predicate_logic.properties

-- Left Neutrality: 
leftNeutralityℕ* : {n : ℕ} → (1 * n) ≡ n
leftNeutralityℕ* {n} = rightNeutralityℕ+ {n}

-- Right Neutrality:
rightNeutralityℕ* : {n : ℕ} → (n * 1) ≡ n
rightNeutralityℕ* {zero} = refl
rightNeutralityℕ* {suc n} = congruence suc (rightNeutralityℕ* {n})
