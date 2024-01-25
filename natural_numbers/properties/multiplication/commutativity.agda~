module natural_numbers.properties.addition.commutativity where

open import natural_numbers.definition
open import natural_numbers.operations

open import predicate_logic.definitions
open import predicate_logic.properties

open import natural_numbers.properties.addition.neutralities


-- Helper lemma
suc+ : (m n : ℕ) → (suc (n + m)) ≡ (n + (suc m))
suc+ m zero = refl
suc+ m (suc n) = congruence suc (suc+ m n)

-- Main Proof: Commutativity 
commutativityℕ+ : (m : ℕ) {n : ℕ} → (m + n) ≡ (n + m)
commutativityℕ+ zero {n} = propertySymmetry (rightNeutralityℕ+ {n})
commutativityℕ+ (suc m) {n} = propertyTransitivity (congruence suc (commutativityℕ+ m {n})) (suc+ m n)
