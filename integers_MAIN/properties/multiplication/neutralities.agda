module integers_MAIN.properties.multiplication.neutralities where

open import natural_numbers.definition

open import predicate_logic.definitions
open import predicate_logic.properties

open import integers_MAIN.definition
open import integers_MAIN.operations

open import integers_MAIN.properties.addition.neutralities

open import integers_MAIN.properties.lemmas.incr_decr
open import integers_MAIN.properties.lemmas.incr_decr_idZ

-- Property: Left Neutrality with pos 1 for ℤ
leftNeutralityℤ* : (x : ℤ) → (pos 1 * x) ≡ idℤ x
leftNeutralityℤ* (pos x) = rightNeutrality+ℤ+ (pos x)
leftNeutralityℤ* (neg zero) = refl
leftNeutralityℤ* (neg (suc zero)) = refl
leftNeutralityℤ* (neg (suc (suc x))) = congruence decrementℤ (leftNeutralityℤ* (neg (suc (x))))

-- Property: Right Neutrality with pos 1 for ℤ
rightNeutralityℤ* : (x : ℤ) → (x * pos 1) ≡ idℤ x
rightNeutralityℤ* (pos zero) = refl
rightNeutralityℤ* (pos (suc x)) = congruence incrementℤ (rightNeutralityℤ* (pos (x)))
rightNeutralityℤ* (neg zero) = refl
rightNeutralityℤ* (neg (suc zero)) = refl
rightNeutralityℤ* (neg (suc (suc x))) = congruence decrementℤ (rightNeutralityℤ* (neg (suc (x))))
