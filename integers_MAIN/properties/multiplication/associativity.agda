module integers_MAIN.properties.multiplication.associativity where

open import natural_numbers.definition
open import natural_numbers.operations renaming (_+_ to _ℕ+_; _*_ to _*ℕ_)


open import predicate_logic.definitions
open import predicate_logic.properties

open import integers_MAIN.definition
open import integers_MAIN.operations

open import integers_MAIN.properties.addition.neutralities

open import integers_MAIN.properties.lemmas.incr_decr
open import integers_MAIN.properties.lemmas.incr_decr_idZ
open import integers_MAIN.properties.lemmas.idZ
open import integers_MAIN.properties.lemmas.negateZ

open import integers_MAIN.properties.distributive_laws

-- Property: ℤ multiplication is associative
associativityℤ* : (x y : ℤ) {z : ℤ} → ((x * y) * z) ≡ (x * (y * z))
associativityℤ* (pos zero) y = refl
associativityℤ* (pos (suc x)) y {z} = propertyTransitivity (rightDistributivityℤ (y) (pos x * y) {z}) (congruence ((y * z) +_ ) (associativityℤ* (pos (x)) y {z}))
associativityℤ* (neg zero) y = refl
associativityℤ* (neg (suc x)) y {z} = propertyTransitivity (propertyTransitivity (rightDistributivityℤ (negateℤ y) (neg x * y) {z}) (congruence (_+ ((neg x * y) * z)) (propertySymmetry (negℤ[a*b]≡[negℤa]*b y {z})))) (congruence (negateℤ (y * z) +_) (associativityℤ* (neg (x)) y {z}))
