module integers_MAIN.properties.addition.associativity where

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


-- Property: ℤ addition is associative
associativityℤ+ : (x y : ℤ) {z : ℤ} → ((x + y) + z) ≡ (x + (y + z))
associativityℤ+ (pos zero) y {z} = (propertySymmetry (idℤ[a+b]≡idℤa+b (y) (z)))
associativityℤ+ (pos (suc zero)) y {z} = propertySymmetry (incr[a+b]≡incr[a]+b y {z})
associativityℤ+ (pos (suc (suc x))) y {z} = propertyTransitivity (propertySymmetry (incr[a+b]≡incr[a]+b ((Itℕ (incrementℤ y) incrementℤ x)) {z})) (congruence incrementℤ (associativityℤ+ (pos (suc (x))) y {z}))
associativityℤ+ (neg zero) y {z} =  (propertySymmetry (idℤ[a+b]≡idℤa+b (y) (z)))
associativityℤ+ (neg (suc zero)) y = propertySymmetry (decr[a+b]≡decr[a]+b y)
associativityℤ+ (neg (suc (suc x))) y {z} = propertyTransitivity (propertySymmetry (decr[a+b]≡decr[a]+b (neg (suc x) + y) {z})) (congruence decrementℤ (associativityℤ+ (neg (suc (x))) y {z}))
