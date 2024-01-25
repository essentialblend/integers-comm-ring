module integers_MAIN.properties.addition.commutativity where

open import natural_numbers.definition

open import predicate_logic.definitions
open import predicate_logic.properties

open import integers_MAIN.definition
open import integers_MAIN.operations

open import integers_MAIN.properties.addition.neutralities

open import integers_MAIN.properties.lemmas.incr_decr
open import integers_MAIN.properties.lemmas.incr_decr_idZ


-- Property: Integer addition is commutative.
commutativityℤ+ : (x : ℤ) {y : ℤ} → (x + y) ≡ (y + x)
commutativityℤ+ (pos zero) {y} = propertySymmetry (rightNeutrality+ℤ+ y)
commutativityℤ+ (pos (suc zero)) {y} = (propertyTransitivity (propertyTransitivity (propertySymmetry (incrℤidℤ≡incrℤ y)) (congruence incrementℤ (propertySymmetry (rightNeutrality+ℤ+ y)))) (incr[a+b]≡a+incr[b] (y) {pos zero}))
commutativityℤ+ (pos (suc (suc x))) {y} = propertyTransitivity (congruence incrementℤ (commutativityℤ+ (pos (suc (x))) {y})) (incr[a+b]≡a+incr[b] y {pos (suc x)})
commutativityℤ+ (neg zero) {y} = propertySymmetry (rightNeutrality-ℤ+ y)
commutativityℤ+ (neg (suc x)) {y} = propertyTransitivity (propertyTransitivity (propertySymmetry (decr[a+b]≡decr[a]+b (neg x) {y})) (congruence decrementℤ (commutativityℤ+ (neg x) {y}))) (decr[a+b]≡a+decr[b] y {neg x})
