module integers_MAIN.properties.addition.inverses where

open import natural_numbers.definition

open import predicate_logic.definitions
open import predicate_logic.properties

open import integers_MAIN.definition
open import integers_MAIN.operations
open import integers_MAIN.properties.lemmas.incr_decr
open import integers_MAIN.properties.lemmas.incr_decr_idZ

-- Lemma for Left Additive Inverse
addℤ→incrℤ : (x : ℕ) {y : ℕ} → (pos x + neg x) ≡ (pos (suc x) + neg (suc x))
addℤ→incrℤ zero = refl
addℤ→incrℤ (suc x) {zero} = propertySymmetry (incr[a+b]≡a+incr[b] (pos (suc x)) {neg (suc (suc x))})
addℤ→incrℤ (suc x) {suc y} = propertySymmetry (incr[a+b]≡a+incr[b] (pos (suc x)) {neg (suc (suc x))})

-- Property: Left Additive Inverse
leftAdditiveInverseℤ+ : (x : ℤ) → ((negateℤ x) + x) ≡ pos zero
leftAdditiveInverseℤ+ (pos zero) = refl
leftAdditiveInverseℤ+ (pos (suc zero)) = refl
leftAdditiveInverseℤ+ (pos (suc (suc x))) = propertyTransitivity (decr[a+b]≡a+decr[b] (neg (suc x)) {pos (suc (suc x))}) (leftAdditiveInverseℤ+ (pos (suc x)))
leftAdditiveInverseℤ+ (neg zero) = refl
leftAdditiveInverseℤ+ (neg (suc x)) = propertyTransitivity (propertySymmetry (addℤ→incrℤ (x) {zero})) (leftAdditiveInverseℤ+ (neg x))

-- Property: Right Additive Inverse
rightAdditiveInverseℤ+ : (x : ℤ) → (x + (negateℤ x)) ≡ pos zero
rightAdditiveInverseℤ+ (pos zero) = refl
rightAdditiveInverseℤ+ (pos (suc zero)) = refl
rightAdditiveInverseℤ+ (pos (suc (suc x))) = propertyTransitivity (incr[a+b]≡a+incr[b] (pos (suc x)) {neg (suc (suc x))}) (rightAdditiveInverseℤ+ (pos (suc (x))))
rightAdditiveInverseℤ+ (neg zero) = refl
rightAdditiveInverseℤ+ (neg (suc zero)) = refl
rightAdditiveInverseℤ+ (neg (suc (suc x))) = propertyTransitivity (decr[a+b]≡a+decr[b] (neg (suc x)) {pos (suc (suc x))}) (rightAdditiveInverseℤ+ (neg (suc (x))))
