module integers_MAIN.properties.multiplication.commutativity where

open import natural_numbers.definition

open import predicate_logic.definitions
open import predicate_logic.properties

open import integers_MAIN.definition
open import integers_MAIN.operations

open import integers_MAIN.properties.addition.neutralities
open import integers_MAIN.properties.addition.commutativity
open import integers_MAIN.properties.addition.associativity

open import integers_MAIN.properties.lemmas.incr_decr
open import integers_MAIN.properties.lemmas.incr_decr_idZ
open import integers_MAIN.properties.lemmas.idZ

-- Lemmas for Commutativity of Multiplication
unfoldMult : (x : ℕ) (y : ℤ) → (y + (y * pos x)) ≡ (y * pos (suc x))
unfoldMult zero (pos zero) = refl
unfoldMult zero (pos (suc zero)) = refl
unfoldMult zero (pos (suc (suc y))) = propertyTransitivity (congruence incrementℤ (propertySymmetry (congruence (pos (suc y) +_) ((idx1-2 (pos y * pos zero)))))) (congruence incrementℤ (unfoldMult zero (pos (suc (y)))))
unfoldMult (suc x) (pos zero) = refl
unfoldMult (suc x) (pos (suc y)) = propertyTransitivity ((propertyTransitivity (commutativityℤ+ (pos (suc y)) {pos (suc x) + (pos y * pos (suc x))}) (propertySymmetry (propertyTransitivity (incr[a+b]≡a+incr[b] (pos (suc x)) {pos y + (pos y * pos (suc x))}) (propertyTransitivity (congruence (pos (suc x) +_) (propertyTransitivity (incr[a+b]≡incr[a]+b (pos y) {pos y * pos (suc x)}) (propertySymmetry (commutativityℤ+ (pos y * pos (suc x)) {pos (suc y)})))) (propertySymmetry (associativityℤ+ (pos (suc x)) (pos y * pos (suc x)) {pos (suc y)}))))))) (congruence incrementℤ (congruence (pos (suc x) +_) (unfoldMult (suc x) (pos (y))))) 
unfoldMult zero (neg zero) = refl
unfoldMult zero (neg (suc zero)) = refl
unfoldMult zero (neg (suc (suc y))) = propertyTransitivity (congruence decrementℤ (congruence (neg (suc y) +_) (propertySymmetry (idx1-2 (neg y * pos 0))))) (congruence decrementℤ (unfoldMult zero (neg (suc (y)))))
unfoldMult (suc x) (neg zero) = refl
unfoldMult (suc x) (neg (suc y)) = propertyTransitivity (propertyTransitivity (commutativityℤ+ (neg (suc y)) {neg (suc x) + (neg y * pos (suc x))}) (propertySymmetry (propertyTransitivity (decr[a+b]≡a+decr[b] (neg (suc x)) {neg y + (neg y * pos (suc x))}) (propertyTransitivity (propertySymmetry (propertyTransitivity (commutativityℤ+ (neg (suc y)) {neg (suc x) + (neg y * pos (suc x))}) (propertyTransitivity (associativityℤ+ (neg (suc x)) (neg y * pos (suc x)) {neg (suc y)}) (congruence (neg (suc x) +_) (propertySymmetry (propertyTransitivity (decr[a+b]≡decr[a]+b (neg y) {neg y * pos (suc x)}) (commutativityℤ+ (neg (suc y)) {neg y * pos (suc x)}))))))) (commutativityℤ+ (neg (suc y)) {neg (suc x) + (neg y * pos (suc x))}))))) (congruence decrementℤ (congruence (neg (suc x) +_) (unfoldMult (suc x) (neg (y)))))

unfoldMult2 : (x : ℕ) (y : ℤ) → (negateℤ y + (y * neg x)) ≡ (y * (neg (suc x)))
unfoldMult2 zero (pos zero) = refl
unfoldMult2 zero (pos (suc zero)) = propertyTransitivity (propertyTransitivity refl (propertySymmetry (decr[a+b]≡decr[a]+b (idℤ (neg zero)) {(pos zero * neg zero)}))) (congruence decrementℤ (unfoldMult2 zero (pos (zero))))
unfoldMult2 zero (pos (suc (suc y))) = propertyTransitivity (congruence decrementℤ (congruence (neg (suc y) +_) (propertySymmetry (idx1-2 (pos y * neg zero))))) (congruence decrementℤ (unfoldMult2 zero (pos (suc y))))
unfoldMult2 (zero) (neg zero) = refl
unfoldMult2 (zero) (neg (suc y)) = propertyTransitivity (propertySymmetry (propertyTransitivity (incr[a+b]≡incr[a]+b (pos y) {neg y * neg zero}) (congruence (pos (suc y) +_) (propertySymmetry (idℤa*b≡a*b (neg y) (neg zero)))))) (congruence incrementℤ (unfoldMult2 (zero) (neg (y))))
unfoldMult2 (suc x) (pos zero) = refl
unfoldMult2 (suc x) (pos (suc zero)) = congruence (neg (suc (suc x)) +_) (unfoldMult2 (suc x) (pos (zero)))
unfoldMult2 (suc x) (pos (suc (suc y))) = propertyTransitivity (propertyTransitivity (propertySymmetry (associativityℤ+ (neg (suc (suc y))) (neg (suc x)))) (propertyTransitivity (congruence (λ l → (decrementℤ l) + (pos (suc y) * neg (suc x))) (commutativityℤ+ (neg (suc y)) {neg (suc x)})) (associativityℤ+ (neg (suc (suc x))) (neg (suc y))))) (congruence (neg (suc (suc x)) +_) (unfoldMult2 (suc x) (pos (suc y))))
unfoldMult2 (suc x) (neg zero) = refl
unfoldMult2 (suc x) (neg (suc zero)) = refl
unfoldMult2 (suc x) (neg (suc (suc y))) = propertyTransitivity (propertyTransitivity (propertySymmetry (associativityℤ+ (pos (suc (suc y))) (pos (suc x)) {neg (suc y) * neg (suc x)})) (propertyTransitivity ( (congruence (λ l → (incrementℤ l) + (neg (suc y) * neg (suc x))) (commutativityℤ+ (pos (suc y)) {pos (suc x)}))) (associativityℤ+ (pos (suc (suc x))) (pos (suc y)) {neg (suc y) * neg (suc x)}))) (congruence (pos (suc (suc x)) +_) (unfoldMult2 (suc x) (neg (suc y))))

-- Property: ℤ multiplication is commutative
commutativityℤ* : (x : ℤ) {y : ℤ} → (x * y) ≡ (y * x)
commutativityℤ* (pos zero) {y} = propertySymmetry (rightZero+ℤ* y)
commutativityℤ* (pos (suc x)) {y} =  propertyTransitivity (congruence (y +_) (commutativityℤ* (pos (x)) {y})) (unfoldMult x y)
commutativityℤ* (neg zero) {y} = propertySymmetry (rightZero-ℤ* y)
commutativityℤ* (neg (suc x)) {y} = propertyTransitivity (congruence (negateℤ y +_) (commutativityℤ* (neg (x)) {y})) (unfoldMult2 x y)
