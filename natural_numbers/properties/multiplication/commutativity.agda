module natural_numbers.properties.multiplication.commutativity where

open import natural_numbers.definition
open import natural_numbers.operations

open import predicate_logic.definitions
open import predicate_logic.properties

open import natural_numbers.properties.addition.neutralities
open import natural_numbers.properties.addition.commutativity
open import natural_numbers.properties.addition.associativity

open import natural_numbers.properties.multiplication.absorption

-- Lemma for commutativity of multiplication
distrRightSucℕ* : (y : ℕ) {x : ℕ} → (y * (suc x)) ≡ (y + (y * x))
distrRightSucℕ* zero {x} = refl
distrRightSucℕ* (suc y) {x} = propertyTransitivity (congruence suc (congruence (x +_) (distrRightSucℕ* (y) {x}))) (congruence suc (propertyTransitivity (propertySymmetry (associativityℕ+ {x} {y} {y * x})) (propertyTransitivity (congruence (_+ (y * x)) (commutativityℕ+ x {y})) (associativityℕ+ {y} {x} {y * x}) )))


-- Main Proof: Commutativity of ℕ multiplication
commutativityℕ* : (m : ℕ) {n : ℕ} → (m * n) ≡ (n * m)
commutativityℕ* zero {n} = propertySymmetry (rightAbsorptionℕ* {n})
commutativityℕ* (suc x) {y} = propertyTransitivity (congruence (y +_) (commutativityℕ* x {y})) (propertySymmetry (distrRightSucℕ* y {x}))
