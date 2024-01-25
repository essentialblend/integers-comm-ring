module natural_numbers.properties.multiplication.absorption where

open import natural_numbers.definition
open import natural_numbers.operations

open import predicate_logic.definitions
open import predicate_logic.properties

-- Left Absorption : 0 * n ≡ 0
leftAbsorptionℕ* : {n : ℕ} → (0 * n) ≡ 0
leftAbsorptionℕ* {zero} = refl
leftAbsorptionℕ* {suc n} = refl

-- Right Absorption : n * 0 ≡ 0
rightAbsorptionℕ* : {n : ℕ} → (n * 0) ≡ 0
rightAbsorptionℕ* {zero} = refl
rightAbsorptionℕ* {suc n} = rightAbsorptionℕ* {n}
