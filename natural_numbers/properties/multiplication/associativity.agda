module natural_numbers.properties.multiplication.associativity where

open import natural_numbers.definition
open import natural_numbers.operations

open import predicate_logic.definitions
open import predicate_logic.properties

open import natural_numbers.properties.distributive_laws

-- Associativity under ℕ multiplication.
associativityℕ* : {m n p : ℕ} → ((m * n) * p) ≡ (m * (n * p))
associativityℕ* {zero} {n} {p} = refl
associativityℕ* {suc m} {n} {p} = propertyTransitivity (leftDistributivityℕ {n} {m * n} {p}) (congruence ((n * p) +_) (associativityℕ* {m} {n} {p}))
