module natural_numbers.properties.distributive_laws where

open import natural_numbers.definition
open import natural_numbers.operations

open import predicate_logic.definitions
open import predicate_logic.properties

open import natural_numbers.properties.addition.associativity
open import natural_numbers.properties.addition.commutativity

-- Left Distributivity Law 
leftDistributivityℕ : {l m n : ℕ} → ((l + m) * n) ≡ ((l * n) + (m * n))
leftDistributivityℕ {zero} {m} {n} = refl
leftDistributivityℕ {suc l} {m} {n} = propertyTransitivity (congruence (λ x → n + x) (leftDistributivityℕ {l})) (propertySymmetry (associativityℕ+ {n} {l * n} {m * n}))

-- Right Distributivity Law
rightDistributivityℕ : {l m n : ℕ} → (l * (m + n)) ≡ ((l * m) + (l * n))
rightDistributivityℕ {zero} {m} {n} = refl
rightDistributivityℕ {suc l} {m} {n} = propertyTransitivity (congruence (λ x → ((m + n) + x)) (rightDistributivityℕ {l} {m} {n})) (propertySymmetry  (propertyTransitivity (associativityℕ+ {m} {(l * m)} {(n + (l * n))}) (propertySymmetry (propertyTransitivity (associativityℕ+ {m} {n} {(l * m) + (l * n)}) (congruence (m +_) (propertyTransitivity (commutativityℕ+ n {(l * m) + (l * n)}) (propertyTransitivity (associativityℕ+ {l * m} {l * n} {n}) (congruence ((l * m) +_) (commutativityℕ+ (l * n) {n})))))))))
