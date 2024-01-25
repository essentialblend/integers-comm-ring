module predicate_logic.properties where

open import constructs.type_variables

open import natural_numbers.definition
open import natural_numbers.operations

open import predicate_logic.definitions


-- Property: Congruence
congruence : {A B : Set} → (f : A → B) → {a b : A} → a ≡ b → f a ≡ f b
congruence f refl = refl

-- Property: Substitution
substitution : (P : A → prop) → {a b : A} → a ≡ b → P a → P b
substitution P refl pA = pA

-- Property: Symmetry 
{- Show that equality is symmetric, refl proves itself -}
propertySymmetry : {a b : A} → (a ≡ b) → (b ≡ a)
propertySymmetry refl = refl

-- Property: Transitivity
propertyTransitivity : ∀ {a b c : A} → (a ≡ b) → (b ≡ c) → (a ≡ c)
propertyTransitivity refl x = x

-- Show that ≡ is an EqRel
≡IsEqRel : {A : Set} → isEqRel (_≡_ {A = A})
≡IsEqRel = record {
  reflexive = refl;
  symmetric = propertySymmetry;
  transitive = propertyTransitivity}
