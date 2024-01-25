module integers_MAIN.properties.ring_proof.group where

open import constructs.type_variables

open import predicate_logic.definitions

open import natural_numbers.definition

open import integers_MAIN.definition
open import integers_MAIN.operations

open import integers_MAIN.properties.addition.neutralities
open import integers_MAIN.properties.addition.commutativity
open import integers_MAIN.properties.addition.associativity
open import integers_MAIN.properties.addition.inverses

open import integers_MAIN.properties.multiplication.neutralities
open import integers_MAIN.properties.multiplication.commutativity
open import integers_MAIN.properties.multiplication.associativity


open import integers_MAIN.properties.ring_proof.monoid

-- Record-type: Group
record IsGroupℤ
  (e : A) (identityFunction : A → A) (negationFunction : A → A)  (_∙_ : A → A → A) : prop where
    field
      -- Is Monoid
      isMonoidℤ : IsMonoidℤ (e) (identityFunction) (_∙_) 
      -- Inverses
      leftInverse : {x : A} → ((negationFunction x) ∙ x) ≡ e
      rightInverse : {x : A} → (x ∙ (negationFunction x)) ≡ e

-- Record-type: Abelian Group
record IsAbelianGroupℤ (e : A) (identityFunction : A → A) (negationFunction : A → A)  (_∙_ : A → A → A) : prop where
    field
      -- Is Group
      isGroupℤ : IsGroupℤ (e) (identityFunction) (negationFunction) (_∙_) 
      -- Commutativity
      isCommutative : {x y : A} → (x ∙ y) ≡ (y ∙ x)

-- Proof: ℤ is a group
ℤIsGroup : IsGroupℤ (pos zero) (idℤ) (negateℤ) (_+_)
ℤIsGroup = record {
  isMonoidℤ = ℤadditionIsMonoid;
  leftInverse = λ {x} → leftAdditiveInverseℤ+ x;
  rightInverse = λ {x} → rightAdditiveInverseℤ+ x }

-- Proof: ℤ is a commutative group
ℤIsCommGroup : IsAbelianGroupℤ (pos zero) (idℤ) (negateℤ) (_+_)
ℤIsCommGroup = record {
  isGroupℤ = ℤIsGroup;
  isCommutative = λ {x} {y} → commutativityℤ+ x {y} }
