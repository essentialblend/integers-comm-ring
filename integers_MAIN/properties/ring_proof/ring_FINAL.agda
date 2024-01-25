module integers_MAIN.properties.ring_proof.ring_FINAL where

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
open import integers_MAIN.properties.ring_proof.group


-- Record-type: Ring
record IsRingℤ
  (additiveIdentity : A) (multiplicativeIdentity : A) (identityFunction : A → A) (negationFunction : A → A) (additionOp : A → A → A) (multiplicationOp : A → A → A) : prop where
    field
      -- ℤ is an abelian group under addition.
      isAbelianGroup : IsAbelianGroupℤ (additiveIdentity) (identityFunction) (negationFunction) (additionOp)
      -- ℤ is a monoid with multiplication.
      isMonoidℤ : IsMonoidℤ (multiplicativeIdentity) (identityFunction) (multiplicationOp)

-- Record-type: Commutative Ring
record IsCommRingℤ
  (additiveIdentity : A) (multiplicativeIdentity : A) (identityFunction : A → A) (negationFunction : A → A) (additionOp : A → A → A) (multiplicationOp : A → A → A) : prop where
    field
      -- ℤ is a ring
      isRingℤ : IsRingℤ (additiveIdentity) (multiplicativeIdentity) (identityFunction) (negationFunction) (additionOp) (multiplicationOp) 
      -- ℤ is commutative monoid
      isCommMonoidℤ : IsCommMonoidℤ (multiplicativeIdentity) (identityFunction) (multiplicationOp)


-- FINAL PROOFS

-- Proof: ℤ is a ring
ℤIsRing : IsRingℤ (pos zero) (pos 1) (idℤ) (negateℤ) (_+_) (_*_)
ℤIsRing = record {
  isAbelianGroup = ℤIsCommGroup;
  isMonoidℤ = ℤmultiplicationIsMonoid}

-- Proof: ℤ is a commutative ring.
ℤIsCommRing : IsCommRingℤ (pos zero) (pos 1) (idℤ) (negateℤ) (_+_) (_*_)
ℤIsCommRing = record {
  isRingℤ = ℤIsRing;
  isCommMonoidℤ = ℤmultiplicationIsCommMonoid }

