module natural_numbers.properties.final_semi_ring.compiled_proofs where

open import constructs.type_variables

open import predicate_logic.definitions
open import predicate_logic.properties

open import natural_numbers.definition
open import natural_numbers.operations

open import natural_numbers.properties.addition.neutralities
open import natural_numbers.properties.addition.associativity
open import natural_numbers.properties.addition.commutativity

open import natural_numbers.properties.multiplication.neutralities
open import natural_numbers.properties.multiplication.associativity
open import natural_numbers.properties.multiplication.commutativity

open import natural_numbers.properties.distributive_laws


-- Definition: Monoid
record IsMonoid
  (e : A) (_∙_ : A → A → A) : prop where
    field
      leftNeutrality  : {x : A} → (e ∙ x) ≡ x
      rightNeutrality : {x : A} → (x ∙ e) ≡ x
      associativity   : {x y z : A} → ((x ∙ y) ∙ z) ≡ (x ∙ (y ∙ z))

-- Definition: Commutative Monoid
record IsCommutativeMonoid
  (e : A) (_∙_ : A → A → A) : prop where
    field
      isMonoid : IsMonoid e (_∙_)
      isCommutative : { x y : A } → (x ∙ y) ≡ (y ∙ x)



-- Proof: Show that ℕ under + is a (commutative) monoid
additionIsMonoid : IsMonoid (zero) (_+_)
additionIsMonoid = record {
  leftNeutrality  = leftNeutralityℕ+;
  rightNeutrality = rightNeutralityℕ+;
  associativity   = λ {x} {y} {z} → associativityℕ+ {x} {y} {z} }

additionIsCommMonoid : IsCommutativeMonoid (zero) (_+_)
additionIsCommMonoid = record {
  isMonoid = additionIsMonoid;
  isCommutative = λ {x} {y} → commutativityℕ+ x {y} }

-- Proof: Show that ℕ under * is a (commutative) monoid
multiplicationIsMonoid : IsMonoid (1) (_*_)
multiplicationIsMonoid = record {
  leftNeutrality = leftNeutralityℕ*;
  rightNeutrality = rightNeutralityℕ*;
  associativity = λ {x} {y} {z} →  associativityℕ* {x} {y} {z} }

multiplicationIsCommMonoid : IsCommutativeMonoid (1) (_*_)
multiplicationIsCommMonoid = record {
  isMonoid = multiplicationIsMonoid;
  isCommutative = λ {x} {y} → commutativityℕ* x {y} }



-- Proof: Show that ℕ under addition and multiplication form a semi-ring
record IsCommutativeSemiRing
  (additionIdentity : A) (multiplicationIdentity : A) (additionOp : A → A → A) (multiplicationOp : A → A → A) : prop where
    field
      additionCommMonoid : IsCommutativeMonoid (additionIdentity) (additionOp)
      multiplicationCommMonoid : IsCommutativeMonoid (multiplicationIdentity) (multiplicationOp)
      leftDistributivity : {x y z : A} → multiplicationOp (additionOp x y) z ≡ additionOp (multiplicationOp x z) (multiplicationOp y z)
      rightDistributivity : {x y z : A} → multiplicationOp x (additionOp y z) ≡ additionOp (multiplicationOp x y) (multiplicationOp x z)


-- FINAL PROOF
semiRing+* : IsCommutativeSemiRing (0) (1) (_+_) (_*_)
semiRing+* = record {
  additionCommMonoid = additionIsCommMonoid;
  multiplicationCommMonoid = multiplicationIsCommMonoid;
  leftDistributivity = λ {x} {y} {z} → leftDistributivityℕ {x} {y} {z};
  rightDistributivity = λ {x} {y} {z} → rightDistributivityℕ {x} {y} {z}}
