# The Commutative Ring of Integers: Type Theoretical Proofs With Agda

## Aim
The goal of this research project submitted as part of requirements for my MS, was to use Agda (a computerized proof assistant) to constructively build a set of proofs. These proofs are reasoned about intuitionistically, starting from base constructs all the way to various algebraic properties required for a certain abstract mathematical structure referred to as a Ring. 

This project was supervised by Dr Thorsten Altenkirch, and I'm forever grateful for all his time, expertise and most importantly, empathy towards my journey with Type Theory. 

The final solution involves an object of type "Ring" which satisfies all algebraic commutative ring axioms.

## Sample Proof
![image](https://github.com/essentialblend/integers-comm-ring/assets/73982939/5f9a7c1e-a672-4068-940b-97df58c28ef3)

## Construction
- Define, construct and prove algebraic properties of natural numbers using the Peano axioms.

  Ex: [Operations over naturals](https://github.com/essentialblend/integers-comm-ring/blob/main/natural_numbers/operations.agda), [properties over natural addition](https://github.com/essentialblend/integers-comm-ring/tree/main/natural_numbers/properties/addition), [properties over natural multiplication](https://github.com/essentialblend/integers-comm-ring/tree/main/natural_numbers/properties/multiplication).
   
- Use naturals constructively to define, construct, and prove algebraic properties of integers.

  Ex: [Properties over integral addition](https://github.com/essentialblend/integers-comm-ring/tree/main/integers_MAIN/properties/addition), [properties over integral multiplication](https://github.com/essentialblend/integers-comm-ring/tree/main/integers_MAIN/properties/multiplication), [distributive laws](https://github.com/essentialblend/integers-comm-ring/blob/main/integers_MAIN/properties/distributive_laws.agda).

- Use our proofs alongside tools for predicate logic, to culminate our final proof for the "type" Ring. 

  Ex: [Final proof](https://github.com/essentialblend/integers-comm-ring/blob/main/integers_MAIN/properties/ring_proof/ring_FINAL.agda).

## Project Structure

- `constructs\`: Basic types and type variables.

- `natural_numbers\`: Definition, operations and properties over natural numbers.

- `integers_MAIN\`: Definition, operations and properties over Integers. Main folder of interest.

- `predicate_logic\`: Tools for predicates.
