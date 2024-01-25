module natural_numbers.definition where

-- Definition: Natural Numbers
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}
