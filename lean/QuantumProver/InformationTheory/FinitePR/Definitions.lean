import Mathlib

/-!
Operational definitions for binary PR boxes.
-/

namespace FinitePR

open scoped BigOperators

/-- The same fixed two-element alphabet is used for every PR input and output. -/
abbrev Bit := ZMod 2

/-- Alice's one-hot input for a finite index known only to Alice. -/
def oneHot {N : ℕ} (I : Fin N) (i : Fin N) : Bit :=
  if i = I then 1 else 0

/-- The PR-box support condition; addition in `ZMod 2` is XOR. -/
def prRelation (u v α β : Bit) : Prop := α + β = u * v

/-- Alice's local output from her offset and her own PR output vector. -/
def aliceParity {N : ℕ} (d : Bit) (α : Fin N → Bit) : Bit :=
  d + ∑ i, α i

/-- Bob's local output from his own PR output vector. -/
def bobParity {N : ℕ} (β : Fin N → Bit) : Bit := ∑ i, β i

/-- The probability table of the ordinary binary PR box. -/
noncomputable def prWeight (u v α β : Bit) : ℝ :=
  by
    classical
    exact if prRelation u v α β then 1 / 2 else 0

/-- Output sign corresponding to the original convention `(-1)^a`. -/
noncomputable def bitSign (a : Bit) : ℝ := if a = 0 then 1 else -1

/-- Every real unit Bloch direction, with no finite input restriction. -/
abbrev Direction := {x : Fin 3 → ℝ // ∑ i, (x i) ^ 2 = 1}

/-- The closed-form projective law of the pure-state distribution.

Equality with the matrix Born formula is proved in `Main`.
-/
noncomputable def projectiveProbability (θ : ℝ) (x y : Direction) (a b : Bit) : ℝ :=
  (1 + bitSign a * Real.cos (2 * θ) * x.1 2
    + bitSign b * Real.cos (2 * θ) * y.1 2
    + bitSign a * bitSign b *
      (x.1 2 * y.1 2 + Real.sin (2 * θ) *
        (x.1 0 * y.1 0 - x.1 1 * y.1 1))) / 4

end FinitePR
