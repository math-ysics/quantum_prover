import QuantumProver.InformationTheory.SuperchannelDiscrimination.FlaggedStates

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.QuantumEntropy

abbrev IsDensity {A : Type*} [Fintype A] [DecidableEq A]
    (R : Matrix A A ℂ) : Prop :=
  QuantumProver.SuperchannelDiscrimination.FlaggedStates.IsDensity R

abbrev entropyBits {A : Type*} [Fintype A] [DecidableEq A]
    (R : Matrix A A ℂ) : ℝ :=
  QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits R

abbrev finiteRelativeEntropyBits {A : Type*} [Fintype A] [DecidableEq A]
    (R S : Matrix A A ℂ) : ℝ :=
  QuantumProver.SuperchannelDiscrimination.FlaggedStates.finiteRelativeEntropyBits R S

abbrev relativeEntropyBits {A : Type*} [Fintype A] [DecidableEq A]
    (R S : Matrix A A ℂ) : EReal :=
  QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits R S

abbrev HasSupportIn {A : Type*} [Fintype A] [DecidableEq A]
    (R S : Matrix A A ℂ) : Prop :=
  QuantumProver.SuperchannelDiscrimination.FlaggedStates.HasSupportIn R S

def entropyNats {A : Type*} [Fintype A] [DecidableEq A]
    (R : Matrix A A ℂ) : ℝ :=
  -(cfc (fun x : ℝ => x * Real.log x) R).trace.re

theorem entropyNats_eq_entropyBits_mul_log_two {A : Type*}
    [Fintype A] [DecidableEq A] (R : Matrix A A ℂ) :
    entropyNats R = entropyBits R * Real.log 2 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simp only [entropyNats, entropyBits,
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits,
    div_mul_cancel₀ _ hlog]

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

def partialTrace_right (R : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ :=
  fun a a' => ∑ b, R (a, b) (a', b)

def partialTrace_left (R : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  fun b b' => ∑ a, R (a, b) (a, b')

def marginalAB (R : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  fun ab ab' => ∑ c, R (ab.1, (ab.2, c)) (ab'.1, (ab'.2, c))

abbrev marginalA (R : Matrix (A × (B × C)) (A × (B × C)) ℂ) : Matrix A A ℂ :=
  partialTrace_right R

abbrev marginalBC (R : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    Matrix (B × C) (B × C) ℂ :=
  partialTrace_left R

abbrev marginalB (R : Matrix (A × (B × C)) (A × (B × C)) ℂ) : Matrix B B ℂ :=
  partialTrace_left (marginalAB R)

def conditionalMutualInformationBits
    (R : Matrix (A × (B × C)) (A × (B × C)) ℂ) : ℝ :=
  entropyBits (marginalAB R) + entropyBits (marginalBC R) -
    entropyBits (marginalB R) - entropyBits R

end QuantumProver.QuantumEntropy
