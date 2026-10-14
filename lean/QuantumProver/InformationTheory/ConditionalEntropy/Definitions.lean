import QuantumProver.InformationTheory.QuantumEntropy.Definitions
import QuantumProver.InformationTheory.SuperchannelDiscrimination.EffectPerturbation

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.ConditionalEntropy

abbrev IsDensity {I : Type*} [Fintype I] [DecidableEq I]
    (R : Matrix I I ℂ) : Prop := QuantumProver.QuantumEntropy.IsDensity R

abbrev entropyBits {I : Type*} [Fintype I] [DecidableEq I]
    (R : Matrix I I ℂ) : ℝ := QuantumProver.QuantumEntropy.entropyBits R

abbrev traceNorm {I : Type*} [Fintype I] [DecidableEq I]
    (R : Matrix I I ℂ) : ℝ :=
  QuantumProver.SuperchannelDiscrimination.EffectPerturbation.traceNorm R

def traceDistance {I : Type*} [Fintype I] [DecidableEq I]
    (R S : Matrix I I ℂ) : ℝ := traceNorm (R - S) / 2

def mix {I : Type*} (p : ℝ) (R S : Matrix I I ℂ) : Matrix I I ℂ :=
  (1 - p) • R + p • S

def conditionalEntropyBits {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (R : Matrix (A × B) (A × B) ℂ) : ℝ :=
  entropyBits R - entropyBits (QuantumProver.QuantumEntropy.partialTrace_left R)

def logDimA (A : Type*) [Fintype A] : ℝ :=
  Real.log (Fintype.card A : ℝ) / Real.log 2

abbrev binaryEntropy (p : ℝ) : ℝ :=
  QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagEntropyBits p

def winterBound (A : Type*) [Fintype A] (epsilon : ℝ) : ℝ :=
  2 * epsilon * logDimA A +
    (1 + epsilon) * binaryEntropy (epsilon / (1 + epsilon))

@[simp] theorem mix_zero {I : Type*} (R S : Matrix I I ℂ) : mix 0 R S = R := by
  simp [mix]

@[simp] theorem mix_one {I : Type*} (R S : Matrix I I ℂ) : mix 1 R S = S := by
  simp [mix]

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy, QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagEntropyBits]

@[simp] theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy, QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagEntropyBits]

@[simp] theorem winterBound_zero (A : Type*) [Fintype A] : winterBound A 0 = 0 := by
  simp [winterBound]

theorem traceDistance_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (R S : Matrix I I ℂ) : 0 ≤ traceDistance R S := by
  exact div_nonneg
    (QuantumProver.SuperchannelDiscrimination.EffectPerturbation.traceNorm_nonneg (R - S))
    (by norm_num)

theorem mix_isDensity {I : Type*} [Fintype I] [DecidableEq I]
    {R S : Matrix I I ℂ} (hR : IsDensity R) (hS : IsDensity S)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsDensity (mix p R S) := by
  refine ⟨(hR.1.smul (sub_nonneg.mpr hp1)).add (hS.1.smul hp0), ?_⟩
  simp only [mix, Matrix.trace_add, Matrix.trace_smul, hR.2, hS.2,
    ← add_smul, sub_add_cancel, one_smul]

theorem winter_scalar_bound (epsilon L a b x y w cost : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hlower : (1 - epsilon / (1 + epsilon)) * a +
      (epsilon / (1 + epsilon)) * x ≤ w)
    (hupper : w ≤ (1 - epsilon / (1 + epsilon)) * b +
      (epsilon / (1 + epsilon)) * y + cost)
    (hx : -L ≤ x) (hy : y ≤ L) :
    a - b ≤ 2 * epsilon * L + (1 + epsilon) * cost := by
  have hdenpos : 0 < 1 + epsilon := by linarith
  have hden : 1 + epsilon ≠ 0 := ne_of_gt hdenpos
  have hbase : (1 + epsilon) * (1 - epsilon / (1 + epsilon)) = 1 := by
    field_simp [hden]
    <;> ring
  have hnoise : (1 + epsilon) * (epsilon / (1 + epsilon)) = epsilon := by
    field_simp [hden]
  have hscaled := mul_le_mul_of_nonneg_left (hlower.trans hupper) (le_of_lt hdenpos)
  simp only [mul_add, ← mul_assoc, hbase, hnoise, one_mul] at hscaled
  have hgap : y - x ≤ 2 * L := by linarith
  have hgapscaled := mul_le_mul_of_nonneg_left hgap hepsilon
  nlinarith

end QuantumProver.ConditionalEntropy
