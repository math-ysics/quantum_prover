import QuantumProver.InformationTheory.QuantumEntropy.MatrixLogSupport
import QuantumProver.InformationTheory.QuantumEntropy.PartialTraceKraus

noncomputable section

open Matrix
open QuantumProver.SuperchannelDiscrimination.MatrixLog
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix Kronecker

namespace QuantumProver.QuantumEntropy

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem entropyNats_eq_trace_cfc_negMulLog (R : Matrix I I ℂ) :
    entropyNats R = (cfc Real.negMulLog R).trace.re := by
  simp only [entropyNats, Real.negMulLog_eq_neg, cfc_neg,
    Matrix.trace_neg, Complex.neg_re]

theorem comparatorLogTrace_tensor
    {R : Matrix (I × J) (I × J) ℂ} {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hs : HasSupportIn R (A ⊗ₖ B)) :
    (R * cfc Real.log (A ⊗ₖ B)).trace =
      (partialTrace_right R * cfc Real.log A).trace +
        (partialTrace_left R * cfc Real.log B).trace := by
  rw [MatrixLogSupport.trace_weighted_tensor_log hA hB hs,
    partialTrace_right_mul_trace, partialTrace_left_mul_trace]

theorem comparatorLogTrace_marginal_tensor
    {R : Matrix (I × J) (I × J) ℂ} (hR : R.PosSemidef) :
    (R * cfc Real.log (partialTrace_right R ⊗ₖ partialTrace_left R)).trace =
      (partialTrace_right R * cfc Real.log (partialTrace_right R)).trace +
        (partialTrace_left R * cfc Real.log (partialTrace_left R)).trace :=
  comparatorLogTrace_tensor (partialTraceRight_posSemidef hR).1
    (partialTraceLeft_posSemidef hR).1 (hasSupportIn_marginal_tensor hR)

theorem relativeEntropyNats_reference_marginal
    {R : Matrix (I × J) (I × J) ℂ} {A : Matrix I I ℂ}
    (hR : R.PosSemidef) (hA : A.IsHermitian)
    (hs : HasSupportIn R (A ⊗ₖ partialTrace_left R)) :
    (R * (cfc Real.log R - cfc Real.log (A ⊗ₖ partialTrace_left R))).trace.re =
      -entropyNats R + entropyNats (partialTrace_left R) -
        (partialTrace_right R * cfc Real.log A).trace.re := by
  have hB := partialTraceLeft_posSemidef hR
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
    comparatorLogTrace_tensor hA hB.1 hs]
  simp only [entropyNats, cfc_mulLog_eq_mul_log hR.1,
    cfc_mulLog_eq_mul_log hB.1, Complex.add_re]
  ring

theorem relativeEntropyNats_reference_marginal_of_posDef
    {R : Matrix (I × J) (I × J) ℂ} {A : Matrix I I ℂ}
    (hR : R.PosSemidef) (hA : A.PosDef) :
    (R * (cfc Real.log R - cfc Real.log (A ⊗ₖ partialTrace_left R))).trace.re =
      -entropyNats R + entropyNats (partialTrace_left R) -
        (partialTrace_right R * cfc Real.log A).trace.re :=
  relativeEntropyNats_reference_marginal hR hA.1
    (hasSupportIn_faithful_left_tensor_marginal hR hA)

theorem relativeEntropyNats_marginal_tensor
    {R : Matrix (I × J) (I × J) ℂ} (hR : R.PosSemidef) :
    (R * (cfc Real.log R -
      cfc Real.log (partialTrace_right R ⊗ₖ partialTrace_left R))).trace.re =
      entropyNats (partialTrace_right R) + entropyNats (partialTrace_left R) -
        entropyNats R := by
  have hA := partialTraceRight_posSemidef hR
  have hB := partialTraceLeft_posSemidef hR
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re,
    comparatorLogTrace_marginal_tensor hR]
  simp only [entropyNats, cfc_mulLog_eq_mul_log hA.1,
    cfc_mulLog_eq_mul_log hB.1, cfc_mulLog_eq_mul_log hR.1, Complex.add_re]
  ring

theorem finiteRelativeEntropyBits_marginal_tensor
    {R : Matrix (I × J) (I × J) ℂ} (hR : R.PosSemidef) :
    finiteRelativeEntropyBits R (partialTrace_right R ⊗ₖ partialTrace_left R) =
      entropyBits (partialTrace_right R) + entropyBits (partialTrace_left R) -
        entropyBits R := by
  have hA := partialTraceRight_posSemidef hR
  have hB := partialTraceLeft_posSemidef hR
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.finiteRelativeEntropyBits R
    (partialTrace_right R ⊗ₖ partialTrace_left R) = _
  rw [QuantumProver.SuperchannelDiscrimination.FlaggedStates.finiteRelativeEntropyBits_eq_spectral hR.1,
    comparatorLogTrace_marginal_tensor hR]
  simp only [entropyBits, QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits,
    cfc_mulLog_eq_mul_log hA.1, cfc_mulLog_eq_mul_log hB.1,
    cfc_mulLog_eq_mul_log hR.1, Complex.add_re]
  ring

theorem relativeEntropyBits_marginal_tensor
    {R : Matrix (I × J) (I × J) ℂ} (hR : R.PosSemidef) :
    relativeEntropyBits R (partialTrace_right R ⊗ₖ partialTrace_left R) =
      ((entropyBits (partialTrace_right R) + entropyBits (partialTrace_left R) -
        entropyBits R : ℝ) : EReal) := by
  classical
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits R
    (partialTrace_right R ⊗ₖ partialTrace_left R) = _
  rw [QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits,
    if_pos (hasSupportIn_marginal_tensor hR)]
  exact congrArg (fun x : ℝ => (x : EReal)) (finiteRelativeEntropyBits_marginal_tensor hR)

theorem relativeEntropyBits_marginal_tensor_of_isDensity
    {R : Matrix (I × J) (I × J) ℂ} (hR : IsDensity R) :
    relativeEntropyBits R (partialTrace_right R ⊗ₖ partialTrace_left R) =
      ((entropyBits (partialTrace_right R) + entropyBits (partialTrace_left R) -
        entropyBits R : ℝ) : EReal) :=
  relativeEntropyBits_marginal_tensor hR.1

end QuantumProver.QuantumEntropy
