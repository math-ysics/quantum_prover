import QuantumProver.InformationTheory.QuantumEntropy.TensorLogTrace

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix Kronecker

namespace QuantumProver.QuantumEntropy

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem entropyNats_eq_neg_trace_mul_log {I : Type*} [Fintype I] [DecidableEq I]
    {R : Matrix I I ℂ} (hR : R.IsHermitian) :
    entropyNats R = -(R * cfc Real.log R).trace.re := by
  rw [entropyNats,
    QuantumProver.SuperchannelDiscrimination.MatrixLog.cfc_mulLog_eq_mul_log hR]

theorem finiteRelativeEntropyBits_faithful_product_chain
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {R : Matrix (I × J) (I × J) ℂ} {P : Matrix I I ℂ}
    (hR : R.PosSemidef) (hP : P.PosDef) :
    finiteRelativeEntropyBits R (P ⊗ₖ partialTrace_left R) =
      finiteRelativeEntropyBits R (partialTrace_right R ⊗ₖ partialTrace_left R) +
        finiteRelativeEntropyBits (partialTrace_right R) P := by
  have hA := partialTraceRight_posSemidef hR
  have hB := partialTraceLeft_posSemidef hR
  have hs := hasSupportIn_faithful_left_tensor_marginal hR hP
  rw [finiteRelativeEntropyBits_marginal_tensor hR]
  simp only [finiteRelativeEntropyBits]
  rw [
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.finiteRelativeEntropyBits_eq_spectral hR.1,
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.finiteRelativeEntropyBits_eq_spectral hA.1,
    comparatorLogTrace_tensor hP.1 hB.1 hs]
  simp only [entropyBits, QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits,
    QuantumProver.SuperchannelDiscrimination.MatrixLog.cfc_mulLog_eq_mul_log hA.1,
    QuantumProver.SuperchannelDiscrimination.MatrixLog.cfc_mulLog_eq_mul_log hB.1,
    QuantumProver.SuperchannelDiscrimination.MatrixLog.cfc_mulLog_eq_mul_log hR.1,
    Complex.add_re]
  ring

theorem relativeEntropyBits_faithful_product_chain
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {R : Matrix (I × J) (I × J) ℂ} {P : Matrix I I ℂ}
    (hR : R.PosSemidef) (hP : P.PosDef) :
    relativeEntropyBits R (P ⊗ₖ partialTrace_left R) =
      relativeEntropyBits R (partialTrace_right R ⊗ₖ partialTrace_left R) +
        relativeEntropyBits (partialTrace_right R) P := by
  classical
  have hs := hasSupportIn_faithful_left_tensor_marginal hR hP
  have hm := hasSupportIn_marginal_tensor hR
  have hfinite : relativeEntropyBits R (P ⊗ₖ partialTrace_left R) =
      (finiteRelativeEntropyBits R (P ⊗ₖ partialTrace_left R) : EReal) := by
    simp only [relativeEntropyBits,
      QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits, if_pos hs]
  have hproduct :
      relativeEntropyBits R (partialTrace_right R ⊗ₖ partialTrace_left R) =
        (finiteRelativeEntropyBits R
          (partialTrace_right R ⊗ₖ partialTrace_left R) : EReal) := by
    simp only [relativeEntropyBits,
      QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits, if_pos hm]
  have hreference : relativeEntropyBits (partialTrace_right R) P =
      (finiteRelativeEntropyBits (partialTrace_right R) P : EReal) := by
    exact QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits_of_posDef _ hP
  rw [hfinite, hproduct, hreference,
    ← EReal.coe_add, finiteRelativeEntropyBits_faithful_product_chain hR hP]

theorem strongSubadditivity_of_posSemidef
    {R : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hR : R.PosSemidef) :
    entropyBits (marginalB R) + entropyBits R ≤
      entropyBits (marginalAB R) + entropyBits (marginalBC R) := by
  have hA := partialTraceRight_posSemidef hR
  have hBC := partialTraceLeft_posSemidef hR
  have hdpi := QuantumProver.SuperchannelDiscrimination.InputSupport.relativeEntropyBits_kraus_dpi
    (traceCKraus (A := A) (B := B) (C := C))
    (traceCKraus_complete (A := A) (B := B) (C := C)) hR (hA.kronecker hBC)
  rw [traceCKraus_action R,
    traceCKraus_kronecker (partialTrace_right R) (partialTrace_left R),
    ← marginalB_eq_partialTraceRight_marginalBC R] at hdpi
  change relativeEntropyBits (marginalAB R) (marginalA R ⊗ₖ marginalB R) ≤
    relativeEntropyBits R (marginalA R ⊗ₖ marginalBC R) at hdpi
  have hout :
      relativeEntropyBits (marginalAB R) (marginalA R ⊗ₖ marginalB R) =
        ((entropyBits (marginalA R) + entropyBits (marginalB R) -
          entropyBits (marginalAB R) : ℝ) : EReal) := by
    simpa only [partialTraceRight_marginalAB R] using
      relativeEntropyBits_marginal_tensor (marginalAB_posSemidef hR)
  have hin : relativeEntropyBits R (marginalA R ⊗ₖ marginalBC R) =
      ((entropyBits (marginalA R) + entropyBits (marginalBC R) -
        entropyBits R : ℝ) : EReal) := relativeEntropyBits_marginal_tensor hR
  rw [hout, hin] at hdpi
  have hreal :
      entropyBits (marginalA R) + entropyBits (marginalB R) -
          entropyBits (marginalAB R) ≤
        entropyBits (marginalA R) + entropyBits (marginalBC R) - entropyBits R :=
    EReal.coe_le_coe_iff.mp hdpi
  linarith only [hreal]

theorem strongSubadditivity
    {R : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hR : IsDensity R) :
    entropyBits (marginalB R) + entropyBits R ≤
      entropyBits (marginalAB R) + entropyBits (marginalBC R) :=
  strongSubadditivity_of_posSemidef hR.1

theorem strongSubadditivity_nats_of_posSemidef
    {R : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hR : R.PosSemidef) :
    entropyNats (marginalB R) + entropyNats R ≤
      entropyNats (marginalAB R) + entropyNats (marginalBC R) := by
  have hbits := strongSubadditivity_of_posSemidef hR
  have hlog : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
  have h := mul_le_mul_of_nonneg_right hbits hlog
  simpa only [add_mul, ← entropyNats_eq_entropyBits_mul_log_two] using h

theorem strongSubadditivity_nats
    {R : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hR : IsDensity R) :
    entropyNats (marginalB R) + entropyNats R ≤
      entropyNats (marginalAB R) + entropyNats (marginalBC R) :=
  strongSubadditivity_nats_of_posSemidef hR.1

theorem conditionalMutualInformationBits_nonneg_of_posSemidef
    {R : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hR : R.PosSemidef) :
    0 ≤ conditionalMutualInformationBits R := by
  have h := strongSubadditivity_of_posSemidef hR
  unfold conditionalMutualInformationBits
  linarith only [h]

theorem conditionalMutualInformationBits_nonneg
    {R : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hR : IsDensity R) :
    0 ≤ conditionalMutualInformationBits R :=
  conditionalMutualInformationBits_nonneg_of_posSemidef hR.1

end QuantumProver.QuantumEntropy
