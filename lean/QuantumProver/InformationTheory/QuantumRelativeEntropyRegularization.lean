import QuantumProver.InformationTheory.QuantumRelativeEntropyContinuity

set_option autoImplicit false

noncomputable section

open Filter Set Topology Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open QuantumProver.SuperchannelDiscrimination
open QuantumProver.SuperchannelDiscrimination.FlaggedStates
open QuantumProver.SuperchannelDiscrimination.TensorEntropy
open QuantumProver.SuperchannelDiscrimination.EntropyContinuity
open QuantumProver.SuperchannelDiscrimination.LogCompression
open QuantumProver.QuantumRelativeEntropyContinuity

namespace QuantumProver.QuantumRelativeEntropyRegularization

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Mat (I : Type*) := Matrix I I ℂ

def identityRegularizedMatrix (R : Mat I) (c δ : ℝ) : Mat I :=
  (1 + δ * c * (Fintype.card I : ℝ))⁻¹ • (R + (δ * c) • (1 : Mat I))

theorem identityRegularizedMatrix_isDensity {R : Mat I} (hR : IsDensity R)
    {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) : IsDensity (identityRegularizedMatrix R c δ) := by
  have hDen : 0 < 1 + δ * c * (Fintype.card I : ℝ) := by positivity
  have hPSD : (identityRegularizedMatrix R c δ).PosSemidef :=
    (hR.1.add (Matrix.PosSemidef.one.smul (mul_nonneg hδ hc))).smul
      (inv_nonneg.mpr hDen.le)
  refine ⟨hPSD, ?_⟩
  apply Complex.ext
  · simp only [identityRegularizedMatrix, Matrix.trace_smul, Complex.smul_re,
      Matrix.trace_add, Complex.add_re, hR.2, Complex.one_re, Matrix.trace_one,
      Complex.natCast_re, smul_eq_mul]
    exact inv_mul_cancel₀ hDen.ne'
  · simpa only [Complex.one_im] using (Complex.nonneg_iff.mp hPSD.trace_nonneg).2.symm

theorem identityRegularizedMatrix_posDef {R : Mat I} (hR : R.PosSemidef)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) : (identityRegularizedMatrix R c δ).PosDef := by
  have hDen : 0 < 1 + δ * c * (Fintype.card I : ℝ) := by positivity
  exact (regularizedReference_posDef hR (mul_pos hδ hc)).smul (inv_pos.mpr hDen)

theorem identityRegularizedMatrix_tendsto (R : Mat I) (c : ℝ) :
    Tendsto (identityRegularizedMatrix R c) (𝓝 (0 : ℝ)) (𝓝 R) := by
  have hId : Tendsto (fun δ : ℝ => δ) (𝓝 0) (𝓝 (0 : ℝ)) := tendsto_id
  have hOne : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 0) (𝓝 (1 : ℝ)) := tendsto_const_nhds
  have hDen : Tendsto (fun δ : ℝ => 1 + δ * c * (Fintype.card I : ℝ)) (𝓝 0) (𝓝 1) := by
    simpa using hOne.add ((hId.mul_const c).mul_const (Fintype.card I : ℝ))
  have hInv := hDen.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hR : Tendsto (fun _ : ℝ => R) (𝓝 0) (𝓝 R) := tendsto_const_nhds
  have hI : Tendsto (fun _ : ℝ => (1 : Mat I)) (𝓝 0) (𝓝 (1 : Mat I)) := tendsto_const_nhds
  have hShift : Tendsto (fun δ : ℝ => R + (δ * c) • (1 : Mat I)) (𝓝 0) (𝓝 R) := by
    simpa using hR.add ((hId.mul_const c).smul hI)
  change Tendsto (fun δ : ℝ => (1 + δ * c * (Fintype.card I : ℝ))⁻¹ •
    (R + (δ * c) • (1 : Mat I))) (𝓝 0) (𝓝 R)
  simpa only [inv_one, one_smul] using hInv.smul hShift

private theorem spectralWeight_one {B : Mat I} (hB : B.IsHermitian) (i : I) :
    spectralWeight (1 : Mat I) hB i = 1 := by
  simp only [spectralWeight, Matrix.mul_one]
  change ((star (hB.eigenvectorUnitary : Mat I) * (hB.eigenvectorUnitary : Mat I)) i i).re = 1
  rw [Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.prop]
  simp

theorem trace_shiftedLog_eq_sum {B : Mat I} (hB : B.IsHermitian) (ε : ℝ) :
    (cfc Real.log (B + ε • (1 : Mat I))).trace.re =
      ∑ i, Real.log (hB.eigenvalues i + ε) := by
  rw [shifted_log_cfc hB ε]
  simpa only [Matrix.one_mul, spectralWeight_one, one_mul] using
    trace_mul_cfc_re_eq_sum (1 : Mat I) hB (fun x : ℝ => Real.log (x + ε))

theorem identity_logContribution_tendsto {B : Mat I} (hB : B.IsHermitian) :
    Tendsto (fun ε : ℝ => ε * (cfc Real.log (B + ε • (1 : Mat I))).trace.re)
      (𝓝 0) (𝓝 0) := by
  have hi (i : I) : Tendsto (fun ε : ℝ => ε * Real.log (hB.eigenvalues i + ε))
      (𝓝 0) (𝓝 0) := by
    by_cases hz : hB.eigenvalues i = 0
    · simpa only [hz, zero_add, mul_zero, Real.log_zero] using
        Real.continuous_mul_log.continuousAt.tendsto (x := (0 : ℝ))
    · have hl : ContinuousAt (fun ε : ℝ => Real.log (hB.eigenvalues i + ε)) 0 := by
        apply ContinuousAt.log
        · fun_prop
        · simpa using hz
      simpa using tendsto_id.mul hl.tendsto
  simpa only [trace_shiftedLog_eq_sum hB, Finset.mul_sum, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun i _ => hi i)

theorem simultaneousShift_eq (A B : Mat I) (hA : A.IsHermitian) (ε : ℝ) :
    finiteRelativeEntropyBits (A + ε • (1 : Mat I)) (B + ε • (1 : Mat I)) =
      regularizedObjectiveBits A B ε +
        (entropyTrace (A + ε • (1 : Mat I)) - entropyTrace A -
          ε * (cfc Real.log (B + ε • (1 : Mat I))).trace.re) / Real.log 2 := by
  have hShift : (A + ε • (1 : Mat I)).IsHermitian :=
    hA.add (Matrix.PosSemidef.one.isHermitian.smul (by rfl : IsSelfAdjoint ε))
  rw [finiteRelativeEntropyBits_eq_spectral hShift, regularizedObjectiveBits]
  simp only [entropyTrace, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_add,
    Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
  ring

theorem simultaneousShift_tendsto {A B : Mat I} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hs : HasSupportIn A B) :
    Tendsto (fun ε : ℝ => finiteRelativeEntropyBits (A + ε • (1 : Mat I)) (B + ε • (1 : Mat I)))
      (𝓝 0) (𝓝 (finiteRelativeEntropyBits A B)) := by
  have hId : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 (0 : ℝ)) := tendsto_id
  have hAConst : Tendsto (fun _ : ℝ => A) (𝓝 0) (𝓝 A) := tendsto_const_nhds
  have hIConst : Tendsto (fun _ : ℝ => (1 : Mat I)) (𝓝 0) (𝓝 (1 : Mat I)) := tendsto_const_nhds
  have hShift : Tendsto (fun ε : ℝ => A + ε • (1 : Mat I)) (𝓝 0) (𝓝 A) := by
    simpa using hAConst.add (hId.smul hIConst)
  have hHerm : ∀ᶠ ε : ℝ in 𝓝 0, (A + ε • (1 : Mat I)).IsHermitian :=
    Filter.Eventually.of_forall fun ε =>
      hA.1.add (Matrix.PosSemidef.one.isHermitian.smul (by rfl : IsSelfAdjoint ε))
  have hEntropy := tendsto_entropyTrace hShift hHerm hA.1
  have hConst : Tendsto (fun _ : ℝ => entropyTrace A) (𝓝 0) (𝓝 (entropyTrace A)) :=
    tendsto_const_nhds
  have hCorrection : Tendsto (fun ε : ℝ =>
      (entropyTrace (A + ε • (1 : Mat I)) - entropyTrace A -
        ε * (cfc Real.log (B + ε • (1 : Mat I))).trace.re) / Real.log 2)
      (𝓝 0) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, sub_zero, zero_div] using ((hEntropy.sub hConst).sub
      (identity_logContribution_tendsto hB.1)).div_const (Real.log 2)
  have ht := (regularizedObjectiveBits_tendsto_of_support hA hB hs).add hCorrection
  simpa only [sub_self, sub_zero, zero_div, add_zero, simultaneousShift_eq A B hA.1] using ht

theorem identityRegularization_relativeEntropy_tendsto {A B : Mat I}
    (hA : IsDensity A) (hB : IsDensity B) (hs : HasSupportIn A B) {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun δ : ℝ => finiteRelativeEntropyBits (identityRegularizedMatrix A c δ)
      (identityRegularizedMatrix B c δ)) (𝓝[>] 0) (𝓝 (finiteRelativeEntropyBits A B)) := by
  by_cases hc0 : c = 0
  · simpa only [hc0, identityRegularizedMatrix, mul_zero, zero_mul, add_zero,
      inv_one, zero_smul, one_smul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => finiteRelativeEntropyBits A B)
        (𝓝[>] (0 : ℝ)) (𝓝 (finiteRelativeEntropyBits A B)))
  have hcPos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hId : Tendsto (fun δ : ℝ => δ) (𝓝 0) (𝓝 (0 : ℝ)) := tendsto_id
  have hOne : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 0) (𝓝 (1 : ℝ)) := tendsto_const_nhds
  have hScale : Tendsto (fun δ : ℝ => (1 + δ * c * (Fintype.card I : ℝ))⁻¹)
      (𝓝[>] 0) (𝓝 1) := by
    have hDen : Tendsto (fun δ : ℝ => 1 + δ * c * (Fintype.card I : ℝ)) (𝓝 0) (𝓝 1) := by
      simpa using hOne.add ((hId.mul_const c).mul_const (Fintype.card I : ℝ))
    simpa using (hDen.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).mono_left nhdsWithin_le_nhds
  have hDelta : Tendsto (fun δ : ℝ => δ * c) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa using (hId.mul_const c).mono_left nhdsWithin_le_nhds
  have hUnscaled := (simultaneousShift_tendsto hA.1 hB.1 hs).comp hDelta
  have hEq : (fun δ : ℝ => finiteRelativeEntropyBits (identityRegularizedMatrix A c δ)
      (identityRegularizedMatrix B c δ)) =ᶠ[𝓝[>] 0]
      fun δ => (1 + δ * c * (Fintype.card I : ℝ))⁻¹ *
        finiteRelativeEntropyBits (A + (δ * c) • (1 : Mat I)) (B + (δ * c) • (1 : Mat I)) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hε : 0 < δ * c := mul_pos hδ hcPos
    have hDen : 0 < 1 + δ * c * (Fintype.card I : ℝ) := by positivity
    have hInv : 0 < (1 + δ * c * (Fintype.card I : ℝ))⁻¹ := inv_pos.mpr hDen
    have hAsh : (A + (δ * c) • (1 : Mat I)).PosSemidef := hA.1.add (Matrix.PosSemidef.one.smul hε.le)
    have hBsh := regularizedReference_posDef hB.1 hε
    simpa only [identityRegularizedMatrix, div_self hInv.ne', Real.log_one,
      mul_zero, zero_div, zero_mul, add_zero] using finiteRelativeEntropyBits_smul hAsh hBsh hInv.le hInv
  have ht := hScale.mul hUnscaled
  have hFinal : Tendsto (fun δ : ℝ => (1 + δ * c * (Fintype.card I : ℝ))⁻¹ *
      finiteRelativeEntropyBits (A + (δ * c) • (1 : Mat I)) (B + (δ * c) • (1 : Mat I)))
      (𝓝[>] 0) (𝓝 (finiteRelativeEntropyBits A B)) := by
    simpa only [Function.comp_apply, one_mul] using ht
  exact hFinal.congr' hEq.symm

theorem identityRegularization_relativeEntropy_tendsto_one {A B : Mat I}
    (hA : IsDensity A) (hB : IsDensity B) (hs : HasSupportIn A B) :
    Tendsto (fun δ : ℝ => finiteRelativeEntropyBits (identityRegularizedMatrix A 1 δ)
      (identityRegularizedMatrix B 1 δ)) (𝓝[>] 0) (𝓝 (finiteRelativeEntropyBits A B)) :=
  identityRegularization_relativeEntropy_tendsto hA hB hs zero_le_one

end QuantumProver.QuantumRelativeEntropyRegularization
