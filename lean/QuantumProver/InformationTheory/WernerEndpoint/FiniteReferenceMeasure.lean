import QuantumProver.InformationTheory.WernerEndpoint.ContinuousChannelIntegrability

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Matrix MeasureTheory Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

namespace QuantumProver.WernerEndpoint.FiniteReferenceMeasure

open LocalChannelMoments ContinuousChannelIntegrability

variable {I J O Ω : Type*} [Fintype I] [Fintype J] [Fintype O]
  [DecidableEq I] [DecidableEq J] [DecidableEq O] [MeasurableSpace Ω]

def gramTraceWeight (K : Matrix J I ℂ) : ℝ := (Kᴴ * K).trace.re

def rescaledKraus (K : Matrix J I ℂ) : Matrix J I ℂ :=
  (Real.sqrt (gramTraceWeight K))⁻¹ • K

def referenceMeasure (μ : Measure Ω) (K : Ω → Matrix J I ℂ) : Measure Ω :=
  μ.withDensity (fun ω => ENNReal.ofReal (gramTraceWeight (K ω)))

omit [DecidableEq I] [DecidableEq J] in
theorem gramTraceWeight_nonneg (K : Matrix J I ℂ) : 0 ≤ gramTraceWeight K :=
  (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self K).trace_nonneg).1

omit [DecidableEq J] in
theorem gramTraceWeight_eq_zero_iff (K : Matrix J I ℂ) :
    gramTraceWeight K = 0 ↔ K = 0 := by
  constructor
  · intro hZero
    have hNorm : ‖Kᴴ * K‖ ≤ 0 := by
      have h := QuantumProver.ConditionalEntropy.ProbabilityMixtures.posSemidef_norm_le_trace
        (Kᴴ * K) (Matrix.posSemidef_conjTranspose_mul_self K)
      change ‖Kᴴ * K‖ ≤ gramTraceWeight K at h
      simpa only [hZero] using h
    rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hNorm
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg K]
  · rintro rfl
    simp [gramTraceWeight]

omit [DecidableEq I] [DecidableEq J] in
theorem rescaledKraus_zero_of_weight_zero (K : Matrix J I ℂ)
    (hZero : gramTraceWeight K = 0) : rescaledKraus K = 0 := by
  simp [rescaledKraus, hZero]

omit [DecidableEq I] [DecidableEq J] in
theorem measurable_gramTraceWeight (K : Ω → Matrix J I ℂ) (hK : Measurable K) :
    Measurable (fun ω => gramTraceWeight (K ω)) := by
  have hc : Continuous (gramTraceWeight : Matrix J I ℂ → ℝ) := by
    unfold gramTraceWeight
    fun_prop
  exact hc.measurable.comp hK

omit [DecidableEq J] in
theorem measurable_rescaledKraus (K : Ω → Matrix J I ℂ) (hK : Measurable K) :
    Measurable (fun ω => rescaledKraus (K ω)) :=
  ((measurable_gramTraceWeight K hK).sqrt.inv).smul hK

omit [DecidableEq I] [DecidableEq J] in
private theorem rescaling_coefficient (K : Matrix J I ℂ)
    (hZero : gramTraceWeight K ≠ 0) :
    gramTraceWeight K * ((Real.sqrt (gramTraceWeight K))⁻¹ *
      (Real.sqrt (gramTraceWeight K))⁻¹) = 1 := by
  have hg : 0 ≤ gramTraceWeight K := gramTraceWeight_nonneg K
  have hs : Real.sqrt (gramTraceWeight K) ≠ 0 :=
    (Real.sqrt_pos.mpr (lt_of_le_of_ne hg (Ne.symm hZero))).ne'
  field_simp [hs]
  nlinarith [Real.sq_sqrt hg]

omit [DecidableEq J] in

theorem weighted_rescaledGram (K : Matrix J I ℂ) :
    gramTraceWeight K • ((rescaledKraus K)ᴴ * rescaledKraus K) = Kᴴ * K := by
  by_cases hZero : gramTraceWeight K = 0
  · have hK : K = 0 := (gramTraceWeight_eq_zero_iff K).mp hZero
    simp [hK, gramTraceWeight, rescaledKraus]
  · simp only [rescaledKraus, Matrix.conjTranspose_smul, star_trivial,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, rescaling_coefficient K hZero, one_smul]

theorem weighted_matrixSandwich (K : Matrix J I ℂ) :
    gramTraceWeight K • matrixSandwichCLM (rescaledKraus K) = matrixSandwichCLM K := by
  by_cases hZero : gramTraceWeight K = 0
  · have hK : K = 0 := (gramTraceWeight_eq_zero_iff K).mp hZero
    ext X
    simp [hK, gramTraceWeight, rescaledKraus, matrixSandwichCLM_apply]
  · simp only [rescaledKraus, matrixSandwichCLM_real_smul, smul_smul,
      rescaling_coefficient K hZero, one_smul]

theorem weighted_leftSandwich {a b p : ℕ} (K : Matrix (Fin p) (Fin a) ℂ) :
    gramTraceWeight K • leftSandwichCLM (b := b) (rescaledKraus K) = leftSandwichCLM K := by
  by_cases hZero : gramTraceWeight K = 0
  · have hK : K = 0 := (gramTraceWeight_eq_zero_iff K).mp hZero
    ext X
    simp [hK, gramTraceWeight, rescaledKraus, leftSandwichCLM_apply]
  · simp only [rescaledKraus, leftSandwichCLM, Matrix.smul_kronecker,
      matrixSandwichCLM_real_smul, smul_smul, rescaling_coefficient K hZero, one_smul]

theorem weighted_rightSandwich {a b p : ℕ} (K : Matrix (Fin p) (Fin b) ℂ) :
    gramTraceWeight K • rightSandwichCLM (a := a) (rescaledKraus K) = rightSandwichCLM K := by
  by_cases hZero : gramTraceWeight K = 0
  · have hK : K = 0 := (gramTraceWeight_eq_zero_iff K).mp hZero
    ext X
    simp [hK, gramTraceWeight, rescaledKraus, rightSandwichCLM_apply]
  · simp only [rescaledKraus, rightSandwichCLM, Matrix.kronecker_smul,
      matrixSandwichCLM_real_smul, smul_smul, rescaling_coefficient K hZero, one_smul]

private def realTraceCLM : Matrix I I ℂ →L[ℝ] ℝ :=
  (Complex.reLm.comp (Matrix.traceLinearMap I ℝ ℂ)).toContinuousLinearMap

omit [DecidableEq I] in
private theorem realTraceCLM_apply (X : Matrix I I ℂ) : realTraceCLM X = X.trace.re := rfl

omit [DecidableEq J] in
theorem integrable_gramTraceWeight (μ : Measure Ω) (K : Ω → Matrix J I ℂ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ) :
    Integrable (fun ω => gramTraceWeight (K ω)) μ := by
  simpa only [realTraceCLM_apply, gramTraceWeight] using
    (realTraceCLM (I := I)).integrable_comp hGram

omit [DecidableEq J] in
theorem integral_gramTraceWeight (μ : Measure Ω) (K : Ω → Matrix J I ℂ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1) :
    (∫ ω, gramTraceWeight (K ω) ∂μ) = (Fintype.card I : ℝ) := by
  have h := (realTraceCLM (I := I)).integral_comp_comm hGram
  simpa only [realTraceCLM_apply, gramTraceWeight, hComplete, Matrix.trace_one,
    Complex.natCast_re] using h

omit [DecidableEq J] in
theorem referenceMeasure_univ (μ : Measure Ω) (K : Ω → Matrix J I ℂ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1) :
    referenceMeasure μ K Set.univ = (Fintype.card I : ENNReal) := by
  rw [referenceMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gramTraceWeight μ K hGram)
    (Eventually.of_forall fun ω => gramTraceWeight_nonneg (K ω)),
    integral_gramTraceWeight μ K hGram hComplete]
  simp

omit [DecidableEq J] in
theorem referenceMeasure_isFinite (μ : Measure Ω) (K : Ω → Matrix J I ℂ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1) :
    IsFiniteMeasure (referenceMeasure μ K) :=
  ⟨by rw [referenceMeasure_univ μ K hGram hComplete]; exact ENNReal.natCast_lt_top _⟩

omit [DecidableEq I] [DecidableEq J] in
theorem referenceMeasure_eq_zero_of_isEmpty [IsEmpty I]
    (μ : Measure Ω) (K : Ω → Matrix J I ℂ) : referenceMeasure μ K = 0 := by
  have hK : ∀ ω, K ω = 0 := by
    intro ω
    ext i j
    exact isEmptyElim j
  simp [referenceMeasure, gramTraceWeight, hK]

omit [DecidableEq I] [DecidableEq J] in
theorem aestronglyMeasurable_referenceMeasure {E : Type*} [TopologicalSpace E]
    (μ : Measure Ω) (K : Ω → Matrix J I ℂ) {F : Ω → E}
    (hF : AEStronglyMeasurable F μ) : AEStronglyMeasurable F (referenceMeasure μ K) :=
  hF.mono_ac (withDensity_absolutelyContinuous μ _)

omit [DecidableEq I] [DecidableEq J] in
private theorem integrable_referenceMeasure_iff_scaled {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (K : Ω → Matrix J I ℂ) (hK : Measurable K) (F : Ω → E) :
    Integrable F (referenceMeasure μ K) ↔
      Integrable (fun ω => gramTraceWeight (K ω) • F ω) μ := by
  have hMeas : Measurable (fun ω => ENNReal.ofReal (gramTraceWeight (K ω))) :=
    ENNReal.measurable_ofReal.comp (measurable_gramTraceWeight K hK)
  have h := integrable_withDensity_iff_integrable_smul' (μ := μ) (g := F) hMeas
    (Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)
  simpa only [referenceMeasure, Function.comp_def,
    ENNReal.toReal_ofReal (gramTraceWeight_nonneg _)] using h

omit [DecidableEq I] [DecidableEq J] in
private theorem integral_referenceMeasure_eq_scaled {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (K : Ω → Matrix J I ℂ) (hK : Measurable K) (F : Ω → E) :
    (∫ ω, F ω ∂referenceMeasure μ K) = ∫ ω, gramTraceWeight (K ω) • F ω ∂μ := by
  have hMeas : Measurable (fun ω => ENNReal.ofReal (gramTraceWeight (K ω))) :=
    ENNReal.measurable_ofReal.comp (measurable_gramTraceWeight K hK)
  simpa only [referenceMeasure, Function.comp_def,
    ENNReal.toReal_ofReal (gramTraceWeight_nonneg _)] using
    integral_withDensity_eq_integral_toReal_smul (μ := μ) hMeas
      (Eventually.of_forall fun ω => ENNReal.ofReal_lt_top) F

omit [DecidableEq J] in
theorem integrable_rescaledGram (μ : Measure Ω) (K : Ω → Matrix J I ℂ)
    (hK : Measurable K) (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ) :
    Integrable (fun ω => (rescaledKraus (K ω))ᴴ * rescaledKraus (K ω))
      (referenceMeasure μ K) := by
  rw [integrable_referenceMeasure_iff_scaled μ K hK]
  simpa only [weighted_rescaledGram] using hGram

omit [DecidableEq J] in
theorem integral_rescaledGram (μ : Measure Ω) (K : Ω → Matrix J I ℂ)
    (hK : Measurable K) :
    (∫ ω, (rescaledKraus (K ω))ᴴ * rescaledKraus (K ω) ∂referenceMeasure μ K) =
      ∫ ω, (K ω)ᴴ * K ω ∂μ := by
  rw [integral_referenceMeasure_eq_scaled μ K hK]
  simp only [weighted_rescaledGram]

omit [DecidableEq J] in
theorem rescaledGram_complete (μ : Measure Ω) (K : Ω → Matrix J I ℂ)
    (hK : Measurable K) (hComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1) :
    (∫ ω, (rescaledKraus (K ω))ᴴ * rescaledKraus (K ω) ∂referenceMeasure μ K) = 1 := by
  rw [integral_rescaledGram μ K hK, hComplete]

omit [Fintype O] [DecidableEq O] in
theorem weighted_matrix_moment (K : Matrix J I ℂ)
    (Φ : Matrix J J ℂ →L[ℂ] Matrix O O ℂ) :
    gramTraceWeight K • Φ.comp (matrixSandwichCLM (rescaledKraus K)) =
      Φ.comp (matrixSandwichCLM K) := by
  rw [← ContinuousLinearMap.comp_smul, weighted_matrixSandwich]

omit [Fintype O] [DecidableEq O] in
theorem weighted_left_moment {a b p : ℕ} (K : Matrix (Fin p) (Fin a) ℂ)
    (Φ : JointMatrix p b →L[ℂ] Matrix O O ℂ) :
    gramTraceWeight K • Φ.comp (leftSandwichCLM (rescaledKraus K)) =
      Φ.comp (leftSandwichCLM K) := by
  rw [← ContinuousLinearMap.comp_smul, weighted_leftSandwich]

omit [Fintype O] [DecidableEq O] in
theorem weighted_right_moment {a b p : ℕ} (K : Matrix (Fin p) (Fin b) ℂ)
    (Φ : JointMatrix a p →L[ℂ] Matrix O O ℂ) :
    gramTraceWeight K • Φ.comp (rightSandwichCLM (rescaledKraus K)) =
      Φ.comp (rightSandwichCLM K) := by
  rw [← ContinuousLinearMap.comp_smul, weighted_rightSandwich]

theorem integrable_matrix_moment_rescaled (μ : Measure Ω) (K : Ω → Matrix J I ℂ)
    (Φ : Ω → Matrix J J ℂ →L[ℂ] Matrix O O ℂ) (hK : Measurable K)
    (hMoment : Integrable (fun ω => (Φ ω).comp (matrixSandwichCLM (K ω))) μ) :
    Integrable (fun ω => (Φ ω).comp (matrixSandwichCLM (rescaledKraus (K ω))))
      (referenceMeasure μ K) := by
  rw [integrable_referenceMeasure_iff_scaled μ K hK
    (fun ω => (Φ ω).comp (matrixSandwichCLM (rescaledKraus (K ω))))]
  simpa only [weighted_matrix_moment] using hMoment

theorem integral_matrix_moment_rescaled (μ : Measure Ω) (K : Ω → Matrix J I ℂ)
    (Φ : Ω → Matrix J J ℂ →L[ℂ] Matrix O O ℂ) (hK : Measurable K) :
    (∫ ω, (Φ ω).comp (matrixSandwichCLM (rescaledKraus (K ω))) ∂referenceMeasure μ K) =
      ∫ ω, (Φ ω).comp (matrixSandwichCLM (K ω)) ∂μ := by
  rw [integral_referenceMeasure_eq_scaled μ K hK
    (fun ω => (Φ ω).comp (matrixSandwichCLM (rescaledKraus (K ω))))]
  simp only [weighted_matrix_moment]

theorem integrable_left_moment_rescaled {a b p : ℕ}
    (μ : Measure Ω) (K : Ω → Matrix (Fin p) (Fin a) ℂ)
    (Φ : Ω → JointMatrix p b →L[ℂ] Matrix O O ℂ) (hK : Measurable K)
    (hMoment : Integrable (fun ω => (Φ ω).comp (leftSandwichCLM (K ω))) μ) :
    Integrable (fun ω => (Φ ω).comp (leftSandwichCLM (rescaledKraus (K ω))))
      (referenceMeasure μ K) := by
  rw [integrable_referenceMeasure_iff_scaled μ K hK
    (fun ω => (Φ ω).comp (leftSandwichCLM (rescaledKraus (K ω))))]
  simpa only [weighted_left_moment] using hMoment

theorem integral_left_moment_rescaled {a b p : ℕ}
    (μ : Measure Ω) (K : Ω → Matrix (Fin p) (Fin a) ℂ)
    (Φ : Ω → JointMatrix p b →L[ℂ] Matrix O O ℂ) (hK : Measurable K) :
    (∫ ω, (Φ ω).comp (leftSandwichCLM (rescaledKraus (K ω))) ∂referenceMeasure μ K) =
      ∫ ω, (Φ ω).comp (leftSandwichCLM (K ω)) ∂μ := by
  rw [integral_referenceMeasure_eq_scaled μ K hK
    (fun ω => (Φ ω).comp (leftSandwichCLM (rescaledKraus (K ω))))]
  simp only [weighted_left_moment]

theorem integrable_right_moment_rescaled {a b p : ℕ}
    (μ : Measure Ω) (K : Ω → Matrix (Fin p) (Fin b) ℂ)
    (Φ : Ω → JointMatrix a p →L[ℂ] Matrix O O ℂ) (hK : Measurable K)
    (hMoment : Integrable (fun ω => (Φ ω).comp (rightSandwichCLM (K ω))) μ) :
    Integrable (fun ω => (Φ ω).comp (rightSandwichCLM (rescaledKraus (K ω))))
      (referenceMeasure μ K) := by
  rw [integrable_referenceMeasure_iff_scaled μ K hK
    (fun ω => (Φ ω).comp (rightSandwichCLM (rescaledKraus (K ω))))]
  simpa only [weighted_right_moment] using hMoment

theorem integral_right_moment_rescaled {a b p : ℕ}
    (μ : Measure Ω) (K : Ω → Matrix (Fin p) (Fin b) ℂ)
    (Φ : Ω → JointMatrix a p →L[ℂ] Matrix O O ℂ) (hK : Measurable K) :
    (∫ ω, (Φ ω).comp (rightSandwichCLM (rescaledKraus (K ω))) ∂referenceMeasure μ K) =
      ∫ ω, (Φ ω).comp (rightSandwichCLM (K ω)) ∂μ := by
  rw [integral_referenceMeasure_eq_scaled μ K hK
    (fun ω => (Φ ω).comp (rightSandwichCLM (rescaledKraus (K ω))))]
  simp only [weighted_right_moment]

end QuantumProver.WernerEndpoint.FiniteReferenceMeasure
