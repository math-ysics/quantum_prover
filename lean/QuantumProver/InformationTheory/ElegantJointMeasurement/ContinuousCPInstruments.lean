import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.IConcurrence
import QuantumProver.InformationTheory.ElegantJointMeasurement.ContinuousInstrumentQuadrature

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
open MeasureTheory Set

namespace QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments

noncomputable section

set_option maxHeartbeats 800000

variable {Ω I O J : Type*} [MeasurableSpace Ω]
variable [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def CoordinateMeasurable
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) : Prop :=
  ∀ i j b c, Measurable (fun a => Φ a (Matrix.single i j 1) b c)

def MatrixTraceComplete (μ : Measure Ω)
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) : Prop :=
  ∀ X, (∫ a, (Φ a X).trace ∂μ) = X.trace

def canonicalKraus (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (a : Ω) (q : I × O) : Matrix O I ℂ := QuantumProver.ElegantJointMeasurement.CP.krausOperator (Φ a) q

def canonicalGram (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (a : Ω) : Matrix I I ℂ :=
  ∑ q, (canonicalKraus Φ a q)ᴴ * canonicalKraus Φ a q

omit [Fintype I] [Fintype O] [DecidableEq O] in
theorem measurable_choi
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) (hΦ : CoordinateMeasurable Φ) :
    Measurable (fun a => QuantumProver.ElegantJointMeasurement.CP.choi (Φ a)) := by
  exact Measurable.of_eval fun i => Measurable.of_eval fun j => hΦ i.1 j.1 i.2 j.2

theorem measurable_choiFactor
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) (hΦ : CoordinateMeasurable Φ) :
    Measurable (fun a => QuantumProver.ElegantJointMeasurement.CP.choiFactor (Φ a)) :=
  CFC.measurable_sqrt.comp (measurable_choi Φ hΦ)

theorem measurable_canonicalKraus
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : CoordinateMeasurable Φ) (q : I × O) :
    Measurable (fun a => canonicalKraus Φ a q) := by
  have h := measurable_choiFactor Φ hΦ
  exact Measurable.of_eval fun b => Measurable.of_eval fun i =>
    (measurable_pi_apply q).comp ((measurable_pi_apply (i, b)).comp h)

theorem stronglyMeasurable_canonicalKraus
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : CoordinateMeasurable Φ) (q : I × O) :
    StronglyMeasurable (fun a => canonicalKraus Φ a q) :=
  (measurable_canonicalKraus Φ hΦ q).stronglyMeasurable

omit [Fintype I] [DecidableEq I] [DecidableEq O] in
private theorem measurable_actual_gram (K : Ω → Matrix O I ℂ) (hK : Measurable K) :
    Measurable (fun a => (K a)ᴴ * K a) := by
  have he : ∀ b i, Measurable (fun a => K a b i) := fun b i =>
    (measurable_pi_apply i).comp ((measurable_pi_apply b).comp hK)
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  fun_prop

theorem measurable_canonicalGram
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) (hΦ : CoordinateMeasurable Φ) :
    Measurable (canonicalGram Φ) := by
  have hq : ∀ q, Measurable (fun a => (canonicalKraus Φ a q)ᴴ * canonicalKraus Φ a q) :=
    fun q => measurable_actual_gram _ (measurable_canonicalKraus Φ hΦ q)
  exact Finset.measurable_sum Finset.univ (fun q _ => hq q)

omit [MeasurableSpace Ω] in
theorem canonicalGram_posSemidef
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) (a : Ω) :
    (canonicalGram Φ a).PosSemidef :=
  Matrix.posSemidef_sum _ fun q _ =>
    Matrix.posSemidef_conjTranspose_mul_self (canonicalKraus Φ a q)

omit [MeasurableSpace Ω] in

theorem canonicalKraus_matrix_action
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a)) (a : Ω) (X : Matrix I I ℂ) :
    Φ a X = ∑ q, canonicalKraus Φ a q * X * (canonicalKraus Φ a q)ᴴ :=
  QuantumProver.ElegantJointMeasurement.CP.completelyPositive_apply_eq_sum _ (hCP a) X

omit [MeasurableSpace Ω] in
theorem matrix_trace_eq_canonicalGram
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a)) (a : Ω) (X : Matrix I I ℂ) :
    (Φ a X).trace = (canonicalGram Φ a * X).trace := by
  rw [QuantumProver.ElegantJointMeasurement.CP.completelyPositive_eq_krausMap _ (hCP a), QuantumProver.ElegantJointMeasurement.CP.krausMap_trace]
  rfl

omit [MeasurableSpace Ω] in
theorem canonicalGram_trace
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a)) (a : Ω) :
    (canonicalGram Φ a).trace = (Φ a 1).trace := by
  simpa only [Matrix.mul_one] using (matrix_trace_eq_canonicalGram Φ hCP a 1).symm

theorem posSemidef_norm_le_trace {α : Type*} [Fintype α] [DecidableEq α]
    (R : Matrix α α ℂ) (hR : R.PosSemidef) :
    ‖R‖ ≤ R.trace.re := by
  have hnorm : ‖R‖ = ‖fun i => (hR.isHermitian.eigenvalues i : ℂ)‖ := by
    conv_lhs => rw [hR.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
    rfl
  have ht : R.trace.re = ∑ i, hR.isHermitian.eigenvalues i := by
    rw [hR.isHermitian.trace_eq_sum_eigenvalues]
    simp
  rw [hnorm, ht]
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg
    (fun i _ => hR.eigenvalues_nonneg i))).mpr
  intro i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hR.eigenvalues_nonneg i)]
  exact Finset.single_le_sum (fun k _ => hR.eigenvalues_nonneg k) (Finset.mem_univ i)

variable [Nonempty I]

omit [DecidableEq O] in

theorem integrable_matrix_trace_identity
    (μ : Measure Ω) (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (htrace : MatrixTraceComplete μ Φ) :
    Integrable (fun a => (Φ a 1).trace) μ := by
  by_contra h
  have ht := htrace 1
  rw [integral_undef h] at ht
  have hn : (1 : Matrix I I ℂ).trace ≠ 0 := by simp
  exact hn ht.symm

theorem integrable_canonicalGram
    (μ : Measure Ω) (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a))
    (htrace : MatrixTraceComplete μ Φ) : Integrable (canonicalGram Φ) μ := by
  have hm : Integrable (fun a => (Φ a 1).trace.re) μ := by
    simpa only [Complex.reCLM_apply] using
      Complex.reCLM.integrable_comp (integrable_matrix_trace_identity μ Φ htrace)
  apply hm.mono' (measurable_canonicalGram Φ hΦ).stronglyMeasurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun a => by
    simpa only [canonicalGram_trace Φ hCP a] using
      posSemidef_norm_le_trace _ (canonicalGram_posSemidef Φ a)

private def tracePairing (X : Matrix I I ℂ) : Matrix I I ℂ →L[ℂ] ℂ :=
  ({ toFun := fun G => (G * X).trace
     map_add' := by intro A B; simp [Matrix.add_mul, Matrix.trace_add]
     map_smul' := by intro z A; simp [Matrix.trace_smul] } :
    Matrix I I ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

theorem integral_canonicalGram_eq_one
    (μ : Measure Ω) (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a))
    (htrace : MatrixTraceComplete μ Φ) : (∫ a, canonicalGram Φ a ∂μ) = 1 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  have hcomm := (tracePairing X).integral_comp_comm (integrable_canonicalGram μ Φ hΦ hCP htrace)
  change (∫ a, (canonicalGram Φ a * X).trace ∂μ) =
    ((∫ a, canonicalGram Φ a ∂μ) * X).trace at hcomm
  have heq : (∫ a, (canonicalGram Φ a * X).trace ∂μ) = (∫ a, (Φ a X).trace ∂μ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun a =>
      (matrix_trace_eq_canonicalGram Φ hCP a X).symm)
  simpa only [Matrix.one_mul] using hcomm.symm.trans (heq.trans (htrace X))

theorem integrable_canonicalKraus_gram
    (μ : Measure Ω) (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a))
    (htrace : MatrixTraceComplete μ Φ) (q : I × O) :
    Integrable (fun a => (canonicalKraus Φ a q)ᴴ * canonicalKraus Φ a q) μ := by
  have hm : Integrable (fun a => (Φ a 1).trace.re) μ := by
    simpa only [Complex.reCLM_apply] using
      Complex.reCLM.integrable_comp (integrable_matrix_trace_identity μ Φ htrace)
  have hq := measurable_actual_gram _ (measurable_canonicalKraus Φ hΦ q)
  apply hm.mono' hq.stronglyMeasurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun a => by
    have hpos := Matrix.posSemidef_conjTranspose_mul_self (canonicalKraus Φ a q)
    have hle : (canonicalKraus Φ a q)ᴴ * canonicalKraus Φ a q ≤ canonicalGram Φ a :=
      Finset.single_le_sum (fun r _ =>
        (Matrix.posSemidef_conjTranspose_mul_self (canonicalKraus Φ a r)).nonneg)
        (Finset.mem_univ q)
    have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle hpos.nonneg
    exact hn.trans (by simpa only [canonicalGram_trace Φ hCP a] using
      posSemidef_norm_le_trace _ (canonicalGram_posSemidef Φ a))

omit [MeasurableSpace Ω] [Nonempty I] [DecidableEq O] in

theorem choi_trace (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    (QuantumProver.ElegantJointMeasurement.CP.choi Φ).trace = (Φ 1).trace := by
  have h1 : (1 : Matrix I I ℂ) = ∑ i, Matrix.single i i (1 : ℂ) :=
    Matrix.sum_single_one.symm
  rw [h1, map_sum, Matrix.trace_sum]
  simp only [Matrix.trace, Matrix.diag_apply, QuantumProver.ElegantJointMeasurement.CP.choi, Fintype.sum_prod_type]

theorem integrable_choi
    (μ : Measure Ω) (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a))
    (htrace : MatrixTraceComplete μ Φ) : Integrable (fun a => QuantumProver.ElegantJointMeasurement.CP.choi (Φ a)) μ := by
  have hm : Integrable (fun a => (Φ a 1).trace.re) μ := by
    simpa only [Complex.reCLM_apply] using
      Complex.reCLM.integrable_comp (integrable_matrix_trace_identity μ Φ htrace)
  apply hm.mono' (measurable_choi Φ hΦ).stronglyMeasurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun a => by
    simpa only [choi_trace] using posSemidef_norm_le_trace _ (QuantumProver.ElegantJointMeasurement.CP.choi_posSemidef _ (hCP a))

private def choiReadout (X : Matrix I I ℂ) :
    Matrix (I × O) (I × O) ℂ →L[ℂ] Matrix O O ℂ :=
  ((∑ i, ∑ j, X i j •
    ({ toFun := fun C => fun b c => C (i, b) (j, c)
       map_add' := by intros; rfl
       map_smul' := by intros; rfl } :
      Matrix (I × O) (I × O) ℂ →ₗ[ℂ] Matrix O O ℂ)) :
    Matrix (I × O) (I × O) ℂ →ₗ[ℂ] Matrix O O ℂ).toContinuousLinearMap

omit [MeasurableSpace Ω] [Nonempty I] [DecidableEq O] in
private theorem matrix_eq_choiReadout
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (X : Matrix I I ℂ) :
    Φ X = choiReadout X (QuantumProver.ElegantJointMeasurement.CP.choi Φ) := by
  simp only [choiReadout, LinearMap.coe_toContinuousLinearMap', LinearMap.sum_apply,
    LinearMap.smul_apply]
  change Φ X = ∑ i, ∑ j, X i j • (fun b c => QuantumProver.ElegantJointMeasurement.CP.choi Φ (i, b) (j, c))
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) := by
    simp [Matrix.smul_single]
  rw [hs, map_smul]
  rfl

theorem integrable_matrix_action
    (μ : Measure Ω) (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a))
    (htrace : MatrixTraceComplete μ Φ) (X : Matrix I I ℂ) :
    Integrable (fun a => Φ a X) μ := by
  have h := (choiReadout X).integrable_comp (integrable_choi μ Φ hΦ hCP htrace)
  simpa only [← matrix_eq_choiReadout] using h

variable [DecidableEq J]

def canonicalReportedGram
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) (report : Ω → J)
    (a : Ω) (j : J) : Matrix I I ℂ :=
  if report a = j then canonicalGram Φ a else 0

omit [MeasurableSpace Ω] [Nonempty I] in
theorem canonicalReportedGram_eq_sum
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) (report : Ω → J) (a : Ω) (j : J) :
    canonicalReportedGram Φ report a j =
      ∑ q, if report a = j then (canonicalKraus Φ a q)ᴴ * canonicalKraus Φ a q else 0 := by
  by_cases h : report a = j <;> simp [canonicalReportedGram, canonicalGram, h]

variable [MeasurableSpace J] [MeasurableSingletonClass J]

theorem integrable_canonicalReportedGram
    (μ : Measure Ω) (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a))
    (htrace : MatrixTraceComplete μ Φ) (report : Ω → J) (hr : Measurable report) (j : J) :
    Integrable (fun a => canonicalReportedGram Φ report a j) μ := by
  have hs : MeasurableSet {a | report a = j} := (measurableSet_singleton j).preimage hr
  have h : Integrable (fun a => {a | report a = j}.indicator (canonicalGram Φ) a) μ :=
    (integrable_canonicalGram μ Φ hΦ hCP htrace).indicator hs
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, canonicalReportedGram] using h

theorem matrix_reported_trace_integral
    (μ : Measure Ω) (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a))
    (htrace : MatrixTraceComplete μ Φ) (report : Ω → J) (hr : Measurable report)
    (j : J) (X : Matrix I I ℂ) :
    (∫ a, if report a = j then (Φ a X).trace else 0 ∂μ) =
      ((∫ a, canonicalReportedGram Φ report a j ∂μ) * X).trace := by
  have hcomm := (tracePairing X).integral_comp_comm
    (integrable_canonicalReportedGram μ Φ hΦ hCP htrace report hr j)
  change (∫ a, (canonicalReportedGram Φ report a j * X).trace ∂μ) =
    ((∫ a, canonicalReportedGram Φ report a j ∂μ) * X).trace at hcomm
  rw [← hcomm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    by_cases h : report a = j
    · simp only [h, ite_true, canonicalReportedGram, matrix_trace_eq_canonicalGram Φ hCP a X]
    · simp [canonicalReportedGram, h]

theorem integrable_matrix_reported_action
    (μ : Measure Ω) (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a))
    (htrace : MatrixTraceComplete μ Φ) (report : Ω → J) (hr : Measurable report)
    (j : J) (X : Matrix I I ℂ) :
    Integrable (fun a => if report a = j then Φ a X else 0) μ := by
  have hs : MeasurableSet {a | report a = j} := (measurableSet_singleton j).preimage hr
  have h : Integrable (fun a => {a | report a = j}.indicator (fun a => Φ a X) a) μ :=
    (integrable_matrix_action μ Φ hΦ hCP htrace X).indicator hs
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using h

omit [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty I] in
theorem matrix_reported_action_integral
    (μ : Measure Ω) (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a)) (report : Ω → J)
    (j : J) (X : Matrix I I ℂ) :
    (∫ a, if report a = j then Φ a X else 0 ∂μ) =
      ∫ a, ∑ q, if report a = j then
        canonicalKraus Φ a q * X * (canonicalKraus Φ a q)ᴴ else 0 ∂μ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    by_cases h : report a = j <;> simp [h, ← canonicalKraus_matrix_action Φ hCP a X]

theorem integrable_canonicalKraus_gram_family
    (μ : Measure Ω) (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a))
    (htrace : MatrixTraceComplete μ Φ) :
    Integrable (fun a q => (canonicalKraus Φ a q)ᴴ * canonicalKraus Φ a q) μ :=
  integrable_pi_iff.mpr (fun q => integrable_canonicalKraus_gram μ Φ hΦ hCP htrace q)

variable [Fintype J]

theorem integrable_joint_reported_gram
    (μ : Measure Ω) (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a))
    (htrace : MatrixTraceComplete μ Φ) (report : Ω → J) (hr : Measurable report) :
    Integrable (fun a => (canonicalGram Φ a, canonicalReportedGram Φ report a)) μ :=
  (integrable_canonicalGram μ Φ hΦ hCP htrace).prodMk
    (integrable_pi_iff.mpr (fun j => integrable_canonicalReportedGram μ Φ hΦ hCP htrace report hr j))

section MatrixQuadrature

def sampledKraus (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) {N : ℕ}
    (w : Fin N → ℝ) (point : Fin N → Ω) (z : Fin N × (I × O)) : Matrix O I ℂ :=
  QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus (w z.1) (canonicalKraus Φ (point z.1) z.2)

omit [MeasurableSpace Ω] [Nonempty I] in
theorem sampledKraus_total_gram
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) {N : ℕ}
    (w : Fin N → ℝ) (point : Fin N → Ω) (hw : ∀ i, 0 ≤ w i) :
    (∑ z, (sampledKraus Φ w point z)ᴴ * sampledKraus Φ w point z) =
      ∑ i, w i • canonicalGram Φ (point i) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [sampledKraus, QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus_gram _ _ (hw i)]
  rw [← Finset.smul_sum]
  rfl

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem exists_matrix_joint_quadrature_on
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a))
    (htrace : MatrixTraceComplete μ Φ) (f : Ω → V) (hf : Integrable f μ)
    (s : Set Ω) (hs : ∀ᵐ a ∂μ, a ∈ s) :
    ∃ (n : ℕ → ℕ) (w : (a : ℕ) → Fin (n a) → ℝ)
      (point : (a : ℕ) → Fin (n a) → Ω),
      (∀ a i, 0 ≤ w a i) ∧ (∀ a, (∑ i, w a i) = μ.real univ) ∧
      (∀ a i, point a i ∈ s) ∧
      Filter.Tendsto (fun a => ∑ z,
        (sampledKraus Φ (w a) (point a) z)ᴴ * sampledKraus Φ (w a) (point a) z)
        Filter.atTop (nhds 1) ∧
      Filter.Tendsto (fun a => ∑ i, w a i • f (point a i))
        Filter.atTop (nhds (∫ a, f a ∂μ)) := by
  have hjoint := (integrable_canonicalGram μ Φ hΦ hCP htrace).prodMk hf
  obtain ⟨n, w, point, hw, hmass, hpoint, hlim⟩ :=
    QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.exists_integral_actual_point_quadrature_on
      μ (fun a => (canonicalGram Φ a, f a)) hjoint s hs
  refine ⟨n, w, point, hw, hmass, hpoint, ?_, ?_⟩
  · have h : Filter.Tendsto (fun a => ∑ i, w a i • canonicalGram Φ (point a i))
        Filter.atTop (nhds (1 : Matrix I I ℂ)) := by
      have hp := (continuous_fst.tendsto _).comp hlim
      simpa only [Function.comp_def, Prod.fst_sum, Prod.smul_fst, fst_integral hjoint,
        integral_canonicalGram_eq_one μ Φ hΦ hCP htrace] using hp
    exact h.congr' (Filter.Eventually.of_forall fun a =>
      (sampledKraus_total_gram Φ (w a) (point a) (hw a)).symm)
  · have hp := (continuous_snd.tendsto _).comp hlim
    simpa only [Function.comp_def, Prod.snd_sum, Prod.smul_snd, snd_integral hjoint] using hp

omit [MeasurableSpace Ω] [MeasurableSpace J] [MeasurableSingletonClass J]
  [Nonempty I] [Fintype J] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] in
theorem sampledKraus_grouped_gram
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) {N : ℕ}
    (w : Fin N → ℝ) (point : Fin N → Ω) (hw : ∀ i, 0 ≤ w i)
    (report : Ω → J) (j : J) :
    (∑ z, if report (point z.1) = j then
      (sampledKraus Φ w point z)ᴴ * sampledKraus Φ w point z else 0) =
      ∑ i, w i • canonicalReportedGram Φ report (point i) j := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : report (point i) = j
  · simp only [h, ite_true, canonicalReportedGram]
    simp only [sampledKraus, QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus_gram _ _ (hw i)]
    rw [← Finset.smul_sum]
    rfl
  · simp [canonicalReportedGram, h]

theorem exists_matrix_reported_quadrature_on
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Φ : Ω → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : CoordinateMeasurable Φ) (hCP : ∀ a, QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (Φ a))
    (htrace : MatrixTraceComplete μ Φ) (report : Ω → J) (hr : Measurable report)
    (s : Set Ω) (hs : ∀ᵐ a ∂μ, a ∈ s) :
    ∃ (n : ℕ → ℕ) (w : (a : ℕ) → Fin (n a) → ℝ)
      (point : (a : ℕ) → Fin (n a) → Ω),
      (∀ a i, 0 ≤ w a i) ∧ (∀ a, (∑ i, w a i) = μ.real univ) ∧
      (∀ a i, point a i ∈ s) ∧
      Filter.Tendsto (fun a => ∑ z,
        (sampledKraus Φ (w a) (point a) z)ᴴ * sampledKraus Φ (w a) (point a) z)
        Filter.atTop (nhds 1) ∧
      Filter.Tendsto (fun a j => ∑ z,
        if report (point a z.1) = j then
          (sampledKraus Φ (w a) (point a) z)ᴴ * sampledKraus Φ (w a) (point a) z else 0)
        Filter.atTop (nhds (fun j => ∫ a, canonicalReportedGram Φ report a j ∂μ)) := by
  have hreported := integrable_pi_iff.mpr
    (fun j => integrable_canonicalReportedGram μ Φ hΦ hCP htrace report hr j)
  obtain ⟨n, w, point, hw, hmass, hpoint, hGram, hF⟩ :=
    exists_matrix_joint_quadrature_on μ Φ hΦ hCP htrace
      (canonicalReportedGram Φ report) hreported s hs
  refine ⟨n, w, point, hw, hmass, hpoint, hGram, ?_⟩
  have hvalues (a : ℕ) :
      (fun j => ∑ z, if report (point a z.1) = j then
        (sampledKraus Φ (w a) (point a) z)ᴴ * sampledKraus Φ (w a) (point a) z else 0) =
      ∑ i, w a i • canonicalReportedGram Φ report (point a i) := by
    funext j
    simpa only [Finset.sum_apply, Pi.smul_apply] using
      sampledKraus_grouped_gram Φ (w a) (point a) (hw a) report j
  have hintegral : (∫ a, canonicalReportedGram Φ report a ∂μ) =
      (fun j => ∫ a, canonicalReportedGram Φ report a j ∂μ) := by
    funext j
    exact eval_integral
      (fun j => integrable_canonicalReportedGram μ Φ hΦ hCP htrace report hr j) j
  have hF' := hF.congr' (Filter.Eventually.of_forall fun a => (hvalues a).symm)
  simpa only [hintegral] using hF'

end MatrixQuadrature

end

end QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments
