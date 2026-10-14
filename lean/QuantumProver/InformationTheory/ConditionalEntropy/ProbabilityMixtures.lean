import QuantumProver.InformationTheory.ConditionalEntropy.MixtureEntropy
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace QuantumProver.ConditionalEntropy.ProbabilityMixtures

variable {I A B Ω : Type*} [Fintype I] [Fintype A] [Fintype B]
  [DecidableEq I] [DecidableEq A] [DecidableEq B] [MeasurableSpace Ω]

theorem isClosed_isDensity : IsClosed {R : Matrix I I ℂ | IsDensity R} :=
  Matrix.posSemidef_is_closed.inter
    (isClosed_eq continuous_id.matrix_trace continuous_const)

theorem posSemidef_norm_le_trace (R : Matrix I I ℂ) (hR : R.PosSemidef) :
    ‖R‖ ≤ R.trace.re := by
  have ht : R.trace.re = ∑ i, hR.isHermitian.eigenvalues i := by
    rw [hR.isHermitian.trace_eq_sum_eigenvalues]
    simp
  have hnonneg : 0 ≤ R.trace.re := by
    rw [ht]
    exact Finset.sum_nonneg (fun i _ => hR.eigenvalues_nonneg i)
  conv_lhs => rw [hR.isHermitian.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
  intro i
  simp only [Function.comp_apply, RCLike.norm_ofReal,
    abs_of_nonneg (hR.eigenvalues_nonneg i)]
  rw [ht]
  exact Finset.single_le_sum (fun j _ => hR.eigenvalues_nonneg j) (Finset.mem_univ i)

theorem isDensity_norm_le_one {R : Matrix I I ℂ} (hR : IsDensity R) : ‖R‖ ≤ 1 := by
  simpa only [hR.2, Complex.one_re] using posSemidef_norm_le_trace R hR.1

theorem integrable_densityFamily (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : Ω → Matrix I I ℂ) (hMeas : AEStronglyMeasurable R μ)
    (hR : ∀ᵐ x ∂μ, IsDensity (R x)) : Integrable R μ :=
  (integrable_const (1 : ℝ)).mono' hMeas (hR.mono fun _ hx => isDensity_norm_le_one hx)

theorem isDensity_spectrum_subset {R : Matrix I I ℂ} (hR : IsDensity R) :
    spectrum ℝ R ⊆ Set.Icc (0 : ℝ) 1 := by
  have hsum : ∑ i, hR.1.isHermitian.eigenvalues i = 1 := by
    rw [← ConditionalRange.trace_re_eq_sum_eigenvalues hR.1.isHermitian, hR.2]
    rfl
  rw [hR.1.isHermitian.spectrum_real_eq_range_eigenvalues]
  rintro x ⟨i, rfl⟩
  refine ⟨hR.1.eigenvalues_nonneg i, ?_⟩
  rw [← hsum]
  exact Finset.single_le_sum (fun j _ => hR.1.eigenvalues_nonneg j) (Finset.mem_univ i)

theorem entropyBits_continuousOn_density :
    ContinuousOn (entropyBits : Matrix I I ℂ → ℝ) {R | IsDensity R} := by
  have hCFC : ContinuousOn (cfc (fun x : ℝ => x * Real.log x) : Matrix I I ℂ → Matrix I I ℂ)
      {R | IsSelfAdjoint R ∧ spectrum ℝ R ⊆ Set.Icc (0 : ℝ) 1} :=
    continuousOn_cfc (Matrix I I ℂ) isCompact_Icc _ Real.continuous_mul_log.continuousOn
  have hRestricted := hCFC.mono (fun R hR =>
    ⟨hR.1.isHermitian.isSelfAdjoint, isDensity_spectrum_subset hR⟩)
  have hTrace : Continuous (fun R : Matrix I I ℂ => -R.trace.re / Real.log 2) := by
    fun_prop
  exact hTrace.comp_continuousOn hRestricted

theorem aestronglyMeasurable_comp_of_density (μ : Measure Ω)
    (R : Ω → Matrix I I ℂ) (hMeas : AEStronglyMeasurable R μ)
    (hR : ∀ᵐ x ∂μ, IsDensity (R x)) (f : Matrix I I ℂ → ℝ)
    (hf : ContinuousOn f {R | IsDensity R}) :
    AEStronglyMeasurable (fun x => f (R x)) μ := by
  classical
  let s : Set (Matrix I I ℂ) := {R | IsDensity R}
  let F : Matrix I I ℂ → ℝ := s.piecewise f (fun _ => 0)
  have hF : Measurable F :=
    hf.measurable_piecewise continuous_const.continuousOn isClosed_isDensity.measurableSet
  have hComp : AEStronglyMeasurable (fun x => F (R x)) μ :=
    (hF.comp_aemeasurable hMeas.aemeasurable).aestronglyMeasurable
  apply hComp.congr
  filter_upwards [hR] with x hx
  exact Set.piecewise_eq_of_mem s f (fun _ => 0) hx

theorem integrable_entropyBits (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : Ω → Matrix I I ℂ) (hMeas : AEStronglyMeasurable R μ)
    (hR : ∀ᵐ x ∂μ, IsDensity (R x)) :
    Integrable (fun x => entropyBits (R x)) μ := by
  apply (integrable_const (logDimA I)).mono'
    (aestronglyMeasurable_comp_of_density μ R hMeas hR entropyBits
      entropyBits_continuousOn_density)
  filter_upwards [hR] with x hx
  have hBounds := ConditionalRange.entropyBits_bounds hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg hBounds.1, logDimA] using hBounds.2

theorem integral_isDensity (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Matrix I I ℂ) (hMeas : AEStronglyMeasurable R μ)
    (hR : ∀ᵐ x ∂μ, IsDensity (R x)) : IsDensity (∫ x, R x ∂μ) :=
  convex_isDensity.integral_mem isClosed_isDensity hR (integrable_densityFamily μ R hMeas hR)

set_option maxHeartbeats 800000 in

theorem entropyBits_integral_lower (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Matrix I I ℂ) (hMeas : AEStronglyMeasurable R μ)
    (hR : ∀ᵐ x ∂μ, IsDensity (R x)) :
    (∫ x, entropyBits (R x) ∂μ) ≤ entropyBits (∫ x, R x ∂μ) := by
  refine ConcaveOn.le_map_integral (E := Matrix I I ℂ) (μ := μ)
    (s := {Q : Matrix I I ℂ | IsDensity Q}) (f := R) (g := entropyBits)
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact entropyBits_concaveOn
  · exact entropyBits_continuousOn_density
  · exact isClosed_isDensity
  · exact hR
  · exact integrable_densityFamily μ R hMeas hR
  · exact integrable_entropyBits μ R hMeas hR

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem partialTraceLeft_continuous :
    Continuous (QuantumProver.QuantumEntropy.partialTrace_left :
      Matrix (A × B) (A × B) ℂ → Matrix B B ℂ) := by
  apply continuous_pi
  intro b
  apply continuous_pi
  intro b'
  simp only [QuantumProver.QuantumEntropy.partialTrace_left]
  fun_prop

theorem conditionalEntropy_continuousOn_density :
    ContinuousOn (conditionalEntropyBits : Matrix (A × B) (A × B) ℂ → ℝ)
      {R | IsDensity R} := by
  have hMarg : ContinuousOn
      (fun R : Matrix (A × B) (A × B) ℂ => entropyBits (QuantumProver.QuantumEntropy.partialTrace_left R))
      {R | IsDensity R} :=
    entropyBits_continuousOn_density.comp partialTraceLeft_continuous.continuousOn
      (fun _ hR => QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR)
  exact entropyBits_continuousOn_density.sub hMarg

theorem integrable_conditionalEntropy (μ : Measure Ω) [IsFiniteMeasure μ]
    (R : Ω → Matrix (A × B) (A × B) ℂ) (hMeas : AEStronglyMeasurable R μ)
    (hR : ∀ᵐ x ∂μ, IsDensity (R x)) :
    Integrable (fun x => conditionalEntropyBits (R x)) μ := by
  apply (integrable_const (logDimA A)).mono'
    (aestronglyMeasurable_comp_of_density μ R hMeas hR conditionalEntropyBits
      conditionalEntropy_continuousOn_density)
  filter_upwards [hR] with x hx
  simpa only [Real.norm_eq_abs] using abs_conditionalEntropy_le_logDim hx

set_option maxHeartbeats 800000 in

theorem conditionalEntropy_integral_lower (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Matrix (A × B) (A × B) ℂ) (hMeas : AEStronglyMeasurable R μ)
    (hR : ∀ᵐ x ∂μ, IsDensity (R x)) :
    (∫ x, conditionalEntropyBits (R x) ∂μ) ≤ conditionalEntropyBits (∫ x, R x ∂μ) := by
  refine ConcaveOn.le_map_integral (E := Matrix (A × B) (A × B) ℂ) (μ := μ)
    (s := {Q : Matrix (A × B) (A × B) ℂ | IsDensity Q}) (f := R)
    (g := conditionalEntropyBits) ?_ ?_ ?_ ?_ ?_ ?_
  · exact conditionalEntropy_concaveOn
  · exact conditionalEntropy_continuousOn_density
  · exact isClosed_isDensity
  · exact hR
  · exact integrable_densityFamily μ R hMeas hR
  · exact integrable_conditionalEntropy μ R hMeas hR

theorem entropyBits_integral_lower_of_measurable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Matrix I I ℂ) (hMeas : Measurable R)
    (hR : ∀ᵐ x ∂μ, IsDensity (R x)) :
    (∫ x, entropyBits (R x) ∂μ) ≤ entropyBits (∫ x, R x ∂μ) :=
  entropyBits_integral_lower μ R hMeas.aestronglyMeasurable hR

theorem conditionalEntropy_integral_lower_of_measurable
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Matrix (A × B) (A × B) ℂ) (hMeas : Measurable R)
    (hR : ∀ᵐ x ∂μ, IsDensity (R x)) :
    (∫ x, conditionalEntropyBits (R x) ∂μ) ≤ conditionalEntropyBits (∫ x, R x ∂μ) :=
  conditionalEntropy_integral_lower μ R hMeas.aestronglyMeasurable hR

end QuantumProver.ConditionalEntropy.ProbabilityMixtures
