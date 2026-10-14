import QuantumProver.InformationTheory.ConditionalEntropy.ProbabilityMixtures
import QuantumProver.LinearAlgebra.LocalInstrumentMarginals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology ENNReal

namespace QuantumProver.ConditionalEntropy.ContinuousLocalInstrument

open QuantumProver.QuantumEntropy
open QuantumProver.LocalInstrumentMarginals

variable {A B O Ω : Type*} [Fintype A] [Fintype B] [Fintype O]
  [DecidableEq A] [DecidableEq B] [DecidableEq O] [MeasurableSpace Ω]

abbrev localBranch (K : Matrix O A ℂ) (R : Matrix (A × B) (A × B) ℂ) := branch K R

abbrev bornWeight (K : Matrix O A ℂ) (R : Matrix (A × B) (A × B) ℂ) :=
  branchProbability K R

def output (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (R : Matrix (A × B) (A × B) ℂ) : Matrix (O × B) (O × B) ℂ :=
  ∫ x, localBranch (K x) R ∂μ

def normalizedBranch (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (R : Matrix (A × B) (A × B) ℂ) (x : Ω) : Matrix (O × B) (O × B) ℂ :=
  if bornWeight (K x) R = 0 then output μ K R
  else (bornWeight (K x) R)⁻¹ • localBranch (K x) R

def normalizedUntouchedMarginal (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (R : Matrix (A × B) (A × B) ℂ) (x : Ω) : Matrix B B ℂ :=
  partialTrace_left (normalizedBranch μ K R x)

def bornDensity (K : Ω → Matrix O A ℂ) (R : Matrix (A × B) (A × B) ℂ) : Ω → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (bornWeight (K x) R)

def bornMeasure (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (R : Matrix (A × B) (A × B) ℂ) : Measure Ω := μ.withDensity (bornDensity K R)

private def realTraceCLM {I : Type*} [Fintype I] [DecidableEq I] :
    Matrix I I ℂ →L[ℝ] ℝ :=
  (Complex.reLm.comp (Matrix.traceLinearMap I ℝ ℂ)).toContinuousLinearMap

def gramToMarginal (R : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ →L[ℂ] Matrix B B ℂ :=
  ({ toFun := fun G b b' => ∑ a', ∑ a, G a' a * R (a,b) (a',b')
     map_add' := by
       intro G H
       ext b b'
       change (∑ a', ∑ a, (G a' a + H a' a) * R (a,b) (a',b')) =
         (∑ a', ∑ a, G a' a * R (a,b) (a',b')) + ∑ a', ∑ a, H a' a * R (a,b) (a',b')
       simp only [add_mul, Finset.sum_add_distrib]
     map_smul' := by
       intro c G
       ext b b'
       change (∑ a', ∑ a, (c * G a' a) * R (a,b) (a',b')) =
         c * ∑ a', ∑ a, G a' a * R (a,b) (a',b')
       simp only [mul_assoc, Finset.mul_sum] } :
    Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ).toContinuousLinearMap

theorem gramToMarginal_gram (K : Matrix O A ℂ) (R : Matrix (A × B) (A × B) ℂ) :
    gramToMarginal R (Kᴴ * K) = partialTrace_left (localBranch K R) := by
  ext b b'
  exact (untouchedMarginal_branch_apply K R b b').symm

omit [Fintype B] [DecidableEq B] in
theorem gramToMarginal_one (R : Matrix (A × B) (A × B) ℂ) :
    gramToMarginal R 1 = partialTrace_left R := by
  ext b b'
  change (∑ a', ∑ a, (1 : Matrix A A ℂ) a' a * R (a,b) (a',b')) =
    ∑ a, R (a,b) (a,b')
  simp [Matrix.one_apply, ite_mul]

private def partialTraceCLM : Matrix (O × B) (O × B) ℂ →L[ℂ] Matrix B B ℂ :=
  ({ toFun := partialTrace_left
     map_add' := by intro X Y; ext b b'; simp [partialTrace_left, Finset.sum_add_distrib]
     map_smul' := by intro c X; ext b b'; simp [partialTrace_left, Finset.mul_sum] } :
    Matrix (O × B) (O × B) ℂ →ₗ[ℂ] Matrix B B ℂ).toContinuousLinearMap

theorem measurable_localBranch (K : Ω → Matrix O A ℂ) (hK : Measurable K)
    (R : Matrix (A × B) (A × B) ℂ) : Measurable (fun x => localBranch (K x) R) := by
  have hc : Continuous (fun L : Matrix O A ℂ => localBranch L R) := by
    apply continuous_pi
    rintro ⟨o,b⟩
    apply continuous_pi
    rintro ⟨o',b'⟩
    change Continuous (fun L : Matrix O A ℂ => branch L R (o,b) (o',b'))
    simp_rw [branch_apply]
    fun_prop
  exact hc.measurable.comp hK

theorem measurable_bornWeight (K : Ω → Matrix O A ℂ) (hK : Measurable K)
    (R : Matrix (A × B) (A × B) ℂ) : Measurable (fun x => bornWeight (K x) R) :=
  realTraceCLM.continuous.measurable.comp (measurable_localBranch K hK R)

theorem measurable_bornDensity (K : Ω → Matrix O A ℂ) (hK : Measurable K)
    (R : Matrix (A × B) (A × B) ℂ) : Measurable (bornDensity K R) :=
  ENNReal.measurable_ofReal.comp (measurable_bornWeight K hK R)

theorem input_nonempty_of_density (R : Matrix (A × B) (A × B) ℂ) (hR : IsDensity R) :
    Nonempty A := by
  classical
  by_contra h
  have : IsEmpty A := not_nonempty_iff.mp h
  have ht : R.trace = 0 := by simp [Matrix.trace]
  exact one_ne_zero (hR.2.symm.trans ht)

omit [DecidableEq O] in

theorem integrable_gram (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (R : Matrix (A × B) (A × B) ℂ) (hR : IsDensity R) :
    Integrable (fun x => (K x)ᴴ * K x) μ := by
  classical
  have : Nonempty A := input_nonempty_of_density R hR
  by_contra hi
  have hz := hComplete
  rw [integral_undef hi] at hz
  exact zero_ne_one hz

theorem integrable_untouchedBranch (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (R : Matrix (A × B) (A × B) ℂ) (hR : IsDensity R) :
    Integrable (fun x => partialTrace_left (localBranch (K x) R)) μ := by
  simpa only [gramToMarginal_gram] using
    (gramToMarginal R).integrable_comp (integrable_gram μ K hComplete R hR)

theorem integral_untouchedBranch (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (hGram : Integrable (fun x => (K x)ᴴ * K x) μ)
    (R : Matrix (A × B) (A × B) ℂ) :
    (∫ x, partialTrace_left (localBranch (K x) R) ∂μ) = partialTrace_left R := by
  calc
    _ = gramToMarginal R (∫ x, (K x)ᴴ * K x ∂μ) := by
      simpa only [gramToMarginal_gram] using (gramToMarginal R).integral_comp_comm hGram
    _ = partialTrace_left R := by rw [hComplete, gramToMarginal_one]

theorem integrable_bornWeight (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (R : Matrix (A × B) (A × B) ℂ) (hR : IsDensity R) :
    Integrable (fun x => bornWeight (K x) R) μ := by
  have hi := realTraceCLM.integrable_comp (integrable_untouchedBranch μ K hComplete R hR)
  change Integrable (fun x => (partialTrace_left (localBranch (K x) R)).trace.re) μ at hi
  simpa only [trace_partialTraceLeft, bornWeight, branchProbability, localBranch] using hi

theorem integral_bornWeight_eq_one (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (R : Matrix (A × B) (A × B) ℂ) (hR : IsDensity R) :
    (∫ x, bornWeight (K x) R ∂μ) = 1 := by
  have hi := realTraceCLM.integral_comp_comm (integrable_untouchedBranch μ K hComplete R hR)
  rw [integral_untouchedBranch μ K hComplete (integrable_gram μ K hComplete R hR) R] at hi
  change (∫ x, (partialTrace_left (localBranch (K x) R)).trace.re ∂μ) =
    (partialTrace_left R).trace.re at hi
  simpa only [trace_partialTraceLeft, hR.2, Complex.one_re, bornWeight, branchProbability, localBranch] using hi

theorem integrable_localBranch (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (R : Matrix (A × B) (A × B) ℂ) (hR : IsDensity R) :
    Integrable (fun x => localBranch (K x) R) μ := by
  apply (integrable_bornWeight μ K hComplete R hR).mono'
    (measurable_localBranch K hK R).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x =>
    ProbabilityMixtures.posSemidef_norm_le_trace _ (branch_posSemidef (K x) hR.1)

theorem output_untouchedMarginal (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (R : Matrix (A × B) (A × B) ℂ) (hR : IsDensity R) :
    partialTrace_left (output μ K R) = partialTrace_left R := by
  calc
    _ = ∫ x, partialTrace_left (localBranch (K x) R) ∂μ :=
      (partialTraceCLM.integral_comp_comm (integrable_localBranch μ K hK hComplete R hR)).symm
    _ = partialTrace_left R :=
      integral_untouchedBranch μ K hComplete (integrable_gram μ K hComplete R hR) R

theorem output_isDensity (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (R : Matrix (A × B) (A × B) ℂ) (hR : IsDensity R) : IsDensity (output μ K R) := by
  have hPSD : (output μ K R).PosSemidef :=
    (integral_nonneg (fun x => (branch_posSemidef (K x) hR.1).nonneg)).posSemidef
  refine ⟨hPSD, ?_⟩
  calc
    (output μ K R).trace = (partialTrace_left (output μ K R)).trace :=
      (trace_partialTraceLeft _).symm
    _ = (partialTrace_left R).trace := congrArg Matrix.trace (output_untouchedMarginal μ K hK hComplete R hR)
    _ = 1 := (trace_partialTraceLeft R).trans hR.2

theorem bornMeasure_isProbability (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (R : Matrix (A × B) (A × B) ℂ) (hR : IsDensity R) :
    IsProbabilityMeasure (bornMeasure μ K R) := by
  constructor
  rw [bornMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp only [bornDensity]
  rw [
    ← ofReal_integral_eq_lintegral_ofReal (integrable_bornWeight μ K hComplete R hR)
      (Filter.Eventually.of_forall fun x => branchProbability_nonneg (K x) hR.1),
    integral_bornWeight_eq_one μ K hComplete R hR, ENNReal.ofReal_one]

theorem normalizedBranch_isDensity (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (R : Matrix (A × B) (A × B) ℂ) (hR : IsDensity R) (x : Ω) :
    IsDensity (normalizedBranch μ K R x) := by
  classical
  by_cases hz : bornWeight (K x) R = 0
  · simpa only [normalizedBranch, ite_eq_left hz] using output_isDensity μ K hK hComplete R hR
  · have hPSD : ((bornWeight (K x) R)⁻¹ • localBranch (K x) R).PosSemidef :=
      (branch_posSemidef (K x) hR.1).smul (inv_nonneg.mpr (branchProbability_nonneg (K x) hR.1))
    refine ⟨by simpa only [normalizedBranch, ite_eq_right hz] using hPSD, ?_⟩
    simp only [normalizedBranch, ite_eq_right hz]
    apply Complex.ext
    · simp only [Matrix.trace_smul, Complex.smul_re, smul_eq_mul, Complex.one_re]
      exact inv_mul_cancel₀ hz
    · simpa only [Complex.one_im] using (Complex.nonneg_iff.mp hPSD.trace_nonneg).2.symm

theorem probability_smul_normalizedBranch (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (R : Matrix (A × B) (A × B) ℂ) (hR : R.PosSemidef) (x : Ω) :
    bornWeight (K x) R • normalizedBranch μ K R x = localBranch (K x) R := by
  classical
  by_cases hz : bornWeight (K x) R = 0
  · rw [hz, zero_smul]
    exact (branch_eq_zero_of_probability_eq_zero (K x) hR hz).symm
  · simp only [normalizedBranch, ite_eq_right hz, smul_smul, mul_inv_cancel₀ hz, one_smul]

theorem measurable_normalizedBranch (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (R : Matrix (A × B) (A × B) ℂ) :
    Measurable (normalizedBranch μ K R) := by
  classical
  exact Measurable.ite
    ((measurable_bornWeight K hK R).stronglyMeasurable.measurableSet_eq_fun stronglyMeasurable_const)
    measurable_const ((measurable_bornWeight K hK R).inv.smul (measurable_localBranch K hK R))

theorem normalizedUntouchedMarginal_isDensity (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (R : Matrix (A × B) (A × B) ℂ) (hR : IsDensity R) (x : Ω) :
    IsDensity (normalizedUntouchedMarginal μ K R x) :=
  partialTraceLeft_isDensity (normalizedBranch_isDensity μ K hK hComplete R hR x)

theorem measurable_normalizedUntouchedMarginal (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (R : Matrix (A × B) (A × B) ℂ) :
    Measurable (normalizedUntouchedMarginal μ K R) :=
  partialTraceCLM.continuous.measurable.comp (measurable_normalizedBranch μ K hK R)

theorem integral_bornMeasure {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure Ω) (K : Ω → Matrix O A ℂ) (hK : Measurable K)
    (R : Matrix (A × B) (A × B) ℂ) (hR : R.PosSemidef) (f : Ω → F) :
    (∫ x, f x ∂bornMeasure μ K R) = ∫ x, bornWeight (K x) R • f x ∂μ := by
  simpa only [bornMeasure, bornDensity, ENNReal.toReal_ofReal (branchProbability_nonneg _ hR)] using
    integral_withDensity_eq_integral_toReal_smul (μ := μ) (measurable_bornDensity K hK R)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f

theorem integral_normalizedUntouchedMarginal (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (R : Matrix (A × B) (A × B) ℂ) (hR : IsDensity R) :
    (∫ x, normalizedUntouchedMarginal μ K R x ∂bornMeasure μ K R) = partialTrace_left R := by
  rw [integral_bornMeasure μ K hK R hR.1]
  calc
    _ = ∫ x, partialTrace_left (localBranch (K x) R) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change bornWeight (K x) R • partialTraceCLM (normalizedBranch μ K R x) = _
        rw [← partialTraceCLM.map_smul_of_tower, probability_smul_normalizedBranch μ K R hR.1 x]
        rfl
    _ = partialTrace_left R :=
      integral_untouchedBranch μ K hComplete (integrable_gram μ K hComplete R hR) R

theorem average_retainedEntropy_le (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (R : Matrix (A × B) (A × B) ℂ) (hR : IsDensity R) :
    (∫ x, entropyBits (normalizedUntouchedMarginal μ K R x) ∂bornMeasure μ K R) ≤
      entropyBits (partialTrace_left R) := by
  have := bornMeasure_isProbability μ K hComplete R hR
  have hj := ProbabilityMixtures.entropyBits_integral_lower (bornMeasure μ K R)
    (normalizedUntouchedMarginal μ K R)
    (measurable_normalizedUntouchedMarginal μ K hK R).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => normalizedUntouchedMarginal_isDensity μ K hK hComplete R hR x)
  rw [integral_normalizedUntouchedMarginal μ K hK hComplete R hR] at hj
  exact hj

def pureDensity {I : Type*} (v : I → ℂ) : Matrix I I ℂ := fun i j => v i * star (v j)

def vectorNormSq {I : Type*} [Fintype I] (v : I → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

theorem pureDensity_posSemidef {I : Type*} [Fintype I] (v : I → ℂ) :
    (pureDensity v).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v

theorem pureDensity_trace {I : Type*} [Fintype I] (v : I → ℂ) :
    (pureDensity v).trace = (vectorNormSq v : ℂ) := by
  simp [pureDensity, Matrix.trace, vectorNormSq, Complex.mul_conj]

theorem pureDensity_isDensity {I : Type*} [Fintype I] [DecidableEq I] (v : I → ℂ)
    (hv : vectorNormSq v = 1) : IsDensity (pureDensity v) :=
  ⟨pureDensity_posSemidef v, by rw [pureDensity_trace, hv]; rfl⟩

omit [Fintype O] [DecidableEq A] [DecidableEq O] in
theorem localBranch_pure (K : Matrix O A ℂ) (ψ : A × B → ℂ) :
    localBranch K (pureDensity ψ) = pureDensity ((localLift K).mulVec ψ) := by
  change localLift K * Matrix.vecMulVec ψ (star ψ) * (localLift K)ᴴ =
    Matrix.vecMulVec ((localLift K).mulVec ψ) (star ((localLift K).mulVec ψ))
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

theorem bornWeight_pure (K : Matrix O A ℂ) (ψ : A × B → ℂ) :
    bornWeight K (pureDensity ψ) = vectorNormSq ((localLift K).mulVec ψ) := by
  change (localBranch K (pureDensity ψ)).trace.re = _
  rw [localBranch_pure, pureDensity_trace, Complex.ofReal_re]

private theorem density_nonempty {I : Type*} [Fintype I] [DecidableEq I] {R : Matrix I I ℂ}
    (hR : IsDensity R) : Nonempty I := by
  classical
  by_contra h
  have : IsEmpty I := not_nonempty_iff.mp h
  have ht : R.trace = 0 := by simp [Matrix.trace]
  exact one_ne_zero (hR.2.symm.trans ht)

def unitFallback {I : Type*} [DecidableEq I] : I → ℂ := by
  classical
  exact if h : Nonempty I then Pi.single (Classical.choice h) 1 else 0

theorem unitFallback_normSq {I : Type*} [Fintype I] [DecidableEq I]
    (hI : Nonempty I) : vectorNormSq (unitFallback (I := I)) = 1 := by
  classical
  simp only [unitFallback, dite_eq_left hI]
  simp [vectorNormSq, Pi.single_apply, apply_ite]

def normalizedVector {I : Type*} [Fintype I] (v fallback : I → ℂ) : I → ℂ :=
  if vectorNormSq v = 0 then fallback else
    (((Real.sqrt (vectorNormSq v))⁻¹ : ℝ) : ℂ) • v

private theorem vectorNormSq_nonneg {I : Type*} [Fintype I] (v : I → ℂ) :
    0 ≤ vectorNormSq v := Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

private theorem vectorNormSq_scalar {I : Type*} [Fintype I] (v : I → ℂ) (z : ℂ) :
    vectorNormSq (z • v) = Complex.normSq z * vectorNormSq v := by
  simp [vectorNormSq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]

private theorem pureDensity_scalar {I : Type*} (v : I → ℂ) (z : ℂ) :
    pureDensity (z • v) = (Complex.normSq z : ℂ) • pureDensity v := by
  have hz : z * star z = (Complex.normSq z : ℂ) := by
    simpa only [Complex.star_def] using Complex.mul_conj z
  ext i j
  simp only [pureDensity, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, star_mul, ← hz]
  ring

private theorem inverse_norm_factor {I : Type*} [Fintype I] (v : I → ℂ) :
    Complex.normSq (((Real.sqrt (vectorNormSq v))⁻¹ : ℝ) : ℂ) = (vectorNormSq v)⁻¹ := by
  simp only [Complex.normSq_ofReal, ← sq, inv_pow]
  rw [Real.sq_sqrt (vectorNormSq_nonneg v)]

theorem normalizedVector_normSq {I : Type*} [Fintype I] (v fallback : I → ℂ)
    (hf : vectorNormSq fallback = 1) : vectorNormSq (normalizedVector v fallback) = 1 := by
  by_cases hz : vectorNormSq v = 0
  · simp only [normalizedVector, ite_eq_left hz, hf]
  · rw [normalizedVector, ite_eq_right hz, vectorNormSq_scalar,
      inverse_norm_factor, inv_mul_cancel₀ hz]

theorem normalizedVector_density_of_nonzero {I : Type*} [Fintype I]
    (v fallback : I → ℂ) (hz : vectorNormSq v ≠ 0) :
    pureDensity (normalizedVector v fallback) = ((vectorNormSq v)⁻¹ : ℝ) • pureDensity v := by
  rw [normalizedVector, ite_eq_right hz, pureDensity_scalar, inverse_norm_factor]
  ext i j
  simp [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]

def normalizedPureBranchVector (K : Ω → Matrix O A ℂ) (ψ : A × B → ℂ) (x : Ω) : O × B → ℂ :=
  normalizedVector ((localLift (K x)).mulVec ψ) unitFallback

theorem normalizedPureBranchVector_normSq (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (ψ : A × B → ℂ) (hψ : vectorNormSq ψ = 1) (x : Ω) :
    vectorNormSq (normalizedPureBranchVector K ψ x) = 1 := by
  have hOut := output_isDensity μ K hK hComplete (pureDensity ψ) (pureDensity_isDensity ψ hψ)
  change vectorNormSq (normalizedVector ((localLift (K x)).mulVec ψ) (unitFallback (I := O × B))) = 1
  exact normalizedVector_normSq _ _ (unitFallback_normSq (density_nonempty hOut))

theorem bornWeight_ne_zero_ae (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (R : Matrix (A × B) (A × B) ℂ) :
    ∀ᵐ x ∂bornMeasure μ K R, bornWeight (K x) R ≠ 0 := by
  change ∀ᵐ x ∂μ.withDensity (bornDensity K R), bornWeight (K x) R ≠ 0
  rw [ae_withDensity_iff (measurable_bornDensity K hK R)]
  exact Filter.Eventually.of_forall fun x hx hz => hx (by simp [bornDensity, hz])

theorem normalizedBranch_pure_ae (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (ψ : A × B → ℂ) :
    ∀ᵐ x ∂bornMeasure μ K (pureDensity ψ),
      normalizedBranch μ K (pureDensity ψ) x = pureDensity (normalizedPureBranchVector K ψ x) := by
  filter_upwards [bornWeight_ne_zero_ae μ K hK (pureDensity ψ)] with x hx
  have hv : vectorNormSq ((localLift (K x)).mulVec ψ) ≠ 0 := by rwa [← bornWeight_pure]
  rw [normalizedBranch, ite_eq_right hx]
  change _ = pureDensity (normalizedVector ((localLift (K x)).mulVec ψ) unitFallback)
  rw [normalizedVector_density_of_nonzero _ _ hv, ← bornWeight_pure, localBranch_pure]

theorem pure_marginal_entropy_eq (ψ : A × B → ℂ) :
    entropyBits (partialTrace_right (pureDensity ψ)) = entropyBits (partialTrace_left (pureDensity ψ)) := by
  let M : Matrix A B ℂ := fun a b => ψ (a,b)
  have hRight : partialTrace_right (pureDensity ψ) = M * Mᴴ := by ext a a'; rfl
  have hLeft : partialTrace_left (pureDensity ψ) = (Mᴴ * M)ᵀ := by
    ext b b'
    change (∑ a, ψ (a,b) * star (ψ (a,b'))) = ∑ a, star (ψ (a,b')) * ψ (a,b)
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hRight, hLeft]
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits (M * Mᴴ) =
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits (Mᴴ * M)ᵀ
  rw [ConditionalRange.entropyBits_transpose (Matrix.posSemidef_conjTranspose_mul_self M).isHermitian]
  exact (ConditionalRange.entropyBits_rectangularGram M).symm

theorem integrable_pureBranchEntropy (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (ψ : A × B → ℂ) (hψ : vectorNormSq ψ = 1) :
    Integrable (fun x => entropyBits (partialTrace_left (pureDensity (normalizedPureBranchVector K ψ x))))
      (bornMeasure μ K (pureDensity ψ)) := by
  have hR := pureDensity_isDensity ψ hψ
  have := bornMeasure_isProbability μ K hComplete (pureDensity ψ) hR
  have hi := ProbabilityMixtures.integrable_entropyBits (bornMeasure μ K (pureDensity ψ))
    (normalizedUntouchedMarginal μ K (pureDensity ψ))
    (measurable_normalizedUntouchedMarginal μ K hK (pureDensity ψ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => normalizedUntouchedMarginal_isDensity μ K hK hComplete _ hR x)
  apply hi.congr
  filter_upwards [normalizedBranch_pure_ae μ K hK ψ] with x hx
  exact congrArg (fun X => entropyBits (partialTrace_left X)) hx

theorem average_pure_retainedEntropy_le (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (ψ : A × B → ℂ) (hψ : vectorNormSq ψ = 1) :
    (∫ x, entropyBits (partialTrace_left (pureDensity (normalizedPureBranchVector K ψ x)))
      ∂bornMeasure μ K (pureDensity ψ)) ≤ entropyBits (partialTrace_left (pureDensity ψ)) := by
  have hj := average_retainedEntropy_le μ K hK hComplete (pureDensity ψ) (pureDensity_isDensity ψ hψ)
  have he : (fun x => entropyBits (partialTrace_left (pureDensity (normalizedPureBranchVector K ψ x)))) =ᵐ[
      bornMeasure μ K (pureDensity ψ)] fun x => entropyBits (normalizedUntouchedMarginal μ K (pureDensity ψ) x) := by
    filter_upwards [normalizedBranch_pure_ae μ K hK ψ] with x hx
    exact congrArg (fun X => entropyBits (partialTrace_left X)) hx.symm
  rw [integral_congr_ae he]
  exact hj

theorem average_pure_actedEntropy_le (μ : Measure Ω) (K : Ω → Matrix O A ℂ)
    (hK : Measurable K) (hComplete : (∫ x, (K x)ᴴ * K x ∂μ) = 1)
    (ψ : A × B → ℂ) (hψ : vectorNormSq ψ = 1) :
    (∫ x, entropyBits (partialTrace_right (pureDensity (normalizedPureBranchVector K ψ x)))
      ∂bornMeasure μ K (pureDensity ψ)) ≤ entropyBits (partialTrace_right (pureDensity ψ)) := by
  simp_rw [pure_marginal_entropy_eq]
  exact average_pure_retainedEntropy_le μ K hK hComplete ψ hψ

end QuantumProver.ConditionalEntropy.ContinuousLocalInstrument
