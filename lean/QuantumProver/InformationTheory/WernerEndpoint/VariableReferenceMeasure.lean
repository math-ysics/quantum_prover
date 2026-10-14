import QuantumProver.InformationTheory.WernerEndpoint.FiniteReferenceMeasure
import QuantumProver.InformationTheory.WernerEndpoint.HeterogeneousChannelBound

set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable section

open Matrix MeasureTheory Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

namespace QuantumProver.WernerEndpoint.MatrixVariableReferenceMeasure

open LocalChannelMoments ContinuousChannelIntegrability
open QuantumProver.SuperchannelDiscrimination

abbrev gramTraceWeight {a p : ℕ} (K : Matrix (Fin p) (Fin a) ℂ) : ℝ :=
  FiniteReferenceMeasure.gramTraceWeight K

abbrev rescaledKraus {a p : ℕ} (K : Matrix (Fin p) (Fin a) ℂ) :
    Matrix (Fin p) (Fin a) ℂ := FiniteReferenceMeasure.rescaledKraus K

def referenceMeasure {Ω : Type*} [MeasurableSpace Ω] {a : ℕ}
    (μ : Measure Ω) (p : Ω → ℕ) (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ) :
    Measure Ω := μ.withDensity (fun ω => ENNReal.ofReal (gramTraceWeight (K ω)))

theorem gramTraceWeight_nonneg {a p : ℕ} (K : Matrix (Fin p) (Fin a) ℂ) :
    0 ≤ gramTraceWeight K := FiniteReferenceMeasure.gramTraceWeight_nonneg K

theorem gramTraceWeight_eq_zero_iff {a p : ℕ} (K : Matrix (Fin p) (Fin a) ℂ) :
    gramTraceWeight K = 0 ↔ K = 0 := FiniteReferenceMeasure.gramTraceWeight_eq_zero_iff K

theorem zeroFiber_weight {a : ℕ} (K : Matrix (Fin 0) (Fin a) ℂ) :
    gramTraceWeight K = 0 := by
  apply (gramTraceWeight_eq_zero_iff K).mpr
  ext i j
  exact isEmptyElim i

theorem weighted_rescaledGram {a p : ℕ} (K : Matrix (Fin p) (Fin a) ℂ) :
    gramTraceWeight K • ((rescaledKraus K)ᴴ * rescaledKraus K) = Kᴴ * K :=
  FiniteReferenceMeasure.weighted_rescaledGram K

abbrev Packed (a : ℕ) (G : ℕ → Type*) :=
  Sigma (fun p => Matrix (Fin p) (Fin a) ℂ × G p)

def rescalePacked (a : ℕ) (G : ℕ → Type*) (z : Packed a G) : Packed a G :=
  ⟨z.1, rescaledKraus z.2.1, z.2.2⟩

private theorem measurable_fiberElim {D : Type*} (F : D → Type*)
    [∀ d, MeasurableSpace (F d)] {E : Type*} [MeasurableSpace E]
    (f : Sigma F → E) (hf : ∀ d, Measurable (fun x : F d => f ⟨d, x⟩)) :
    Measurable f := by
  intro s hs
  change MeasurableSet[⨅ d, (inferInstance : MeasurableSpace (F d)).map (Sigma.mk d)]
    (f ⁻¹' s)
  rw [MeasurableSpace.measurableSet_iInf]
  intro d
  exact hf d hs

private theorem measurable_fiberMk {D : Type*} (F : D → Type*)
    [∀ d, MeasurableSpace (F d)] (d : D) : Measurable (Sigma.mk d : F d → Sigma F) := by
  intro s hs
  change MeasurableSet[⨅ e, (inferInstance : MeasurableSpace (F e)).map (Sigma.mk e)] s at hs
  rw [MeasurableSpace.measurableSet_iInf] at hs
  exact hs d

theorem measurable_rescalePacked (a : ℕ) (G : ℕ → Type*)
    [∀ p, MeasurableSpace (G p)] : Measurable (rescalePacked a G) := by
  apply measurable_fiberElim
  intro p
  exact (measurable_fiberMk (fun p => Matrix (Fin p) (Fin a) ℂ × G p) p).comp
    ((FiniteReferenceMeasure.measurable_rescaledKraus
      (fun z : Matrix (Fin p) (Fin a) ℂ × G p => z.1) measurable_fst).prodMk measurable_snd)

theorem measurable_packedGram (a : ℕ) (G : ℕ → Type*)
    [∀ p, MeasurableSpace (G p)] :
    Measurable (fun z : Packed a G => z.2.1.conjTranspose * z.2.1) := by
  apply measurable_fiberElim
  intro p
  have hGram : Continuous (fun K : Matrix (Fin p) (Fin a) ℂ => Kᴴ * K) := by
    fun_prop
  exact hGram.measurable.comp measurable_fst

theorem measurable_packedWeight (a : ℕ) (G : ℕ → Type*)
    [∀ p, MeasurableSpace (G p)] :
    Measurable (fun z : Packed a G => gramTraceWeight z.2.1) := by
  apply measurable_fiberElim
  intro p
  exact FiniteReferenceMeasure.measurable_gramTraceWeight
    (fun z : Matrix (Fin p) (Fin a) ℂ × G p => z.1) measurable_fst

theorem measurable_packedDimension (a : ℕ) (G : ℕ → Type*)
    [∀ p, MeasurableSpace (G p)] : Measurable (Sigma.fst : Packed a G → ℕ) := by
  apply measurable_fiberElim
  intro p
  exact measurable_const

section Reference

variable {Ω : Type*} [MeasurableSpace Ω] {a : ℕ}

private def realTraceCLM : Matrix (Fin a) (Fin a) ℂ →L[ℝ] ℝ :=
  (Complex.reLm.comp (Matrix.traceLinearMap (Fin a) ℝ ℂ)).toContinuousLinearMap

private theorem realTraceCLM_apply (X : Matrix (Fin a) (Fin a) ℂ) :
    realTraceCLM X = X.trace.re := rfl

theorem integrable_gram_of_complete (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (hComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1) :
    Integrable (fun ω => (K ω)ᴴ * K ω) μ := by
  classical
  by_cases hInput : Nonempty (Fin a)
  · let := hInput
    by_contra hNot
    have hZero := integral_undef hNot
    rw [hComplete] at hZero
    exact one_ne_zero hZero
  · let : IsEmpty (Fin a) := not_nonempty_iff.mp hInput
    have hZero : (fun ω => (K ω)ᴴ * K ω) = (0 : Ω → Matrix (Fin a) (Fin a) ℂ) := by
      ext ω i j
      exact isEmptyElim i
    rw [hZero]
    exact integrable_zero Ω (Matrix (Fin a) (Fin a) ℂ) μ

theorem measurable_gramTraceWeight (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (hGram : Measurable (fun ω => (K ω)ᴴ * K ω)) :
    Measurable (fun ω => gramTraceWeight (K ω)) :=
  (realTraceCLM (a := a)).continuous.measurable.comp hGram

theorem integrable_gramTraceWeight (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ) :
    Integrable (fun ω => gramTraceWeight (K ω)) μ := by
  simpa only [realTraceCLM_apply, gramTraceWeight, FiniteReferenceMeasure.gramTraceWeight]
    using (realTraceCLM (a := a)).integrable_comp hGram

theorem integral_gramTraceWeight (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1) :
    (∫ ω, gramTraceWeight (K ω) ∂μ) = (a : ℝ) := by
  have h := (realTraceCLM (a := a)).integral_comp_comm hGram
  simpa only [realTraceCLM_apply, gramTraceWeight, FiniteReferenceMeasure.gramTraceWeight,
    hComplete, Matrix.trace_one, Complex.natCast_re,
    Fintype.card_fin] using h

theorem referenceMeasure_univ (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1) :
    referenceMeasure μ p K Set.univ = (a : ENNReal) := by
  rw [referenceMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gramTraceWeight μ p K hGram)
    (Eventually.of_forall fun ω => gramTraceWeight_nonneg (K ω)),
    integral_gramTraceWeight μ p K hGram hComplete]
  simp

theorem referenceMeasure_isFinite (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1) :
    IsFiniteMeasure (referenceMeasure μ p K) :=
  ⟨by rw [referenceMeasure_univ μ p K hGram hComplete]; exact ENNReal.natCast_lt_top _⟩

theorem referenceMeasure_eq_zero_of_empty_input (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin 0) ℂ) : referenceMeasure μ p K = 0 := by
  have hK : ∀ ω, K ω = 0 := by
    intro ω
    ext i j
    exact isEmptyElim j
  simp [referenceMeasure, gramTraceWeight, FiniteReferenceMeasure.gramTraceWeight, hK]

theorem aestronglyMeasurable_referenceMeasure {E : Type*} [TopologicalSpace E]
    (μ : Measure Ω) (p : Ω → ℕ) (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    {F : Ω → E} (hF : AEStronglyMeasurable F μ) :
    AEStronglyMeasurable F (referenceMeasure μ p K) :=
  hF.mono_ac (withDensity_absolutelyContinuous μ _)

theorem integrable_referenceMeasure_iff_scaled {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (p : Ω → ℕ) (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (hWeight : Measurable (fun ω => gramTraceWeight (K ω))) (F : Ω → E) :
    Integrable F (referenceMeasure μ p K) ↔
      Integrable (fun ω => gramTraceWeight (K ω) • F ω) μ := by
  have h := integrable_withDensity_iff_integrable_smul' (μ := μ) (g := F)
    (ENNReal.measurable_ofReal.comp hWeight)
    (Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)
  simpa only [referenceMeasure, Function.comp_def,
    ENNReal.toReal_ofReal (gramTraceWeight_nonneg _)] using h

theorem integral_referenceMeasure_eq_scaled {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (p : Ω → ℕ) (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (hWeight : Measurable (fun ω => gramTraceWeight (K ω))) (F : Ω → E) :
    (∫ ω, F ω ∂referenceMeasure μ p K) = ∫ ω, gramTraceWeight (K ω) • F ω ∂μ := by
  simpa only [referenceMeasure, Function.comp_def,
    ENNReal.toReal_ofReal (gramTraceWeight_nonneg _)] using
    integral_withDensity_eq_integral_toReal_smul (μ := μ)
      (ENNReal.measurable_ofReal.comp hWeight)
      (Eventually.of_forall fun ω => ENNReal.ofReal_lt_top) F

theorem integrable_rescaledGram (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (hWeight : Measurable (fun ω => gramTraceWeight (K ω)))
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ) :
    Integrable (fun ω => (rescaledKraus (K ω))ᴴ * rescaledKraus (K ω))
      (referenceMeasure μ p K) := by
  rw [integrable_referenceMeasure_iff_scaled μ p K hWeight]
  simpa only [weighted_rescaledGram] using hGram

theorem integral_rescaledGram (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (hWeight : Measurable (fun ω => gramTraceWeight (K ω))) :
    (∫ ω, (rescaledKraus (K ω))ᴴ * rescaledKraus (K ω) ∂referenceMeasure μ p K) =
      ∫ ω, (K ω)ᴴ * K ω ∂μ := by
  rw [integral_referenceMeasure_eq_scaled μ p K hWeight]
  simp only [weighted_rescaledGram]

theorem rescaledGram_complete (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (hWeight : Measurable (fun ω => gramTraceWeight (K ω)))
    (hComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1) :
    (∫ ω, (rescaledKraus (K ω))ᴴ * rescaledKraus (K ω) ∂referenceMeasure μ p K) = 1 := by
  rw [integral_rescaledGram μ p K hWeight, hComplete]

end Reference

section Moments

variable {Ω O : Type*} [MeasurableSpace Ω] [Fintype O] [DecidableEq O]

abbrev MatrixFiber (a : ℕ) (O : Type*) [Fintype O] [DecidableEq O] (p : ℕ) :=
  Matrix (Fin p) (Fin a) ℂ × (Matrix (Fin p) (Fin p) ℂ →L[ℂ] Matrix O O ℂ)
abbrev LeftFiber (a b : ℕ) (O : Type*) [Fintype O] [DecidableEq O] (p : ℕ) :=
  Matrix (Fin p) (Fin a) ℂ × (JointMatrix p b →L[ℂ] Matrix O O ℂ)
abbrev RightFiber (a b : ℕ) (O : Type*) [Fintype O] [DecidableEq O] (p : ℕ) :=
  Matrix (Fin p) (Fin b) ℂ × (JointMatrix a p →L[ℂ] Matrix O O ℂ)

theorem measurable_matrix_moment (a : ℕ) :
    Measurable (fun z : Sigma (MatrixFiber a O) =>
      z.2.2.comp (matrixSandwichCLM z.2.1)) := by
  apply measurable_fiberElim
  intro p
  exact (continuous_snd.clm_comp
    (continuous_matrixSandwichCLM.comp continuous_fst)).measurable

theorem measurable_left_moment (a b : ℕ) :
    Measurable (fun z : Sigma (LeftFiber a b O) =>
      z.2.2.comp (leftSandwichCLM z.2.1)) := by
  apply measurable_fiberElim
  intro p
  exact (continuous_snd.clm_comp
    (continuous_leftSandwichCLM.comp continuous_fst)).measurable

theorem measurable_right_moment (a b : ℕ) :
    Measurable (fun z : Sigma (RightFiber a b O) =>
      z.2.2.comp (rightSandwichCLM z.2.1)) := by
  apply measurable_fiberElim
  intro p
  exact (continuous_snd.clm_comp
    (continuous_rightSandwichCLM.comp continuous_fst)).measurable

theorem integrable_matrix_moment_of_cptp {a : ℕ} (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (Φ : ∀ ω, Matrix (Fin (p ω)) (Fin (p ω)) ℂ →L[ℂ] Matrix O O ℂ)
    (hPacked : Measurable (fun ω => (⟨p ω, K ω, Φ ω⟩ : Sigma (MatrixFiber a O))))
    (hCP : ∀ ω, CPWrappers.CompletelyPositive (Φ ω).toLinearMap)
    (hTP : ∀ ω, CPTPKraus.TracePreserving (Φ ω).toLinearMap)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ) :
    Integrable (fun ω => (Φ ω).comp (matrixSandwichCLM (K ω))) μ := by
  exact HeterogeneousChannelBound.integrable_varying_cptp_moment μ K Φ hCP hTP
    ((measurable_matrix_moment (O := O) a).comp hPacked).aestronglyMeasurable hGram

theorem integrable_left_moment_of_cptp {a b : ℕ} (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (Φ : ∀ ω, JointMatrix (p ω) b →L[ℂ] Matrix O O ℂ)
    (hPacked : Measurable (fun ω => (⟨p ω, K ω, Φ ω⟩ : Sigma (LeftFiber a b O))))
    (hCP : ∀ ω, CPWrappers.CompletelyPositive (Φ ω).toLinearMap)
    (hTP : ∀ ω, CPTPKraus.TracePreserving (Φ ω).toLinearMap)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ) :
    Integrable (fun ω => (Φ ω).comp (leftSandwichCLM (K ω))) μ := by
  have hLift : Integrable (fun ω =>
      (K ω ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ *
        (K ω ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))) μ := by
    simpa only [leftGramLiftCLM_apply, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul] using
      (leftGramLiftCLM (I := Fin a) (Fin b)).integrable_comp hGram
  exact HeterogeneousChannelBound.integrable_varying_cptp_moment μ
    (fun ω => K ω ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) Φ hCP hTP
    ((measurable_left_moment (O := O) a b).comp hPacked).aestronglyMeasurable hLift

theorem integrable_right_moment_of_cptp {a b : ℕ} (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin b) ℂ)
    (Φ : ∀ ω, JointMatrix a (p ω) →L[ℂ] Matrix O O ℂ)
    (hPacked : Measurable (fun ω => (⟨p ω, K ω, Φ ω⟩ : Sigma (RightFiber a b O))))
    (hCP : ∀ ω, CPWrappers.CompletelyPositive (Φ ω).toLinearMap)
    (hTP : ∀ ω, CPTPKraus.TracePreserving (Φ ω).toLinearMap)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ) :
    Integrable (fun ω => (Φ ω).comp (rightSandwichCLM (K ω))) μ := by
  have hLift : Integrable (fun ω =>
      ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K ω)ᴴ *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K ω)) μ := by
    simpa only [rightGramLiftCLM_apply, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul] using
      (rightGramLiftCLM (I := Fin b) (Fin a)).integrable_comp hGram
  exact HeterogeneousChannelBound.integrable_varying_cptp_moment μ
    (fun ω => (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K ω) Φ hCP hTP
    ((measurable_right_moment (O := O) a b).comp hPacked).aestronglyMeasurable hLift

theorem integrable_matrix_moment_rescaled {a : ℕ} (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (Φ : ∀ ω, Matrix (Fin (p ω)) (Fin (p ω)) ℂ →L[ℂ] Matrix O O ℂ)
    (hWeight : Measurable (fun ω => gramTraceWeight (K ω)))
    (hMoment : Integrable (fun ω => (Φ ω).comp (matrixSandwichCLM (K ω))) μ) :
    Integrable (fun ω => (Φ ω).comp (matrixSandwichCLM (rescaledKraus (K ω))))
      (referenceMeasure μ p K) := by
  rw [integrable_referenceMeasure_iff_scaled μ p K hWeight
    (fun ω => (Φ ω).comp (matrixSandwichCLM (rescaledKraus (K ω))))]
  simpa only [gramTraceWeight, rescaledKraus, FiniteReferenceMeasure.weighted_matrix_moment]
    using hMoment

theorem integral_matrix_moment_rescaled {a : ℕ} (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (Φ : ∀ ω, Matrix (Fin (p ω)) (Fin (p ω)) ℂ →L[ℂ] Matrix O O ℂ)
    (hWeight : Measurable (fun ω => gramTraceWeight (K ω))) :
    (∫ ω, (Φ ω).comp (matrixSandwichCLM (rescaledKraus (K ω))) ∂referenceMeasure μ p K) =
      ∫ ω, (Φ ω).comp (matrixSandwichCLM (K ω)) ∂μ := by
  rw [integral_referenceMeasure_eq_scaled μ p K hWeight]
  simp only [FiniteReferenceMeasure.weighted_matrix_moment]

theorem integrable_left_moment_rescaled {a b : ℕ} (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (Φ : ∀ ω, JointMatrix (p ω) b →L[ℂ] Matrix O O ℂ)
    (hWeight : Measurable (fun ω => gramTraceWeight (K ω)))
    (hMoment : Integrable (fun ω => (Φ ω).comp (leftSandwichCLM (K ω))) μ) :
    Integrable (fun ω => (Φ ω).comp (leftSandwichCLM (rescaledKraus (K ω))))
      (referenceMeasure μ p K) := by
  rw [integrable_referenceMeasure_iff_scaled μ p K hWeight
    (fun ω => (Φ ω).comp (leftSandwichCLM (rescaledKraus (K ω))))]
  simpa only [gramTraceWeight, rescaledKraus, FiniteReferenceMeasure.weighted_left_moment]
    using hMoment

theorem integral_left_moment_rescaled {a b : ℕ} (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin a) ℂ)
    (Φ : ∀ ω, JointMatrix (p ω) b →L[ℂ] Matrix O O ℂ)
    (hWeight : Measurable (fun ω => gramTraceWeight (K ω))) :
    (∫ ω, (Φ ω).comp (leftSandwichCLM (rescaledKraus (K ω))) ∂referenceMeasure μ p K) =
      ∫ ω, (Φ ω).comp (leftSandwichCLM (K ω)) ∂μ := by
  rw [integral_referenceMeasure_eq_scaled μ p K hWeight]
  simp only [FiniteReferenceMeasure.weighted_left_moment]

theorem integrable_right_moment_rescaled {a b : ℕ} (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin b) ℂ)
    (Φ : ∀ ω, JointMatrix a (p ω) →L[ℂ] Matrix O O ℂ)
    (hWeight : Measurable (fun ω => gramTraceWeight (K ω)))
    (hMoment : Integrable (fun ω => (Φ ω).comp (rightSandwichCLM (K ω))) μ) :
    Integrable (fun ω => (Φ ω).comp (rightSandwichCLM (rescaledKraus (K ω))))
      (referenceMeasure μ p K) := by
  rw [integrable_referenceMeasure_iff_scaled μ p K hWeight
    (fun ω => (Φ ω).comp (rightSandwichCLM (rescaledKraus (K ω))))]
  simpa only [gramTraceWeight, rescaledKraus, FiniteReferenceMeasure.weighted_right_moment]
    using hMoment

theorem integral_right_moment_rescaled {a b : ℕ} (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ ω, Matrix (Fin (p ω)) (Fin b) ℂ)
    (Φ : ∀ ω, JointMatrix a (p ω) →L[ℂ] Matrix O O ℂ)
    (hWeight : Measurable (fun ω => gramTraceWeight (K ω))) :
    (∫ ω, (Φ ω).comp (rightSandwichCLM (rescaledKraus (K ω))) ∂referenceMeasure μ p K) =
      ∫ ω, (Φ ω).comp (rightSandwichCLM (K ω)) ∂μ := by
  rw [integral_referenceMeasure_eq_scaled μ p K hWeight]
  simp only [FiniteReferenceMeasure.weighted_right_moment]

end Moments

end QuantumProver.WernerEndpoint.MatrixVariableReferenceMeasure
