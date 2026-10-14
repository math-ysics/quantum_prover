import QuantumProver.InformationTheory.WernerEndpoint.LocalChannelMoments
import QuantumProver.InformationTheory.ConditionalEntropy.ProbabilityMixtures
import QuantumProver.LinearAlgebra.SandwichedDPI.TraceNorm

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

namespace QuantumProver.WernerEndpoint.ContinuousChannelIntegrability

open LocalChannelMoments
open QuantumProver.SuperchannelDiscrimination QuantumProver.SandwichedDPI

variable {I J O B Ω : Type*} [Fintype I] [Fintype J] [Fintype O] [Fintype B]
  [DecidableEq I] [DecidableEq J] [DecidableEq O] [DecidableEq B] [MeasurableSpace Ω]

theorem matrixSandwichCLM_norm_le_gram (K : Matrix J I ℂ) :
    ‖matrixSandwichCLM K‖ ≤ ‖Kᴴ * K‖ := by
  apply (matrixSandwichCLM K).opNorm_le_bound (norm_nonneg _)
  intro X
  rw [matrixSandwichCLM_apply]
  calc
    ‖K * X * Kᴴ‖ ≤ ‖K * X‖ * ‖Kᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖K‖ * ‖X‖) * ‖Kᴴ‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul K X) (norm_nonneg _)
    _ = ‖Kᴴ * K‖ * ‖X‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose_mul_self]
      ring

theorem matrixSandwichCLM_norm_le_gram_trace (K : Matrix J I ℂ) :
    ‖matrixSandwichCLM K‖ ≤ (Kᴴ * K).trace.re :=
  (matrixSandwichCLM_norm_le_gram K).trans
    (QuantumProver.ConditionalEntropy.ProbabilityMixtures.posSemidef_norm_le_trace _
      (Matrix.posSemidef_conjTranspose_mul_self K))

theorem matrix_norm_le_traceNorm (X : Matrix I I ℂ) : ‖X‖ ≤ traceNorm X := by
  simpa only [CFC.norm_abs, traceNorm] using
    QuantumProver.ConditionalEntropy.ProbabilityMixtures.posSemidef_norm_le_trace
      (CFC.abs X) (CFC.abs_nonneg X).posSemidef

theorem traceNorm_le_card_mul_matrix_norm (X : Matrix I I ℂ) :
    traceNorm X ≤ (Fintype.card I : ℝ) * ‖X‖ := by
  have hX := (CFC.abs_nonneg X).posSemidef
  have htrace : traceNorm X = ∑ i, hX.1.eigenvalues i := by
    simpa only [traceNorm, Complex.re_sum, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_re] using congrArg Complex.re hX.1.trace_eq_sum_eigenvalues
  calc
    traceNorm X = ∑ i, hX.1.eigenvalues i := htrace
    _ ≤ ∑ _i : I, ‖X‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hi : hX.1.eigenvalues i ∈ spectrum ℝ (CFC.abs X) := by
        rw [hX.1.spectrum_real_eq_range_eigenvalues]
        exact ⟨i, rfl⟩
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hX.eigenvalues_nonneg i),
        CFC.norm_abs] using IsometricContinuousFunctionalCalculus.norm_spectrum_le
          (CFC.abs X) hi hX.1.isSelfAdjoint
    _ = _ := by simp

theorem norm_toContinuousLinearMap_le_card_of_cptp
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hCP : CPWrappers.CompletelyPositive Φ) (hTP : CPTPKraus.TracePreserving Φ) :
    ‖Φ.toContinuousLinearMap‖ ≤ (Fintype.card I : ℝ) := by
  apply Φ.toContinuousLinearMap.opNorm_le_bound (Nat.cast_nonneg _)
  intro X
  change ‖Φ X‖ ≤ (Fintype.card I : ℝ) * ‖X‖
  exact (matrix_norm_le_traceNorm _).trans
    ((traceNorm_map_le_of_cp_tracePreserving hCP hTP X).trans
      (traceNorm_le_card_mul_matrix_norm X))

theorem norm_clm_le_card_of_cptp
    (Φ : Matrix I I ℂ →L[ℂ] Matrix O O ℂ)
    (hCP : CPWrappers.CompletelyPositive Φ.toLinearMap)
    (hTP : CPTPKraus.TracePreserving Φ.toLinearMap) :
    ‖Φ‖ ≤ (Fintype.card I : ℝ) := by
  have heq : Φ.toLinearMap.toContinuousLinearMap = Φ := by ext X; rfl
  simpa only [heq] using norm_toContinuousLinearMap_le_card_of_cptp Φ.toLinearMap hCP hTP

theorem norm_clm_le_card_of_complete_kraus {Z : Type*} [Fintype Z]
    (Φ : Matrix I I ℂ →L[ℂ] Matrix O O ℂ) (K : Z → Matrix O I ℂ)
    (hComplete : ∑ z, (K z)ᴴ * K z = 1)
    (hApply : ∀ X : Matrix I I ℂ, Φ X = KrausCompletion.krausAction K X) :
    ‖Φ‖ ≤ (Fintype.card I : ℝ) := by
  apply Φ.opNorm_le_bound (Nat.cast_nonneg _)
  intro X
  rw [hApply]
  exact (matrix_norm_le_traceNorm _).trans
    ((traceNorm_krausAction_le K hComplete X).trans (traceNorm_le_card_mul_matrix_norm X))

theorem integrable_matrix_channel_moment
    (μ : Measure Ω) (K : Ω → Matrix J I ℂ)
    (Φ : Ω → Matrix J J ℂ →L[ℂ] Matrix O O ℂ)
    (hK : Measurable K) (hΦ : AEStronglyMeasurable Φ μ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    {C : ℝ} (hC : 0 ≤ C) (hBound : ∀ᵐ ω ∂μ, ‖Φ ω‖ ≤ C) :
    Integrable (fun ω => (Φ ω).comp (matrixSandwichCLM (K ω))) μ := by
  have hSand : AEStronglyMeasurable (fun ω => matrixSandwichCLM (K ω)) μ :=
    continuous_matrixSandwichCLM.comp_aestronglyMeasurable hK.aestronglyMeasurable
  have hComp : Continuous (fun z : (Matrix J J ℂ →L[ℂ] Matrix O O ℂ) ×
      (Matrix I I ℂ →L[ℂ] Matrix J J ℂ) => z.1.comp z.2) :=
    continuous_fst.clm_comp continuous_snd
  have hMeas := hComp.comp_aestronglyMeasurable (hΦ.prodMk hSand)
  refine ⟨hMeas, (hGram.norm.const_mul C).hasFiniteIntegral.mono'
    (f := fun ω => (Φ ω).comp (matrixSandwichCLM (K ω))) ?_⟩
  filter_upwards [hBound] with ω hω
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hω (matrixSandwichCLM_norm_le_gram (K ω)) (norm_nonneg _) hC)

def leftGramLiftCLM (B : Type*) [Fintype B] [DecidableEq B] :
    Matrix I I ℂ →L[ℂ] Matrix (I × B) (I × B) ℂ :=
  ({ toFun := fun G => G ⊗ₖ (1 : Matrix B B ℂ)
     map_add' := fun G H => Matrix.add_kronecker G H _
     map_smul' := fun c G => Matrix.smul_kronecker c G _ } :
      Matrix I I ℂ →ₗ[ℂ] Matrix (I × B) (I × B) ℂ).toContinuousLinearMap

omit [DecidableEq I] in
@[simp] theorem leftGramLiftCLM_apply (G : Matrix I I ℂ) :
    leftGramLiftCLM B G = G ⊗ₖ (1 : Matrix B B ℂ) := rfl

def rightGramLiftCLM (B : Type*) [Fintype B] [DecidableEq B] :
    Matrix I I ℂ →L[ℂ] Matrix (B × I) (B × I) ℂ :=
  ({ toFun := fun G => (1 : Matrix B B ℂ) ⊗ₖ G
     map_add' := fun G H => Matrix.kronecker_add _ G H
     map_smul' := fun c G => Matrix.kronecker_smul c _ G } :
      Matrix I I ℂ →ₗ[ℂ] Matrix (B × I) (B × I) ℂ).toContinuousLinearMap

omit [DecidableEq I] in
@[simp] theorem rightGramLiftCLM_apply (G : Matrix I I ℂ) :
    rightGramLiftCLM B G = (1 : Matrix B B ℂ) ⊗ₖ G := rfl

theorem leftSandwichCLM_norm_le_gram {a b p : ℕ}
    (K : Matrix (Fin p) (Fin a) ℂ) :
    ‖leftSandwichCLM (b := b) K‖ ≤
      ‖leftGramLiftCLM (I := Fin a) (Fin b)‖ * ‖Kᴴ * K‖ := by
  have hGram : (K ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ *
      (K ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) = leftGramLiftCLM (Fin b) (Kᴴ * K) := by
    simp only [leftGramLiftCLM_apply, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  apply (matrixSandwichCLM_norm_le_gram _).trans
  rw [hGram]
  exact (leftGramLiftCLM (I := Fin a) (Fin b)).le_opNorm (Kᴴ * K)

theorem rightSandwichCLM_norm_le_gram {a b p : ℕ}
    (K : Matrix (Fin p) (Fin b) ℂ) :
    ‖rightSandwichCLM (a := a) K‖ ≤
      ‖rightGramLiftCLM (I := Fin b) (Fin a)‖ * ‖Kᴴ * K‖ := by
  have hGram : ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K)ᴴ *
      ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K) = rightGramLiftCLM (Fin a) (Kᴴ * K) := by
    simp only [rightGramLiftCLM_apply, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  apply (matrixSandwichCLM_norm_le_gram _).trans
  rw [hGram]
  exact (rightGramLiftCLM (I := Fin b) (Fin a)).le_opNorm (Kᴴ * K)

theorem integrable_left_channel_moment {a b p : ℕ}
    (μ : Measure Ω) (K : Ω → Matrix (Fin p) (Fin a) ℂ)
    (Φ : Ω → JointMatrix p b →L[ℂ] Matrix O O ℂ)
    (hK : Measurable K) (hΦ : AEStronglyMeasurable Φ μ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    {C : ℝ} (hC : 0 ≤ C) (hBound : ∀ᵐ ω ∂μ, ‖Φ ω‖ ≤ C) :
    Integrable (fun ω => (Φ ω).comp (leftSandwichCLM (K ω))) μ := by
  have hSand : AEStronglyMeasurable (fun ω => leftSandwichCLM (b := b) (K ω)) μ :=
    continuous_leftSandwichCLM.comp_aestronglyMeasurable hK.aestronglyMeasurable
  have hComp : Continuous (fun z : (JointMatrix p b →L[ℂ] Matrix O O ℂ) ×
      (JointMatrix a b →L[ℂ] JointMatrix p b) => z.1.comp z.2) :=
    continuous_fst.clm_comp continuous_snd
  have hMeas := hComp.comp_aestronglyMeasurable (hΦ.prodMk hSand)
  refine ⟨hMeas, (hGram.norm.const_mul
    (C * ‖leftGramLiftCLM (I := Fin a) (Fin b)‖)).hasFiniteIntegral.mono'
      (f := fun ω => (Φ ω).comp (leftSandwichCLM (K ω))) ?_⟩
  filter_upwards [hBound] with ω hω
  calc
    ‖(Φ ω).comp (leftSandwichCLM (K ω))‖ ≤ ‖Φ ω‖ * ‖leftSandwichCLM (K ω)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * (‖leftGramLiftCLM (I := Fin a) (Fin b)‖ * ‖(K ω)ᴴ * K ω‖) :=
      mul_le_mul hω (leftSandwichCLM_norm_le_gram _) (norm_nonneg _) hC
    _ = _ := by ring

theorem integrable_right_channel_moment {a b p : ℕ}
    (μ : Measure Ω) (K : Ω → Matrix (Fin p) (Fin b) ℂ)
    (Φ : Ω → JointMatrix a p →L[ℂ] Matrix O O ℂ)
    (hK : Measurable K) (hΦ : AEStronglyMeasurable Φ μ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    {C : ℝ} (hC : 0 ≤ C) (hBound : ∀ᵐ ω ∂μ, ‖Φ ω‖ ≤ C) :
    Integrable (fun ω => (Φ ω).comp (rightSandwichCLM (K ω))) μ := by
  have hSand : AEStronglyMeasurable (fun ω => rightSandwichCLM (a := a) (K ω)) μ :=
    continuous_rightSandwichCLM.comp_aestronglyMeasurable hK.aestronglyMeasurable
  have hComp : Continuous (fun z : (JointMatrix a p →L[ℂ] Matrix O O ℂ) ×
      (JointMatrix a b →L[ℂ] JointMatrix a p) => z.1.comp z.2) :=
    continuous_fst.clm_comp continuous_snd
  have hMeas := hComp.comp_aestronglyMeasurable (hΦ.prodMk hSand)
  refine ⟨hMeas, (hGram.norm.const_mul
    (C * ‖rightGramLiftCLM (I := Fin b) (Fin a)‖)).hasFiniteIntegral.mono'
      (f := fun ω => (Φ ω).comp (rightSandwichCLM (K ω))) ?_⟩
  filter_upwards [hBound] with ω hω
  calc
    ‖(Φ ω).comp (rightSandwichCLM (K ω))‖ ≤ ‖Φ ω‖ * ‖rightSandwichCLM (K ω)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * (‖rightGramLiftCLM (I := Fin b) (Fin a)‖ * ‖(K ω)ᴴ * K ω‖) :=
      mul_le_mul hω (rightSandwichCLM_norm_le_gram _) (norm_nonneg _) hC
    _ = _ := by ring

theorem integrable_left_channel_moment_of_cptp {a b p : ℕ}
    (μ : Measure Ω) (K : Ω → Matrix (Fin p) (Fin a) ℂ)
    (Φ : Ω → JointMatrix p b →L[ℂ] Matrix O O ℂ)
    (hK : Measurable K) (hΦ : AEStronglyMeasurable Φ μ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hCP : ∀ᵐ ω ∂μ, CPWrappers.CompletelyPositive (Φ ω).toLinearMap)
    (hTP : ∀ᵐ ω ∂μ, CPTPKraus.TracePreserving (Φ ω).toLinearMap) :
    Integrable (fun ω => (Φ ω).comp (leftSandwichCLM (K ω))) μ := by
  apply integrable_left_channel_moment μ K Φ hK hΦ hGram
    (Nat.cast_nonneg (Fintype.card (Fin p × Fin b)))
  filter_upwards [hCP, hTP] with ω hCPω hTPω
  exact norm_clm_le_card_of_cptp (Φ ω) hCPω hTPω

theorem integrable_right_channel_moment_of_cptp {a b p : ℕ}
    (μ : Measure Ω) (K : Ω → Matrix (Fin p) (Fin b) ℂ)
    (Φ : Ω → JointMatrix a p →L[ℂ] Matrix O O ℂ)
    (hK : Measurable K) (hΦ : AEStronglyMeasurable Φ μ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hCP : ∀ᵐ ω ∂μ, CPWrappers.CompletelyPositive (Φ ω).toLinearMap)
    (hTP : ∀ᵐ ω ∂μ, CPTPKraus.TracePreserving (Φ ω).toLinearMap) :
    Integrable (fun ω => (Φ ω).comp (rightSandwichCLM (K ω))) μ := by
  apply integrable_right_channel_moment μ K Φ hK hΦ hGram
    (Nat.cast_nonneg (Fintype.card (Fin a × Fin p)))
  filter_upwards [hCP, hTP] with ω hCPω hTPω
  exact norm_clm_le_card_of_cptp (Φ ω) hCPω hTPω

end QuantumProver.WernerEndpoint.ContinuousChannelIntegrability
