import QuantumProver.InformationTheory.WernerEndpoint.ContinuousChannelIntegrability
import QuantumProver.LinearAlgebra.SandwichedDPI.TraceNorm

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

namespace QuantumProver.WernerEndpoint.HeterogeneousChannelBound

open LocalChannelMoments ContinuousChannelIntegrability
open QuantumProver.SuperchannelDiscrimination QuantumProver.SandwichedDPI

variable {I J O B Ω : Type*} [Fintype I] [Fintype J] [Fintype O] [Fintype B]
  [DecidableEq I] [DecidableEq J] [DecidableEq O] [DecidableEq B] [MeasurableSpace Ω]

theorem norm_trace_mul_le_norm_mul_traceNorm (S X : Matrix I I ℂ) :
    ‖(S * X).trace‖ ≤ ‖S‖ * traceNorm X := by
  by_cases hS : ‖S‖ = 0
  · have hz : S = 0 := norm_eq_zero.mp hS
    simp [hz]
  · let T : Matrix I I ℂ := ‖S‖⁻¹ • S
    have hT : ‖T‖ ≤ 1 := by
      simp [T, norm_smul, Real.norm_eq_abs, inv_mul_cancel₀ hS]
    have hScale : ‖S‖ • T = S := by
      simp only [T, smul_smul, mul_inv_cancel₀ hS, one_smul]
    have ht : (S * X).trace = ‖S‖ • (T * X).trace := by
      rw [← Matrix.trace_smul, ← Matrix.smul_mul, hScale]
    calc
      ‖(S * X).trace‖ = ‖S‖ * ‖(T * X).trace‖ := by
        rw [ht, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg S)]
      _ ≤ ‖S‖ * traceNorm X := mul_le_mul_of_nonneg_left
        (norm_trace_mul_le_traceNorm T X hT) (norm_nonneg S)

private theorem unitary_norm_le_one (V : Matrix J J ℂ)
    (hV : V ∈ Matrix.unitaryGroup J ℂ) : ‖V‖ ≤ 1 := by
  have hV1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hq : ‖Vᴴ * V‖ ≤ 1 := by
    rw [hV1]
    exact (CStarAlgebra.norm_le_one_iff_of_nonneg (1 : Matrix J J ℂ)
      Matrix.PosSemidef.one.nonneg).mpr le_rfl
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hq
  nlinarith [norm_nonneg V]

theorem traceNorm_sandwich_le_gram (K : Matrix J I ℂ) (X : Matrix I I ℂ) :
    traceNorm (K * X * Kᴴ) ≤ ‖Kᴴ * K‖ * traceNorm X := by
  obtain ⟨V, hV, htrace⟩ := exists_unitary_traceNorm_attainer (K * X * Kᴴ)
  have hVnorm := unitary_norm_le_one V hV
  have hS : ‖Kᴴ * V * K‖ ≤ ‖Kᴴ * K‖ := by
    calc
      ‖Kᴴ * V * K‖ ≤ ‖Kᴴ * V‖ * ‖K‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Kᴴ‖ * ‖V‖) * ‖K‖ := mul_le_mul_of_nonneg_right
        (Matrix.l2_opNorm_mul Kᴴ V) (norm_nonneg K)
      _ ≤ (‖K‖ * 1) * ‖K‖ := by
        rw [Matrix.l2_opNorm_conjTranspose]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hVnorm (norm_nonneg K)) (norm_nonneg K)
      _ = ‖Kᴴ * K‖ := by rw [Matrix.l2_opNorm_conjTranspose_mul_self]; ring
  calc
    traceNorm (K * X * Kᴴ) = (V * (K * X * Kᴴ)).trace.re := htrace.symm
    _ = ((Kᴴ * V * K) * X).trace.re := by
      simpa only [Matrix.mul_assoc] using
        congrArg Complex.re (Matrix.trace_mul_cycle (V * K) X Kᴴ)
    _ ≤ ‖((Kᴴ * V * K) * X).trace‖ := Complex.re_le_norm _
    _ ≤ ‖Kᴴ * V * K‖ * traceNorm X := norm_trace_mul_le_norm_mul_traceNorm _ X
    _ ≤ ‖Kᴴ * K‖ * traceNorm X :=
      mul_le_mul_of_nonneg_right hS (traceNorm_nonneg X)

theorem norm_cptp_comp_sandwich_le_gram
    (Φ : Matrix J J ℂ →L[ℂ] Matrix O O ℂ)
    (hCP : CPWrappers.CompletelyPositive Φ.toLinearMap)
    (hTP : CPTPKraus.TracePreserving Φ.toLinearMap) (K : Matrix J I ℂ) :
    ‖Φ.comp (matrixSandwichCLM K)‖ ≤ (Fintype.card I : ℝ) * ‖Kᴴ * K‖ := by
  apply (Φ.comp (matrixSandwichCLM K)).opNorm_le_bound
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  intro X
  rw [ContinuousLinearMap.comp_apply, matrixSandwichCLM_apply]
  calc
    ‖Φ (K * X * Kᴴ)‖ ≤ traceNorm (Φ (K * X * Kᴴ)) := matrix_norm_le_traceNorm _
    _ ≤ traceNorm (K * X * Kᴴ) := traceNorm_map_le_of_cp_tracePreserving hCP hTP _
    _ ≤ ‖Kᴴ * K‖ * traceNorm X := traceNorm_sandwich_le_gram K X
    _ ≤ ‖Kᴴ * K‖ * ((Fintype.card I : ℝ) * ‖X‖) :=
      mul_le_mul_of_nonneg_left (traceNorm_le_card_mul_matrix_norm X) (norm_nonneg _)
    _ = _ := by ring

theorem norm_cptp_comp_left_sandwich_le_gram
    (Φ : Matrix (J × B) (J × B) ℂ →L[ℂ] Matrix O O ℂ)
    (hCP : CPWrappers.CompletelyPositive Φ.toLinearMap)
    (hTP : CPTPKraus.TracePreserving Φ.toLinearMap) (K : Matrix J I ℂ) :
    ‖Φ.comp (matrixSandwichCLM (K ⊗ₖ (1 : Matrix B B ℂ)))‖ ≤
      ((Fintype.card (I × B) : ℝ) * ‖leftGramLiftCLM (I := I) B‖) * ‖Kᴴ * K‖ := by
  have hGram : (K ⊗ₖ (1 : Matrix B B ℂ))ᴴ * (K ⊗ₖ (1 : Matrix B B ℂ)) =
      leftGramLiftCLM (I := I) B (Kᴴ * K) := by
    simp only [leftGramLiftCLM_apply, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  apply (norm_cptp_comp_sandwich_le_gram Φ hCP hTP _).trans
  rw [hGram]
  calc
    (Fintype.card (I × B) : ℝ) * ‖leftGramLiftCLM B (Kᴴ * K)‖ ≤
        (Fintype.card (I × B) : ℝ) * (‖leftGramLiftCLM (I := I) B‖ * ‖Kᴴ * K‖) :=
      mul_le_mul_of_nonneg_left ((leftGramLiftCLM (I := I) B).le_opNorm (Kᴴ * K))
        (Nat.cast_nonneg _)
    _ = _ := by ring

theorem norm_cptp_comp_right_sandwich_le_gram
    (Φ : Matrix (B × J) (B × J) ℂ →L[ℂ] Matrix O O ℂ)
    (hCP : CPWrappers.CompletelyPositive Φ.toLinearMap)
    (hTP : CPTPKraus.TracePreserving Φ.toLinearMap) (K : Matrix J I ℂ) :
    ‖Φ.comp (matrixSandwichCLM ((1 : Matrix B B ℂ) ⊗ₖ K))‖ ≤
      ((Fintype.card (B × I) : ℝ) * ‖rightGramLiftCLM (I := I) B‖) * ‖Kᴴ * K‖ := by
  have hGram : ((1 : Matrix B B ℂ) ⊗ₖ K)ᴴ * ((1 : Matrix B B ℂ) ⊗ₖ K) =
      rightGramLiftCLM (I := I) B (Kᴴ * K) := by
    simp only [rightGramLiftCLM_apply, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  apply (norm_cptp_comp_sandwich_le_gram Φ hCP hTP _).trans
  rw [hGram]
  calc
    (Fintype.card (B × I) : ℝ) * ‖rightGramLiftCLM B (Kᴴ * K)‖ ≤
        (Fintype.card (B × I) : ℝ) * (‖rightGramLiftCLM (I := I) B‖ * ‖Kᴴ * K‖) :=
      mul_le_mul_of_nonneg_left ((rightGramLiftCLM (I := I) B).le_opNorm (Kᴴ * K))
        (Nat.cast_nonneg _)
    _ = _ := by ring

theorem integrable_varying_cptp_moment {Fiber : Ω → Type*}
    [∀ ω, Fintype (Fiber ω)] [∀ ω, DecidableEq (Fiber ω)]
    (μ : Measure Ω) (K : ∀ ω, Matrix (Fiber ω) I ℂ)
    (Φ : ∀ ω, Matrix (Fiber ω) (Fiber ω) ℂ →L[ℂ] Matrix O O ℂ)
    (hCP : ∀ ω, CPWrappers.CompletelyPositive (Φ ω).toLinearMap)
    (hTP : ∀ ω, CPTPKraus.TracePreserving (Φ ω).toLinearMap)
    (hMoment : AEStronglyMeasurable (fun ω => (Φ ω).comp (matrixSandwichCLM (K ω))) μ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ) :
    Integrable (fun ω => (Φ ω).comp (matrixSandwichCLM (K ω))) μ := by
  refine ⟨hMoment, (hGram.norm.const_mul (Fintype.card I : ℝ)).hasFiniteIntegral.mono'
    (f := fun ω => (Φ ω).comp (matrixSandwichCLM (K ω))) ?_⟩
  exact Filter.Eventually.of_forall fun ω =>
    norm_cptp_comp_sandwich_le_gram (Φ ω) (hCP ω) (hTP ω) (K ω)

end QuantumProver.WernerEndpoint.HeterogeneousChannelBound
