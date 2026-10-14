import QuantumProver.LinearAlgebra.CountableGramSchmidt
import QuantumProver.InformationTheory.ElegantJointMeasurement.SeparableHilbertEmbedding

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Classical
open Submodule
open QuantumProver.CountableGramSchmidt
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.NuclearOperator

namespace QuantumProver.CountableFrameProjection

theorem commonBasis_inner (y : CommonHilbert) (n : ℕ) :
    inner ℂ (commonBasis n) y = y n :=
  (commonBasis.repr_apply_apply y n).symm

theorem commonBasis_apply (n m : ℕ) :
    commonBasis n m = if m = n then 1 else 0 := by
  have h : commonBasis n = lp.single 2 n (1 : ℂ) := commonBasis.repr_self n
  rw [h]
  simp only [lp.single_apply, Pi.single_apply]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem coordinateEmbedding_adjoint_commonBasis (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) (n : ℕ) :
    (coordinateEmbedding v hDense).toContinuousLinearMap.adjoint (commonBasis n) =
      frame v n := by
  apply ext_inner_right ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left, commonBasis_inner]
  exact coordinateEmbedding_apply v hDense x n

theorem coordinateEmbedding_frame_eq (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) (n : ℕ) :
    coordinateEmbedding v hDense (frame v n) =
      if frame v n ≠ 0 then commonBasis n else 0 := by
  by_cases h : frame v n = 0
  · simp [h]
  · rw [ite_eq_left h]
    apply lp.ext
    funext m
    rw [coordinateEmbedding_frame, commonBasis_apply]
    simp only [ite_eq_right h]

def rangeProjection (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) :
    CommonHilbert →L[ℂ] CommonHilbert :=
  (coordinateEmbedding v hDense).toContinuousLinearMap.comp
    (coordinateEmbedding v hDense).toContinuousLinearMap.adjoint

theorem rangeProjection_apply_coordinate (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤)
    (y : CommonHilbert) (n : ℕ) :
    rangeProjection v hDense y n = if frame v n ≠ 0 then y n else 0 := by
  change coordinateEmbedding v hDense
    ((coordinateEmbedding v hDense).toContinuousLinearMap.adjoint y) n = _
  rw [coordinateEmbedding_apply, ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (coordinateEmbedding v hDense (frame v n)) y = _
  rw [coordinateEmbedding_frame_eq]
  by_cases h : frame v n ≠ 0
  · rw [ite_eq_left h, ite_eq_left h, commonBasis_inner]
  · rw [ite_eq_right h, ite_eq_right h, inner_zero_left]

theorem rangeProjection_adjoint (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) :
    (rangeProjection v hDense).adjoint = rangeProjection v hDense := by
  simp only [rangeProjection, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem rangeProjection_idempotent (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) :
    (rangeProjection v hDense).comp (rangeProjection v hDense) =
      rangeProjection v hDense := by
  apply ContinuousLinearMap.ext
  intro y
  change coordinateEmbedding v hDense
    ((coordinateEmbedding v hDense).toContinuousLinearMap.adjoint
      (coordinateEmbedding v hDense
        ((coordinateEmbedding v hDense).toContinuousLinearMap.adjoint y))) = _
  rw [adjoint_embedding_apply]
  rfl

theorem rangeProjection_embedding (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) (x : E) :
    rangeProjection v hDense (coordinateEmbedding v hDense x) =
      coordinateEmbedding v hDense x := by
  change coordinateEmbedding v hDense
    ((coordinateEmbedding v hDense).toContinuousLinearMap.adjoint
      (coordinateEmbedding v hDense x)) = _
  rw [adjoint_embedding_apply]

theorem padNuclear_apply_coordinate (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤)
    (T : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear E) (y : CommonHilbert) (n : ℕ) :
    toOperator (padNuclear (coordinateEmbedding v hDense) T) y n =
      inner ℂ (frame v n)
        (toOperator T ((coordinateEmbedding v hDense).toContinuousLinearMap.adjoint y)) := by
  rw [toOperator_padNuclear]
  change coordinateEmbedding v hDense
    (toOperator T ((coordinateEmbedding v hDense).toContinuousLinearMap.adjoint y)) n = _
  exact coordinateEmbedding_apply v hDense _ n

theorem padNuclear_matrix_coordinate (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤)
    (T : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear E) (i j : ℕ) :
    inner ℂ (commonBasis i)
      (toOperator (padNuclear (coordinateEmbedding v hDense) T) (commonBasis j)) =
      inner ℂ (frame v i) (toOperator T (frame v j)) := by
  rw [commonBasis_inner, padNuclear_apply_coordinate,
    coordinateEmbedding_adjoint_commonBasis]

end QuantumProver.CountableFrameProjection
