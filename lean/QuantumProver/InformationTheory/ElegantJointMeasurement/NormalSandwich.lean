import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped BigOperators InnerProduct ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.NormalSandwich

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def sandwich (L : F →L[ℂ] E) : NormalOperation F E := compose L L.adjoint

@[simp] theorem toOperator_sandwich (L : F →L[ℂ] E) (T : Nuclear F) :
    toOperator (sandwich L T) = L ∘L toOperator T ∘L L.adjoint :=
  toOperator_compose L L.adjoint T

theorem sandwich_isPositive (L : F →L[ℂ] E) (T : Nuclear F)
    (hT : (toOperator T).IsPositive) :
    (toOperator (sandwich L T)).IsPositive := by
  rw [toOperator_sandwich]
  exact hT.conj_adjoint L

variable {R : Type} [Fintype R] [DecidableEq R]

theorem normalAmplification_sandwich (L : F →L[ℂ] E)
    (T : Nuclear (BlockSpace R F)) :
    normalAmplification (sandwich L) T =
      compose (blockLift (R := R) L) (blockLift (R := R) L).adjoint T := by
  apply toOperator_injective
  rw [normalAmplification_apply, toOperator_nuclearAssembly, toOperator_compose,
    blockLift_adjoint]
  ext x r
  simp only [blockOperator_apply, toOperator_sandwich, toOperator_nuclearBlock,
    ContinuousLinearMap.comp_apply, blockLift_apply, PiLp.proj_apply]
  have hx : (∑ s : R, insert (E := F) s (L.adjoint (x s))) =
      blockLift (R := R) L.adjoint x := by
    ext s
    simp [insert_apply_apply, blockLift_apply]
  have he := congrArg (fun z => L ((toOperator T z) r)) hx
  simpa only [map_sum, WithLp.ofLp_sum, Finset.sum_apply, blockLift_apply] using he

theorem normalCompletelyPositive_sandwich (L : F →L[ℂ] E) :
    NormalCompletelyPositive (sandwich L) := by
  intro R _ _ T hT
  rw [normalAmplification_sandwich, toOperator_compose]
  exact hT.conj_adjoint (blockLift (R := R) L)

theorem normalAmplification_comp (Φ : NormalOperation F E) (Ψ : NormalOperation G F)
    (T : Nuclear (BlockSpace R G)) :
    normalAmplification (Φ.comp Ψ) T =
      normalAmplification Φ (normalAmplification Ψ T) := by
  simp only [normalAmplification_apply, nuclearBlock_nuclearAssembly,
    ContinuousLinearMap.comp_apply]

theorem normalCompletelyPositive_comp (Φ : NormalOperation F E) (Ψ : NormalOperation G F)
    (hΦ : NormalCompletelyPositive Φ) (hΨ : NormalCompletelyPositive Ψ) :
    NormalCompletelyPositive (Φ.comp Ψ) := by
  intro R _ _ T hT
  rw [normalAmplification_comp]
  exact hΦ R _ (hΨ R T hT)

end QuantumProver.ElegantJointMeasurement.NormalSandwich
