import QuantumProver.InformationTheory.ElegantJointMeasurement.MeasurableHilbertOperator
import QuantumProver.LinearAlgebra.HilbertNuclearCompressionExpansion

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

open MeasureTheory
open QuantumProver.ElegantJointMeasurement.MeasurableHilbertField QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression (compose toOperator_compose)

namespace QuantumProver.ElegantJointMeasurement.MeasurableNuclearField

universe u v
variable {Z : Type u} [MeasurableSpace Z] {E : Z → Type v}
  [∀ z, NormedAddCommGroup (E z)] [∀ z, InnerProductSpace ℂ (E z)]
  [∀ z, CompleteSpace (E z)]

abbrev Nuclear (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] := QuantumProver.NuclearOperator.Nuclear ℂ H H

local instance commonNuclearMeasurable : MeasurableSpace (Nuclear CommonHilbert) :=
  borel (Nuclear CommonHilbert)
local instance commonNuclearBorel : BorelSpace (Nuclear CommonHilbert) := ⟨rfl⟩

def CoefficientsMeasurable (F : FundamentalFamily E) (T : (z : Z) → Nuclear (E z)) : Prop :=
  QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator.CoefficientsMeasurable F F (fun z => toOperator (T z))

def padNuclearField (F : FundamentalFamily E) (T : (z : Z) → Nuclear (E z)) :
    Z → Nuclear CommonHilbert := fun z => padNuclear (F.embedding z) (T z)

def recoverNuclearField (F : FundamentalFamily E) (U : Z → Nuclear CommonHilbert) :
    (z : Z) → Nuclear (E z) := fun z => recoverNuclear (F.embedding z) (U z)

theorem padNuclearField_matrix_coordinate (F : FundamentalFamily E)
    (T : (z : Z) → Nuclear (E z)) (z : Z) (i j : ℕ) :
    inner ℂ (commonBasis i) (toOperator (padNuclearField F T z) (commonBasis j)) =
      inner ℂ (F.frame i z) (toOperator (T z) (F.frame j z)) :=
  QuantumProver.CountableFrameProjection.padNuclear_matrix_coordinate
    (F.vector z) (F.dense z) (T z) i j

theorem stronglyMeasurable_padNuclearField (F : FundamentalFamily E)
    (T : (z : Z) → Nuclear (E z)) (hT : CoefficientsMeasurable F T) :
    StronglyMeasurable (padNuclearField F T) := by
  apply QuantumProver.HilbertNuclearCompressionExpansion.stronglyMeasurable_of_coordinates commonBasis
  intro i j
  have hm := QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator.measurable_matrix_element F F
    (fun z => toOperator (T z)) hT (F.frame j) (F.frame_measurableSection j)
      (F.frame i) (F.frame_measurableSection i)
  have heq : (fun z => inner ℂ (commonBasis i)
      (toOperator (padNuclearField F T z) (commonBasis j))) =
      (fun z => inner ℂ (F.frame i z) (toOperator (T z) (F.frame j z))) :=
    funext (fun z => padNuclearField_matrix_coordinate F T z i j)
  rw [heq]
  exact hm

theorem measurable_padNuclearField (F : FundamentalFamily E)
    (T : (z : Z) → Nuclear (E z)) (hT : CoefficientsMeasurable F T) :
    Measurable (padNuclearField F T) :=
  (stronglyMeasurable_padNuclearField F T hT).measurable

theorem recover_padNuclearField (F : FundamentalFamily E)
    (T : (z : Z) → Nuclear (E z)) (z : Z) :
    recoverNuclearField F (padNuclearField F T) z = T z :=
  recover_padNuclear (F.embedding z) (T z)

theorem norm_padNuclearField (F : FundamentalFamily E)
    (T : (z : Z) → Nuclear (E z)) (z : Z) :
    ‖padNuclearField F T z‖ = ‖T z‖ := norm_padNuclear (F.embedding z) (T z)

theorem trace_padNuclearField (F : FundamentalFamily E)
    (T : (z : Z) → Nuclear (E z)) (z : Z) :
    QuantumProver.HilbertNuclearTrace.trace (padNuclearField F T z) =
      QuantumProver.HilbertNuclearTrace.trace (T z) := trace_padNuclear (F.embedding z) (T z)

theorem padNuclearField_isPositive (F : FundamentalFamily E)
    (T : (z : Z) → Nuclear (E z)) (z : Z) (hT : (toOperator (T z)).IsPositive) :
    (toOperator (padNuclearField F T z)).IsPositive :=
  padNuclear_isPositive (F.embedding z) (T z) hT

theorem coefficientsMeasurable_recoverNuclearField (F : FundamentalFamily E)
    (U : Z → Nuclear CommonHilbert) (hU : StronglyMeasurable U) :
    CoefficientsMeasurable F (recoverNuclearField F U) := by
  intro i j
  have hi := F.stronglyMeasurable_embedding_section _ (F.fundamental_measurableSection i)
  have hj := F.stronglyMeasurable_embedding_section _ (F.fundamental_measurableSection j)
  have hOp : StronglyMeasurable (fun z => toOperator (U z)) :=
    toOperator.continuous.comp_stronglyMeasurable hU
  have hEval : StronglyMeasurable (fun z => toOperator (U z) (F.embedding z (F.vector z j))) :=
    (isBoundedBilinearMap_apply (𝕜 := ℂ)).continuous.comp_stronglyMeasurable (hOp.prodMk hj)
  have hm := (hi.inner (𝕜 := ℂ) hEval).measurable
  simpa only [recoverNuclearField, recoverNuclear, toOperator_compose,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap] using hm

theorem stronglyMeasurable_pad_recoverNuclearField (F : FundamentalFamily E)
    (U : Z → Nuclear CommonHilbert) (hU : StronglyMeasurable U) :
    StronglyMeasurable (padNuclearField F (recoverNuclearField F U)) :=
  stronglyMeasurable_padNuclearField F _ (coefficientsMeasurable_recoverNuclearField F U hU)

theorem coefficientsMeasurable_iff_stronglyMeasurable_pad (F : FundamentalFamily E)
    (T : (z : Z) → Nuclear (E z)) :
    CoefficientsMeasurable F T ↔ StronglyMeasurable (padNuclearField F T) := by
  constructor
  · exact stronglyMeasurable_padNuclearField F T
  · intro h
    have hr := coefficientsMeasurable_recoverNuclearField F (padNuclearField F T) h
    intro i j
    have hm := hr i j
    simpa only [recover_padNuclearField] using hm

theorem norm_recoverNuclearField_le (F : FundamentalFamily E)
    (U : Z → Nuclear CommonHilbert) (z : Z) :
    ‖recoverNuclearField F U z‖ ≤ ‖U z‖ := norm_recoverNuclear_le (F.embedding z) (U z)

theorem recoverNuclearField_isPositive (F : FundamentalFamily E)
    (U : Z → Nuclear CommonHilbert) (z : Z) (hU : (toOperator (U z)).IsPositive) :
    (toOperator (recoverNuclearField F U z)).IsPositive := by
  simp only [recoverNuclearField, recoverNuclear, toOperator_compose]
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    hU.conj_adjoint (F.embedding z).toContinuousLinearMap.adjoint

theorem pad_recover_eq_projection (F : FundamentalFamily E) (z : Z)
    (U : Nuclear CommonHilbert) :
    padNuclear (F.embedding z) (recoverNuclear (F.embedding z) U) =
      compose (F.rangeProjection z) (F.rangeProjection z) U := by
  have hP : F.rangeProjection z = (F.embedding z).toContinuousLinearMap.comp
      (F.embedding z).toContinuousLinearMap.adjoint := rfl
  apply toOperator_injective
  ext x
  simp only [padNuclear, recoverNuclear, toOperator_compose, hP,
    ContinuousLinearMap.comp_apply]

theorem padNuclearField_supported (F : FundamentalFamily E)
    (T : (z : Z) → Nuclear (E z)) (z : Z) :
    compose (F.rangeProjection z) (F.rangeProjection z) (padNuclearField F T z) =
      padNuclearField F T z := by
  rw [← pad_recover_eq_projection]
  exact congrArg (padNuclear (F.embedding z)) (recover_padNuclear (F.embedding z) (T z))

theorem trace_recover_on_support (F : FundamentalFamily E) (z : Z)
    (U : Nuclear CommonHilbert)
    (hU : compose (F.rangeProjection z) (F.rangeProjection z) U = U) :
    QuantumProver.HilbertNuclearTrace.trace (recoverNuclear (F.embedding z) U) =
      QuantumProver.HilbertNuclearTrace.trace U := by
  have hp := pad_recover_eq_projection F z U
  rw [hU] at hp
  have ht := trace_padNuclear (F.embedding z) (recoverNuclear (F.embedding z) U)
  rw [hp] at ht
  exact ht.symm

end QuantumProver.ElegantJointMeasurement.MeasurableNuclearField

namespace QuantumProver.ElegantJointMeasurement.MeasurableNuclearField

open scoped Classical

universe u v
variable {Z : Type u} [MeasurableSpace Z] {E : Z → Type v}
  [∀ z, NormedAddCommGroup (E z)] [∀ z, InnerProductSpace ℂ (E z)]
  [∀ z, CompleteSpace (E z)]

def pureStateField (s : (z : Z) → E z) : (z : Z) → Nuclear (E z) :=
  fun z => QuantumProver.NuclearOperator.rankOne (innerSL ℂ (s z)) (s z)

theorem pureStateField_coefficientsMeasurable (F : FundamentalFamily E)
    (s : (z : Z) → E z) (hs : F.IsMeasurableSection s) :
    CoefficientsMeasurable F (pureStateField s) := by
  intro i j
  have hi := QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator.measurable_inner_sections F
    (F.vector · i) s (F.fundamental_measurableSection i) hs
  have hj := QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator.measurable_inner_sections F
    s (F.vector · j) hs (F.fundamental_measurableSection j)
  have hm : Measurable (fun z : Z =>
      inner ℂ (s z) (F.vector z j) * inner ℂ (F.vector z i) (s z)) :=
    measurable_mul.comp (hj.prodMk hi)
  have heq : (fun z : Z =>
      inner ℂ (F.vector z i) (toOperator (pureStateField s z) (F.vector z j))) =
      (fun z : Z => inner ℂ (s z) (F.vector z j) * inner ℂ (F.vector z i) (s z)) := by
    funext z
    simp only [pureStateField, QuantumProver.NuclearOperator.toOperator_rankOne,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right]
  rw [heq]
  exact hm

theorem stronglyMeasurable_pad_pureStateField (F : FundamentalFamily E)
    (s : (z : Z) → E z) (hs : F.IsMeasurableSection s) :
    StronglyMeasurable (padNuclearField F (pureStateField s)) :=
  stronglyMeasurable_padNuclearField F _ (pureStateField_coefficientsMeasurable F s hs)

theorem pureStateField_isPositive (s : (z : Z) → E z) (z : Z) :
    (toOperator (pureStateField s z)).IsPositive := by
  rw [pureStateField, QuantumProver.NuclearOperator.toOperator_rankOne]
  exact InnerProductSpace.isPositive_rankOne_self (s z)

theorem pureStateField_trace (s : (z : Z) → E z) (z : Z) :
    QuantumProver.HilbertNuclearTrace.trace (pureStateField s z) = (‖s z‖ : ℂ) ^ 2 := by
  rw [pureStateField, QuantumProver.HilbertNuclearTrace.trace_rankOne, innerSL_apply_apply,
    inner_self_eq_norm_sq_to_K]
  rfl

theorem pureStateField_norm (s : (z : Z) → E z) (z : Z) :
    ‖pureStateField s z‖ = ‖s z‖ ^ 2 := by
  rw [pureStateField, QuantumProver.NuclearOperator.norm_rankOne, innerSL_apply_norm, pow_two]

def unitStateField (F : FundamentalFamily E) : (z : Z) → Nuclear (E z) :=
  pureStateField F.unitSection

theorem unitStateField_coefficientsMeasurable (F : FundamentalFamily E) :
    CoefficientsMeasurable F (unitStateField F) :=
  pureStateField_coefficientsMeasurable F F.unitSection F.unitSection_measurableSection

theorem stronglyMeasurable_pad_unitStateField (F : FundamentalFamily E) :
    StronglyMeasurable (padNuclearField F (unitStateField F)) :=
  stronglyMeasurable_pad_pureStateField F F.unitSection F.unitSection_measurableSection

theorem unitStateField_isPositive (F : FundamentalFamily E) (z : Z) :
    (toOperator (unitStateField F z)).IsPositive := pureStateField_isPositive _ z

theorem unitStateField_zero (F : FundamentalFamily E) (z : Z)
    (hz : ¬ F.NonzeroFiber z) : unitStateField F z = 0 := by
  apply toOperator_injective
  ext x
  simp only [unitStateField, pureStateField, QuantumProver.NuclearOperator.toOperator_rankOne,
    F.unitSection_zero z hz, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, inner_zero_left, zero_smul, map_zero, zero_apply]

theorem unitStateField_trace (F : FundamentalFamily E) (z : Z) :
    QuantumProver.HilbertNuclearTrace.trace (unitStateField F z) =
      if F.NonzeroFiber z then 1 else 0 := by
  classical
  by_cases hz : F.NonzeroFiber z
  · rw [unitStateField, pureStateField_trace, F.unitSection_norm z hz]
    simp only [Complex.ofReal_one, one_pow, ite_eq_left hz]
  · rw [unitStateField_zero F z hz]
    simp only [map_zero, ite_eq_right hz]

theorem unitStateField_norm_le_one (F : FundamentalFamily E) (z : Z) :
    ‖unitStateField F z‖ ≤ 1 := by
  by_cases hz : F.NonzeroFiber z
  · rw [unitStateField, pureStateField_norm, F.unitSection_norm z hz]
    norm_num
  · rw [unitStateField_zero F z hz, norm_zero]
    exact zero_le_one

end QuantumProver.ElegantJointMeasurement.MeasurableNuclearField
