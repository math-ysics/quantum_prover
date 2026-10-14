import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCost
import QuantumProver.InformationTheory.ElegantJointMeasurement.CommonPhysicalEventTensor

noncomputable section
set_option autoImplicit false

namespace QuantumProver.ElegantJointMeasurement.PhysicalPreparationMarker

open MeasureTheory Set TopologicalSpace
open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalAncillaPreparation QuantumProver.ElegantJointMeasurement.NormalCost
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.MatrixNormalFreePreparationChronology
open QuantumProver.MatrixNormalTensorInstrument QuantumProver.MatrixNormalRightTensor
open QuantumProver.NuclearOperator (toOperator)
open scoped Classical

theorem tensorOperation_eq_of_operation_eq {H S : Type*}
    [MeasurableSpace H] [MeasurableSpace S]
    (A : Instrument QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace H S)
    (h : H) (s t : Set S) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : A.operation h s = A.operation h t) :
    tensorOperation (G := QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace) A h s =
      tensorOperation (G := QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace) A h t := by
  simpa only [tensorInstrument_operation] using
    QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalEventTensor.left_event_transport A A h h s t hs ht hst

theorem rightTensorOperation_eq_of_operation_eq {H S : Type*}
    [MeasurableSpace H] [MeasurableSpace S]
    (A : Instrument QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace H S)
    (h : H) (s t : Set S) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : A.operation h s = A.operation h t) :
    rightTensorOperation (G := QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace) A h s =
      rightTensorOperation (G := QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace) A h t := by
  simpa only [rightTensorInstrument_operation] using
    QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalEventTensor.right_event_transport A A h h s t hs ht hst

theorem tensorOperation_eq_zero_of_operation_eq_zero {H S : Type*}
    [MeasurableSpace H] [MeasurableSpace S]
    (A : Instrument QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace H S)
    (h : H) (s : Set S) (hs : MeasurableSet s) (hz : A.operation h s = 0) :
    tensorOperation (G := QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace) A h s = 0 :=
  (tensorOperation_eq_of_operation_eq A h s ∅ hs MeasurableSet.empty
    (hz.trans (A.empty h).symm)).trans (tensorOperation_empty A h)

theorem rightTensorOperation_eq_zero_of_operation_eq_zero {H S : Type*}
    [MeasurableSpace H] [MeasurableSpace S]
    (A : Instrument QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace H S)
    (h : H) (s : Set S) (hs : MeasurableSet s) (hz : A.operation h s = 0) :
    rightTensorOperation (G := QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace) A h s = 0 :=
  (rightTensorOperation_eq_of_operation_eq A h s ∅ hs MeasurableSet.empty
    (hz.trans (A.empty h).symm)).trans (rightTensorOperation_empty A h)

universe u

private theorem preparationRecord_borel {R : Type u} [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] : BorelSpace (PreparationRecord R) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hl := (measurableSet_sum_iff.mp hs).1
    have hr := (measurableSet_sum_iff.mp hs).2
    letI : MeasurableSpace (PreparationRecord R) := borel (PreparationRecord R)
    letI : BorelSpace (PreparationRecord R) := ⟨rfl⟩
    have he : s = Sum.inl '' (Sum.inl ⁻¹' s) ∪ Sum.inr '' (Sum.inr ⁻¹' s) := by
      ext z
      constructor
      · intro hz
        cases z with
        | inl x => exact Or.inl (mem_image_of_mem Sum.inl hz)
        | inr y => exact Or.inr (mem_image_of_mem Sum.inr hz)
      · rintro (⟨x,hx,rfl⟩ | ⟨y,hy,rfl⟩)
        · exact hx
        · exact hy
    rw [he]
    exact (Topology.IsOpenEmbedding.inl.measurableEmbedding.measurableSet_image' hl).union
      (Topology.IsOpenEmbedding.inr.measurableEmbedding.measurableSet_image' hr)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact measurableSet_sum_iff.mpr
      ⟨(isOpen_sum_iff.mp hs).1.measurableSet, (isOpen_sum_iff.mp hs).2.measurableSet⟩

local instance preparationRecord_standardBorel {R : Type u} [MeasurableSpace R]
    [StandardBorelSpace R] : StandardBorelSpace (PreparationRecord R) := by
  letI := upgradeStandardBorel R
  letI : BorelSpace (PreparationRecord R) := preparationRecord_borel
  infer_instance

section MixedPreparations

variable {a b : ℕ} [NeZero a] [NeZero b]
  {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
  {FA FB : Type*}
  [NormedAddCommGroup FA] [InnerProductSpace ℂ FA] [CompleteSpace FA] [SeparableSpace FA]
  [NormedAddCommGroup FB] [InnerProductSpace ℂ FB] [CompleteSpace FB] [SeparableSpace FB]
  (P : MatrixProcess a b R) (τA : Nuclear FA) (τB : Nuclear FB)
  (hA : (toOperator τA).IsPositive) (hB : (toOperator τB).IsPositive)
  (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
  (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1)

theorem first_marker_step (s : Set (PreparationRecord R)) (hs : MeasurableSet s) :
    ((insertMixedMatrixProcess P τA τB hA hB hAT hBT).represented_physicalStepInstrument 0).operation
      PUnit.unit s =
      if preparationTag ∈ s then
        ((insertMixedMatrixProcess P τA τB hA hB hAT hBT).represented_physicalStepInstrument 0).operation
          PUnit.unit univ else 0 := by
  let A : Instrument QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace
      (History (PreparationRecord R) 0) (PreparationRecord R) :=
    taggedSingleton (R := R) (commonPreparation (E := QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace) τA)
      (commonPreparation_completelyPositive τA hA) (trace_commonPreparation τA hAT)
  change tensorOperation (G := QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace) A PUnit.unit s =
    if preparationTag ∈ s then
      tensorOperation (G := QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace) A PUnit.unit univ else 0
  by_cases ht : preparationTag ∈ s
  · rw [if_pos ht]
    apply tensorOperation_eq_of_operation_eq A PUnit.unit s univ hs MeasurableSet.univ
    simp only [A, taggedSingleton_operation, ht, mem_univ, ite_true]
  · rw [if_neg ht]
    apply tensorOperation_eq_zero_of_operation_eq_zero A PUnit.unit s hs
    simp only [A, taggedSingleton_operation, ht, ite_false]

theorem second_marker_step (s : Set (PreparationRecord R)) (hs : MeasurableSet s) :
    ((insertMixedMatrixProcess P τA τB hA hB hAT hBT).represented_physicalStepInstrument 1).operation
      firstPreparationHistory s =
      if preparationTag ∈ s then
        ((insertMixedMatrixProcess P τA τB hA hB hAT hBT).represented_physicalStepInstrument 1).operation
          firstPreparationHistory univ else 0 := by
  let B := secondPreparation (R := R) (commonPreparation (E := QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace) τB)
    (commonPreparation_completelyPositive τB hB) (trace_commonPreparation τB hBT)
  change rightTensorOperation (G := QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace) B firstPreparationHistory s =
    if preparationTag ∈ s then
      rightTensorOperation (G := QuantumProver.ElegantJointMeasurement.NormalProcess.Workspace) B firstPreparationHistory univ else 0
  by_cases ht : preparationTag ∈ s
  · rw [if_pos ht]
    apply rightTensorOperation_eq_of_operation_eq B firstPreparationHistory s univ hs
      MeasurableSet.univ
    simp only [B, secondPreparation_operation, ht, mem_univ, ite_true]
  · rw [if_neg ht]
    apply rightTensorOperation_eq_zero_of_operation_eq_zero B firstPreparationHistory s hs
    simp only [B, secondPreparation_operation, ht, ite_false]

end MixedPreparations

end QuantumProver.ElegantJointMeasurement.PhysicalPreparationMarker
