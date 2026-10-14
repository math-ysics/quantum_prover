import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCost
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPreparedChronology
import QuantumProver.InformationTheory.WernerEndpoint.CommonPhysicalRealization
import QuantumProver.InformationTheory.ElegantJointMeasurement.CommonPhysicalChronology
import QuantumProver.InformationTheory.ElegantJointMeasurement.CommonPhysicalQuantumOutput
import QuantumProver.InformationTheory.ElegantJointMeasurement.PhysicalPreparationMarker
import QuantumProver.InformationTheory.ElegantJointMeasurement.PreparationHistoryCoding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace QuantumProver.ElegantJointMeasurement.PhysicalFreePreparationSerialization

open MeasureTheory ProbabilityTheory Set Function InnerProductSpace TopologicalSpace Preorder
open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
open QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM (Transcript prefix_extension_unique)
open QuantumProver.ElegantJointMeasurement.NormalPreparedChronology
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalAncillaPreparation
open QuantumProver.ElegantJointMeasurement.NormalSandwich QuantumProver.ElegantJointMeasurement.NormalCost
open QuantumProver.MatrixNormalFreePreparationChronology
open QuantumProver.NuclearOperator (toOperator)
open scoped BigOperators Topology ComplexOrder Classical

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

instance preparationRecord_standardBorel {R : Type u} [MeasurableSpace R]
    [StandardBorelSpace R] : StandardBorelSpace (PreparationRecord R) := by
  letI := upgradeStandardBorel R
  letI : BorelSpace (PreparationRecord R) := preparationRecord_borel
  infer_instance

section MixedOperation

variable {FA FB : Type*}
  [NormedAddCommGroup FA] [InnerProductSpace ℂ FA] [CompleteSpace FA] [SeparableSpace FA]
  [NormedAddCommGroup FB] [InnerProductSpace ℂ FB] [CompleteSpace FB] [SeparableSpace FB]
  (τA : Nuclear FA) (τB : Nuclear FB)
  (hA : (toOperator τA).IsPositive) (hB : (toOperator τB).IsPositive)
  (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
  (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1)

theorem mixedJointPreparation_completelyPositive :
    NormalCompletelyPositive (mixedJointPreparation τA τB hA hB hAT hBT) := by
  unfold mixedJointPreparation
  apply normalCompletelyPositive_comp
  · exact QuantumProver.MatrixNormalRightTensor.extendRight_completelyPositive _ _ _
  · exact QuantumProver.MatrixNormalTensorExtension.extendLeft_completelyPositive _ _ _

theorem mixedJointPreparation_trace (T : Nuclear JointWorkspace) :
    QuantumProver.HilbertNuclearTrace.trace (mixedJointPreparation τA τB hA hB hAT hBT T) =
      QuantumProver.HilbertNuclearTrace.trace T := by
  unfold mixedJointPreparation
  simp only [ContinuousLinearMap.comp_apply]
  rw [QuantumProver.MatrixNormalRightTensor.trace_extendRight _ _ _ (trace_commonPreparation τB hBT),
    QuantumProver.MatrixNormalTensorExtension.trace_extendLeft _ _ _ (trace_commonPreparation τA hAT)]

end MixedOperation

section PreparedInitialLayer

variable {a b : ℕ} [NeZero a] [NeZero b]
  {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
  {FA FB : Type*}
  [NormedAddCommGroup FA] [InnerProductSpace ℂ FA] [CompleteSpace FA] [SeparableSpace FA]
  [NormedAddCommGroup FB] [InnerProductSpace ℂ FB] [CompleteSpace FB] [SeparableSpace FB]
  (P : MatrixProcess a b R)
  (τA : Nuclear FA) (τB : Nuclear FB)
  (hA : (toOperator τA).IsPositive) (hB : (toOperator τB).IsPositive)
  (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
  (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1)

def preparedInitialAction : PhysicalOperation (Fin a × Fin b) JointWorkspace :=
  (mixedJointPreparation τA τB hA hB hAT hBT).comp P.initialJointOperation

theorem preparedInitialAction_apply (X : JointInputMatrix a b) :
    preparedInitialAction P τA τB hA hB hAT hBT X =
      mixedJointPreparation τA τB hA hB hAT hBT (P.initialJointOperation X) := rfl

theorem preparedInitialAction_trace (X : JointInputMatrix a b) :
    QuantumProver.HilbertNuclearTrace.trace (preparedInitialAction P τA τB hA hB hAT hBT X) =
      X.trace := by
  rw [preparedInitialAction_apply, mixedJointPreparation_trace]
  exact P.initialJointOperation_trace X

def preparedChoiState : Nuclear (PhysicalChoiWorkspace a b) :=
  normalAmplification (R := Fin a × Fin b)
    (mixedJointPreparation τA τB hA hB hAT hBT) P.initialChoiState

theorem preparedChoiState_positive :
    (toOperator (preparedChoiState P τA τB hA hB hAT hBT)).IsPositive :=
  mixedJointPreparation_completelyPositive τA τB hA hB hAT hBT
    (Fin a × Fin b) P.initialChoiState P.initialChoiState_isPositive

theorem preparedChoiState_trace :
    QuantumProver.HilbertNuclearTrace.trace (preparedChoiState P τA τB hA hB hAT hBT) = 1 := by
  rw [preparedChoiState,
    QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.trace_normalAmplification _
      (mixedJointPreparation_trace τA τB hA hB hAT hBT)]
  exact P.initialChoiState_trace

theorem chargedDecode_initialChoiState (X : JointInputMatrix a b) :
    chargedDecode X P.initialChoiState = P.initialJointOperation X := by
  have hc : (Fintype.card (Fin a × Fin b) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Fin a × Fin b)
  change (Fintype.card (Fin a × Fin b) : ℂ) • nuclearDecode X P.initialChoiState = _
  rw [MatrixProcess.initialChoiState, map_smul, nuclearDecode_nuclearChoi, smul_smul]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast, mul_inv_cancel₀ hc, one_smul]

theorem chargedDecode_preparedChoiState (X : JointInputMatrix a b) :
    chargedDecode X (preparedChoiState P τA τB hA hB hAT hBT) =
      preparedInitialAction P τA τB hA hB hAT hBT X := by
  rw [preparedChoiState, chargedDecode_normalAmplification, chargedDecode_initialChoiState]
  rfl

def preparedPhysicalStateLayer :
    MatrixProcess.PhysicalStateLayer (a := a) (b := b) (R := R) 0 where
  state _ := preparedChoiState P τA τB hA hB hAT hBT
  stronglyMeasurable_state := stronglyMeasurable_const
  positive _ := preparedChoiState_positive P τA τB hA hB hAT hBT
  trace_one _ := preparedChoiState_trace P τA τB hA hB hAT hBT

@[simp] theorem preparedPhysicalStateLayer_state (h : History R 0) :
    (preparedPhysicalStateLayer P τA τB hA hB hAT hBT).state h =
      preparedChoiState P τA τB hA hB hAT hBT := rfl

abbrev serialized :=
  insertMixedMatrixProcess P τA τB hA hB hAT hBT

theorem serialized_initialAlice :
    (serialized P τA τB hA hB hAT hBT).initialAlice = P.initialAlice :=
  insertMixedMatrixProcess_initialAlice P τA τB hA hB hAT hBT

theorem serialized_initialBob :
    (serialized P τA τB hA hB hAT hBT).initialBob = P.initialBob :=
  insertMixedMatrixProcess_initialBob P τA τB hA hB hAT hBT

theorem serialized_prefix_two (X : JointInputMatrix a b) :
    (serialized P τA τB hA hB hAT hBT).represented_physicalPrefixAction 2 {preparationHistory} X =
      preparedInitialAction P τA τB hA hB hAT hBT X :=
  insertMixedMatrixProcess_physicalPrefix_two P τA τB hA hB hAT hBT X

theorem serialized_initialChoiState :
    (serialized P τA τB hA hB hAT hBT).initialChoiState = P.initialChoiState := rfl

theorem serialized_first_marker_step (s : Set (PreparationRecord R)) (hs : MeasurableSet s) :
    ((serialized P τA τB hA hB hAT hBT).represented_physicalStepInstrument 0).operation
      PUnit.unit s =
      if preparationTag ∈ s then
        ((serialized P τA τB hA hB hAT hBT).represented_physicalStepInstrument 0).operation PUnit.unit univ
      else 0 :=
  QuantumProver.ElegantJointMeasurement.PhysicalPreparationMarker.first_marker_step P τA τB hA hB hAT hBT s hs

theorem serialized_second_marker_step (s : Set (PreparationRecord R)) (hs : MeasurableSet s) :
    ((serialized P τA τB hA hB hAT hBT).represented_physicalStepInstrument 1).operation
      firstPreparationHistory s =
      if preparationTag ∈ s then
        ((serialized P τA τB hA hB hAT hBT).represented_physicalStepInstrument 1).operation
          firstPreparationHistory univ else 0 :=
  QuantumProver.ElegantJointMeasurement.PhysicalPreparationMarker.second_marker_step P τA τB hA hB hAT hBT s hs

theorem serialized_first_marker_reference (s : Set (PreparationRecord R)) (hs : MeasurableSet s) :
    ((serialized P τA τB hA hB hAT hBT).represented_physicalReferenceInstrument 0).operation
      PUnit.unit s =
      if preparationTag ∈ s then
        ((serialized P τA τB hA hB hAT hBT).represented_physicalReferenceInstrument 0).operation
          PUnit.unit univ else 0 := by
  by_cases ht : preparationTag ∈ s
  · rw [if_pos ht]
    ext U
    change normalAmplification _ U = normalAmplification _ U
    rw [serialized_first_marker_step P τA τB hA hB hAT hBT s hs, if_pos ht]
  · rw [if_neg ht]
    ext U
    change normalAmplification _ U = 0
    rw [serialized_first_marker_step P τA τB hA hB hAT hBT s hs, if_neg ht]
    simp [normalAmplification]

theorem serialized_second_marker_reference (s : Set (PreparationRecord R)) (hs : MeasurableSet s) :
    ((serialized P τA τB hA hB hAT hBT).represented_physicalReferenceInstrument 1).operation
      firstPreparationHistory s =
      if preparationTag ∈ s then
        ((serialized P τA τB hA hB hAT hBT).represented_physicalReferenceInstrument 1).operation
          firstPreparationHistory univ else 0 := by
  by_cases ht : preparationTag ∈ s
  · rw [if_pos ht]
    ext U
    change normalAmplification _ U = normalAmplification _ U
    rw [serialized_second_marker_step P τA τB hA hB hAT hBT s hs, if_pos ht]
  · rw [if_neg ht]
    ext U
    change normalAmplification _ U = 0
    rw [serialized_second_marker_step P τA τB hA hB hAT hBT s hs, if_neg ht]
    simp [normalAmplification]

theorem serialized_first_bornKernel :
    (serialized P τA τB hA hB hAT hBT).represented_physicalBornKernel 0 PUnit.unit =
      Measure.dirac (preparationTag (R := R)) := by
  ext s hs
  rw [MatrixProcess.physicalBornKernel_apply _ _ _ _ hs,
    serialized_first_marker_reference P τA τB hA hB hAT hBT s hs]
  split_ifs with ht
  · rw [((serialized P τA τB hA hB hAT hBT).represented_physicalReferenceInstrument 0).trace_preserving,
      MatrixProcess.physicalState_trace]
    simp [Measure.dirac_apply' _ hs, ht]
  · simp [Measure.dirac_apply' _ hs, ht]

theorem serialized_second_bornKernel :
    (serialized P τA τB hA hB hAT hBT).represented_physicalBornKernel 1 firstPreparationHistory =
      Measure.dirac (preparationTag (R := R)) := by
  ext s hs
  rw [MatrixProcess.physicalBornKernel_apply _ _ _ _ hs,
    serialized_second_marker_reference P τA τB hA hB hAT hBT s hs]
  split_ifs with ht
  · rw [((serialized P τA τB hA hB hAT hBT).represented_physicalReferenceInstrument 1).trace_preserving,
      MatrixProcess.physicalState_trace]
    simp [Measure.dirac_apply' _ hs, ht]
  · simp [Measure.dirac_apply' _ hs, ht]

theorem serialized_first_state :
    (serialized P τA τB hA hB hAT hBT).represented_physicalState 1 firstPreparationHistory =
      ((serialized P τA τB hA hB hAT hBT).represented_physicalReferenceInstrument 0).operation
        PUnit.unit {preparationTag} P.initialChoiState := by
  have he := (serialized P τA τB hA hB hAT hBT).represented_physicalState_successor_setIntegral
    0 PUnit.unit {preparationTag} measurableSet_preparationTag
  rw [serialized_first_bornKernel P τA τB hA hB hAT hBT] at he
  rw [setIntegral_dirac] at he
  simp only [mem_singleton_iff, ite_true] at he
  have hh : appendHistory (R := PreparationRecord R) 0 (PUnit.unit, preparationTag) =
      firstPreparationHistory := rfl
  rw [hh] at he
  have hz : (serialized P τA τB hA hB hAT hBT).represented_physicalState 0 PUnit.unit =
      P.initialChoiState := serialized_initialChoiState P τA τB hA hB hAT hBT
  rw [hz] at he
  exact he

theorem serialized_state_two :
    (serialized P τA τB hA hB hAT hBT).represented_physicalState 2 preparationHistory =
      preparedChoiState P τA τB hA hB hAT hBT := by
  have he := (serialized P τA τB hA hB hAT hBT).represented_physicalState_successor_setIntegral
    1 firstPreparationHistory {preparationTag} measurableSet_preparationTag
  rw [serialized_second_bornKernel P τA τB hA hB hAT hBT] at he
  rw [setIntegral_dirac] at he
  have he' :
      (serialized P τA τB hA hB hAT hBT).represented_physicalState 2 preparationHistory =
      ((serialized P τA τB hA hB hAT hBT).represented_physicalReferenceInstrument 1).operation
        firstPreparationHistory {preparationTag}
        ((serialized P τA τB hA hB hAT hBT).represented_physicalState 1 firstPreparationHistory) := by
    simpa only [mem_singleton_iff, ite_true, preparationHistory] using he
  rw [he', serialized_first_state P τA τB hA hB hAT hBT]
  have hj :
      (((serialized P τA τB hA hB hAT hBT).represented_physicalStepInstrument 1).operation
        firstPreparationHistory {preparationTag}).comp
        (((serialized P τA τB hA hB hAT hBT).represented_physicalStepInstrument 0).operation
          PUnit.unit {preparationTag}) = mixedJointPreparation τA τB hA hB hAT hBT := by
    ext T
    exact insertMixedMatrixProcess_preparation_singletons P τA τB hA hB hAT hBT T
  change normalAmplification _ (normalAmplification _ P.initialChoiState) = _
  rw [← normalAmplification_comp, hj]
  rfl

theorem serialized_prefixMeasure_one :
    (serialized P τA τB hA hB hAT hBT).represented_physicalPrefixMeasure 1 =
      Measure.dirac (firstPreparationHistory (R := R)) := by
  letI : IsMarkovKernel ((serialized P τA τB hA hB hAT hBT).represented_physicalBornKernel 0) :=
    (serialized P τA τB hA hB hAT hBT).represented_physicalBornKernel_markov 0
  ext s hs
  rw [MatrixProcess.represented_physicalPrefixMeasure, Measure.map_apply (appendHistory 0).measurable hs,
    MatrixProcess.represented_physicalPrefixMeasure, Measure.dirac_compProd_apply
      (hs.preimage (appendHistory 0).measurable),
    serialized_first_bornKernel P τA τB hA hB hAT hBT]
  simp [Measure.dirac_apply' _ hs, firstPreparationHistory, appendHistory,
    Set.indicator, Set.mem_preimage]

theorem serialized_prefixMeasure_two :
    (serialized P τA τB hA hB hAT hBT).represented_physicalPrefixMeasure 2 =
      Measure.dirac (preparationHistory (R := R)) := by
  letI : IsMarkovKernel ((serialized P τA τB hA hB hAT hBT).represented_physicalBornKernel 1) :=
    (serialized P τA τB hA hB hAT hBT).represented_physicalBornKernel_markov 1
  ext s hs
  rw [MatrixProcess.represented_physicalPrefixMeasure,
    serialized_prefixMeasure_one P τA τB hA hB hAT hBT,
    Measure.map_apply (appendHistory 1).measurable hs,
    Measure.dirac_compProd_apply (hs.preimage (appendHistory 1).measurable),
    serialized_second_bornKernel P τA τB hA hB hAT hBT]
  simp [Measure.dirac_apply' _ hs, preparationHistory, Set.indicator, Set.mem_preimage]

theorem serialized_prefixMeasure_two_map :
    (serialized P τA τB hA hB hAT hBT).represented_physicalPrefixMeasure 2 =
      (Measure.dirac PUnit.unit : Measure (History R 0)).map (padHistory 0) := by
  rw [serialized_prefixMeasure_two P τA τB hA hB hAT hBT]
  simp only [Measure.map_dirac, padHistory]

theorem serialized_state_two_layer :
    (serialized P τA τB hA hB hAT hBT).represented_physicalState 2 preparationHistory =
      (preparedPhysicalStateLayer P τA τB hA hB hAT hBT).state PUnit.unit :=
  serialized_state_two P τA τB hA hB hAT hBT

theorem serialized_all_event_step (n : ℕ) (h : History R n)
    (s : Set (PreparationRecord R)) (hs : MeasurableSet s) :
    ((serialized P τA τB hA hB hAT hBT).represented_physicalStepInstrument (n+2)).operation
      (padHistory n h) s =
      (P.represented_physicalStepInstrument n).operation h (Sum.inr ⁻¹' s) := by
  have hi : MeasurableSet (Sum.inr ⁻¹' s : Set R) := hs.preimage measurable_inr
  change rawEventAction (insertMixedPreparation (matrixRawFamilies P) τA τB hA hB hAT hBT)
    (n+2) (padHistory n h) s = rawEventAction (matrixRawFamilies P) n h (Sum.inr ⁻¹' s)
  by_cases ht : P.aliceTurn n h = true
  · simp only [rawEventAction, insertMixedPreparation, insertLocalPreparations,
      shiftedParty_padHistory, matrixRawFamilies, ht, ite_true]
    rw [QuantumProver.MatrixNormalTensorInstrument.tensorOperation_of_measurable _ _ _ hs,
      QuantumProver.MatrixNormalTensorInstrument.tensorOperation_of_measurable _ _ _ hi]
    simp only [shiftedInstrument_operation]
  · simp only [rawEventAction, insertMixedPreparation, insertLocalPreparations,
      shiftedParty_padHistory, matrixRawFamilies, ht, ite_false]
    rw [QuantumProver.MatrixNormalRightTensor.rightTensorOperation_of_measurable _ _ _ hs,
      QuantumProver.MatrixNormalRightTensor.rightTensorOperation_of_measurable _ _ _ hi]
    simp only [shiftedInstrument_operation, Bool.false_eq_true, ite_false]

theorem serialized_all_event_reference (n : ℕ) (h : History R n)
    (s : Set (PreparationRecord R)) (hs : MeasurableSet s) :
    ((serialized P τA τB hA hB hAT hBT).represented_physicalReferenceInstrument (n+2)).operation
      (padHistory n h) s =
      (P.represented_physicalReferenceInstrument n).operation h (Sum.inr ⁻¹' s) := by
  ext U
  change normalAmplification _ U = normalAmplification _ U
  rw [serialized_all_event_step P τA τB hA hB hAT hBT n h s hs]

def preparedPrefixAction (n : ℕ) (s : Set (History R n)) (X : JointInputMatrix a b) :
    Nuclear JointWorkspace :=
  seededPrefixAction P (preparedPhysicalStateLayer P τA τB hA hB hAT hBT) n s X

theorem preparedPrefixAction_serialized (n : ℕ) (s : Set (History R n))
    (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    preparedPrefixAction P τA τB hA hB hAT hBT n s X =
      (serialized P τA τB hA hB hAT hBT).represented_physicalPrefixAction (n+2) (padHistory n '' s) X :=
  seededPrefixAction_shift P (serialized P τA τB hA hB hAT hBT)
    (preparedPhysicalStateLayer P τA τB hA hB hAT hBT)
    (serialized_prefixMeasure_two P τA τB hA hB hAT hBT)
    (serialized_state_two_layer P τA τB hA hB hAT hBT)
    (serialized_all_event_reference P τA τB hA hB hAT hBT) n s hs X

theorem preparedPrefixAction_serialized_preimage (n : ℕ)
    (s : Set (History (PreparationRecord R) (n+2))) (hs : MeasurableSet s)
    (X : JointInputMatrix a b) :
    preparedPrefixAction P τA τB hA hB hAT hBT n (padHistory n ⁻¹' s) X =
      (serialized P τA τB hA hB hAT hBT).represented_physicalPrefixAction (n+2) s X := by
  have he := seeded_prefix_setIntegral_shift P (serialized P τA τB hA hB hAT hBT)
    (preparedPhysicalStateLayer P τA τB hA hB hAT hBT)
    (serialized_prefixMeasure_two P τA τB hA hB hAT hBT)
    (serialized_state_two_layer P τA τB hA hB hAT hBT)
    (serialized_all_event_reference P τA τB hA hB hAT hBT) n s hs
  change chargedDecode X (seededPrefixVectorMeasure P
      (preparedPhysicalStateLayer P τA τB hA hB hAT hBT) n (padHistory n ⁻¹' s)) =
    chargedDecode X ((serialized P τA τB hA hB hAT hBT).represented_physicalPrefixVectorMeasure (n+2) s)
  rw [seededPrefixVectorMeasure_apply P _ n _
      (hs.preimage (measurableEmbedding_padHistory n).measurable),
    MatrixProcess.represented_physicalPrefixVectorMeasure_apply _ _ _ hs, he]

theorem preparedPrefixAction_trace_univ (n : ℕ) (X : JointInputMatrix a b) :
    QuantumProver.HilbertNuclearTrace.trace (preparedPrefixAction P τA τB hA hB hAT hBT n univ X) =
      X.trace := by
  apply seededPrefixAction_trace_univ P (preparedPhysicalStateLayer P τA τB hA hB hAT hBT)
  intro Y
  rw [preparedPhysicalStateLayer_state, chargedDecode_preparedChoiState]
  exact preparedInitialAction_trace P τA τB hA hB hAT hBT Y

theorem serialized_prefixMeasure_shift (n : ℕ) :
    (serialized P τA τB hA hB hAT hBT).represented_physicalPrefixMeasure (n+2) =
      (seededPrefixMeasure P (preparedPhysicalStateLayer P τA τB hA hB hAT hBT) n).map
        (padHistory n) :=
  seededPrefixMeasure_shift P (serialized P τA τB hA hB hAT hBT)
    (preparedPhysicalStateLayer P τA τB hA hB hAT hBT)
    (serialized_prefixMeasure_two P τA τB hA hB hAT hBT)
    (serialized_state_two_layer P τA τB hA hB hAT hBT)
    (serialized_all_event_reference P τA τB hA hB hAT hBT) n

theorem serialized_quantum_output {c d : ℕ} (n : ℕ)
    (Q : NormalTerminal (PreparationRecord R) (n+2) c d) (X : JointInputMatrix a b) :
    (serialized P τA τB hA hB hAT hBT).represented_physicalQuantumOutput (n+2) Q X =
      seededQuantumOutput P (preparedPhysicalStateLayer P τA τB hA hB hAT hBT)
        n (pullbackShiftedTerminal n Q) X :=
  seededQuantumOutput_shift P (serialized P τA τB hA hB hAT hBT)
    (preparedPhysicalStateLayer P τA τB hA hB hAT hBT)
    (serialized_prefixMeasure_two P τA τB hA hB hAT hBT)
    (serialized_state_two_layer P τA τB hA hB hAT hBT)
    (serialized_all_event_reference P τA τB hA hB hAT hBT) n Q X

def physicalMixedPreparation :
    MatrixProcess a b (QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.CommonRecord
      (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes (PreparationRecord R))) :=
  QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.realization
    (serialized P τA τB hA hB hAT hBT)

theorem physicalMixedPreparation_initialAlice :
    (physicalMixedPreparation P τA τB hA hB hAT hBT).initialAlice = P.initialAlice := by
  rw [physicalMixedPreparation,
    QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.realization_initialAlice,
    serialized_initialAlice]

theorem physicalMixedPreparation_initialBob :
    (physicalMixedPreparation P τA τB hA hB hAT hBT).initialBob = P.initialBob := by
  rw [physicalMixedPreparation,
    QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.realization_initialBob,
    serialized_initialBob]

def preparedSingletonResponse : (n : ℕ) → History R n → JointInputMatrix a b →
    Nuclear JointWorkspace
  | 0, _, X => preparedInitialAction P τA τB hA hB hAT hBT X
  | n+1, h, X =>
      let z := (appendHistory n).symm h
      (P.represented_physicalStepInstrument n).operation z.1 {z.2}
        (preparedSingletonResponse n z.1 X)

theorem serialized_singleton_prefix (n : ℕ) (h : History R n)
    (X : JointInputMatrix a b) :
    (serialized P τA τB hA hB hAT hBT).represented_physicalPrefixAction (n+2) {padHistory n h} X =
      preparedSingletonResponse P τA τB hA hB hAT hBT n h X := by
  induction n with
  | zero =>
      exact serialized_prefix_two P τA τB hA hB hAT hBT X
  | succ n ih =>
      let z := (appendHistory n).symm h
      have hz : appendHistory n z = h := (appendHistory n).apply_symm_apply h
      rw [← hz, padHistory_append]
      change (serialized P τA τB hA hB hAT hBT).represented_physicalPrefixAction (n+2+1)
        {appendHistory (n+2) (padHistory n z.1, Sum.inr z.2)} X = _
      rw [MatrixProcess.physicalPrefixAction_singleton_successor]
      have hstep := insertMixedMatrixProcess_physicalStep P τA τB hA hB hAT hBT
        n z.1 {z.2} (measurableSet_singleton z.2)
      simp only [Set.image_singleton] at hstep
      rw [hstep, ih]
      simp only [preparedSingletonResponse, MeasurableEquiv.symm_apply_apply]

end PreparedInitialLayer

section TranscriptCoding

variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]

def paddedTranscript (ω : Transcript R) : Transcript (PreparationRecord R) :=
  fun n => if n < 2 then preparationTag else Sum.inr (ω (n-2))

theorem measurable_paddedTranscript :
    Measurable (paddedTranscript (R := R)) := by
  apply measurable_pi_lambda
  intro n
  by_cases hn : n < 2
  · simp only [paddedTranscript, hn, ite_true]
    exact measurable_const
  · simp only [paddedTranscript, hn, ite_false]
    exact measurable_inr.comp (measurable_pi_apply (n-2))

theorem paddedTranscript_injective : Injective (paddedTranscript (R := R)) := by
  intro ω η h
  funext n
  have hn : ¬ n+2 < 2 := by omega
  have he := congrFun h (n+2)
  simpa only [paddedTranscript, hn, ite_false, Nat.add_sub_cancel,
    Sum.inr.injEq] using he

theorem measurableEmbedding_paddedTranscript :
    MeasurableEmbedding (paddedTranscript (R := R)) :=
  measurable_paddedTranscript.measurableEmbedding paddedTranscript_injective

theorem padHistory_physical_coordinate (n : ℕ) (h : Prefix R n) (i : Finset.Iic n) :
    padHistory (n+1) h ⟨i.val+2, Finset.mem_Iic.mpr (by
      have hi := Finset.mem_Iic.mp i.property
      omega)⟩ = Sum.inr (h i) :=
  QuantumProver.ElegantJointMeasurement.HilbertPreparationHistoryCoding.padHistory_physical_coordinate n h i

variable {a b : ℕ} [NeZero a] [NeZero b] (P : MatrixProcess a b R)

def physicalRecordOfPrepared : PreparationRecord R → R :=
  Sum.elim (fun _ => Classical.choice P.record_nonempty) id

theorem measurable_physicalRecordOfPrepared :
    Measurable (physicalRecordOfPrepared P) :=
  measurable_const.sumElim measurable_id

def dropPreparationTranscript (ω : Transcript (PreparationRecord R)) : Transcript R :=
  fun n => physicalRecordOfPrepared P (ω (n+2))

def physicalPrefixOfPrepared (N : ℕ) (h : Prefix (PreparationRecord R) (N+2)) : Prefix R N :=
  fun i => physicalRecordOfPrepared P (h ⟨i.val+2, Finset.mem_Iic.mpr (by
    have hi := Finset.mem_Iic.mp i.property
    omega)⟩)

theorem measurable_physicalPrefixOfPrepared (N : ℕ) :
    Measurable (physicalPrefixOfPrepared P N) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_physicalRecordOfPrepared P).comp (measurable_pi_apply _)

@[simp] theorem physicalPrefixOfPrepared_padHistory (N : ℕ) (h : Prefix R N) :
    physicalPrefixOfPrepared P N (padHistory (N+1) h) = h := by
  funext i
  rw [physicalPrefixOfPrepared, padHistory_physical_coordinate]
  rfl

theorem physicalPrefixOfPrepared_restrict (N : ℕ) (ω : Transcript (PreparationRecord R)) :
    physicalPrefixOfPrepared P N (frestrictLe (π := fun _ => PreparationRecord R) (N+2) ω) =
      frestrictLe (π := fun _ => R) N (dropPreparationTranscript P ω) := rfl

def dropPreparedHistory : (n : ℕ) → History (PreparationRecord R) (n+2) → History R n
  | 0, _ => PUnit.unit
  | n+1, h => physicalPrefixOfPrepared P n h

theorem measurable_dropPreparedHistory (n : ℕ) :
    Measurable (dropPreparedHistory P n) := by
  cases n with
  | zero => exact measurable_const
  | succ n => exact measurable_physicalPrefixOfPrepared P n

@[simp] theorem dropPreparedHistory_padHistory (n : ℕ) (h : History R n) :
    dropPreparedHistory P n (padHistory n h) = h := by
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n => exact physicalPrefixOfPrepared_padHistory P n h

def liftPreparedTerminal {c d : ℕ} (n : ℕ) (Q : NormalTerminal R n c d) :
    NormalTerminal (PreparationRecord R) (n+2) c d where
  alice := QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization.pullbackTerminalInstrument
    Q.alice (dropPreparedHistory P n) (measurable_dropPreparedHistory P n)
  bob := QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization.pullbackTerminalInstrument
    Q.bob (dropPreparedHistory P n) (measurable_dropPreparedHistory P n)

theorem terminalJointOperation_liftPreparedTerminal {c d : ℕ} (n : ℕ)
    (Q : NormalTerminal R n c d) (h : History R n) :
    terminalJointOperation (liftPreparedTerminal P n Q) (padHistory n h) =
      terminalJointOperation Q h := by
  simp only [terminalJointOperation,
    QuantumProver.MatrixNormalTensorInstrument.tensorOperation_of_measurable _ _ _
      MeasurableSet.univ,
    QuantumProver.MatrixNormalRightTensor.rightTensorOperation_of_measurable _ _ _
      MeasurableSet.univ,
    liftPreparedTerminal,
    QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization.pullbackTerminalInstrument_operation,
    dropPreparedHistory_padHistory]

def serializedTerminalFamily {c d : ℕ} (Q : (n : ℕ) → NormalTerminal R n c d) :
    (N : ℕ) → NormalTerminal (PreparationRecord R) N c d
  | 0 => {
      alice := QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization.pullbackTerminalInstrument
        (Q 0).alice (fun _ => PUnit.unit) measurable_const
      bob := QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization.pullbackTerminalInstrument
        (Q 0).bob (fun _ => PUnit.unit) measurable_const }
  | 1 => {
      alice := QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization.pullbackTerminalInstrument
        (Q 0).alice (fun _ => PUnit.unit) measurable_const
      bob := QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization.pullbackTerminalInstrument
        (Q 0).bob (fun _ => PUnit.unit) measurable_const }
  | n+2 => liftPreparedTerminal P n (Q n)

@[simp] theorem serializedTerminalFamily_after_two {c d : ℕ}
    (Q : (n : ℕ) → NormalTerminal R n c d) (n : ℕ) :
    serializedTerminalFamily P Q (n+2) = liftPreparedTerminal P n (Q n) := rfl

theorem measurable_dropPreparationTranscript :
    Measurable (dropPreparationTranscript P) := by
  exact measurable_pi_lambda (fun n =>
    (measurable_physicalRecordOfPrepared P).comp (measurable_pi_apply (n+2)))

@[simp] theorem dropPreparationTranscript_padded (ω : Transcript R) :
    dropPreparationTranscript P (paddedTranscript ω) = ω := by
  funext n
  have hn : ¬ n+2 < 2 := by omega
  simp only [dropPreparationTranscript, paddedTranscript, hn, ite_false,
    Nat.add_sub_cancel, physicalRecordOfPrepared, Sum.elim_inr, id_eq]

def liftedPreparedReport {J : Type*} (f : Transcript R → J) :
    Transcript (PreparationRecord R) → J :=
  f ∘ dropPreparationTranscript P

theorem liftedPreparedReport_padded {J : Type*} (f : Transcript R → J) :
    liftedPreparedReport P f ∘ paddedTranscript = f := by
  funext ω
  simp only [liftedPreparedReport, Function.comp_apply, dropPreparationTranscript_padded]

theorem measurable_liftedPreparedReport {J : Type*} [MeasurableSpace J]
    (f : Transcript R → J) (hf : Measurable f) : Measurable (liftedPreparedReport P f) :=
  hf.comp (measurable_dropPreparationTranscript P)

theorem report_on_padded_measure {J : Type*} (f : Transcript R → J)
    (ν : Measure (Transcript R)) (j : J) :
    (ν.map paddedTranscript) {ω | liftedPreparedReport P f ω = j} =
      ν {ω | f ω = j} := by
  rw [measurableEmbedding_paddedTranscript.map_apply]
  congr 1

end TranscriptCoding

section PreparedBornAndPhysicalTransport

variable {a b : ℕ} [NeZero a] [NeZero b]
  {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
  {FA FB : Type*}
  [NormedAddCommGroup FA] [InnerProductSpace ℂ FA] [CompleteSpace FA] [SeparableSpace FA]
  [NormedAddCommGroup FB] [InnerProductSpace ℂ FB] [CompleteSpace FB] [SeparableSpace FB]
  (P : MatrixProcess a b R)
  (τA : Nuclear FA) (τB : Nuclear FB)
  (hA : (toOperator τA).IsPositive) (hB : (toOperator τB).IsPositive)
  (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
  (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1)

def preparedBornMeasure (X : JointInputMatrix a b) (hX : X.PosSemidef) :
    Measure (Transcript R) :=
  ((serialized P τA τB hA hB hAT hBT).represented_physicalBornMeasure X hX).map
    (dropPreparationTranscript P)

theorem preparedBornMeasure_prefix (X : JointInputMatrix a b) (hX : X.PosSemidef)
    (N : ℕ) (s : Set (Prefix R N)) (hs : MeasurableSet s) :
    preparedBornMeasure P τA τB hA hB hAT hBT X hX
      ((frestrictLe (π := fun _ => R) N) ⁻¹' s) =
      ENNReal.ofReal (QuantumProver.HilbertNuclearTrace.trace
        (preparedPrefixAction P τA τB hA hB hAT hBT (N+1) s X)).re := by
  rw [preparedBornMeasure, Measure.map_apply (measurable_dropPreparationTranscript P)
    (hs.preimage (measurable_frestrictLe N))]
  have he :
      dropPreparationTranscript P ⁻¹' ((frestrictLe (π := fun _ => R) N) ⁻¹' s) =
        (frestrictLe (π := fun _ => PreparationRecord R) (N+2)) ⁻¹'
          (physicalPrefixOfPrepared P N ⁻¹' s) := by
    ext ω
    change frestrictLe (π := fun _ => R) N (dropPreparationTranscript P ω) ∈ s ↔
      physicalPrefixOfPrepared P N (frestrictLe (π := fun _ => PreparationRecord R) (N+2) ω) ∈ s
    rw [physicalPrefixOfPrepared_restrict]
  rw [he, MatrixProcess.physicalBornMeasure_prefix _ X hX (N+2)
    (physicalPrefixOfPrepared P N ⁻¹' s)
    (hs.preimage (measurable_physicalPrefixOfPrepared P N))]
  have hp : padHistory (N+1) ⁻¹' (physicalPrefixOfPrepared P N ⁻¹' s) = s := by
    ext h
    simp only [Set.mem_preimage, physicalPrefixOfPrepared_padHistory]
  have ha := preparedPrefixAction_serialized_preimage P τA τB hA hB hAT hBT (N+1)
    (physicalPrefixOfPrepared P N ⁻¹' s)
    (hs.preimage (measurable_physicalPrefixOfPrepared P N)) X
  rw [hp] at ha
  exact congrArg (fun T : Nuclear JointWorkspace =>
    ENNReal.ofReal (QuantumProver.HilbertNuclearTrace.trace T).re) ha.symm

theorem preparedBornMeasure_probability (X : JointInputMatrix a b) (hX : X.PosSemidef)
    (htrace : X.trace = 1) :
    IsProbabilityMeasure (preparedBornMeasure P τA τB hA hB hAT hBT X hX) := by
  letI := (serialized P τA τB hA hB hAT hBT).physicalBornMeasure_isProbability X hX htrace
  change IsProbabilityMeasure
    (((serialized P τA τB hA hB hAT hBT).represented_physicalBornMeasure X hX).map
      (dropPreparationTranscript P))
  infer_instance

theorem serialized_report_probability {J : Type*} [MeasurableSpace J]
    [MeasurableSingletonClass J]
    (f : Transcript R → J) (hf : Measurable f) (j : J)
    (X : JointInputMatrix a b) (hX : X.PosSemidef) :
    (serialized P τA τB hA hB hAT hBT).represented_physicalBornMeasure X hX
      {ω | liftedPreparedReport P f ω = j} =
      preparedBornMeasure P τA τB hA hB hAT hBT X hX {ω | f ω = j} := by
  have hs : MeasurableSet {ω | f ω = j} := by
    simpa only [Set.preimage, Set.mem_singleton_iff] using hf (measurableSet_singleton j)
  rw [preparedBornMeasure, Measure.map_apply (measurable_dropPreparationTranscript P)
    hs]
  rfl

def physicalPreparedBornMeasure (X : JointInputMatrix a b) (hX : X.PosSemidef) :
    Measure (Transcript R) :=
  (QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology.constantPhysicalBornMeasure
    (serialized P τA τB hA hB hAT hBT) X hX).map (dropPreparationTranscript P)

theorem physicalPreparedBornMeasure_eq_prepared (X : JointInputMatrix a b)
    (hX : X.PosSemidef) :
    physicalPreparedBornMeasure P τA τB hA hB hAT hBT X hX =
      preparedBornMeasure P τA τB hA hB hAT hBT X hX := by
  rw [physicalPreparedBornMeasure,
    QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology.constantPhysicalBornMeasure_eq_physical]
  rfl

theorem physical_prepared_report_probability {J : Type*} [MeasurableSpace J]
    [MeasurableSingletonClass J]
    (f : Transcript R → J) (hf : Measurable f) (j : J)
    (X : JointInputMatrix a b) (hX : X.PosSemidef) :
    QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology.constantPhysicalBornMeasure
      (serialized P τA τB hA hB hAT hBT) X hX
      {ω | liftedPreparedReport P f ω = j} =
      preparedBornMeasure P τA τB hA hB hAT hBT X hX {ω | f ω = j} := by
  rw [QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology.constantPhysicalBornMeasure_eq_physical]
  exact serialized_report_probability P τA τB hA hB hAT hBT f hf j X hX

theorem preparedBornMeasure_finite (X : JointInputMatrix a b) (hX : X.PosSemidef) :
    IsFiniteMeasure (preparedBornMeasure P τA τB hA hB hAT hBT X hX) := by
  let S := serialized P τA τB hA hB hAT hBT
  letI : Nonempty (PreparationRecord R) := S.record_nonempty
  haveI : IsFiniteMeasure (S.represented_physicalBornMeasure X hX) := by
    change IsFiniteMeasure (S.represented_physicalCylinderPOVM.fullBornMeasure X hX)
    infer_instance
  change IsFiniteMeasure ((S.represented_physicalBornMeasure X hX).map (dropPreparationTranscript P))
  infer_instance

theorem preparedBornMeasure_unique (X : JointInputMatrix a b) (hX : X.PosSemidef)
    (ν : Measure (Transcript R))
    (hν : ∀ (N : ℕ) (s : Set (Prefix R N)), MeasurableSet s →
      ν ((frestrictLe (π := fun _ => R) N) ⁻¹' s) =
        ENNReal.ofReal (QuantumProver.HilbertNuclearTrace.trace
          (preparedPrefixAction P τA τB hA hB hAT hBT (N+1) s X)).re) :
    preparedBornMeasure P τA τB hA hB hAT hBT X hX = ν := by
  letI : Nonempty R := P.record_nonempty
  let μ := preparedBornMeasure P τA τB hA hB hAT hBT X hX
  let F : ∀ N, Measure (Prefix R N) := fun N =>
    μ.map (frestrictLe (π := fun _ => R) N)
  haveI : IsFiniteMeasure μ := preparedBornMeasure_finite P τA τB hA hB hAT hBT X hX
  haveI : ∀ N, IsFiniteMeasure (F N) := fun N => by
    dsimp [F]
    infer_instance
  have hF : ∀ i j (hij : i ≤ j),
      (F j).map (frestrictLe₂ (π := fun _ => R) hij) = F i := by
    intro i j hij
    dsimp [F]
    rw [Measure.map_map (measurable_frestrictLe₂ hij) (measurable_frestrictLe j)]
    congr 1
  apply prefix_extension_unique F hF μ ν (fun N => rfl)
  intro N
  ext s hs
  rw [Measure.map_apply (measurable_frestrictLe N) hs, hν N s hs]
  dsimp only [F, μ]
  rw [Measure.map_apply (measurable_frestrictLe N) hs]
  exact (preparedBornMeasure_prefix P τA τB hA hB hAT hBT X hX N s hs).symm

theorem nullMeasurable_liftedPreparedReport {J : Type*} [MeasurableSpace J]
    (f : Transcript R → J) (X : JointInputMatrix a b) (hX : X.PosSemidef)
    (hf : NullMeasurable f (preparedBornMeasure P τA τB hA hB hAT hBT X hX)) :
    NullMeasurable (liftedPreparedReport P f)
      ((serialized P τA τB hA hB hAT hBT).represented_physicalBornMeasure X hX) := by
  exact hf.comp_quasiMeasurePreserving
    ((measurable_dropPreparationTranscript P).quasiMeasurePreserving _)

theorem serialized_completed_report_probability {J : Type*} [MeasurableSpace J]
    [MeasurableSingletonClass J] (f : Transcript R → J) (j : J)
    (X : JointInputMatrix a b) (hX : X.PosSemidef)
    (hf : NullMeasurable f (preparedBornMeasure P τA τB hA hB hAT hBT X hX)) :
    (serialized P τA τB hA hB hAT hBT).represented_physicalBornMeasure X hX
      {ω | liftedPreparedReport P f ω = j} =
      preparedBornMeasure P τA τB hA hB hAT hBT X hX {ω | f ω = j} := by
  have hs : NullMeasurableSet {ω | f ω = j}
      (preparedBornMeasure P τA τB hA hB hAT hBT X hX) := by
    exact hf (measurableSet_singleton j)
  rw [preparedBornMeasure, Measure.map_apply₀
    (measurable_dropPreparationTranscript P).aemeasurable hs]
  rfl

theorem physical_completed_report_probability {J : Type*} [MeasurableSpace J]
    [MeasurableSingletonClass J] (f : Transcript R → J) (j : J)
    (X : JointInputMatrix a b) (hX : X.PosSemidef)
    (hf : NullMeasurable f (preparedBornMeasure P τA τB hA hB hAT hBT X hX)) :
    QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology.constantPhysicalBornMeasure
      (serialized P τA τB hA hB hAT hBT) X hX
      {ω | liftedPreparedReport P f ω = j} =
      preparedBornMeasure P τA τB hA hB hAT hBT X hX {ω | f ω = j} := by
  rw [QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology.constantPhysicalBornMeasure_eq_physical]
  exact serialized_completed_report_probability P τA τB hA hB hAT hBT f j X hX hf

def physicalPreparedPrefixAction (n : ℕ) (s : Set (History R n))
    (X : JointInputMatrix a b) : Nuclear JointWorkspace :=
  let S := serialized P τA τB hA hB hAT hBT
  QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge.physicalPrefixAction
    (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes (PreparationRecord R))
    (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.domains S)
    (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.sourceFamily S)
    (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.sourceFamily S)
    (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.outputFamily S true)
    (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.outputFamily S false)
    (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.wiring S true)
    (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.wiring S false)
    (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.localFamily S true)
    (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.localFamily S false)
    S.initialAlice S.initialBob (n+2)
    (QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology.constantHistoryCoding S (n+2) '' (padHistory n '' s)) X

theorem physicalPreparedPrefixAction_eq (n : ℕ) (s : Set (History R n))
    (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    physicalPreparedPrefixAction P τA τB hA hB hAT hBT n s X =
      preparedPrefixAction P τA τB hA hB hAT hBT n s X := by
  unfold physicalPreparedPrefixAction
  rw [QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology.constant_physicalPrefixAction_image
    (serialized P τA τB hA hB hAT hBT) (n+2) (padHistory n '' s)
    ((measurableEmbedding_padHistory n).measurableSet_image' hs) X]
  exact (preparedPrefixAction_serialized P τA τB hA hB hAT hBT n s hs X).symm

theorem physical_preparation_two (X : JointInputMatrix a b) :
    physicalPreparedPrefixAction P τA τB hA hB hAT hBT 0 {PUnit.unit} X =
      mixedJointPreparation τA τB hA hB hAT hBT (P.initialJointOperation X) := by
  unfold physicalPreparedPrefixAction
  rw [QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology.constant_physicalPrefixAction_image
    (serialized P τA τB hA hB hAT hBT) 2 (padHistory 0 '' {PUnit.unit})
    ((measurableEmbedding_padHistory 0).measurableSet_image'
      (measurableSet_singleton PUnit.unit)) X]
  have hp : padHistory (R := R) 0 '' {PUnit.unit} = {preparationHistory} := by
    simp only [image_singleton, padHistory]
  rw [hp, serialized_prefix_two]
  rfl

theorem physicalPreparedPrefixAction_trace_univ (n : ℕ) (X : JointInputMatrix a b) :
    QuantumProver.HilbertNuclearTrace.trace
      (physicalPreparedPrefixAction P τA τB hA hB hAT hBT n univ X) = X.trace := by
  rw [physicalPreparedPrefixAction_eq P τA τB hA hB hAT hBT n univ MeasurableSet.univ X]
  exact preparedPrefixAction_trace_univ P τA τB hA hB hAT hBT n X

theorem serialized_quantum_output_prepared {c d : ℕ} (n : ℕ)
    (Q : NormalTerminal R n c d) (X : JointInputMatrix a b) :
    (serialized P τA τB hA hB hAT hBT).represented_physicalQuantumOutput (n+2)
      (liftPreparedTerminal P n Q) X =
      seededQuantumOutput P (preparedPhysicalStateLayer P τA τB hA hB hAT hBT) n Q X := by
  rw [serialized_quantum_output P τA τB hA hB hAT hBT]
  unfold seededQuantumOutput seededQuantumNuclearOutput
  apply congrArg (finiteJointDecode c d)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun h => by
    change terminalJointOperation (pullbackShiftedTerminal n (liftPreparedTerminal P n Q)) h
      (seededInputDensity P (preparedPhysicalStateLayer P τA τB hA hB hAT hBT) n X h) =
        terminalJointOperation Q h
          (seededInputDensity P (preparedPhysicalStateLayer P τA τB hA hB hAT hBT) n X h)
    rw [terminalJointOperation_pullbackShiftedTerminal,
      terminalJointOperation_liftPreparedTerminal])

def physicalPreparedTerminalHistory (n : ℕ)
    (h : (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.domains
      (serialized P τA τB hA hB hAT hBT)).admissible (n+2)) : History R n :=
  dropPreparedHistory P n
    (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv
      (PreparationRecord R) (n+2) h.val)

theorem measurable_physicalPreparedTerminalHistory (n : ℕ) :
    Measurable (physicalPreparedTerminalHistory P τA τB hA hB hAT hBT n) :=
  (measurable_dropPreparedHistory P n).comp
    ((QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv
      (PreparationRecord R) (n+2)).measurable.comp measurable_subtype_coe)

def physicalPreparedTerminalAlice {c d : ℕ} (n : ℕ) (Q : NormalTerminal R n c d) :
    QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument.MatrixInstrument
      (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.sourceFamily
        (serialized P τA τB hA hB hAT hBT) (n+2))
      (QuantumProver.ElegantJointMeasurement.NormalPhysicalTerminalAdmission.finiteOutputFamily
        (H := (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.domains
          (serialized P τA τB hA hB hAT hBT)).admissible (n+2)) c) PUnit.{u+1} :=
  QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization.rawTerminalAlice Q
    (physicalPreparedTerminalHistory P τA τB hA hB hAT hBT n)
    (measurable_physicalPreparedTerminalHistory P τA τB hA hB hAT hBT n)

def physicalPreparedTerminalBob {c d : ℕ} (n : ℕ) (Q : NormalTerminal R n c d) :
    QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument.MatrixInstrument
      (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.sourceFamily
        (serialized P τA τB hA hB hAT hBT) (n+2))
      (QuantumProver.ElegantJointMeasurement.NormalPhysicalTerminalAdmission.finiteOutputFamily
        (H := (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.domains
          (serialized P τA τB hA hB hAT hBT)).admissible (n+2)) d) PUnit.{u+1} :=
  QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization.rawTerminalBob Q
    (physicalPreparedTerminalHistory P τA τB hA hB hAT hBT n)
    (measurable_physicalPreparedTerminalHistory P τA τB hA hB hAT hBT n)

theorem physicalPreparedTerminalAlice_operation {c d : ℕ} (n : ℕ)
    (Q : NormalTerminal R n c d)
    (h : (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.domains
      (serialized P τA τB hA hB hAT hBT)).admissible (n+2)) (s : Set PUnit.{u+1}) :
    (physicalPreparedTerminalAlice P τA τB hA hB hAT hBT n Q).operation h s =
      Q.alice.operation (physicalPreparedTerminalHistory P τA τB hA hB hAT hBT n h) s :=
  QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization.rawTerminalAlice_operation Q _ _ h s

theorem physicalPreparedTerminalBob_operation {c d : ℕ} (n : ℕ)
    (Q : NormalTerminal R n c d)
    (h : (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.domains
      (serialized P τA τB hA hB hAT hBT)).admissible (n+2)) (s : Set PUnit.{u+1}) :
    (physicalPreparedTerminalBob P τA τB hA hB hAT hBT n Q).operation h s =
      Q.bob.operation (physicalPreparedTerminalHistory P τA τB hA hB hAT hBT n h) s :=
  QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalTerminalRealization.rawTerminalBob_operation Q _ _ h s

def physicalMixedProtocol :
    QuantumProver.ElegantJointMeasurement.PhysicalCost.PhysicalProtocol.{u,0,0} a b :=
  QuantumProver.ElegantJointMeasurement.PhysicalCost.commonPhysicalProtocol
    (serialized P τA τB hA hB hAT hBT)

theorem physicalMixedProtocol_matrix :
    (physicalMixedProtocol P τA τB hA hB hAT hBT).represented =
      physicalMixedPreparation P τA τB hA hB hAT hBT := rfl

def physicalMixedReadout {c d : ℕ} (n : ℕ) (Q : NormalTerminal R n c d) :
    QuantumProver.ElegantJointMeasurement.PhysicalCost.PhysicalReadout
      (physicalMixedProtocol P τA τB hA hB hAT hBT) (n+2) c d :=
  QuantumProver.ElegantJointMeasurement.PhysicalCost.commonPhysicalReadout
    (serialized P τA τB hA hB hAT hBT) (n+2) (liftPreparedTerminal P n Q)

theorem physical_mixed_quantum_output_prepared {c d : ℕ} (n : ℕ)
    (Q : NormalTerminal R n c d) (hc : 0 < c) (hd : 0 < d)
    (X : JointInputMatrix a b) :
    QuantumProver.ElegantJointMeasurement.PhysicalCost.physicalQuantumOutput
      (physicalMixedProtocol P τA τB hA hB hAT hBT)
      (physicalMixedReadout P τA τB hA hB hAT hBT n Q) X =
        seededQuantumOutput P (preparedPhysicalStateLayer P τA τB hA hB hAT hBT) n Q X := by
  change QuantumProver.ElegantJointMeasurement.PhysicalCost.physicalQuantumOutput
      (QuantumProver.ElegantJointMeasurement.PhysicalCost.commonPhysicalProtocol
        (serialized P τA τB hA hB hAT hBT))
      (QuantumProver.ElegantJointMeasurement.PhysicalCost.commonPhysicalReadout
        (serialized P τA τB hA hB hAT hBT) (n+2) (liftPreparedTerminal P n Q)) X = _
  rw [QuantumProver.ElegantJointMeasurement.PhysicalCost.common_physicalQuantumOutput_eq_physical
      (serialized P τA τB hA hB hAT hBT) (n+2) (liftPreparedTerminal P n Q) hc hd X]
  exact serialized_quantum_output_prepared P τA τB hA hB hAT hBT n Q X

def physicalMixedReadoutFamily {c d : ℕ}
    (Q : (n : ℕ) → NormalTerminal R n c d) (N : ℕ) :
    QuantumProver.ElegantJointMeasurement.PhysicalCost.PhysicalReadout
      (physicalMixedProtocol P τA τB hA hB hAT hBT) N c d :=
  QuantumProver.ElegantJointMeasurement.PhysicalCost.commonPhysicalReadout
    (serialized P τA τB hA hB hAT hBT) N (serializedTerminalFamily P Q N)

theorem physical_mixed_quantum_output_tendsto {c d : ℕ}
    (Q : (n : ℕ) → NormalTerminal R n c d) (hc : 0 < c) (hd : 0 < d)
    (X : JointInputMatrix a b) (Y : JointInputMatrix c d)
    (hQ : Filter.Tendsto
      (fun n => seededQuantumOutput P
        (preparedPhysicalStateLayer P τA τB hA hB hAT hBT) n (Q n) X)
      Filter.atTop (𝓝 Y)) :
    Filter.Tendsto
      (fun N => QuantumProver.ElegantJointMeasurement.PhysicalCost.physicalQuantumOutput
        (physicalMixedProtocol P τA τB hA hB hAT hBT)
        (physicalMixedReadoutFamily P τA τB hA hB hAT hBT Q N) X)
      Filter.atTop (𝓝 Y) := by
  apply (Filter.tendsto_add_atTop_iff_nat 2).mp
  have he :
      (fun n => QuantumProver.ElegantJointMeasurement.PhysicalCost.physicalQuantumOutput
        (physicalMixedProtocol P τA τB hA hB hAT hBT)
        (physicalMixedReadoutFamily P τA τB hA hB hAT hBT Q (n+2)) X) =
      (fun n => seededQuantumOutput P
        (preparedPhysicalStateLayer P τA τB hA hB hAT hBT) n (Q n) X) := by
    funext n
    exact physical_mixed_quantum_output_prepared P τA τB hA hB hAT hBT n (Q n) hc hd X
  rw [he]
  exact hQ

end PreparedBornAndPhysicalTransport
end QuantumProver.ElegantJointMeasurement.PhysicalFreePreparationSerialization
