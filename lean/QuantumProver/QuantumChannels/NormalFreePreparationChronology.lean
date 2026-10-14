import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalAncillaPreparation
import QuantumProver.InformationTheory.ElegantJointMeasurement.RecordCoding
import QuantumProver.QuantumChannels.NormalTensorInstrument
import QuantumProver.QuantumChannels.NormalRightTensor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace QuantumProver.MatrixNormalFreePreparationChronology

open MeasureTheory Set Function Filter InnerProductSpace TopologicalSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess (History appendHistory firstRecordEquiv)
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalAncillaPreparation
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.MatrixNuclearTensor
open scoped BigOperators Topology TensorProduct ComplexOrder Classical

universe u

abbrev Workspace := CommonHilbert
abbrev Nuc := QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear
abbrev PreparationRecord (R : Type u) := Unit ⊕ R
abbrev workspaceTensor := tensorNuclear (E := Workspace) (F := Workspace)
  (E' := Workspace) (F' := Workspace)

variable {R : Type u} [MeasurableSpace R]

structure RawFamilies (R : Type u) [MeasurableSpace R] where
  alice : (n : ℕ) → Instrument Workspace Workspace (History R n) R
  bob : (n : ℕ) → Instrument Workspace Workspace (History R n) R
  aliceTurn : (n : ℕ) → History R n → Bool
  turn_measurable : ∀ n, Measurable (aliceTurn n)

def preparationTag : PreparationRecord R := Sum.inl ()

def firstPreparationHistory : History (PreparationRecord R) 1 :=
  firstRecordEquiv preparationTag

def preparationHistory : History (PreparationRecord R) 2 :=
  appendHistory 1 (firstPreparationHistory, preparationTag)

theorem measurableSet_preparationTag :
    MeasurableSet ({preparationTag} : Set (PreparationRecord R)) := by
  simpa only [preparationTag, image_singleton] using
    (measurableSet_singleton ()).inl_image (β := R)

theorem measurableSet_firstPreparationHistory :
    MeasurableSet ({firstPreparationHistory} : Set (History (PreparationRecord R) 1)) := by
  simpa only [firstPreparationHistory, image_singleton] using
    (firstRecordEquiv (R := PreparationRecord R)).measurableEmbedding.measurableSet_image'
      (measurableSet_preparationTag (R := R))

theorem measurableSet_preparationHistory :
    MeasurableSet ({preparationHistory} : Set (History (PreparationRecord R) 2)) := by
  have hp : MeasurableSet ({(firstPreparationHistory, preparationTag)} :
      Set (History (PreparationRecord R) 1 × PreparationRecord R)) := by
    simpa only [singleton_prod_singleton] using
      (measurableSet_firstPreparationHistory (R := R)).prod
        (measurableSet_preparationTag (R := R))
  simpa only [preparationHistory, image_singleton] using
    (appendHistory (R := PreparationRecord R) 1).measurableEmbedding.measurableSet_image' hp

omit [MeasurableSpace R] in
private theorem measurableEmbedding_zero_history_const {Y : Type*} [MeasurableSpace Y]
    (y : Y) (hy : MeasurableSet ({y} : Set Y)) :
    MeasurableEmbedding (fun _ : History R 0 => y) where
  injective := fun _ _ _ => Subsingleton.elim _ _
  measurable := measurable_const
  measurableSet_image' := by
    intro s hs
    by_cases he : s = ∅
    · simp [he]
    · rw [(Set.nonempty_iff_ne_empty.mpr he).image_const]
      exact hy

def firstHistoryEmbedding (_h : History R 0) : History (PreparationRecord R) 1 :=
  firstPreparationHistory

theorem measurableEmbedding_firstHistoryEmbedding :
    MeasurableEmbedding (firstHistoryEmbedding (R := R)) :=
  measurableEmbedding_zero_history_const firstPreparationHistory
    measurableSet_firstPreparationHistory

def padHistory : (n : ℕ) → History R n → History (PreparationRecord R) (n+2)
  | 0, _ => preparationHistory
  | n+1, h =>
      let z := (appendHistory n).symm h
      appendHistory (n+2) (padHistory n z.1, Sum.inr z.2)

theorem measurableEmbedding_inr : MeasurableEmbedding (Sum.inr : R → PreparationRecord R) :=
  ⟨Sum.inr_injective, measurable_inr, fun _ hs => hs.inr_image⟩

theorem measurableEmbedding_padHistory (n : ℕ) :
    MeasurableEmbedding (padHistory (R := R) n) := by
  induction n with
  | zero =>
      exact measurableEmbedding_zero_history_const (R := R)
        (preparationHistory (R := R)) (measurableSet_preparationHistory (R := R))
  | succ n ih =>
      change MeasurableEmbedding ((appendHistory (R := PreparationRecord R) (n+2)) ∘
        Prod.map (padHistory n) Sum.inr ∘ (appendHistory (R := R) n).symm)
      exact (appendHistory (R := PreparationRecord R) (n+2)).measurableEmbedding.comp
        ((ih.prodMap measurableEmbedding_inr).comp (appendHistory n).symm.measurableEmbedding)

theorem padHistory_append (n : ℕ) (h : History R n) (r : R) :
    padHistory (n+1) (appendHistory n (h,r)) =
      appendHistory (n+2) (padHistory n h, Sum.inr r) := by
  simp only [padHistory, MeasurableEquiv.symm_apply_apply]

def ValidHistory (n : ℕ) : Set (History (PreparationRecord R) (n+2)) := range (padHistory n)

theorem measurableSet_validHistory (n : ℕ) : MeasurableSet (ValidHistory (R := R) n) :=
  (measurableEmbedding_padHistory n).measurableSet_range

def decodeHistory (n : ℕ) : ValidHistory (R := R) n ≃ᵐ History R n :=
  (measurableEmbedding_padHistory n).equivRange.symm

@[simp] theorem decodeHistory_padHistory (n : ℕ) (h : History R n) :
    decodeHistory n ⟨padHistory n h, mem_range_self h⟩ = h :=
  (measurableEmbedding_padHistory n).equivRange_symm_apply_mk h

def shiftedInstrument (n : ℕ) (P : Instrument Workspace Workspace (History R n) R) :
    Instrument Workspace Workspace (History (PreparationRecord R) (n+2)) (PreparationRecord R) :=
  QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.liftInstrumentAlongEmbedding P (padHistory n)
    (measurableEmbedding_padHistory n) Sum.inr measurable_inr preparationTag

theorem shiftedInstrument_operation (n : ℕ)
    (P : Instrument Workspace Workspace (History R n) R) (h : History R n)
    (s : Set (PreparationRecord R)) :
    (shiftedInstrument n P).operation (padHistory n h) s = P.operation h (Sum.inr ⁻¹' s) :=
  QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.liftInstrumentAlongEmbedding_encoded P (padHistory n)
    (measurableEmbedding_padHistory n) Sum.inr measurable_inr preparationTag h s

theorem shiftedInstrument_physical_event (n : ℕ)
    (P : Instrument Workspace Workspace (History R n) R) (h : History R n) (s : Set R) :
    (shiftedInstrument n P).operation (padHistory n h) (Sum.inr '' s) = P.operation h s := by
  rw [shiftedInstrument_operation, Sum.inr_injective.preimage_image]

theorem shiftedInstrument_invalid (n : ℕ)
    (P : Instrument Workspace Workspace (History R n) R)
    (h : History (PreparationRecord R) (n+2)) (hh : h ∉ ValidHistory n)
    (s : Set (PreparationRecord R)) (T : Nuc Workspace) :
    (shiftedInstrument n P).operation h s T = if preparationTag ∈ s then T else 0 := by
  simp only [shiftedInstrument, QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.liftInstrumentAlongEmbedding,
    ValidHistory] at hh ⊢
  rw [dite_eq_right hh]
  simp only [QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.dummyInstrument]
  split_ifs <;> rfl

def shiftedParty (P : RawFamilies R) (n : ℕ)
    (h : History (PreparationRecord R) (n+2)) : Bool :=
  if hh : h ∈ ValidHistory n then P.aliceTurn n (decodeHistory n ⟨h,hh⟩) else true

theorem measurable_shiftedParty (P : RawFamilies R) (n : ℕ) :
    Measurable (shiftedParty P n) := by
  have hm : Measurable (fun h : ValidHistory (R := R) n =>
      P.aliceTurn n (decodeHistory n h)) := (P.turn_measurable n).comp (decodeHistory n).measurable
  have hm' : Measurable (fun _ : {h : History (PreparationRecord R) (n+2) //
      h ∉ ValidHistory n} => true) := measurable_const
  exact hm.dite hm' (measurableSet_validHistory n)

@[simp] theorem shiftedParty_padHistory (P : RawFamilies R) (n : ℕ) (h : History R n) :
    shiftedParty P n (padHistory n h) = P.aliceTurn n h := by
  simp only [shiftedParty, ValidHistory, mem_range_self, ↓reduceDIte]
  exact congrArg (P.aliceTurn n) (decodeHistory_padHistory (R := R) n h)

def taggedSingleton {H : Type*} [MeasurableSpace H]
    (Φ : NormalOperation Workspace Workspace) (hCP : NormalCompletelyPositive Φ)
    (hTP : ∀ T, HilbertNuclearTrace.trace (Φ T) = HilbertNuclearTrace.trace T) :
    Instrument Workspace Workspace H (PreparationRecord R) :=
  QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.pushforwardInstrument (singletonInstrument Φ hCP hTP)
    (fun _ : PUnit.{1} => preparationTag) measurable_const

theorem taggedSingleton_operation {H : Type*} [MeasurableSpace H]
    (Φ : NormalOperation Workspace Workspace) (hCP : NormalCompletelyPositive Φ)
    (hTP : ∀ T, HilbertNuclearTrace.trace (Φ T) = HilbertNuclearTrace.trace T)
    (h : H) (s : Set (PreparationRecord R)) :
    (taggedSingleton Φ hCP hTP).operation h s = if preparationTag ∈ s then Φ else 0 := rfl

def secondPreparation
    (Φ : NormalOperation Workspace Workspace) (hCP : NormalCompletelyPositive Φ)
    (hTP : ∀ T, HilbertNuclearTrace.trace (Φ T) = HilbertNuclearTrace.trace T) :
    Instrument Workspace Workspace (History (PreparationRecord R) 1) (PreparationRecord R) :=
  QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.liftInstrumentAlongEmbedding
    (singletonInstrument (H := History R 0) Φ hCP hTP) firstHistoryEmbedding
    measurableEmbedding_firstHistoryEmbedding (fun _ : PUnit.{1} => preparationTag)
    measurable_const preparationTag

theorem secondPreparation_operation
    (Φ : NormalOperation Workspace Workspace) (hCP : NormalCompletelyPositive Φ)
    (hTP : ∀ T, HilbertNuclearTrace.trace (Φ T) = HilbertNuclearTrace.trace T)
    (s : Set (PreparationRecord R)) :
    (secondPreparation Φ hCP hTP).operation firstPreparationHistory s =
      if preparationTag ∈ s then Φ else 0 := by
  exact QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.liftInstrumentAlongEmbedding_encoded
    (singletonInstrument (H := History R 0) Φ hCP hTP) firstHistoryEmbedding
    measurableEmbedding_firstHistoryEmbedding (fun _ : PUnit.{1} => preparationTag)
    measurable_const preparationTag PUnit.unit s

def insertLocalPreparations (P : RawFamilies R)
    (ΦA ΦB : NormalOperation Workspace Workspace)
    (hA : NormalCompletelyPositive ΦA) (hB : NormalCompletelyPositive ΦB)
    (hAT : ∀ T, HilbertNuclearTrace.trace (ΦA T) = HilbertNuclearTrace.trace T)
    (hBT : ∀ T, HilbertNuclearTrace.trace (ΦB T) = HilbertNuclearTrace.trace T) :
    RawFamilies (PreparationRecord R) where
  alice
    | 0 => taggedSingleton ΦA hA hAT
    | 1 => QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.dummyInstrument preparationTag
    | n+2 => shiftedInstrument n (P.alice n)
  bob
    | 0 => QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.dummyInstrument preparationTag
    | 1 => secondPreparation ΦB hB hBT
    | n+2 => shiftedInstrument n (P.bob n)
  aliceTurn
    | 0 => fun _ => true
    | 1 => fun _ => false
    | n+2 => shiftedParty P n
  turn_measurable
    | 0 => measurable_const
    | 1 => measurable_const
    | n+2 => measurable_shiftedParty P n

variable (P : RawFamilies R) (ΦA ΦB : NormalOperation Workspace Workspace)
    (hA : NormalCompletelyPositive ΦA) (hB : NormalCompletelyPositive ΦB)
    (hAT : ∀ T, HilbertNuclearTrace.trace (ΦA T) = HilbertNuclearTrace.trace T)
    (hBT : ∀ T, HilbertNuclearTrace.trace (ΦB T) = HilbertNuclearTrace.trace T)

theorem inserted_alice_physical_event (n : ℕ) (h : History R n) (s : Set R) :
    ((insertLocalPreparations P ΦA ΦB hA hB hAT hBT).alice (n+2)).operation
      (padHistory n h) (Sum.inr '' s) = (P.alice n).operation h s :=
  shiftedInstrument_physical_event n (P.alice n) h s

theorem inserted_bob_physical_event (n : ℕ) (h : History R n) (s : Set R) :
    ((insertLocalPreparations P ΦA ΦB hA hB hAT hBT).bob (n+2)).operation
      (padHistory n h) (Sum.inr '' s) = (P.bob n).operation h s :=
  shiftedInstrument_physical_event n (P.bob n) h s

theorem inserted_physical_party (n : ℕ) (h : History R n) :
    (insertLocalPreparations P ΦA ΦB hA hB hAT hBT).aliceTurn (n+2) (padHistory n h) =
      P.aliceTurn n h := shiftedParty_padHistory P n h

theorem workspace_separable : SeparableSpace Workspace := by
  have hs : IsSeparable (closure (Submodule.span ℂ (range commonBasis) : Set Workspace)) :=
    ((countable_range commonBasis).isSeparable.span (R := ℂ)).closure
  have hc : closure (Submodule.span ℂ (range commonBasis) : Set Workspace) = univ := by
    rw [← Submodule.topologicalClosure_coe, commonBasis.dense_span, Submodule.top_coe]
  exact isSeparable_univ_iff.mp (hc ▸ hs)

local instance : SeparableSpace Workspace := workspace_separable

def rawEventAction (F : RawFamilies R) (n : ℕ) (h : History R n) (s : Set R) :
    NormalOperation (Joint Workspace Workspace) (Joint Workspace Workspace) :=
  if F.aliceTurn n h = true then
    MatrixNormalTensorInstrument.tensorOperation (G := Workspace) (F.alice n) h s
  else MatrixNormalRightTensor.rightTensorOperation (G := Workspace) (F.bob n) h s

theorem inserted_physical_joint_event (n : ℕ) (h : History R n) (s : Set R)
    (hs : MeasurableSet s) :
    rawEventAction (insertLocalPreparations P ΦA ΦB hA hB hAT hBT) (n+2)
        (padHistory n h) (Sum.inr '' s) = rawEventAction P n h s := by
  have hsi : MeasurableSet (Sum.inr '' s : Set (PreparationRecord R)) := hs.inr_image
  by_cases ht : P.aliceTurn n h = true
  · simp only [rawEventAction, inserted_physical_party, ht, ite_true]
    rw [MatrixNormalTensorInstrument.tensorOperation_of_measurable _ _ _ hsi,
      MatrixNormalTensorInstrument.tensorOperation_of_measurable _ _ _ hs]
    simp only [inserted_alice_physical_event]
  · simp only [rawEventAction, inserted_physical_party, ite_eq_right ht]
    rw [MatrixNormalRightTensor.rightTensorOperation_of_measurable _ _ _ hsi,
      MatrixNormalRightTensor.rightTensorOperation_of_measurable _ _ _ hs]
    simp only [inserted_bob_physical_event]

private theorem traceNonincreasing_of_trace_preserving
    (Φ : NormalOperation Workspace Workspace)
    (hTP : ∀ T, HilbertNuclearTrace.trace (Φ T) = HilbertNuclearTrace.trace T) :
    QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.TraceNonincreasing Φ := by
  intro T hT
  rw [hTP]

theorem first_preparation_joint_action (W : Nuc (Joint Workspace Workspace)) :
    rawEventAction (insertLocalPreparations P ΦA ΦB hA hB hAT hBT) 0 PUnit.unit univ W =
      MatrixNormalTensorExtension.extendLeft (G := Workspace) ΦA hA
        (traceNonincreasing_of_trace_preserving ΦA hAT) W := by
  simp only [rawEventAction, insertLocalPreparations, ite_true]
  rw [MatrixNormalTensorInstrument.tensorOperation_of_measurable _ _ _ MeasurableSet.univ]
  simp only [taggedSingleton_operation, mem_univ, ite_true]

theorem second_preparation_joint_action (W : Nuc (Joint Workspace Workspace)) :
    rawEventAction (insertLocalPreparations P ΦA ΦB hA hB hAT hBT) 1
        firstPreparationHistory univ W =
      MatrixNormalRightTensor.extendRight (G := Workspace) ΦB hB
        (traceNonincreasing_of_trace_preserving ΦB hBT) W := by
  simp only [rawEventAction, insertLocalPreparations, Bool.false_eq_true, ite_false]
  rw [MatrixNormalRightTensor.rightTensorOperation_of_measurable _ _ _ MeasurableSet.univ]
  simp only [secondPreparation_operation, mem_univ, ite_true]

theorem two_turn_joint_action (W : Nuc (Joint Workspace Workspace)) :
    rawEventAction (insertLocalPreparations P ΦA ΦB hA hB hAT hBT) 1 firstPreparationHistory univ
      (rawEventAction (insertLocalPreparations P ΦA ΦB hA hB hAT hBT) 0 PUnit.unit univ W) =
    MatrixNormalRightTensor.extendRight (G := Workspace) ΦB hB
      (traceNonincreasing_of_trace_preserving ΦB hBT)
      (MatrixNormalTensorExtension.extendLeft (G := Workspace) ΦA hA
        (traceNonincreasing_of_trace_preserving ΦA hAT) W) := by
  rw [first_preparation_joint_action, second_preparation_joint_action]

theorem two_turn_product_action (T U : Nuc Workspace) :
    rawEventAction (insertLocalPreparations P ΦA ΦB hA hB hAT hBT) 1 firstPreparationHistory univ
      (rawEventAction (insertLocalPreparations P ΦA ΦB hA hB hAT hBT) 0 PUnit.unit univ
        (workspaceTensor T U)) = workspaceTensor (ΦA T) (ΦB U) := by
  rw [two_turn_joint_action P ΦA ΦB hA hB hAT hBT (workspaceTensor T U)]
  exact (congrArg
    (MatrixNormalRightTensor.extendRight (E := Workspace) (F := Workspace) (G := Workspace)
      ΦB hB (traceNonincreasing_of_trace_preserving ΦB hBT))
    (MatrixNormalTensorExtension.extendLeft_tensor
      (E := Workspace) (F := Workspace) (G := Workspace) ΦA hA
      (traceNonincreasing_of_trace_preserving ΦA hAT) T U)).trans
    (MatrixNormalRightTensor.extendRight_tensor (E := Workspace) (F := Workspace) (G := Workspace)
      ΦB hB (traceNonincreasing_of_trace_preserving ΦB hBT) (ΦA T) U)

section ActualMixedPreparation

variable {FA FB : Type*}
  [NormedAddCommGroup FA] [InnerProductSpace ℂ FA] [CompleteSpace FA] [SeparableSpace FA]
  [NormedAddCommGroup FB] [InnerProductSpace ℂ FB] [CompleteSpace FB] [SeparableSpace FB]

def insertMixedPreparation (F : RawFamilies R) (τA : Nuc FA) (τB : Nuc FB)
    (hA : (NuclearOperator.toOperator τA).IsPositive)
    (hB : (NuclearOperator.toOperator τB).IsPositive)
    (hAT : HilbertNuclearTrace.trace τA = 1) (hBT : HilbertNuclearTrace.trace τB = 1) :
    RawFamilies (PreparationRecord R) :=
  insertLocalPreparations F (commonPreparation (E := Workspace) τA)
    (commonPreparation (E := Workspace) τB)
    (commonPreparation_completelyPositive τA hA) (commonPreparation_completelyPositive τB hB)
    (trace_commonPreparation τA hAT) (trace_commonPreparation τB hBT)

def mixedJointPreparation (τA : Nuc FA) (τB : Nuc FB)
    (hA : (NuclearOperator.toOperator τA).IsPositive)
    (hB : (NuclearOperator.toOperator τB).IsPositive)
    (hAT : HilbertNuclearTrace.trace τA = 1) (hBT : HilbertNuclearTrace.trace τB = 1) :
    NormalOperation (Joint Workspace Workspace) (Joint Workspace Workspace) :=
  (MatrixNormalRightTensor.extendRight (G := Workspace)
      (commonPreparation (E := Workspace) τB) (commonPreparation_completelyPositive τB hB)
      (traceNonincreasing_of_trace_preserving _ (trace_commonPreparation τB hBT))).comp
    (MatrixNormalTensorExtension.extendLeft (G := Workspace)
      (commonPreparation (E := Workspace) τA) (commonPreparation_completelyPositive τA hA)
      (traceNonincreasing_of_trace_preserving _ (trace_commonPreparation τA hAT)))

theorem mixed_preparation_all_input_action (F : RawFamilies R)
    (τA : Nuc FA) (τB : Nuc FB) (hA : (NuclearOperator.toOperator τA).IsPositive)
    (hB : (NuclearOperator.toOperator τB).IsPositive)
    (hAT : HilbertNuclearTrace.trace τA = 1) (hBT : HilbertNuclearTrace.trace τB = 1)
    (W : Nuc (Joint Workspace Workspace)) :
    rawEventAction (insertMixedPreparation F τA τB hA hB hAT hBT) 1 firstPreparationHistory univ
      (rawEventAction (insertMixedPreparation F τA τB hA hB hAT hBT) 0 PUnit.unit univ W) =
      mixedJointPreparation τA τB hA hB hAT hBT W :=
  two_turn_joint_action F _ _ _ _ _ _ W

theorem mixed_preparation_two_turn_action (F : RawFamilies R)
    (τA : Nuc FA) (τB : Nuc FB) (hA : (NuclearOperator.toOperator τA).IsPositive)
    (hB : (NuclearOperator.toOperator τB).IsPositive)
    (hAT : HilbertNuclearTrace.trace τA = 1) (hBT : HilbertNuclearTrace.trace τB = 1)
    (T U : Nuc Workspace) :
    rawEventAction (insertMixedPreparation F τA τB hA hB hAT hBT) 1 firstPreparationHistory univ
      (rawEventAction (insertMixedPreparation F τA τB hA hB hAT hBT) 0 PUnit.unit univ
        (workspaceTensor T U)) =
      workspaceTensor
        (padNuclear (jointPadding (E := Workspace) (F := FA))
          (tensorNuclear (E := Workspace) (F := FA) (E' := Workspace) (F' := FA) T τA))
        (padNuclear (jointPadding (E := Workspace) (F := FB))
          (tensorNuclear (E := Workspace) (F := FB) (E' := Workspace) (F' := FB) U τB)) :=
  two_turn_product_action F _ _ _ _ _ _ T U

end ActualMixedPreparation

end QuantumProver.MatrixNormalFreePreparationChronology
