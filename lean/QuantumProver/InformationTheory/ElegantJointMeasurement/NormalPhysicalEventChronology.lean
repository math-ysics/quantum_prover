import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalAdmission
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalProcess

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory ProbabilityTheory Set Filter Function InnerProductSpace TopologicalSpace
open scoped BigOperators Topology ComplexOrder
namespace QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge
open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertRecordCoding
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.ElegantJointMeasurement.HilbertFiniteKrausPredual QuantumProver.ElegantJointMeasurement.HilbertPendingTensor
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixNormalTensorInstrument QuantumProver.MatrixNormalRightTensor
open QuantumProver.MatrixNormalSourceCompletion QuantumProver.MatrixNormalStateKernel
open QuantumProver.NuclearOperator (toOperator)
universe u v w

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
  [∀ n, StandardBorelSpace (Ω n)]

section IndependentPhysicalChronology

variable (D : PhysicalDomains Ω)
  {EA EB : (n : ℕ) → D.admissible n → Type v}
  [∀ n h, NormedAddCommGroup (EA n h)] [∀ n h, InnerProductSpace ℂ (EA n h)]
  [∀ n h, CompleteSpace (EA n h)]
  [∀ n h, NormedAddCommGroup (EB n h)] [∀ n h, InnerProductSpace ℂ (EB n h)]
  [∀ n h, CompleteSpace (EB n h)]
  (FA : (n : ℕ) → FundamentalFamily (EA n))
  (FB : (n : ℕ) → FundamentalFamily (EB n))
  {GA : (n : ℕ) → D.actingDomain n true × Ω n → Type w}
  {GB : (n : ℕ) → D.actingDomain n false × Ω n → Type w}
  [∀ n z, NormedAddCommGroup (GA n z)] [∀ n z, InnerProductSpace ℂ (GA n z)]
  [∀ n z, CompleteSpace (GA n z)]
  [∀ n z, NormedAddCommGroup (GB n z)] [∀ n z, InnerProductSpace ℂ (GB n z)]
  [∀ n z, CompleteSpace (GB n z)]
  (QA : (n : ℕ) → FundamentalFamily (GA n))
  (QB : (n : ℕ) → FundamentalFamily (GB n))
  (WA : PhysicalMemoryWiring Ω D true FA QA)
  (WB : PhysicalMemoryWiring Ω D false FB QB)
  (PA : PhysicalLocalFamily Ω D true FA QA)
  (PB : PhysicalLocalFamily Ω D false FB QB)
  {a b : ℕ} [NeZero a] [NeZero b]
  (JA : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EA 0 D.initialHistory)
  (JB : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EB 0 D.initialHistory)

local notation "N" => ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB
local notation "CA" n => IntrinsicFamily.family (selectedMemory Ω D true FA QA WA n)
local notation "CB" n => IntrinsicFamily.family (selectedMemory Ω D false FB QB WB n)

def physicalStepInstrument (n : ℕ) :
    Instrument JointWorkspace JointWorkspace (History (CommonRecord Ω) n) (CommonRecord Ω) := by
  let A := tensorInstrument (G := CommonHilbert) (admittedMemoryTurn Ω D true FA QA WA PA n)
  let B := rightTensorInstrument (G := CommonHilbert) (admittedMemoryTurn Ω D false FB QB WB PB n)
  let c := liftHistoryFunction Ω n (D.physicalParty n) true
  have hc : Measurable c := measurable_liftHistoryFunction Ω n _ (D.measurable_physicalParty n) true
  exact {
    operation := fun h s => if c h = true then A.operation h s else B.operation h s
    empty := fun h => by
      split
      · exact A.empty h
      · exact B.empty h
    countable_additivity := fun h s hs hd U => by
      by_cases hh : c h = true
      · simpa only [if_pos hh] using A.countable_additivity h s hs hd U
      · simpa only [if_neg hh] using B.countable_additivity h s hs hd U
    completelyPositive := fun h s hs => by
      split
      · exact A.completelyPositive h s hs
      · exact B.completelyPositive h s hs
    measurable_coordinate := fun s hs U x y => by
      have hm : Measurable (fun h : History (CommonRecord Ω) n => if c h = true then
          inner ℂ x (toOperator (A.operation h s U) y) else
          inner ℂ x (toOperator (B.operation h s U) y)) :=
        Measurable.ite (measurableSet_eq_fun hc (measurable_const (a := true)))
        (A.measurable_coordinate s hs U x y) (B.measurable_coordinate s hs U x y)
      convert hm using 1
      funext h
      by_cases hh : c h = true
      · simp only [if_pos hh]
      · simp only [if_neg hh]
    trace_preserving := fun h U => by
      split
      · exact A.trace_preserving h U
      · exact B.trace_preserving h U }

theorem physicalStepInstrument_eq_admitted (n : ℕ) :
    physicalStepInstrument Ω D FA FB QA QB WA WB PA PB n = (N).represented_physicalStepInstrument n := by
  rfl

def physicalReferenceInstrument (n : ℕ) :
    Instrument (PhysicalChoiWorkspace a b) (PhysicalChoiWorkspace a b)
      (History (CommonRecord Ω) n) (CommonRecord Ω) :=
  QuantumProver.MatrixNormalAmplifiedInstrument.amplifiedInstrument (Fin a × Fin b)
    (physicalStepInstrument Ω D FA FB QA QB WA WB PA PB n)

theorem physicalReferenceInstrument_eq_admitted (n : ℕ) :
    physicalReferenceInstrument Ω D FA FB QA QB WA WB PA PB (a := a) (b := b) n =
      (N).represented_physicalReferenceInstrument n := by
  rw [physicalReferenceInstrument,
    physicalStepInstrument_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB n]
  rfl

def physicalInitialJointMap : EuclideanSpace ℂ (Fin a × Fin b) →L[ℂ] JointWorkspace :=
  jointKraus
    (fun _ : Unit => ((FA 0).embedding D.initialHistory).toContinuousLinearMap.comp JA.toContinuousLinearMap)
    (fun _ : Unit => ((FB 0).embedding D.initialHistory).toContinuousLinearMap.comp JB.toContinuousLinearMap)
    ((),())

def physicalInitialJointOperation : PhysicalOperation (Fin a × Fin b) JointWorkspace :=
  finiteKrausOperation (fun _ : Unit => physicalInitialJointMap Ω D FA FB JA JB)

theorem physicalInitialJointOperation_eq_admitted :
    physicalInitialJointOperation Ω D FA FB JA JB = (N).initialJointOperation := by
  rfl

def physicalInitialChoiState : Nuclear (PhysicalChoiWorkspace a b) :=
  (((Fintype.card (Fin a × Fin b) : ℝ)⁻¹ : ℂ) •
    nuclearChoi (physicalInitialJointOperation Ω D FA FB JA JB))

theorem physicalInitialChoiState_eq_admitted :
    physicalInitialChoiState Ω D FA FB JA JB = (N).initialChoiState := by
  rw [physicalInitialChoiState,
    physicalInitialJointOperation_eq_admitted (GA := GA) (GB := GB)
      Ω D FA FB QA QB WA WB PA PB JA JB]
  rfl

def physicalInitialStateLayer :
    MatrixProcess.PhysicalStateLayer (a := a) (b := b) (R := CommonRecord Ω) 0 where
  state _ := physicalInitialChoiState Ω D FA FB JA JB
  stronglyMeasurable_state := stronglyMeasurable_const
  positive _ := by
    rw [physicalInitialChoiState_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB]
    exact (N).initialChoiState_isPositive
  trace_one _ := by
    rw [physicalInitialChoiState_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB]
    exact (N).initialChoiState_trace

def physicalNextStateLayer {n : ℕ}
    (L : MatrixProcess.PhysicalStateLayer (a := a) (b := b) (R := CommonRecord Ω) n) :
    MatrixProcess.PhysicalStateLayer (a := a) (b := b) (R := CommonRecord Ω) (n+1) where
  state h := posterior
    (physicalReferenceInstrument Ω D FA FB QA QB WA WB PA PB (a := a) (b := b) n)
    L.state L.positive L.stronglyMeasurable_state L.trace_one ((appendHistory n).symm h)
  stronglyMeasurable_state :=
    (stronglyMeasurable_posterior
      (physicalReferenceInstrument Ω D FA FB QA QB WA WB PA PB (a := a) (b := b) n)
      L.state L.positive L.stronglyMeasurable_state L.trace_one).comp_measurable
        (appendHistory (R := CommonRecord Ω) n).symm.measurable
  positive h := posterior_isPositive
    (physicalReferenceInstrument Ω D FA FB QA QB WA WB PA PB (a := a) (b := b) n)
    L.state L.positive L.stronglyMeasurable_state L.trace_one
    ((appendHistory n).symm h).1 ((appendHistory n).symm h).2
  trace_one h := posterior_trace
    (physicalReferenceInstrument Ω D FA FB QA QB WA WB PA PB (a := a) (b := b) n)
    L.state L.positive L.stronglyMeasurable_state L.trace_one
    ((appendHistory n).symm h).1 ((appendHistory n).symm h).2

def physicalStateLayers : (n : ℕ) →
    MatrixProcess.PhysicalStateLayer (a := a) (b := b) (R := CommonRecord Ω) n
  | 0 => physicalInitialStateLayer Ω D FA FB QA QB WA WB PA PB JA JB
  | n+1 => physicalNextStateLayer Ω D FA FB QA QB WA WB PA PB
      (physicalStateLayers n)

theorem physicalChronologyLayer_ext {n : ℕ}
    (L K : MatrixProcess.PhysicalStateLayer (a := a) (b := b) (R := CommonRecord Ω) n)
    (he : L.state = K.state) : L = K := by
  cases L
  cases K
  cases he
  rfl

theorem physicalStateLayers_eq_admitted (n : ℕ) :
    physicalStateLayers Ω D FA FB QA QB WA WB PA PB JA JB n = (N).represented_physicalStateLayers n := by
  induction n with
  | zero =>
      apply physicalChronologyLayer_ext Ω
      funext h
      exact physicalInitialChoiState_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB
  | succ n ih =>
      change physicalNextStateLayer Ω D FA FB QA QB WA WB PA PB
        (physicalStateLayers Ω D FA FB QA QB WA WB PA PB JA JB n) = _
      rw [ih]
      apply physicalChronologyLayer_ext Ω
      funext h
      change posterior
        (physicalReferenceInstrument Ω D FA FB QA QB WA WB PA PB (a := a) (b := b) n)
        _ _ _ _ _ = _
      rw [physicalReferenceInstrument_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB]
      rfl

def physicalState (n : ℕ) : History (CommonRecord Ω) n → Nuclear (PhysicalChoiWorkspace a b) :=
  (physicalStateLayers Ω D FA FB QA QB WA WB PA PB JA JB n).state

def physicalBornKernel (n : ℕ) : Kernel (History (CommonRecord Ω) n) (CommonRecord Ω) :=
  bornKernel (physicalReferenceInstrument Ω D FA FB QA QB WA WB PA PB (a := a) (b := b) n)
    (physicalStateLayers Ω D FA FB QA QB WA WB PA PB JA JB n).state
    (physicalStateLayers Ω D FA FB QA QB WA WB PA PB JA JB n).positive
    (physicalStateLayers Ω D FA FB QA QB WA WB PA PB JA JB n).stronglyMeasurable_state
    (physicalStateLayers Ω D FA FB QA QB WA WB PA PB JA JB n).trace_one

theorem physicalState_eq_admitted (n : ℕ) :
    physicalState Ω D FA FB QA QB WA WB PA PB JA JB n = (N).represented_physicalState n := by
  rw [physicalState, physicalStateLayers_eq_admitted]
  rfl

theorem physicalBornKernel_eq_admitted (n : ℕ) :
    physicalBornKernel Ω D FA FB QA QB WA WB PA PB JA JB n = (N).represented_physicalBornKernel n := by
  change bornKernel
    (physicalReferenceInstrument Ω D FA FB QA QB WA WB PA PB (a := a) (b := b) n)
    (physicalStateLayers Ω D FA FB QA QB WA WB PA PB JA JB n).state
    (physicalStateLayers Ω D FA FB QA QB WA WB PA PB JA JB n).positive
    (physicalStateLayers Ω D FA FB QA QB WA WB PA PB JA JB n).stronglyMeasurable_state
    (physicalStateLayers Ω D FA FB QA QB WA WB PA PB JA JB n).trace_one = _
  rw [physicalReferenceInstrument_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB]
  exact congrArg (fun L : MatrixProcess.PhysicalStateLayer (a := a) (b := b) (R := CommonRecord Ω) n =>
    bornKernel ((N).represented_physicalReferenceInstrument n) L.state L.positive L.stronglyMeasurable_state L.trace_one)
      (physicalStateLayers_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB n)

instance physicalBornKernel_markov (n : ℕ) :
    IsMarkovKernel (physicalBornKernel Ω D FA FB QA QB WA WB PA PB JA JB n) := by
  dsimp only [physicalBornKernel]
  exact isMarkovKernel_bornKernel _ _ _ _ _

def physicalPrefixMeasure : (n : ℕ) → Measure (History (CommonRecord Ω) n)
  | 0 => Measure.dirac PUnit.unit
  | n+1 => ((physicalPrefixMeasure n) ⊗ₘ
      physicalBornKernel Ω D FA FB QA QB WA WB PA PB JA JB n).map (appendHistory n)

theorem physicalPrefixMeasure_eq_admitted (n : ℕ) :
    physicalPrefixMeasure Ω D FA FB QA QB WA WB PA PB JA JB n = (N).represented_physicalPrefixMeasure n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((physicalPrefixMeasure Ω D FA FB QA QB WA WB PA PB JA JB n) ⊗ₘ _).map _ = _
      rw [ih, physicalBornKernel_eq_admitted]
      rfl

instance physicalPrefixMeasure_probability (n : ℕ) :
    IsProbabilityMeasure (physicalPrefixMeasure Ω D FA FB QA QB WA WB PA PB JA JB n) := by
  rw [physicalPrefixMeasure_eq_admitted]
  infer_instance

def physicalPrefixAction (n : ℕ) (s : Set (History (CommonRecord Ω) n))
    (X : JointInputMatrix a b) : Nuclear JointWorkspace :=
  ∫ h in s, chargedDecode X (physicalState Ω D FA FB QA QB WA WB PA PB JA JB n h)
    ∂physicalPrefixMeasure Ω D FA FB QA QB WA WB PA PB JA JB n

theorem physicalPrefixAction_eq_admitted (n : ℕ) (s : Set (History (CommonRecord Ω) n))
    (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    physicalPrefixAction Ω D FA FB QA QB WA WB PA PB JA JB n s X = (N).represented_physicalPrefixAction n s X := by
  rw [physicalPrefixAction, physicalState_eq_admitted, physicalPrefixMeasure_eq_admitted,
    (N).physicalPrefixAction_eq_physicalInputDensity n s hs X]
  rfl

theorem physicalState_integrable (n : ℕ) :
    Integrable (physicalState Ω D FA FB QA QB WA WB PA PB JA JB n)
      (physicalPrefixMeasure Ω D FA FB QA QB WA WB PA PB JA JB n) := by
  rw [physicalState_eq_admitted, physicalPrefixMeasure_eq_admitted]
  exact (N).represented_physicalState_integrable n

theorem physicalState_successor_setIntegral (n : ℕ)
    (h : History (CommonRecord Ω) n) (t : Set (CommonRecord Ω)) (ht : MeasurableSet t) :
    (∫ r in t, physicalState Ω D FA FB QA QB WA WB PA PB JA JB (n + 1)
      (appendHistory n (h, r))
      ∂physicalBornKernel Ω D FA FB QA QB WA WB PA PB JA JB n h) =
      (physicalReferenceInstrument Ω D FA FB QA QB WA WB PA PB (a := a) (b := b) n).operation
        h t (physicalState Ω D FA FB QA QB WA WB PA PB JA JB n h) := by
  rw [physicalState_eq_admitted, physicalBornKernel_eq_admitted,
    physicalReferenceInstrument_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB,
    physicalState_eq_admitted]
  exact (N).represented_physicalState_successor_setIntegral n h t ht

def physicalPrefixVectorMeasure (n : ℕ) :
    VectorMeasure (History (CommonRecord Ω) n) (Nuclear (PhysicalChoiWorkspace a b)) :=
  (physicalPrefixMeasure Ω D FA FB QA QB WA WB PA PB JA JB n).withDensityᵥ
    (physicalState Ω D FA FB QA QB WA WB PA PB JA JB n)

theorem physicalPrefixVectorMeasure_eq_admitted (n : ℕ) :
    physicalPrefixVectorMeasure Ω D FA FB QA QB WA WB PA PB JA JB n =
      (N).represented_physicalPrefixVectorMeasure n := by
  rw [physicalPrefixVectorMeasure, physicalPrefixMeasure_eq_admitted, physicalState_eq_admitted]
  rfl

theorem physicalPrefixVectorMeasure_apply (n : ℕ)
    (s : Set (History (CommonRecord Ω) n)) (hs : MeasurableSet s) :
    physicalPrefixVectorMeasure Ω D FA FB QA QB WA WB PA PB JA JB n s =
      ∫ h in s, physicalState Ω D FA FB QA QB WA WB PA PB JA JB n h
        ∂physicalPrefixMeasure Ω D FA FB QA QB WA WB PA PB JA JB n :=
  MeasureTheory.withDensityᵥ_apply
    (physicalState_integrable Ω D FA FB QA QB WA WB PA PB JA JB n) hs

theorem physicalPrefixVectorMeasure_successorEvent (n : ℕ)
    (s : Set (History (CommonRecord Ω) n)) (t : Set (CommonRecord Ω))
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    physicalPrefixVectorMeasure Ω D FA FB QA QB WA WB PA PB JA JB (n + 1)
      (MatrixProcess.successorEvent n s t) =
      ∫ h in s, (physicalReferenceInstrument Ω D FA FB QA QB WA WB PA PB
          (a := a) (b := b) n).operation h t
        (physicalState Ω D FA FB QA QB WA WB PA PB JA JB n h)
        ∂physicalPrefixMeasure Ω D FA FB QA QB WA WB PA PB JA JB n := by
  rw [physicalPrefixVectorMeasure_eq_admitted,
    physicalReferenceInstrument_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB,
    physicalState_eq_admitted, physicalPrefixMeasure_eq_admitted]
  exact (N).represented_physicalPrefixVectorMeasure_successorEvent n s t hs ht

end IndependentPhysicalChronology
end QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge
