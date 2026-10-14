import QuantumProver.InformationTheory.ElegantJointMeasurement.CommonPhysicalEventTensor
import QuantumProver.InformationTheory.ElegantJointMeasurement.CommonPhysicalChronologyCore
import QuantumProver.InformationTheory.WernerEndpoint.CommonPhysicalRealization
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalProcess
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalEventChronology
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalBornTransport
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalOutputTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory Set Filter Function InnerProductSpace Preorder
open scoped BigOperators Topology ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology

open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertRecordCoding
open QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM QuantumProver.ElegantJointMeasurement.PhysicalTranscriptCoding
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge
open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixNuclearKernelTransport QuantumProver.MatrixCommonPhysicalInstrument

universe u v

local instance chronologyNuclearMeasurable (a b : ℕ) :
    MeasurableSpace (Nuclear (PhysicalChoiWorkspace a b)) := borel _
local instance chronologyNuclearBorel (a b : ℕ) :
    BorelSpace (Nuclear (PhysicalChoiWorkspace a b)) := ⟨rfl⟩

section ConstantRealization

variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
  {a b : ℕ} [NeZero a] [NeZero b] (P : MatrixProcess a b R)

abbrev constantProcess := QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.realization P

def constantHistoryCoding (P : MatrixProcess a b R) (n : ℕ) :
    History R n → History (CommonRecord (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R)) n :=
  encodeHistory (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R) n ∘ (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R n).symm

theorem measurableEmbedding_constantHistoryCoding (n : ℕ) :
    MeasurableEmbedding (constantHistoryCoding P n) :=
  (measurableEmbedding_encodeHistory (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R) n).comp
    (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R n).symm.measurableEmbedding

theorem measurable_constantHistoryCoding (n : ℕ) :
    Measurable (constantHistoryCoding P n) :=
  (measurableEmbedding_constantHistoryCoding P n).measurable

@[simp] theorem constantHistoryCoding_zero (h : History R 0) :
    constantHistoryCoding P 0 h = h := rfl

theorem constantHistoryCoding_append (n : ℕ) (h : History R n) (r : R) :
    constantHistoryCoding P (n+1) (appendHistory n (h,r)) =
      appendHistory n (constantHistoryCoding P n h,
        encodeOutcome (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R) n r) := by
  have hSymm : (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R (n+1)).symm (appendHistory n (h,r)) =
      ((QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R n).symm h,r) := by
    apply (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R (n+1)).injective
    rw [MeasurableEquiv.apply_symm_apply]
    simpa only [MeasurableEquiv.apply_symm_apply] using
      (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv_append (R := R) n
        ((QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R n).symm h) r).symm
  simp only [constantHistoryCoding, Function.comp_apply, hSymm]
  exact encodeHistory_append (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R) n
    ((QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R n).symm h) r

theorem constant_initialJointOperation :
    (constantProcess P).initialJointOperation = P.initialJointOperation := by
  simp only [MatrixProcess.initialJointOperation, MatrixProcess.initialJointMap,
    QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.realization_initialAlice, QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.realization_initialBob]

theorem constant_initialChoiState :
    (constantProcess P).initialChoiState = P.initialChoiState := by
  rw [MatrixProcess.initialChoiState, MatrixProcess.initialChoiState,
    constant_initialJointOperation]

theorem constant_physicalStep_all_events (n : ℕ) (h : History R n)
    (s : Set (CommonRecord (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R))) (hs : MeasurableSet s) :
    ((constantProcess P).represented_physicalStepInstrument n).operation (constantHistoryCoding P n h) s =
      (P.represented_physicalStepInstrument n).operation h
        (encodeOutcome (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R) n ⁻¹' s) := by
  let rh := (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R n).symm h
  let hh : (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.domains P).admissible n := ⟨rh, mem_univ _⟩
  have hRaw : QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R n rh = h :=
    (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R n).apply_symm_apply h
  have hParty : (constantProcess P).aliceTurn n (constantHistoryCoding P n h) =
      P.aliceTurn n h := by
    exact (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.realization_party P n hh).trans (congrArg (P.aliceTurn n) hRaw)
  have hsRaw : MeasurableSet (encodeOutcome (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R) n ⁻¹' s) :=
    measurable_encodeOutcome (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R) n hs
  change (if (constantProcess P).aliceTurn n (constantHistoryCoding P n h) = true then
      ((constantProcess P).physicalAliceInstrument n).operation (constantHistoryCoding P n h) s
    else ((constantProcess P).physicalBobInstrument n).operation (constantHistoryCoding P n h) s) =
    (if P.aliceTurn n h = true then (P.physicalAliceInstrument n).operation h _
      else (P.physicalBobInstrument n).operation h _)
  rw [hParty]
  cases hTurn : P.aliceTurn n h with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      let ha : (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.domains P).actingDomain n false := ⟨rh, by
        refine ⟨mem_univ _, ?_⟩
        change (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.domains P).physicalParty n rh = false
        rw [QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.domains_physicalParty, hRaw, hTurn]⟩
      have hLocal : ((constantProcess P).bob n).operation (constantHistoryCoding P n h) s =
          (P.bob n).operation h (encodeOutcome (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R) n ⁻¹' s) := by
        apply ContinuousLinearMap.ext
        intro T
        have he := QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.admittedMemoryTurn_all_events P false n ha s T
        change ((constantProcess P).bob n).operation (constantHistoryCoding P n h) s T =
          (P.bob n).operation (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R n rh)
            (encodeOutcome (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R) n ⁻¹' s) T at he
        rw [hRaw] at he
        exact he
      exact QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalEventTensor.right_event_transport ((constantProcess P).bob n) (P.bob n)
        (constantHistoryCoding P n h) h s _ hs hsRaw hLocal
  | true =>
      simp only [if_true]
      let ha : (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.domains P).actingDomain n true := ⟨rh, by
        refine ⟨mem_univ _, ?_⟩
        change (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.domains P).physicalParty n rh = true
        rw [QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.domains_physicalParty, hRaw, hTurn]⟩
      have hLocal : ((constantProcess P).alice n).operation (constantHistoryCoding P n h) s =
          (P.alice n).operation h (encodeOutcome (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R) n ⁻¹' s) := by
        apply ContinuousLinearMap.ext
        intro T
        have he := QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.admittedMemoryTurn_all_events P true n ha s T
        change ((constantProcess P).alice n).operation (constantHistoryCoding P n h) s T =
          (P.alice n).operation (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R n rh)
            (encodeOutcome (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R) n ⁻¹' s) T at he
        rw [hRaw] at he
        exact he
      exact QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalEventTensor.left_event_transport ((constantProcess P).alice n) (P.alice n)
        (constantHistoryCoding P n h) h s _ hs hsRaw hLocal

theorem constant_physicalReference_all_events (n : ℕ) (h : History R n)
    (s : Set (CommonRecord (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R))) (hs : MeasurableSet s) :
    ((constantProcess P).represented_physicalReferenceInstrument n).operation (constantHistoryCoding P n h) s =
      (P.represented_physicalReferenceInstrument n).operation h
        (encodeOutcome (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R) n ⁻¹' s) := by
  change normalAmplification (R := Fin a × Fin b)
      (((constantProcess P).represented_physicalStepInstrument n).operation (constantHistoryCoding P n h) s) =
    normalAmplification (R := Fin a × Fin b)
      ((P.represented_physicalStepInstrument n).operation h (encodeOutcome (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R) n ⁻¹' s))
  rw [constant_physicalStep_all_events P n h s hs]

theorem constant_prefix_setIntegral (n : ℕ)
    (s : Set (History (CommonRecord (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R)) n)) (hs : MeasurableSet s) :
    (∫ h in constantHistoryCoding P n ⁻¹' s, P.represented_physicalState n h ∂P.represented_physicalPrefixMeasure n) =
      ∫ h in s, (constantProcess P).represented_physicalState n h ∂(constantProcess P).represented_physicalPrefixMeasure n :=
  prefix_setIntegral_of_local_events P (constantProcess P)
    (encodeOutcome (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R)) (measurable_encodeOutcome _)
    (constantHistoryCoding P) (measurable_constantHistoryCoding P)
    (constantHistoryCoding_zero P) (constantHistoryCoding_append P)
    (constant_initialChoiState P).symm (constant_physicalReference_all_events P) n s hs

theorem represented_constant_physicalPrefixAction (n : ℕ)
    (s : Set (History (CommonRecord (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R)) n))
    (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    (constantProcess P).represented_physicalPrefixAction n s X =
      P.represented_physicalPrefixAction n (constantHistoryCoding P n ⁻¹' s) X := by
  rw [(constantProcess P).physicalPrefixAction_apply n s hs X,
    P.physicalPrefixAction_apply n _ (measurable_constantHistoryCoding P n hs) X,
    constant_prefix_setIntegral P n s hs]

theorem represented_constant_physicalPrefixMeasure_map (n : ℕ) :
    (P.represented_physicalPrefixMeasure n).map (constantHistoryCoding P n) =
      (constantProcess P).represented_physicalPrefixMeasure n :=
  prefixMeasure_of_local_events P (constantProcess P)
    (encodeOutcome (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R))
    (measurable_encodeOutcome _)
    (constantHistoryCoding P) (measurable_constantHistoryCoding P)
    (constantHistoryCoding_zero P) (constantHistoryCoding_append P)
    (constant_initialChoiState P).symm (constant_physicalReference_all_events P) n

theorem represented_constant_physicalState_ae (n : ℕ) :
    (fun h => (constantProcess P).represented_physicalState n (constantHistoryCoding P n h))
      =ᵐ[P.represented_physicalPrefixMeasure n] P.represented_physicalState n :=
  state_ae_of_local_events P (constantProcess P)
    (encodeOutcome (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R))
    (measurable_encodeOutcome _)
    (constantHistoryCoding P) (measurable_constantHistoryCoding P)
    (constantHistoryCoding_zero P) (constantHistoryCoding_append P)
    (constant_initialChoiState P).symm (constant_physicalReference_all_events P) n
    (measurableEmbedding_constantHistoryCoding P n)
local notation "ΩR" => QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.constantOutcomes R
local notation "DP" => QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.domains P
local notation "FP" => QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.sourceFamily P
local notation "QAP" => QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.outputFamily P true
local notation "QBP" => QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.outputFamily P false
local notation "WAP" => QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.wiring P true
local notation "WBP" => QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.wiring P false
local notation "PAP" => QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.localFamily P true
local notation "PBP" => QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.localFamily P false

theorem constant_physicalPrefixMeasure_map (n : ℕ) :
    (P.represented_physicalPrefixMeasure n).map (constantHistoryCoding P n) =
      physicalPrefixMeasure ΩR DP FP FP QAP QBP WAP WBP PAP PBP
        P.initialAlice P.initialBob n := by
  rw [physicalPrefixMeasure_eq_admitted]
  exact represented_constant_physicalPrefixMeasure_map P n

theorem constant_physicalState_ae (n : ℕ) :
    (fun h => physicalState ΩR DP FP FP QAP QBP WAP WBP PAP PBP
      P.initialAlice P.initialBob n (constantHistoryCoding P n h))
      =ᵐ[P.represented_physicalPrefixMeasure n] P.represented_physicalState n := by
  simp only [physicalState_eq_admitted]
  exact represented_constant_physicalState_ae P n

theorem constant_physicalPrefixAction (n : ℕ)
    (s : Set (History (CommonRecord ΩR) n)) (hs : MeasurableSet s)
    (X : JointInputMatrix a b) :
    physicalPrefixAction ΩR DP FP FP QAP QBP WAP WBP PAP PBP
      P.initialAlice P.initialBob n s X =
        P.represented_physicalPrefixAction n (constantHistoryCoding P n ⁻¹' s) X := by
  exact (physicalPrefixAction_eq_admitted ΩR DP FP FP QAP QBP WAP WBP PAP PBP
    P.initialAlice P.initialBob n s hs X).trans (represented_constant_physicalPrefixAction P n s hs X)

theorem constant_physicalPrefixAction_image (n : ℕ) (s : Set (History R n))
    (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    physicalPrefixAction ΩR DP FP FP QAP QBP WAP WBP PAP PBP
      P.initialAlice P.initialBob n (constantHistoryCoding P n '' s) X =
        P.represented_physicalPrefixAction n s X := by
  rw [constant_physicalPrefixAction P n _
      ((measurableEmbedding_constantHistoryCoding P n).measurableSet_image' hs) X,
    (measurableEmbedding_constantHistoryCoding P n).injective.preimage_image s]

theorem constant_chosenJointRecover (n : ℕ) (h : (DP).admissible n) :
    chosenJointRecover ΩR DP FP FP QAP QBP WAP WBP n h =
      ContinuousLinearMap.id ℂ (Nuclear JointWorkspace) := by
  change sandwich (tensorMap
    ((selectedMemory ΩR DP true FP QAP WAP n).family.embedding h).toContinuousLinearMap
    ((selectedMemory ΩR DP false FP QBP WBP n).family.embedding h).toContinuousLinearMap).adjoint = _
  rw [QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.selectedMemory_embedding, QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.selectedMemory_embedding,
    commonCoordinateEmbedding_clm_eq_id, tensorMap_id_id, ContinuousLinearMap.adjoint_id]
  ext T
  apply QuantumProver.NuclearOperator.toOperator_injective
  simp only [sandwich, toOperator_compose,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

theorem constant_physicalInputDensity_ae (n : ℕ) (X : JointInputMatrix a b) :
    (fun h => physicalInputDensity ΩR DP FP FP QAP QBP WAP WBP PAP PBP
      P.initialAlice P.initialBob n X
        ⟨(QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R n).symm h, mem_univ _⟩)
      =ᵐ[P.represented_physicalPrefixMeasure n] P.represented_physicalInputDensity n X := by
  filter_upwards [constant_physicalState_ae P n] with h hh
  simp only [physicalInputDensity, constant_chosenJointRecover,
    ContinuousLinearMap.id_apply, MatrixProcess.represented_physicalInputDensity]
  exact congrArg (chargedDecode X) hh

def constantTranscriptEquiv (P : MatrixProcess a b R) : PhysicalTranscript ΩR ≃ᵐ Transcript R :=
  MeasurableEquiv.refl _

def constantTranscriptCoding (P : MatrixProcess a b R) :
    Transcript R → Transcript (CommonRecord ΩR) :=
  encodePhysicalTranscript ΩR ∘ (constantTranscriptEquiv P).symm

theorem measurable_constantTranscriptCoding : Measurable (constantTranscriptCoding P) :=
  (measurable_encodePhysicalTranscript ΩR).comp (constantTranscriptEquiv P).symm.measurable

theorem measurableEmbedding_constantTranscriptCoding :
    MeasurableEmbedding (constantTranscriptCoding P) :=
  (measurableEmbedding_encodePhysicalTranscript ΩR).comp
    (constantTranscriptEquiv P).symm.measurableEmbedding

theorem constant_historyEquiv_roundPrefix (P : MatrixProcess a b R) (t : Transcript R) (N : ℕ) :
    QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R (N+1) (roundPrefix ΩR t (N+1)) =
      frestrictLe (π := fun _ => R) N t := by
  induction N with
  | zero =>
      funext i
      change t 0 = t i.val
      have hi : i.val = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property)
      rw [hi]
  | succ N ih =>
      change QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.prefixStepEquiv N
          (QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization.historyEquiv R (N+1) (roundPrefix ΩR t (N+1)), t (N+1)) = _
      rw [ih]
      apply (QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.prefixStepEquiv (R := R) N).symm.injective
      simp only [MeasurableEquiv.symm_apply_apply]
      apply Prod.ext <;> rfl

theorem constant_coding_transcript_prefix (t : Transcript R) (N : ℕ) :
    constantHistoryCoding P (N+1) (frestrictLe (π := fun _ => R) N t) =
      frestrictLe (π := fun _ => CommonRecord ΩR) N (encodePhysicalTranscript ΩR t) := by
  rw [← constant_historyEquiv_roundPrefix P t N]
  simp only [constantHistoryCoding, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  exact (encodePhysicalTranscript_prefix ΩR t N).symm

theorem constant_physicalTranscriptVectorMeasure_map :
    P.represented_physicalTranscriptVectorMeasure.map (constantTranscriptCoding P) =
      (constantProcess P).represented_physicalTranscriptVectorMeasure := by
  apply vectorMeasure_eq_of_prefix
  intro N s hs
  rw [VectorMeasure.map_apply _ (measurable_constantTranscriptCoding P)
    (hs.preimage (measurable_frestrictLe N))]
  have hPre : constantTranscriptCoding P ⁻¹'
      (frestrictLe (π := fun _ => CommonRecord ΩR) N ⁻¹' s) =
      frestrictLe (π := fun _ => R) N ⁻¹' (constantHistoryCoding P (N+1) ⁻¹' s) := by
    ext t
    change frestrictLe (π := fun _ => CommonRecord ΩR) N (encodePhysicalTranscript ΩR t) ∈ s ↔
      constantHistoryCoding P (N+1) (frestrictLe (π := fun _ => R) N t) ∈ s
    rw [constant_coding_transcript_prefix]
  rw [hPre, P.represented_physicalTranscriptVectorMeasure_prefix N _
    (measurable_constantHistoryCoding P (N+1) hs),
    (constantProcess P).represented_physicalTranscriptVectorMeasure_prefix N s hs]
  ext i j
  change QuantumProver.HilbertNuclearTrace.trace (P.represented_physicalPrefixAction (N+1) _ _) =
    QuantumProver.HilbertNuclearTrace.trace ((constantProcess P).represented_physicalPrefixAction (N+1) s _)
  exact congrArg QuantumProver.HilbertNuclearTrace.trace
    (represented_constant_physicalPrefixAction P (N+1) s hs _).symm

theorem constant_physicalBornMeasure_map (X : JointInputMatrix a b) (hX : X.PosSemidef) :
    (P.represented_physicalBornMeasure X hX).map (constantTranscriptCoding P) =
      (constantProcess P).represented_physicalBornMeasure X hX := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_constantTranscriptCoding P) hs,
    P.physicalBornMeasure_apply X hX _ ((measurable_constantTranscriptCoding P) hs),
    (constantProcess P).physicalBornMeasure_apply X hX s hs,
    ← constant_physicalTranscriptVectorMeasure_map P,
    VectorMeasure.map_apply _ (measurable_constantTranscriptCoding P) hs]

def constantPhysicalBornMeasure (X : JointInputMatrix a b) (hX : X.PosSemidef) :
    Measure (Transcript R) :=
  physicalBornMeasure ΩR DP FP FP QAP QBP WAP WBP PAP PBP
    P.initialAlice P.initialBob X hX

theorem constantPhysicalBornMeasure_eq_physical (X : JointInputMatrix a b)
    (hX : X.PosSemidef) : constantPhysicalBornMeasure P X hX = P.represented_physicalBornMeasure X hX := by
  change (physicalCodedBornMeasure ΩR DP FP FP QAP QBP WAP WBP PAP PBP
      P.initialAlice P.initialBob X hX).comap (constantTranscriptCoding P) = _
  rw [physicalCodedBornMeasure_eq_admitted]
  exact (congrArg
    (fun μ : Measure (Transcript (CommonRecord ΩR)) => μ.comap (constantTranscriptCoding P))
    (constant_physicalBornMeasure_map P X hX).symm).trans
      ((measurableEmbedding_constantTranscriptCoding P).comap_map _)

theorem constantPhysicalBornMeasure_map_physical (X : JointInputMatrix a b)
    (hX : X.PosSemidef) :
    (constantPhysicalBornMeasure P X hX).map (constantTranscriptEquiv P) =
      P.represented_physicalBornMeasure X hX := by
  rw [constantPhysicalBornMeasure_eq_physical]
  exact Measure.map_id

end ConstantRealization

end QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology
