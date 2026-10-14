import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCostModels
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalAdmission
import QuantumProver.QuantumChannels.CommonPhysicalInstrument

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Set Function
open scoped BigOperators Topology Classical

namespace QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization

open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertRecordCoding QuantumProver.ElegantJointMeasurement.HilbertSquareProcess
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.MatrixNormalSourceCompletion
open QuantumProver.MatrixCommonPhysicalInstrument
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption

universe u
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : ℕ} (P : MatrixProcess a b R)

def constantOutcomes (R : Type u) : ℕ → Type u := fun _ => R

instance constantOutcomes_measurableSpace (n : ℕ) :
    MeasurableSpace (constantOutcomes R n) := inferInstanceAs (MeasurableSpace R)

instance constantOutcomes_standardBorelSpace (n : ℕ) :
    StandardBorelSpace (constantOutcomes R n) := inferInstanceAs (StandardBorelSpace R)

def historyEquiv (R : Type u) [MeasurableSpace R] :
    (n : ℕ) → RoundHistory (constantOutcomes R) n ≃ᵐ History R n
  | 0 => MeasurableEquiv.refl PUnit
  | n+1 => ((historyEquiv R n).prodCongr (MeasurableEquiv.refl R)).trans
      (QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.appendHistory n)

@[simp] theorem historyEquiv_zero (h : RoundHistory (constantOutcomes R) 0) :
    historyEquiv R 0 h = h := rfl

@[simp] theorem historyEquiv_append (n : ℕ)
    (h : RoundHistory (constantOutcomes R) n) (r : R) :
    historyEquiv R (n+1) (h,r) =
      QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.appendHistory n (historyEquiv R n h,r) := rfl

def domains : PhysicalDomains (constantOutcomes R) where
  admissible _ := univ
  admissible_measurable _ := MeasurableSet.univ
  initial_valid := mem_univ _
  party n h := P.aliceTurn n (historyEquiv R n h.val)
  party_measurable n := (P.turn_measurable n).comp
    ((historyEquiv R n).measurable.comp measurable_subtype_coe)
  graph _ := univ
  graph_measurable _ := MeasurableSet.univ
  append_valid _ _ := mem_univ _

@[simp] theorem domains_admissible (n : ℕ) :
    (domains P).admissible n = univ := rfl

@[simp] theorem domains_graph (n : ℕ) : (domains P).graph n = univ := rfl

@[simp] theorem domains_party (n : ℕ) (h : (domains P).admissible n) :
    (domains P).party n h = P.aliceTurn n (historyEquiv R n h.val) := rfl

@[simp] theorem domains_physicalParty (n : ℕ) (h : RoundHistory (constantOutcomes R) n) :
    (domains P).physicalParty n h = P.aliceTurn n (historyEquiv R n h) := by
  simp only [PhysicalDomains.physicalParty, domains, mem_univ, ↓reduceDIte]

@[simp] theorem domains_actingGraph (n : ℕ) (side : Bool) :
    (domains P).actingGraph n side = univ := by
  simp only [PhysicalDomains.actingGraph, domains_graph, preimage_univ]

def sourceFamily (n : ℕ) :
    FundamentalFamily (fun _ : (domains P).admissible n => CommonHilbert) :=
  commonFundamentalFamily

def outputFamily (side : Bool) (n : ℕ) :
    FundamentalFamily (fun _ : (domains P).actingDomain n side × constantOutcomes R n =>
      CommonHilbert) := commonFundamentalFamily

@[simp] theorem sourceFamily_vector (n : ℕ) (h : (domains P).admissible n) (i : ℕ) :
    (sourceFamily P n).vector h i = commonBasis i := rfl

@[simp] theorem outputFamily_vector (side : Bool) (n : ℕ)
    (z : (domains P).actingDomain n side × constantOutcomes R n) (i : ℕ) :
    (outputFamily P side n).vector z i = commonBasis i := rfl

def wiring (side : Bool) : PhysicalMemoryWiring (constantOutcomes R) (domains P)
    side (sourceFamily P) (outputFamily P side) where
  acted _ _ := LinearIsometryEquiv.refl ℂ CommonHilbert
  acted_measurable n i j := by
    simpa only [outputOnSuccessor, targetOnSuccessor, pullbackFamily, sourceFamily,
      outputFamily, commonFundamentalFamily, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.coe_refl, id_eq] using
      (measurable_const : Measurable (fun _ : (domains P).successorDomain n side =>
        inner ℂ (commonBasis i) (commonBasis j)))
  idle _ _ := LinearIsometryEquiv.refl ℂ CommonHilbert
  idle_measurable n i j := by
    simpa only [sourceOnSuccessor, targetOnSuccessor, pullbackFamily, sourceFamily,
      commonFundamentalFamily, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.coe_refl, id_eq] using
      (measurable_const : Measurable (fun _ : (domains P).successorDomain n (!side) =>
        inner ℂ (commonBasis i) (commonBasis j)))

@[simp] theorem wiring_acted_apply (side : Bool) (n : ℕ)
    (h : (domains P).successorDomain n side) (x : CommonHilbert) :
    (wiring P side).acted n h x = x := rfl

@[simp] theorem wiring_idle_apply (side : Bool) (n : ℕ)
    (h : (domains P).successorDomain n (!side)) (x : CommonHilbert) :
    (wiring P side).idle n h x = x := rfl

theorem selectedMemory_vector (side : Bool) (n : ℕ)
    (h : (domains P).admissible n) (i : ℕ) :
    (selectedMemory (constantOutcomes R) (domains P) side
      (sourceFamily P) (outputFamily P side) (wiring P side) n).family.vector h i =
      commonBasis i := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [selectedMemory, chooseNextMemory, glueFamily]
      split_ifs
      · change (wiring P side).acted n _ (commonBasis i) = commonBasis i
        exact wiring_acted_apply P side n _ _
      · change (wiring P side).idle n _
          ((selectedMemory (constantOutcomes R) (domains P) side
            (sourceFamily P) (outputFamily P side) (wiring P side) n).family.vector _ i) = _
        rw [wiring_idle_apply]
        exact ih _
      · rfl

theorem selectedMemory_embedding (side : Bool) (n : ℕ)
    (h : (domains P).admissible n) :
    (selectedMemory (constantOutcomes R) (domains P) side
      (sourceFamily P) (outputFamily P side) (wiring P side) n).family.embedding h =
      commonCoordinateEmbedding := by
  apply LinearIsometry.ext
  intro x
  have he := family_embedding_naturality (sourceFamily P n)
    (selectedMemory (constantOutcomes R) (domains P) side
      (sourceFamily P) (outputFamily P side) (wiring P side) n).family
    (fun _ => LinearIsometryEquiv.refl ℂ CommonHilbert)
    (fun z i => selectedMemory_vector P side n z i) h x
  exact he

@[simp] theorem selectedMemory_embedding_apply (side : Bool) (n : ℕ)
    (h : (domains P).admissible n) (x : CommonHilbert) :
    (selectedMemory (constantOutcomes R) (domains P) side
      (sourceFamily P) (outputFamily P side) (wiring P side) n).family.embedding h x = x := by
  rw [selectedMemory_embedding]
  exact commonCoordinateEmbedding_apply_eq_self x

def sideInstrument (side : Bool) (n : ℕ) :
    Instrument CommonHilbert CommonHilbert (History R n) R :=
  if side then P.alice n else P.bob n

def physicalSide (side : Bool) (n : ℕ) :
    Instrument CommonHilbert CommonHilbert ((domains P).actingDomain n side) R where
  operation h s := (sideInstrument P side n).operation (historyEquiv R n h.val) s
  empty h := (sideInstrument P side n).empty (historyEquiv R n h.val)
  countable_additivity h s hs hd T :=
    (sideInstrument P side n).countable_additivity (historyEquiv R n h.val) s hs hd T
  completelyPositive h s hs :=
    (sideInstrument P side n).completelyPositive (historyEquiv R n h.val) s hs
  measurable_coordinate s hs T x y :=
    ((sideInstrument P side n).measurable_coordinate s hs T x y).comp
      ((historyEquiv R n).measurable.comp measurable_subtype_coe)
  trace_preserving h T :=
    (sideInstrument P side n).trace_preserving (historyEquiv R n h.val) T

def localFamily (side : Bool) : PhysicalLocalFamily (constantOutcomes R) (domains P)
    side (sourceFamily P) (outputFamily P side) where
  instrument n := recordedSourceInstrument (physicalSide P side n)
  off_graph n h := by
    have hEmpty : {x | (h,x) ∉ (domains P).actingGraph n side} = ∅ := by
      simp only [domains_actingGraph, mem_univ, not_true_eq_false, setOf_false]
    rw [hEmpty]
    exact (sourceInstrument (physicalSide P side n)).empty h

@[simp] theorem localFamily_physical_operation (side : Bool) (n : ℕ)
    (h : (domains P).actingDomain n side) (s : Set R) :
    ((localFamily P side).instrument n).represented_physical.operation h s =
      (sideInstrument P side n).operation (historyEquiv R n h.val) s := by
  change (sourceInstrument (physicalSide P side n)).operation h s = _
  rw [sourceInstrument_operation]
  rfl

def realization : MatrixProcess a b (CommonRecord (constantOutcomes R)) :=
  ofPhysicalFamilies (constantOutcomes R) (domains P)
    (sourceFamily P) (sourceFamily P) (outputFamily P true) (outputFamily P false)
    (wiring P true) (wiring P false) (localFamily P true) (localFamily P false)
    P.initialAlice P.initialBob

@[simp] theorem realization_initialAlice : (realization P).initialAlice = P.initialAlice := by
  apply LinearIsometry.ext
  intro x
  change commonCoordinateEmbedding (P.initialAlice x) = P.initialAlice x
  exact commonCoordinateEmbedding_apply_eq_self _

@[simp] theorem realization_initialBob : (realization P).initialBob = P.initialBob := by
  apply LinearIsometry.ext
  intro x
  change commonCoordinateEmbedding (P.initialBob x) = P.initialBob x
  exact commonCoordinateEmbedding_apply_eq_self _

theorem realization_initialJointCode
    (T : QuantumProver.NuclearOperator.Nuclear ℂ
      (QuantumProver.MatrixNuclearTensor.Joint (EuclideanSpace ℂ (Fin a)) (EuclideanSpace ℂ (Fin b)))
      (QuantumProver.MatrixNuclearTensor.Joint (EuclideanSpace ℂ (Fin a)) (EuclideanSpace ℂ (Fin b)))) :
    physicalJointCode (realization P).initialAlice (realization P).initialBob T =
      physicalJointCode P.initialAlice P.initialBob T := by
  rw [realization_initialAlice, realization_initialBob]

@[simp] theorem realization_party (n : ℕ) (h : (domains P).admissible n) :
    (realization P).aliceTurn n (encodeHistory (constantOutcomes R) n h.val) =
      P.aliceTurn n (historyEquiv R n h.val) :=
  ofPhysicalFamilies_party (constantOutcomes R) (domains P)
    (sourceFamily P) (sourceFamily P) (outputFamily P true) (outputFamily P false)
    (wiring P true) (wiring P false) (localFamily P true) (localFamily P false)
    P.initialAlice P.initialBob n h

theorem admittedMemoryTurn_physical_event (side : Bool) (n : ℕ)
    (h : (domains P).actingDomain n side) (s : Set R)
    (T : QuantumProver.MatrixNormalSourceCompletion.Nuc CommonHilbert) :
    (admittedMemoryTurn (constantOutcomes R) (domains P) side
      (sourceFamily P) (outputFamily P side) (wiring P side) (localFamily P side) n).operation
      (encodeHistory (constantOutcomes R) n h.val)
      (encodeOutcome (constantOutcomes R) n '' s) T =
      (sideInstrument P side n).operation (historyEquiv R n h.val) s T := by
  have he := admittedMemoryTurn_physical_input (constantOutcomes R) (domains P) side
    (sourceFamily P) (outputFamily P side) (wiring P side) (localFamily P side) n h s T
  simpa only [selectedMemory_embedding, padNuclear_commonCoordinateEmbedding,
    localFamily_physical_operation] using he

theorem admittedMemoryTurn_all_events (side : Bool) (n : ℕ)
    (h : (domains P).actingDomain n side) (s : Set (CommonRecord (constantOutcomes R)))
    (T : QuantumProver.MatrixNormalSourceCompletion.Nuc CommonHilbert) :
    (admittedMemoryTurn (constantOutcomes R) (domains P) side
      (sourceFamily P) (outputFamily P side) (wiring P side) (localFamily P side) n).operation
      (encodeHistory (constantOutcomes R) n h.val) s T =
      (sideInstrument P side n).operation (historyEquiv R n h.val)
        (encodeOutcome (constantOutcomes R) n ⁻¹' s) T := by
  have he := QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission.admittedMemoryTurn_all_events
    (constantOutcomes R) (domains P) side
    (sourceFamily P) (outputFamily P side) (wiring P side) (localFamily P side) n h s T
  calc
    _ = ((localFamily P side).instrument n).represented_physical.operation h
        (encodeOutcome (constantOutcomes R) n ⁻¹' s) T := by
      simpa only [selectedMemory_embedding, padNuclear_commonCoordinateEmbedding] using he
    _ = _ := congrArg (fun L : Nuc CommonHilbert →L[ℂ] Nuc CommonHilbert => L T)
      (localFamily_physical_operation P side n h (encodeOutcome (constantOutcomes R) n ⁻¹' s))

theorem admittedMemoryTurn_dummy_zero (side : Bool) (n : ℕ)
    (h : (domains P).actingDomain n side)
    (T : QuantumProver.MatrixNormalSourceCompletion.Nuc CommonHilbert) :
    (admittedMemoryTurn (constantOutcomes R) (domains P) side
      (sourceFamily P) (outputFamily P side) (wiring P side) (localFamily P side) n).operation
      (encodeHistory (constantOutcomes R) n h.val) {dummyRecord (constantOutcomes R)} T = 0 := by
  have he := admittedMemoryTurn_dummy_on_physical (constantOutcomes R) (domains P) side
    (sourceFamily P) (outputFamily P side) (wiring P side) (localFamily P side) n h T
  simpa only [selectedMemory_embedding, padNuclear_commonCoordinateEmbedding] using he

end QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization
