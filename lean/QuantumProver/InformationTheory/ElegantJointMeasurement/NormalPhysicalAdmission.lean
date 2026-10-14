import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCostModels
import QuantumProver.QuantumChannels.NormalSourceCompletion
import QuantumProver.InformationTheory.ElegantJointMeasurement.RecordCoding
import QuantumProver.QuantumChannels.NormalRightTensor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Function InnerProductSpace
open scoped BigOperators Topology Classical

namespace QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission

open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertRecordCoding QuantumProver.ElegantJointMeasurement.HilbertSquareProcess
open QuantumProver.ElegantJointMeasurement.MeasurableHilbertField QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.HilbertChoi
open QuantumProver.MatrixNormalSourceCompletion QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixNormalTensorInstrument QuantumProver.MatrixNormalRightTensor
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression (compose)

universe u v w

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
  [∀ n, StandardBorelSpace (Ω n)]

def completedOutcome (n : ℕ) : Ω n ⊕ Unit → CommonRecord Ω
  | Sum.inl x => encodeOutcome Ω n x
  | Sum.inr _ => dummyRecord Ω

theorem measurable_completedOutcome (n : ℕ) : Measurable (completedOutcome Ω n) :=
  (measurable_encodeOutcome Ω n).sumElim measurable_const

theorem completedOutcome_preimage_physical (n : ℕ) (s : Set (Ω n)) :
    completedOutcome Ω n ⁻¹' (encodeOutcome Ω n '' s) = Sum.inl '' s := by
  ext z
  cases z with
  | inl x =>
      simpa [completedOutcome] using
        Iff.of_eq (congrArg (fun A => x ∈ A) (encodeOutcome_preimage_image Ω n s))
  | inr z => simp [completedOutcome, encodeOutcome, dummyRecord]

theorem completedOutcome_preimage_dummy (n : ℕ) :
    completedOutcome Ω n ⁻¹' {dummyRecord Ω} = {Sum.inr ()} := by
  ext z
  cases z <;> simp [completedOutcome, encodeOutcome, dummyRecord]

theorem completedOutcome_physical_preimage (n : ℕ) (s : Set (CommonRecord Ω)) :
    Sum.inl ⁻¹' (completedOutcome Ω n ⁻¹' s) = encodeOutcome Ω n ⁻¹' s := rfl

section ActiveTurn

variable (n : ℕ) (S : Set (RoundHistory Ω n)) (hS : MeasurableSet S)
  {E : S → Type v} [∀ h, NormedAddCommGroup (E h)]
  [∀ h, InnerProductSpace ℂ (E h)] [∀ h, CompleteSpace (E h)]
  (F : FundamentalFamily E) (P : SourceInstrument F (Ω n))

def admittedTurn : Instrument CommonHilbert CommonHilbert
    (History (CommonRecord Ω) n) (CommonRecord Ω) :=
  liftInstrumentAlongEmbedding (completeSourceInstrument P)
    (fun h : S => encodeHistory Ω n h.val)
    (measurableEmbedding_encodeAdmissibleHistory Ω n S hS)
    (completedOutcome Ω n) (measurable_completedOutcome Ω n) (dummyRecord Ω)

theorem admittedTurn_encoded (h : S) (s : Set (CommonRecord Ω)) :
    (admittedTurn Ω n S hS F P).operation (encodeHistory Ω n h.val) s =
      (completeSourceInstrument P).operation h (completedOutcome Ω n ⁻¹' s) := by
  exact liftInstrumentAlongEmbedding_encoded _ _ _ _ _ _ h s

theorem admittedTurn_physical_event (h : S) (s : Set (Ω n)) :
    (admittedTurn Ω n S hS F P).operation (encodeHistory Ω n h.val)
      (encodeOutcome Ω n '' s) = sourceCodedOperation P h s := by
  rw [admittedTurn_encoded, completedOutcome_preimage_physical,
    completeSourceInstrument_physical_event]

theorem admittedTurn_physical_input (h : S) (s : Set (Ω n))
    (T : Nuc (E h)) :
    (admittedTurn Ω n S hS F P).operation (encodeHistory Ω n h.val)
      (encodeOutcome Ω n '' s) (padNuclear (F.embedding h) T) = P.operation h s T := by
  rw [admittedTurn_physical_event]
  exact sourceCodedOperation_on_physical P h s T

theorem admittedTurn_all_events_on_physical (h : S) (s : Set (CommonRecord Ω))
    (T : Nuc (E h)) :
    (admittedTurn Ω n S hS F P).operation (encodeHistory Ω n h.val) s
      (padNuclear (F.embedding h) T) = P.operation h (encodeOutcome Ω n ⁻¹' s) T := by
  rw [admittedTurn_encoded, completeSourceInstrument_all_events_on_physical,
    completedOutcome_physical_preimage]

theorem admittedTurn_dummy_on_physical (h : S) (T : Nuc (E h)) :
    (admittedTurn Ω n S hS F P).operation (encodeHistory Ω n h.val) {dummyRecord Ω}
      (padNuclear (F.embedding h) T) = 0 := by
  rw [admittedTurn_all_events_on_physical, encodeOutcome_preimage_dummy, P.empty]
  exact ContinuousLinearMap.zero_apply T

theorem admittedTurn_invalid (h : History (CommonRecord Ω) n)
    (hh : h ∉ range (fun z : S => encodeHistory Ω n z.val))
    (s : Set (CommonRecord Ω)) :
    (admittedTurn Ω n S hS F P).operation h s =
      if dummyRecord Ω ∈ s then ContinuousLinearMap.id ℂ (Nuc CommonHilbert) else 0 := by
  simp only [admittedTurn, liftInstrumentAlongEmbedding, hh, ↓reduceDIte, dummyInstrument]

theorem admittedTurn_off_graph_on_physical
    (G : Set (S × Ω n))
    (hSupport : ∀ h, P.operation h {x | (h,x) ∉ G} = 0)
    (h : S) (T : Nuc (E h)) :
    (admittedTurn Ω n S hS F P).operation (encodeHistory Ω n h.val)
      {r | (h,r) ∉ encodedAdmissibleGraph Ω n G}
      (padNuclear (F.embedding h) T) = 0 := by
  rw [admittedTurn_all_events_on_physical]
  have he : encodeOutcome Ω n ⁻¹' {r | (h,r) ∉ encodedAdmissibleGraph Ω n G} =
      {x | (h,x) ∉ G} := by
    ext x
    have hp := congrArg (fun A => (h,x) ∈ A) (encodedAdmissibleGraph_preimage Ω n G)
    simpa only [mem_preimage, mem_ofPred_eq, encodeGraphMap] using Iff.of_eq (congrArg Not hp)
  rw [he, hSupport h]
  exact ContinuousLinearMap.zero_apply T

section FiniteReference

variable {R : Type} [Fintype R] [DecidableEq R]
local instance blockComplete {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] : CompleteSpace (BlockSpace R V) :=
  PiLp.completeSpace 2 (fun _ : R => V)

theorem admittedTurn_amplified_physical_input (h : S) (s : Set (Ω n))
    (T : Nuc (BlockSpace R (E h))) :
    normalAmplification ((admittedTurn Ω n S hS F P).operation
      (encodeHistory Ω n h.val) (encodeOutcome Ω n '' s))
      (normalAmplification (padNuclear (F.embedding h)) T) =
        normalAmplification (P.operation h s) T := by
  rw [admittedTurn_encoded, completedOutcome_preimage_physical]
  exact completeSourceInstrument_amplified_physical_input P h s T

theorem admittedTurn_amplified_all_events_on_physical (h : S)
    (s : Set (CommonRecord Ω)) (T : Nuc (BlockSpace R (E h))) :
    normalAmplification ((admittedTurn Ω n S hS F P).operation
      (encodeHistory Ω n h.val) s)
      (normalAmplification (padNuclear (F.embedding h)) T) =
        normalAmplification (P.operation h (encodeOutcome Ω n ⁻¹' s)) T := by
  rw [admittedTurn_encoded]
  exact completeSourceInstrument_amplified_all_events_on_physical P h _ T

theorem admittedTurn_amplified_dummy_on_physical (h : S)
    (T : Nuc (BlockSpace R (E h))) :
    normalAmplification ((admittedTurn Ω n S hS F P).operation
      (encodeHistory Ω n h.val) {dummyRecord Ω})
      (normalAmplification (padNuclear (F.embedding h)) T) = 0 := by
  rw [admittedTurn_encoded, completedOutcome_preimage_dummy]
  exact completeSourceInstrument_amplified_dummy_on_physical P h T

end FiniteReference

section Spectator

variable {V : Type w} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def leftSourceCode (h : S) : Nuc (Joint (E h) V) →L[ℂ] Nuc (Joint CommonHilbert V) :=
  compose (tensorMap (F.embedding h).toContinuousLinearMap (ContinuousLinearMap.id ℂ V))
    (tensorMap (F.embedding h).toContinuousLinearMap.adjoint (ContinuousLinearMap.id ℂ V))

theorem leftSourceCode_tensor (h : S) (T : Nuc (E h)) (U : Nuc V) :
    leftSourceCode (V := V) Ω n S F h
      (tensorNuclear (E := E h) (E' := E h) (F := V) (F' := V) T U) =
      tensorNuclear (E := CommonHilbert) (E' := CommonHilbert) (F := V) (F' := V)
        (padNuclear (F.embedding h) T) U := by
  simpa only [leftSourceCode, padNuclear,
    QuantumProver.MatrixNormalTensorExtension.compose_id_id_apply] using
      (tensorNuclear_compose (F.embedding h).toContinuousLinearMap
        (F.embedding h).toContinuousLinearMap.adjoint
        (ContinuousLinearMap.id ℂ V) (ContinuousLinearMap.id ℂ V) T U).symm

theorem admittedTurn_left_physical_event (h : S) (s : Set (Ω n))
    (hs : MeasurableSet s) (W : Nuc (Joint (E h) V)) :
    tensorOperation (G := V) (admittedTurn Ω n S hS F P) (encodeHistory Ω n h.val)
      (encodeOutcome Ω n '' s) (leftSourceCode Ω n S F h W) =
        tensorOperation (G := V) (physicalInstrument P h) () s W := by
  have heq : (tensorOperation (G := V) (admittedTurn Ω n S hS F P)
      (encodeHistory Ω n h.val) (encodeOutcome Ω n '' s)).comp (leftSourceCode Ω n S F h) =
      tensorOperation (G := V) (physicalInstrument P h) () s := by
    apply nuclear_joint_clm_ext_tensors
    intro T U
    simp only [ContinuousLinearMap.comp_apply, leftSourceCode_tensor]
    rw [tensorOperation_tensor _ _ _
      ((measurableEmbedding_encodeOutcome Ω n).measurableSet_image' hs),
      admittedTurn_physical_input, tensorOperation_tensor _ _ _ hs]
    rfl
  exact congrArg (fun L => L W) heq

def rightSourceCode (h : S) : Nuc (Joint V (E h)) →L[ℂ] Nuc (Joint V CommonHilbert) :=
  compose (tensorMap (ContinuousLinearMap.id ℂ V) (F.embedding h).toContinuousLinearMap)
    (tensorMap (ContinuousLinearMap.id ℂ V) (F.embedding h).toContinuousLinearMap.adjoint)

theorem rightSourceCode_tensor (h : S) (T : Nuc V) (U : Nuc (E h)) :
    rightSourceCode (V := V) Ω n S F h
      (tensorNuclear (E := V) (E' := V) (F := E h) (F' := E h) T U) =
      tensorNuclear (E := V) (E' := V) (F := CommonHilbert) (F' := CommonHilbert)
        T (padNuclear (F.embedding h) U) := by
  simpa only [rightSourceCode, padNuclear,
    QuantumProver.MatrixNormalTensorExtension.compose_id_id_apply] using
      (tensorNuclear_compose (ContinuousLinearMap.id ℂ V) (ContinuousLinearMap.id ℂ V)
        (F.embedding h).toContinuousLinearMap
        (F.embedding h).toContinuousLinearMap.adjoint T U).symm

theorem admittedTurn_right_physical_event (h : S) (s : Set (Ω n))
    (hs : MeasurableSet s) (W : Nuc (Joint V (E h))) :
    rightTensorOperation (G := V) (admittedTurn Ω n S hS F P) (encodeHistory Ω n h.val)
      (encodeOutcome Ω n '' s) (rightSourceCode Ω n S F h W) =
        rightTensorOperation (G := V) (physicalInstrument P h) () s W := by
  have heq : (rightTensorOperation (G := V) (admittedTurn Ω n S hS F P)
      (encodeHistory Ω n h.val) (encodeOutcome Ω n '' s)).comp (rightSourceCode Ω n S F h) =
      rightTensorOperation (G := V) (physicalInstrument P h) () s := by
    apply nuclear_joint_clm_ext_tensors
    intro T U
    simp only [ContinuousLinearMap.comp_apply, rightSourceCode_tensor]
    rw [rightTensorOperation_tensor _ _ _
      ((measurableEmbedding_encodeOutcome Ω n).measurableSet_image' hs),
      admittedTurn_physical_input, rightTensorOperation_tensor _ _ _ hs]
    rfl
  exact congrArg (fun L => L W) heq

end Spectator
end ActiveTurn

section PhysicalNaturality

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

theorem residual_formula (v : ℕ → X) (n : ℕ) :
    QuantumProver.CountableGramSchmidt.residual v n = v n - ∑ i ∈ Finset.Iio n,
      (inner ℂ (QuantumProver.CountableGramSchmidt.residual v i) (v n) /
        (‖QuantumProver.CountableGramSchmidt.residual v i‖ : ℂ) ^ 2) •
          QuantumProver.CountableGramSchmidt.residual v i :=
  eq_sub_iff_add_eq.mpr
    (QuantumProver.CountableGramSchmidt.residual_decomposition v n).symm

theorem residual_isometry (J : X →ₗᵢ[ℂ] Y) (v : ℕ → X) (n : ℕ) :
    QuantumProver.CountableGramSchmidt.residual (fun i => J (v i)) n =
      J (QuantumProver.CountableGramSchmidt.residual v n) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [residual_formula, residual_formula, map_sub, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [ih i (Finset.mem_Iio.mp hi)]
    simp only [LinearIsometry.inner_map_map, LinearIsometry.norm_map, map_smul]

theorem frame_isometry (J : X →ₗᵢ[ℂ] Y) (v : ℕ → X) (n : ℕ) :
    QuantumProver.CountableGramSchmidt.frame (fun i => J (v i)) n =
      J (QuantumProver.CountableGramSchmidt.frame v n) := by
  rw [QuantumProver.CountableGramSchmidt.frame_def, QuantumProver.CountableGramSchmidt.frame_def,
    residual_isometry]
  simp only [LinearIsometry.norm_map, map_smul]

end PhysicalNaturality

section Pullback

variable {Z : Type*} [MeasurableSpace Z] {H : Type*} [MeasurableSpace H]
  {E : Z → Type*} [∀ z, NormedAddCommGroup (E z)]
  [∀ z, InnerProductSpace ℂ (E z)] [∀ z, CompleteSpace (E z)]

def pullbackFamily (F : FundamentalFamily E) (f : H → Z) (hf : Measurable f) :
    FundamentalFamily (fun h => E (f h)) where
  vector h := F.vector (f h)
  pairingMeasurable i j := (F.pairingMeasurable i j).comp hf
  dense h := F.dense (f h)

@[simp] theorem pullbackFamily_embedding (F : FundamentalFamily E) (f : H → Z)
    (hf : Measurable f) (h : H) :
    (pullbackFamily F f hf).embedding h = F.embedding (f h) := rfl

end Pullback

section FamilyNaturality

variable {Z : Type*} [MeasurableSpace Z] {E G : Z → Type*}
  [∀ z, NormedAddCommGroup (E z)] [∀ z, InnerProductSpace ℂ (E z)]
  [∀ z, CompleteSpace (E z)]
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]

theorem family_embedding_naturality (F : FundamentalFamily E)
    (Q : FundamentalFamily G) (J : (z : Z) → E z ≃ₗᵢ[ℂ] G z)
    (hvector : ∀ z i, Q.vector z i = J z (F.vector z i))
    (z : Z) (x : E z) : Q.embedding z (J z x) = F.embedding z x := by
  apply lp.ext
  funext n
  rw [FundamentalFamily.embedding_apply, FundamentalFamily.embedding_apply]
  have hv : Q.vector z = fun i => J z (F.vector z i) := funext (hvector z)
  change inner ℂ (QuantumProver.CountableGramSchmidt.frame (Q.vector z) n) (J z x) =
    inner ℂ (QuantumProver.CountableGramSchmidt.frame (F.vector z) n) x
  have hf := frame_isometry (J z).toLinearIsometry (F.vector z) n
  change QuantumProver.CountableGramSchmidt.frame (fun i => J z (F.vector z i)) n =
    J z (QuantumProver.CountableGramSchmidt.frame (F.vector z) n) at hf
  rw [hv, hf]
  exact (J z).inner_map_map _ _

theorem family_identification_measurableSection (F : FundamentalFamily E)
    (Q : FundamentalFamily G) (J : (z : Z) → E z ≃ₗᵢ[ℂ] G z)
    (hvector : ∀ z i, Q.vector z i = J z (F.vector z i))
    (s : (z : Z) → E z) (hs : F.IsMeasurableSection s) :
    Q.IsMeasurableSection (fun z => J z (s z)) := by
  intro i
  have he : (fun z => inner ℂ (Q.vector z i) (J z (s z))) =
      fun z => inner ℂ (F.vector z i) (s z) := by
    funext z
    rw [hvector, (J z).inner_map_map]
  rw [he]
  exact hs i

end FamilyNaturality

section ChosenSections

variable {Z : Type*} [MeasurableSpace Z] {E G : Z → Type*}
  [∀ z, NormedAddCommGroup (E z)] [∀ z, InnerProductSpace ℂ (E z)]
  [∀ z, CompleteSpace (E z)]
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]

def transportFamily (F : FundamentalFamily E)
    (J : (z : Z) → E z ≃ₗᵢ[ℂ] G z) : FundamentalFamily G where
  vector z i := J z (F.vector z i)
  pairingMeasurable i j := by
    simpa only [LinearIsometryEquiv.inner_map_map] using F.pairingMeasurable i j
  dense z := by
    have hd : DenseRange (J z).toLinearIsometry.toContinuousLinearMap :=
      (J z).surjective.denseRange
    have h := hd.topologicalClosure_map_submodule (F.dense z)
    rw [Submodule.map_span] at h
    change (Submodule.span ℂ (J z '' range (F.vector z))).topologicalClosure = ⊤ at h
    rw [← Set.range_comp'] at h
    exact h

theorem transportFamily_embedding (F : FundamentalFamily E)
    (J : (z : Z) → E z ≃ₗᵢ[ℂ] G z) (z : Z) (x : E z) :
    (transportFamily F J).embedding z (J z x) = F.embedding z x :=
  family_embedding_naturality F (transportFamily F J) J (fun _ _ => rfl) z x

theorem transportFamily_intrinsic (F : FundamentalFamily E)
    (Q : FundamentalFamily G) (J : (z : Z) → E z ≃ₗᵢ[ℂ] G z)
    (hJ : QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator.CoefficientsMeasurable F Q
      (fun z => (J z).toLinearIsometry.toContinuousLinearMap)) (i : ℕ) :
    Q.IsMeasurableSection (fun z => (transportFamily F J).vector z i) :=
  QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator.apply_isMeasurableSection F Q _ hJ _
    (F.fundamental_measurableSection i)

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

def retargetSource (F F' : FundamentalFamily E) (P : SourceInstrument F Ω₀)
    (hF' : ∀ i, F.IsMeasurableSection (fun z => F'.vector z i)) :
    SourceInstrument F' Ω₀ where
  operation := P.operation
  empty := P.empty
  countable_additivity := P.countable_additivity
  completelyPositive := P.completelyPositive
  trace_preserving := P.trace_preserving
  fundamental_measurable s hs i j k l :=
    QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument.measurable_operation_rankOne_coordinate F
      (commonFundamentalFamily (H := Z)) (fun z => P.operation z s)
      (P.fundamental_measurable s hs)
      (fun z => F'.vector z i) (fun z => F'.vector z j) (hF' i) (hF' j) k l

@[simp] theorem retargetSource_operation (F F' : FundamentalFamily E)
    (P : SourceInstrument F Ω₀)
    (hF' : ∀ i, F.IsMeasurableSection (fun z => F'.vector z i))
    (z : Z) (s : Set Ω₀) :
    (retargetSource F F' P hF').operation z s = P.operation z s := rfl

end ChosenSections

structure PhysicalDomains where
  admissible : (n : ℕ) → Set (RoundHistory Ω n)
  admissible_measurable : ∀ n, MeasurableSet (admissible n)
  initial_valid : (PUnit.unit : RoundHistory Ω 0) ∈ admissible 0
  party : (n : ℕ) → admissible n → Bool
  party_measurable : ∀ n, Measurable (party n)
  graph : (n : ℕ) → Set (admissible n × Ω n)
  graph_measurable : ∀ n, MeasurableSet (graph n)
  append_valid : ∀ n (z : graph n), (z.val.1.val, z.val.2) ∈ admissible (n+1)

namespace PhysicalDomains

variable {Ω} (D : PhysicalDomains Ω)

def initialHistory : D.admissible 0 := ⟨PUnit.unit, D.initial_valid⟩

def physicalParty (n : ℕ) (h : RoundHistory Ω n) : Bool :=
  if hh : h ∈ D.admissible n then D.party n ⟨h,hh⟩ else true

theorem measurable_physicalParty (n : ℕ) : Measurable (D.physicalParty n) :=
  (D.party_measurable n).dite measurable_const (D.admissible_measurable n)

@[simp] theorem physicalParty_admissible (n : ℕ) (h : D.admissible n) :
    D.physicalParty n h.val = D.party n h := by
  simp only [physicalParty, h.property, ↓reduceDIte]

def actingDomain (n : ℕ) (b : Bool) : Set (RoundHistory Ω n) :=
  D.admissible n ∩ D.physicalParty n ⁻¹' {b}

theorem measurableSet_actingDomain (n : ℕ) (b : Bool) :
    MeasurableSet (D.actingDomain n b) :=
  (D.admissible_measurable n).inter
    ((D.measurable_physicalParty n) (MeasurableSet.singleton b))

def actingHistory (n : ℕ) (b : Bool) (h : D.actingDomain n b) : D.admissible n :=
  ⟨h.val,h.property.1⟩

theorem measurable_actingHistory (n : ℕ) (b : Bool) :
    Measurable (D.actingHistory n b) := measurable_subtype_coe.subtype_mk

theorem party_actingHistory (n : ℕ) (b : Bool) (h : D.actingDomain n b) :
    D.party n (D.actingHistory n b h) = b := by
  have hp := h.property.2
  change D.physicalParty n h.val = b at hp
  have he := D.physicalParty_admissible n (D.actingHistory n b h)
  change D.physicalParty n h.val = D.party n (D.actingHistory n b h) at he
  exact he.symm.trans hp

def actingGraphMap (n : ℕ) (b : Bool) (z : D.actingDomain n b × Ω n) :
    D.admissible n × Ω n := (D.actingHistory n b z.1,z.2)

theorem measurable_actingGraphMap (n : ℕ) (b : Bool) :
    Measurable (D.actingGraphMap n b) :=
  ((D.measurable_actingHistory n b).comp measurable_fst).prodMk measurable_snd

def actingGraph (n : ℕ) (b : Bool) : Set (D.actingDomain n b × Ω n) :=
  D.actingGraphMap n b ⁻¹' D.graph n

theorem measurableSet_actingGraph (n : ℕ) (b : Bool) :
    MeasurableSet (D.actingGraph n b) :=
  (D.measurable_actingGraphMap n b) (D.graph_measurable n)

def appendGraph (n : ℕ) (z : D.graph n) : D.admissible (n+1) :=
  ⟨(z.val.1.val,z.val.2),D.append_valid n z⟩

theorem measurable_appendGraph (n : ℕ) : Measurable (D.appendGraph n) := by
  apply Measurable.subtype_mk
  exact (measurable_subtype_coe.comp
    (measurable_fst.comp measurable_subtype_coe)).prodMk
      (measurable_snd.comp measurable_subtype_coe)

def appendActingGraph (n : ℕ) (b : Bool) (z : D.actingGraph n b) :
    D.admissible (n+1) :=
  D.appendGraph n ⟨D.actingGraphMap n b z.val,z.property⟩

theorem measurable_appendActingGraph (n : ℕ) (b : Bool) :
    Measurable (D.appendActingGraph n b) :=
  (D.measurable_appendGraph n).comp
    (((D.measurable_actingGraphMap n b).comp measurable_subtype_coe).subtype_mk)

def actingPhysical (n : ℕ) (b : Bool) (h : D.admissible n)
    (hh : D.party n h = b) : D.actingDomain n b :=
  ⟨h.val,h.property,by simpa only [mem_preimage, mem_singleton_iff,
    D.physicalParty_admissible] using hh⟩

@[simp] theorem actingHistory_actingPhysical (n : ℕ) (b : Bool)
    (h : D.admissible n) (hh : D.party n h = b) :
    D.actingHistory n b (D.actingPhysical n b h hh) = h := rfl

end PhysicalDomains

section MeasurableGluing

variable {Z : Type*} [MeasurableSpace Z] {E : Z → Type*}
  [∀ z, NormedAddCommGroup (E z)] [∀ z, InnerProductSpace ℂ (E z)]
  [∀ z, CompleteSpace (E z)]

def glueFamily (S : Set Z) (hS : MeasurableSet S)
    (FS : FundamentalFamily (fun z : S => E z.val))
    (F : FundamentalFamily E) : FundamentalFamily E where
  vector z i := if hz : z ∈ S then FS.vector ⟨z,hz⟩ i else F.vector z i
  pairingMeasurable i j := by
    have hf := (F.pairingMeasurable i j).comp
      (measurable_subtype_coe : Measurable (fun z : {z : Z // z ∉ S} => z.val))
    convert (FS.pairingMeasurable i j).dite hf hS using 1
    funext z
    split_ifs <;> rfl
  dense z := by
    by_cases hz : z ∈ S
    · simpa only [hz, ↓reduceDIte] using FS.dense ⟨z,hz⟩
    · simpa only [hz, ↓reduceDIte] using F.dense z

theorem glueFamily_embedding_on (S : Set Z) (hS : MeasurableSet S)
    (FS : FundamentalFamily (fun z : S => E z.val))
    (F : FundamentalFamily E) (z : S) (x : E z.val) :
    (glueFamily S hS FS F).embedding z.val x = FS.embedding z x := by
  apply lp.ext
  funext n
  have hv : (glueFamily S hS FS F).vector z.val = FS.vector z := by
    funext i
    simp only [glueFamily, z.property, ↓reduceDIte]
  change inner ℂ (QuantumProver.CountableGramSchmidt.frame
    ((glueFamily S hS FS F).vector z.val) n) x =
      inner ℂ (QuantumProver.CountableGramSchmidt.frame (FS.vector z) n) x
  rw [hv]

theorem glueFamily_embedding_off (S : Set Z) (hS : MeasurableSet S)
    (FS : FundamentalFamily (fun z : S => E z.val))
    (F : FundamentalFamily E) (z : Z) (hz : z ∉ S) (x : E z) :
    (glueFamily S hS FS F).embedding z x = F.embedding z x := by
  apply lp.ext
  funext n
  have hv : (glueFamily S hS FS F).vector z = F.vector z := by
    funext i
    simp only [glueFamily, hz, ↓reduceDIte]
  change inner ℂ (QuantumProver.CountableGramSchmidt.frame
    ((glueFamily S hS FS F).vector z) n) x =
      inner ℂ (QuantumProver.CountableGramSchmidt.frame (F.vector z) n) x
  rw [hv]

theorem pullback_intrinsic (F F' : FundamentalFamily E)
    (hF' : ∀ i, F.IsMeasurableSection (fun z => F'.vector z i))
    {H : Type*} [MeasurableSpace H] (f : H → Z) (hf : Measurable f) (i : ℕ) :
    (pullbackFamily F f hf).IsMeasurableSection
      (fun h => (pullbackFamily F' f hf).vector h i) :=
  fun j => (hF' i j).comp hf

theorem glueFamily_intrinsic (F₀ F : FundamentalFamily E)
    (hF : ∀ i, F₀.IsMeasurableSection (fun z => F.vector z i))
    (S : Set Z) (hS : MeasurableSet S)
    (FS : FundamentalFamily (fun z : S => E z.val))
    (hFS : ∀ i, (pullbackFamily F₀ (fun z : S => z.val) measurable_subtype_coe).IsMeasurableSection
      (fun z => FS.vector z i)) (i : ℕ) :
    F₀.IsMeasurableSection (fun z => (glueFamily S hS FS F).vector z i) := by
  intro j
  have hf := (hF i j).comp
    (measurable_subtype_coe : Measurable (fun z : {z : Z // z ∉ S} => z.val))
  convert (hFS i j).dite hf hS using 1
  funext z
  simp only [glueFamily, pullbackFamily, Function.comp_apply]
  split_ifs <;> rfl

end MeasurableGluing

namespace PhysicalDomains

variable {Ω} (D : PhysicalDomains Ω)

theorem appendActingGraph_injective (n : ℕ) (b : Bool) :
    Injective (D.appendActingGraph n b) := by
  intro z w he
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun h : D.admissible (n+1) => h.val.1) he
  · exact congrArg (fun h : D.admissible (n+1) => h.val.2) he

theorem measurableEmbedding_appendActingGraph (n : ℕ) (b : Bool) :
    MeasurableEmbedding (D.appendActingGraph n b) := by
  letI : StandardBorelSpace (D.actingDomain n b) :=
    (D.measurableSet_actingDomain n b).standardBorel
  letI : StandardBorelSpace (D.actingGraph n b) :=
    (D.measurableSet_actingGraph n b).standardBorel
  letI : StandardBorelSpace (D.admissible (n+1)) :=
    (D.admissible_measurable (n+1)).standardBorel
  let := upgradeStandardBorel (D.actingGraph n b)
  let := upgradeStandardBorel (D.admissible (n+1))
  exact (D.measurable_appendActingGraph n b).measurableEmbedding
    (D.appendActingGraph_injective n b)

def successorDomain (n : ℕ) (b : Bool) : Set (D.admissible (n+1)) :=
  range (D.appendActingGraph n b)

theorem measurableSet_successorDomain (n : ℕ) (b : Bool) :
    MeasurableSet (D.successorDomain n b) :=
  (D.measurableEmbedding_appendActingGraph n b).measurableSet_range

def decodeSuccessor (n : ℕ) (b : Bool) : D.successorDomain n b → D.actingGraph n b :=
  (D.measurableEmbedding_appendActingGraph n b).equivRange.symm

theorem measurable_decodeSuccessor (n : ℕ) (b : Bool) :
    Measurable (D.decodeSuccessor n b) :=
  (D.measurableEmbedding_appendActingGraph n b).equivRange.symm.measurable

@[simp] theorem decodeSuccessor_append (n : ℕ) (b : Bool) (z : D.actingGraph n b) :
    D.decodeSuccessor n b ⟨D.appendActingGraph n b z,mem_range_self z⟩ = z :=
  (D.measurableEmbedding_appendActingGraph n b).equivRange_symm_apply_mk z

def successorOutcomePoint (n : ℕ) (b : Bool) (r : D.successorDomain n b) :
    D.actingDomain n b × Ω n := (D.decodeSuccessor n b r).val

theorem measurable_successorOutcomePoint (n : ℕ) (b : Bool) :
    Measurable (D.successorOutcomePoint n b) :=
  measurable_subtype_coe.comp (D.measurable_decodeSuccessor n b)

def predecessorHistory (n : ℕ) (b : Bool) (r : D.successorDomain n b) :
    D.admissible n := D.actingHistory n b (D.successorOutcomePoint n b r).1

theorem measurable_predecessorHistory (n : ℕ) (b : Bool) :
    Measurable (D.predecessorHistory n b) :=
  (D.measurable_actingHistory n b).comp
    (measurable_fst.comp (D.measurable_successorOutcomePoint n b))

theorem successorDomain_disjoint (n : ℕ) (b : Bool) :
    Disjoint (D.successorDomain n b) (D.successorDomain n (!b)) := by
  apply Set.disjoint_left.mpr
  intro r ha hb
  obtain ⟨z,hz⟩ := ha
  obtain ⟨w,hw⟩ := hb
  have hParent : D.actingHistory n b z.val.1 =
      D.actingHistory n (!b) w.val.1 := by
    apply Subtype.ext
    exact congrArg (fun h : D.admissible (n+1) => h.val.1) (hz.trans hw.symm)
  have hp := D.party_actingHistory n b z.val.1
  have hq := D.party_actingHistory n (!b) w.val.1
  rw [hParent, hq] at hp
  cases b <;> cases hp

end PhysicalDomains

section IntrinsicFamilies

variable {H : Type*} [MeasurableSpace H] {E : H → Type*}
  [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
  [∀ h, CompleteSpace (E h)]

structure IntrinsicFamily (F : FundamentalFamily E) where
  family : FundamentalFamily E
  intrinsic : ∀ i, F.IsMeasurableSection (fun h => family.vector h i)

end IntrinsicFamilies

section PhysicalMemoryChoice

variable (D : PhysicalDomains Ω) (b : Bool)
  {E : (n : ℕ) → D.admissible n → Type v}
  [∀ n h, NormedAddCommGroup (E n h)] [∀ n h, InnerProductSpace ℂ (E n h)]
  [∀ n h, CompleteSpace (E n h)]
  (F : (n : ℕ) → FundamentalFamily (E n))
  {G : (n : ℕ) → D.actingDomain n b × Ω n → Type w}
  [∀ n z, NormedAddCommGroup (G n z)] [∀ n z, InnerProductSpace ℂ (G n z)]
  [∀ n z, CompleteSpace (G n z)]
  (Q : (n : ℕ) → FundamentalFamily (G n))

def outputOnSuccessor (n : ℕ) : FundamentalFamily
    (fun r : D.successorDomain n b => G n (D.successorOutcomePoint n b r)) :=
  pullbackFamily (Q n) (D.successorOutcomePoint n b)
    (D.measurable_successorOutcomePoint n b)

def sourceOnSuccessor (n : ℕ) : FundamentalFamily
    (fun r : D.successorDomain n (!b) => E n (D.predecessorHistory n (!b) r)) :=
  pullbackFamily (F n) (D.predecessorHistory n (!b))
    (D.measurable_predecessorHistory n (!b))

def targetOnSuccessor (n : ℕ) (c : Bool) : FundamentalFamily
    (fun r : D.successorDomain n c => E (n+1) r.val) :=
  pullbackFamily (F (n+1)) (fun r : D.successorDomain n c => r.val)
    measurable_subtype_coe

structure PhysicalMemoryWiring where
  acted : (n : ℕ) → (r : D.successorDomain n b) →
    G n (D.successorOutcomePoint n b r) ≃ₗᵢ[ℂ] E (n+1) r.val
  acted_measurable : ∀ n,
    QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator.CoefficientsMeasurable
      (outputOnSuccessor Ω D b Q n) (targetOnSuccessor Ω D F n b)
      (fun r => (acted n r).toLinearIsometry.toContinuousLinearMap)
  idle : (n : ℕ) → (r : D.successorDomain n (!b)) →
    E n (D.predecessorHistory n (!b) r) ≃ₗᵢ[ℂ] E (n+1) r.val
  idle_measurable : ∀ n,
    QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator.CoefficientsMeasurable
      (sourceOnSuccessor Ω D b F n) (targetOnSuccessor Ω D F n (!b))
      (fun r => (idle n r).toLinearIsometry.toContinuousLinearMap)

variable (W : PhysicalMemoryWiring Ω D b F Q)

def actedNextFamily (n : ℕ) : FundamentalFamily
    (fun r : D.successorDomain n b => E (n+1) r.val) :=
  transportFamily (outputOnSuccessor Ω D b Q n) (W.acted n)

def idleNextFamily (n : ℕ) (S : IntrinsicFamily (F n)) : FundamentalFamily
    (fun r : D.successorDomain n (!b) => E (n+1) r.val) :=
  transportFamily
    (pullbackFamily S.family (D.predecessorHistory n (!b))
      (D.measurable_predecessorHistory n (!b))) (W.idle n)

theorem idle_chosen_coefficients (n : ℕ) (S : IntrinsicFamily (F n)) :
    QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator.CoefficientsMeasurable
      (pullbackFamily S.family (D.predecessorHistory n (!b))
        (D.measurable_predecessorHistory n (!b)))
      (targetOnSuccessor Ω D F n (!b))
      (fun r => (W.idle n r).toLinearIsometry.toContinuousLinearMap) := by
  intro i j
  exact QuantumProver.ElegantJointMeasurement.MeasurableHilbertOperator.measurable_matrix_element
    (sourceOnSuccessor Ω D b F n) (targetOnSuccessor Ω D F n (!b))
    _ (W.idle_measurable n)
    (fun r => S.family.vector (D.predecessorHistory n (!b) r) j)
    (pullback_intrinsic (F n) S.family S.intrinsic
      (D.predecessorHistory n (!b)) (D.measurable_predecessorHistory n (!b)) j)
    (fun r => (targetOnSuccessor Ω D F n (!b)).vector r i)
    ((targetOnSuccessor Ω D F n (!b)).fundamental_measurableSection i)

def chooseNextMemory (n : ℕ) (S : IntrinsicFamily (F n)) :
    IntrinsicFamily (F (n+1)) := by
  let A := actedNextFamily Ω D b F Q W n
  let I := idleNextFamily Ω D b F Q W n S
  let B := glueFamily (D.successorDomain n (!b))
    (D.measurableSet_successorDomain n (!b)) I (F (n+1))
  have hA : ∀ i, (targetOnSuccessor Ω D F n b).IsMeasurableSection
      (fun r => A.vector r i) :=
    fun i => transportFamily_intrinsic (outputOnSuccessor Ω D b Q n)
      (targetOnSuccessor Ω D F n b) (W.acted n) (W.acted_measurable n) i
  have hI : ∀ i, (targetOnSuccessor Ω D F n (!b)).IsMeasurableSection
      (fun r => I.vector r i) :=
    fun i => transportFamily_intrinsic
      (pullbackFamily S.family (D.predecessorHistory n (!b))
        (D.measurable_predecessorHistory n (!b)))
      (targetOnSuccessor Ω D F n (!b)) (W.idle n)
      (idle_chosen_coefficients Ω D b F Q W n S) i
  have hB : ∀ i, (F (n+1)).IsMeasurableSection (fun h => B.vector h i) :=
    glueFamily_intrinsic (F (n+1)) (F (n+1))
      (fun i => (F (n+1)).fundamental_measurableSection i)
      (D.successorDomain n (!b)) (D.measurableSet_successorDomain n (!b)) I hI
  exact ⟨glueFamily (D.successorDomain n b) (D.measurableSet_successorDomain n b) A B,
    glueFamily_intrinsic (F (n+1)) B hB (D.successorDomain n b)
      (D.measurableSet_successorDomain n b) A hA⟩

def selectedMemory : (n : ℕ) → IntrinsicFamily (F n)
  | 0 => ⟨F 0,fun i => (F 0).fundamental_measurableSection i⟩
  | n+1 => chooseNextMemory Ω D b F Q W n (selectedMemory n)

theorem selectedMemory_acted_code (n : ℕ) (r : D.successorDomain n b)
    (x : G n (D.successorOutcomePoint n b r)) :
    (selectedMemory Ω D b F Q W (n+1)).family.embedding r.val (W.acted n r x) =
      (Q n).embedding (D.successorOutcomePoint n b r) x := by
  simp only [selectedMemory, chooseNextMemory]
  rw [glueFamily_embedding_on, actedNextFamily, transportFamily_embedding,
    outputOnSuccessor, pullbackFamily_embedding]

theorem selectedMemory_idle_code (n : ℕ) (r : D.successorDomain n (!b))
    (x : E n (D.predecessorHistory n (!b) r)) :
    (selectedMemory Ω D b F Q W (n+1)).family.embedding r.val (W.idle n r x) =
      (selectedMemory Ω D b F Q W n).family.embedding
        (D.predecessorHistory n (!b) r) x := by
  have hr : r.val ∉ D.successorDomain n b := by
    intro ha
    exact Set.disjoint_left.mp (D.successorDomain_disjoint n b) ha r.property
  simp only [selectedMemory, chooseNextMemory]
  rw [glueFamily_embedding_off _ _ _ _ _ hr, glueFamily_embedding_on,
    idleNextFamily, transportFamily_embedding, pullbackFamily_embedding]

end PhysicalMemoryChoice

section RecordedSourceRetargeting

variable {H : Type*} [MeasurableSpace H] {X : Type*} [MeasurableSpace X]
  {E : H → Type*} [∀ h, NormedAddCommGroup (E h)]
  [∀ h, InnerProductSpace ℂ (E h)] [∀ h, CompleteSpace (E h)]
  {G : H × X → Type*} [∀ z, NormedAddCommGroup (G z)]
  [∀ z, InnerProductSpace ℂ (G z)] [∀ z, CompleteSpace (G z)]

def retargetRecordedSource (F F' : FundamentalFamily E) (Q : FundamentalFamily G)
    (P : RecordedSourceInstrument F Q)
    (hF' : ∀ i, F.IsMeasurableSection (fun h => F'.vector h i)) :
    RecordedSourceInstrument F' Q where
  represented_physical := retargetSource F F' P.represented_physical hF'
  controlled_output J _ _ _ h U hU W hW := by
    simpa only [physicalInstrument, retargetSource] using
      P.controlled_output J h U hU W hW

end RecordedSourceRetargeting

section ActivePhysicalFamilies

variable (D : PhysicalDomains Ω) (b : Bool)
  {E : (n : ℕ) → D.admissible n → Type v}
  [∀ n h, NormedAddCommGroup (E n h)] [∀ n h, InnerProductSpace ℂ (E n h)]
  [∀ n h, CompleteSpace (E n h)]
  (F : (n : ℕ) → FundamentalFamily (E n))
  {G : (n : ℕ) → D.actingDomain n b × Ω n → Type w}
  [∀ n z, NormedAddCommGroup (G n z)] [∀ n z, InnerProductSpace ℂ (G n z)]
  [∀ n z, CompleteSpace (G n z)]
  (Q : (n : ℕ) → FundamentalFamily (G n))

def physicalActiveSource (n : ℕ) : FundamentalFamily
    (fun h : D.actingDomain n b => E n (D.actingHistory n b h)) :=
  pullbackFamily (F n) (D.actingHistory n b) (D.measurable_actingHistory n b)

structure PhysicalLocalFamily where
  instrument : (n : ℕ) → RecordedSourceInstrument
    (physicalActiveSource Ω D b F n) (Q n)
  off_graph : ∀ n (h : D.actingDomain n b),
    (instrument n).represented_physical.operation h
      {x | (h,x) ∉ D.actingGraph n b} = 0

def physicalPhysicalMemoryTurn (P : PhysicalLocalFamily Ω D b F Q)
    (n : ℕ) (h : D.actingDomain n b) :
    Instrument (E n (D.actingHistory n b h)) CommonHilbert Unit (Ω n) :=
  physicalInstrument (E := fun z : D.actingDomain n b => E n (D.actingHistory n b z))
    (F := physicalActiveSource Ω D b F n) (Ω := Ω n) (P.instrument n).represented_physical h

@[simp] theorem physicalPhysicalMemoryTurn_operation (P : PhysicalLocalFamily Ω D b F Q)
    (n : ℕ) (h : D.actingDomain n b) (s : Set (Ω n)) :
    (physicalPhysicalMemoryTurn Ω D b F Q P n h).operation () s =
      (P.instrument n).represented_physical.operation h s := rfl

variable (W : PhysicalMemoryWiring Ω D b F Q) (P : PhysicalLocalFamily Ω D b F Q)

def chosenActiveSource (n : ℕ) : FundamentalFamily
    (fun h : D.actingDomain n b => E n (D.actingHistory n b h)) :=
  pullbackFamily (selectedMemory Ω D b F Q W n).family
    (D.actingHistory n b) (D.measurable_actingHistory n b)

def retargetedPhysicalInstrument (n : ℕ) : RecordedSourceInstrument
    (chosenActiveSource Ω D b F Q W n) (Q n) :=
  retargetRecordedSource (physicalActiveSource Ω D b F n)
    (chosenActiveSource Ω D b F Q W n) (Q n) (P.instrument n)
    (pullback_intrinsic (F n) (selectedMemory Ω D b F Q W n).family
      (selectedMemory Ω D b F Q W n).intrinsic
      (D.actingHistory n b) (D.measurable_actingHistory n b))

def admittedMemoryTurn (n : ℕ) : Instrument CommonHilbert CommonHilbert
    (History (CommonRecord Ω) n) (CommonRecord Ω) :=
  admittedTurn Ω n (D.actingDomain n b) (D.measurableSet_actingDomain n b)
    (chosenActiveSource Ω D b F Q W n)
    (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical

def admittedRecordedMemoryTurn (n : ℕ) :
    QuantumProver.ElegantJointMeasurement.NormalRecordedAbsorption.RecordedNormalInstrument
      CommonHilbert (taggedOutputFamily (Q n)) :=
  completeRecordedSourceInstrument (Q n)
    (retargetedPhysicalInstrument Ω D b F Q W P n)

@[simp] theorem admittedRecordedMemoryTurn_physical (n : ℕ) :
    (admittedRecordedMemoryTurn Ω D b F Q W P n).represented_physical =
      completeSourceInstrument (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical := rfl

theorem admittedMemoryTurn_recorded_encoded (n : ℕ) (h : D.actingDomain n b)
    (s : Set (CommonRecord Ω)) :
    (admittedMemoryTurn Ω D b F Q W P n).operation (encodeHistory Ω n h.val) s =
      (admittedRecordedMemoryTurn Ω D b F Q W P n).represented_physical.operation h
        (completedOutcome Ω n ⁻¹' s) := by
  exact admittedTurn_encoded Ω n (D.actingDomain n b)
    (D.measurableSet_actingDomain n b) (chosenActiveSource Ω D b F Q W n)
    (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical h s

theorem admittedMemoryTurn_physical_input (n : ℕ) (h : D.actingDomain n b)
    (s : Set (Ω n)) (T : Nuc (E n (D.actingHistory n b h))) :
    (admittedMemoryTurn Ω D b F Q W P n).operation (encodeHistory Ω n h.val)
      (encodeOutcome Ω n '' s)
      (padNuclear ((selectedMemory Ω D b F Q W n).family.embedding
        (D.actingHistory n b h)) T) = (P.instrument n).represented_physical.operation h s T := by
  simpa only [admittedMemoryTurn, chosenActiveSource, pullbackFamily_embedding,
    retargetedPhysicalInstrument, retargetRecordedSource, retargetSource_operation] using
      admittedTurn_physical_input Ω n (D.actingDomain n b)
        (D.measurableSet_actingDomain n b) (chosenActiveSource Ω D b F Q W n)
        (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical h s T

theorem admittedMemoryTurn_all_events (n : ℕ) (h : D.actingDomain n b)
    (s : Set (CommonRecord Ω)) (T : Nuc (E n (D.actingHistory n b h))) :
    (admittedMemoryTurn Ω D b F Q W P n).operation (encodeHistory Ω n h.val) s
      (padNuclear ((selectedMemory Ω D b F Q W n).family.embedding
        (D.actingHistory n b h)) T) =
      (P.instrument n).represented_physical.operation h (encodeOutcome Ω n ⁻¹' s) T := by
  simpa only [admittedMemoryTurn, chosenActiveSource, pullbackFamily_embedding,
    retargetedPhysicalInstrument, retargetRecordedSource, retargetSource_operation] using
      admittedTurn_all_events_on_physical Ω n (D.actingDomain n b)
        (D.measurableSet_actingDomain n b) (chosenActiveSource Ω D b F Q W n)
        (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical h s T

theorem admittedMemoryTurn_dummy_on_physical (n : ℕ) (h : D.actingDomain n b)
    (T : Nuc (E n (D.actingHistory n b h))) :
    (admittedMemoryTurn Ω D b F Q W P n).operation (encodeHistory Ω n h.val)
      {dummyRecord Ω}
      (padNuclear ((selectedMemory Ω D b F Q W n).family.embedding
        (D.actingHistory n b h)) T) = 0 := by
  simpa only [admittedMemoryTurn, chosenActiveSource, pullbackFamily_embedding] using
    admittedTurn_dummy_on_physical Ω n (D.actingDomain n b)
      (D.measurableSet_actingDomain n b) (chosenActiveSource Ω D b F Q W n)
      (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical h T

theorem admittedMemoryTurn_off_graph (n : ℕ) (h : D.actingDomain n b)
    (T : Nuc (E n (D.actingHistory n b h))) :
    (admittedMemoryTurn Ω D b F Q W P n).operation (encodeHistory Ω n h.val)
      {r | (h,r) ∉ encodedAdmissibleGraph Ω n (D.actingGraph n b)}
      (padNuclear ((selectedMemory Ω D b F Q W n).family.embedding
        (D.actingHistory n b h)) T) = 0 := by
  have hSupp : ∀ h, (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical.operation h
      {x | (h,x) ∉ D.actingGraph n b} = 0 := P.off_graph n
  simpa only [admittedMemoryTurn, chosenActiveSource, pullbackFamily_embedding] using
    admittedTurn_off_graph_on_physical Ω n (D.actingDomain n b)
      (D.measurableSet_actingDomain n b) (chosenActiveSource Ω D b F Q W n)
      (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical
      (D.actingGraph n b) hSupp h T

theorem admittedMemoryTurn_invalid (n : ℕ) (h : History (CommonRecord Ω) n)
    (hh : h ∉ range (fun z : D.actingDomain n b => encodeHistory Ω n z.val))
    (s : Set (CommonRecord Ω)) :
    (admittedMemoryTurn Ω D b F Q W P n).operation h s =
      if dummyRecord Ω ∈ s then ContinuousLinearMap.id ℂ (Nuc CommonHilbert) else 0 :=
  admittedTurn_invalid Ω n (D.actingDomain n b) (D.measurableSet_actingDomain n b)
    (chosenActiveSource Ω D b F Q W n)
    (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical h hh s

def chargedInitialMemory {d : ℕ}
    (J : EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] E 0 D.initialHistory) :
    EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] CommonHilbert :=
  ((selectedMemory Ω D b F Q W 0).family.embedding D.initialHistory).comp J

theorem chargedInitialMemory_apply {d : ℕ}
    (J : EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] E 0 D.initialHistory)
    (x : EuclideanSpace ℂ (Fin d)) :
    chargedInitialMemory Ω D b F Q W J x = (F 0).embedding D.initialHistory (J x) := rfl

end ActivePhysicalFamilies

section MatrixPhysicalFamily

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

def ofPhysicalFamilies {a b : ℕ}
    (JA : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EA 0 D.initialHistory)
    (JB : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EB 0 D.initialHistory) :
    MatrixProcess a b (CommonRecord Ω) where
  initialAlice := chargedInitialMemory Ω D true FA QA WA JA
  initialBob := chargedInitialMemory Ω D false FB QB WB JB
  alice := admittedMemoryTurn Ω D true FA QA WA PA
  bob := admittedMemoryTurn Ω D false FB QB WB PB
  aliceTurn n := liftHistoryFunction Ω n (D.physicalParty n) true
  turn_measurable n := measurable_liftHistoryFunction Ω n _
    (D.measurable_physicalParty n) true

theorem ofPhysicalFamilies_party {a b : ℕ}
    (JA : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EA 0 D.initialHistory)
    (JB : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EB 0 D.initialHistory)
    (n : ℕ) (h : D.admissible n) :
    (ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB).aliceTurn n
      (encodeHistory Ω n h.val) = D.party n h := by
  simp only [ofPhysicalFamilies, liftHistoryFunction_encode, D.physicalParty_admissible]

theorem ofPhysicalFamilies_initialAlice {a b : ℕ}
    (JA : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EA 0 D.initialHistory)
    (JB : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EB 0 D.initialHistory)
    (x : EuclideanSpace ℂ (Fin a)) :
    (ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB).initialAlice x =
      (FA 0).embedding D.initialHistory (JA x) := rfl

theorem ofPhysicalFamilies_initialBob {a b : ℕ}
    (JA : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EA 0 D.initialHistory)
    (JB : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EB 0 D.initialHistory)
    (x : EuclideanSpace ℂ (Fin b)) :
    (ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB).initialBob x =
      (FB 0).embedding D.initialHistory (JB x) := rfl

theorem ofPhysicalFamilies_alice_physical_input {a b : ℕ}
    (JA : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EA 0 D.initialHistory)
    (JB : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EB 0 D.initialHistory)
    (n : ℕ) (h : D.actingDomain n true) (s : Set (Ω n))
    (T : Nuc (EA n (D.actingHistory n true h))) :
    ((ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB).alice n).operation
      (encodeHistory Ω n h.val) (encodeOutcome Ω n '' s)
      (padNuclear ((selectedMemory Ω D true FA QA WA n).family.embedding
        (D.actingHistory n true h)) T) = (PA.instrument n).represented_physical.operation h s T :=
  admittedMemoryTurn_physical_input Ω D true FA QA WA PA n h s T

theorem ofPhysicalFamilies_bob_physical_input {a b : ℕ}
    (JA : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EA 0 D.initialHistory)
    (JB : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EB 0 D.initialHistory)
    (n : ℕ) (h : D.actingDomain n false) (s : Set (Ω n))
    (T : Nuc (EB n (D.actingHistory n false h))) :
    ((ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB).bob n).operation
      (encodeHistory Ω n h.val) (encodeOutcome Ω n '' s)
      (padNuclear ((selectedMemory Ω D false FB QB WB n).family.embedding
        (D.actingHistory n false h)) T) = (PB.instrument n).represented_physical.operation h s T :=
  admittedMemoryTurn_physical_input Ω D false FB QB WB PB n h s T

end MatrixPhysicalFamily

section PhysicalJointCode

variable {X Y Z X' Y' Z' : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
  [NormedAddCommGroup X'] [InnerProductSpace ℂ X'] [CompleteSpace X']
  [NormedAddCommGroup Y'] [InnerProductSpace ℂ Y'] [CompleteSpace Y']
  [NormedAddCommGroup Z'] [InnerProductSpace ℂ Z'] [CompleteSpace Z']

theorem padNuclear_comp (I : X →ₗᵢ[ℂ] Y) (J : Y →ₗᵢ[ℂ] Z) (T : Nuc X) :
    padNuclear (J.comp I) T = padNuclear J (padNuclear I T) := by
  apply toOperator_injective
  have hc : (J.comp I).toContinuousLinearMap =
      J.toContinuousLinearMap.comp I.toContinuousLinearMap := rfl
  rw [toOperator_padNuclear, toOperator_padNuclear, toOperator_padNuclear,
    hc, ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro x
  rfl

def physicalJointCode (JA : X →ₗᵢ[ℂ] Y) (JB : X' →ₗᵢ[ℂ] Y') :
    Nuc (Joint X X') →L[ℂ] Nuc (Joint Y Y') :=
  compose (tensorMap JA.toContinuousLinearMap JB.toContinuousLinearMap)
    (tensorMap JA.toContinuousLinearMap.adjoint JB.toContinuousLinearMap.adjoint)

theorem physicalJointCode_tensor (JA : X →ₗᵢ[ℂ] Y) (JB : X' →ₗᵢ[ℂ] Y')
    (T : Nuc X) (U : Nuc X') :
    physicalJointCode JA JB
      (tensorNuclear (E := X) (E' := X) (F := X') (F' := X') T U) =
      tensorNuclear (E := Y) (E' := Y) (F := Y') (F' := Y')
        (padNuclear JA T) (padNuclear JB U) := by
  exact (tensorNuclear_compose JA.toContinuousLinearMap JA.toContinuousLinearMap.adjoint
    JB.toContinuousLinearMap JB.toContinuousLinearMap.adjoint T U).symm

theorem physicalJointCode_comp (IA : X →ₗᵢ[ℂ] Y) (IB : X' →ₗᵢ[ℂ] Y')
    (JA : Y →ₗᵢ[ℂ] Z) (JB : Y' →ₗᵢ[ℂ] Z') :
    physicalJointCode (JA.comp IA) (JB.comp IB) =
      (physicalJointCode JA JB).comp (physicalJointCode IA IB) := by
  apply nuclear_joint_clm_ext_tensors
  intro T U
  simp only [ContinuousLinearMap.comp_apply, physicalJointCode_tensor, padNuclear_comp]

theorem physicalJointCode_all_inputs (IA : X →ₗᵢ[ℂ] Y) (IB : X' →ₗᵢ[ℂ] Y')
    (JA : Y →ₗᵢ[ℂ] Z) (JB : Y' →ₗᵢ[ℂ] Z') (W : Nuc (Joint X X')) :
    physicalJointCode (JA.comp IA) (JB.comp IB) W =
      physicalJointCode JA JB (physicalJointCode IA IB W) := by
  rw [physicalJointCode_comp, ContinuousLinearMap.comp_apply]

section FiniteInitialReference

variable {R : Type} [Fintype R] [DecidableEq R]
local instance initialBlockComplete {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] : CompleteSpace (BlockSpace R V) :=
  PiLp.completeSpace 2 (fun _ : R => V)

theorem physicalJointCode_amplified (IA : X →ₗᵢ[ℂ] Y) (IB : X' →ₗᵢ[ℂ] Y')
    (JA : Y →ₗᵢ[ℂ] Z) (JB : Y' →ₗᵢ[ℂ] Z') (U : Nuc (BlockSpace R (Joint X X'))) :
    normalAmplification (physicalJointCode (JA.comp IA) (JB.comp IB)) U =
      normalAmplification (physicalJointCode JA JB)
        (normalAmplification (physicalJointCode IA IB) U) := by
  rw [physicalJointCode_comp]
  exact QuantumProver.ElegantJointMeasurement.NormalSandwich.normalAmplification_comp _ _ U

end FiniteInitialReference

end PhysicalJointCode

section FullSpectatorEvents

variable (n : ℕ) (S : Set (RoundHistory Ω n)) (hS : MeasurableSet S)
  {E : S → Type v} [∀ h, NormedAddCommGroup (E h)]
  [∀ h, InnerProductSpace ℂ (E h)] [∀ h, CompleteSpace (E h)]
  (F : FundamentalFamily E) (P : SourceInstrument F (Ω n))
  {V : Type w} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem admittedTurn_left_all_events (h : S) (s : Set (CommonRecord Ω))
    (hs : MeasurableSet s) (W : Nuc (Joint (E h) V)) :
    tensorOperation (G := V) (admittedTurn Ω n S hS F P) (encodeHistory Ω n h.val) s
      (leftSourceCode Ω n S F h W) =
        tensorOperation (G := V) (physicalInstrument P h) () (encodeOutcome Ω n ⁻¹' s) W := by
  have heq : (tensorOperation (G := V) (admittedTurn Ω n S hS F P)
      (encodeHistory Ω n h.val) s).comp (leftSourceCode Ω n S F h) =
      tensorOperation (G := V) (physicalInstrument P h) () (encodeOutcome Ω n ⁻¹' s) := by
    apply nuclear_joint_clm_ext_tensors
    intro T U
    simp only [ContinuousLinearMap.comp_apply, leftSourceCode_tensor]
    rw [tensorOperation_tensor _ _ _ hs, admittedTurn_all_events_on_physical,
      tensorOperation_tensor _ _ _ ((measurable_encodeOutcome Ω n) hs)]
    rfl
  exact congrArg (fun L => L W) heq

theorem admittedTurn_right_all_events (h : S) (s : Set (CommonRecord Ω))
    (hs : MeasurableSet s) (W : Nuc (Joint V (E h))) :
    rightTensorOperation (G := V) (admittedTurn Ω n S hS F P)
      (encodeHistory Ω n h.val) s (rightSourceCode Ω n S F h W) =
        rightTensorOperation (G := V) (physicalInstrument P h) ()
          (encodeOutcome Ω n ⁻¹' s) W := by
  have heq : (rightTensorOperation (G := V) (admittedTurn Ω n S hS F P)
      (encodeHistory Ω n h.val) s).comp (rightSourceCode Ω n S F h) =
      rightTensorOperation (G := V) (physicalInstrument P h) () (encodeOutcome Ω n ⁻¹' s) := by
    apply nuclear_joint_clm_ext_tensors
    intro T U
    simp only [ContinuousLinearMap.comp_apply, rightSourceCode_tensor]
    rw [rightTensorOperation_tensor _ _ _ hs, admittedTurn_all_events_on_physical,
      rightTensorOperation_tensor _ _ _ ((measurable_encodeOutcome Ω n) hs)]
    rfl
  exact congrArg (fun L => L W) heq

theorem admittedTurn_left_dummy (h : S) (W : Nuc (Joint (E h) V)) :
    tensorOperation (G := V) (admittedTurn Ω n S hS F P)
      (encodeHistory Ω n h.val) {dummyRecord Ω} (leftSourceCode Ω n S F h W) = 0 := by
  rw [admittedTurn_left_all_events Ω n S hS F P h _ (MeasurableSet.singleton _),
    encodeOutcome_preimage_dummy, tensorOperation_empty]
  exact zero_apply W

theorem admittedTurn_right_dummy (h : S) (W : Nuc (Joint V (E h))) :
    rightTensorOperation (G := V) (admittedTurn Ω n S hS F P)
      (encodeHistory Ω n h.val) {dummyRecord Ω} (rightSourceCode Ω n S F h W) = 0 := by
  rw [admittedTurn_right_all_events Ω n S hS F P h _ (MeasurableSet.singleton _),
    encodeOutcome_preimage_dummy, rightTensorOperation_empty]
  exact zero_apply W

end FullSpectatorEvents

namespace PhysicalDomains

variable {Ω} (D : PhysicalDomains Ω)

theorem encoded_not_acting (n : ℕ) (b : Bool) (h : D.admissible n)
    (hh : D.party n h ≠ b) :
    encodeHistory Ω n h.val ∉ range
      (fun z : D.actingDomain n b => encodeHistory Ω n z.val) := by
  intro hr
  obtain ⟨z,hz⟩ := hr
  have he : D.actingHistory n b z = h := by
    apply Subtype.ext
    exact (encodeHistory_injective Ω n) hz
  have hp := D.party_actingHistory n b z
  rw [he] at hp
  exact hh hp

end PhysicalDomains

section DerivedProjections

variable {Z : Type*} [MeasurableSpace Z] {E G : Z → Type*}
  [∀ z, NormedAddCommGroup (E z)] [∀ z, InnerProductSpace ℂ (E z)]
  [∀ z, CompleteSpace (E z)]
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]

@[simp] theorem pullbackFamily_rangeProjection (F : FundamentalFamily E)
    {H : Type*} [MeasurableSpace H] (f : H → Z) (hf : Measurable f) (h : H) :
    (pullbackFamily F f hf).rangeProjection h = F.rangeProjection (f h) := rfl

theorem transportFamily_rangeProjection (F : FundamentalFamily E)
    (J : (z : Z) → E z ≃ₗᵢ[ℂ] G z) (z : Z) :
    (transportFamily F J).rangeProjection z = F.rangeProjection z := by
  apply ContinuousLinearMap.ext
  intro y
  apply lp.ext
  funext n
  rw [FundamentalFamily.rangeProjection_coordinate, FundamentalFamily.rangeProjection_coordinate]
  have hf : (transportFamily F J).frame n z = J z (F.frame n z) :=
    frame_isometry (J z).toLinearIsometry (F.vector z) n
  have hz : J z (F.frame n z) = 0 ↔ F.frame n z = 0 := by
    constructor
    · intro h
      apply (J z).injective
      simpa only [map_zero] using h
    · intro h
      rw [h,map_zero]
  simp only [hf, ne_eq, hz]

theorem glueFamily_rangeProjection_on (S : Set Z) (hS : MeasurableSet S)
    (FS : FundamentalFamily (fun z : S => E z.val))
    (F : FundamentalFamily E) (z : S) :
    (glueFamily S hS FS F).rangeProjection z.val = FS.rangeProjection z := by
  apply ContinuousLinearMap.ext
  intro y
  apply lp.ext
  funext n
  rw [FundamentalFamily.rangeProjection_coordinate, FundamentalFamily.rangeProjection_coordinate]
  have hv : (glueFamily S hS FS F).vector z.val = FS.vector z := by
    funext i
    simp only [glueFamily, z.property, ↓reduceDIte]
  change (if QuantumProver.CountableGramSchmidt.frame
    ((glueFamily S hS FS F).vector z.val) n ≠ 0 then y n else 0) =
      if QuantumProver.CountableGramSchmidt.frame (FS.vector z) n ≠ 0 then y n else 0
  rw [hv]

theorem glueFamily_rangeProjection_off (S : Set Z) (hS : MeasurableSet S)
    (FS : FundamentalFamily (fun z : S => E z.val))
    (F : FundamentalFamily E) (z : Z) (hz : z ∉ S) :
    (glueFamily S hS FS F).rangeProjection z = F.rangeProjection z := by
  apply ContinuousLinearMap.ext
  intro y
  apply lp.ext
  funext n
  rw [FundamentalFamily.rangeProjection_coordinate, FundamentalFamily.rangeProjection_coordinate]
  have hv : (glueFamily S hS FS F).vector z = F.vector z := by
    funext i
    simp only [glueFamily, hz, ↓reduceDIte]
  change (if QuantumProver.CountableGramSchmidt.frame
    ((glueFamily S hS FS F).vector z) n ≠ 0 then y n else 0) =
      if QuantumProver.CountableGramSchmidt.frame (F.vector z) n ≠ 0 then y n else 0
  rw [hv]

end DerivedProjections

section ChosenProjectionCoherence

variable (D : PhysicalDomains Ω) (b : Bool)
  {E : (n : ℕ) → D.admissible n → Type v}
  [∀ n h, NormedAddCommGroup (E n h)] [∀ n h, InnerProductSpace ℂ (E n h)]
  [∀ n h, CompleteSpace (E n h)]
  (F : (n : ℕ) → FundamentalFamily (E n))
  {G : (n : ℕ) → D.actingDomain n b × Ω n → Type w}
  [∀ n z, NormedAddCommGroup (G n z)] [∀ n z, InnerProductSpace ℂ (G n z)]
  [∀ n z, CompleteSpace (G n z)]
  (Q : (n : ℕ) → FundamentalFamily (G n))
  (W : PhysicalMemoryWiring Ω D b F Q)

theorem selectedMemory_acted_projection (n : ℕ) (r : D.successorDomain n b) :
    (selectedMemory Ω D b F Q W (n+1)).family.rangeProjection r.val =
      (Q n).rangeProjection (D.successorOutcomePoint n b r) := by
  simp only [selectedMemory, chooseNextMemory]
  rw [glueFamily_rangeProjection_on, actedNextFamily, transportFamily_rangeProjection,
    outputOnSuccessor, pullbackFamily_rangeProjection]

theorem selectedMemory_idle_projection (n : ℕ) (r : D.successorDomain n (!b)) :
    (selectedMemory Ω D b F Q W (n+1)).family.rangeProjection r.val =
      (selectedMemory Ω D b F Q W n).family.rangeProjection
        (D.predecessorHistory n (!b) r) := by
  have hr : r.val ∉ D.successorDomain n b := by
    intro ha
    exact Set.disjoint_left.mp (D.successorDomain_disjoint n b) ha r.property
  simp only [selectedMemory, chooseNextMemory]
  rw [glueFamily_rangeProjection_off _ _ _ _ _ hr, glueFamily_rangeProjection_on,
    idleNextFamily, transportFamily_rangeProjection, pullbackFamily_rangeProjection]

end ChosenProjectionCoherence

section FinalMatrixJoint

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
  {a b : ℕ}
  (JA : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EA 0 D.initialHistory)
  (JB : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EB 0 D.initialHistory)

theorem ofPhysicalFamilies_initial_joint
    (U : Nuc (Joint (EuclideanSpace ℂ (Fin a)) (EuclideanSpace ℂ (Fin b)))) :
    physicalJointCode
      (ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB).initialAlice
      (ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB).initialBob U =
      physicalJointCode ((FA 0).embedding D.initialHistory)
        ((FB 0).embedding D.initialHistory) (physicalJointCode JA JB U) := by
  simpa only [ofPhysicalFamilies, chargedInitialMemory, selectedMemory] using
    physicalJointCode_all_inputs JA JB ((FA 0).embedding D.initialHistory)
      ((FB 0).embedding D.initialHistory) U

section Reference

variable {R : Type} [Fintype R] [DecidableEq R]
local instance finalBlockComplete {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] : CompleteSpace (BlockSpace R V) :=
  PiLp.completeSpace 2 (fun _ : R => V)

theorem ofPhysicalFamilies_initial_joint_reference
    (U : Nuc (BlockSpace R
      (Joint (EuclideanSpace ℂ (Fin a)) (EuclideanSpace ℂ (Fin b))))) :
    normalAmplification (physicalJointCode
      (ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB).initialAlice
      (ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB).initialBob) U =
      normalAmplification (physicalJointCode ((FA 0).embedding D.initialHistory)
        ((FB 0).embedding D.initialHistory))
          (normalAmplification (physicalJointCode JA JB) U) := by
  simpa only [ofPhysicalFamilies, chargedInitialMemory, selectedMemory] using
    physicalJointCode_amplified JA JB ((FA 0).embedding D.initialHistory)
      ((FB 0).embedding D.initialHistory) U

end Reference

theorem ofPhysicalFamilies_bob_inactive (n : ℕ) (h : D.admissible n)
    (hh : D.party n h = true) (s : Set (CommonRecord Ω)) :
    ((ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB).bob n).operation
      (encodeHistory Ω n h.val) s =
      if dummyRecord Ω ∈ s then ContinuousLinearMap.id ℂ (Nuc CommonHilbert) else 0 := by
  apply admittedMemoryTurn_invalid
  apply D.encoded_not_acting n false h
  simp [hh]

theorem ofPhysicalFamilies_alice_inactive (n : ℕ) (h : D.admissible n)
    (hh : D.party n h = false) (s : Set (CommonRecord Ω)) :
    ((ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB).alice n).operation
      (encodeHistory Ω n h.val) s =
      if dummyRecord Ω ∈ s then ContinuousLinearMap.id ℂ (Nuc CommonHilbert) else 0 := by
  apply admittedMemoryTurn_invalid
  apply D.encoded_not_acting n true h
  simp [hh]

end FinalMatrixJoint

section FinalMemoryPreservation

variable (D : PhysicalDomains Ω) (b : Bool)
  {E : (n : ℕ) → D.admissible n → Type v}
  [∀ n h, NormedAddCommGroup (E n h)] [∀ n h, InnerProductSpace ℂ (E n h)]
  [∀ n h, CompleteSpace (E n h)]
  (F : (n : ℕ) → FundamentalFamily (E n))
  {G : (n : ℕ) → D.actingDomain n b × Ω n → Type w}
  [∀ n z, NormedAddCommGroup (G n z)] [∀ n z, InnerProductSpace ℂ (G n z)]
  [∀ n z, CompleteSpace (G n z)]
  (Q : (n : ℕ) → FundamentalFamily (G n))
  (W : PhysicalMemoryWiring Ω D b F Q) (P : PhysicalLocalFamily Ω D b F Q)

section Reference

variable {R : Type} [Fintype R] [DecidableEq R]
local instance memoryBlockComplete {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] : CompleteSpace (BlockSpace R V) :=
  PiLp.completeSpace 2 (fun _ : R => V)

theorem admittedMemoryTurn_reference_all_events (n : ℕ) (h : D.actingDomain n b)
    (s : Set (CommonRecord Ω)) (U : Nuc (BlockSpace R (E n (D.actingHistory n b h)))) :
    normalAmplification ((admittedMemoryTurn Ω D b F Q W P n).operation
      (encodeHistory Ω n h.val) s)
      (normalAmplification (padNuclear ((selectedMemory Ω D b F Q W n).family.embedding
        (D.actingHistory n b h))) U) =
        normalAmplification ((P.instrument n).represented_physical.operation h
          (encodeOutcome Ω n ⁻¹' s)) U := by
  simpa only [admittedMemoryTurn, chosenActiveSource, pullbackFamily_embedding,
    retargetedPhysicalInstrument, retargetRecordedSource, retargetSource_operation] using
      admittedTurn_amplified_all_events_on_physical Ω n (D.actingDomain n b)
        (D.measurableSet_actingDomain n b) (chosenActiveSource Ω D b F Q W n)
        (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical h s U

theorem admittedMemoryTurn_reference_dummy (n : ℕ) (h : D.actingDomain n b)
    (U : Nuc (BlockSpace R (E n (D.actingHistory n b h)))) :
    normalAmplification ((admittedMemoryTurn Ω D b F Q W P n).operation
      (encodeHistory Ω n h.val) {dummyRecord Ω})
      (normalAmplification (padNuclear ((selectedMemory Ω D b F Q W n).family.embedding
        (D.actingHistory n b h))) U) = 0 := by
  simpa only [admittedMemoryTurn, chosenActiveSource, pullbackFamily_embedding] using
    admittedTurn_amplified_dummy_on_physical Ω n (D.actingDomain n b)
      (D.measurableSet_actingDomain n b) (chosenActiveSource Ω D b F Q W n)
      (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical h U

end Reference

section Spectator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem admittedMemoryTurn_left_all_events (n : ℕ) (h : D.actingDomain n b)
    (s : Set (CommonRecord Ω)) (hs : MeasurableSet s)
    (U : Nuc (Joint (E n (D.actingHistory n b h)) V)) :
    tensorOperation (G := V) (admittedMemoryTurn Ω D b F Q W P n)
      (encodeHistory Ω n h.val) s
      (leftSourceCode Ω n (D.actingDomain n b) (chosenActiveSource Ω D b F Q W n) h U) =
        tensorOperation (G := V) (physicalInstrument (P.instrument n).represented_physical h) ()
          (encodeOutcome Ω n ⁻¹' s) U := by
  simpa only [admittedMemoryTurn, retargetedPhysicalInstrument, retargetRecordedSource,
    physicalInstrument, retargetSource] using
      admittedTurn_left_all_events Ω n (D.actingDomain n b)
        (D.measurableSet_actingDomain n b) (chosenActiveSource Ω D b F Q W n)
        (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical h s hs U

theorem admittedMemoryTurn_right_all_events (n : ℕ) (h : D.actingDomain n b)
    (s : Set (CommonRecord Ω)) (hs : MeasurableSet s)
    (U : Nuc (Joint V (E n (D.actingHistory n b h)))) :
    rightTensorOperation (G := V) (admittedMemoryTurn Ω D b F Q W P n)
      (encodeHistory Ω n h.val) s
      (rightSourceCode Ω n (D.actingDomain n b) (chosenActiveSource Ω D b F Q W n) h U) =
        rightTensorOperation (G := V) (physicalInstrument (P.instrument n).represented_physical h) ()
          (encodeOutcome Ω n ⁻¹' s) U := by
  simpa only [admittedMemoryTurn, retargetedPhysicalInstrument, retargetRecordedSource,
    physicalInstrument, retargetSource] using
      admittedTurn_right_all_events Ω n (D.actingDomain n b)
        (D.measurableSet_actingDomain n b) (chosenActiveSource Ω D b F Q W n)
        (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical h s hs U

theorem admittedMemoryTurn_left_dummy (n : ℕ) (h : D.actingDomain n b)
    (U : Nuc (Joint (E n (D.actingHistory n b h)) V)) :
    tensorOperation (G := V) (admittedMemoryTurn Ω D b F Q W P n)
      (encodeHistory Ω n h.val) {dummyRecord Ω}
      (leftSourceCode Ω n (D.actingDomain n b) (chosenActiveSource Ω D b F Q W n) h U) = 0 :=
  admittedTurn_left_dummy Ω n (D.actingDomain n b) (D.measurableSet_actingDomain n b)
    (chosenActiveSource Ω D b F Q W n)
    (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical h U

theorem admittedMemoryTurn_right_dummy (n : ℕ) (h : D.actingDomain n b)
    (U : Nuc (Joint V (E n (D.actingHistory n b h)))) :
    rightTensorOperation (G := V) (admittedMemoryTurn Ω D b F Q W P n)
      (encodeHistory Ω n h.val) {dummyRecord Ω}
      (rightSourceCode Ω n (D.actingDomain n b) (chosenActiveSource Ω D b F Q W n) h U) = 0 :=
  admittedTurn_right_dummy Ω n (D.actingDomain n b) (D.measurableSet_actingDomain n b)
    (chosenActiveSource Ω D b F Q W n)
    (retargetedPhysicalInstrument Ω D b F Q W P n).represented_physical h U

end Spectator
end FinalMemoryPreservation

section PhysicalPhysicalJointTransition

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 6000000

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

theorem physicalAlice_joint_transition (n : ℕ) (h : D.actingDomain n true)
    (s : Set (CommonRecord Ω)) (hs : MeasurableSet s) :
    (tensorOperation (F := CommonHilbert) (E := CommonHilbert) (G := CommonHilbert)
      (admittedMemoryTurn Ω D true FA QA WA PA n)
      (encodeHistory Ω n h.val) s).comp
      (physicalJointCode (X := EA n (D.actingHistory n true h))
        (X' := EB n (D.actingHistory n true h)) (Y := CommonHilbert) (Y' := CommonHilbert)
        ((selectedMemory Ω D true FA QA WA n).family.embedding (D.actingHistory n true h))
        ((selectedMemory Ω D false FB QB WB n).family.embedding (D.actingHistory n true h))) =
      (rightSourceCode (E := EB n) (V := CommonHilbert) Ω n (D.admissible n)
        (selectedMemory Ω D false FB QB WB n).family (D.actingHistory n true h)).comp
        (tensorOperation (F := EA n (D.actingHistory n true h)) (E := CommonHilbert)
          (G := EB n (D.actingHistory n true h))
          (physicalPhysicalMemoryTurn Ω D true FA QA PA n h) () (encodeOutcome Ω n ⁻¹' s)) := by
  apply nuclear_joint_clm_ext_tensors
    (E := EA n (D.actingHistory n true h)) (E' := EA n (D.actingHistory n true h))
    (F := EB n (D.actingHistory n true h)) (F' := EB n (D.actingHistory n true h))
  intro T U
  simp only [ContinuousLinearMap.comp_apply, physicalJointCode_tensor]
  have hMatrix := tensorOperation_tensor
    (F := CommonHilbert) (E := CommonHilbert) (G := CommonHilbert)
    (admittedMemoryTurn Ω D true FA QA WA PA n) (encodeHistory Ω n h.val) s hs
    (padNuclear ((selectedMemory Ω D true FA QA WA n).family.embedding
      (D.actingHistory n true h)) T)
    (padNuclear ((selectedMemory Ω D false FB QB WB n).family.embedding
      (D.actingHistory n true h)) U)
  have hLocal := admittedMemoryTurn_all_events Ω D true FA QA WA PA n h s T
  have hPhysical := tensorOperation_tensor
    (F := EA n (D.actingHistory n true h)) (E := CommonHilbert)
    (G := EB n (D.actingHistory n true h))
    (physicalPhysicalMemoryTurn Ω D true FA QA PA n h) () (encodeOutcome Ω n ⁻¹' s)
    ((measurable_encodeOutcome Ω n) hs) T U
  have hRemote := rightSourceCode_tensor (E := EB n) (V := CommonHilbert)
    Ω n (D.admissible n) (selectedMemory Ω D false FB QB WB n).family
    (D.actingHistory n true h)
    ((PA.instrument n).represented_physical.operation h (encodeOutcome Ω n ⁻¹' s) T) U
  rw [physicalPhysicalMemoryTurn_operation] at hPhysical
  rw [hMatrix, hLocal, hPhysical, hRemote]

theorem physicalBob_joint_transition (n : ℕ) (h : D.actingDomain n false)
    (s : Set (CommonRecord Ω)) (hs : MeasurableSet s) :
    (rightTensorOperation (F := CommonHilbert) (E := CommonHilbert) (G := CommonHilbert)
      (admittedMemoryTurn Ω D false FB QB WB PB n)
      (encodeHistory Ω n h.val) s).comp
      (physicalJointCode (X := EA n (D.actingHistory n false h))
        (X' := EB n (D.actingHistory n false h)) (Y := CommonHilbert) (Y' := CommonHilbert)
        ((selectedMemory Ω D true FA QA WA n).family.embedding (D.actingHistory n false h))
        ((selectedMemory Ω D false FB QB WB n).family.embedding (D.actingHistory n false h))) =
      (leftSourceCode (E := EA n) (V := CommonHilbert) Ω n (D.admissible n)
        (selectedMemory Ω D true FA QA WA n).family (D.actingHistory n false h)).comp
        (rightTensorOperation (F := EB n (D.actingHistory n false h)) (E := CommonHilbert)
          (G := EA n (D.actingHistory n false h))
          (physicalPhysicalMemoryTurn Ω D false FB QB PB n h) () (encodeOutcome Ω n ⁻¹' s)) := by
  apply nuclear_joint_clm_ext_tensors
    (E := EA n (D.actingHistory n false h)) (E' := EA n (D.actingHistory n false h))
    (F := EB n (D.actingHistory n false h)) (F' := EB n (D.actingHistory n false h))
  intro T U
  simp only [ContinuousLinearMap.comp_apply, physicalJointCode_tensor]
  have hMatrix := rightTensorOperation_tensor
    (F := CommonHilbert) (E := CommonHilbert) (G := CommonHilbert)
    (admittedMemoryTurn Ω D false FB QB WB PB n) (encodeHistory Ω n h.val) s hs
    (padNuclear ((selectedMemory Ω D true FA QA WA n).family.embedding
      (D.actingHistory n false h)) T)
    (padNuclear ((selectedMemory Ω D false FB QB WB n).family.embedding
      (D.actingHistory n false h)) U)
  have hLocal := admittedMemoryTurn_all_events Ω D false FB QB WB PB n h s U
  have hPhysical := rightTensorOperation_tensor
    (F := EB n (D.actingHistory n false h)) (E := CommonHilbert)
    (G := EA n (D.actingHistory n false h))
    (physicalPhysicalMemoryTurn Ω D false FB QB PB n h) () (encodeOutcome Ω n ⁻¹' s)
    ((measurable_encodeOutcome Ω n) hs) T U
  have hRemote := leftSourceCode_tensor (E := EA n) (V := CommonHilbert)
    Ω n (D.admissible n) (selectedMemory Ω D true FA QA WA n).family
    (D.actingHistory n false h) T
    ((PB.instrument n).represented_physical.operation h (encodeOutcome Ω n ⁻¹' s) U)
  rw [physicalPhysicalMemoryTurn_operation] at hPhysical
  rw [hMatrix, hLocal, hPhysical, hRemote]

end PhysicalPhysicalJointTransition

end QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission
