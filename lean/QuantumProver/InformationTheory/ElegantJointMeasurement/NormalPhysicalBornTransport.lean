import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalOperationalBridge
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalEventChronology
import QuantumProver.InformationTheory.ElegantJointMeasurement.PhysicalTranscriptCoding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory ProbabilityTheory Set Filter Function InnerProductSpace TopologicalSpace Preorder
open scoped BigOperators Topology ComplexOrder
namespace QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge
open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertRecordCoding
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM QuantumProver.ElegantJointMeasurement.PhysicalTranscriptCoding
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.NuclearOperator (toOperator)
universe u v w

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
  [∀ n, StandardBorelSpace (Ω n)]

section PhysicalCylinderAndBornLaw

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

def physicalCylinderEffect (k : ℕ) (s : Set (QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Prefix (CommonRecord Ω) k)) : JointInputMatrix a b :=
  fun i j => QuantumProver.HilbertNuclearTrace.trace
    (physicalPrefixAction Ω D FA FB QA QB WA WB PA PB JA JB (k+1) s (Matrix.single j i (1 : ℂ)))

theorem physicalCylinderEffect_eq_admitted (k : ℕ) (s : Set (QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Prefix (CommonRecord Ω) k))
    (hs : MeasurableSet s) :
    physicalCylinderEffect Ω D FA FB QA QB WA WB PA PB JA JB k s = (N).represented_physicalCylinderEffect k s := by
  ext i j
  exact congrArg QuantumProver.HilbertNuclearTrace.trace
    (physicalPrefixAction_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB (k+1) s hs _)

def physicalCylinderPOVM : ConsistentCylinderPOVM (CommonRecord Ω) (Fin a × Fin b) where
  effect := physicalCylinderEffect Ω D FA FB QA QB WA WB PA PB JA JB
  empty := by
    intro k
    rw [physicalCylinderEffect_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB k ∅ MeasurableSet.empty]
    exact (N).represented_physicalCylinderPOVM.empty k
  positive := by
    intro k s hs
    rw [physicalCylinderEffect_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB k s hs]
    exact (N).represented_physicalCylinderPOVM.positive k s hs
  total := by
    intro k
    rw [physicalCylinderEffect_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB k univ MeasurableSet.univ]
    exact (N).represented_physicalCylinderPOVM.total k
  coordinate_additive := by
    intro k s hs hd i j
    simp_rw [physicalCylinderEffect_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB k _ (hs _)]
    rw [physicalCylinderEffect_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB k _ (MeasurableSet.iUnion hs)]
    exact (N).represented_physicalCylinderPOVM.coordinate_additive k s hs hd i j
  consistent := by
    intro k l hkl s hs
    rw [physicalCylinderEffect_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB l _
      (hs.preimage (SquareProcess.measurable_prefixRestrict hkl)),
      physicalCylinderEffect_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB k s hs]
    exact (N).represented_physicalCylinderPOVM.consistent k l hkl s hs

local instance physicalCommonRecordNonempty : Nonempty (CommonRecord Ω) := ⟨dummyRecord Ω⟩

def physicalTranscriptVectorMeasure : VectorMeasure (Transcript (CommonRecord Ω)) (JointInputMatrix a b) :=
  (physicalCylinderPOVM Ω D FA FB QA QB WA WB PA PB JA JB).fullVectorMeasure

theorem physicalTranscriptVectorMeasure_prefix (k : ℕ) (s : Set (QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Prefix (CommonRecord Ω) k))
    (hs : MeasurableSet s) :
    physicalTranscriptVectorMeasure Ω D FA FB QA QB WA WB PA PB JA JB
      ((frestrictLe (π := fun _ => CommonRecord Ω) k) ⁻¹' s) =
      physicalCylinderEffect Ω D FA FB QA QB WA WB PA PB JA JB k s :=
  (physicalCylinderPOVM Ω D FA FB QA QB WA WB PA PB JA JB).fullVectorMeasure_prefix k s hs

theorem physicalTranscriptVectorMeasure_eq_admitted :
    physicalTranscriptVectorMeasure Ω D FA FB QA QB WA WB PA PB JA JB =
      (N).represented_physicalTranscriptVectorMeasure := by
  apply vectorMeasure_eq_of_prefix
  intro k s hs
  rw [physicalTranscriptVectorMeasure_prefix Ω D FA FB QA QB WA WB PA PB JA JB k s hs,
    (N).represented_physicalTranscriptVectorMeasure_prefix k s hs,
    physicalCylinderEffect_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB k s hs]

theorem physicalTranscriptVectorMeasure_unique
    (F : VectorMeasure (Transcript (CommonRecord Ω)) (JointInputMatrix a b))
    (hF : ∀ k (s : Set (QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Prefix (CommonRecord Ω) k)), MeasurableSet s →
      F ((frestrictLe (π := fun _ => CommonRecord Ω) k) ⁻¹' s) =
        physicalCylinderEffect Ω D FA FB QA QB WA WB PA PB JA JB k s) :
    F = physicalTranscriptVectorMeasure Ω D FA FB QA QB WA WB PA PB JA JB := by
  apply vectorMeasure_eq_of_prefix
  intro k s hs
  exact (hF k s hs).trans
    (physicalTranscriptVectorMeasure_prefix Ω D FA FB QA QB WA WB PA PB JA JB k s hs).symm

def physicalCodedBornMeasure (X : JointInputMatrix a b) (hX : X.PosSemidef) :
    Measure (Transcript (CommonRecord Ω)) :=
  (physicalCylinderPOVM Ω D FA FB QA QB WA WB PA PB JA JB).fullBornMeasure X hX

theorem physicalCodedBornMeasure_eq_admitted (X : JointInputMatrix a b) (hX : X.PosSemidef) :
    physicalCodedBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX = (N).represented_physicalBornMeasure X hX := by
  apply Measure.ext
  intro s hs
  rw [physicalCodedBornMeasure,
    (physicalCylinderPOVM Ω D FA FB QA QB WA WB PA PB JA JB).fullBornMeasure_apply X hX s hs,
    (N).physicalBornMeasure_apply X hX s hs]
  change ENNReal.ofReal ((physicalTranscriptVectorMeasure Ω D FA FB QA QB WA WB PA PB JA JB s * X).trace.re) = _
  rw [physicalTranscriptVectorMeasure_eq_admitted]

theorem physicalCodedBornMeasure_prefix (X : JointInputMatrix a b) (hX : X.PosSemidef)
    (k : ℕ) (s : Set (QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Prefix (CommonRecord Ω) k)) (hs : MeasurableSet s) :
    physicalCodedBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX
      ((frestrictLe (π := fun _ => CommonRecord Ω) k) ⁻¹' s) =
      ENNReal.ofReal (QuantumProver.HilbertNuclearTrace.trace
        (physicalPrefixAction Ω D FA FB QA QB WA WB PA PB JA JB (k+1) s X)).re := by
  rw [physicalCodedBornMeasure_eq_admitted, (N).physicalBornMeasure_prefix X hX k s hs,
    physicalPrefixAction_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB (k+1) s hs X]

instance physicalCodedBornMeasure_finite (X : JointInputMatrix a b) (hX : X.PosSemidef) :
    IsFiniteMeasure (physicalCodedBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX) := by
  change IsFiniteMeasure ((physicalCylinderPOVM Ω D FA FB QA QB WA WB PA PB JA JB).fullBornMeasure X hX)
  infer_instance

theorem physicalCodedBornMeasure_probability (X : JointInputMatrix a b) (hX : X.PosSemidef)
    (htrace : X.trace = 1) :
    IsProbabilityMeasure (physicalCodedBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX) :=
  (physicalCylinderPOVM Ω D FA FB QA QB WA WB PA PB JA JB).fullBornMeasure_isProbability X hX htrace

theorem physicalCodedBornMeasure_ae_prefix_supported (X : JointInputMatrix a b) (hX : X.PosSemidef)
    (k : ℕ) : ∀ᵐ t ∂physicalCodedBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX,
      frestrictLe (π := fun _ => CommonRecord Ω) k t ∈
        encodedPhysicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB (k+1) := by
  apply ae_iff.mpr
  change physicalCodedBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX
    ((frestrictLe (π := fun _ => CommonRecord Ω) k) ⁻¹'
      (encodedPhysicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB (k+1))ᶜ) = 0
  rw [physicalCodedBornMeasure_prefix Ω D FA FB QA QB WA WB PA PB JA JB X hX k _
    (measurableSet_encodedPhysicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB (k+1)).compl,
    physicalPrefixAction_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB (k+1) _
      (measurableSet_encodedPhysicallySupportedHistory Ω D FA FB QA QB WA WB PA PB JA JB (k+1)).compl X,
    physical_physicalPrefixAction_bad_zero Ω D FA FB QA QB WA WB PA PB JA JB (k+1) X]
  simp

theorem physicalCodedBornMeasure_ae_physicalTranscript (X : JointInputMatrix a b) (hX : X.PosSemidef) :
    ∀ᵐ t ∂physicalCodedBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX,
      t ∈ range (encodePhysicalTranscript Ω) := by
  have hAll := ae_all_iff.mpr
    (fun k => physicalCodedBornMeasure_ae_prefix_supported Ω D FA FB QA QB WA WB PA PB JA JB X hX k)
  filter_upwards [hAll] with t ht
  have hOutcome : ∀ k, ∃ x : Ω k, encodeOutcome Ω k x = t k := by
    intro k
    rcases ht k with ⟨h,hh,he⟩
    have hp : commonPrefix Ω t (k+1) = frestrictLe (π := fun _ => CommonRecord Ω) k t :=
      commonPrefix_eq_prefixProjection Ω t k
    refine ⟨h.val.2, ?_⟩
    have hLast := congrArg (fun z => ((appendHistory (R := CommonRecord Ω) k).symm z).2)
      (he.trans hp.symm)
    change ((appendHistory k).symm (appendHistory k
      (encodeHistory Ω k h.val.1,encodeOutcome Ω k h.val.2))).2 =
      ((appendHistory k).symm (appendHistory k (commonPrefix Ω t k,t k))).2 at hLast
    simpa only [MeasurableEquiv.symm_apply_apply] using hLast
  choose x hx using hOutcome
  exact ⟨x,funext hx⟩

def physicalBornMeasure (X : JointInputMatrix a b) (hX : X.PosSemidef) : Measure (PhysicalTranscript Ω) :=
  (physicalCodedBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX).comap (encodePhysicalTranscript Ω)

theorem physicalBornMeasure_map (X : JointInputMatrix a b) (hX : X.PosSemidef) :
    (physicalBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX).map (encodePhysicalTranscript Ω) =
      (N).represented_physicalBornMeasure X hX := by
  rw [physicalBornMeasure, (measurableEmbedding_encodePhysicalTranscript Ω).map_comap,
    Measure.restrict_eq_self_of_ae_mem
      (physicalCodedBornMeasure_ae_physicalTranscript Ω D FA FB QA QB WA WB PA PB JA JB X hX),
    physicalCodedBornMeasure_eq_admitted]

instance physicalBornMeasure_finite (X : JointInputMatrix a b) (hX : X.PosSemidef) :
    IsFiniteMeasure (physicalBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX) := by
  dsimp only [physicalBornMeasure]
  infer_instance

theorem physicalBornMeasure_probability (X : JointInputMatrix a b) (hX : X.PosSemidef)
    (htrace : X.trace = 1) :
    IsProbabilityMeasure (physicalBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX) := by
  letI := physicalCodedBornMeasure_probability Ω D FA FB QA QB WA WB PA PB JA JB X hX htrace
  exact (measurableEmbedding_encodePhysicalTranscript Ω).isProbabilityMeasure_comap
    (physicalCodedBornMeasure_ae_physicalTranscript Ω D FA FB QA QB WA WB PA PB JA JB X hX)

theorem physicalBornMeasure_physical_prefix (X : JointInputMatrix a b) (hX : X.PosSemidef)
    (k : ℕ) (s : Set (RoundHistory Ω (k+1))) (hs : MeasurableSet s) :
    physicalBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX
      {t | roundPrefix Ω t (k+1) ∈ s} =
      ENNReal.ofReal (QuantumProver.HilbertNuclearTrace.trace
        (physicalPrefixAction Ω D FA FB QA QB WA WB PA PB JA JB (k+1)
          (encodeHistory Ω (k+1) '' s) X)).re := by
  have hp : encodePhysicalTranscript Ω ⁻¹'
      ((frestrictLe (π := fun _ => CommonRecord Ω) k) ⁻¹' (encodeHistory Ω (k+1) '' s)) =
      {t | roundPrefix Ω t (k+1) ∈ s} := by
    ext t
    change prefixProjection Ω k (encodePhysicalTranscript Ω t) ∈
      encodeHistory Ω (k+1) '' s ↔ roundPrefix Ω t (k+1) ∈ s
    rw [encodePhysicalTranscript_prefix Ω t k]
    exact (encodeHistory_injective Ω (k+1)).mem_set_image
  have hMatrix := (N).physicalBornMeasure_prefix X hX k (encodeHistory Ω (k+1) '' s)
    ((measurableEmbedding_encodeHistory Ω (k+1)).measurableSet_image' hs)
  rw [← physicalBornMeasure_map Ω D FA FB QA QB WA WB PA PB JA JB X hX,
    (measurableEmbedding_encodePhysicalTranscript Ω).map_apply, hp] at hMatrix
  rw [physicalPrefixAction_eq_admitted Ω D FA FB QA QB WA WB PA PB JA JB (k+1) _
    ((measurableEmbedding_encodeHistory Ω (k+1)).measurableSet_image' hs) X]
  exact hMatrix

theorem physicalReport_nullMeasurable (X : JointInputMatrix a b) (hX : X.PosSemidef)
    (J : PhysicalTranscript Ω → Fin 4)
    (hJ : NullMeasurable J (physicalBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX)) :
    NullMeasurable (liftPhysicalReport Ω J) ((N).represented_physicalBornMeasure X hX) := by
  rw [← physicalBornMeasure_map Ω D FA FB QA QB WA WB PA PB JA JB X hX]
  exact nullMeasurable_liftPhysicalReport Ω _ J hJ

theorem physicalReport_probability (X : JointInputMatrix a b) (hX : X.PosSemidef)
    (J : PhysicalTranscript Ω → Fin 4) (s : Set (Fin 4)) :
    (N).represented_physicalBornMeasure X hX (liftPhysicalReport Ω J ⁻¹' s) =
      physicalBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX (J ⁻¹' s) := by
  rw [← physicalBornMeasure_map Ω D FA FB QA QB WA WB PA PB JA JB X hX]
  exact liftPhysicalReport_event_probability Ω _ J s

theorem physicalReport_completed_event_probability (X : JointInputMatrix a b)
    (hX : X.PosSemidef) (J : PhysicalTranscript Ω → Fin 4)
    (hJ : NullMeasurable J (physicalBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX))
    (s : Set (Fin 4)) (hs : MeasurableSet s) :
    NullMeasurableSet (liftPhysicalReport Ω J ⁻¹' s) ((N).represented_physicalBornMeasure X hX) ∧
      (N).represented_physicalBornMeasure X hX (liftPhysicalReport Ω J ⁻¹' s) =
        physicalBornMeasure Ω D FA FB QA QB WA WB PA PB JA JB X hX (J ⁻¹' s) :=
  ⟨physicalReport_nullMeasurable Ω D FA FB QA QB WA WB PA PB JA JB X hX J hJ hs,
    physicalReport_probability Ω D FA FB QA QB WA WB PA PB JA JB X hX J s⟩

end PhysicalCylinderAndBornLaw
end QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge
