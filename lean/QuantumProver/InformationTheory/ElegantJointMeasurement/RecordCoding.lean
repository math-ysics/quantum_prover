import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentAbsorption
import QuantumProver.InformationTheory.ElegantJointMeasurement.SquareProcess

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open MeasureTheory ProbabilityTheory Set Function Filter Topology
open scoped BigOperators ComplexOrder Topology Classical

namespace QuantumProver.ElegantJointMeasurement.HilbertRecordCoding

open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess (History appendHistory)

universe u

private theorem measurable_sigmaMk {D : Type*} (F : D → Type*)
    [∀ d, MeasurableSpace (F d)] (d : D) : Measurable (Sigma.mk d : F d → Sigma F) := by
  intro s hs
  change MeasurableSet[⨅ e, (inferInstance : MeasurableSpace (F e)).map (Sigma.mk e)] s at hs
  rw [MeasurableSpace.measurableSet_iInf] at hs
  exact hs d

private theorem borelSpace_sigma {D : Type*} [Countable D] (F : D → Type*)
    [∀ d, TopologicalSpace (F d)] [∀ d, MeasurableSpace (F d)]
    [∀ d, BorelSpace (F d)] : BorelSpace (Sigma F) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hp : ∀ d, MeasurableSet (Sigma.mk d ⁻¹' s) := by
      change MeasurableSet[⨅ d, (inferInstance : MeasurableSpace (F d)).map (Sigma.mk d)] s at hs
      rwa [MeasurableSpace.measurableSet_iInf] at hs
    let : MeasurableSpace (Sigma F) := borel (Sigma F)
    let : BorelSpace (Sigma F) := ⟨rfl⟩
    have he : s = ⋃ d, Sigma.mk d '' (Sigma.mk d ⁻¹' s) := by
      ext z
      constructor
      · intro hz
        exact mem_iUnion.mpr ⟨z.1, mem_image_of_mem (Sigma.mk z.1) hz⟩
      · intro hz
        rcases mem_iUnion.mp hz with ⟨d, x, hx, rfl⟩
        exact hx
    rw [he]
    exact MeasurableSet.iUnion fun d =>
      Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding.measurableSet_image' (hp d)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    change MeasurableSet[⨅ d, (inferInstance : MeasurableSpace (F d)).map (Sigma.mk d)] s
    rw [MeasurableSpace.measurableSet_iInf]
    exact fun d => (isOpen_sigma_iff.mp hs d).measurableSet

private theorem borelSpace_sum {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B] :
    BorelSpace (A ⊕ B) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hl := (measurableSet_sum_iff.mp hs).1
    have hr := (measurableSet_sum_iff.mp hs).2
    let : MeasurableSpace (A ⊕ B) := borel (A ⊕ B)
    let : BorelSpace (A ⊕ B) := ⟨rfl⟩
    have he : s = Sum.inl '' (Sum.inl ⁻¹' s) ∪ Sum.inr '' (Sum.inr ⁻¹' s) := by
      ext z
      cases z <;> simp
    rw [he]
    exact (Topology.IsOpenEmbedding.inl.measurableEmbedding.measurableSet_image' hl).union
      (Topology.IsOpenEmbedding.inr.measurableEmbedding.measurableSet_image' hr)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact measurableSet_sum_iff.mpr
      ⟨(isOpen_sum_iff.mp hs).1.measurableSet, (isOpen_sum_iff.mp hs).2.measurableSet⟩

abbrev CommonRecord (Ω : ℕ → Type u) := Unit ⊕ Sigma Ω

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]

def dummyRecord : CommonRecord Ω := Sum.inl ()

def encodeOutcome (n : ℕ) (x : Ω n) : CommonRecord Ω := Sum.inr ⟨n, x⟩

theorem measurable_encodeOutcome (n : ℕ) : Measurable (encodeOutcome Ω n) :=
  measurable_inr.comp (measurable_sigmaMk Ω n)

omit [∀ n, MeasurableSpace (Ω n)] in
theorem encodeOutcome_injective (n : ℕ) : Injective (encodeOutcome Ω n) := by
  intro x y h
  exact eq_of_heq (Sigma.mk.inj (Sum.inr_injective h)).2

instance commonRecord_standardBorel [∀ n, StandardBorelSpace (Ω n)] :
    StandardBorelSpace (CommonRecord Ω) := by
  let := fun n => upgradeStandardBorel (Ω n)
  let : BorelSpace (Sigma Ω) := borelSpace_sigma Ω
  let : BorelSpace (CommonRecord Ω) := borelSpace_sum
  infer_instance

theorem measurableEmbedding_encodeOutcome [∀ n, StandardBorelSpace (Ω n)] (n : ℕ) :
    MeasurableEmbedding (encodeOutcome Ω n) := by
  let := upgradeStandardBorel (Ω n)
  let := upgradeStandardBorel (CommonRecord Ω)
  exact (measurable_encodeOutcome Ω n).measurableEmbedding (encodeOutcome_injective Ω n)

omit [∀ n, MeasurableSpace (Ω n)] in
theorem encodeOutcome_preimage_image (n : ℕ) (s : Set (Ω n)) :
    encodeOutcome Ω n ⁻¹' (encodeOutcome Ω n '' s) = s :=
  (encodeOutcome_injective Ω n).preimage_image s

omit [∀ n, MeasurableSpace (Ω n)] in
theorem encodeOutcome_preimage_wrong_tag {n m : ℕ} (hnm : n ≠ m) (s : Set (Ω m)) :
    encodeOutcome Ω n ⁻¹' (encodeOutcome Ω m '' s) = ∅ := by
  ext x
  constructor
  · rintro ⟨y, _, he⟩
    exact False.elim (hnm (congrArg Sigma.fst (Sum.inr_injective he)).symm)
  · exact False.elim

omit [∀ n, MeasurableSpace (Ω n)] in
@[simp] theorem encodeOutcome_preimage_dummy (n : ℕ) :
    encodeOutcome Ω n ⁻¹' {dummyRecord Ω} = ∅ := by
  ext x
  simp [encodeOutcome, dummyRecord]

abbrev RoundHistory : ℕ → Type u
  | 0 => PUnit
  | n + 1 => RoundHistory n × Ω n

instance roundHistory_measurableSpace : (n : ℕ) → MeasurableSpace (RoundHistory Ω n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n + 1 => by
      let := roundHistory_measurableSpace n
      exact inferInstanceAs (MeasurableSpace (RoundHistory Ω n × Ω n))

instance roundHistory_standardBorel [∀ n, StandardBorelSpace (Ω n)] (n : ℕ) :
    StandardBorelSpace (RoundHistory Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (StandardBorelSpace PUnit)
  | succ n ih =>
      let := ih
      exact inferInstanceAs (StandardBorelSpace (RoundHistory Ω n × Ω n))

private theorem commonHistory_standardBorel [∀ n, StandardBorelSpace (Ω n)] (n : ℕ) :
    StandardBorelSpace (History (CommonRecord Ω) n) := by
  cases n <;> infer_instance

def encodeHistory : (n : ℕ) → RoundHistory Ω n → History (CommonRecord Ω) n
  | 0, h => h
  | n + 1, h => appendHistory n (encodeHistory n h.1, encodeOutcome Ω n h.2)

@[simp] theorem encodeHistory_append (n : ℕ) (h : RoundHistory Ω n) (x : Ω n) :
    encodeHistory Ω (n+1) (h,x) =
      appendHistory n (encodeHistory Ω n h, encodeOutcome Ω n x) := rfl

theorem measurable_encodeHistory (n : ℕ) : Measurable (encodeHistory Ω n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih =>
      exact (appendHistory n).measurable.comp
        ((ih.comp measurable_fst).prodMk ((measurable_encodeOutcome Ω n).comp measurable_snd))

theorem encodeHistory_injective (n : ℕ) : Injective (encodeHistory Ω n) := by
  induction n with
  | zero => exact injective_id
  | succ n ih =>
      intro x y hxy
      have h := (appendHistory n).injective hxy
      exact Prod.ext (ih (congrArg Prod.fst h))
        ((encodeOutcome_injective Ω n) (congrArg Prod.snd h))

theorem measurableEmbedding_encodeHistory [∀ n, StandardBorelSpace (Ω n)] (n : ℕ) :
    MeasurableEmbedding (encodeHistory Ω n) := by
  let := commonHistory_standardBorel Ω n
  let := upgradeStandardBorel (RoundHistory Ω n)
  let := upgradeStandardBorel (History (CommonRecord Ω) n)
  exact (measurable_encodeHistory Ω n).measurableEmbedding (encodeHistory_injective Ω n)

def ValidHistory (n : ℕ) : Set (History (CommonRecord Ω) n) := range (encodeHistory Ω n)

theorem measurableSet_validHistory [∀ n, StandardBorelSpace (Ω n)] (n : ℕ) :
    MeasurableSet (ValidHistory Ω n) :=
  (measurableEmbedding_encodeHistory Ω n).measurableSet_range

def decodeValidHistory [∀ n, StandardBorelSpace (Ω n)] (n : ℕ) :
    ValidHistory Ω n → RoundHistory Ω n :=
  (measurableEmbedding_encodeHistory Ω n).equivRange.symm

theorem measurable_decodeValidHistory [∀ n, StandardBorelSpace (Ω n)] (n : ℕ) :
    Measurable (decodeValidHistory Ω n) :=
  (measurableEmbedding_encodeHistory Ω n).equivRange.symm.measurable

@[simp] theorem decodeValidHistory_encode [∀ n, StandardBorelSpace (Ω n)] (n : ℕ)
    (h : RoundHistory Ω n) :
    decodeValidHistory Ω n ⟨encodeHistory Ω n h, mem_range_self h⟩ = h :=
  (measurableEmbedding_encodeHistory Ω n).equivRange_symm_apply_mk h

theorem encodeHistory_preimage_image (n : ℕ) (s : Set (RoundHistory Ω n)) :
    encodeHistory Ω n ⁻¹' (encodeHistory Ω n '' s) = s :=
  (encodeHistory_injective Ω n).preimage_image s

def encodeTranscript (x : ∀ n, Ω n) : ℕ → CommonRecord Ω :=
  fun n => encodeOutcome Ω n (x n)

theorem measurable_encodeTranscript : Measurable (encodeTranscript Ω) :=
  Measurable.of_eval fun n => (measurable_encodeOutcome Ω n).comp (measurable_pi_apply n)

omit [∀ n, MeasurableSpace (Ω n)] in
theorem encodeTranscript_injective : Injective (encodeTranscript Ω) := by
  intro x y h
  funext n
  exact encodeOutcome_injective Ω n (congrFun h n)

theorem measurableEmbedding_encodeTranscript [∀ n, StandardBorelSpace (Ω n)] :
    MeasurableEmbedding (encodeTranscript Ω) := by
  let := upgradeStandardBorel (∀ n, Ω n)
  let := upgradeStandardBorel (ℕ → CommonRecord Ω)
  exact (measurable_encodeTranscript Ω).measurableEmbedding (encodeTranscript_injective Ω)

def roundPrefix (x : ∀ n, Ω n) : (n : ℕ) → RoundHistory Ω n
  | 0 => PUnit.unit
  | n + 1 => (roundPrefix x n, x n)

def commonPrefix (x : ℕ → CommonRecord Ω) : (n : ℕ) → History (CommonRecord Ω) n
  | 0 => PUnit.unit
  | n + 1 => appendHistory n (commonPrefix x n, x n)

theorem encodeHistory_roundPrefix (x : ∀ n, Ω n) (n : ℕ) :
    encodeHistory Ω n (roundPrefix Ω x n) = commonPrefix Ω (encodeTranscript Ω x) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [roundPrefix, commonPrefix, encodeHistory, encodeTranscript, ih]

theorem transcript_cylinder_preimage (n : ℕ) (s : Set (RoundHistory Ω n)) :
    encodeTranscript Ω ⁻¹' {x | commonPrefix Ω x n ∈ encodeHistory Ω n '' s} =
      {x | roundPrefix Ω x n ∈ s} := by
  ext x
  change commonPrefix Ω (encodeTranscript Ω x) n ∈ encodeHistory Ω n '' s ↔
    roundPrefix Ω x n ∈ s
  rw [← encodeHistory_roundPrefix]
  constructor
  · rintro ⟨h, hh, he⟩
    have hEq := encodeHistory_injective Ω n he
    rwa [← hEq]
  · exact mem_image_of_mem (encodeHistory Ω n)

theorem measurable_roundPrefix (n : ℕ) : Measurable (fun x => roundPrefix Ω x n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.prodMk (measurable_pi_apply n)

theorem measurable_commonPrefix (n : ℕ) : Measurable (fun x => commonPrefix Ω x n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (appendHistory n).measurable.comp (ih.prodMk (measurable_pi_apply n))

section Policy

variable [∀ n, StandardBorelSpace (Ω n)] {Z : Type*} [MeasurableSpace Z]

def liftHistoryFunction (n : ℕ) (f : RoundHistory Ω n → Z) (z : Z)
    (h : History (CommonRecord Ω) n) : Z :=
  if hh : h ∈ ValidHistory Ω n then f (decodeValidHistory Ω n ⟨h,hh⟩) else z

theorem measurable_liftHistoryFunction (n : ℕ) (f : RoundHistory Ω n → Z)
    (hf : Measurable f) (z : Z) : Measurable (liftHistoryFunction Ω n f z) :=
  (hf.comp (measurable_decodeValidHistory Ω n)).dite measurable_const
    (measurableSet_validHistory Ω n)

omit [MeasurableSpace Z] in
@[simp] theorem liftHistoryFunction_encode (n : ℕ) (f : RoundHistory Ω n → Z)
    (z : Z) (h : RoundHistory Ω n) :
    liftHistoryFunction Ω n f z (encodeHistory Ω n h) = f h := by
  simp only [liftHistoryFunction, show encodeHistory Ω n h ∈ ValidHistory Ω n from mem_range_self h,
    ↓reduceDIte, decodeValidHistory_encode]

def ValidTranscript : Set (ℕ → CommonRecord Ω) := range (encodeTranscript Ω)

def decodeValidTranscript : ValidTranscript Ω → (∀ n, Ω n) :=
  (measurableEmbedding_encodeTranscript Ω).equivRange.symm

theorem measurableSet_validTranscript : MeasurableSet (ValidTranscript Ω) :=
  (measurableEmbedding_encodeTranscript Ω).measurableSet_range

theorem measurable_decodeValidTranscript : Measurable (decodeValidTranscript Ω) :=
  (measurableEmbedding_encodeTranscript Ω).equivRange.symm.measurable

@[simp] theorem decodeValidTranscript_encode (x : ∀ n, Ω n) :
    decodeValidTranscript Ω ⟨encodeTranscript Ω x, mem_range_self x⟩ = x :=
  (measurableEmbedding_encodeTranscript Ω).equivRange_symm_apply_mk x

def liftTranscriptFunction (f : (∀ n, Ω n) → Z) (z : Z) (x : ℕ → CommonRecord Ω) : Z :=
  if hx : x ∈ ValidTranscript Ω then f (decodeValidTranscript Ω ⟨x,hx⟩) else z

theorem measurable_liftTranscriptFunction (f : (∀ n, Ω n) → Z)
    (hf : Measurable f) (z : Z) : Measurable (liftTranscriptFunction Ω f z) :=
  (hf.comp (measurable_decodeValidTranscript Ω)).dite measurable_const
    (measurableSet_validTranscript Ω)

omit [MeasurableSpace Z] in
@[simp] theorem liftTranscriptFunction_encode (f : (∀ n, Ω n) → Z) (z : Z)
    (x : ∀ n, Ω n) : liftTranscriptFunction Ω f z (encodeTranscript Ω x) = f x := by
  simp only [liftTranscriptFunction,
    show encodeTranscript Ω x ∈ ValidTranscript Ω from mem_range_self x,
    ↓reduceDIte, decodeValidTranscript_encode]

omit [MeasurableSpace Z] in
theorem transcript_report_event_preimage (f : (∀ n, Ω n) → Z) (z : Z) (s : Set Z) :
    encodeTranscript Ω ⁻¹' (liftTranscriptFunction Ω f z ⁻¹' s) = f ⁻¹' s := by
  ext x
  simp only [mem_preimage, liftTranscriptFunction_encode]

theorem transcript_report_map_measure (μ : Measure (∀ n, Ω n))
    (f : (∀ n, Ω n) → Z) (hf : Measurable f) (z : Z) (s : Set Z) (hs : MeasurableSet s) :
    (μ.map (encodeTranscript Ω)) (liftTranscriptFunction Ω f z ⁻¹' s) = μ (f ⁻¹' s) := by
  rw [Measure.map_apply (measurable_encodeTranscript Ω)
    ((measurable_liftTranscriptFunction Ω f hf z) hs), transcript_report_event_preimage]

end Policy

section AdmissibleBundle

variable [∀ n, StandardBorelSpace (Ω n)] {H : Type*}
  [MeasurableSpace H] [StandardBorelSpace H]

def encodeGraphMap (n : ℕ) (z : H × Ω n) : H × CommonRecord Ω :=
  (z.1, encodeOutcome Ω n z.2)

omit [∀ n, MeasurableSpace (Ω n)] [∀ n, StandardBorelSpace (Ω n)]
  [MeasurableSpace H] [StandardBorelSpace H] in
theorem encodeGraphMap_injective (n : ℕ) : Injective (encodeGraphMap (H := H) Ω n) := by
  intro x y h
  exact Prod.ext (congrArg (fun z : H × CommonRecord Ω => z.1) h)
    (encodeOutcome_injective Ω n (congrArg (fun z : H × CommonRecord Ω => z.2) h))

theorem measurableEmbedding_encodeGraphMap (n : ℕ) :
    MeasurableEmbedding (encodeGraphMap (H := H) Ω n) := by
  let := upgradeStandardBorel (H × Ω n)
  let := upgradeStandardBorel (H × CommonRecord Ω)
  exact (measurable_fst.prodMk ((measurable_encodeOutcome Ω n).comp measurable_snd)).measurableEmbedding
    (encodeGraphMap_injective Ω n)

def encodedAdmissibleGraph (n : ℕ) (G : Set (H × Ω n)) : Set (H × CommonRecord Ω) :=
  encodeGraphMap Ω n '' G

theorem measurableSet_encodedAdmissibleGraph (n : ℕ) (G : Set (H × Ω n))
    (hG : MeasurableSet G) : MeasurableSet (encodedAdmissibleGraph Ω n G) :=
  (measurableEmbedding_encodeGraphMap Ω n).measurableSet_image' hG

omit [∀ n, MeasurableSpace (Ω n)] [∀ n, StandardBorelSpace (Ω n)]
  [MeasurableSpace H] [StandardBorelSpace H] in
theorem encodedAdmissibleGraph_preimage (n : ℕ) (G : Set (H × Ω n)) :
    encodeGraphMap Ω n ⁻¹' encodedAdmissibleGraph Ω n G = G :=
  (encodeGraphMap_injective Ω n).preimage_image G

end AdmissibleBundle

section Instruments

variable {F E H X Y : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Y]

def pushforwardInstrument (P : Instrument F E H X) (e : X → Y) (he : Measurable e) :
    Instrument F E H Y where
  operation h s := P.operation h (e ⁻¹' s)
  empty h := by simpa using P.empty h
  countable_additivity h s hs hd T := by
    have hd' : Pairwise (Disjoint on fun n => e ⁻¹' s n) := by
      intro i j hij
      exact (hd hij).preimage e
    simpa only [preimage_iUnion] using
      P.countable_additivity h (fun n => e ⁻¹' s n) (fun n => he (hs n)) hd' T
  completelyPositive h s hs := P.completelyPositive h _ (he hs)
  measurable_coordinate s hs T x y := P.measurable_coordinate _ (he hs) T x y
  trace_preserving h T := by simpa using P.trace_preserving h T

@[simp] theorem pushforwardInstrument_operation (P : Instrument F E H X)
    (e : X → Y) (he : Measurable e) (h : H) (s : Set Y) :
    (pushforwardInstrument P e he).operation h s = P.operation h (e ⁻¹' s) := rfl

theorem pushforwardInstrument_image (P : Instrument F E H X) (e : X → Y)
    (he : MeasurableEmbedding e) (h : H) (s : Set X) :
    (pushforwardInstrument P e he.measurable).operation h (e '' s) = P.operation h s := by
  simp only [pushforwardInstrument_operation, he.injective.preimage_image]

theorem pushforwardInstrument_off_range (P : Instrument F E H X) (e : X → Y)
    (he : Measurable e) (h : H) (s : Set Y) (hs : Disjoint s (range e)) :
    (pushforwardInstrument P e he).operation h s = 0 := by
  have hp : e ⁻¹' s = ∅ := by
    ext x
    exact ⟨fun hx => (Set.disjoint_left.mp hs hx (mem_range_self x)).elim, False.elim⟩
  simp only [pushforwardInstrument_operation, hp, P.empty]

variable [∀ n, StandardBorelSpace (Ω n)]

omit [∀ n, StandardBorelSpace (Ω n)] in

theorem pushforwardInstrument_admissible_support (n : ℕ)
    (P : Instrument F E H (Ω n)) (G : Set (H × Ω n))
    (hSupport : ∀ h, P.operation h {x | (h,x) ∉ G} = 0) (h : H) :
    (pushforwardInstrument P (encodeOutcome Ω n) (measurable_encodeOutcome Ω n)).operation h
      {r | (h,r) ∉ encodedAdmissibleGraph Ω n G} = 0 := by
  rw [pushforwardInstrument_operation]
  have he : encodeOutcome Ω n ⁻¹' {r | (h,r) ∉ encodedAdmissibleGraph Ω n G} =
      {x | (h,x) ∉ G} := by
    ext x
    have hp := congrArg (fun A => (h,x) ∈ A) (encodedAdmissibleGraph_preimage Ω n G)
    simpa only [mem_preimage, mem_ofPred_eq, encodeGraphMap] using Iff.of_eq (congrArg Not hp)
  rw [he]
  exact hSupport h

private theorem normalCP_id :
    NormalCompletelyPositive (ContinuousLinearMap.id ℂ (Nuclear F)) := by
  intro R _ _ T hT
  simpa only [normalAmplification_apply, ContinuousLinearMap.id_apply,
    nuclearAssembly_nuclearBlock] using hT

private theorem normalCP_zero : NormalCompletelyPositive (0 : NormalOperation F E) := by
  intro R _ _ T _
  simp [normalAmplification_apply, nuclearAssembly]

def dummyInstrument (r : Y) : Instrument F F H Y where
  operation _ s := if r ∈ s then ContinuousLinearMap.id ℂ (Nuclear F) else 0
  empty _ := by simp
  countable_additivity _ s _ hd T := by
    have hApply (A : Set Y) :
        (if r ∈ A then ContinuousLinearMap.id ℂ (Nuclear F) else 0) T =
          if r ∈ A then T else 0 := by
      split_ifs <;> rfl
    simp only [hApply]
    change HasSum (fun n => (if r ∈ s n then T else 0)) (if r ∈ ⋃ n, s n then T else 0)
    by_cases hx : ∃ n, r ∈ s n
    · obtain ⟨k, hk⟩ := hx
      have hu : r ∈ ⋃ n, s n := mem_iUnion.mpr ⟨k, hk⟩
      simp only [ite_eq_left hu]
      have hz (j : ℕ) (hj : j ≠ k) : r ∉ s j := by
        intro hr
        exact Set.disjoint_left.mp (hd hj) hr hk
      simpa only [ite_eq_left hk] using hasSum_single k
        (f := fun n => if r ∈ s n then T else 0) (fun j hj => ite_eq_right (hz j hj))
    · have hz : ∀ n, r ∉ s n := by simpa only [not_exists] using hx
      have hu : r ∉ ⋃ n, s n := by simpa only [mem_iUnion, not_exists] using hx
      simp only [ite_eq_right hu, ite_eq_right (hz _)]
      exact hasSum_zero
  completelyPositive _ s _ := by
    split_ifs
    · exact normalCP_id
    · exact normalCP_zero
  measurable_coordinate _ _ _ _ _ := measurable_const
  trace_preserving _ _ := by simp

variable {K : Type*} [MeasurableSpace K]

omit [∀ n, MeasurableSpace (Ω n)] [∀ n, StandardBorelSpace (Ω n)] in

def liftInstrumentAlongEmbedding (P : Instrument F F H X) (eH : H → K)
    (heH : MeasurableEmbedding eH) (eX : X → Y) (heX : Measurable eX) (r : Y) :
    Instrument F F K Y where
  operation h s := if hh : h ∈ range eH then
      P.operation (heH.equivRange.symm ⟨h,hh⟩) (eX ⁻¹' s)
    else (dummyInstrument (F := F) (H := Unit) r).operation () s
  empty h := by
    split_ifs <;> simp [P.empty, dummyInstrument]
  countable_additivity h s hs hd T := by
    split_ifs with hh
    · exact (pushforwardInstrument P eX heX).countable_additivity
        (heH.equivRange.symm ⟨h,hh⟩) s hs hd T
    · exact (dummyInstrument (F := F) (H := Unit) r).countable_additivity () s hs hd T
  completelyPositive h s hs := by
    split_ifs
    · exact P.completelyPositive _ _ (heX hs)
    · exact (dummyInstrument (F := F) (H := Unit) r).completelyPositive () s hs
  measurable_coordinate s hs T x y := by
    have hm : Measurable (fun h : range eH =>
        inner ℂ x (QuantumProver.NuclearOperator.toOperator
          (P.operation (heH.equivRange.symm h) (eX ⁻¹' s) T) y)) :=
      (P.measurable_coordinate _ (heX hs) T x y).comp heH.equivRange.symm.measurable
    have hm' : Measurable (fun _ : {h : K // h ∉ range eH} =>
        inner ℂ x (QuantumProver.NuclearOperator.toOperator
          ((dummyInstrument (F := F) (H := Unit) r).operation () s T) y)) := measurable_const
    convert hm.dite hm' heH.measurableSet_range using 1
    funext h
    split_ifs <;> rfl
  trace_preserving h T := by
    split_ifs
    · simpa using P.trace_preserving _ T
    · exact (dummyInstrument (F := F) (H := Unit) r).trace_preserving () T

omit [∀ n, MeasurableSpace (Ω n)] [∀ n, StandardBorelSpace (Ω n)] in
theorem liftInstrumentAlongEmbedding_encoded (P : Instrument F F H X) (eH : H → K)
    (heH : MeasurableEmbedding eH) (eX : X → Y) (heX : Measurable eX) (r : Y)
    (h : H) (s : Set Y) :
    (liftInstrumentAlongEmbedding P eH heH eX heX r).operation (eH h) s =
      P.operation h (eX ⁻¹' s) := by
  simp only [liftInstrumentAlongEmbedding, mem_range_self, ↓reduceDIte,
    heH.equivRange_symm_apply_mk]

theorem measurableEmbedding_encodeAdmissibleHistory (n : ℕ)
    (S : Set (RoundHistory Ω n)) (hS : MeasurableSet S) :
    MeasurableEmbedding (fun h : S => encodeHistory Ω n h.val) :=
  (measurableEmbedding_encodeHistory Ω n).comp (MeasurableEmbedding.subtype_coe hS)

def liftAdmissibleTurnInstrument (n : ℕ) (S : Set (RoundHistory Ω n))
    (hS : MeasurableSet S) (P : Instrument F F S (Ω n)) :
    Instrument F F (History (CommonRecord Ω) n) (CommonRecord Ω) :=
  liftInstrumentAlongEmbedding P (fun h : S => encodeHistory Ω n h.val)
    (measurableEmbedding_encodeAdmissibleHistory Ω n S hS)
    (encodeOutcome Ω n) (measurable_encodeOutcome Ω n) (dummyRecord Ω)

theorem liftAdmissibleTurnInstrument_physical_event (n : ℕ) (S : Set (RoundHistory Ω n))
    (hS : MeasurableSet S) (P : Instrument F F S (Ω n)) (h : S) (s : Set (Ω n)) :
    (liftAdmissibleTurnInstrument Ω n S hS P).operation (encodeHistory Ω n h.val)
      (encodeOutcome Ω n '' s) = P.operation h s := by
  rw [liftAdmissibleTurnInstrument, liftInstrumentAlongEmbedding_encoded,
    encodeOutcome_preimage_image]

def liftTurnInstrument (n : ℕ) (P : Instrument F F (RoundHistory Ω n) (Ω n)) :
    Instrument F F (History (CommonRecord Ω) n) (CommonRecord Ω) where
  operation h s := if hh : h ∈ ValidHistory Ω n then
      P.operation (decodeValidHistory Ω n ⟨h, hh⟩) (encodeOutcome Ω n ⁻¹' s)
    else (dummyInstrument (F := F) (H := Unit) (dummyRecord Ω)).operation () s
  empty h := by
    split_ifs <;> simp [P.empty, dummyInstrument]
  countable_additivity h s hs hd T := by
    split_ifs with hh
    · exact (pushforwardInstrument P (encodeOutcome Ω n) (measurable_encodeOutcome Ω n)).countable_additivity
        (decodeValidHistory Ω n ⟨h, hh⟩) s hs hd T
    · exact (dummyInstrument (F := F) (H := Unit) (dummyRecord Ω)).countable_additivity () s hs hd T
  completelyPositive h s hs := by
    split_ifs with hh
    · exact P.completelyPositive _ _ ((measurable_encodeOutcome Ω n) hs)
    · exact (dummyInstrument (F := F) (H := Unit) (dummyRecord Ω)).completelyPositive () s hs
  measurable_coordinate s hs T x y := by
    have hm : Measurable (fun h : ValidHistory Ω n =>
        inner ℂ x (QuantumProver.NuclearOperator.toOperator
          (P.operation (decodeValidHistory Ω n h) (encodeOutcome Ω n ⁻¹' s) T) y)) :=
      (P.measurable_coordinate _ ((measurable_encodeOutcome Ω n) hs) T x y).comp
        (measurable_decodeValidHistory Ω n)
    have hm' : Measurable (fun _ : {h : History (CommonRecord Ω) n // h ∉ ValidHistory Ω n} =>
        inner ℂ x (QuantumProver.NuclearOperator.toOperator
          ((dummyInstrument (F := F) (H := Unit) (dummyRecord Ω)).operation () s T) y)) :=
      measurable_const
    convert hm.dite hm' (measurableSet_validHistory Ω n) using 1
    funext h
    split_ifs <;> rfl
  trace_preserving h T := by
    split_ifs
    · simpa using P.trace_preserving _ T
    · exact (dummyInstrument (F := F) (H := Unit) (dummyRecord Ω)).trace_preserving () T

@[simp] theorem liftTurnInstrument_encoded (n : ℕ)
    (P : Instrument F F (RoundHistory Ω n) (Ω n)) (h : RoundHistory Ω n)
    (s : Set (CommonRecord Ω)) :
    (liftTurnInstrument Ω n P).operation (encodeHistory Ω n h) s =
      P.operation h (encodeOutcome Ω n ⁻¹' s) := by
  simp only [liftTurnInstrument, show encodeHistory Ω n h ∈ ValidHistory Ω n from mem_range_self h,
    ↓reduceDIte, decodeValidHistory_encode]

theorem liftTurnInstrument_physical_event (n : ℕ)
    (P : Instrument F F (RoundHistory Ω n) (Ω n)) (h : RoundHistory Ω n) (s : Set (Ω n)) :
    (liftTurnInstrument Ω n P).operation (encodeHistory Ω n h) (encodeOutcome Ω n '' s) =
      P.operation h s := by
  rw [liftTurnInstrument_encoded, encodeOutcome_preimage_image]

theorem liftTurnInstrument_wrong_time {n m : ℕ} (hnm : n ≠ m)
    (P : Instrument F F (RoundHistory Ω n) (Ω n)) (h : RoundHistory Ω n) (s : Set (Ω m)) :
    (liftTurnInstrument Ω n P).operation (encodeHistory Ω n h) (encodeOutcome Ω m '' s) = 0 := by
  rw [liftTurnInstrument_encoded, encodeOutcome_preimage_wrong_tag Ω hnm, P.empty]

theorem liftTurnInstrument_dummy_zero (n : ℕ)
    (P : Instrument F F (RoundHistory Ω n) (Ω n)) (h : RoundHistory Ω n) :
    (liftTurnInstrument Ω n P).operation (encodeHistory Ω n h) {dummyRecord Ω} = 0 := by
  rw [liftTurnInstrument_encoded, encodeOutcome_preimage_dummy, P.empty]

theorem liftTurnInstrument_invalid (n : ℕ)
    (P : Instrument F F (RoundHistory Ω n) (Ω n)) (h : History (CommonRecord Ω) n)
    (hh : h ∉ ValidHistory Ω n) (s : Set (CommonRecord Ω)) :
    (liftTurnInstrument Ω n P).operation h s =
      if dummyRecord Ω ∈ s then ContinuousLinearMap.id ℂ (Nuclear F) else 0 := by
  simp only [liftTurnInstrument, hh, ↓reduceDIte, dummyInstrument]

end Instruments
end QuantumProver.ElegantJointMeasurement.HilbertRecordCoding
