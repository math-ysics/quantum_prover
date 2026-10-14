import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalSandwich
import QuantumProver.InformationTheory.ElegantJointMeasurement.MeasurableNormalInstrument

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory Set Filter Function InnerProductSpace
open scoped BigOperators Topology ComplexOrder Classical

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.NuclearOperator (toOperator toOperator_injective)
open QuantumProver.HilbertNuclearCompression

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def preparedState (φ : E) : Nuclear E :=
  QuantumProver.NuclearOperator.rankOne (innerSL ℂ φ) φ

@[simp] theorem toOperator_preparedState (φ : E) :
    toOperator (preparedState φ) = InnerProductSpace.rankOne ℂ φ φ := by
  rw [preparedState, QuantumProver.NuclearOperator.toOperator_rankOne]
  rfl

@[simp] theorem trace_preparedState (φ : E) :
    QuantumProver.HilbertNuclearTrace.trace (preparedState φ) = (‖φ‖ ^ 2 : ℝ) := by
  simp [preparedState, inner_self_eq_norm_sq_to_K]

def tracePrepare (φ : E) : NormalOperation F E :=
  (QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := F)).smulRight (preparedState φ)

@[simp] theorem tracePrepare_apply (φ : E) (T : Nuclear F) :
    tracePrepare φ T = QuantumProver.HilbertNuclearTrace.trace T • preparedState φ := rfl

@[simp] theorem trace_tracePrepare (φ : E) (T : Nuclear F) :
    QuantumProver.HilbertNuclearTrace.trace (tracePrepare φ T) =
      QuantumProver.HilbertNuclearTrace.trace T * (‖φ‖ ^ 2 : ℝ) := by
  simp only [tracePrepare_apply, map_smul, trace_preparedState, smul_eq_mul]

theorem tracePrepare_trace_preserving (φ : E) (hφ : ‖φ‖ = 1) (T : Nuclear F) :
    QuantumProver.HilbertNuclearTrace.trace (tracePrepare φ T) =
      QuantumProver.HilbertNuclearTrace.trace T := by
  simp [hφ]

variable {R : Type} [Fintype R] [DecidableEq R]

def scalarPrepare (φ : E) : (R → R → ℂ) →L[ℂ] Nuclear (BlockSpace R E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => nuclearAssembly (fun i j => a i j • preparedState φ)
      map_add' := by
        intro a b
        simp [nuclearAssembly, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp [nuclearAssembly, smul_smul, Finset.smul_sum] }

@[simp] theorem scalarPrepare_apply (φ : E) (a : R → R → ℂ) :
    scalarPrepare φ a = nuclearAssembly (fun i j => a i j • preparedState φ) := rfl

theorem scalarPrepare_trace_eq_amplification (φ : E) (T : Nuclear (BlockSpace R F)) :
    scalarPrepare φ (fun i j => QuantumProver.HilbertNuclearTrace.trace (nuclearBlock i j T)) =
      normalAmplification (tracePrepare φ) T := by
  simp only [scalarPrepare_apply, normalAmplification_apply, tracePrepare_apply]

theorem rankOne_sandwich (φ : E) (v : F) (T : Nuclear F) :
    sandwich (InnerProductSpace.rankOne ℂ φ v) T =
      inner ℂ v (toOperator T v) • preparedState φ := by
  apply toOperator_injective
  simp only [toOperator_sandwich, adjoint_rankOne, map_smul, toOperator_preparedState]
  ext x
  simp only [ContinuousLinearMap.comp_apply, rankOne_apply, smul_apply,
    map_smul, smul_smul]
  congr 1
  ring

theorem scalarPrepare_diagonal_eq_amplified_sandwich (φ : E) (v : F)
    (T : Nuclear (BlockSpace R F)) :
    scalarPrepare φ (fun i j => inner ℂ v (toOperator (nuclearBlock i j T) v)) =
      normalAmplification (sandwich (InnerProductSpace.rankOne ℂ φ v)) T := by
  simp only [scalarPrepare_apply, normalAmplification_apply, rankOne_sandwich]

theorem tracePrepare_amplification_hasSum {L : Type*} (b : HilbertBasis L ℂ F)
    (φ : E) (T : Nuclear (BlockSpace R F)) :
    HasSum (fun l => normalAmplification
      (sandwich (InnerProductSpace.rankOne ℂ φ (b l))) T)
      (normalAmplification (tracePrepare φ) T) := by
  have hs : HasSum (fun l => fun i j => inner ℂ (b l)
      (toOperator (nuclearBlock i j T) (b l)))
      (fun i j => QuantumProver.HilbertNuclearTrace.trace (nuclearBlock i j T)) := by
    change Tendsto (fun s : Finset L => ∑ l ∈ s, fun i j => inner ℂ (b l)
      (toOperator (nuclearBlock i j T) (b l))) (SummationFilter.unconditional L).filter
      (nhds (fun i j => QuantumProver.HilbertNuclearTrace.trace (nuclearBlock i j T)))
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [HasSum, Finset.sum_apply] using
      QuantumProver.HilbertNuclearTrace.hasSum_diagonal b (nuclearBlock i j T)
  simpa only [scalarPrepare_trace_eq_amplification,
    scalarPrepare_diagonal_eq_amplified_sandwich] using hs.mapL (scalarPrepare φ)

theorem normalCompletelyPositive_tracePrepare (φ : E) :
    NormalCompletelyPositive (tracePrepare (F := F) φ) := by
  intro R _ _ T hT
  obtain ⟨L, b, hb⟩ := exists_hilbertBasis ℂ F
  have hs := (tracePrepare_amplification_hasSum b φ T).mapL
    (QuantumProver.NuclearOperator.toOperator (𝕜 := ℂ) (E := BlockSpace R E) (F := BlockSpace R E))
  apply ContinuousLinearMap.nonneg_iff_isPositive.mp
  apply isClosed_Ici.mem_of_tendsto hs
  filter_upwards [] with s
  exact Finset.sum_nonneg (fun l hl =>
    ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (normalCompletelyPositive_sandwich (InnerProductSpace.rankOne ℂ φ (b l)) R T hT))

theorem normalAmplification_add (Φ Ψ : NormalOperation F E)
    (T : Nuclear (BlockSpace R F)) :
    normalAmplification (Φ + Ψ) T = normalAmplification Φ T + normalAmplification Ψ T := by
  simp [normalAmplification_apply, nuclearAssembly, Finset.sum_add_distrib]

theorem normalCompletelyPositive_add (Φ Ψ : NormalOperation F E)
    (hΦ : NormalCompletelyPositive Φ) (hΨ : NormalCompletelyPositive Ψ) :
    NormalCompletelyPositive (Φ + Ψ) := by
  intro R _ _ T hT
  rw [normalAmplification_add, map_add]
  exact (hΦ R T hT).add (hΨ R T hT)

theorem normalCompletelyPositive_zero :
    NormalCompletelyPositive (0 : NormalOperation F E) := by
  intro R _ _ T hT
  simpa [normalAmplification_apply, nuclearAssembly] using
    (ContinuousLinearMap.isPositive_zero (𝕜 := ℂ) (E := BlockSpace R E))

def complement (P : F →L[ℂ] F) : F →L[ℂ] F := ContinuousLinearMap.id ℂ F - P

theorem complement_adjoint (P : F →L[ℂ] F) (hPa : P.adjoint = P) :
    (complement P).adjoint = complement P := by
  simp [complement, hPa, ContinuousLinearMap.adjoint_id]

theorem complement_gram (P : F →L[ℂ] F) (hPa : P.adjoint = P)
    (hPi : P ∘L P = P) :
    (complement P).adjoint ∘L complement P = ContinuousLinearMap.id ℂ F - P := by
  rw [complement_adjoint P hPa]
  have hp (x : F) : P (P x) = P x := congrArg (fun A : F →L[ℂ] F => A x) hPi
  ext x
  simp only [complement, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub, hp]
  abel

theorem trace_complement_sandwich (P : F →L[ℂ] F) (hPa : P.adjoint = P)
    (hPi : P ∘L P = P) (T : Nuclear F) :
    QuantumProver.HilbertNuclearTrace.trace (sandwich (complement P) T) =
      QuantumProver.HilbertNuclearTrace.trace T - QuantumProver.HilbertNuclearTrace.trace (sandwich P T) := by
  have hc : compose (ContinuousLinearMap.id ℂ F) (ContinuousLinearMap.id ℂ F - P) T =
      T - compose (ContinuousLinearMap.id ℂ F) P T := by
    apply toOperator_injective
    simp only [toOperator_compose, map_sub]
    ext x
    simp
  have hp : P.adjoint ∘L P = P := by rw [hPa, hPi]
  have ht : QuantumProver.HilbertNuclearTrace.trace (sandwich P T) =
      QuantumProver.HilbertNuclearTrace.trace (compose (ContinuousLinearMap.id ℂ F) P T) := by
    rw [sandwich, QuantumProver.ElegantJointMeasurement.NormalCPInstruments.trace_compose_cycle, hp]
  calc
    QuantumProver.HilbertNuclearTrace.trace (sandwich (complement P) T) =
        QuantumProver.HilbertNuclearTrace.trace
          (compose (ContinuousLinearMap.id ℂ F) (ContinuousLinearMap.id ℂ F - P) T) := by
      rw [sandwich, QuantumProver.ElegantJointMeasurement.NormalCPInstruments.trace_compose_cycle,
        complement_gram P hPa hPi]
    _ = QuantumProver.HilbertNuclearTrace.trace T -
        QuantumProver.HilbertNuclearTrace.trace (sandwich P T) := by rw [hc, map_sub, ht]

def complementReset (φ : E) (P : F →L[ℂ] F) : NormalOperation F E :=
  (tracePrepare φ).comp (sandwich (complement P))

theorem normalCompletelyPositive_complementReset (φ : E) (P : F →L[ℂ] F) :
    NormalCompletelyPositive (complementReset φ P) :=
  normalCompletelyPositive_comp _ _ (normalCompletelyPositive_tracePrepare φ)
    (normalCompletelyPositive_sandwich (complement P))

theorem complementReset_apply (φ : E) (P : F →L[ℂ] F)
    (hPa : P.adjoint = P) (hPi : P ∘L P = P) (T : Nuclear F) :
    complementReset φ P T =
      (QuantumProver.HilbertNuclearTrace.trace T - QuantumProver.HilbertNuclearTrace.trace (sandwich P T)) •
        preparedState φ := by
  simp only [complementReset, ContinuousLinearMap.comp_apply, tracePrepare_apply,
    trace_complement_sandwich P hPa hPi]

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

structure RangeInstrument (F E H Ω : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [MeasurableSpace H] [MeasurableSpace Ω] where
  inputProjection : H → F →L[ℂ] F
  projection_adjoint : ∀ h, (inputProjection h).adjoint = inputProjection h
  projection_idempotent : ∀ h, inputProjection h ∘L inputProjection h = inputProjection h
  operation : H → Set Ω → NormalOperation F E
  empty : ∀ h, operation h ∅ = 0
  countable_additivity : ∀ h (s : ℕ → Set Ω), (∀ n, MeasurableSet (s n)) →
    Pairwise (Disjoint on s) → ∀ T : Nuclear F,
      HasSum (fun n => operation h (s n) T) (operation h (⋃ n, s n) T)
  completelyPositive : ∀ h s, MeasurableSet s → NormalCompletelyPositive (operation h s)
  measurable_coordinate : ∀ s, MeasurableSet s → ∀ (T : Nuclear F) (x y : E),
    Measurable (fun h => inner ℂ x (toOperator (operation h s T) y))
  trace_on_range : ∀ h T,
    QuantumProver.HilbertNuclearTrace.trace (operation h univ T) =
      QuantumProver.HilbertNuclearTrace.trace (sandwich (inputProjection h) T)

theorem dummy_hasSum {A O : Type*} [NormedAddCommGroup A]
    (o : O) (s : ℕ → Set O) (hd : Pairwise (Disjoint on s)) (a : A) :
    HasSum (fun n => if o ∈ s n then a else 0) (if o ∈ ⋃ n, s n then a else 0) := by
  classical
  by_cases ho : ∃ n, o ∈ s n
  · obtain ⟨n, hn⟩ := ho
    have hu : o ∈ ⋃ n, s n := mem_iUnion.mpr ⟨n, hn⟩
    have he : (fun m => if o ∈ s m then a else 0) =
        (fun m => if m = n then a else 0) := by
      funext m
      by_cases hm : m = n
      · subst m; simp [hn]
      · have hnot : o ∉ s m := by
          intro hom
          exact Set.disjoint_left.mp (hd hm) hom hn
        simp [hm, hnot]
    rw [he, if_pos hu]
    exact hasSum_ite_eq n a
  · have hn (n : ℕ) : o ∉ s n := fun h => ho ⟨n, h⟩
    have hu : o ∉ ⋃ n, s n := by simpa only [mem_iUnion] using ho
    simpa only [if_neg (hn _), if_neg hu] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : A)) 0)

namespace RangeInstrument

variable (P : RangeInstrument F E H Ω)

def completedOperation (φ : E) (h : H) (s : Set (Ω ⊕ Unit)) : NormalOperation F E :=
  P.operation h (Sum.inl ⁻¹' s) +
    if Sum.inr () ∈ s then complementReset φ (P.inputProjection h) else 0

theorem completedOperation_apply (φ : E) (h : H) (s : Set (Ω ⊕ Unit)) (T : Nuclear F) :
    P.completedOperation φ h s T = P.operation h (Sum.inl ⁻¹' s) T +
      if Sum.inr () ∈ s then complementReset φ (P.inputProjection h) T else 0 := by
  by_cases hd : (Sum.inr () : Ω ⊕ Unit) ∈ s <;> simp [completedOperation, hd]

@[simp] theorem completedOperation_empty (φ : E) (h : H) :
    P.completedOperation φ h ∅ = 0 := by
  simp [completedOperation, P.empty]

theorem completedOperation_countable_additivity (φ : E) (h : H)
    (s : ℕ → Set (Ω ⊕ Unit)) (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Disjoint on s)) (T : Nuclear F) :
    HasSum (fun n => P.completedOperation φ h (s n) T)
      (P.completedOperation φ h (⋃ n, s n) T) := by
  have hp := P.countable_additivity h (fun n => Sum.inl ⁻¹' s n)
    (fun n => measurable_inl (hs n)) (fun i j hij => (hd hij).preimage Sum.inl) T
  have hdummy := dummy_hasSum (Sum.inr () : Ω ⊕ Unit) s hd
    (complementReset φ (P.inputProjection h) T)
  simpa only [completedOperation_apply, Set.preimage_iUnion] using hp.add hdummy

theorem completedOperation_completelyPositive (φ : E) (h : H)
    (s : Set (Ω ⊕ Unit)) (hs : MeasurableSet s) :
    NormalCompletelyPositive (P.completedOperation φ h s) := by
  apply normalCompletelyPositive_add
  · exact P.completelyPositive h _ (measurable_inl hs)
  · split_ifs
    · exact normalCompletelyPositive_complementReset φ _
    · exact normalCompletelyPositive_zero

theorem completedOperation_trace_preserving (φ : E) (hφ : ‖φ‖ = 1)
    (h : H) (T : Nuclear F) :
    QuantumProver.HilbertNuclearTrace.trace (P.completedOperation φ h univ T) =
      QuantumProver.HilbertNuclearTrace.trace T := by
  simp only [completedOperation, preimage_univ, mem_univ, if_true,
    ContinuousLinearMap.add_apply, map_add, complementReset, ContinuousLinearMap.comp_apply]
  rw [tracePrepare_trace_preserving φ hφ, trace_complement_sandwich _
    (P.projection_adjoint h) (P.projection_idempotent h), P.trace_on_range]
  abel

local instance nuclearMeasurableE : MeasurableSpace (Nuclear E) := borel (Nuclear E)
local instance nuclearBorelE : BorelSpace (Nuclear E) := ⟨rfl⟩

theorem measurable_range_trace [TopologicalSpace.SeparableSpace E] (T : Nuclear F) :
    Measurable (fun h => QuantumProver.HilbertNuclearTrace.trace
      (sandwich (P.inputProjection h) T)) := by
  have hm := stronglyMeasurable_of_weak_coordinates
    (fun h => P.operation h univ T) (P.measurable_coordinate univ MeasurableSet.univ T)
  have ht := (QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := E)).continuous.comp_stronglyMeasurable hm
  simpa only [P.trace_on_range] using ht.measurable

theorem completedOperation_measurable_coordinate [TopologicalSpace.SeparableSpace E]
    (φ : E) (s : Set (Ω ⊕ Unit)) (hs : MeasurableSet s) (T : Nuclear F) (x y : E) :
    Measurable (fun h => inner ℂ x (toOperator (P.completedOperation φ h s T) y)) := by
  have hp := P.measurable_coordinate (Sum.inl ⁻¹' s) (measurable_inl hs) T x y
  by_cases hd : (Sum.inr () : Ω ⊕ Unit) ∈ s
  · have hc : Measurable (fun h => QuantumProver.HilbertNuclearTrace.trace T -
        QuantumProver.HilbertNuclearTrace.trace (sandwich (P.inputProjection h) T)) :=
      measurable_const.sub (P.measurable_range_trace T)
    have hr := hc.mul_const (inner ℂ x (toOperator (preparedState φ) y))
    have he : (fun h => inner ℂ x (toOperator (P.completedOperation φ h s T) y)) =
        (fun h => inner ℂ x (toOperator (P.operation h (Sum.inl ⁻¹' s) T) y)) +
        (fun h => (QuantumProver.HilbertNuclearTrace.trace T -
          QuantumProver.HilbertNuclearTrace.trace (sandwich (P.inputProjection h) T)) *
          inner ℂ x (toOperator (preparedState φ) y)) := by
      funext h
      change inner ℂ x (toOperator (P.completedOperation φ h s T) y) =
        inner ℂ x (toOperator (P.operation h (Sum.inl ⁻¹' s) T) y) +
          (QuantumProver.HilbertNuclearTrace.trace T -
            QuantumProver.HilbertNuclearTrace.trace (sandwich (P.inputProjection h) T)) *
          inner ℂ x (toOperator (preparedState φ) y)
      simp only [completedOperation_apply, if_pos hd, map_add, add_apply, inner_add_right,
        complementReset_apply φ _ (P.projection_adjoint _) (P.projection_idempotent _),
        map_smul, smul_apply, inner_smul_right]
    rw [he]
    exact hp.add hr
  · simpa [completedOperation, hd] using hp

def complete [TopologicalSpace.SeparableSpace E] (φ : E) (hφ : ‖φ‖ = 1) :
    Instrument F E H (Ω ⊕ Unit) where
  operation := P.completedOperation φ
  empty := P.completedOperation_empty φ
  countable_additivity := P.completedOperation_countable_additivity φ
  completelyPositive := P.completedOperation_completelyPositive φ
  measurable_coordinate := P.completedOperation_measurable_coordinate φ
  trace_preserving := P.completedOperation_trace_preserving φ hφ

@[simp] theorem complete_operation [TopologicalSpace.SeparableSpace E]
    (φ : E) (hφ : ‖φ‖ = 1) (h : H) (s : Set (Ω ⊕ Unit)) (T : Nuclear F) :
    (P.complete φ hφ).operation h s T = P.completedOperation φ h s T := rfl

@[simp] theorem completedOperation_dummy (φ : E) (h : H) (T : Nuclear F) :
    P.completedOperation φ h {Sum.inr ()} T =
      complementReset φ (P.inputProjection h) T := by
  have he : Sum.inl ⁻¹' ({Sum.inr ()} : Set (Ω ⊕ Unit)) = ∅ := by ext x; simp
  simp [completedOperation, he, P.empty]

theorem completedOperation_physical_event (φ : E) (h : H) (s : Set Ω) (T : Nuclear F) :
    P.completedOperation φ h (Sum.inl '' s) T = P.operation h s T := by
  simp [completedOperation, Set.preimage_image_eq _ Sum.inl_injective]

end RangeInstrument

variable {G : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem complementReset_supported_input (φ : E) (P : F →L[ℂ] F)
    (V : G →L[ℂ] F) (hPV : P ∘L V = V) (T : Nuclear G) :
    complementReset φ P (sandwich V T) = 0 := by
  have hQV : complement P ∘L V = 0 := by
    ext x
    have hx := congrArg (fun A : G →L[ℂ] F => A x) hPV
    simp only [ContinuousLinearMap.comp_apply] at hx
    simp [complement, hx]
  have hz : sandwich (complement P) (sandwich V T) = 0 := by
    apply toOperator_injective
    simp only [toOperator_sandwich, map_zero]
    ext x
    have hvzero (z : G) : complement P (V z) = 0 :=
      congrArg (fun A : G →L[ℂ] F => A z) hQV
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
    exact hvzero _
  simp [complementReset, hz]

theorem RangeInstrument.completedOperation_supported_input
    (P : RangeInstrument F E H Ω) (φ : E) (h : H) (s : Set (Ω ⊕ Unit))
    (V : G →L[ℂ] F) (hPV : P.inputProjection h ∘L V = V) (T : Nuclear G) :
    P.completedOperation φ h s (sandwich V T) =
      P.operation h (Sum.inl ⁻¹' s) (sandwich V T) := by
  rw [RangeInstrument.completedOperation_apply]
  by_cases hd : (Sum.inr () : Ω ⊕ Unit) ∈ s
  · simp only [if_pos hd, complementReset_supported_input φ _ V hPV T, add_zero]
  · simp only [if_neg hd, add_zero]

end QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion

namespace QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion

open QuantumProver.ElegantJointMeasurement.MeasurableHilbertField QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument
open QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.NuclearOperator (toOperator)

universe u v w
variable {Z : Type u} [MeasurableSpace Z] {E : Z → Type v} {G : Z → Type w}
  [∀ z, NormedAddCommGroup (E z)] [∀ z, InnerProductSpace ℂ (E z)]
  [∀ z, CompleteSpace (E z)]
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]
  {Ω : Type*} [MeasurableSpace Ω]

local instance commonSeparable : TopologicalSpace.SeparableSpace CommonHilbert := by
  have hs : TopologicalSpace.IsSeparable
      (closure (Submodule.span ℂ (Set.range commonBasis) : Set CommonHilbert)) :=
    ((Set.countable_range commonBasis).isSeparable.span (R := ℂ)).closure
  have hc : closure (Submodule.span ℂ (Set.range commonBasis) : Set CommonHilbert) = univ := by
    rw [← Submodule.topologicalClosure_coe, commonBasis.dense_span, Submodule.top_coe]
  exact TopologicalSpace.isSeparable_univ_iff.mp (hc ▸ hs)

def matrixRangeInstrument {F : FundamentalFamily E} {H : FundamentalFamily G}
    (P : MatrixInstrument F H Ω) : RangeInstrument CommonHilbert CommonHilbert Z Ω where
  inputProjection := F.rangeProjection
  projection_adjoint := inputProjection_adjoint F
  projection_idempotent := inputProjection_idempotent F
  operation := P.codedOperation
  empty := P.codedOperation_empty
  countable_additivity := P.codedOperation_countable_additivity
  completelyPositive := P.codedOperation_completelyPositive
  measurable_coordinate s hs U x y := by
    let L : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear CommonHilbert →L[ℂ] ℂ :=
      (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ CommonHilbert y).comp toOperator)
    exact (L.continuous.comp_stronglyMeasurable (P.stronglyMeasurable_codedOperation s hs U)).measurable
  trace_on_range z U := by
    simpa only [sandwich, inputProjection_adjoint F z] using P.codedOperation_total_trace z U

def commonResetVector : CommonHilbert := commonBasis 0

theorem norm_commonResetVector : ‖commonResetVector‖ = 1 := commonBasis.orthonormal.1 0

def completeMatrixInstrument {F : FundamentalFamily E} {H : FundamentalFamily G}
    (P : MatrixInstrument F H Ω) :
    QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument CommonHilbert CommonHilbert Z (Ω ⊕ Unit) :=
  (matrixRangeInstrument P).complete commonResetVector norm_commonResetVector

theorem completeMatrixInstrument_physical_event {F : FundamentalFamily E}
    {H : FundamentalFamily G} (P : MatrixInstrument F H Ω) (z : Z) (s : Set Ω)
    (T : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (E z)) :
    (completeMatrixInstrument P).operation z (Sum.inl '' s) (padNuclear (F.embedding z) T) =
      padNuclear (H.embedding z) (P.operation z s T) := by
  rw [completeMatrixInstrument, RangeInstrument.complete_operation,
    RangeInstrument.completedOperation_physical_event]
  simp only [matrixRangeInstrument, MatrixInstrument.codedOperation, encodedOperation,
    ContinuousLinearMap.comp_apply, recover_padNuclear]

theorem completeMatrixInstrument_recover_physical {F : FundamentalFamily E}
    {H : FundamentalFamily G} (P : MatrixInstrument F H Ω) (z : Z) (s : Set Ω)
    (T : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (E z)) :
    recoverNuclear (H.embedding z)
      ((completeMatrixInstrument P).operation z (Sum.inl '' s) (padNuclear (F.embedding z) T)) =
      P.operation z s T := by
  rw [completeMatrixInstrument_physical_event, recover_padNuclear]

theorem completeMatrixInstrument_dummy_on_physical {F : FundamentalFamily E}
    {H : FundamentalFamily G} (P : MatrixInstrument F H Ω) (z : Z)
    (T : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (E z)) :
    (completeMatrixInstrument P).operation z {Sum.inr ()} (padNuclear (F.embedding z) T) = 0 := by
  rw [completeMatrixInstrument, RangeInstrument.complete_operation,
    RangeInstrument.completedOperation_dummy]
  have hPV : F.rangeProjection z ∘L (F.embedding z).toContinuousLinearMap =
      (F.embedding z).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    exact QuantumProver.CountableFrameProjection.rangeProjection_embedding (F.vector z) (F.dense z) x
  exact complementReset_supported_input commonResetVector (F.rangeProjection z)
    (F.embedding z).toContinuousLinearMap hPV T

theorem completeMatrixInstrument_all_events_on_physical {F : FundamentalFamily E}
    {H : FundamentalFamily G} (P : MatrixInstrument F H Ω) (z : Z) (s : Set (Ω ⊕ Unit))
    (T : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (E z)) :
    (completeMatrixInstrument P).operation z s (padNuclear (F.embedding z) T) =
      padNuclear (H.embedding z) (P.operation z (Sum.inl ⁻¹' s) T) := by
  have hPV : F.rangeProjection z ∘L (F.embedding z).toContinuousLinearMap =
      (F.embedding z).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro x
    exact QuantumProver.CountableFrameProjection.rangeProjection_embedding (F.vector z) (F.dense z) x
  rw [completeMatrixInstrument, RangeInstrument.complete_operation]
  change (matrixRangeInstrument P).completedOperation commonResetVector z s
    (sandwich (F.embedding z).toContinuousLinearMap T) = _
  rw [RangeInstrument.completedOperation_supported_input (matrixRangeInstrument P)
    commonResetVector z s (F.embedding z).toContinuousLinearMap hPV T]
  change P.codedOperation z (Sum.inl ⁻¹' s) (padNuclear (F.embedding z) T) = _
  simp only [matrixRangeInstrument, MatrixInstrument.codedOperation, encodedOperation,
    ContinuousLinearMap.comp_apply, recover_padNuclear]

end QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion
