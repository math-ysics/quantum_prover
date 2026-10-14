import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentCompletion
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCompleteContraction
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalRecordedAbsorption
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalRecordedConvergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Filter Function InnerProductSpace
open scoped BigOperators Topology Classical

namespace QuantumProver.MatrixNormalSourceCompletion

open QuantumProver.ElegantJointMeasurement.MeasurableHilbertField QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.NuclearOperator (toOperator)

abbrev Nuc (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] := QuantumProver.NuclearOperator.Nuclear ℂ V V

instance commonSeparable : TopologicalSpace.SeparableSpace CommonHilbert := by
  have hs : TopologicalSpace.IsSeparable
      (closure (Submodule.span ℂ (Set.range commonBasis) : Set CommonHilbert)) :=
    ((Set.countable_range commonBasis).isSeparable.span (R := ℂ)).closure
  have hc : closure (Submodule.span ℂ (Set.range commonBasis) : Set CommonHilbert) = univ := by
    rw [← Submodule.topologicalClosure_coe, commonBasis.dense_span, Submodule.top_coe]
  exact TopologicalSpace.isSeparable_univ_iff.mp (hc ▸ hs)

universe u v w
variable {H : Type u} [MeasurableSpace H]

def commonFundamentalFamily : FundamentalFamily (fun _ : H => CommonHilbert) where
  vector _ := commonBasis
  pairingMeasurable _ _ := measurable_const
  dense _ := commonBasis.dense_span

def commonCoordinateEmbedding : CommonHilbert →ₗᵢ[ℂ] CommonHilbert :=
  QuantumProver.CountableGramSchmidt.coordinateEmbedding commonBasis commonBasis.dense_span

theorem commonFundamentalFamily_embedding (h : H) :
    (commonFundamentalFamily (H := H)).embedding h = commonCoordinateEmbedding := rfl

variable {E : H → Type v}
  [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
  [∀ h, CompleteSpace (E h)]
  {F : FundamentalFamily E} {Ω : Type*} [MeasurableSpace Ω]

abbrev SourceInstrument (F : FundamentalFamily E) (Ω : Type*) [MeasurableSpace Ω] :=
  QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument.MatrixInstrument F
    (commonFundamentalFamily (H := H)) Ω

variable (P : SourceInstrument F Ω)

def physicalInstrument (h : H) :
    QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument (E h) CommonHilbert Unit Ω where
  operation _ := P.operation h
  empty _ := P.empty h
  countable_additivity _ s hs hd T := P.countable_additivity h s hs hd T
  completelyPositive _ s hs := P.completelyPositive h s hs
  measurable_coordinate _ _ _ _ _ := measurable_const
  trace_preserving _ T := P.trace_preserving h T

@[simp] theorem physicalInstrument_operation (h : H) (s : Set Ω) :
    (physicalInstrument P h).operation () s = P.operation h s := rfl

def sourceCodedOperation (h : H) (s : Set Ω) : NormalOperation CommonHilbert CommonHilbert :=
  (P.operation h s).comp (recoverNuclear (F.embedding h))

theorem sourceCodedOperation_empty (h : H) : sourceCodedOperation P h ∅ = 0 := by
  ext U
  simp [sourceCodedOperation, P.empty]

theorem sourceCodedOperation_countable_additivity (h : H) (s : ℕ → Set Ω)
    (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Disjoint on s)) (U : Nuc CommonHilbert) :
    HasSum (fun n => sourceCodedOperation P h (s n) U)
      (sourceCodedOperation P h (⋃ n, s n) U) :=
  P.countable_additivity h s hs hd (recoverNuclear (F.embedding h) U)

theorem recoverNuclear_completelyPositive (h : H) :
    NormalCompletelyPositive (recoverNuclear (F.embedding h)) := by
  simpa only [sandwich, recoverNuclear, ContinuousLinearMap.adjoint_adjoint] using
    normalCompletelyPositive_sandwich (F.embedding h).toContinuousLinearMap.adjoint

theorem sourceCodedOperation_completelyPositive (h : H) (s : Set Ω)
    (hs : MeasurableSet s) : NormalCompletelyPositive (sourceCodedOperation P h s) :=
  normalCompletelyPositive_comp _ _ (P.completelyPositive h s hs)
    (recoverNuclear_completelyPositive (F := F) h)

theorem stronglyMeasurable_sourceCodedOperation (s : Set Ω) (hs : MeasurableSet s)
    (U : Nuc CommonHilbert) :
    StronglyMeasurable (fun h => sourceCodedOperation P h s U) := by
  have hm := P.stronglyMeasurable_codedOperation s hs U
  have hr := (recoverNuclear commonCoordinateEmbedding).continuous.comp_stronglyMeasurable hm
  have heq : (fun h => recoverNuclear commonCoordinateEmbedding (P.codedOperation h s U)) =
      (fun h => sourceCodedOperation P h s U) := by
    funext h
    change recoverNuclear commonCoordinateEmbedding
      (padNuclear commonCoordinateEmbedding (P.operation h s (recoverNuclear (F.embedding h) U))) = _
    rw [recover_padNuclear]
    rfl
  rw [heq] at hr
  exact hr

theorem stronglyMeasurable_sourceCodedOperation_variable (s : Set Ω) (hs : MeasurableSet s)
    (U : H → Nuc CommonHilbert) (hU : StronglyMeasurable U) :
    StronglyMeasurable (fun h => sourceCodedOperation P h s (U h)) :=
  QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.stronglyMeasurable_variable_apply _
    (stronglyMeasurable_sourceCodedOperation P s hs) U hU

theorem sourceCodedOperation_total_trace (h : H) (U : Nuc CommonHilbert) :
    QuantumProver.HilbertNuclearTrace.trace (sourceCodedOperation P h univ U) =
      QuantumProver.HilbertNuclearTrace.trace (sandwich (F.rangeProjection h) U) := by
  change QuantumProver.HilbertNuclearTrace.trace (P.operation h univ (recoverNuclear (F.embedding h) U)) = _
  rw [P.trace_preserving]
  rw [sandwich, inputProjection_adjoint]
  rw [← QuantumProver.ElegantJointMeasurement.MeasurableNuclearField.pad_recover_eq_projection, trace_padNuclear]

def sourceRangeInstrument :
    RangeInstrument CommonHilbert CommonHilbert H Ω where
  inputProjection := F.rangeProjection
  projection_adjoint := inputProjection_adjoint F
  projection_idempotent := inputProjection_idempotent F
  operation := sourceCodedOperation P
  empty := sourceCodedOperation_empty P
  countable_additivity := sourceCodedOperation_countable_additivity P
  completelyPositive := sourceCodedOperation_completelyPositive P
  measurable_coordinate s hs U x y := by
    let L : Nuc CommonHilbert →L[ℂ] ℂ :=
      (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ CommonHilbert y).comp toOperator)
    exact (L.continuous.comp_stronglyMeasurable
      (stronglyMeasurable_sourceCodedOperation P s hs U)).measurable
  trace_on_range := sourceCodedOperation_total_trace P

def completeSourceInstrument :
    QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument CommonHilbert CommonHilbert H (Ω ⊕ Unit) :=
  (sourceRangeInstrument P).complete commonResetVector norm_commonResetVector

theorem completeSourceInstrument_physical_event (h : H) (s : Set Ω) :
    (completeSourceInstrument P).operation h (Sum.inl '' s) = sourceCodedOperation P h s := by
  ext U
  exact RangeInstrument.completedOperation_physical_event (sourceRangeInstrument P)
    commonResetVector h s U

theorem sourceCodedOperation_on_physical (h : H) (s : Set Ω) (T : Nuc (E h)) :
    sourceCodedOperation P h s (padNuclear (F.embedding h) T) = P.operation h s T := by
  simp only [sourceCodedOperation, ContinuousLinearMap.comp_apply, recover_padNuclear]

theorem completeSourceInstrument_physical_input (h : H) (s : Set Ω) (T : Nuc (E h)) :
    (completeSourceInstrument P).operation h (Sum.inl '' s) (padNuclear (F.embedding h) T) =
      P.operation h s T := by
  rw [completeSourceInstrument_physical_event, sourceCodedOperation_on_physical]

theorem completeSourceInstrument_dummy (h : H) (U : Nuc CommonHilbert) :
    (completeSourceInstrument P).operation h {Sum.inr ()} U =
      complementReset commonResetVector (F.rangeProjection h) U :=
  RangeInstrument.completedOperation_dummy (sourceRangeInstrument P) commonResetVector h U

theorem sourceProjection_embedding (h : H) :
    (F.rangeProjection h).comp (F.embedding h).toContinuousLinearMap =
      (F.embedding h).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  exact QuantumProver.CountableFrameProjection.rangeProjection_embedding (F.vector h) (F.dense h) x

theorem completeSourceInstrument_dummy_on_physical (h : H) (T : Nuc (E h)) :
    (completeSourceInstrument P).operation h {Sum.inr ()} (padNuclear (F.embedding h) T) = 0 := by
  rw [completeSourceInstrument_dummy]
  exact complementReset_supported_input commonResetVector (F.rangeProjection h)
    (F.embedding h).toContinuousLinearMap (sourceProjection_embedding (F := F) h) T

theorem completeSourceInstrument_all_events_on_physical (h : H) (s : Set (Ω ⊕ Unit))
    (T : Nuc (E h)) :
    (completeSourceInstrument P).operation h s (padNuclear (F.embedding h) T) =
      P.operation h (Sum.inl ⁻¹' s) T := by
  change (sourceRangeInstrument P).completedOperation commonResetVector h s
    (sandwich (F.embedding h).toContinuousLinearMap T) = _
  rw [RangeInstrument.completedOperation_supported_input (sourceRangeInstrument P)
    commonResetVector h s (F.embedding h).toContinuousLinearMap (sourceProjection_embedding (F := F) h)]
  exact sourceCodedOperation_on_physical P h (Sum.inl ⁻¹' s) T

theorem completeSourceInstrument_trace_preserving (h : H) (U : Nuc CommonHilbert) :
    QuantumProver.HilbertNuclearTrace.trace ((completeSourceInstrument P).operation h univ U) =
      QuantumProver.HilbertNuclearTrace.trace U := (completeSourceInstrument P).trace_preserving h U

theorem completeSourceInstrument_countable_additivity (h : H) (s : ℕ → Set (Ω ⊕ Unit))
    (hs : ∀ n, MeasurableSet (s n)) (hd : Pairwise (Disjoint on s)) (U : Nuc CommonHilbert) :
    HasSum (fun n => (completeSourceInstrument P).operation h (s n) U)
      ((completeSourceInstrument P).operation h (⋃ n, s n) U) :=
  (completeSourceInstrument P).countable_additivity h s hs hd U

theorem completeSourceInstrument_completelyPositive (h : H) (s : Set (Ω ⊕ Unit))
    (hs : MeasurableSet s) : NormalCompletelyPositive ((completeSourceInstrument P).operation h s) :=
  (completeSourceInstrument P).completelyPositive h s hs

theorem stronglyMeasurable_completeSourceInstrument (s : Set (Ω ⊕ Unit))
    (hs : MeasurableSet s) (U : Nuc CommonHilbert) :
    StronglyMeasurable (fun h => (completeSourceInstrument P).operation h s U) :=
  stronglyMeasurable_of_weak_coordinates _ ((completeSourceInstrument P).measurable_coordinate s hs U)

theorem stronglyMeasurable_completeSourceInstrument_variable (s : Set (Ω ⊕ Unit))
    (hs : MeasurableSet s) (U : H → Nuc CommonHilbert) (hU : StronglyMeasurable U) :
    StronglyMeasurable (fun h => (completeSourceInstrument P).operation h s (U h)) :=
  QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.stronglyMeasurable_variable_apply _
    (stronglyMeasurable_completeSourceInstrument P s hs) U hU

section FiniteReference
variable {R : Type} [Fintype R] [DecidableEq R]

theorem completeSourceInstrument_amplified_physical_event (h : H) (s : Set Ω)
    (U : Nuc (BlockSpace R CommonHilbert)) :
    normalAmplification ((completeSourceInstrument P).operation h (Sum.inl '' s)) U =
      normalAmplification (P.operation h s) (normalAmplification (recoverNuclear (F.embedding h)) U) := by
  rw [completeSourceInstrument_physical_event, sourceCodedOperation, normalAmplification_comp]

theorem completeSourceInstrument_amplified_all_events_on_physical (h : H)
    (s : Set (Ω ⊕ Unit)) (T : Nuc (BlockSpace R (E h))) :
    normalAmplification ((completeSourceInstrument P).operation h s)
      (normalAmplification (padNuclear (F.embedding h)) T) =
        normalAmplification (P.operation h (Sum.inl ⁻¹' s)) T := by
  rw [← normalAmplification_comp]
  have heq : ((completeSourceInstrument P).operation h s).comp (padNuclear (F.embedding h)) =
      P.operation h (Sum.inl ⁻¹' s) := by
    ext T
    exact completeSourceInstrument_all_events_on_physical P h s T
  rw [heq]

theorem completeSourceInstrument_amplified_physical_input (h : H) (s : Set Ω)
    (T : Nuc (BlockSpace R (E h))) :
    normalAmplification ((completeSourceInstrument P).operation h (Sum.inl '' s))
      (normalAmplification (padNuclear (F.embedding h)) T) =
        normalAmplification (P.operation h s) T := by
  simpa only [Set.preimage_image_eq _ Sum.inl_injective] using
    completeSourceInstrument_amplified_all_events_on_physical P h (Sum.inl '' s) T

theorem completeSourceInstrument_amplified_dummy_on_physical (h : H)
    (T : Nuc (BlockSpace R (E h))) :
    normalAmplification ((completeSourceInstrument P).operation h {Sum.inr ()})
      (normalAmplification (padNuclear (F.embedding h)) T) = 0 := by
  rw [← normalAmplification_comp]
  have heq : ((completeSourceInstrument P).operation h {Sum.inr ()}).comp
      (padNuclear (F.embedding h)) = 0 := by
    ext T
    exact completeSourceInstrument_dummy_on_physical P h T
  simp [heq, normalAmplification_apply, nuclearAssembly]

theorem amplified_recover_isPositive (h : H) (U : Nuc (BlockSpace R CommonHilbert))
    (hU : (toOperator U).IsPositive) :
    (toOperator (normalAmplification (recoverNuclear (F.embedding h)) U)).IsPositive :=
  recoverNuclear_completelyPositive (F := F) h R U hU

theorem completeSourceInstrument_amplified_trace_preserving (h : H)
    (U : Nuc (BlockSpace R CommonHilbert)) :
    QuantumProver.HilbertNuclearTrace.trace
      (normalAmplification ((completeSourceInstrument P).operation h univ) U) =
        QuantumProver.HilbertNuclearTrace.trace U :=
  QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.trace_normalAmplification _
    ((completeSourceInstrument P).trace_preserving h) U

end FiniteReference

section TaggedOutputField

instance dummyInnerProductSpace : InnerProductSpace ℂ (ULift.{w} CommonHilbert) where
  inner x y := inner ℂ x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y c := inner_smul_left x.down y.down c
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner x.down
  conj_inner_symm x y := inner_conj_symm x.down y.down

def dummyBasis : HilbertBasis ℕ ℂ (ULift.{w} CommonHilbert) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.ulift ℂ CommonHilbert)

variable (G : H × Ω → Type w)
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]

abbrev taggedOutputFiber (z : H × (Ω ⊕ Unit)) : Type w :=
  match z.2 with
  | Sum.inl ω => G (z.1, ω)
  | Sum.inr _ => ULift.{w} CommonHilbert

@[reducible] instance taggedNormedAddCommGroup (z : H × (Ω ⊕ Unit)) :
    NormedAddCommGroup (taggedOutputFiber G z) :=
  match z with
  | (h, Sum.inl ω) => inferInstance
  | (_, Sum.inr _) => inferInstance

@[reducible] instance taggedInnerProductSpace (z : H × (Ω ⊕ Unit)) :
    InnerProductSpace ℂ (taggedOutputFiber G z) :=
  match z with
  | (h, Sum.inl ω) => inferInstance
  | (_, Sum.inr _) => inferInstance

instance taggedCompleteSpace (z : H × (Ω ⊕ Unit)) :
    CompleteSpace (taggedOutputFiber G z) :=
  match z with
  | (h, Sum.inl ω) => inferInstance
  | (_, Sum.inr _) => inferInstance

variable {G}

def taggedOutputFamily (Q : FundamentalFamily G) : FundamentalFamily (taggedOutputFiber G) where
  vector z n := match z with
    | (h, Sum.inl ω) => Q.vector (h, ω) n
    | (_, Sum.inr _) => dummyBasis n
  pairingMeasurable i j := by
    have hm : Measurable (Sum.elim
        (fun z : H × Ω => inner ℂ (Q.vector z i) (Q.vector z j))
        (fun _ : H × Unit => inner ℂ (dummyBasis.{w} i) (dummyBasis.{w} j))) :=
      (Q.pairingMeasurable i j).sumElim measurable_const
    have ht := hm.comp (MeasurableEquiv.prodSumDistrib H Ω Unit).measurable
    convert ht using 1
    funext z
    rcases z with ⟨h, s⟩
    cases s <;> rfl
  dense z := by
    rcases z with ⟨h, s⟩
    cases s with
    | inl ω => exact Q.dense (h, ω)
    | inr t => exact dummyBasis.dense_span

theorem taggedOutputFamily_physical_projection (Q : FundamentalFamily G) (h : H) (ω : Ω) :
    (taggedOutputFamily Q).rangeProjection (h, Sum.inl ω) = Q.rangeProjection (h, ω) := rfl

theorem taggedOutputFamily_dummy_projection (Q : FundamentalFamily G) (h : H) :
    (taggedOutputFamily Q).rangeProjection (h, Sum.inr ()) =
      ContinuousLinearMap.id ℂ CommonHilbert := by
  ext y n
  change (taggedOutputFamily Q).rangeProjection (h, Sum.inr ()) y n = y n
  rw [FundamentalFamily.rangeProjection_coordinate]
  have hn : (taggedOutputFamily Q).frame n (h, Sum.inr ()) ≠ 0 := by
    change QuantumProver.CountableGramSchmidt.frame dummyBasis n ≠ 0
    have hnorm : ‖QuantumProver.CountableGramSchmidt.frame dummyBasis n‖ = 1 :=
      InnerProductSpace.gramSchmidtNormed_unit_length n dummyBasis.orthonormal.linearIndependent
    intro hz
    rw [hz, norm_zero] at hnorm
    exact zero_ne_one hnorm
  simp only [ite_eq_left hn]

theorem stronglyMeasurable_taggedOutputProjection_apply (Q : FundamentalFamily G)
    (u : H × (Ω ⊕ Unit) → CommonHilbert) (hu : StronglyMeasurable u) :
    StronglyMeasurable (fun z => (taggedOutputFamily Q).rangeProjection z (u z)) :=
  (taggedOutputFamily Q).stronglyMeasurable_rangeProjection_apply u hu

end TaggedOutputField

end QuantumProver.MatrixNormalSourceCompletion

namespace QuantumProver.MatrixNormalSourceCompletion

open QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest QuantumProver.ElegantJointMeasurement.NormalRecordedAbsorption
open QuantumProver.ElegantJointMeasurement.HilbertRecordedHilbertInstrument
open QuantumProver.ElegantJointMeasurement.MeasurableHilbertField QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion
open QuantumProver.ElegantJointMeasurement.NormalSandwich QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.NuclearOperator (toOperator)

section TaggedTests

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {Ω : Type*} [MeasurableSpace Ω]

def taggedProbe (κ : V → Measure Ω) (A : Nuc V) (v : V) : Measure (Ω ⊕ Unit) :=
  (κ v).map Sum.inl + ENNReal.ofReal (inner ℂ v (toOperator A v)).re • Measure.dirac (Sum.inr ())

theorem integral_taggedProbe (κ : V → Measure Ω) [∀ v, IsFiniteMeasure (κ v)]
    (A : Nuc V) (hA : (toOperator A).IsPositive) (v : V)
    (f : Ω ⊕ Unit → ℂ) (hf : Measurable f) (C : ℝ) (hbound : ∀ ω, ‖f ω‖ ≤ C) :
    (∫ ω, f ω ∂taggedProbe κ A v) =
      (∫ ω, f (Sum.inl ω) ∂κ v) + complexProbe v A * f (Sum.inr ()) := by
  haveI : IsFiniteMeasure ((κ v).map (Sum.inl : Ω → Ω ⊕ Unit)) := inferInstance
  haveI : IsFiniteMeasure
      (ENNReal.ofReal (inner ℂ v (toOperator A v)).re •
        Measure.dirac (Sum.inr () : Ω ⊕ Unit)) :=
    (Measure.dirac (Sum.inr () : Ω ⊕ Unit)).smul_finite ENNReal.ofReal_ne_top
  have hm : Integrable f ((κ v).map (Sum.inl : Ω → Ω ⊕ Unit)) :=
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hbound)
  have ha : Integrable f
      (ENNReal.ofReal (inner ℂ v (toOperator A v)).re •
        Measure.dirac (Sum.inr () : Ω ⊕ Unit)) :=
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hbound)
  rw [taggedProbe, integral_add_measure hm ha,
    integral_map_of_stronglyMeasurable measurable_inl hf.stronglyMeasurable,
    integral_smul_measure, integral_dirac' _ _ hf.stronglyMeasurable]
  have hnon : 0 ≤ (inner ℂ v (toOperator A v)).re := hA.re_inner_nonneg_right v
  simp only [ENNReal.toReal_ofReal hnon, complexProbe_apply, Complex.real_smul]

theorem rawPairTest_taggedProbe (κ : V → Measure Ω) [∀ v, IsFiniteMeasure (κ v)]
    (A : Nuc V) (hA : (toOperator A).IsPositive)
    (f : Ω ⊕ Unit → ℂ) (hf : Measurable f) (C : ℝ) (hbound : ∀ ω, ‖f ω‖ ≤ C)
    (x y : V) :
    rawPairTest (taggedProbe κ A) f x y =
      rawPairTest κ (fun ω => f (Sum.inl ω)) x y +
        inner ℂ x (toOperator A y) * f (Sum.inr ()) := by
  simp only [rawPairTest, integral_taggedProbe κ A hA _ f hf C hbound]
  have hp := probe_polarization A hA x y
  linear_combination hp * f (Sum.inr ())

theorem rawFiniteTest_taggedProbe (b : HilbertBasis ℕ ℂ V)
    (κ : V → Measure Ω) [∀ v, IsFiniteMeasure (κ v)] (A : Nuc V)
    (hA : (toOperator A).IsPositive) (W : Ω ⊕ Unit → V →L[ℂ] V)
    (hW : ∀ x, StronglyMeasurable (fun ω => W ω x))
    (C : ℝ) (hbound : ∀ ω, ‖W ω‖ ≤ C) (n : ℕ) :
    rawFiniteTest b (taggedProbe κ A) W n =
      rawFiniteTest b κ (fun ω => W (Sum.inl ω)) n +
        densityTest (W (Sum.inr ()))
          (QuantumProver.HilbertNuclearCompression.compression b (Finset.range n) A) := by
  rw [densityTest_compression_eq_sum]
  simp only [rawFiniteTest]
  simp_rw [rawPairTest_taggedProbe κ A hA _
    (measurable_observable_entry b W hW _ _) C (norm_observable_entry_le b W hbound _ _)]
  simp only [Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end TaggedTests

section CanonicalTaggedProbes

universe u v
variable {H : Type u} [MeasurableSpace H] {E : H → Type v}
  [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
  [∀ h, CompleteSpace (E h)] {F : FundamentalFamily E}
  {Ω : Type*} [MeasurableSpace Ω] (P : SourceInstrument F Ω)
  {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]

theorem completeSourceInstrument_response_decomposition (h : H)
    (U : Nuc (BlockSpace J CommonHilbert)) (s : Set (Ω ⊕ Unit)) :
    normalResponse (completeSourceInstrument P) h U s =
      normalResponse (physicalInstrument P h) ()
        (normalAmplification (recoverNuclear (F.embedding h)) U) (Sum.inl ⁻¹' s) +
      if Sum.inr () ∈ s then
        normalAmplification (complementReset commonResetVector (F.rangeProjection h)) U else 0 := by
  simp only [normalResponse, completeSourceInstrument, RangeInstrument.complete,
    RangeInstrument.completedOperation]
  rw [normalAmplification_add]
  change normalAmplification (sourceCodedOperation P h (Sum.inl ⁻¹' s)) U + _ = _
  rw [sourceCodedOperation, normalAmplification_comp]
  by_cases hd : (Sum.inr () : Ω ⊕ Unit) ∈ s
  · simp only [ite_eq_left hd]
    rfl
  · simp [hd, normalAmplification_apply, nuclearAssembly, physicalInstrument]

theorem normalProbe_completeSourceInstrument (h : H) (U : Nuc (BlockSpace J CommonHilbert))
    (hU : (toOperator U).IsPositive) (v : BlockSpace J CommonHilbert) :
    normalProbe (completeSourceInstrument P) h U hU v =
      taggedProbe
        (fun v => normalProbe (physicalInstrument P h) ()
          (normalAmplification (recoverNuclear (F.embedding h)) U)
          (amplified_recover_isPositive (F := F) h U hU) v)
        (normalAmplification (complementReset commonResetVector (F.rangeProjection h)) U) v := by
  apply Measure.ext
  intro s hs
  have hA : (toOperator
      (normalAmplification (complementReset commonResetVector (F.rangeProjection h)) U)).IsPositive :=
    normalCompletelyPositive_complementReset commonResetVector (F.rangeProjection h) J U hU
  have represented_hPhysical : (toOperator (normalResponse (physicalInstrument P h) ()
      (normalAmplification (recoverNuclear (F.embedding h)) U) (Sum.inl ⁻¹' s))).IsPositive :=
    normalResponse_isPositive _ _ _ (amplified_recover_isPositive (F := F) h U hU)
      _ (measurable_inl hs)
  rw [normalProbe_apply _ _ _ _ _ _ hs, completeSourceInstrument_response_decomposition]
  rw [taggedProbe, Measure.add_apply, Measure.map_apply measurable_inl hs,
    normalProbe_apply _ _ _ _ _ _ (measurable_inl hs), Measure.smul_apply,
    Measure.dirac_apply' _ hs]
  by_cases hd : (Sum.inr () : Ω ⊕ Unit) ∈ s
  · simp only [ite_eq_left hd, map_add, ContinuousLinearMap.add_apply, inner_add_right,
      Complex.add_re, smul_eq_mul, Set.indicator_of_mem hd, Pi.one_apply, mul_one]
    exact ENNReal.ofReal_add (represented_hPhysical.re_inner_nonneg_right v) (hA.re_inner_nonneg_right v)
  · simp [hd]

end CanonicalTaggedProbes
end QuantumProver.MatrixNormalSourceCompletion

namespace QuantumProver.MatrixNormalSourceCompletion

open QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest QuantumProver.ElegantJointMeasurement.NormalRecordedAbsorption
open QuantumProver.ElegantJointMeasurement.NormalRecordedConvergence QuantumProver.ElegantJointMeasurement.HilbertRecordedHilbertInstrument
open QuantumProver.ElegantJointMeasurement.MeasurableHilbertField QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalInstrumentCompletion
open QuantumProver.ElegantJointMeasurement.NormalSandwich QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.NuclearOperator (toOperator)

universe u v w
variable {H : Type u} [MeasurableSpace H] {E : H → Type v}
  [∀ h, NormedAddCommGroup (E h)] [∀ h, InnerProductSpace ℂ (E h)]
  [∀ h, CompleteSpace (E h)] {F : FundamentalFamily E}
  {Ω : Type*} [MeasurableSpace Ω]
  {G : H × Ω → Type w}
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]

section RecordedTransport
variable {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]

theorem isRecordedObservable_physical
    (W : (Ω ⊕ Unit) → RecordedSpace J →L[ℂ] RecordedSpace J)
    (hW : IsRecordedObservable W) :
    IsRecordedObservable (fun ω => W (Sum.inl ω)) := by
  obtain ⟨hstrong, C, hC, hbound⟩ := hW
  exact ⟨fun x => (hstrong x).comp_measurable measurable_inl,
    C, hC, fun ω => hbound (Sum.inl ω)⟩

theorem controlledObservable_tagged_physical (Q : FundamentalFamily G) (h : H)
    (W : (Ω ⊕ Unit) → RecordedSpace J →L[ℂ] RecordedSpace J) :
    (fun ω => controlledObservable (taggedOutputFamily Q) h W (Sum.inl ω)) =
      controlledObservable Q h (fun ω => W (Sum.inl ω)) := by
  funext ω
  simp only [controlledObservable, outputProjection, taggedOutputFamily_physical_projection]

theorem outputProjection_tagged_dummy (Q : FundamentalFamily G) (h : H) :
    outputProjection (I := J) (taggedOutputFamily Q) h (Sum.inr ()) =
      ContinuousLinearMap.id ℂ (RecordedSpace J) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  rw [outputProjection_apply_coordinate, taggedOutputFamily_dummy_projection]
  rfl

theorem controlledObservable_tagged_dummy (Q : FundamentalFamily G) (h : H)
    (W : (Ω ⊕ Unit) → RecordedSpace J →L[ℂ] RecordedSpace J) :
    controlledObservable (taggedOutputFamily Q) h W (Sum.inr ()) = W (Sum.inr ()) := by
  simp only [controlledObservable, outputProjection_tagged_dummy,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]

theorem normalRecordedExpectation_completeSourceInstrument (P : SourceInstrument F Ω)
    (h : H) (U : Nuc (BlockSpace J CommonHilbert)) (hU : (toOperator U).IsPositive)
    (W : (Ω ⊕ Unit) → RecordedSpace J →L[ℂ] RecordedSpace J)
    (hW : IsRecordedObservable W) :
    normalRecordedExpectation (completeSourceInstrument P) h U hU W =
      normalRecordedExpectation (physicalInstrument P h) ()
        (normalAmplification (recoverNuclear (F.embedding h)) U)
        (amplified_recover_isPositive (F := F) h U hU) (fun ω => W (Sum.inl ω)) +
      densityTest (W (Sum.inr ()))
        (normalAmplification (complementReset commonResetVector (F.rangeProjection h)) U) := by
  let Ur := normalAmplification (recoverNuclear (F.embedding h)) U
  have hUr : (toOperator Ur).IsPositive := amplified_recover_isPositive (F := F) h U hU
  let A := normalAmplification (complementReset commonResetVector (F.rangeProjection h)) U
  have hA : (toOperator A).IsPositive :=
    normalCompletelyPositive_complementReset commonResetVector (F.rangeProjection h) J U hU
  let κ := fun v => normalProbe (physicalInstrument P h) () Ur hUr v
  letI : ∀ v, IsFiniteMeasure (κ v) := fun v => normalProbe_isFinite _ _ _ _ v
  have hSome := isRecordedObservable_physical W hW
  have represented_hPhysical := normalFiniteTest_tendsto_normalRecordedExpectation
    (physicalInstrument P h) () Ur hUr (fun ω => W (Sum.inl ω)) hSome
  have hDummy := compressed_densityTest_tendsto (commonBlockBasis (I := J))
    (W (Sum.inr ())) A
  have hSplit : rawFiniteTest (commonBlockBasis (I := J))
      (fun v => normalProbe (completeSourceInstrument P) h U hU v) W =
      fun n => rawFiniteTest (commonBlockBasis (I := J)) κ (fun ω => W (Sum.inl ω)) n +
        densityTest (W (Sum.inr ()))
          (QuantumProver.HilbertNuclearCompression.compression (commonBlockBasis (I := J))
            (Finset.range n) A) := by
    funext n
    simp_rw [normalProbe_completeSourceInstrument P h U hU]
    obtain ⟨hstrong, C, hC, hbound⟩ := hW
    exact rawFiniteTest_taggedProbe (commonBlockBasis (I := J)) κ A hA W hstrong C hbound n
  have ht := represented_hPhysical.add hDummy
  rw [← hSplit] at ht
  exact ht.limUnder_eq

end RecordedTransport

structure RecordedSourceInstrument (F : FundamentalFamily E) (Q : FundamentalFamily G) where
  represented_physical : SourceInstrument F Ω
  controlled_output : ∀ (J : Type) [Fintype J] [DecidableEq J] [Nonempty J]
    (h : H) (U : Nuc (BlockSpace J (E h))) (hU : (toOperator U).IsPositive)
    (W : Ω → RecordedSpace J →L[ℂ] RecordedSpace J), IsRecordedObservable W →
      normalRecordedExpectation (physicalInstrument represented_physical h) () U hU W =
        normalRecordedExpectation (physicalInstrument represented_physical h) () U hU
          (controlledObservable Q h W)

def completeRecordedSourceInstrument (Q : FundamentalFamily G)
    (P : RecordedSourceInstrument F Q) :
    RecordedNormalInstrument CommonHilbert (taggedOutputFamily Q) where
  represented_physical := completeSourceInstrument P.represented_physical
  controlled_output J _ _ _ h U hU W hW := by
    rw [normalRecordedExpectation_completeSourceInstrument P.represented_physical h U hU W hW]
    rw [normalRecordedExpectation_completeSourceInstrument P.represented_physical h U hU
      (controlledObservable (taggedOutputFamily Q) h W)
      (controlledObservable_isRecordedObservable (taggedOutputFamily Q) h W hW)]
    rw [controlledObservable_tagged_physical, controlledObservable_tagged_dummy]
    exact congrArg (fun z => z + densityTest (W (Sum.inr ()))
      (normalAmplification (complementReset commonResetVector (F.rangeProjection h)) U))
      (P.controlled_output J h _ (amplified_recover_isPositive (F := F) h U hU)
        (fun ω => W (Sum.inl ω)) (isRecordedObservable_physical W hW))

@[simp] theorem completeRecordedSourceInstrument_physical (Q : FundamentalFamily G)
    (P : RecordedSourceInstrument F Q) :
    (completeRecordedSourceInstrument Q P).represented_physical = completeSourceInstrument P.represented_physical := rfl

end QuantumProver.MatrixNormalSourceCompletion
