import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentAbsorption
import QuantumProver.InformationTheory.ElegantJointMeasurement.RecordedHilbertInstrument

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter Set Function InnerProductSpace
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.NormalRecordedAbsorption

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.ElegantJointMeasurement.MeasurableHilbertField QuantumProver.ElegantJointMeasurement.HilbertRecordedHilbertInstrument
open QuantumProver.HilbertNuclearCompression
open QuantumProver.NuclearOperator (toOperator)

local instance commonSeparable : TopologicalSpace.SeparableSpace CommonHilbert := by
  have hs : TopologicalSpace.IsSeparable
      (closure (Submodule.span ℂ (Set.range commonBasis) : Set CommonHilbert)) :=
    ((Set.countable_range commonBasis).isSeparable.span (R := ℂ)).closure
  have hc : closure (Submodule.span ℂ (Set.range commonBasis) : Set CommonHilbert) =
      Set.univ := by
    rw [← Submodule.topologicalClosure_coe, commonBasis.dense_span, Submodule.top_coe]
  exact TopologicalSpace.isSeparable_univ_iff.mp (hc ▸ hs)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable {J : Type} [Fintype J] [DecidableEq J]

def normalResponse (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E CommonHilbert H Ω)
    (h : H) (U : Nuclear (BlockSpace J E)) (s : Set Ω) :
    Nuclear (BlockSpace J CommonHilbert) :=
  normalAmplification (P.operation h s) U

@[simp] theorem normalResponse_empty
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E CommonHilbert H Ω)
    (h : H) (U : Nuclear (BlockSpace J E)) : normalResponse P h U ∅ = 0 := by
  simp [normalResponse, P.empty, normalAmplification_apply, nuclearAssembly]

theorem normalResponse_hasSum
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E CommonHilbert H Ω)
    (h : H) (U : Nuclear (BlockSpace J E)) (s : ℕ → Set Ω)
    (hs : ∀ n, MeasurableSet (s n)) (hd : Pairwise (Disjoint on s)) :
    HasSum (fun n => normalResponse P h U (s n)) (normalResponse P h U (⋃ n, s n)) := by
  have ht (i j : J) : HasSum
      (fun n => compose (insert (E := CommonHilbert) i)
        (PiLp.proj 2 (fun _ : J => CommonHilbert) j)
        (P.operation h (s n) (nuclearBlock i j U)))
      (compose (insert (E := CommonHilbert) i)
        (PiLp.proj 2 (fun _ : J => CommonHilbert) j)
        (P.operation h (⋃ n, s n) (nuclearBlock i j U))) :=
    (P.countable_additivity h s hs hd (nuclearBlock i j U)).mapL _
  simpa only [normalResponse, normalAmplification_apply, nuclearAssembly] using
    (hasSum_sum (s := Finset.univ) fun i hi =>
      hasSum_sum (s := Finset.univ) fun j hj => ht i j)

theorem normalResponse_isPositive
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E CommonHilbert H Ω)
    (h : H) (U : Nuclear (BlockSpace J E)) (hU : (toOperator U).IsPositive)
    (s : Set Ω) (hs : MeasurableSet s) :
    (toOperator (normalResponse P h U s)).IsPositive :=
  P.completelyPositive h s hs J U hU

private theorem trace_assembly {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (A : J → J → Nuclear V) :
    QuantumProver.HilbertNuclearTrace.trace (nuclearAssembly A) =
      ∑ i, QuantumProver.HilbertNuclearTrace.trace (A i i) := by
  simp only [nuclearAssembly, map_sum, QuantumProver.ElegantJointMeasurement.NormalCPInstruments.trace_block]
  simp

theorem normalResponse_trace_univ
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E CommonHilbert H Ω)
    (h : H) (U : Nuclear (BlockSpace J E)) :
    QuantumProver.HilbertNuclearTrace.trace (normalResponse P h U univ) =
      QuantumProver.HilbertNuclearTrace.trace U := by
  rw [normalResponse, normalAmplification_apply, trace_assembly]
  simp_rw [P.trace_preserving]
  rw [← trace_assembly (fun i j => nuclearBlock i j U), nuclearAssembly_nuclearBlock]

variable [Nonempty J]

def normalProbe
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E CommonHilbert H Ω)
    (h : H) (U : Nuclear (BlockSpace J E)) (hU : (toOperator U).IsPositive)
    (v : BlockSpace J CommonHilbert) : Measure Ω :=
  Measure.ofMeasurable (fun s hs => ENNReal.ofReal
      (QuantumProver.ElegantJointMeasurement.NormalChoiKernels.quadraticProbe v (normalResponse P h U s)))
    (by simp) (by
      intro s hs hd
      have ht := (QuantumProver.ElegantJointMeasurement.NormalChoiKernels.quadraticProbe v).hasSum
        (normalResponse_hasSum P h U s hs hd)
      have hn (n : ℕ) : 0 ≤ QuantumProver.ElegantJointMeasurement.NormalChoiKernels.quadraticProbe v
          (normalResponse P h U (s n)) :=
        (normalResponse_isPositive P h U hU (s n) (hs n)).re_inner_nonneg_right v
      rw [← ht.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hn ht.summable])

theorem normalProbe_apply
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E CommonHilbert H Ω)
    (h : H) (U : Nuclear (BlockSpace J E)) (hU : (toOperator U).IsPositive)
    (v : BlockSpace J CommonHilbert) (s : Set Ω) (hs : MeasurableSet s) :
    normalProbe P h U hU v s =
      ENNReal.ofReal (inner ℂ v (toOperator (normalResponse P h U s) v)).re :=
  Measure.ofMeasurable_apply _ hs

instance normalProbe_isFinite
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E CommonHilbert H Ω)
    (h : H) (U : Nuclear (BlockSpace J E)) (hU : (toOperator U).IsPositive)
    (v : BlockSpace J CommonHilbert) : IsFiniteMeasure (normalProbe P h U hU v) := by
  constructor
  rw [normalProbe_apply P h U hU v univ MeasurableSet.univ]
  exact ENNReal.ofReal_lt_top

def normalRecordedExpectation
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E CommonHilbert H Ω)
    (h : H) (U : Nuclear (BlockSpace J E)) (hU : (toOperator U).IsPositive)
    (W : Ω → RecordedSpace J →L[ℂ] RecordedSpace J) : ℂ :=
  limUnder atTop (QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := J))
    (fun v => normalProbe P h U hU v) W)

variable {G : H × Ω → Type*}
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]

structure RecordedNormalInstrument (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (F : FundamentalFamily G) where
  represented_physical : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E CommonHilbert H Ω
  controlled_output : ∀ (J : Type) [Fintype J] [DecidableEq J] [Nonempty J]
    (h : H) (U : Nuclear (BlockSpace J E)) (hU : (toOperator U).IsPositive)
    (W : Ω → RecordedSpace J →L[ℂ] RecordedSpace J), IsRecordedObservable W →
      normalRecordedExpectation represented_physical h U hU W =
        normalRecordedExpectation represented_physical h U hU (controlledObservable F h W)

variable {I : Type} [Fintype I] [DecidableEq I]

def incomingChoi (ρ : PhysicalOperation I E) : Nuclear (BlockSpace I E) :=
  nuclearAssembly (fun i j => ρ (matrixUnit i j))

theorem incomingChoi_eq_nuclearChoi (ρ : PhysicalOperation I E) :
    incomingChoi ρ = nuclearChoi ρ := by
  rw [nuclearChoi_eq]
  rfl

theorem incomingChoi_positive_of_cp (ρ : PhysicalOperation I E)
    (hρ : CompletelyPositive (operationOperator ρ.toLinearMap)) :
    (toOperator (incomingChoi ρ)).IsPositive := by
  rw [incomingChoi_eq_nuclearChoi]
  exact nuclearChoi_isPositive ρ hρ

section Absorption

variable [Nonempty I]
variable (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E CommonHilbert H Ω)
  (ρ : H → PhysicalOperation I E)
  (hρcp : ∀ h, CompletelyPositive (operationOperator (ρ h).toLinearMap))
  (hρmeas : ∀ X, StronglyMeasurable (fun h => ρ h X))
  (hρtrace : ∀ h X, QuantumProver.HilbertNuclearTrace.trace (ρ h X) = Matrix.trace X)

theorem absorbed_physicalChoi_eq_normalResponse (h : H) (s : Set Ω) :
    (absorbInstrument P ρ hρcp hρmeas hρtrace).physicalChoi h s =
      normalResponse P h (incomingChoi (ρ h)) s := by
  rw [QuantumProver.ElegantJointMeasurement.NormalCPInstruments.Instrument.physicalChoi, nuclearChoi_eq,
    normalResponse, normalAmplification_apply, incomingChoi]
  simp only [nuclearBlock_nuclearAssembly, absorbInstrument_operation]
  rfl

theorem normalProbe_absorbed_eq (h : H) (v : RecordedSpace I) :
    normalProbe P h (incomingChoi (ρ h)) (incomingChoi_positive_of_cp (ρ h) (hρcp h)) v =
      QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe
        (absorbInstrument P ρ hρcp hρmeas hρtrace) v h := by
  apply Measure.ext
  intro s hs
  rw [normalProbe_apply P h _ _ v s hs,
    QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe_apply _ v h s hs,
    absorbed_physicalChoi_eq_normalResponse P ρ hρcp hρmeas hρtrace h s]

theorem rawFiniteTest_absorbed_eq (h : H)
    (W : Ω → RecordedSpace I →L[ℂ] RecordedSpace I) :
    QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := I))
      (fun v => normalProbe P h (incomingChoi (ρ h))
        (incomingChoi_positive_of_cp (ρ h) (hρcp h)) v) W =
    QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := I))
      (fun v => QuantumProver.ElegantJointMeasurement.NormalChoiKernels.Instrument.physicalProbe
        (absorbInstrument P ρ hρcp hρmeas hρtrace) v h) W := by
  congr 1
  funext v
  exact normalProbe_absorbed_eq P ρ hρcp hρmeas hρtrace h v

theorem normalRecordedExpectation_absorbed_eq (h : H)
    (W : Ω → RecordedSpace I →L[ℂ] RecordedSpace I) :
    normalRecordedExpectation P h (incomingChoi (ρ h))
      (incomingChoi_positive_of_cp (ρ h) (hρcp h)) W =
      recordedExpectation (absorbInstrument P ρ hρcp hρmeas hρtrace) h W := by
  unfold normalRecordedExpectation recordedExpectation
  rw [rawFiniteTest_absorbed_eq P ρ hρcp hρmeas hρtrace h W]

variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]

include hρmeas hρtrace in

theorem raw_normal_response_absorbed_tendsto (h : H)
    (W : Ω → RecordedSpace I →L[ℂ] RecordedSpace I) (hW : IsRecordedObservable W) :
    Tendsto (QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := I))
      (fun v => normalProbe P h (incomingChoi (ρ h))
        (incomingChoi_positive_of_cp (ρ h) (hρcp h)) v) W) atTop
      (𝓝 (normalRecordedExpectation P h (incomingChoi (ρ h))
        (incomingChoi_positive_of_cp (ρ h) (hρcp h)) W)) := by
  rw [rawFiniteTest_absorbed_eq P ρ hρcp hρmeas hρtrace h W,
    normalRecordedExpectation_absorbed_eq P ρ hρcp hρmeas hρtrace h W]
  exact physical_recorded_response_converges _ h W hW

end Absorption

section RecordedAbsorption

variable [Nonempty I] {F : FundamentalFamily G}

def absorbRecordedInstrument (P : RecordedNormalInstrument E F)
    (ρ : H → PhysicalOperation I E)
    (hρcp : ∀ h, CompletelyPositive (operationOperator (ρ h).toLinearMap))
    (hρmeas : ∀ X, StronglyMeasurable (fun h => ρ h X))
    (hρtrace : ∀ h X, QuantumProver.HilbertNuclearTrace.trace (ρ h X) = Matrix.trace X) :
    RecordedInstrument (I := I) F where
  represented_physical := absorbInstrument P.represented_physical ρ hρcp hρmeas hρtrace
  controlled_output h W hW := by
    rw [← normalRecordedExpectation_absorbed_eq P.represented_physical ρ hρcp hρmeas hρtrace h W,
      ← normalRecordedExpectation_absorbed_eq P.represented_physical ρ hρcp hρmeas hρtrace h
        (controlledObservable F h W)]
    exact P.controlled_output I h (incomingChoi (ρ h))
      (incomingChoi_positive_of_cp (ρ h) (hρcp h)) W hW

@[simp] theorem absorbRecordedInstrument_physical (P : RecordedNormalInstrument E F)
    (ρ : H → PhysicalOperation I E)
    (hρcp : ∀ h, CompletelyPositive (operationOperator (ρ h).toLinearMap))
    (hρmeas : ∀ X, StronglyMeasurable (fun h => ρ h X))
    (hρtrace : ∀ h X, QuantumProver.HilbertNuclearTrace.trace (ρ h X) = Matrix.trace X) :
    (absorbRecordedInstrument P ρ hρcp hρmeas hρtrace).represented_physical =
      absorbInstrument P.represented_physical ρ hρcp hρmeas hρtrace := rfl

theorem absorbed_compared_responses_converge
    [MeasurableSpace.CountableOrCountablyGenerated H Ω]
    (P : RecordedNormalInstrument E F) (ρ : H → PhysicalOperation I E)
    (hρcp : ∀ h, CompletelyPositive (operationOperator (ρ h).toLinearMap))
    (hρmeas : ∀ X, StronglyMeasurable (fun h => ρ h X))
    (hρtrace : ∀ h X, QuantumProver.HilbertNuclearTrace.trace (ρ h X) = Matrix.trace X)
    (h : H) (W : Ω → RecordedSpace I →L[ℂ] RecordedSpace I) (hW : IsRecordedObservable W) :
    Tendsto (QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := I))
      (fun v => normalProbe P.represented_physical h (incomingChoi (ρ h))
        (incomingChoi_positive_of_cp (ρ h) (hρcp h)) v) W) atTop
      (𝓝 (recordedExpectation (absorbRecordedInstrument P ρ hρcp hρmeas hρtrace).represented_physical h W)) ∧
    Tendsto (QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := I))
      (fun v => normalProbe P.represented_physical h (incomingChoi (ρ h))
        (incomingChoi_positive_of_cp (ρ h) (hρcp h)) v) (controlledObservable F h W)) atTop
      (𝓝 (recordedExpectation (absorbRecordedInstrument P ρ hρcp hρmeas hρtrace).represented_physical h
        (controlledObservable F h W))) := by
  simp only [absorbRecordedInstrument_physical]
  rw [rawFiniteTest_absorbed_eq P.represented_physical ρ hρcp hρmeas hρtrace h W,
    rawFiniteTest_absorbed_eq P.represented_physical ρ hρcp hρmeas hρtrace h (controlledObservable F h W)]
  exact ⟨physical_recorded_response_converges _ h W hW,
    physical_recorded_response_converges _ h _ (controlledObservable_isRecordedObservable F h W hW)⟩

end RecordedAbsorption

end QuantumProver.ElegantJointMeasurement.NormalRecordedAbsorption
