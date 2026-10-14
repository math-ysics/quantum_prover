import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCompleteContraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Function InnerProductSpace
open scoped BigOperators InnerProduct Topology ComplexOrder

namespace QuantumProver.MatrixNormalAmplifiedInstrument

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalCompleteContraction
open QuantumProver.HilbertNuclearCompression
open QuantumProver.NuclearOperator (toOperator)

variable {E F H Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [MeasurableSpace H] [MeasurableSpace Ω]
variable {I : Type} [Fintype I] [DecidableEq I]

local instance blockComplete {K : Type} [Fintype K]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] :
    CompleteSpace (BlockSpace K G) := PiLp.completeSpace 2 (fun _ : K => G)

local instance nuclearMeasurable {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] :
    MeasurableSpace (Nuclear G) := borel (Nuclear G)

local instance nuclearBorel {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] :
    BorelSpace (Nuclear G) := ⟨rfl⟩

def scalarCoordinate (x y : E) : Nuclear E →L[ℂ] ℂ :=
  (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ E y).comp toOperator)

@[simp] theorem scalarCoordinate_apply (x y : E) (T : Nuclear E) :
    scalarCoordinate x y T = inner ℂ x (toOperator T y) := rfl

theorem normalAmplification_coordinate (Φ : NormalOperation F E)
    (T : Nuclear (BlockSpace I F)) (x y : BlockSpace I E) :
    inner ℂ x (toOperator (normalAmplification (R := I) Φ T) y) =
      ∑ i, ∑ j, inner ℂ (x i) (toOperator (Φ (nuclearBlock i j T)) (y j)) := by
  rw [normalAmplification_apply, toOperator_nuclearAssembly, PiLp.inner_apply]
  simp only [blockOperator_apply, inner_sum]

theorem normalAmplification_hasSum (P : Instrument F E H Ω)
    (h : H) (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Disjoint on s)) (T : Nuclear (BlockSpace I F)) :
    HasSum (fun n => normalAmplification (R := I) (P.operation h (s n)) T)
      (normalAmplification (R := I) (P.operation h (⋃ n, s n)) T) := by
  simp_rw [normalAmplification_apply, nuclearAssembly]
  apply hasSum_sum
  intro i hi
  apply hasSum_sum
  intro j hj
  exact (P.countable_additivity h s hs hd (nuclearBlock i j T)).mapL
    (compose (insert (E := E) i) (PiLp.proj 2 (fun _ : I => E) j))

theorem measurable_normalAmplification_coordinate (P : Instrument F E H Ω)
    (s : Set Ω) (hs : MeasurableSet s) (T : Nuclear (BlockSpace I F))
    (x y : BlockSpace I E) :
    Measurable (fun h => inner ℂ x
      (toOperator (normalAmplification (R := I) (P.operation h s) T) y)) := by
  simp_rw [normalAmplification_coordinate]
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro j hj
  exact P.measurable_coordinate s hs (nuclearBlock i j T) (x i) (y j)

def amplifiedInstrument (I : Type) [Fintype I] [DecidableEq I]
    (P : Instrument F E H Ω) : Instrument (BlockSpace I F) (BlockSpace I E) H Ω where
  operation h s := normalAmplification (R := I) (P.operation h s)
  empty h := by
    ext T
    simp [normalAmplification_apply, P.empty, nuclearAssembly]
  countable_additivity h s hs hd T := normalAmplification_hasSum P h s hs hd T
  completelyPositive h s hs := normalCompletelyPositive_normalAmplification _
    (P.completelyPositive h s hs)
  measurable_coordinate s hs T x y := measurable_normalAmplification_coordinate P s hs T x y
  trace_preserving h T := trace_normalAmplification _ (P.trace_preserving h) T

@[simp] theorem amplifiedInstrument_operation (P : Instrument F E H Ω)
    (h : H) (s : Set Ω) :
    (amplifiedInstrument I P).operation h s =
      normalAmplification (R := I) (P.operation h s) := rfl

@[simp] theorem amplifiedInstrument_operation_apply (P : Instrument F E H Ω)
    (h : H) (s : Set Ω) (T : Nuclear (BlockSpace I F)) :
    (amplifiedInstrument I P).operation h s T =
      nuclearAssembly (fun i j => P.operation h s (nuclearBlock i j T)) :=
  normalAmplification_apply _ _

@[simp] theorem amplifiedInstrument_operation_block (P : Instrument F E H Ω)
    (h : H) (s : Set Ω) (T : Nuclear (BlockSpace I F)) (i j : I) :
    nuclearBlock i j ((amplifiedInstrument I P).operation h s T) =
      P.operation h s (nuclearBlock i j T) :=
  nuclearBlock_normalAmplification _ _ _ _

theorem amplifiedInstrument_normalCP (P : Instrument F E H Ω)
    (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    NormalCompletelyPositive ((amplifiedInstrument I P).operation h s) :=
  (amplifiedInstrument I P).completelyPositive h s hs

theorem amplifiedInstrument_trace_preserving (P : Instrument F E H Ω)
    (h : H) (T : Nuclear (BlockSpace I F)) :
    QuantumProver.HilbertNuclearTrace.trace ((amplifiedInstrument I P).operation h univ T) =
      QuantumProver.HilbertNuclearTrace.trace T :=
  (amplifiedInstrument I P).trace_preserving h T

theorem amplifiedInstrument_countable_additivity (P : Instrument F E H Ω)
    (h : H) (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Disjoint on s)) (T : Nuclear (BlockSpace I F)) :
    HasSum (fun n => (amplifiedInstrument I P).operation h (s n) T)
      ((amplifiedInstrument I P).operation h (⋃ n, s n) T) :=
  (amplifiedInstrument I P).countable_additivity h s hs hd T

theorem measurable_amplifiedInstrument_coordinate (P : Instrument F E H Ω)
    (s : Set Ω) (hs : MeasurableSet s) (T : Nuclear (BlockSpace I F))
    (x y : BlockSpace I E) :
    Measurable (fun h => inner ℂ x
      (toOperator ((amplifiedInstrument I P).operation h s T) y)) :=
  (amplifiedInstrument I P).measurable_coordinate s hs T x y

theorem measurable_amplifiedInstrument_coordinate_variable (P : Instrument F E H Ω)
    (s : Set Ω) (hs : MeasurableSet s) (T : H → Nuclear (BlockSpace I F))
    (hT : StronglyMeasurable T) (x y : BlockSpace I E) :
    Measurable (fun h => inner ℂ x
      (toOperator ((amplifiedInstrument I P).operation h s (T h)) y)) := by
  let L : H → Nuclear (BlockSpace I F) →L[ℂ] ℂ := fun h =>
    (scalarCoordinate x y).comp ((amplifiedInstrument I P).operation h s)
  have hm : ∀ X, StronglyMeasurable (fun h => L h X) := by
    intro X
    exact (measurable_amplifiedInstrument_coordinate P s hs X x y).stronglyMeasurable
  have hv := stronglyMeasurable_variable_apply L hm T hT
  exact hv.measurable

theorem stronglyMeasurable_amplifiedInstrument_operation
    [TopologicalSpace.SeparableSpace E] (P : Instrument F E H Ω)
    (s : Set Ω) (hs : MeasurableSet s) (T : Nuclear (BlockSpace I F)) :
    StronglyMeasurable (fun h => (amplifiedInstrument I P).operation h s T) := by
  simp_rw [amplifiedInstrument_operation_apply, nuclearAssembly]
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  apply Finset.stronglyMeasurable_fun_sum
  intro j hj
  exact (compose (insert (E := E) i) (PiLp.proj 2 (fun _ : I => E) j)).continuous
    |>.comp_stronglyMeasurable (P.stronglyMeasurable_operation s hs (nuclearBlock i j T))

theorem stronglyMeasurable_amplifiedInstrument_operation_variable
    [TopologicalSpace.SeparableSpace E] (P : Instrument F E H Ω)
    (s : Set Ω) (hs : MeasurableSet s) (T : H → Nuclear (BlockSpace I F))
    (hT : StronglyMeasurable T) :
    StronglyMeasurable (fun h => (amplifiedInstrument I P).operation h s (T h)) :=
  stronglyMeasurable_variable_apply _
    (fun X => stronglyMeasurable_amplifiedInstrument_operation P s hs X) T hT

end QuantumProver.MatrixNormalAmplifiedInstrument
