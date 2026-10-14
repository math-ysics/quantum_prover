import QuantumProver.QuantumChannels.HilbertSwap
import QuantumProver.QuantumChannels.NormalTensorInstrument

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open MeasureTheory Set Filter Function InnerProductSpace
open scoped BigOperators Topology TensorProduct

namespace QuantumProver.MatrixNormalRightTensor

open MatrixNuclearTensor MatrixNormalTensorExtension MatrixHilbertSwap
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.NormalCompleteContraction (TraceNonincreasing)

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem nuclearSwap_completelyPositive : NormalCompletelyPositive (nuclearSwap E F) := by
  rw [nuclearSwap_eq_sandwich E F]
  exact normalCompletelyPositive_sandwich _

theorem nuclearSwap_isPositive (W : Nuc (Joint E F))
    (hW : (NuclearOperator.toOperator W).IsPositive) :
    (NuclearOperator.toOperator (nuclearSwap E F W)).IsPositive :=
  QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.normalOperation_isPositive _
    (nuclearSwap_completelyPositive (E := E) (F := F)) W hW

def extendRight (Φ : NormalOperation F E) (hCP : NormalCompletelyPositive Φ)
    (hTNI : TraceNonincreasing Φ) : NormalOperation (Joint G F) (Joint G E) :=
  (nuclearSwap E G).comp ((extendLeft (G := G) Φ hCP hTNI).comp (nuclearSwap G F))

theorem extendRight_tensor (Φ : NormalOperation F E) (hCP : NormalCompletelyPositive Φ)
    (hTNI : TraceNonincreasing Φ) (T : Nuc G) (U : Nuc F) :
    extendRight Φ hCP hTNI
      (tensorNuclear (E := G) (F := F) (E' := G) (F' := F) T U) =
      tensorNuclear (E := G) (F := E) (E' := G) (F' := E) T (Φ U) := by
  simp only [extendRight, ContinuousLinearMap.comp_apply, nuclearSwap_tensor, extendLeft_tensor]

theorem extendRight_norm_le (Φ : NormalOperation F E) (hCP : NormalCompletelyPositive Φ)
    (hTNI : TraceNonincreasing Φ) (W : Nuc (Joint G F)) :
    ‖extendRight Φ hCP hTNI W‖ ≤ ‖W‖ := by
  simp only [extendRight, ContinuousLinearMap.comp_apply, nuclearSwap_norm]
  simpa only [nuclearSwap_norm] using extendLeft_norm_le Φ hCP hTNI (nuclearSwap G F W)

theorem norm_extendRight_le_one (Φ : NormalOperation F E) (hCP : NormalCompletelyPositive Φ)
    (hTNI : TraceNonincreasing Φ) : ‖extendRight (G := G) Φ hCP hTNI‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro W
  simpa only [one_mul] using extendRight_norm_le Φ hCP hTNI W

theorem extendRight_unique (Φ : NormalOperation F E) (hCP : NormalCompletelyPositive Φ)
    (hTNI : TraceNonincreasing Φ) (L : NormalOperation (Joint G F) (Joint G E))
    (hL : ∀ T : Nuc G, ∀ U : Nuc F,
      L (tensorNuclear (E := G) (F := F) (E' := G) (F' := F) T U) =
        tensorNuclear (E := G) (F := E) (E' := G) (F' := E) T (Φ U)) :
    L = extendRight Φ hCP hTNI := by
  apply nuclear_joint_clm_ext_tensors
  intro T U
  rw [hL, extendRight_tensor]

theorem extendRight_completelyPositive (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ) :
    NormalCompletelyPositive (extendRight (G := G) Φ hCP hTNI) :=
  normalCompletelyPositive_comp _ _ (nuclearSwap_completelyPositive (E := E) (F := G))
    (normalCompletelyPositive_comp _ _ (extendLeft_completelyPositive Φ hCP hTNI)
      (nuclearSwap_completelyPositive (E := G) (F := F)))

theorem extendRight_isPositive (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (W : Nuc (Joint G F)) (hW : (NuclearOperator.toOperator W).IsPositive) :
    (NuclearOperator.toOperator (extendRight Φ hCP hTNI W)).IsPositive :=
  QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.normalOperation_isPositive _
    (extendRight_completelyPositive Φ hCP hTNI) W hW

theorem extendRight_traceNonincreasing (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ) :
    TraceNonincreasing (extendRight (G := G) Φ hCP hTNI) := by
  intro W hW
  simpa only [extendRight, ContinuousLinearMap.comp_apply, trace_nuclearSwap] using
    extendLeft_traceNonincreasing Φ hCP hTNI (nuclearSwap G F W)
      (nuclearSwap_isPositive W hW)

theorem trace_extendRight (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (hTP : ∀ U, HilbertNuclearTrace.trace (Φ U) = HilbertNuclearTrace.trace U)
    (W : Nuc (Joint G F)) :
    HilbertNuclearTrace.trace (extendRight Φ hCP hTNI W) = HilbertNuclearTrace.trace W := by
  simp only [extendRight, ContinuousLinearMap.comp_apply, trace_nuclearSwap,
    trace_extendLeft Φ hCP hTNI hTP]

section IndependentActions

variable {G' : Type*}
  [NormedAddCommGroup G'] [InnerProductSpace ℂ G'] [CompleteSpace G']

theorem extendLeft_extendRight_commute (Φ : NormalOperation F E) (Ψ : NormalOperation G G')
    (hΦ : NormalCompletelyPositive Φ) (hΨ : NormalCompletelyPositive Ψ)
    (hΦTNI : TraceNonincreasing Φ) (hΨTNI : TraceNonincreasing Ψ) :
    (extendLeft (G := G') Φ hΦ hΦTNI).comp (extendRight (G := F) Ψ hΨ hΨTNI) =
      (extendRight (G := E) Ψ hΨ hΨTNI).comp (extendLeft (G := G) Φ hΦ hΦTNI) := by
  apply nuclear_joint_clm_ext_tensors
  intro T U
  simp only [ContinuousLinearMap.comp_apply, extendLeft_tensor, extendRight_tensor]

theorem extendLeft_extendRight_commute_apply (Φ : NormalOperation F E) (Ψ : NormalOperation G G')
    (hΦ : NormalCompletelyPositive Φ) (hΨ : NormalCompletelyPositive Ψ)
    (hΦTNI : TraceNonincreasing Φ) (hΨTNI : TraceNonincreasing Ψ)
    (W : Nuc (Joint F G)) :
    extendLeft (G := G') Φ hΦ hΦTNI (extendRight (G := F) Ψ hΨ hΨTNI W) =
      extendRight (G := E) Ψ hΨ hΨTNI (extendLeft (G := G) Φ hΦ hΦTNI W) :=
  congrArg (fun L : Nuc (Joint F G) →L[ℂ] Nuc (Joint E G') => L W)
    (extendLeft_extendRight_commute Φ Ψ hΦ hΨ hΦTNI hΨTNI)

end IndependentActions

section Instrument

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument F E H Ω)

def rightTensorOperation (h : H) (s : Set Ω) : NormalOperation (Joint G F) (Joint G E) :=
  (nuclearSwap E G).comp
    ((MatrixNormalTensorInstrument.tensorOperation (G := G) P h s).comp (nuclearSwap G F))

theorem rightTensorOperation_of_measurable (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    rightTensorOperation (G := G) P h s =
      extendRight (G := G) (P.operation h s) (P.completelyPositive h s hs)
        (QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.Instrument.traceNonincreasing P h s hs) := by
  simp only [rightTensorOperation, extendRight,
    MatrixNormalTensorInstrument.tensorOperation_of_measurable P h s hs]

theorem rightTensorOperation_tensor (h : H) (s : Set Ω) (hs : MeasurableSet s)
    (T : Nuc G) (U : Nuc F) :
    rightTensorOperation P h s
      (tensorNuclear (E := G) (F := F) (E' := G) (F' := F) T U) =
      tensorNuclear (E := G) (F := E) (E' := G) (F' := E) T (P.operation h s U) := by
  rw [rightTensorOperation_of_measurable P h s hs]
  exact extendRight_tensor _ _ _ T U

theorem rightTensorOperation_norm_le (h : H) (s : Set Ω) (W : Nuc (Joint G F)) :
    ‖rightTensorOperation P h s W‖ ≤ ‖W‖ := by
  simp only [rightTensorOperation, ContinuousLinearMap.comp_apply, nuclearSwap_norm]
  simpa only [nuclearSwap_norm] using
    MatrixNormalTensorInstrument.tensorOperation_norm_le P h s (nuclearSwap G F W)

theorem rightTensorOperation_empty (h : H) : rightTensorOperation (G := G) P h ∅ = 0 := by
  simp [rightTensorOperation, MatrixNormalTensorInstrument.tensorOperation_empty]

theorem rightTensorOperation_countable_additivity (h : H) (a : ℕ → Set Ω)
    (ha : ∀ i, MeasurableSet (a i)) (hd : Pairwise (Disjoint on a))
    (W : Nuc (Joint G F)) :
    HasSum (fun i => rightTensorOperation P h (a i) W)
      (rightTensorOperation P h (⋃ i, a i) W) := by
  simpa only [rightTensorOperation, ContinuousLinearMap.comp_apply, Function.comp_def] using
    (MatrixNormalTensorInstrument.tensorOperation_countable_additivity P h a ha hd
      (nuclearSwap G F W)).mapL (nuclearSwap E G)

theorem rightTensorOperation_completelyPositive (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    NormalCompletelyPositive (rightTensorOperation (G := G) P h s) := by
  rw [rightTensorOperation_of_measurable P h s hs]
  exact extendRight_completelyPositive _ _ _

theorem rightTensorOperation_isPositive (h : H) (s : Set Ω) (hs : MeasurableSet s)
    (W : Nuc (Joint G F)) (hW : (NuclearOperator.toOperator W).IsPositive) :
    (NuclearOperator.toOperator (rightTensorOperation P h s W)).IsPositive := by
  rw [rightTensorOperation_of_measurable P h s hs]
  exact extendRight_isPositive _ _ _ W hW

theorem rightTensorOperation_traceNonincreasing (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    TraceNonincreasing (rightTensorOperation (G := G) P h s) := by
  rw [rightTensorOperation_of_measurable P h s hs]
  exact extendRight_traceNonincreasing _ _ _

theorem rightTensorOperation_trace_preserving (h : H) (W : Nuc (Joint G F)) :
    HilbertNuclearTrace.trace (rightTensorOperation P h univ W) = HilbertNuclearTrace.trace W := by
  simp only [rightTensorOperation, ContinuousLinearMap.comp_apply, trace_nuclearSwap,
    MatrixNormalTensorInstrument.tensorOperation_trace_preserving P h]

theorem stronglyMeasurable_rightTensorOperation [TopologicalSpace.SeparableSpace E]
    (s : Set Ω) (hs : MeasurableSet s) (W : Nuc (Joint G F)) :
    StronglyMeasurable (fun h => rightTensorOperation P h s W) := by
  simpa only [rightTensorOperation, ContinuousLinearMap.comp_apply, Function.comp_def] using
    (nuclearSwap E G).continuous.comp_stronglyMeasurable
      (MatrixNormalTensorInstrument.stronglyMeasurable_tensorOperation P s hs (nuclearSwap G F W))

theorem stronglyMeasurable_rightTensorOperation_variable [TopologicalSpace.SeparableSpace E]
    (s : Set Ω) (hs : MeasurableSet s) (W : H → Nuc (Joint G F))
    (hW : StronglyMeasurable W) :
    StronglyMeasurable (fun h => rightTensorOperation P h s (W h)) :=
  QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.stronglyMeasurable_variable_apply
    (fun h => rightTensorOperation P h s) (stronglyMeasurable_rightTensorOperation P s hs) W hW

theorem measurable_rightTensorOperation_coordinate [TopologicalSpace.SeparableSpace E]
    (s : Set Ω) (hs : MeasurableSet s) (W : Nuc (Joint G F)) (x y : Joint G E) :
    Measurable (fun h => inner ℂ x (NuclearOperator.toOperator (rightTensorOperation P h s W) y)) := by
  let coordinate : Nuc (Joint G E) →L[ℂ] ℂ :=
    (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ (Joint G E) y).comp NuclearOperator.toOperator)
  change Measurable (fun h => coordinate (rightTensorOperation P h s W))
  exact (coordinate.continuous.comp_stronglyMeasurable
    (stronglyMeasurable_rightTensorOperation P s hs W)).measurable

def rightTensorInstrument [TopologicalSpace.SeparableSpace E] :
    QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument (Joint G F) (Joint G E) H Ω where
  operation := rightTensorOperation P
  empty := rightTensorOperation_empty P
  countable_additivity := rightTensorOperation_countable_additivity P
  completelyPositive := rightTensorOperation_completelyPositive P
  measurable_coordinate := measurable_rightTensorOperation_coordinate P
  trace_preserving := rightTensorOperation_trace_preserving P

@[simp] theorem rightTensorInstrument_operation [TopologicalSpace.SeparableSpace E]
    (h : H) (s : Set Ω) :
    (rightTensorInstrument (G := G) P).operation h s = rightTensorOperation P h s := rfl

theorem rightTensorInstrument_product_action [TopologicalSpace.SeparableSpace E]
    (h : H) (s : Set Ω) (hs : MeasurableSet s) (T : Nuc G) (U : Nuc F) :
    (rightTensorInstrument P).operation h s
      (tensorNuclear (E := G) (F := F) (E' := G) (F' := F) T U) =
      tensorNuclear (E := G) (F := E) (E' := G) (F' := E) T (P.operation h s U) :=
  rightTensorOperation_tensor P h s hs T U

end Instrument

end QuantumProver.MatrixNormalRightTensor
