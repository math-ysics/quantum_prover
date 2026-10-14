import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentAbsorption
import QuantumProver.QuantumChannels.NormalTensorExtension

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open MeasureTheory Set Filter Function InnerProductSpace
open scoped BigOperators Topology TensorProduct

namespace QuantumProver.MatrixNormalTensorInstrument

section DenseLaws

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem hasSum_apply_of_dense (D : Set X) (hD : Dense D)
    (L : ℕ → X →L[ℂ] Y) (M : X →L[ℂ] Y)
    (hPartial : ∀ a : Finset ℕ, ∀ x : X, ‖(∑ i ∈ a, L i) x‖ ≤ ‖x‖)
    (hM : ∀ x : X, ‖M x‖ ≤ ‖x‖)
    (hSum : ∀ x ∈ D, HasSum (fun i => L i x) (M x))
    (x : X) : HasSum (fun i => L i x) (M x) := by
  classical
  have hlim : Tendsto (fun a : Finset ℕ => (∑ i ∈ a, L i) x) atTop (𝓝 (M x)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have he : 0 < ε / 3 := by linarith
    obtain ⟨y, hy, hxy⟩ := hD.exists_dist_lt x he
    have hsumy : Tendsto (fun a : Finset ℕ => (∑ i ∈ a, L i) y) atTop (𝓝 (M y)) := by
      simpa only [HasSum, SummationFilter.unconditional_filter, ContinuousLinearMap.sum_apply]
        using hSum y hy
    obtain ⟨a, ha⟩ := Metric.tendsto_atTop.mp hsumy (ε / 3) he
    refine ⟨a, ?_⟩
    intro b hab
    have hp : dist ((∑ i ∈ b, L i) x) ((∑ i ∈ b, L i) y) ≤ dist x y := by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub]
      exact hPartial b (x - y)
    have hm : dist (M y) (M x) ≤ dist x y := by
      rw [dist_eq_norm, ← map_sub]
      simpa only [← dist_eq_norm, dist_comm] using hM (y - x)
    have hb := ha b hab
    have htriangle := dist_triangle ((∑ i ∈ b, L i) x) ((∑ i ∈ b, L i) y) (M x)
    have htriangle' := dist_triangle ((∑ i ∈ b, L i) y) (M y) (M x)
    linarith
  simpa only [HasSum, SummationFilter.unconditional_filter, ContinuousLinearMap.sum_apply]
    using hlim

variable {H : Type*} [MeasurableSpace H]

theorem stronglyMeasurable_apply_of_dense (D : Set X) (hD : Dense D)
    (L : H → X →L[ℂ] Y)
    (hL : ∀ x ∈ D, StronglyMeasurable (fun h => L h x))
    (x : X) : StronglyMeasurable (fun h => L h x) := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (hD x)
  apply stronglyMeasurable_of_tendsto (Filter.atTop : Filter ℕ) (fun n => hL (u n) (hu n))
  apply tendsto_pi_nhds.mpr
  intro h
  exact (L h).continuous.tendsto x |>.comp hlim

end DenseLaws

end QuantumProver.MatrixNormalTensorInstrument

namespace QuantumProver.MatrixNormalTensorInstrument

open MatrixNuclearTensor
open MatrixNormalTensorExtension
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalCompleteContraction (TraceNonincreasing)

variable {E F G H Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [MeasurableSpace H] [MeasurableSpace Ω]

variable (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument F E H Ω)

local instance tensorBlockComplete {R : Type} [Fintype R]
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q] :
    CompleteSpace (QuantumProver.ElegantJointMeasurement.HilbertChoi.BlockSpace R Q) := PiLp.completeSpace 2 (fun _ : R => Q)

def tensorOperation (h : H) (s : Set Ω) : Nuc (Joint F G) →L[ℂ] Nuc (Joint E G) := by
  classical
  exact if hs : MeasurableSet s then
    extendLeft (G := G) (P.operation h s) (P.completelyPositive h s hs)
      (QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.Instrument.traceNonincreasing P h s hs)
  else 0

theorem tensorOperation_of_measurable (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    tensorOperation (G := G) P h s =
      extendLeft (G := G) (P.operation h s) (P.completelyPositive h s hs)
        (QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.Instrument.traceNonincreasing P h s hs) := by
  simp only [tensorOperation, dif_pos hs]

theorem tensorOperation_tensor (h : H) (s : Set Ω) (hs : MeasurableSet s)
    (T : Nuc F) (U : Nuc G) :
    tensorOperation P h s (tensorNuclear (E := F) (F := G) (E' := F) (F' := G) T U) = tensorNuclear (E := E) (F := G) (E' := E) (F' := G) (P.operation h s T) U := by
  rw [tensorOperation_of_measurable P h s hs]
  exact extendLeft_tensor _ _ _ T U

theorem tensorOperation_norm_le (h : H) (s : Set Ω) (W : Nuc (Joint F G)) :
    ‖tensorOperation P h s W‖ ≤ ‖W‖ := by
  classical
  by_cases hs : MeasurableSet s
  · rw [tensorOperation_of_measurable P h s hs]
    exact extendLeft_norm_le _ _ _ W
  · simp [tensorOperation, hs]

theorem tensorOperation_empty (h : H) : tensorOperation (G := G) P h ∅ = 0 := by
  apply nuclear_joint_clm_ext_tensors
  intro T U
  rw [tensorOperation_tensor P h ∅ MeasurableSet.empty]
  simp [P.empty]

theorem tensorOperation_union (h : H) (s t : Set Ω)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hd : Disjoint s t) :
    tensorOperation (G := G) P h (s ∪ t) = tensorOperation P h s + tensorOperation P h t := by
  apply nuclear_joint_clm_ext_tensors
  intro T U
  rw [tensorOperation_tensor P h (s ∪ t) (hs.union ht)]
  rw [QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.Instrument.operation_union_apply P h s t hs ht hd T]
  simp only [map_add, ContinuousLinearMap.add_apply,
    tensorOperation_tensor P h s hs, tensorOperation_tensor P h t ht]

theorem tensorOperation_finset_union (h : H) (a : ℕ → Set Ω)
    (ha : ∀ i, MeasurableSet (a i)) (hd : Pairwise (Disjoint on a)) (u : Finset ℕ) :
    (∑ i ∈ u, tensorOperation (G := G) P h (a i)) =
      tensorOperation P h (⋃ i ∈ u, a i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [tensorOperation_empty P h]
  | @insert i u hi hu =>
    have hmu : MeasurableSet (⋃ j ∈ u, a j) :=
      MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ => ha j))
    have hdu : Disjoint (a i) (⋃ j ∈ u, a j) := by
      apply Set.disjoint_iUnion_right.mpr
      intro j
      apply Set.disjoint_iUnion_right.mpr
      intro hj
      exact hd (fun he => hi (he.symm ▸ hj))
    have hiu : (⋃ j ∈ insert i u, a j) = a i ∪ (⋃ j ∈ u, a j) := by
      ext x
      simp
    rw [Finset.sum_insert hi, hu, hiu, tensorOperation_union P h (a i) _ (ha i) hmu hdu]

theorem tensorOperation_partialSum_norm_le (h : H) (a : ℕ → Set Ω)
    (ha : ∀ i, MeasurableSet (a i)) (hd : Pairwise (Disjoint on a))
    (u : Finset ℕ) (W : Nuc (Joint F G)) :
    ‖(∑ i ∈ u, tensorOperation P h (a i)) W‖ ≤ ‖W‖ := by
  rw [tensorOperation_finset_union P h a ha hd u]
  exact tensorOperation_norm_le P h _ W

theorem tensorOperation_countable_additivity (h : H) (a : ℕ → Set Ω)
    (ha : ∀ i, MeasurableSet (a i)) (hd : Pairwise (Disjoint on a))
    (W : Nuc (Joint F G)) :
    HasSum (fun i => tensorOperation P h (a i) W)
      (tensorOperation P h (⋃ i, a i) W) := by
  have hUnion : MeasurableSet (⋃ i, a i) := MeasurableSet.iUnion ha
  apply hasSum_apply_of_dense
    (Set.range (algebraicNuclearTensor (E := F) (F := G) (E' := F) (F' := G)))
    denseRange_algebraicNuclearTensor
    (fun i => tensorOperation P h (a i)) (tensorOperation P h (⋃ i, a i))
    (tensorOperation_partialSum_norm_le P h a ha hd)
    (tensorOperation_norm_le P h (⋃ i, a i)) ?_ W
  rintro V ⟨z, rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul T U =>
    rw [algebraicNuclearTensor_tmul]
    have hRaw := (P.countable_additivity h a ha hd T).mapL
      ((tensorNuclear (E := E) (F := G) (E' := E) (F' := G)).flip U)
    convert hRaw using 1
    · funext i
      exact tensorOperation_tensor P h (a i) (ha i) T U
    · exact tensorOperation_tensor P h (⋃ i, a i) hUnion T U
  | add z v hz hv =>
    simpa only [map_add] using hz.add hv

theorem stronglyMeasurable_tensorOperation [TopologicalSpace.SeparableSpace E]
    (s : Set Ω) (hs : MeasurableSet s) (W : Nuc (Joint F G)) :
    StronglyMeasurable (fun h => tensorOperation P h s W) := by
  apply stronglyMeasurable_apply_of_dense
    (Set.range (algebraicNuclearTensor (E := F) (F := G) (E' := F) (F' := G)))
    denseRange_algebraicNuclearTensor (fun h => tensorOperation P h s) ?_ W
  rintro V ⟨z, rfl⟩
  induction z using TensorProduct.inductionOn with
  | tmul T U =>
    have hRaw := QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument.stronglyMeasurable_operation P s hs T
    have hTensor := ((tensorNuclear (E := E) (F := G) (E' := E) (F' := G)).flip U).continuous.comp_stronglyMeasurable hRaw
    rw [algebraicNuclearTensor_tmul]
    convert hTensor using 1
    funext h
    exact tensorOperation_tensor P h s hs T U
  | add z v hz hv =>
    convert hz.add hv using 1
    funext h
    simp only [map_add, Pi.add_apply]

theorem stronglyMeasurable_tensorOperation_variable [TopologicalSpace.SeparableSpace E]
    (s : Set Ω) (hs : MeasurableSet s) (W : H → Nuc (Joint F G))
    (hW : StronglyMeasurable W) :
    StronglyMeasurable (fun h => tensorOperation P h s (W h)) :=
  QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.stronglyMeasurable_variable_apply
    (fun h => tensorOperation P h s) (stronglyMeasurable_tensorOperation P s hs) W hW

theorem tensorOperation_completelyPositive (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    NormalCompletelyPositive (tensorOperation (G := G) P h s) := by
  rw [tensorOperation_of_measurable P h s hs]
  exact extendLeft_completelyPositive _ _ _

theorem tensorOperation_isPositive (h : H) (s : Set Ω) (hs : MeasurableSet s)
    (W : Nuc (Joint F G)) (hW : (NuclearOperator.toOperator W).IsPositive) :
    (NuclearOperator.toOperator (tensorOperation P h s W)).IsPositive := by
  rw [tensorOperation_of_measurable P h s hs]
  exact extendLeft_isPositive _ _ _ W hW

theorem tensorOperation_traceNonincreasing (h : H) (s : Set Ω) (hs : MeasurableSet s) :
    TraceNonincreasing (tensorOperation (G := G) P h s) := by
  rw [tensorOperation_of_measurable P h s hs]
  exact extendLeft_traceNonincreasing _ _ _

theorem tensorOperation_trace_preserving (h : H) (W : Nuc (Joint F G)) :
    HilbertNuclearTrace.trace (tensorOperation P h univ W) = HilbertNuclearTrace.trace W := by
  rw [tensorOperation_of_measurable P h univ MeasurableSet.univ]
  exact trace_extendLeft _ _ _ (P.trace_preserving h) W

theorem normalAmplification_tensorOperation_norm_le {R : Type} [Fintype R] [DecidableEq R]
    (h : H) (s : Set Ω) (hs : MeasurableSet s)
    (W : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (QuantumProver.ElegantJointMeasurement.HilbertChoi.BlockSpace R (Joint F G))) :
    ‖normalAmplification (tensorOperation P h s) W‖ ≤ ‖W‖ :=
  QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.normalAmplification_norm_le_of_cp_trace_nonincreasing _
    (tensorOperation_completelyPositive P h s hs)
    (tensorOperation_traceNonincreasing P h s hs) W

theorem measurable_tensorOperation_coordinate [TopologicalSpace.SeparableSpace E]
    (s : Set Ω) (hs : MeasurableSet s) (W : Nuc (Joint F G)) (x y : Joint E G) :
    Measurable (fun h => inner ℂ x (NuclearOperator.toOperator (tensorOperation P h s W) y)) := by
  let coordinate : Nuc (Joint E G) →L[ℂ] ℂ :=
    (innerSL ℂ x).comp ((ContinuousLinearMap.apply ℂ (Joint E G) y).comp NuclearOperator.toOperator)
  change Measurable (fun h => coordinate (tensorOperation P h s W))
  exact (coordinate.continuous.comp_stronglyMeasurable
    (stronglyMeasurable_tensorOperation P s hs W)).measurable

def tensorInstrument [TopologicalSpace.SeparableSpace E] :
    QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument (Joint F G) (Joint E G) H Ω where
  operation := tensorOperation P
  empty := tensorOperation_empty P
  countable_additivity := tensorOperation_countable_additivity P
  completelyPositive := tensorOperation_completelyPositive P
  measurable_coordinate := measurable_tensorOperation_coordinate P
  trace_preserving := tensorOperation_trace_preserving P

@[simp] theorem tensorInstrument_operation [TopologicalSpace.SeparableSpace E]
    (h : H) (s : Set Ω) :
    (tensorInstrument (G := G) P).operation h s = tensorOperation P h s := rfl

theorem tensorInstrument_product_action [TopologicalSpace.SeparableSpace E]
    (h : H) (s : Set Ω) (hs : MeasurableSet s) (T : Nuc F) (U : Nuc G) :
    (tensorInstrument P).operation h s
      (tensorNuclear (E := F) (F := G) (E' := F) (F' := G) T U) =
        tensorNuclear (E := E) (F := G) (E' := E) (F' := G) (P.operation h s T) U :=
  tensorOperation_tensor P h s hs T U

end QuantumProver.MatrixNormalTensorInstrument
