import QuantumProver.QuantumChannels.NuclearTensor
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentAbsorption
import QuantumProver.InformationTheory.ElegantJointMeasurement.SeparableHilbertEmbedding
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalSandwich
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalTensorBlocks

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 5000

noncomputable section

open MeasureTheory Set Filter Function InnerProductSpace TopologicalSpace
open scoped BigOperators Topology TensorProduct InnerProductSpace ComplexOrder Classical

namespace QuantumProver.ElegantJointMeasurement.NormalAncillaPreparation

open QuantumProver.MatrixNuclearTensor QuantumProver.NuclearOperator QuantumProver.HilbertNuclearCompression
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding

variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev Nuc (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] :=
  QuantumProver.NuclearOperator.Nuclear ℂ X X

def preparation (τ : Nuc F) : NormalOperation E (Joint E F) :=
  (tensorNuclear (E := E) (F := F) (E' := E) (F' := F)).flip τ

@[simp] theorem preparation_apply (τ : Nuc F) (T : Nuc E) :
    preparation τ T = tensorNuclear (E := E) (F := F) (E' := E) (F' := F) T τ := rfl

theorem preparation_isPositive (τ : Nuc F) (hτ : (toOperator τ).IsPositive)
    (T : Nuc E) (hT : (toOperator T).IsPositive) :
    (toOperator (preparation τ T)).IsPositive := by
  exact tensorNuclear_isPositive T τ hT hτ

theorem norm_ancilla_eq_one (τ : Nuc F) (hτ : (toOperator τ).IsPositive)
    (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1) : ‖τ‖ = 1 := by
  obtain ⟨ι, b, hb⟩ := exists_hilbertBasis ℂ F
  rw [QuantumProver.ElegantJointMeasurement.NuclearChoi.norm_positive_nuclear_eq_re_trace b τ hτ, htrace]
  rfl

theorem preparation_norm_le (τ : Nuc F) (hτ : (toOperator τ).IsPositive)
    (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1) (T : Nuc E) :
    ‖preparation τ T‖ ≤ ‖T‖ := by
  simpa only [preparation_apply, norm_ancilla_eq_one τ hτ htrace, mul_one] using
    norm_tensorNuclear_le T τ

theorem norm_preparation_le_one (τ : Nuc F) (hτ : (toOperator τ).IsPositive)
    (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1) :
    ‖preparation (E := E) τ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun T => by simpa only [one_mul] using preparation_norm_le τ hτ htrace T)

theorem trace_preparation (τ : Nuc F) (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1)
    (T : Nuc E) : QuantumProver.HilbertNuclearTrace.trace (preparation τ T) =
      QuantumProver.HilbertNuclearTrace.trace T := by
  rw [preparation_apply, trace_tensorNuclear, htrace, mul_one]

section ActualSeparableJoint

theorem separableSpace_joint [SeparableSpace E] [SeparableSpace F] :
    SeparableSpace (Joint E F) := by
  classical
  obtain ⟨ι, bE, hbE⟩ := exists_hilbertBasis ℂ E
  obtain ⟨κ, bF, hbF⟩ := exists_hilbertBasis ℂ F
  letI : Countable ι := countable_of_orthonormal bE.orthonormal
  letI : Countable κ := countable_of_orthonormal bF.orthonormal
  let S : Set (Joint E F) := Set.range (fun p : ι × κ => tmulJoint (bE p.1) (bF p.2))
  let V : Submodule ℂ (Joint E F) := Submodule.span ℂ S
  let C := V.topologicalClosure
  have hC : IsClosed (C : Set (Joint E F)) := V.isClosed_topologicalClosure
  have hbase (i : ι) (j : κ) : tmulJoint (bE i) (bF j) ∈ C :=
    V.le_topologicalClosure (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hleft (x : E) (j : κ) : tmulJoint x (bF j) ∈ C := by
    have hs := (bE.hasSum_repr x).mapL
      ((tmulJoint (E := E) (F := F)).flip (bF j))
    apply hC.mem_of_tendsto hs
    exact Filter.Eventually.of_forall (fun s => C.sum_mem (fun i hi => by
      simpa only [ContinuousLinearMap.flip_apply, map_smul] using
        C.smul_mem (bE.repr x i) (hbase i j)))
  have hpure (x : E) (y : F) : tmulJoint x y ∈ C := by
    have hs := (bF.hasSum_repr y).mapL (tmulJoint x)
    apply hC.mem_of_tendsto hs
    exact Filter.Eventually.of_forall (fun s => C.sum_mem (fun j hj => by
      simpa only [map_smul] using C.smul_mem (bF.repr y j) (hleft x j)))
  have hfull (z : Joint E F) : z ∈ C := by
    refine UniformSpace.Completion.induction_on z hC ?_
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simpa only [UniformSpace.Completion.coe_zero] using C.zero_mem
    | tmul x y => exact hpure x y
    | add x y hx hy =>
        simpa only [UniformSpace.Completion.coe_add] using C.add_mem hx hy
  have htop : C = ⊤ := by
    apply top_unique
    intro z hz
    exact hfull z
  have hsep : IsSeparable (C : Set (Joint E F)) := by
    simpa only [C, V, Submodule.topologicalClosure_coe] using
      ((Set.countable_range (fun p : ι × κ => tmulJoint (bE p.1) (bF p.2))).isSeparable.span
        (R := ℂ)).closure
  rw [htop] at hsep
  exact isSeparable_univ_iff.mp hsep

def jointPadding [SeparableSpace E] [SeparableSpace F] : Joint E F →ₗᵢ[ℂ] CommonHilbert := by
  letI := separableSpace_joint (E := E) (F := F)
  exact separableEmbedding

end ActualSeparableJoint

section SingletonEvents

variable {H : Type*} [MeasurableSpace H]

def singletonOperation (Φ : NormalOperation E K) (_h : H) (s : Set PUnit) :
    NormalOperation E K := if PUnit.unit ∈ s then Φ else 0

theorem normalCompletelyPositive_zero : NormalCompletelyPositive (0 : NormalOperation E K) := by
  intro R _ _ T hT
  simp only [normalAmplification_apply, ContinuousLinearMap.zero_apply, nuclearAssembly,
    map_zero, Finset.sum_const_zero]
  exact ContinuousLinearMap.isPositive_zero

theorem singletonOperation_countable_additivity (Φ : NormalOperation E K) (h : H)
    (s : ℕ → Set PUnit) (hd : Pairwise (Disjoint on s)) (T : Nuc E) :
    HasSum (fun n => singletonOperation Φ h (s n) T)
      (singletonOperation Φ h (⋃ n, s n) T) := by
  classical
  by_cases hm : PUnit.unit ∈ ⋃ n, s n
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hm
    convert hasSum_ite_eq k (Φ T) using 1
    · funext n
      by_cases hn : n = k
      · subst n
        simp [singletonOperation, hk]
      · have hnot : PUnit.unit ∉ s n := fun hmem =>
          Set.disjoint_left.mp (hd hn) hmem hk
        simp [singletonOperation, hn, hnot]
    · simp [singletonOperation, hm]
  · have hnot (n : ℕ) : PUnit.unit ∉ s n :=
      fun hmem => hm (Set.mem_iUnion.mpr ⟨n, hmem⟩)
    simpa only [singletonOperation, if_neg hm, if_neg (hnot _), ContinuousLinearMap.zero_apply] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : Nuc K)) 0)

def singletonInstrument (Φ : NormalOperation E K) (hCP : NormalCompletelyPositive Φ)
    (hTP : ∀ T, QuantumProver.HilbertNuclearTrace.trace (Φ T) = QuantumProver.HilbertNuclearTrace.trace T) :
    Instrument E K H PUnit where
  operation := singletonOperation Φ
  empty h := by simp [singletonOperation]
  countable_additivity h s hs hd T := singletonOperation_countable_additivity Φ h s hd T
  completelyPositive h s hs := by
    classical
    by_cases hm : PUnit.unit ∈ s
    · simpa only [singletonOperation, if_pos hm] using hCP
    · simpa only [singletonOperation, if_neg hm] using
        (normalCompletelyPositive_zero (E := E) (K := K))
  measurable_coordinate s hs T x y := by
    change Measurable (fun _ : H => inner ℂ x
      (toOperator ((if PUnit.unit ∈ s then Φ else 0) T) y))
    exact measurable_const
  trace_preserving h T := by simp only [singletonOperation, Set.mem_univ, if_true, hTP]

@[simp] theorem singletonInstrument_operation (Φ : NormalOperation E K)
    (hCP : NormalCompletelyPositive Φ)
    (hTP : ∀ T, QuantumProver.HilbertNuclearTrace.trace (Φ T) = QuantumProver.HilbertNuclearTrace.trace T)
    (h : H) (s : Set PUnit) (T : Nuc E) :
    (singletonInstrument Φ hCP hTP).operation h s T =
      if PUnit.unit ∈ s then Φ T else 0 := by
  classical
  by_cases hm : PUnit.unit ∈ s <;> simp [singletonInstrument, singletonOperation, hm]

theorem stronglyMeasurable_singletonOperation (Φ : NormalOperation E K)
    (s : Set PUnit) (T : Nuc E) :
    StronglyMeasurable (fun h : H => singletonOperation Φ h s T) := by
  change StronglyMeasurable (fun _ : H => (if PUnit.unit ∈ s then Φ else 0) T)
  exact stronglyMeasurable_const

theorem stronglyMeasurable_singletonOperation_variable (Φ : NormalOperation E K)
    (s : Set PUnit) (T : H → Nuc E) (hT : StronglyMeasurable T) :
    StronglyMeasurable (fun h : H => singletonOperation Φ h s (T h)) := by
  by_cases hm : PUnit.unit ∈ s
  · simpa only [singletonOperation, if_pos hm] using
      Φ.continuous.comp_stronglyMeasurable hT
  · simpa only [singletonOperation, if_neg hm, ContinuousLinearMap.zero_apply] using
      (stronglyMeasurable_const : StronglyMeasurable (fun _ : H => (0 : Nuc K)))

end SingletonEvents

def paddedPreparation (τ : Nuc F) (J : Joint E F →ₗᵢ[ℂ] K) : NormalOperation E K :=
  (padNuclear J).comp (preparation τ)

@[simp] theorem paddedPreparation_apply (τ : Nuc F) (J : Joint E F →ₗᵢ[ℂ] K) (T : Nuc E) :
    paddedPreparation τ J T = padNuclear J
      (tensorNuclear (E := E) (F := F) (E' := E) (F' := F) T τ) := rfl

theorem toOperator_paddedPreparation (τ : Nuc F) (J : Joint E F →ₗᵢ[ℂ] K) (T : Nuc E) :
    toOperator (paddedPreparation τ J T) = J.toContinuousLinearMap ∘L
      tensorMap (toOperator T) (toOperator τ) ∘L J.toContinuousLinearMap.adjoint := by
  rw [paddedPreparation_apply, toOperator_padNuclear, toOperator_tensorNuclear]

theorem trace_paddedPreparation (τ : Nuc F) (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1)
    (J : Joint E F →ₗᵢ[ℂ] K) (T : Nuc E) :
    QuantumProver.HilbertNuclearTrace.trace (paddedPreparation τ J T) =
      QuantumProver.HilbertNuclearTrace.trace T := by
  rw [paddedPreparation, ContinuousLinearMap.comp_apply, trace_padNuclear, trace_preparation τ htrace]

theorem paddedPreparation_norm_le (τ : Nuc F) (hτ : (toOperator τ).IsPositive)
    (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1) (J : Joint E F →ₗᵢ[ℂ] K) (T : Nuc E) :
    ‖paddedPreparation τ J T‖ ≤ ‖T‖ :=
  (norm_padNuclear_le J _).trans (preparation_norm_le τ hτ htrace T)

theorem norm_paddedPreparation_le_one (τ : Nuc F) (hτ : (toOperator τ).IsPositive)
    (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1) (J : Joint E F →ₗᵢ[ℂ] K) :
    ‖paddedPreparation τ J‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun T => by simpa only [one_mul] using paddedPreparation_norm_le τ hτ htrace J T)

theorem padNuclear_completelyPositive (J : E →ₗᵢ[ℂ] K) :
    NormalCompletelyPositive (padNuclear J) :=
  normalCompletelyPositive_sandwich J.toContinuousLinearMap

theorem preparation_completelyPositive (τ : Nuc F) (hτ : (toOperator τ).IsPositive) :
    NormalCompletelyPositive (preparation (E := E) τ) := by
  intro R _ _ T hT
  rw [normalAmplification_apply]
  simpa only [preparation_apply] using
    QuantumProver.ElegantJointMeasurement.NormalTensorBlocks.nuclearAssembly_tensor_isPositive T τ hT hτ

def singletonPreparationInstrument {H : Type*} [MeasurableSpace H]
    (τ : Nuc F) (hτ : (toOperator τ).IsPositive)
    (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1) :
    Instrument E (Joint E F) H PUnit :=
  singletonInstrument (preparation τ) (preparation_completelyPositive τ hτ)
    (trace_preparation τ htrace)

@[simp] theorem singletonPreparationInstrument_operation {H : Type*} [MeasurableSpace H]
    (τ : Nuc F) (hτ : (toOperator τ).IsPositive)
    (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1) (h : H) (s : Set PUnit) (T : Nuc E) :
    (singletonPreparationInstrument τ hτ htrace).operation h s T =
      if PUnit.unit ∈ s then
        tensorNuclear (E := E) (F := F) (E' := E) (F' := F) T τ else 0 := by
  simp only [singletonPreparationInstrument, singletonInstrument_operation, preparation_apply]

theorem paddedPreparation_completelyPositive (τ : Nuc F)
    (hτ : (toOperator τ).IsPositive) (J : Joint E F →ₗᵢ[ℂ] K) :
    NormalCompletelyPositive (paddedPreparation τ J) :=
  normalCompletelyPositive_comp (padNuclear J) (preparation τ)
    (padNuclear_completelyPositive J) (preparation_completelyPositive τ hτ)

def paddedSingletonPreparationInstrument {H : Type*} [MeasurableSpace H]
    (τ : Nuc F) (hτ : (toOperator τ).IsPositive)
    (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1) (J : Joint E F →ₗᵢ[ℂ] K) :
    Instrument E K H PUnit :=
  singletonInstrument (paddedPreparation τ J) (paddedPreparation_completelyPositive τ hτ J)
    (trace_paddedPreparation τ htrace J)

@[simp] theorem paddedSingletonPreparationInstrument_operation {H : Type*} [MeasurableSpace H]
    (τ : Nuc F) (hτ : (toOperator τ).IsPositive)
    (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1) (J : Joint E F →ₗᵢ[ℂ] K)
    (h : H) (s : Set PUnit) (T : Nuc E) :
    (paddedSingletonPreparationInstrument τ hτ htrace J).operation h s T =
      if PUnit.unit ∈ s then padNuclear J
        (tensorNuclear (E := E) (F := F) (E' := E) (F' := F) T τ) else 0 := by
  simp only [paddedSingletonPreparationInstrument, singletonInstrument_operation,
    paddedPreparation_apply]

def commonPreparation [SeparableSpace E] [SeparableSpace F] (τ : Nuc F) :
    NormalOperation E CommonHilbert :=
  paddedPreparation τ (jointPadding (E := E) (F := F))

theorem commonPreparation_completelyPositive [SeparableSpace E] [SeparableSpace F]
    (τ : Nuc F) (hτ : (toOperator τ).IsPositive) :
    NormalCompletelyPositive (commonPreparation (E := E) τ) :=
  paddedPreparation_completelyPositive τ hτ _

theorem trace_commonPreparation [SeparableSpace E] [SeparableSpace F]
    (τ : Nuc F) (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1) (T : Nuc E) :
    QuantumProver.HilbertNuclearTrace.trace (commonPreparation τ T) =
      QuantumProver.HilbertNuclearTrace.trace T :=
  trace_paddedPreparation τ htrace _ T

theorem commonPreparation_norm_le [SeparableSpace E] [SeparableSpace F]
    (τ : Nuc F) (hτ : (toOperator τ).IsPositive)
    (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1) (T : Nuc E) :
    ‖commonPreparation τ T‖ ≤ ‖T‖ :=
  paddedPreparation_norm_le τ hτ htrace _ T

def commonSingletonPreparationInstrument {H : Type*} [MeasurableSpace H]
    [SeparableSpace E] [SeparableSpace F] (τ : Nuc F) (hτ : (toOperator τ).IsPositive)
    (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1) :
    Instrument E CommonHilbert H PUnit :=
  paddedSingletonPreparationInstrument τ hτ htrace (jointPadding (E := E) (F := F))

@[simp] theorem commonSingletonPreparationInstrument_operation {H : Type*} [MeasurableSpace H]
    [SeparableSpace E] [SeparableSpace F] (τ : Nuc F) (hτ : (toOperator τ).IsPositive)
    (htrace : QuantumProver.HilbertNuclearTrace.trace τ = 1) (h : H) (s : Set PUnit) (T : Nuc E) :
    (commonSingletonPreparationInstrument τ hτ htrace).operation h s T =
      if PUnit.unit ∈ s then padNuclear (jointPadding (E := E) (F := F))
        (tensorNuclear (E := E) (F := F) (E' := E) (F' := F) T τ) else 0 := by
  simp only [commonSingletonPreparationInstrument, paddedSingletonPreparationInstrument_operation]

end QuantumProver.ElegantJointMeasurement.NormalAncillaPreparation
