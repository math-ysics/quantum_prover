import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCPInstruments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory InnerProductSpace Set Filter TopologicalSpace
open scoped BigOperators Topology ComplexOrder
open scoped Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.NuclearOperator QuantumProver.HilbertNuclearCompression

abbrev CommonHilbert := lp (fun _ : ℕ => ℂ) 2

def commonBasis : HilbertBasis ℕ ℂ CommonHilbert :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ CommonHilbert)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem countable_of_orthonormal [SeparableSpace E] {ι : Type*} {v : ι → E}
    (hv : Orthonormal ℂ v) : Countable ι := by
  apply Pairwise.countable_of_isOpen_disjoint
    (s := fun i => Metric.ball (v i) (1/2 : ℝ))
  · intro i j hij
    apply disjoint_left.mpr
    intro z hi hj
    have hi' : dist (v i) z < (1/2 : ℝ) := by
      simpa only [Metric.mem_ball, dist_comm] using hi
    have hj' : dist z (v j) < (1/2 : ℝ) := hj
    have hd : dist (v i) (v j) < 1 := by
      linarith [dist_triangle (v i) z (v j)]
    have hs : dist (v i) (v j) ^ 2 = 2 := by
      rw [dist_eq_norm, @norm_sub_sq ℂ E, hv.1 i, hv.1 j, hv.2 hij]
      norm_num
    nlinarith [show 0 ≤ dist (v i) (v j) from dist_nonneg]
  · intro i
    exact Metric.isOpen_ball
  · intro i
    exact ⟨v i, Metric.mem_ball_self (by norm_num)⟩

theorem exists_separable_embedding [SeparableSpace E] :
    Nonempty (E →ₗᵢ[ℂ] CommonHilbert) := by
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℂ E
  letI : Countable w := countable_of_orthonormal b.orthonormal
  obtain ⟨f, hf⟩ := exists_injective_nat w
  have hon : Orthonormal ℂ (fun i : w => commonBasis (f i)) :=
    ⟨fun i => commonBasis.orthonormal.1 _, fun i j hij =>
      commonBasis.orthonormal.2 (fun he => hij (hf he))⟩
  exact ⟨hon.orthogonalFamily.linearIsometry.comp b.repr.toLinearIsometry⟩

def separableEmbedding [SeparableSpace E] : E →ₗᵢ[ℂ] CommonHilbert :=
  Classical.choice exists_separable_embedding

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem adjoint_embedding_apply (J : E →ₗᵢ[ℂ] F) (x : E) :
    J.toContinuousLinearMap.adjoint (J x) = x := by
  have h := congrArg (fun A : E →L[ℂ] E => A x) J.adjoint_comp_self
  simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self,
    LinearIsometry.coe_toContinuousLinearMap] using h

theorem norm_embedding_le_one (J : E →ₗᵢ[ℂ] F) : ‖J.toContinuousLinearMap‖ ≤ 1 := by
  apply J.toContinuousLinearMap.opNorm_le_bound zero_le_one
  intro x
  simp only [LinearIsometry.coe_toContinuousLinearMap, J.norm_map, one_mul, le_refl]

def padNuclear (J : E →ₗᵢ[ℂ] F) : Nuclear E →L[ℂ] Nuclear F :=
  compose J.toContinuousLinearMap J.toContinuousLinearMap.adjoint

def recoverNuclear (J : E →ₗᵢ[ℂ] F) : Nuclear F →L[ℂ] Nuclear E :=
  compose J.toContinuousLinearMap.adjoint J.toContinuousLinearMap

theorem toOperator_padNuclear (J : E →ₗᵢ[ℂ] F) (T : Nuclear E) :
    toOperator (padNuclear J T) =
      J.toContinuousLinearMap ∘L toOperator T ∘L J.toContinuousLinearMap.adjoint :=
  toOperator_compose _ _ _

theorem recover_padNuclear (J : E →ₗᵢ[ℂ] F) (T : Nuclear E) :
    recoverNuclear J (padNuclear J T) = T := by
  apply toOperator_injective
  ext x
  simp only [recoverNuclear, padNuclear, toOperator_compose,
    ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    adjoint_embedding_apply]

theorem norm_padNuclear_le (J : E →ₗᵢ[ℂ] F) (T : Nuclear E) :
    ‖padNuclear J T‖ ≤ ‖T‖ := by
  have hJ := norm_embedding_le_one J
  have hA : ‖J.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hJ
  apply (norm_compose_apply_le _ _ T).trans
  calc
    _ ≤ (1 * 1) * ‖T‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul hJ hA (norm_nonneg _) zero_le_one) (norm_nonneg T)
    _ = _ := by ring

theorem norm_recoverNuclear_le (J : E →ₗᵢ[ℂ] F) (T : Nuclear F) :
    ‖recoverNuclear J T‖ ≤ ‖T‖ := by
  have hJ := norm_embedding_le_one J
  have hA : ‖J.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hJ
  apply (norm_compose_apply_le _ _ T).trans
  calc
    _ ≤ (1 * 1) * ‖T‖ := mul_le_mul_of_nonneg_right
      (mul_le_mul hA hJ (norm_nonneg _) zero_le_one) (norm_nonneg T)
    _ = _ := by ring

theorem norm_padNuclear (J : E →ₗᵢ[ℂ] F) (T : Nuclear E) :
    ‖padNuclear J T‖ = ‖T‖ := by
  apply le_antisymm (norm_padNuclear_le J T)
  simpa only [recover_padNuclear] using norm_recoverNuclear_le J (padNuclear J T)

theorem padNuclear_isPositive (J : E →ₗᵢ[ℂ] F) (T : Nuclear E)
    (hT : (toOperator T).IsPositive) : (toOperator (padNuclear J T)).IsPositive := by
  rw [toOperator_padNuclear]
  exact hT.conj_adjoint J.toContinuousLinearMap

theorem trace_padNuclear (J : E →ₗᵢ[ℂ] F) (T : Nuclear E) :
    QuantumProver.HilbertNuclearTrace.trace (padNuclear J T) = QuantumProver.HilbertNuclearTrace.trace T := by
  rw [padNuclear, QuantumProver.ElegantJointMeasurement.NormalCPInstruments.trace_compose_cycle, J.adjoint_comp_self]
  congr 1
  apply toOperator_injective
  ext x
  simp only [toOperator_compose, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, one_apply_eq_self]

theorem padNuclear_pureState (J : E →ₗᵢ[ℂ] F) (x : E) :
    padNuclear J (QuantumProver.NuclearOperator.rankOne (innerSL ℂ x) x) =
      QuantumProver.NuclearOperator.rankOne (innerSL ℂ (J x)) (J x) := by
  have hφ : (innerSL ℂ x).comp J.toContinuousLinearMap.adjoint = innerSL ℂ (J x) := by
    ext y
    exact J.toContinuousLinearMap.adjoint_inner_right x y
  simp only [padNuclear, compose_rankOne, hφ, LinearIsometry.coe_toContinuousLinearMap]

variable {P : Type*} [MeasurableSpace P]
local instance nuclearMeasurableE : MeasurableSpace (Nuclear E) := borel (Nuclear E)
local instance nuclearBorelE : BorelSpace (Nuclear E) := ⟨rfl⟩
local instance nuclearMeasurableF : MeasurableSpace (Nuclear F) := borel (Nuclear F)
local instance nuclearBorelF : BorelSpace (Nuclear F) := ⟨rfl⟩

theorem measurable_padNuclear (J : E →ₗᵢ[ℂ] F) (T : P → Nuclear E)
    (hT : Measurable T) : Measurable (fun p => padNuclear J (T p)) :=
  (padNuclear J).continuous.measurable.comp hT

theorem stronglyMeasurable_padNuclear (J : E →ₗᵢ[ℂ] F) (T : P → Nuclear E)
    (hT : StronglyMeasurable T) : StronglyMeasurable (fun p => padNuclear J (T p)) :=
  (padNuclear J).continuous.comp_stronglyMeasurable hT

theorem integrable_padNuclear (J : E →ₗᵢ[ℂ] F) (T : P → Nuclear E)
    (μ : Measure P) (hT : Integrable T μ) :
    Integrable (fun p => padNuclear J (T p)) μ := (padNuclear J).integrable_comp hT

theorem measurable_recoverNuclear (J : E →ₗᵢ[ℂ] F) (T : P → Nuclear F)
    (hT : Measurable T) : Measurable (fun p => recoverNuclear J (T p)) :=
  (recoverNuclear J).continuous.measurable.comp hT

theorem integrable_recoverNuclear (J : E →ₗᵢ[ℂ] F) (T : P → Nuclear F)
    (μ : Measure P) (hT : Integrable T μ) :
    Integrable (fun p => recoverNuclear J (T p)) μ := (recoverNuclear J).integrable_comp hT

theorem integral_recoverNuclear (J : E →ₗᵢ[ℂ] F) (T : P → Nuclear F)
    (μ : Measure P) (hT : Integrable T μ) :
    (∫ p, recoverNuclear J (T p) ∂μ) = recoverNuclear J (∫ p, T p ∂μ) :=
  (recoverNuclear J).integral_comp_comm hT

open QuantumProver.ElegantJointMeasurement.HilbertChoi
variable {I : Type} [Fintype I] [DecidableEq I]

def blockFamily (q : I × ℕ) : BlockSpace I CommonHilbert :=
  insert q.1 (commonBasis q.2)

theorem blockFamily_orthonormal : Orthonormal ℂ (blockFamily (I := I)) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i,n⟩ ⟨j,m⟩
  by_cases hij : i = j
  · subst j
    simp [blockFamily, PiLp.inner_apply, insert_apply_apply, apply_ite, ite_apply,
      orthonormal_iff_ite.mp commonBasis.orthonormal]
  · simp [blockFamily, PiLp.inner_apply, insert_apply_apply, apply_ite, ite_apply,
      hij, Ne.symm hij]

theorem blockFamily_dense_span :
    (Submodule.span ℂ (range (blockFamily (I := I)))).topologicalClosure = ⊤ := by
  let S := Submodule.span ℂ (range (blockFamily (I := I)))
  have hi (i : I) (x : CommonHilbert) : insert i x ∈ S.topologicalClosure := by
    have ht := (commonBasis.hasSum_repr x).mapL (insert (E := CommonHilbert) i)
    apply S.isClosed_topologicalClosure.mem_of_tendsto ht
    apply Filter.Eventually.of_forall
    intro s
    apply S.topologicalClosure.sum_mem
    intro l hl
    simp only [map_smul]
    apply S.topologicalClosure.smul_mem
    exact S.le_topologicalClosure
      (Submodule.subset_span (show insert i (commonBasis l) ∈ range blockFamily from
        ⟨(i,l),rfl⟩))
  apply eq_top_iff.mpr
  intro x hx
  have he : (∑ i, insert i (x i)) = x := by
    ext i
    simp [insert_apply_apply]
  rw [← he]
  exact S.topologicalClosure.sum_mem fun i _ => hi i (x i)

def commonBlockBasis [Nonempty I] : HilbertBasis ℕ ℂ (BlockSpace I CommonHilbert) := by
  let e : ℕ ≃ I × ℕ := Classical.choice inferInstance
  have hon : Orthonormal ℂ (fun n => blockFamily (e n)) :=
    ⟨fun n => blockFamily_orthonormal.1 _, fun n m hnm =>
      blockFamily_orthonormal.2 (fun he => hnm (e.injective he))⟩
  apply HilbertBasis.mk hon
  have hr : range (fun n => blockFamily (e n)) = range (blockFamily (I := I)) := by
    ext x
    constructor
    · rintro ⟨n,rfl⟩
      exact ⟨e n,rfl⟩
    · rintro ⟨q,rfl⟩
      refine ⟨e.symm q, ?_⟩
      change blockFamily (e (e.symm q)) = blockFamily q
      rw [e.apply_symm_apply]
  rw [hr, blockFamily_dense_span]

variable {R : Type} [Fintype R] [DecidableEq R]

def blockLift (V : E →L[ℂ] F) : BlockSpace R E →L[ℂ] BlockSpace R F :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : R => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun r => V.comp (PiLp.proj 2 (fun _ : R => E) r))

@[simp] theorem blockLift_apply (V : E →L[ℂ] F) (x : BlockSpace R E) (r : R) :
    blockLift V x r = V (x r) := rfl

theorem blockLift_adjoint (V : E →L[ℂ] F) :
    (blockLift (R := R) V).adjoint = blockLift V.adjoint := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, blockLift_apply, ContinuousLinearMap.adjoint_inner_left]

open QuantumProver.ElegantJointMeasurement.NormalCPInstruments

def padOperation (J : E →ₗᵢ[ℂ] F) : PhysicalOperation I E →L[ℂ] PhysicalOperation I F :=
  ContinuousLinearMap.compL ℂ (Matrix I I ℂ) (Nuclear E) (Nuclear F) (padNuclear J)

@[simp] theorem padOperation_apply (J : E →ₗᵢ[ℂ] F) (Φ : PhysicalOperation I E)
    (X : Matrix I I ℂ) : padOperation J Φ X = padNuclear J (Φ X) := rfl

theorem amplification_padOperation (J : E →ₗᵢ[ℂ] F) (Φ : PhysicalOperation I E)
    (X : Matrix (R × I) (R × I) ℂ) :
    amplification (operationOperator (padOperation J Φ).toLinearMap) X =
      blockLift J.toContinuousLinearMap ∘L
        amplification (operationOperator Φ.toLinearMap) X ∘L
        (blockLift (R := R) J.toContinuousLinearMap).adjoint := by
  rw [blockLift_adjoint]
  ext x r
  simp only [amplification, blockOperator_apply, blockLift_apply,
    ContinuousLinearMap.comp_apply, operationOperator, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, padOperation_apply, toOperator_padNuclear,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    map_sum, map_smul]

theorem completelyPositive_padOperation (J : E →ₗᵢ[ℂ] F) (Φ : PhysicalOperation I E)
    (hΦ : CompletelyPositive (operationOperator Φ.toLinearMap)) :
    CompletelyPositive (operationOperator (padOperation J Φ).toLinearMap) := by
  intro R _ _ X hX
  rw [amplification_padOperation]
  exact (hΦ R X hX).conj_adjoint (blockLift J.toContinuousLinearMap)

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
local instance operationMeasurableE : MeasurableSpace (PhysicalOperation I E) :=
  borel (PhysicalOperation I E)
local instance operationBorelE : BorelSpace (PhysicalOperation I E) := ⟨rfl⟩
local instance operationMeasurableF : MeasurableSpace (PhysicalOperation I F) :=
  borel (PhysicalOperation I F)
local instance operationBorelF : BorelSpace (PhysicalOperation I F) := ⟨rfl⟩

def padInstrument (J : E →ₗᵢ[ℂ] F) (P : Instrument I E H Ω) : Instrument I F H Ω where
  operation h s := padOperation J (P.operation h s)
  empty h := by simp only [P.empty, map_zero]
  countable_additivity h s hs hd X :=
    (padNuclear J).hasSum (P.countable_additivity h s hs hd X)
  completelyPositive h s hs := completelyPositive_padOperation J _ (P.completelyPositive h s hs)
  measurable_operation s hs := (padOperation J).continuous.measurable.comp (P.measurable_operation s hs)
  trace_preserving h X := by
    rw [padOperation_apply, trace_padNuclear]
    exact P.trace_preserving h X

@[simp] theorem padInstrument_operation (J : E →ₗᵢ[ℂ] F) (P : Instrument I E H Ω)
    (h : H) (s : Set Ω) (X : Matrix I I ℂ) :
    (padInstrument J P).operation h s X = padNuclear J (P.operation h s X) := rfl

theorem recover_padInstrument_operation (J : E →ₗᵢ[ℂ] F) (P : Instrument I E H Ω)
    (h : H) (s : Set Ω) (X : Matrix I I ℂ) :
    recoverNuclear J ((padInstrument J P).operation h s X) = P.operation h s X :=
  recover_padNuclear J _

theorem trace_physicalChoi_padInstrument (J : E →ₗᵢ[ℂ] F) (P : Instrument I E H Ω)
    (h : H) (s : Set Ω) :
    QuantumProver.HilbertNuclearTrace.trace ((padInstrument J P).physicalChoi h s) =
      QuantumProver.HilbertNuclearTrace.trace (P.physicalChoi h s) := by
  rw [Instrument.trace_physicalChoi, Instrument.trace_physicalChoi,
    padInstrument_operation, trace_padNuclear]

theorem referenceKernel_padInstrument [Nonempty I]
    (J : E →ₗᵢ[ℂ] F) (P : Instrument I E H Ω) :
    (padInstrument J P).referenceKernel = P.referenceKernel := by
  ext h s hs
  rw [Instrument.referenceKernel_apply, Instrument.referenceKernel_apply,
    Instrument.referenceMeasure_apply _ h s hs, Instrument.referenceMeasure_apply _ h s hs]
  unfold Instrument.referenceMass
  rw [trace_physicalChoi_padInstrument]

end QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
