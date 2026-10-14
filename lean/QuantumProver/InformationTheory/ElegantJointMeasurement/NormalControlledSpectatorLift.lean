import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalRecordedConvergence
import QuantumProver.QuantumChannels.NormalRightTensor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter Set InnerProductSpace
open scoped BigOperators Topology ComplexOrder InnerProductSpace

namespace QuantumProver.ElegantJointMeasurement.NormalControlledSpectatorLift

open QuantumProver.NuclearOperator QuantumProver.HilbertNuclearCompression
open QuantumProver.MatrixNuclearTensor QuantumProver.MatrixNormalTensorExtension
open QuantumProver.MatrixNormalTensorInstrument QuantumProver.MatrixNormalRightTensor
open QuantumProver.MatrixHilbertSwap
open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalSandwich
open QuantumProver.ElegantJointMeasurement.NormalRecordedAbsorption QuantumProver.ElegantJointMeasurement.HilbertRecordedHilbertInstrument
open QuantumProver.ElegantJointMeasurement.NormalRecordedConvergence QuantumProver.ElegantJointMeasurement.MeasurableHilbertField

variable {E F V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

local instance blockComplete {I : Type} [Fintype I]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    CompleteSpace (BlockSpace I K) := PiLp.completeSpace 2 (fun _ : I => K)

local instance nuclearNormedGroup {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] : NormedAddCommGroup (Nuc K) := inferInstance

local instance nuclearNormedSpace {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] : NormedSpace ℂ (Nuc K) := inferInstance

def spectatorKet (v : V) : E →L[ℂ] Joint E V := tmulJoint.flip v

@[simp] theorem spectatorKet_apply (v : V) (x : E) :
    spectatorKet v x = tmulJoint x v := rfl

theorem spectatorKet_adjoint_tmul (v w : V) (x : E) :
    (spectatorKet (E := E) v).adjoint (tmulJoint x w) = inner ℂ v w • x := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [spectatorKet_apply, QuantumProver.MatrixNuclearTensor.inner_tmulJoint, inner_smul_right]
  ring

def spectatorSlice (v : V) : NormalOperation (Joint E V) E :=
  sandwich (spectatorKet (E := E) v).adjoint

theorem spectatorSlice_tensor (v : V) (T : Nuc E) (S : Nuc V) :
    spectatorSlice v (tensorNuclear T S) = inner ℂ v (toOperator S v) • T := by
  apply toOperator_injective
  ext x
  simp only [spectatorSlice, toOperator_sandwich, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_adjoint, spectatorKet_apply, toOperator_tensorNuclear,
    tensorMap_tmul, spectatorKet_adjoint_tmul, map_smul, ContinuousLinearMap.smul_apply]

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

theorem spectatorSlice_tensorOperation
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E F H Ω)
    (h : H) (s : Set Ω) (hs : MeasurableSet s) (v : V) :
    (spectatorSlice (E := F) v).comp (tensorOperation (G := V) P h s) =
      (P.operation h s).comp (spectatorSlice (E := E) v) := by
  apply nuclear_joint_clm_ext_tensors
  intro T S
  simp only [ContinuousLinearMap.comp_apply]
  rw [tensorOperation_tensor P h s hs, spectatorSlice_tensor, spectatorSlice_tensor,
    map_smul]

variable {I : Type} [Fintype I] [DecidableEq I]

def amplifiedSlice (v : V) :
    Nuc (BlockSpace I (Joint E V)) →L[ℂ] Nuc (BlockSpace I E) :=
  normalAmplification (R := I) (spectatorSlice v)

theorem amplifiedSlice_eq_compose (v : V) (T : Nuc (BlockSpace I (Joint E V))) :
    amplifiedSlice v T =
      compose (blockLift (R := I) (spectatorKet (E := E) v)).adjoint
        (blockLift (R := I) (spectatorKet (E := E) v)) T := by
  simpa only [amplifiedSlice, spectatorSlice, blockLift_adjoint,
    ContinuousLinearMap.adjoint_adjoint] using
      normalAmplification_sandwich (R := I) (spectatorKet (E := E) v).adjoint T

theorem amplifiedSlice_isPositive (v : V) (T : Nuc (BlockSpace I (Joint E V)))
    (hT : (toOperator T).IsPositive) : (toOperator (amplifiedSlice v T)).IsPositive :=
  normalCompletelyPositive_sandwich (spectatorKet (E := E) v).adjoint I T hT

theorem amplifiedSlice_tensorOperation
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E F H Ω)
    (h : H) (s : Set Ω) (hs : MeasurableSet s) (v : V)
    (T : Nuc (BlockSpace I (Joint E V))) :
    amplifiedSlice v (normalAmplification (R := I) (tensorOperation (G := V) P h s) T) =
      normalAmplification (R := I) (P.operation h s) (amplifiedSlice v T) := by
  change normalAmplification (R := I) (spectatorSlice (E := F) v)
    (normalAmplification (R := I) (tensorOperation (G := V) P h s) T) = _
  rw [← normalAmplification_comp, spectatorSlice_tensorOperation P h s hs v,
    normalAmplification_comp]
  rfl

section FiniteControlledDensity

variable {G : H × Ω → Type*}
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]
variable (Q : FundamentalFamily G) (P : RecordedNormalInstrument E Q)
variable [Nonempty I]

theorem normalRecordedExpectation_zero (h : H) (U : Nuc (BlockSpace I E))
    (hU : (toOperator U).IsPositive) :
    normalRecordedExpectation P.represented_physical h U hU (fun _ => 0) = 0 := by
  have ht : Tendsto (QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := I))
      (fun v => normalProbe P.represented_physical h U hU v) (fun _ => 0))
      atTop (𝓝 (0 : ℂ)) := by
    have heq : QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest (commonBlockBasis (I := I))
        (fun v => normalProbe P.represented_physical h U hU v) (fun _ => 0) =
          (fun _ : ℕ => (0 : ℂ)) := by
      funext n
      simp [QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawFiniteTest,
        QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.rawPairTest]
    rw [heq]
    exact tendsto_const_nhds
  exact ht.limUnder_eq

theorem normalRecordedExpectation_complement_zero (h : H)
    (U : Nuc (BlockSpace I E)) (hU : (toOperator U).IsPositive) :
    normalRecordedExpectation P.represented_physical h U hU (outputComplement (I := I) Q h) = 0 := by
  have h := P.controlled_output I h U hU (outputComplement (I := I) Q h)
    (outputComplement_isRecordedObservable Q h)
  rw [controlledObservable_complement_eq_zero] at h
  exact h.trans (normalRecordedExpectation_zero Q P _ _ _)

theorem finite_density_supported (h : H) (U : Nuc (BlockSpace I E))
    (hU : (toOperator U).IsPositive) (μ : Measure Ω)
    (D : Ω → Nuc (RecordedSpace I)) (hD : StronglyMeasurable D)
    (hInt : Integrable D μ) (hPos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive)
    (hSet : ∀ s, MeasurableSet s → ∫ ω in s, D ω ∂μ = normalResponse P.represented_physical h U s) :
    ∀ᵐ ω ∂μ, compose (outputProjection Q h ω) (outputProjection Q h ω) (D ω) = D ω := by
  have hκ (v : RecordedSpace I) (s : Set Ω) (hs : MeasurableSet s) :
      (normalProbe P.represented_physical h U hU v s).toReal =
        (inner ℂ v (toOperator (normalResponse P.represented_physical h U s) v)).re := by
    rw [normalProbe_apply P.represented_physical h U hU v s hs]
    exact ENNReal.toReal_ofReal
      ((normalResponse_isPositive P.represented_physical h U hU s hs).re_inner_nonneg_right v)
  have hRaw := normalFiniteTest_tendsto_normalRecordedExpectation P.represented_physical h U hU
    (outputComplement (I := I) Q h) (outputComplement_isRecordedObservable Q h)
  rw [normalRecordedExpectation_complement_zero Q P h U hU] at hRaw
  have hZero : (∫ ω, (QuantumProver.HilbertNuclearTrace.trace
      (compose (outputComplement (I := I) Q h ω)
        (outputComplement (I := I) Q h ω) (D ω))).re ∂μ) = 0 :=
    QuantumProver.ElegantJointMeasurement.HilbertControlledNuclearTest.complement_integral_eq_zero_of_raw_response_zero
    (H := RecordedSpace I) (Ω := Ω) (μ := μ)
    (commonBlockBasis (I := I)) (normalResponse P.represented_physical h U)
    (fun v => normalProbe P.represented_physical h U hU v) D hInt hPos hSet hκ
    (outputProjection (I := I) Q h) (stronglyMeasurable_outputProjection_apply Q h)
    (outputProjection_idempotent Q h) (C := 1) zero_le_one
    (norm_outputComplement_le_one Q h) hRaw
  exact QuantumProver.ElegantJointMeasurement.NuclearFieldSupport.ae_projection_sandwich_eq_of_integral_complementTrace_eq_zero
    (H := RecordedSpace I) (Ω := Ω)
    μ (outputProjection Q h) (outputProjection_adjoint Q h)
    (outputProjection_idempotent Q h) (stronglyMeasurable_outputProjection_apply Q h)
    D hD hInt hPos hZero

end FiniteControlledDensity

section SpectatorSupportReconstruction

theorem normalAmplification_selfadjoint_compose (L : E →L[ℂ] E)
    (hL : L.adjoint = L) (T : Nuc (BlockSpace I E)) :
    normalAmplification (R := I) (compose L L) T =
      compose (blockLift (R := I) L) (blockLift (R := I) L) T := by
  simpa only [sandwich, hL, blockLift_adjoint] using
    normalAmplification_sandwich (R := I) L T

theorem spectatorSlice_local_compose (v : V) (L R : E →L[ℂ] E) :
    (spectatorSlice (E := E) v).comp
      (compose (tensorMap L (ContinuousLinearMap.id ℂ V))
        (tensorMap R (ContinuousLinearMap.id ℂ V))) =
      (compose L R).comp (spectatorSlice (E := E) v) := by
  apply nuclear_joint_clm_ext_tensors
  intro T S
  simp only [ContinuousLinearMap.comp_apply]
  rw [← tensorNuclear_compose, compose_id_id_apply, spectatorSlice_tensor,
    spectatorSlice_tensor, map_smul]

def localLift (L : E →L[ℂ] E) :
    BlockSpace I (Joint E V) →L[ℂ] BlockSpace I (Joint E V) :=
  blockLift (R := I) (tensorMap L (ContinuousLinearMap.id ℂ V))

theorem localLift_adjoint (L : E →L[ℂ] E) (hL : L.adjoint = L) :
    (localLift (I := I) (V := V) L).adjoint = localLift L := by
  simp only [localLift, blockLift_adjoint, tensorMap_adjoint, hL,
    ContinuousLinearMap.adjoint_id]

theorem localLift_idempotent (L : E →L[ℂ] E) (hL : L.comp L = L) :
    (localLift (I := I) (V := V) L).comp (localLift L) = localLift L := by
  ext x i
  change tensorMap L (ContinuousLinearMap.id ℂ V)
    (tensorMap L (ContinuousLinearMap.id ℂ V) (x i)) =
      tensorMap L (ContinuousLinearMap.id ℂ V) (x i)
  have ht := tensorMap_comp L L (ContinuousLinearMap.id ℂ V)
    (ContinuousLinearMap.id ℂ V)
  rw [hL, ContinuousLinearMap.id_comp] at ht
  exact congrArg (fun A => A (x i)) ht.symm

theorem localLift_complement (L : E →L[ℂ] E) :
    localLift (I := I) (V := V) (ContinuousLinearMap.id ℂ E - L) =
      ContinuousLinearMap.id ℂ (BlockSpace I (Joint E V)) - localLift L := by
  have ht : tensorMap (ContinuousLinearMap.id ℂ E - L)
      (ContinuousLinearMap.id ℂ V) =
        ContinuousLinearMap.id ℂ (Joint E V) -
          tensorMap L (ContinuousLinearMap.id ℂ V) := by
    apply joint_clm_ext
    intro x v
    simp only [tensorMap_tmul, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, map_sub]
  ext x i
  simpa only [localLift, blockLift_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, WithLp.ofLp_sub, Pi.sub_apply]
    using congrArg (fun A => A (x i)) ht

theorem amplifiedSlice_local_compose (v : V) (L : E →L[ℂ] E)
    (hL : L.adjoint = L) (T : Nuc (BlockSpace I (Joint E V))) :
    amplifiedSlice v (compose (localLift L) (localLift L) T) =
      compose (blockLift (R := I) L) (blockLift (R := I) L) (amplifiedSlice v T) := by
  have hJoint : (tensorMap L (ContinuousLinearMap.id ℂ V)).adjoint =
      tensorMap L (ContinuousLinearMap.id ℂ V) := by
    simp only [tensorMap_adjoint, hL, ContinuousLinearMap.adjoint_id]
  rw [localLift, ← normalAmplification_selfadjoint_compose _ hJoint]
  change normalAmplification (R := I) (spectatorSlice (E := E) v)
    (normalAmplification (R := I)
      (compose (tensorMap L (ContinuousLinearMap.id ℂ V))
        (tensorMap L (ContinuousLinearMap.id ℂ V))) T) = _
  rw [← normalAmplification_comp, spectatorSlice_local_compose,
    normalAmplification_comp, normalAmplification_selfadjoint_compose _ hL]
  rfl

theorem positive_operator_sqrt_factor (A : E →L[ℂ] E) (hA : A.IsPositive) :
    ∃ S : E →L[ℂ] E, S.adjoint = S ∧ S.comp S = A :=
  ⟨CFC.sqrt A, sqrt_adjoint_eq A, sqrt_comp_sqrt A hA⟩

theorem positive_nuclear_eq_zero_of_amplifiedSlices_eq_zero
    {J : Type*} (b : HilbertBasis J ℂ V)
    (T : Nuc (BlockSpace I (Joint E V))) (hT : (toOperator T).IsPositive)
    (hSlices : ∀ j, amplifiedSlice (I := I) (b j) T = 0) : T = 0 := by
  classical
  let A : BlockSpace I (Joint E V) →L[ℂ] BlockSpace I (Joint E V) := toOperator T
  obtain ⟨S, hSAdj, hSS⟩ := positive_operator_sqrt_factor A hT
  have hKet (j : J) :
      S.comp (blockLift (R := I) (spectatorKet (E := E) (b j))) = 0 := by
    have hz := congrArg (toOperator (𝕜 := ℂ) (E := BlockSpace I E)
      (F := BlockSpace I E)) (hSlices j)
    rw [amplifiedSlice_eq_compose, toOperator_compose, map_zero] at hz
    have hGram :
        (S.comp (blockLift (R := I) (spectatorKet (E := E) (b j)))).adjoint.comp
          (S.comp (blockLift (R := I) (spectatorKet (E := E) (b j)))) = 0 := by
      rw [ContinuousLinearMap.adjoint_comp, hSAdj]
      calc
        _ = (blockLift (R := I) (spectatorKet (E := E) (b j))).adjoint.comp
            ((S.comp S).comp (blockLift (R := I) (spectatorKet (E := E) (b j)))) := by
          simp only [ContinuousLinearMap.comp_assoc]
        _ = 0 := by
          rw [hSS]
          simpa only [ContinuousLinearMap.comp_assoc] using hz
    exact ContinuousLinearMap.adjoint_comp_self_eq_zero_iff.mp hGram
  have hPure (i : I) (x : E) (v : V) : S (insert i (tmulJoint x v)) = 0 := by
    let L : V →L[ℂ] BlockSpace I (Joint E V) :=
      S.comp ((insert (E := Joint E V) i).comp (tmulJoint x))
    have hb (j : J) : L (b j) = 0 := by
      have hj := congrArg (fun M => M (insert i x)) (hKet j)
      have hk : blockLift (R := I) (spectatorKet (E := E) (b j)) (insert i x) =
          insert i (tmulJoint x (b j)) := by
        ext r
        by_cases hr : r = i
        · subst r
          simp [blockLift_apply, insert_apply_apply, spectatorKet_apply]
        · simp [blockLift_apply, insert_apply_apply, hr, spectatorKet_apply]
      simpa only [ContinuousLinearMap.comp_apply, hk,
        ContinuousLinearMap.zero_apply, L] using hj
    have hv := (b.hasSum_repr v).mapL L
    simp only [map_smul, hb, smul_zero] at hv
    exact (HasSum.unique hv (hasSum_zero : HasSum (fun _ : J =>
      (0 : BlockSpace I (Joint E V))) 0))
  have hInsert (i : I) : S.comp (insert (E := Joint E V) i) = 0 := by
    apply joint_clm_ext
    intro x v
    exact hPure i x v
  have hS : S = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change S x = 0
    have hx : (∑ i : I, insert (E := Joint E V) i (x i)) = x := by
      ext i
      simp [insert_apply_apply]
    rw [← hx, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    exact congrArg (fun L => L (x i)) (hInsert i)
  apply toOperator_injective
  change A = toOperator (0 : Nuc (BlockSpace I (Joint E V)))
  rw [← hSS, hS, ContinuousLinearMap.zero_comp, map_zero]

theorem complement_sandwich_eq_zero_of_supported (L : E →L[ℂ] E)
    (hL : L.comp L = L) (T : Nuc E) (hT : compose L L T = T) :
    compose (ContinuousLinearMap.id ℂ E - L)
      (ContinuousLinearMap.id ℂ E - L) T = 0 := by
  have hLeft : (ContinuousLinearMap.id ℂ E - L).comp L = 0 := by
    ext x
    have hx := congrArg (fun A => A x) hL
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply] at hx ⊢
    simpa only [ContinuousLinearMap.zero_apply] using sub_eq_zero.mpr hx.symm
  apply toOperator_injective
  rw [← hT, toOperator_compose, toOperator_compose]
  simp only [← ContinuousLinearMap.comp_assoc, hLeft,
    ContinuousLinearMap.zero_comp, map_zero]

theorem local_supported_of_amplifiedSlices_supported
    {J : Type*} (b : HilbertBasis J ℂ V)
    (L : E →L[ℂ] E) (hAdj : L.adjoint = L) (hId : L.comp L = L)
    (T : Nuc (BlockSpace I (Joint E V))) (hPos : (toOperator T).IsPositive)
    (hSlices : ∀ j, compose (blockLift (R := I) L) (blockLift (R := I) L)
      (amplifiedSlice (b j) T) = amplifiedSlice (b j) T) :
    compose (localLift L) (localLift L) T = T := by
  let C := compose (ContinuousLinearMap.id ℂ _ - localLift (I := I) (V := V) L)
    (ContinuousLinearMap.id ℂ _ - localLift (I := I) (V := V) L) T
  have hCompAdj : (ContinuousLinearMap.id ℂ E - L).adjoint =
      ContinuousLinearMap.id ℂ E - L := by simp [hAdj]
  have hCPos : (toOperator C).IsPositive := by
    exact QuantumProver.ElegantJointMeasurement.NuclearProjectionSupport.nuclear_sandwich_isPositive T _ hPos
      (by simp [localLift_adjoint L hAdj])
  have hZero : C = 0 := by
    apply positive_nuclear_eq_zero_of_amplifiedSlices_eq_zero b C hCPos
    intro j
    change amplifiedSlice (b j)
      (compose (ContinuousLinearMap.id ℂ _ - localLift L)
        (ContinuousLinearMap.id ℂ _ - localLift L) T) = 0
    rw [← localLift_complement, amplifiedSlice_local_compose _ _ hCompAdj]
    have hLiftId : (blockLift (R := I) L).comp (blockLift (R := I) L) =
        blockLift (R := I) L := by
      ext x i
      exact congrArg (fun A => A (x i)) hId
    have hCompLift : blockLift (R := I) (ContinuousLinearMap.id ℂ E - L) =
        ContinuousLinearMap.id ℂ (BlockSpace I E) - blockLift L := by
      ext x i
      rfl
    rw [hCompLift]
    exact complement_sandwich_eq_zero_of_supported _ hLiftId _ (hSlices j)
  apply QuantumProver.ElegantJointMeasurement.NuclearProjectionSupport.projection_sandwich_eq_of_re_complement_trace_eq_zero
    T (localLift L) hPos (localLift_adjoint L hAdj) (localLift_idempotent L hId)
  change (QuantumProver.HilbertNuclearTrace.trace C).re = 0
  simp only [hZero, map_zero, Complex.zero_re]

end SpectatorSupportReconstruction

section LeftControlledDensity

variable {G : H × Ω → Type*}
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]
variable (Q : FundamentalFamily G) (P : RecordedNormalInstrument E Q)
variable [Nonempty I] [TopologicalSpace.SeparableSpace V]

theorem left_density_supported_strong (h : H)
    (U : Nuc (BlockSpace I (Joint E V))) (hU : (toOperator U).IsPositive)
    (μ : Measure Ω) (D : Ω → Nuc (BlockSpace I (Joint CommonHilbert V)))
    (hD : StronglyMeasurable D) (hInt : Integrable D μ)
    (hPos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive)
    (hSet : ∀ s, MeasurableSet s → ∫ ω in s, D ω ∂μ =
      normalAmplification (R := I) (tensorOperation (G := V) P.represented_physical h s) U) :
    ∀ᵐ ω ∂μ, compose (localLift (I := I) (V := V) (Q.rangeProjection (h, ω)))
      (localLift (I := I) (V := V) (Q.rangeProjection (h, ω))) (D ω) = D ω := by
  classical
  obtain ⟨J, b, hb⟩ := exists_hilbertBasis ℂ V
  letI : Countable J := countable_of_orthonormal b.orthonormal
  have hFinite (j : J) : ∀ᵐ ω ∂μ,
      compose (outputProjection (I := I) Q h ω) (outputProjection Q h ω)
        (amplifiedSlice (b j) (D ω)) = amplifiedSlice (b j) (D ω) := by
    apply finite_density_supported Q P h (amplifiedSlice (b j) U)
      (amplifiedSlice_isPositive _ _ hU) μ
      (fun ω => amplifiedSlice (b j) (D ω))
      ((amplifiedSlice (E := CommonHilbert) (I := I) (b j)).continuous.comp_stronglyMeasurable hD)
      ((amplifiedSlice (E := CommonHilbert) (I := I) (b j)).integrable_comp hInt)
    · filter_upwards [hPos] with ω hω
      exact amplifiedSlice_isPositive _ _ hω
    · intro s hs
      rw [(amplifiedSlice (E := CommonHilbert) (I := I) (b j)).integral_comp_comm
        hInt.integrableOn, hSet s hs, amplifiedSlice_tensorOperation P.represented_physical h s hs]
      rfl
  filter_upwards [ae_all_iff.mpr hFinite, hPos] with ω hω hωPos
  apply local_supported_of_amplifiedSlices_supported b _
    (QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument.inputProjection_adjoint Q (h, ω))
    (QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument.inputProjection_idempotent Q (h, ω)) (D ω) hωPos
  exact hω

theorem left_density_supported (h : H)
    (U : Nuc (BlockSpace I (Joint E V))) (hU : (toOperator U).IsPositive)
    (μ : Measure Ω) (D : Ω → Nuc (BlockSpace I (Joint CommonHilbert V)))
    (hInt : Integrable D μ) (hPos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive)
    (hSet : ∀ s, MeasurableSet s → ∫ ω in s, D ω ∂μ =
      normalAmplification (R := I) (tensorOperation (G := V) P.represented_physical h s) U) :
    ∀ᵐ ω ∂μ, compose (localLift (I := I) (V := V) (Q.rangeProjection (h, ω)))
      (localLift (I := I) (V := V) (Q.rangeProjection (h, ω))) (D ω) = D ω := by
  let D₀ := hInt.aestronglyMeasurable.mk D
  have heq : D =ᵐ[μ] D₀ := hInt.aestronglyMeasurable.ae_eq_mk
  have hInt₀ : Integrable D₀ μ := hInt.congr heq
  have hPos₀ : ∀ᵐ ω ∂μ, (toOperator (D₀ ω)).IsPositive := by
    filter_upwards [hPos, heq] with ω hω heω
    simpa only [← heω] using hω
  have hSet₀ : ∀ s, MeasurableSet s → ∫ ω in s, D₀ ω ∂μ =
      normalAmplification (R := I) (tensorOperation (G := V) P.represented_physical h s) U := by
    intro s hs
    rw [integral_congr_ae (ae_restrict_of_ae heq.symm), hSet s hs]
  have h := left_density_supported_strong Q P h U hU μ D₀
    hInt.aestronglyMeasurable.stronglyMeasurable_mk hInt₀ hPos₀ hSet₀
  filter_upwards [h, heq] with ω hω heω
  simpa only [← heω] using hω

end LeftControlledDensity

section RemoteSupport

def remoteLift (R : V →L[ℂ] V) :
    BlockSpace I (Joint E V) →L[ℂ] BlockSpace I (Joint E V) :=
  blockLift (R := I) (tensorMap (ContinuousLinearMap.id ℂ E) R)

theorem tensorOperation_remote_compose
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E F H Ω)
    (h : H) (s : Set Ω) (hs : MeasurableSet s) (L R : V →L[ℂ] V) :
    (tensorOperation (G := V) P h s).comp
      (compose (tensorMap (ContinuousLinearMap.id ℂ E) L)
        (tensorMap (ContinuousLinearMap.id ℂ E) R)) =
      (compose (tensorMap (ContinuousLinearMap.id ℂ F) L)
        (tensorMap (ContinuousLinearMap.id ℂ F) R)).comp
          (tensorOperation (G := V) P h s) := by
  apply nuclear_joint_clm_ext_tensors
  intro T S
  simp only [ContinuousLinearMap.comp_apply]
  rw [← tensorNuclear_compose, compose_id_id_apply, tensorOperation_tensor P h s hs,
    tensorOperation_tensor P h s hs]
  simpa only [compose_id_id_apply] using
    tensorNuclear_compose (ContinuousLinearMap.id ℂ F) (ContinuousLinearMap.id ℂ F)
      L R (P.operation h s T) S

theorem amplified_tensorOperation_remote_compose
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E F H Ω)
    (h : H) (s : Set Ω) (hs : MeasurableSet s)
    (R : V →L[ℂ] V) (hR : R.adjoint = R) (U : Nuc (BlockSpace I (Joint E V))) :
    normalAmplification (R := I) (tensorOperation (G := V) P h s)
      (compose (remoteLift R) (remoteLift R) U) =
      compose (remoteLift R) (remoteLift R)
        (normalAmplification (R := I) (tensorOperation (G := V) P h s) U) := by
  have hIn : (tensorMap (ContinuousLinearMap.id ℂ E) R).adjoint =
      tensorMap (ContinuousLinearMap.id ℂ E) R := by simp [tensorMap_adjoint, hR]
  have hOut : (tensorMap (ContinuousLinearMap.id ℂ F) R).adjoint =
      tensorMap (ContinuousLinearMap.id ℂ F) R := by simp [tensorMap_adjoint, hR]
  rw [remoteLift, ← normalAmplification_selfadjoint_compose _ hIn,
    ← normalAmplification_comp, tensorOperation_remote_compose P h s hs R R,
    normalAmplification_comp, normalAmplification_selfadjoint_compose _ hOut]
  rfl

theorem left_event_remote_supported
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E F H Ω)
    (h : H) (s : Set Ω) (hs : MeasurableSet s)
    (R : V →L[ℂ] V) (hR : R.adjoint = R)
    (U : Nuc (BlockSpace I (Joint E V)))
    (hSupport : compose (remoteLift R) (remoteLift R) U = U) :
    compose (remoteLift R) (remoteLift R)
      (normalAmplification (R := I) (tensorOperation (G := V) P h s) U) =
        normalAmplification (R := I) (tensorOperation (G := V) P h s) U := by
  rw [← amplified_tensorOperation_remote_compose P h s hs R hR, hSupport]

theorem left_density_remote_supported
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E F H Ω)
    (h : H) (R : V →L[ℂ] V) (hR : R.adjoint = R)
    (U : Nuc (BlockSpace I (Joint E V)))
    (hSupport : compose (remoteLift R) (remoteLift R) U = U)
    (μ : Measure Ω) (D : Ω → Nuc (BlockSpace I (Joint F V))) (hInt : Integrable D μ)
    (hSet : ∀ s, MeasurableSet s → ∫ ω in s, D ω ∂μ =
      normalAmplification (R := I) (tensorOperation (G := V) P h s) U) :
    ∀ᵐ ω ∂μ, compose (remoteLift R) (remoteLift R) (D ω) = D ω := by
  let L : Nuc (BlockSpace I (Joint F V)) →L[ℂ] Nuc (BlockSpace I (Joint F V)) :=
    compose (remoteLift (E := F) (I := I) R) (remoteLift (E := F) (I := I) R)
  change ∀ᵐ ω ∂μ, L (D ω) = D ω
  apply Integrable.ae_eq_of_forall_setIntegral_eq (fun ω => L (D ω)) D
    (L.integrable_comp hInt) hInt
  intro s hs hFinite
  rw [L.integral_comp_comm hInt.integrableOn, hSet s hs]
  exact left_event_remote_supported P h s hs R hR U hSupport

theorem compose_nested (L R L' R' : E →L[ℂ] E) (T : Nuc E) :
    compose L R (compose L' R' T) = compose (L.comp L') (R'.comp R) T := by
  apply toOperator_injective
  simp only [toOperator_compose, ContinuousLinearMap.comp_assoc]

theorem combinedLift_factor_left (Q : E →L[ℂ] E) (R : V →L[ℂ] V) :
    blockLift (R := I) (tensorMap Q R) =
      (localLift (I := I) (V := V) Q).comp (remoteLift (E := E) (I := I) R) := by
  ext x i
  have ht := tensorMap_comp Q (ContinuousLinearMap.id ℂ E)
    (ContinuousLinearMap.id ℂ V) R
  simp only [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp] at ht
  exact congrArg (fun A => A (x i)) ht

theorem combinedLift_factor_right (Q : E →L[ℂ] E) (R : V →L[ℂ] V) :
    blockLift (R := I) (tensorMap Q R) =
      (remoteLift (E := E) (I := I) R).comp (localLift (I := I) (V := V) Q) := by
  ext x i
  have ht := tensorMap_comp (ContinuousLinearMap.id ℂ E) Q R
    (ContinuousLinearMap.id ℂ V)
  simp only [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp] at ht
  exact congrArg (fun A => A (x i)) ht

theorem combined_supported_of_local_remote (Q : E →L[ℂ] E) (R : V →L[ℂ] V)
    (T : Nuc (BlockSpace I (Joint E V)))
    (hLocal : compose (localLift Q) (localLift Q) T = T)
    (hRemote : compose (remoteLift R) (remoteLift R) T = T) :
    compose (blockLift (R := I) (tensorMap Q R))
      (blockLift (R := I) (tensorMap Q R)) T = T := by
  have hn := compose_nested (localLift (I := I) (V := V) Q) (localLift Q)
    (remoteLift (E := E) R) (remoteLift R) T
  rw [← combinedLift_factor_left, ← combinedLift_factor_right] at hn
  rw [← hn, hRemote, hLocal]

end RemoteSupport

section LeftCombinedDensity

variable {G : H × Ω → Type*}
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]
variable (Q : FundamentalFamily G) (P : RecordedNormalInstrument E Q)
variable [Nonempty I] [TopologicalSpace.SeparableSpace V]

theorem left_density_combined_supported (h : H)
    (R : V →L[ℂ] V) (hR : R.adjoint = R)
    (U : Nuc (BlockSpace I (Joint E V))) (hU : (toOperator U).IsPositive)
    (hSupport : compose (remoteLift R) (remoteLift R) U = U)
    (μ : Measure Ω) (D : Ω → Nuc (BlockSpace I (Joint CommonHilbert V)))
    (hInt : Integrable D μ) (hPos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive)
    (hSet : ∀ s, MeasurableSet s → ∫ ω in s, D ω ∂μ =
      normalAmplification (R := I) (tensorOperation (G := V) P.represented_physical h s) U) :
    ∀ᵐ ω ∂μ, compose (blockLift (R := I) (tensorMap (Q.rangeProjection (h, ω)) R))
      (blockLift (R := I) (tensorMap (Q.rangeProjection (h, ω)) R)) (D ω) = D ω := by
  filter_upwards [left_density_supported Q P h U hU μ D hInt hPos hSet,
    left_density_remote_supported P.represented_physical h R hR U hSupport μ D hInt hSet]
    with ω hLocal hRemote
  exact combined_supported_of_local_remote _ R (D ω) hLocal hRemote

end LeftCombinedDensity

section AmplifiedSwap

def amplifiedSwap (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :
    Nuc (BlockSpace I (Joint E F)) →L[ℂ] Nuc (BlockSpace I (Joint F E)) :=
  normalAmplification (R := I) (nuclearSwap E F)

theorem amplifiedSwap_isPositive (T : Nuc (BlockSpace I (Joint E F)))
    (hT : (toOperator T).IsPositive) :
    (toOperator (amplifiedSwap (I := I) E F T)).IsPositive :=
  nuclearSwap_completelyPositive I T hT

@[simp] theorem amplifiedSwap_involutive (T : Nuc (BlockSpace I (Joint E F))) :
    amplifiedSwap (I := I) F E (amplifiedSwap E F T) = T := by
  have hid : (nuclearSwap F E).comp (nuclearSwap E F) =
      ContinuousLinearMap.id ℂ (Nuc (Joint E F)) := by
    ext U
    exact nuclearSwap_involutive U
  change normalAmplification (R := I) (nuclearSwap F E)
    (normalAmplification (R := I) (nuclearSwap E F) T) = T
  rw [← normalAmplification_comp, hid, normalAmplification_apply]
  simpa only [ContinuousLinearMap.id_apply] using nuclearAssembly_nuclearBlock T

theorem nuclearSwap_local_compose (L R : E →L[ℂ] E) :
    (nuclearSwap E V).comp
      (compose (tensorMap L (ContinuousLinearMap.id ℂ V))
        (tensorMap R (ContinuousLinearMap.id ℂ V))) =
      (compose (tensorMap (ContinuousLinearMap.id ℂ V) L)
        (tensorMap (ContinuousLinearMap.id ℂ V) R)).comp (nuclearSwap E V) := by
  apply nuclear_joint_clm_ext_tensors
  intro T S
  simp only [ContinuousLinearMap.comp_apply]
  rw [← tensorNuclear_compose, compose_id_id_apply, nuclearSwap_tensor, nuclearSwap_tensor]
  simpa only [compose_id_id_apply] using
    tensorNuclear_compose (ContinuousLinearMap.id ℂ V) (ContinuousLinearMap.id ℂ V)
      L R S T

theorem amplifiedSwap_local_compose (L : E →L[ℂ] E) (hL : L.adjoint = L)
    (T : Nuc (BlockSpace I (Joint E V))) :
    amplifiedSwap (I := I) E V (compose (localLift L) (localLift L) T) =
      compose (remoteLift (E := V) L) (remoteLift (E := V) L)
        (amplifiedSwap E V T) := by
  have hIn : (tensorMap L (ContinuousLinearMap.id ℂ V)).adjoint =
      tensorMap L (ContinuousLinearMap.id ℂ V) := by simp [tensorMap_adjoint, hL]
  have hOut : (tensorMap (ContinuousLinearMap.id ℂ V) L).adjoint =
      tensorMap (ContinuousLinearMap.id ℂ V) L := by simp [tensorMap_adjoint, hL]
  rw [localLift, ← normalAmplification_selfadjoint_compose _ hIn]
  change normalAmplification (R := I) (nuclearSwap E V)
    (normalAmplification (R := I) (compose (tensorMap L (ContinuousLinearMap.id ℂ V))
      (tensorMap L (ContinuousLinearMap.id ℂ V))) T) = _
  rw [← normalAmplification_comp, nuclearSwap_local_compose,
    normalAmplification_comp, normalAmplification_selfadjoint_compose _ hOut]
  rfl

theorem amplifiedSwap_rightTensorOperation
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E F H Ω)
    (h : H) (s : Set Ω) (T : Nuc (BlockSpace I (Joint V E))) :
    amplifiedSwap (I := I) V F
      (normalAmplification (R := I) (rightTensorOperation (G := V) P h s) T) =
      normalAmplification (R := I) (tensorOperation (G := V) P h s)
        (amplifiedSwap V E T) := by
  rw [rightTensorOperation, normalAmplification_comp, normalAmplification_comp]
  change amplifiedSwap (I := I) V F (amplifiedSwap F V
    (normalAmplification (R := I) (tensorOperation (G := V) P h s)
      (amplifiedSwap V E T))) = _
  rw [amplifiedSwap_involutive]

end AmplifiedSwap

section RightControlledDensity

variable {G : H × Ω → Type*}
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]
variable (Q : FundamentalFamily G) (P : RecordedNormalInstrument E Q)
variable [Nonempty I] [TopologicalSpace.SeparableSpace V]

theorem right_density_supported (h : H)
    (U : Nuc (BlockSpace I (Joint V E))) (hU : (toOperator U).IsPositive)
    (μ : Measure Ω) (D : Ω → Nuc (BlockSpace I (Joint V CommonHilbert)))
    (hInt : Integrable D μ) (hPos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive)
    (hSet : ∀ s, MeasurableSet s → ∫ ω in s, D ω ∂μ =
      normalAmplification (R := I) (rightTensorOperation (G := V) P.represented_physical h s) U) :
    ∀ᵐ ω ∂μ, compose (remoteLift (E := V) (I := I) (Q.rangeProjection (h, ω)))
      (remoteLift (E := V) (I := I) (Q.rangeProjection (h, ω))) (D ω) = D ω := by
  have hInt' : Integrable (fun ω => amplifiedSwap (I := I) V CommonHilbert (D ω)) μ :=
    (amplifiedSwap (I := I) V CommonHilbert).integrable_comp hInt
  have hPos' : ∀ᵐ ω ∂μ,
      (toOperator (amplifiedSwap (I := I) V CommonHilbert (D ω))).IsPositive := by
    filter_upwards [hPos] with ω hω
    exact amplifiedSwap_isPositive _ hω
  have hSet' : ∀ s, MeasurableSet s →
      ∫ ω in s, amplifiedSwap (I := I) V CommonHilbert (D ω) ∂μ =
        normalAmplification (R := I) (tensorOperation (G := V) P.represented_physical h s)
          (amplifiedSwap V E U) := by
    intro s hs
    rw [(amplifiedSwap (I := I) V CommonHilbert).integral_comp_comm hInt.integrableOn,
      hSet s hs, amplifiedSwap_rightTensorOperation]
  have hLeft := left_density_supported Q P h (amplifiedSwap (I := I) V E U)
    (amplifiedSwap_isPositive _ hU) μ
    (fun ω => amplifiedSwap (I := I) V CommonHilbert (D ω)) hInt' hPos' hSet'
  filter_upwards [hLeft] with ω hω
  have hx := congrArg (amplifiedSwap (I := I) CommonHilbert V) hω
  rw [amplifiedSwap_local_compose _
      (QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument.inputProjection_adjoint Q (h, ω)),
    amplifiedSwap_involutive] at hx
  exact hx

end RightControlledDensity

section RightRemoteSupport

theorem rightTensorOperation_remote_compose
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E F H Ω)
    (h : H) (s : Set Ω) (hs : MeasurableSet s) (L R : V →L[ℂ] V) :
    (rightTensorOperation (G := V) P h s).comp
      (compose (tensorMap L (ContinuousLinearMap.id ℂ E))
        (tensorMap R (ContinuousLinearMap.id ℂ E))) =
      (compose (tensorMap L (ContinuousLinearMap.id ℂ F))
        (tensorMap R (ContinuousLinearMap.id ℂ F))).comp
          (rightTensorOperation (G := V) P h s) := by
  apply nuclear_joint_clm_ext_tensors
  intro T S
  simp only [ContinuousLinearMap.comp_apply]
  rw [← tensorNuclear_compose, compose_id_id_apply, rightTensorOperation_tensor P h s hs,
    rightTensorOperation_tensor P h s hs]
  simpa only [compose_id_id_apply] using
    tensorNuclear_compose L R (ContinuousLinearMap.id ℂ F) (ContinuousLinearMap.id ℂ F)
      T (P.operation h s S)

theorem right_event_remote_supported
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E F H Ω)
    (h : H) (s : Set Ω) (hs : MeasurableSet s) (R : V →L[ℂ] V) (hR : R.adjoint = R)
    (U : Nuc (BlockSpace I (Joint V E)))
    (hSupport : compose (localLift (V := E) R) (localLift (V := E) R) U = U) :
    compose (localLift (V := F) R) (localLift (V := F) R)
      (normalAmplification (R := I) (rightTensorOperation (G := V) P h s) U) =
        normalAmplification (R := I) (rightTensorOperation (G := V) P h s) U := by
  have hIn : (tensorMap R (ContinuousLinearMap.id ℂ E)).adjoint =
      tensorMap R (ContinuousLinearMap.id ℂ E) := by simp [tensorMap_adjoint, hR]
  have hOut : (tensorMap R (ContinuousLinearMap.id ℂ F)).adjoint =
      tensorMap R (ContinuousLinearMap.id ℂ F) := by simp [tensorMap_adjoint, hR]
  have hComm : normalAmplification (R := I) (rightTensorOperation (G := V) P h s)
      (compose (localLift (V := E) R) (localLift (V := E) R) U) =
        compose (localLift (V := F) R) (localLift (V := F) R)
          (normalAmplification (R := I) (rightTensorOperation (G := V) P h s) U) := by
    rw [localLift, ← normalAmplification_selfadjoint_compose _ hIn,
      ← normalAmplification_comp, rightTensorOperation_remote_compose P h s hs R R,
      normalAmplification_comp, normalAmplification_selfadjoint_compose _ hOut]
    rfl
  rw [hSupport] at hComm
  exact hComm.symm

theorem right_density_remote_supported
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E F H Ω)
    (h : H) (R : V →L[ℂ] V) (hR : R.adjoint = R)
    (U : Nuc (BlockSpace I (Joint V E)))
    (hSupport : compose (localLift (V := E) R) (localLift (V := E) R) U = U)
    (μ : Measure Ω) (D : Ω → Nuc (BlockSpace I (Joint V F))) (hInt : Integrable D μ)
    (hSet : ∀ s, MeasurableSet s → ∫ ω in s, D ω ∂μ =
      normalAmplification (R := I) (rightTensorOperation (G := V) P h s) U) :
    ∀ᵐ ω ∂μ, compose (localLift (V := F) R) (localLift (V := F) R) (D ω) = D ω := by
  let L : Nuc (BlockSpace I (Joint V F)) →L[ℂ] Nuc (BlockSpace I (Joint V F)) :=
    compose (localLift (E := V) (V := F) (I := I) R)
      (localLift (E := V) (V := F) (I := I) R)
  change ∀ᵐ ω ∂μ, L (D ω) = D ω
  apply Integrable.ae_eq_of_forall_setIntegral_eq (fun ω => L (D ω)) D
    (L.integrable_comp hInt) hInt
  intro s hs hFinite
  rw [L.integral_comp_comm hInt.integrableOn, hSet s hs]
  exact right_event_remote_supported P h s hs R hR U hSupport

end RightRemoteSupport

section RightCombinedDensity

variable {G : H × Ω → Type*}
  [∀ z, NormedAddCommGroup (G z)] [∀ z, InnerProductSpace ℂ (G z)]
  [∀ z, CompleteSpace (G z)]
variable (Q : FundamentalFamily G) (P : RecordedNormalInstrument E Q)
variable [Nonempty I] [TopologicalSpace.SeparableSpace V]

theorem right_density_combined_supported (h : H)
    (R : V →L[ℂ] V) (hR : R.adjoint = R)
    (U : Nuc (BlockSpace I (Joint V E))) (hU : (toOperator U).IsPositive)
    (hSupport : compose (localLift (V := E) R) (localLift (V := E) R) U = U)
    (μ : Measure Ω) (D : Ω → Nuc (BlockSpace I (Joint V CommonHilbert)))
    (hInt : Integrable D μ) (hPos : ∀ᵐ ω ∂μ, (toOperator (D ω)).IsPositive)
    (hSet : ∀ s, MeasurableSet s → ∫ ω in s, D ω ∂μ =
      normalAmplification (R := I) (rightTensorOperation (G := V) P.represented_physical h s) U) :
    ∀ᵐ ω ∂μ, compose (blockLift (R := I) (tensorMap R (Q.rangeProjection (h, ω))))
      (blockLift (R := I) (tensorMap R (Q.rangeProjection (h, ω)))) (D ω) = D ω := by
  filter_upwards [right_density_supported Q P h U hU μ D hInt hPos hSet,
    right_density_remote_supported P.represented_physical h R hR U hSupport μ D hInt hSet]
    with ω hLocal hRemote
  exact combined_supported_of_local_remote R _ (D ω) hRemote hLocal

end RightCombinedDensity

end QuantumProver.ElegantJointMeasurement.NormalControlledSpectatorLift
