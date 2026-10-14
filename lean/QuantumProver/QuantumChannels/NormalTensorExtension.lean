import QuantumProver.QuantumChannels.NuclearTensor
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCompleteContraction
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalSandwich
import QuantumProver.LinearAlgebra.HilbertNuclearCompressionExpansion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Sequences

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000

noncomputable section

open Matrix Filter InnerProductSpace
open scoped BigOperators Topology TensorProduct InnerProductSpace ComplexOrder

namespace QuantumProver.MatrixNormalTensorExtension

open MatrixNuclearTensor NuclearOperator HilbertNuclearCompression
open HilbertNuclearCompressionExpansion
open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalCompleteContraction

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

abbrev Nuc (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  NuclearOperator.Nuclear ℂ H H

local instance blockComplete {R : Type} [Fintype R]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    CompleteSpace (BlockSpace R H) := PiLp.completeSpace 2 (fun _ : R => H)

theorem inner_tmulJoint (x y : F) (u v : G) :
    inner ℂ (tmulJoint x u) (tmulJoint y v) = inner ℂ x y * inner ℂ u v := by
  simp only [tmulJoint_apply, UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]

section FiniteSpectator

variable {R : Type} [Fintype R] [DecidableEq R]

def spectatorVectorLinear (b : R → G) : BlockSpace R F →ₗ[ℂ] Joint F G where
  toFun x := ∑ i, tmulJoint (x i) (b i)
  map_add' x y := by simp [map_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [map_smul, Finset.smul_sum]

theorem spectatorVectorLinear_inner (b : R → G) (hb : Orthonormal ℂ b)
    (x y : BlockSpace R F) :
    inner ℂ (spectatorVectorLinear b x) (spectatorVectorLinear b y) = inner ℂ x y := by
  have hinner := (orthonormal_iff_ite.mp hb)
  simp [spectatorVectorLinear, sum_inner, inner_sum, inner_tmulJoint, hinner,
    PiLp.inner_apply]

def spectatorVector (b : R → G) (hb : Orthonormal ℂ b) :
    BlockSpace R F →ₗᵢ[ℂ] Joint F G where
  toLinearMap := spectatorVectorLinear b
  norm_map' x := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (spectatorVectorLinear b x),
      norm_eq_sqrt_re_inner (𝕜 := ℂ) x, spectatorVectorLinear_inner b hb]

@[simp] theorem spectatorVector_apply (b : R → G) (hb : Orthonormal ℂ b)
    (x : BlockSpace R F) : spectatorVector b hb x = ∑ i, tmulJoint (x i) (b i) := rfl

@[simp] theorem spectatorVector_insert (b : R → G) (hb : Orthonormal ℂ b)
    (i : R) (x : F) : spectatorVector b hb (insert i x) = tmulJoint x (b i) := by
  simp only [spectatorVector_apply, insert_apply_apply]
  have hterm (j : R) : tmulJoint (if j = i then x else 0) (b j) =
      if j = i then tmulJoint x (b i) else 0 := by
    by_cases h : j = i
    · subst j
      simp
    · simp [h, map_zero]
  simp only [hterm]
  simp

end FiniteSpectator

section NuclearIsometry

def isometryNuclear (V : F →ₗᵢ[ℂ] E) : Nuc F →L[ℂ] Nuc E :=
  compose V.toContinuousLinearMap V.toContinuousLinearMap.adjoint

theorem isometryNuclear_leftInverse (V : F →ₗᵢ[ℂ] E) (T : Nuc F) :
    compose V.toContinuousLinearMap.adjoint V.toContinuousLinearMap
      (isometryNuclear V T) = T := by
  apply toOperator_injective
  ext x
  have hV (y : F) : V.toContinuousLinearMap.adjoint (V y) = y := by
    have h := congrArg (fun L : F →L[ℂ] F => L y) V.adjoint_comp_self
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply,
      LinearIsometry.coe_toContinuousLinearMap] using h
  simp only [isometryNuclear, toOperator_compose, ContinuousLinearMap.comp_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap, hV]

theorem norm_isometryNuclear_le (V : F →ₗᵢ[ℂ] E) (T : Nuc F) :
    ‖isometryNuclear V T‖ ≤ ‖T‖ := by
  have hV := V.norm_toContinuousLinearMap_le
  have hprod : ‖V.toContinuousLinearMap‖ * ‖V.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    simpa using mul_le_mul hV hV (norm_nonneg _) zero_le_one
  exact (norm_compose_apply_le _ _ T).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod (norm_nonneg T))

theorem norm_isometryCompression_le (V : F →ₗᵢ[ℂ] E) (T : Nuc E) :
    ‖compose V.toContinuousLinearMap.adjoint V.toContinuousLinearMap T‖ ≤ ‖T‖ := by
  have hV := V.norm_toContinuousLinearMap_le
  have hprod : ‖V.toContinuousLinearMap.adjoint‖ * ‖V.toContinuousLinearMap‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    simpa using mul_le_mul hV hV (norm_nonneg _) zero_le_one
  exact (norm_compose_apply_le _ _ T).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod (norm_nonneg T))

theorem norm_isometryNuclear (V : F →ₗᵢ[ℂ] E) (T : Nuc F) :
    ‖isometryNuclear V T‖ = ‖T‖ := by
  apply le_antisymm (norm_isometryNuclear_le V T)
  simpa only [isometryNuclear_leftInverse] using
    norm_isometryCompression_le V (isometryNuclear V T)

end NuclearIsometry

section FiniteAction

variable {R : Type} [Fintype R] [DecidableEq R]

def finiteSpectatorAction (Φ : NormalOperation F E)
    (b : R → G) (hb : Orthonormal ℂ b) : Nuc (Joint F G) →L[ℂ] Nuc (Joint E G) :=
  (isometryNuclear (spectatorVector (F := E) b hb)).comp
    ((normalAmplification (R := R) Φ).comp
      (compose (spectatorVector (F := F) b hb).toContinuousLinearMap.adjoint
        (spectatorVector (F := F) b hb).toContinuousLinearMap))

theorem norm_finiteSpectatorAction_le (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (b : R → G) (hb : Orthonormal ℂ b) (W : Nuc (Joint F G)) :
    ‖finiteSpectatorAction Φ b hb W‖ ≤ ‖W‖ := by
  exact (norm_isometryNuclear_le _ _).trans
    ((normalAmplification_norm_le_of_cp_trace_nonincreasing Φ hCP hTNI _).trans
      (norm_isometryCompression_le _ W))

def spectatorCoefficient (b : R → G) (i j : R) : Nuc G →L[ℂ] ℂ :=
  (innerSL ℂ (b i)).comp ((ContinuousLinearMap.apply ℂ G (b j)).comp toOperator)

@[simp] theorem spectatorCoefficient_apply (b : R → G) (i j : R) (U : Nuc G) :
    spectatorCoefficient b i j U = inner ℂ (b i) (toOperator U (b j)) := rfl

def spectatorCompression (b : R → G) : Nuc G →L[ℂ] Nuc G :=
  ∑ i, ∑ j, (spectatorCoefficient b i j).smulRight (rankOne (innerSL ℂ (b j)) (b i))

@[simp] theorem spectatorCompression_apply (b : R → G) (U : Nuc G) :
    spectatorCompression b U = ∑ i, ∑ j,
      inner ℂ (b i) (toOperator U (b j)) • rankOne (innerSL ℂ (b j)) (b i) := by
  simp only [spectatorCompression, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, spectatorCoefficient_apply]

theorem spectatorVector_adjoint_tmul (b : R → G) (hb : Orthonormal ℂ b)
    (x : F) (u : G) (i : R) :
    (spectatorVector b hb).toContinuousLinearMap.adjoint (tmulJoint x u) i =
      inner ℂ (b i) u • x := by
  apply ext_inner_left ℂ
  intro y
  rw [← inner_insert_left i y]
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [LinearIsometry.coe_toContinuousLinearMap, spectatorVector_insert,
    inner_tmulJoint, inner_smul_right, mul_comm]

theorem nuclearBlock_compress_tensor (b : R → G) (hb : Orthonormal ℂ b)
    (T : Nuc F) (U : Nuc G) (i j : R) :
    nuclearBlock i j
      (compose (spectatorVector (F := F) b hb).toContinuousLinearMap.adjoint
        (spectatorVector (F := F) b hb).toContinuousLinearMap (tensorNuclear (E := F) (F := G) (E' := F) (F' := G) T U)) =
      inner ℂ (b i) (toOperator U (b j)) • T := by
  apply toOperator_injective
  ext x
  simp only [toOperator_nuclearBlock, toOperator_compose, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, LinearIsometry.coe_toContinuousLinearMap, spectatorVector_insert,
    toOperator_tensorNuclear, tensorMap_tmul, spectatorVector_adjoint_tmul,
    map_smul, ContinuousLinearMap.smul_apply]

theorem finiteSpectatorAction_tensor (Φ : NormalOperation F E)
    (b : R → G) (hb : Orthonormal ℂ b) (T : Nuc F) (U : Nuc G) :
    finiteSpectatorAction Φ b hb (tensorNuclear (E := F) (F := G) (E' := F) (F' := G) T U) =
      tensorNuclear (E := E) (F := G) (E' := E) (F' := G) (Φ T) (spectatorCompression b U) := by
  simp only [finiteSpectatorAction, ContinuousLinearMap.comp_apply,
    normalAmplification_apply, nuclearBlock_compress_tensor, map_smul]
  apply toOperator_injective
  rw [isometryNuclear, toOperator_compose, toOperator_nuclearAssembly,
    toOperator_tensorNuclear]
  apply joint_clm_ext
  intro x u
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    tensorMap_tmul, spectatorVector_apply, blockOperator_apply,
    spectatorVector_adjoint_tmul, map_smul, ContinuousLinearMap.smul_apply,
    spectatorCompression_apply, map_sum, toOperator_rankOne,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_smul, mul_comm]

end FiniteAction

section BasisCuts

variable {ι : Type*}

abbrev CutIndex (s : Finset ι) := Fin (Fintype.card ↥s)

def cutBasis (b : HilbertBasis ι ℂ G) (s : Finset ι) : CutIndex s → G :=
  fun i => b ((Fintype.equivFin ↥s).symm i).val

theorem cutBasis_orthonormal (b : HilbertBasis ι ℂ G) (s : Finset ι) :
    Orthonormal ℂ (cutBasis b s) := by
  apply b.orthonormal.comp (fun i : CutIndex s => ((Fintype.equivFin ↥s).symm i).val)
  intro i j h
  apply (Fintype.equivFin ↥s).symm.injective
  exact Subtype.ext h

theorem sum_cutIndex {Z : Type*} [AddCommMonoid Z] (s : Finset ι) (f : ι → Z) :
    (∑ i : CutIndex s, f ((Fintype.equivFin ↥s).symm i).val) = ∑ i ∈ s, f i := by
  calc
    _ = ∑ i : ↥s, f i.val := (Fintype.equivFin ↥s).symm.sum_comp _
    _ = _ := Finset.sum_coe_sort s f

theorem spectatorCompression_cutBasis (b : HilbertBasis ι ℂ G) (s : Finset ι)
    (U : Nuc G) : spectatorCompression (cutBasis b s) U = compression b s U := by
  rw [spectatorCompression_apply, compression_eq_coefficientCompression]
  simp only [cutBasis, coefficientCompression]
  let K : ι → ι → Nuc G := fun i j => inner ℂ (b i) (toOperator U (b j)) •
    rankOne (innerSL ℂ (b j)) (b i)
  change (∑ i : CutIndex s, ∑ j : CutIndex s,
    K ((Fintype.equivFin ↥s).symm i).val ((Fintype.equivFin ↥s).symm j).val) =
    ∑ i ∈ s, ∑ j ∈ s, K i j
  rw [sum_cutIndex s (fun i => ∑ j : CutIndex s, K i ((Fintype.equivFin ↥s).symm j).val)]
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_cutIndex s (K i)

def finiteSpectatorActionNet (Φ : NormalOperation F E) (b : HilbertBasis ι ℂ G)
    (s : Finset ι) : Nuc (Joint F G) →L[ℂ] Nuc (Joint E G) :=
  finiteSpectatorAction Φ (cutBasis b s) (cutBasis_orthonormal b s)

theorem norm_finiteSpectatorActionNet_le (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (b : HilbertBasis ι ℂ G) (s : Finset ι) (W : Nuc (Joint F G)) :
    ‖finiteSpectatorActionNet Φ b s W‖ ≤ ‖W‖ :=
  norm_finiteSpectatorAction_le Φ hCP hTNI _ _ W

@[simp] theorem finiteSpectatorActionNet_tensor (Φ : NormalOperation F E)
    (b : HilbertBasis ι ℂ G) (s : Finset ι) (T : Nuc F) (U : Nuc G) :
    finiteSpectatorActionNet Φ b s (tensorNuclear (E := F) (F := G) (E' := F) (F' := G) T U) =
      tensorNuclear (E := E) (F := G) (E' := E) (F' := G) (Φ T) (compression b s U) := by
  rw [finiteSpectatorActionNet, finiteSpectatorAction_tensor, spectatorCompression_cutBasis]

end BasisCuts

section Extension

def leftAlgebraic (Φ : NormalOperation F E) :
    (Nuc F ⊗[ℂ] Nuc G) →ₗ[ℂ] Nuc (Joint E G) :=
  (algebraicNuclearTensor (E := E) (F := G) (E' := E) (F' := G)).comp
    (TensorProduct.map Φ.toLinearMap (LinearMap.id : Nuc G →ₗ[ℂ] Nuc G))

@[simp] theorem leftAlgebraic_tmul (Φ : NormalOperation F E) (T : Nuc F) (U : Nuc G) :
    leftAlgebraic Φ (T ⊗ₜ[ℂ] U) = tensorNuclear (E := E) (F := G) (E' := E) (F' := G) (Φ T) U := by
  simp [leftAlgebraic, TensorProduct.map_tmul]

theorem finiteSpectatorActionNet_algebraic_tendsto {ι : Type*}
    (Φ : NormalOperation F E) (b : HilbertBasis ι ℂ G) (w : Nuc F ⊗[ℂ] Nuc G) :
    Tendsto (fun s : Finset ι => finiteSpectatorActionNet Φ b s
      (algebraicNuclearTensor (E := F) (F := G) (E' := F) (F' := G) w)) atTop (𝓝 (leftAlgebraic Φ w)) := by
  classical
  induction w using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : Finset ι =>
      (0 : Nuc (Joint E G))) atTop (𝓝 0))
  | tmul T U =>
      simpa only [algebraicNuclearTensor_tmul, leftAlgebraic_tmul,
        finiteSpectatorActionNet_tensor, Function.comp_def] using
        (tensorNuclear (E := E) (F := G) (E' := E) (F' := G) (Φ T)).continuous.tendsto U |>.comp (compression_tendsto b U)
  | add w v hw hv => simpa only [map_add] using hw.add hv

theorem leftAlgebraic_norm_le (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (w : Nuc F ⊗[ℂ] Nuc G) :
    ‖leftAlgebraic Φ w‖ ≤ ‖algebraicNuclearTensor (E := F) (F := G) (E' := F) (F' := G) w‖ := by
  classical
  obtain ⟨ι, b, hb⟩ := exists_hilbertBasis ℂ G
  exact le_of_tendsto' (finiteSpectatorActionNet_algebraic_tendsto Φ b w).norm
    (fun s => norm_finiteSpectatorActionNet_le Φ hCP hTNI b s _)

def extendLeft (Φ : NormalOperation F E) (_hCP : NormalCompletelyPositive Φ)
    (_hTNI : TraceNonincreasing Φ) : Nuc (Joint F G) →L[ℂ] Nuc (Joint E G) :=
  (leftAlgebraic Φ).extendOfNorm
    (algebraicNuclearTensor (E := F) (F := G) (E' := F) (F' := G))

theorem extendLeft_algebraic (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (w : Nuc F ⊗[ℂ] Nuc G) :
    extendLeft Φ hCP hTNI (algebraicNuclearTensor (E := F) (F := G) (E' := F) (F' := G) w) = leftAlgebraic Φ w := by
  exact LinearMap.extendOfNorm_eq denseRange_algebraicNuclearTensor
    ⟨1, fun z => by simpa only [one_mul] using leftAlgebraic_norm_le Φ hCP hTNI z⟩ w

@[simp] theorem extendLeft_tensor (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ) (T : Nuc F) (U : Nuc G) :
    extendLeft Φ hCP hTNI (tensorNuclear (E := F) (F := G) (E' := F) (F' := G) T U) = tensorNuclear (E := E) (F := G) (E' := E) (F' := G) (Φ T) U := by
  simpa only [algebraicNuclearTensor_tmul, leftAlgebraic_tmul] using
    extendLeft_algebraic Φ hCP hTNI (T ⊗ₜ[ℂ] U)

theorem extendLeft_norm_le (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ) (W : Nuc (Joint F G)) :
    ‖extendLeft Φ hCP hTNI W‖ ≤ ‖W‖ := by
  simpa only [extendLeft, one_mul] using LinearMap.norm_extendOfNorm_apply_le
    denseRange_algebraicNuclearTensor 1
      (fun z => by simpa only [one_mul] using leftAlgebraic_norm_le Φ hCP hTNI z) W

theorem norm_extendLeft_le_one (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ) :
    ‖extendLeft (G := G) Φ hCP hTNI‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun W => by simpa only [one_mul] using extendLeft_norm_le Φ hCP hTNI W)

theorem extendLeft_unique (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (L : Nuc (Joint F G) →L[ℂ] Nuc (Joint E G))
    (hL : ∀ T : Nuc F, ∀ U : Nuc G, L (tensorNuclear (E := F) (F := G) (E' := F) (F' := G) T U) = tensorNuclear (E := E) (F := G) (E' := E) (F' := G) (Φ T) U) :
    L = extendLeft Φ hCP hTNI := by
  apply nuclear_joint_clm_ext_tensors
  intro T U
  exact (hL T U).trans (extendLeft_tensor Φ hCP hTNI T U).symm

theorem exists_algebraic_sequence (W : Nuc (Joint F G)) :
    ∃ w : ℕ → Nuc F ⊗[ℂ] Nuc G,
      Tendsto (fun n => algebraicNuclearTensor (E := F) (F := G) (E' := F) (F' := G) (w n)) atTop (𝓝 W) := by
  classical
  have hmem : W ∈ closure (Set.range
      (algebraicNuclearTensor (E := F) (F := G) (E' := F) (F' := G))) :=
    denseRange_algebraicNuclearTensor W
  obtain ⟨a, ha, hlim⟩ := mem_closure_iff_seq_limit.mp hmem
  choose w hw using ha
  refine ⟨w, ?_⟩
  simpa only [hw] using hlim

theorem finiteSpectatorActionNet_tendsto {ι : Type*}
    (Φ : NormalOperation F E) (hCP : NormalCompletelyPositive Φ)
    (hTNI : TraceNonincreasing Φ) (b : HilbertBasis ι ℂ G)
    (W : Nuc (Joint F G)) :
    Tendsto (fun s : Finset ι => finiteSpectatorActionNet Φ b s W)
      atTop (𝓝 (extendLeft Φ hCP hTNI W)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨S, hS, w, rfl⟩ := Metric.dense_iff.mp
    (denseRange_algebraicNuclearTensor (E := F) (F := G) (E' := F) (F' := G))
    W (ε / 3) (by linarith)
  have hnear : ‖algebraicNuclearTensor (E := F) (F := G) (E' := F) (F' := G) w - W‖ < ε / 3 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hS
  have hmid := Metric.tendsto_nhds.mp
    (finiteSpectatorActionNet_algebraic_tendsto Φ b w) (ε / 3) (by linarith)
  rw [← extendLeft_algebraic Φ hCP hTNI w] at hmid
  filter_upwards [hmid] with s hs
  simp only [dist_eq_norm] at hs ⊢
  let S := algebraicNuclearTensor (E := F) (F := G) (E' := F) (F' := G) w
  let A := finiteSpectatorActionNet Φ b s
  let L := extendLeft (G := G) Φ hCP hTNI
  have hsplit : A W - L W = A (W - S) + (A S - L S) + L (S - W) := by
    simp only [map_sub]
    abel
  have htriangle : ‖A W - L W‖ ≤ ‖W - S‖ + ‖A S - L S‖ + ‖S - W‖ := by
    rw [hsplit]
    calc
      ‖A (W - S) + (A S - L S) + L (S - W)‖ ≤
          ‖A (W - S) + (A S - L S)‖ + ‖L (S - W)‖ := norm_add_le _ _
      _ ≤ ‖A (W - S)‖ + ‖A S - L S‖ + ‖L (S - W)‖ :=
        add_le_add (norm_add_le (A (W - S)) (A S - L S)) le_rfl
      _ ≤ ‖W - S‖ + ‖A S - L S‖ + ‖S - W‖ :=
        add_le_add
          (add_le_add (norm_finiteSpectatorActionNet_le Φ hCP hTNI b s (W - S)) le_rfl)
          (extendLeft_norm_le Φ hCP hTNI (S - W))
  have hnear' : ‖W - S‖ < ε / 3 := by
    simpa only [S, norm_sub_rev W] using hnear
  exact htriangle.trans_lt (by
    change ‖W - S‖ + ‖A S - L S‖ + ‖S - W‖ < ε
    change ‖A S - L S‖ < ε / 3 at hs
    change ‖S - W‖ < ε / 3 at hnear
    linarith)

theorem finiteSpectatorAction_isPositive {R : Type} [Fintype R] [DecidableEq R]
    (Φ : NormalOperation F E) (hCP : NormalCompletelyPositive Φ)
    (b : R → G) (hb : Orthonormal ℂ b) (W : Nuc (Joint F G))
    (hW : (toOperator W).IsPositive) :
    (toOperator (finiteSpectatorAction Φ b hb W)).IsPositive := by
  have hCut : (toOperator (compose
      (spectatorVector (F := F) b hb).toContinuousLinearMap.adjoint
      (spectatorVector (F := F) b hb).toContinuousLinearMap W)).IsPositive := by
    rw [toOperator_compose]
    exact hW.adjoint_conj (spectatorVector (F := F) b hb).toContinuousLinearMap
  have hOut := hCP R _ hCut
  simp only [finiteSpectatorAction, ContinuousLinearMap.comp_apply,
    isometryNuclear, toOperator_compose]
  exact hOut.conj_adjoint (spectatorVector (F := E) b hb).toContinuousLinearMap

theorem isPositive_nuclear_limit {κ : Type*} {l : Filter κ} [NeBot l]
    (W : κ → Nuc F) (T : Nuc F) (hlim : Tendsto W l (𝓝 T))
    (hW : ∀ k, (toOperator (W k)).IsPositive) : (toOperator T).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hop : Tendsto (fun k => toOperator (W k) x) l (𝓝 (toOperator T x)) :=
    (((ContinuousLinearMap.apply ℂ F x).comp toOperator).continuous.tendsto T).comp hlim
  have hz := hop.inner (𝕜 := ℂ) (tendsto_const_nhds (x := x))
  have hre : Tendsto (fun k => (inner ℂ (toOperator (W k) x) x).re) l
      (𝓝 (inner ℂ (toOperator T x) x).re) :=
    (Complex.continuous_re.tendsto _).comp hz
  have hp (k : κ) := (ContinuousLinearMap.isPositive_iff_complex _).mp (hW k) x
  constructor
  · have hr : Tendsto (fun k => inner ℂ (toOperator (W k) x) x) l
        (𝓝 ((inner ℂ (toOperator T x) x).re : ℂ)) := by
      convert Filter.Tendsto.ofReal hre using 1
      funext k
      exact (hp k).1.symm
    exact tendsto_nhds_unique hr hz
  · exact ge_of_tendsto' hre (fun k => (hp k).2)

theorem extendLeft_isPositive (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (W : Nuc (Joint F G)) (hW : (toOperator W).IsPositive) :
    (toOperator (extendLeft Φ hCP hTNI W)).IsPositive := by
  obtain ⟨ι, b, hb⟩ := exists_hilbertBasis ℂ G
  exact isPositive_nuclear_limit _ _ (finiteSpectatorActionNet_tendsto Φ hCP hTNI b W)
    (fun s => finiteSpectatorAction_isPositive Φ hCP _ _ W hW)

theorem extendLeft_traceNonincreasing (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ) :
    TraceNonincreasing (extendLeft (G := G) Φ hCP hTNI) := by
  intro W hW
  obtain ⟨ι, b, hb⟩ := exists_hilbertBasis ℂ (Joint F G)
  exact (HilbertNuclearTrace.re_trace_le_norm _).trans
    ((extendLeft_norm_le Φ hCP hTNI W).trans
      (QuantumProver.ElegantJointMeasurement.NuclearChoi.norm_positive_nuclear_eq_re_trace b W hW).le)

theorem trace_extendLeft (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (hTP : ∀ T, HilbertNuclearTrace.trace (Φ T) = HilbertNuclearTrace.trace T)
    (W : Nuc (Joint F G)) :
    HilbertNuclearTrace.trace (extendLeft Φ hCP hTNI W) = HilbertNuclearTrace.trace W := by
  have hmaps : HilbertNuclearTrace.trace.comp (extendLeft (G := G) Φ hCP hTNI) =
      (HilbertNuclearTrace.trace (E := Joint F G)) := by
    apply nuclear_joint_clm_ext_tensors
    intro T U
    simp only [ContinuousLinearMap.comp_apply, extendLeft_tensor, trace_tensorNuclear, hTP]
  exact congrArg (fun L => L W) hmaps

open QuantumProver.ElegantJointMeasurement.NormalSandwich

section CompletePositivity

variable {R : Type} [Fintype R] [DecidableEq R]

theorem finiteSpectatorAction_completelyPositive
    (Φ : NormalOperation F E) (hCP : NormalCompletelyPositive Φ)
    (b : R → G) (hb : Orthonormal ℂ b) :
    NormalCompletelyPositive (finiteSpectatorAction Φ b hb) := by
  have hin := normalCompletelyPositive_sandwich
    (spectatorVector (F := F) b hb).toContinuousLinearMap.adjoint
  have hmid := normalCompletelyPositive_normalAmplification (R := R) Φ hCP
  have hout := normalCompletelyPositive_sandwich
    (spectatorVector (F := E) b hb).toContinuousLinearMap
  simpa only [finiteSpectatorAction, isometryNuclear, sandwich,
    ContinuousLinearMap.adjoint_adjoint] using
    normalCompletelyPositive_comp _ _ hout (normalCompletelyPositive_comp _ _ hmid hin)

theorem normalAmplification_finiteSpectatorActionNet_tendsto {ι : Type*}
    (Φ : NormalOperation F E) (hCP : NormalCompletelyPositive Φ)
    (hTNI : TraceNonincreasing Φ) (b : HilbertBasis ι ℂ G)
    (W : Nuc (BlockSpace R (Joint F G))) :
    Tendsto (fun s : Finset ι => normalAmplification (finiteSpectatorActionNet Φ b s) W)
      atTop (𝓝 (normalAmplification (extendLeft Φ hCP hTNI) W)) := by
  classical
  simp only [normalAmplification_apply, nuclearAssembly]
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  exact ((compose (insert (E := Joint E G) i)
    (PiLp.proj 2 (fun _ : R => Joint E G) j)).continuous.tendsto _).comp
      (finiteSpectatorActionNet_tendsto Φ hCP hTNI b (nuclearBlock i j W))

theorem extendLeft_completelyPositive (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ) :
    NormalCompletelyPositive (extendLeft (G := G) Φ hCP hTNI) := by
  intro R _ _ W hW
  obtain ⟨ι, b, hb⟩ := exists_hilbertBasis ℂ G
  apply isPositive_nuclear_limit _ _
    (normalAmplification_finiteSpectatorActionNet_tendsto Φ hCP hTNI b W)
  intro s
  exact finiteSpectatorAction_completelyPositive Φ hCP _ _ R W hW

end CompletePositivity

section ChronologicalLaws

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem traceNonincreasing_comp (Ψ : NormalOperation E H) (Φ : NormalOperation F E)
    (hΦ : NormalCompletelyPositive Φ) (hΨTNI : TraceNonincreasing Ψ)
    (hΦTNI : TraceNonincreasing Φ) : TraceNonincreasing (Ψ.comp Φ) := by
  intro T hT
  exact (hΨTNI (Φ T) (normalOperation_isPositive Φ hΦ T hT)).trans (hΦTNI T hT)

theorem extendLeft_comp (Ψ : NormalOperation E H) (Φ : NormalOperation F E)
    (hΨ : NormalCompletelyPositive Ψ) (hΦ : NormalCompletelyPositive Φ)
    (hΨTNI : TraceNonincreasing Ψ) (hΦTNI : TraceNonincreasing Φ) :
    extendLeft (G := G) (Ψ.comp Φ) (normalCompletelyPositive_comp Ψ Φ hΨ hΦ)
      (traceNonincreasing_comp Ψ Φ hΦ hΨTNI hΦTNI) =
      (extendLeft (G := G) Ψ hΨ hΨTNI).comp (extendLeft (G := G) Φ hΦ hΦTNI) := by
  apply nuclear_joint_clm_ext_tensors
  intro T U
  simp only [ContinuousLinearMap.comp_apply, extendLeft_tensor]

theorem normalCompletelyPositive_id :
    NormalCompletelyPositive (ContinuousLinearMap.id ℂ (Nuc F)) := by
  intro R _ _ W hW
  simpa only [normalAmplification_apply, ContinuousLinearMap.id_apply,
    nuclearAssembly_nuclearBlock] using hW

theorem traceNonincreasing_id : TraceNonincreasing (ContinuousLinearMap.id ℂ (Nuc F)) :=
  fun T _ => le_rfl

@[simp] theorem extendLeft_id :
    extendLeft (G := G) (ContinuousLinearMap.id ℂ (Nuc F))
      normalCompletelyPositive_id traceNonincreasing_id =
      ContinuousLinearMap.id ℂ (Nuc (Joint F G)) := by
  apply nuclear_joint_clm_ext_tensors
  intro T U
  simp only [extendLeft_tensor, ContinuousLinearMap.id_apply]

theorem extendLeft_rankOne_tmul (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (x y : F) (u v : G) :
    extendLeft Φ hCP hTNI
      (rankOne (innerSL ℂ (tmulJoint x u)) (tmulJoint y v)) =
      tensorNuclear (E := E) (F := G) (E' := E) (F' := G) (Φ (rankOne (innerSL ℂ x) y)) (rankOne (innerSL ℂ u) v) := by
  rw [← tensorFunctional_innerSL, ← tensorNuclear_rankOne, extendLeft_tensor]

end ChronologicalLaws

theorem compose_id_id_apply (T : Nuc F) :
    compose (ContinuousLinearMap.id ℂ F) (ContinuousLinearMap.id ℂ F) T = T := by
  apply toOperator_injective
  simp only [toOperator_compose, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

theorem extendLeft_sandwich (L : F →L[ℂ] E) (hTNI : TraceNonincreasing (sandwich L)) :
    extendLeft (G := G) (sandwich L) (normalCompletelyPositive_sandwich L) hTNI =
      compose (tensorMap L (ContinuousLinearMap.id ℂ G))
        (tensorMap L.adjoint (ContinuousLinearMap.id ℂ G)) := by
  apply nuclear_joint_clm_ext_tensors
  intro T U
  rw [extendLeft_tensor]
  simpa only [compose_id_id_apply, sandwich] using
    tensorNuclear_compose L L.adjoint (ContinuousLinearMap.id ℂ G)
      (ContinuousLinearMap.id ℂ G) T U

section RemoteSandwich

variable {G' : Type*}
  [NormedAddCommGroup G'] [InnerProductSpace ℂ G'] [CompleteSpace G']

theorem extendLeft_remote_sandwich (Φ : NormalOperation F E)
    (hCP : NormalCompletelyPositive Φ) (hTNI : TraceNonincreasing Φ)
    (L : G →L[ℂ] G') (R : G' →L[ℂ] G) (W : Nuc (Joint F G)) :
    extendLeft (G := G') Φ hCP hTNI
      (compose (tensorMap (ContinuousLinearMap.id ℂ F) L)
        (tensorMap (ContinuousLinearMap.id ℂ F) R) W) =
      compose (tensorMap (ContinuousLinearMap.id ℂ E) L)
        (tensorMap (ContinuousLinearMap.id ℂ E) R)
        (extendLeft (G := G) Φ hCP hTNI W) := by
  have heq : (extendLeft (G := G') Φ hCP hTNI).comp
      (compose (tensorMap (ContinuousLinearMap.id ℂ F) L)
        (tensorMap (ContinuousLinearMap.id ℂ F) R)) =
      (compose (tensorMap (ContinuousLinearMap.id ℂ E) L)
        (tensorMap (ContinuousLinearMap.id ℂ E) R)).comp
        (extendLeft (G := G) Φ hCP hTNI) := by
    apply nuclear_joint_clm_ext_tensors
    intro T U
    simp only [ContinuousLinearMap.comp_apply]
    rw [← tensorNuclear_compose, compose_id_id_apply, extendLeft_tensor, extendLeft_tensor]
    simpa only [compose_id_id_apply] using
      tensorNuclear_compose (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ E) L R (Φ T) U
  exact congrArg (fun A => A W) heq

end RemoteSandwich

end Extension

end QuantumProver.MatrixNormalTensorExtension
