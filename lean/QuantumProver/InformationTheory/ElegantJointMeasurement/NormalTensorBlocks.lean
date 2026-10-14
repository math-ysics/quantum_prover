import QuantumProver.QuantumChannels.NuclearTensor
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentAbsorption
import QuantumProver.InformationTheory.ElegantJointMeasurement.SeparableHilbertEmbedding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators Topology ComplexOrder InnerProductSpace

namespace QuantumProver.ElegantJointMeasurement.NormalTensorBlocks

open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.MatrixNuclearTensor QuantumProver.HilbertNuclearCompression
open QuantumProver.NuclearOperator (toOperator toOperator_injective)

variable {R : Type} [Fintype R] [DecidableEq R]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem sum_insert (x : BlockSpace R E) : (∑ r : R, QuantumProver.ElegantJointMeasurement.HilbertChoi.insert r (x r)) = x := by
  apply PiLp.ext
  intro i
  change (PiLp.proj (𝕜 := ℂ) 2 (fun _ : R => E) i) (∑ r : R, QuantumProver.ElegantJointMeasurement.HilbertChoi.insert r (x r)) = x i
  rw [map_sum]
  simp [insert_apply_apply]

theorem insert_adjoint (r : R) :
    (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := E) r).adjoint = PiLp.proj (𝕜 := ℂ) 2 (fun _ : R => E) r := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp [PiLp.inner_apply, insert_apply_apply, apply_ite]

theorem proj_adjoint (r : R) :
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : R => E) r).adjoint = QuantumProver.ElegantJointMeasurement.HilbertChoi.insert r := by
  rw [← insert_adjoint, ContinuousLinearMap.adjoint_adjoint]

def blockTensorForward : Joint (BlockSpace R E) F →L[ℂ] BlockSpace R (Joint E F) :=
  ∑ r : R, (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := Joint E F) r).comp
    (tensorMap (PiLp.proj (𝕜 := ℂ) 2 (fun _ : R => E) r) (ContinuousLinearMap.id ℂ F))

def blockTensorReverse : BlockSpace R (Joint E F) →L[ℂ] Joint (BlockSpace R E) F :=
  ∑ r : R, (tensorMap (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := E) r) (ContinuousLinearMap.id ℂ F)).comp
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : R => Joint E F) r)

local notation "V" => blockTensorForward (R := R) (E := E) (F := F)
local notation "W" => blockTensorReverse (R := R) (E := E) (F := F)

@[simp] theorem blockTensorForward_tmul (x : BlockSpace R E) (y : F) (r : R) :
    V (tmulJoint x y) r = tmulJoint (x r) y := by
  change (PiLp.proj (𝕜 := ℂ) 2 (fun _ : R => Joint E F) r)
    (V (tmulJoint x y)) = _
  simp [blockTensorForward, map_sum, insert_apply_apply]

theorem blockTensorForward_tensorInsert (r : R) :
    (V).comp (tensorMap (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := E) r) (ContinuousLinearMap.id ℂ F)) =
      QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := Joint E F) r := by
  apply joint_clm_ext
  intro x y
  apply PiLp.ext
  intro i
  by_cases hi : i = r
  · simp [insert_apply_apply, hi]
  · simp [insert_apply_apply, hi]

@[simp] theorem blockTensorForward_tensorInsert_apply (r : R) (z : Joint E F) :
    V (tensorMap (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := E) r) (ContinuousLinearMap.id ℂ F) z) =
      QuantumProver.ElegantJointMeasurement.HilbertChoi.insert r z :=
  congrArg (fun L : Joint E F →L[ℂ] BlockSpace R (Joint E F) => L z)
    (blockTensorForward_tensorInsert r)

theorem blockTensorForward_reverse : (V).comp W = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change V (W x) = x
  simp only [blockTensorReverse, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply]
  rw [map_sum]
  simp only [blockTensorForward_tensorInsert_apply]
  exact sum_insert x

theorem blockTensorReverse_forward : (W).comp V = 1 := by
  apply joint_clm_ext
  intro x y
  change W (V (tmulJoint x y)) = tmulJoint x y
  simp only [blockTensorReverse, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, blockTensorForward_tmul, tensorMap_tmul, ContinuousLinearMap.id_apply]
  calc
    (∑ r : R, tmulJoint (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert r (x r)) y) =
        tmulJoint (∑ r : R, QuantumProver.ElegantJointMeasurement.HilbertChoi.insert r (x r)) y := by
      simpa only [ContinuousLinearMap.flip_apply] using
        (map_sum (tmulJoint.flip y) (fun r : R => QuantumProver.ElegantJointMeasurement.HilbertChoi.insert r (x r)) Finset.univ).symm
    _ = tmulJoint x y := by rw [sum_insert]

theorem blockTensorForward_adjoint : (V).adjoint = W := by
  simp only [blockTensorForward, blockTensorReverse, map_sum, ContinuousLinearMap.adjoint_comp,
    tensorMap_adjoint, proj_adjoint, insert_adjoint, ContinuousLinearMap.adjoint_id]

def blockTensorIsometry : Joint (BlockSpace R E) F →ₗᵢ[ℂ] BlockSpace R (Joint E F) where
  __ := (V).toLinearMap
  norm_map' := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self V).mpr (by
    rw [blockTensorForward_adjoint]
    exact blockTensorReverse_forward)

def blockTensor : Joint (BlockSpace R E) F ≃ₗᵢ[ℂ] BlockSpace R (Joint E F) :=
  LinearIsometryEquiv.ofLinearIsometry (blockTensorIsometry (R := R) (E := E) (F := F)) (W).toLinearMap
    (by
      apply LinearMap.ext
      intro x
      change V (W x) = x
      exact congrArg (fun L : BlockSpace R (Joint E F) →L[ℂ] BlockSpace R (Joint E F) => L x)
        blockTensorForward_reverse)
    (by
      apply LinearMap.ext
      intro x
      change W (V x) = x
      exact congrArg (fun L : Joint (BlockSpace R E) F →L[ℂ] Joint (BlockSpace R E) F => L x)
        blockTensorReverse_forward)

theorem blockTensor_toContinuousLinearMap :
    (blockTensor (R := R) (E := E) (F := F)).toLinearIsometry.toContinuousLinearMap = V := by
  ext x
  rfl

@[simp] theorem blockTensor_tmul (x : BlockSpace R E) (y : F) (r : R) :
    blockTensor (tmulJoint x y) r = tmulJoint (x r) y := by
  change V (tmulJoint x y) r = _
  exact blockTensorForward_tmul x y r

theorem blockTensor_adjoint :
    (blockTensor (R := R) (E := E) (F := F)).toLinearIsometry.toContinuousLinearMap.adjoint = W := by
  rw [blockTensor_toContinuousLinearMap, blockTensorForward_adjoint]

theorem blockTensorForward_component (r : R) :
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : R => Joint E F) r).comp V =
      tensorMap (PiLp.proj (𝕜 := ℂ) 2 (fun _ : R => E) r) (ContinuousLinearMap.id ℂ F) := by
  apply joint_clm_ext
  intro x y
  simp

theorem nuclearAssembly_tensor_eq (T : Nuclear (BlockSpace R E)) (τ : Nuclear F) :
    nuclearAssembly (fun i j : R => tensorNuclear (nuclearBlock i j T) τ) =
      compose (blockTensor (R := R) (E := E) (F := F)).toLinearIsometry.toContinuousLinearMap
        (blockTensor (R := R) (E := E) (F := F)).toLinearIsometry.toContinuousLinearMap.adjoint
        (tensorNuclear T τ) := by
  apply toOperator_injective
  simp only [toOperator_nuclearAssembly, toOperator_compose, toOperator_tensorNuclear,
    blockTensor_toContinuousLinearMap, blockTensorForward_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  rw [blockOperator_apply]
  change (∑ j : R, tensorMap (toOperator (nuclearBlock i j T)) (toOperator τ) (x j)) =
    V (tensorMap (toOperator T) (toOperator τ) (W x)) i
  have hc := congrArg (fun L : Joint (BlockSpace R E) F →L[ℂ] Joint E F =>
    L (tensorMap (toOperator T) (toOperator τ) (W x)))
    (blockTensorForward_component (E := E) (F := F) i)
  change V (tensorMap (toOperator T) (toOperator τ) (W x)) i =
    tensorMap (PiLp.proj (𝕜 := ℂ) 2 (fun _ : R => E) i) (ContinuousLinearMap.id ℂ F)
      (tensorMap (toOperator T) (toOperator τ) (W x)) at hc
  rw [hc]
  simp only [blockTensorReverse, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [toOperator_nuclearBlock]
  have hcomp : tensorMap
      ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : R => E) i).comp ((toOperator T).comp (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert j))) (toOperator τ) =
      (tensorMap (PiLp.proj (𝕜 := ℂ) 2 (fun _ : R => E) i) (ContinuousLinearMap.id ℂ F)).comp
        ((tensorMap (toOperator T) (toOperator τ)).comp
          (tensorMap (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert j) (ContinuousLinearMap.id ℂ F))) := by
    apply joint_clm_ext
    intro u v
    simp only [tensorMap_tmul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  exact congrArg (fun L : Joint E F →L[ℂ] Joint E F => L (x j)) hcomp

theorem nuclearAssembly_tensor_isPositive (T : Nuclear (BlockSpace R E)) (τ : Nuclear F)
    (hT : (toOperator T).IsPositive) (hτ : (toOperator τ).IsPositive) :
    (toOperator (nuclearAssembly (fun i j : R => tensorNuclear (nuclearBlock i j T) τ))).IsPositive := by
  rw [nuclearAssembly_tensor_eq, toOperator_compose]
  exact (tensorNuclear_isPositive T τ hT hτ).conj_adjoint
    (blockTensor (R := R) (E := E) (F := F)).toLinearIsometry.toContinuousLinearMap

end QuantumProver.ElegantJointMeasurement.NormalTensorBlocks
