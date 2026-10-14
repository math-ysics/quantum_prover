import QuantumProver.QuantumChannels.NuclearTensor
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open scoped TensorProduct ComplexOrder InnerProductSpace

namespace QuantumProver.MatrixHilbertSwap

open NuclearOperator HilbertNuclearTrace HilbertNuclearCompression MatrixNuclearTensor

variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

def jointSwapMap (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    Joint E F →ₗᵢ[ℂ] Joint F E :=
  (TensorProduct.commIsometry ℂ E F).toLinearIsometry.completion

@[simp] theorem jointSwapMap_tmul (x : E) (y : F) :
    jointSwapMap E F (tmulJoint x y) = tmulJoint y x := by
  simp only [jointSwapMap, tmulJoint_apply, LinearIsometry.completion_apply_coe]
  rfl

@[simp] theorem jointSwapMap_involutive (z : Joint E F) :
    jointSwapMap F E (jointSwapMap E F z) = z := by
  have h : (jointSwapMap F E).toContinuousLinearMap ∘L
      (jointSwapMap E F).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (Joint E F) := by
    apply joint_clm_ext
    intro x y
    simp
  exact congrArg (fun L : Joint E F →L[ℂ] Joint E F => L z) h

def jointSwap (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    Joint E F ≃ₗᵢ[ℂ] Joint F E where
  toLinearEquiv :=
    { (jointSwapMap E F).toLinearMap with
      invFun := jointSwapMap F E
      left_inv := fun z => jointSwapMap_involutive z
      right_inv := fun z => jointSwapMap_involutive z }
  norm_map' := (jointSwapMap E F).norm_map

@[simp] theorem jointSwap_tmul (x : E) (y : F) :
    jointSwap E F (tmulJoint x y) = tmulJoint y x := jointSwapMap_tmul x y

@[simp] theorem jointSwap_involutive (z : Joint E F) :
    jointSwap F E (jointSwap E F z) = z := jointSwapMap_involutive z

@[simp] theorem jointSwap_symm : (jointSwap E F).symm = jointSwap F E := by
  apply LinearIsometryEquiv.ext
  intro z
  apply (jointSwap E F).injective
  simp

@[simp] theorem jointSwap_adjoint :
    (jointSwap E F : Joint E F →L[ℂ] Joint F E).adjoint =
      (jointSwap F E : Joint F E →L[ℂ] Joint E F) := by
  rw [LinearIsometryEquiv.adjoint_eq_symm, jointSwap_symm]

theorem jointSwap_tensorMap (f : E →L[ℂ] E') (g : F →L[ℂ] F') :
    (jointSwap E' F' : Joint E' F' →L[ℂ] Joint F' E') ∘L tensorMap f g =
      tensorMap g f ∘L (jointSwap E F : Joint E F →L[ℂ] Joint F E) := by
  apply joint_clm_ext
  intro x y
  simp

theorem jointSwap_opNorm_le_one :
    ‖(jointSwap E F : Joint E F →L[ℂ] Joint F E)‖ ≤ 1 :=
  (jointSwap E F).toLinearIsometry.norm_toContinuousLinearMap_le

def nuclearSwap (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    Nuclear ℂ (Joint E F) (Joint E F) →L[ℂ]
      Nuclear ℂ (Joint F E) (Joint F E) :=
  compose (jointSwap E F : Joint E F →L[ℂ] Joint F E)
    (jointSwap F E : Joint F E →L[ℂ] Joint E F)

theorem nuclearSwap_eq_compose (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    nuclearSwap E F = compose (jointSwap E F : Joint E F →L[ℂ] Joint F E)
      (jointSwap F E : Joint F E →L[ℂ] Joint E F) := rfl

theorem nuclearSwap_eq_sandwich (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    nuclearSwap E F = compose (jointSwap E F : Joint E F →L[ℂ] Joint F E)
      (jointSwap E F : Joint E F →L[ℂ] Joint F E).adjoint := by
  rw [jointSwap_adjoint]
  rfl

@[simp] theorem toOperator_nuclearSwap (T : Nuclear ℂ (Joint E F) (Joint E F)) :
    toOperator (nuclearSwap E F T) =
      (jointSwap E F : Joint E F →L[ℂ] Joint F E) ∘L toOperator T ∘L
        (jointSwap F E : Joint F E →L[ℂ] Joint E F) :=
  toOperator_compose _ _ T

@[simp] theorem nuclearSwap_rankOne (phi : Joint E F →L[ℂ] ℂ) (y : Joint E F) :
    nuclearSwap E F (rankOne phi y) =
      rankOne (phi ∘L (jointSwap F E : Joint F E →L[ℂ] Joint E F)) (jointSwap E F y) :=
  compose_rankOne _ _ phi y

@[simp] theorem nuclearSwap_involutive (T : Nuclear ℂ (Joint E F) (Joint E F)) :
    nuclearSwap F E (nuclearSwap E F T) = T := by
  apply toOperator_injective
  ext z
  simp

@[simp] theorem trace_nuclearSwap (T : Nuclear ℂ (Joint E F) (Joint E F)) :
    trace (nuclearSwap E F T) = trace T := by
  have h : (trace (E := Joint F E)) ∘L nuclearSwap E F = trace (E := Joint E F) := by
    apply nuclear_clm_ext_rankOne
    intro phi y
    simp
  exact congrArg (fun L : Nuclear ℂ (Joint E F) (Joint E F) →L[ℂ] ℂ => L T) h

theorem nuclearSwap_norm_le (T : Nuclear ℂ (Joint E F) (Joint E F)) :
    ‖nuclearSwap E F T‖ ≤ ‖T‖ := by
  refine (norm_compose_apply_le _ _ T).trans ?_
  have h₁ := jointSwap_opNorm_le_one (E := E) (F := F)
  have h₂ := jointSwap_opNorm_le_one (E := F) (F := E)
  have hmul : ‖(jointSwap E F : Joint E F →L[ℂ] Joint F E)‖ *
      ‖(jointSwap F E : Joint F E →L[ℂ] Joint E F)‖ ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul h₁ h₂
        (norm_nonneg (jointSwap F E : Joint F E →L[ℂ] Joint E F)) zero_le_one
      _ = 1 := one_mul 1
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hmul (norm_nonneg T)

@[simp] theorem nuclearSwap_norm (T : Nuclear ℂ (Joint E F) (Joint E F)) :
    ‖nuclearSwap E F T‖ = ‖T‖ := by
  apply le_antisymm (nuclearSwap_norm_le T)
  simpa only [nuclearSwap_involutive] using nuclearSwap_norm_le (nuclearSwap E F T)

section TensorOperators

variable [CompleteSpace E] [CompleteSpace F]

@[simp] theorem nuclearSwap_tensor (T : Nuclear ℂ E E) (U : Nuclear ℂ F F) :
    nuclearSwap E F (tensorNuclear T U) = tensorNuclear U T := by
  apply toOperator_injective
  rw [toOperator_nuclearSwap, toOperator_tensorNuclear, toOperator_tensorNuclear]
  apply joint_clm_ext
  intro y x
  simp

end TensorOperators

end QuantumProver.MatrixHilbertSwap
