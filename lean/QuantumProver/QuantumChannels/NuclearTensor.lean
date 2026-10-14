import QuantumProver.LinearAlgebra.HilbertNuclearCompression
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.StarOrder

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Filter
open scoped BigOperators Topology TensorProduct ComplexOrder InnerProductSpace lp Classical ENNReal

namespace QuantumProver.MatrixNuclearTensor

open NuclearOperator HilbertNuclearTrace HilbertNuclearCompression

section CompletionNorm

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem completion_apply_norm_le (f : X →L[ℂ] Y)
    (z : UniformSpace.Completion X) : ‖f.completion z‖ ≤ ‖f‖*‖z‖ := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro x
  simpa only [ContinuousLinearMap.completion_apply_coe,
    UniformSpace.Completion.norm_coe] using f.le_opNorm x

theorem norm_completion_le (f : X →L[ℂ] Y) : ‖f.completion‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (completion_apply_norm_le f)

variable [CompleteSpace Y]

theorem fromCompletion_apply_norm_le (f : X →L[ℂ] Y)
    (z : UniformSpace.Completion X) : ‖f.fromCompletion z‖ ≤ ‖f‖*‖z‖ := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro x
  simpa only [ContinuousLinearMap.fromCompletion_apply_coe,
    UniformSpace.Completion.norm_coe] using f.le_opNorm x

theorem norm_fromCompletion_le (f : X →L[ℂ] Y) : ‖f.fromCompletion‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fromCompletion_apply_norm_le f)

end CompletionNorm

variable {E F E' F' E'' F'' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']
  [NormedAddCommGroup E''] [InnerProductSpace ℂ E'']
  [NormedAddCommGroup F''] [InnerProductSpace ℂ F'']

abbrev Joint (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :=
  UniformSpace.Completion (TensorProduct ℂ E F)

def tmulJoint : E →L[ℂ] F →L[ℂ] Joint E F :=
  (ContinuousLinearMap.compL ℂ F (TensorProduct ℂ E F) (Joint E F)
    UniformSpace.Completion.toComplL) ∘L TensorProduct.mkL ℂ E F

theorem tmulJoint_apply (x : E) (y : F) :
    tmulJoint x y = (↑(x ⊗ₜ[ℂ] y) : Joint E F) := rfl

@[simp] theorem norm_tmulJoint (x : E) (y : F) :
    ‖tmulJoint x y‖ = ‖x‖*‖y‖ := by simp only [tmulJoint_apply,
      UniformSpace.Completion.norm_coe,TensorProduct.norm_tmul]

theorem joint_clm_ext {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {f g : Joint E F →L[ℂ] Z}
    (h : ∀ x : E,∀ y : F,f (tmulJoint x y)=g (tmulJoint x y)) : f=g := by
  apply ContinuousLinearMap.ext
  intro z
  refine UniformSpace.Completion.induction_on z (isClosed_eq f.continuous g.continuous) ?_
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simpa only [UniformSpace.Completion.coe_zero, map_zero]
  | tmul x y => exact h x y
  | add w v hw hv => simpa only [UniformSpace.Completion.coe_add,map_add,hw,hv]

def tensorMap (f : E →L[ℂ] E') (g : F →L[ℂ] F') : Joint E F →L[ℂ] Joint E' F' :=
  (TensorProduct.mapL f g).completion

@[simp] theorem tensorMap_tmul (f : E →L[ℂ] E') (g : F →L[ℂ] F') (x : E) (y : F) :
    tensorMap f g (tmulJoint x y)=tmulJoint (f x) (g y) := by
  simp only [tmulJoint_apply,tensorMap,ContinuousLinearMap.completion_apply_coe,
    TensorProduct.mapL_tmul]

theorem norm_tensorMap_le (f : E →L[ℂ] E') (g : F →L[ℂ] F') :
    ‖tensorMap f g‖ ≤ ‖f‖*‖g‖ :=
  (norm_completion_le (TensorProduct.mapL f g)).trans (TensorProduct.norm_mapL_le f g)

@[simp] theorem tensorMap_id_id :
    tensorMap (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ F) =
      ContinuousLinearMap.id ℂ (Joint E F) := by
  apply joint_clm_ext
  intro x y
  simp

@[simp] theorem tensorMap_zero_left (g : F →L[ℂ] F') :
    tensorMap (0 : E →L[ℂ] E') g=0 := by
  apply joint_clm_ext
  intro x y
  simp only [tensorMap_tmul, ContinuousLinearMap.zero_apply, map_zero]

@[simp] theorem tensorMap_zero_right (f : E →L[ℂ] E') :
    tensorMap f (0 : F →L[ℂ] F')=0 := by
  apply joint_clm_ext
  intro x y
  simp only [tensorMap_tmul, ContinuousLinearMap.zero_apply, map_zero,
    ContinuousLinearMap.zero_apply]

theorem tensorMap_comp (f : E' →L[ℂ] E'') (f' : E →L[ℂ] E')
    (g : F' →L[ℂ] F'') (g' : F →L[ℂ] F') :
    tensorMap (f ∘L f') (g ∘L g')=tensorMap f g ∘L tensorMap f' g' := by
  apply joint_clm_ext
  intro x y
  simp

theorem tensorMap_add_left (f f' : E →L[ℂ] E') (g : F →L[ℂ] F') :
    tensorMap (f+f') g=tensorMap f g+tensorMap f' g := by
  apply joint_clm_ext
  intro x y
  simp only [tensorMap_tmul, ContinuousLinearMap.add_apply, map_add]

theorem tensorMap_add_right (f : E →L[ℂ] E') (g g' : F →L[ℂ] F') :
    tensorMap f (g+g')=tensorMap f g+tensorMap f g' := by
  apply joint_clm_ext
  intro x y
  simp only [tensorMap_tmul, ContinuousLinearMap.add_apply, map_add]

theorem tensorMap_smul_left (c : ℂ) (f : E →L[ℂ] E') (g : F →L[ℂ] F') :
    tensorMap (c • f) g=c • tensorMap f g := by
  apply joint_clm_ext
  intro x y
  simp only [tensorMap_tmul, ContinuousLinearMap.smul_apply, map_smul]

theorem tensorMap_smul_right (c : ℂ) (f : E →L[ℂ] E') (g : F →L[ℂ] F') :
    tensorMap f (c • g)=c • tensorMap f g := by
  apply joint_clm_ext
  intro x y
  simp only [tensorMap_tmul, ContinuousLinearMap.smul_apply, map_smul]

def scalarTensor : TensorProduct ℂ ℂ ℂ →L[ℂ] ℂ :=
  (TensorProduct.lidIsometry ℂ ℂ).toLinearIsometry.toContinuousLinearMap

@[simp] theorem scalarTensor_tmul (x y : ℂ) : scalarTensor (x ⊗ₜ[ℂ] y)=x*y := rfl

theorem norm_scalarTensor_le_one : ‖scalarTensor‖ ≤ 1 :=
  (TensorProduct.lidIsometry ℂ ℂ).toLinearIsometry.norm_toContinuousLinearMap_le

def tensorFunctional (phi : E →L[ℂ] ℂ) (psi : F →L[ℂ] ℂ) : Joint E F →L[ℂ] ℂ :=
  (scalarTensor ∘L TensorProduct.mapL phi psi).fromCompletion

@[simp] theorem tensorFunctional_tmul (phi : E →L[ℂ] ℂ) (psi : F →L[ℂ] ℂ)
    (x : E) (y : F) : tensorFunctional phi psi (tmulJoint x y)=phi x*psi y := by
  simp only [tensorFunctional,tmulJoint_apply,ContinuousLinearMap.fromCompletion_apply_coe,
    ContinuousLinearMap.comp_apply,TensorProduct.mapL_tmul,scalarTensor_tmul]

theorem norm_tensorFunctional_le (phi : E →L[ℂ] ℂ) (psi : F →L[ℂ] ℂ) :
    ‖tensorFunctional phi psi‖ ≤ ‖phi‖*‖psi‖ := by
  refine (norm_fromCompletion_le _).trans
    ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_)
  calc
    ‖scalarTensor‖*‖TensorProduct.mapL phi psi‖ ≤ 1*(‖phi‖*‖psi‖) :=
      mul_le_mul norm_scalarTensor_le_one (TensorProduct.norm_mapL_le phi psi)
        (norm_nonneg (TensorProduct.mapL phi psi)) zero_le_one
    _=‖phi‖*‖psi‖ := one_mul _

section NuclearTensor

variable [CompleteSpace E'] [CompleteSpace F']

local instance leftOperatorGroup : NormedAddCommGroup (E →L[ℂ] E') := inferInstance
local instance leftOperatorSpace : NormedSpace ℂ (E →L[ℂ] E') := inferInstance
local instance rightOperatorGroup : NormedAddCommGroup (F →L[ℂ] F') := inferInstance
local instance rightOperatorSpace : NormedSpace ℂ (F →L[ℂ] F') := inferInstance
local instance jointOperatorGroup : NormedAddCommGroup (Joint E F →L[ℂ] Joint E' F') := inferInstance
local instance jointOperatorSpace : NormedSpace ℂ (Joint E F →L[ℂ] Joint E' F') := inferInstance
local instance leftNuclearGroup : NormedAddCommGroup (Nuclear ℂ E E') := inferInstance
local instance leftNuclearSpace : NormedSpace ℂ (Nuclear ℂ E E') := inferInstance
local instance rightNuclearGroup : NormedAddCommGroup (Nuclear ℂ F F') := inferInstance
local instance rightNuclearSpace : NormedSpace ℂ (Nuclear ℂ F F') := inferInstance
local instance jointNuclearGroup : NormedAddCommGroup (Nuclear ℂ (Joint E F) (Joint E' F')) := inferInstance
local instance jointNuclearSpace : NormedSpace ℂ (Nuclear ℂ (Joint E F) (Joint E' F')) := inferInstance
local instance rightNuclearMapGroup :
    NormedAddCommGroup (Nuclear ℂ F F' →L[ℂ] Nuclear ℂ (Joint E F) (Joint E' F')) := inferInstance
local instance rightNuclearMapSpace :
    NormedSpace ℂ (Nuclear ℂ F F' →L[ℂ] Nuclear ℂ (Joint E F) (Joint E' F')) := inferInstance
local instance leftCoefficientMapGroup :
    NormedAddCommGroup (Coefficients ℂ E E' →L[ℂ]
      Nuclear ℂ F F' →L[ℂ] Nuclear ℂ (Joint E F) (Joint E' F')) := inferInstance

def tensorMapRightLinear (f : E →L[ℂ] E') :
    (F →L[ℂ] F') →ₗ[ℂ] (Joint E F →L[ℂ] Joint E' F') where
  toFun := tensorMap f
  map_add' := tensorMap_add_right f
  map_smul' := fun c g => tensorMap_smul_right c f g

def tensorMapRight (f : E →L[ℂ] E') :
    (F →L[ℂ] F') →L[ℂ] (Joint E F →L[ℂ] Joint E' F') := by
  refine ⟨tensorMapRightLinear f, ?_⟩
  exact AddMonoidHomClass.continuous_of_bound (tensorMapRightLinear f) ‖f‖
    (fun g => norm_tensorMap_le f g)

@[simp] theorem tensorMapRight_apply (f : E →L[ℂ] E') (g : F →L[ℂ] F') :
    tensorMapRight f g=tensorMap f g := rfl

def tensorMapLeftLinear (g : F →L[ℂ] F') :
    (E →L[ℂ] E') →ₗ[ℂ] (Joint E F →L[ℂ] Joint E' F') where
  toFun := fun f => tensorMap f g
  map_add' := fun f f' => tensorMap_add_left f f' g
  map_smul' := fun c f => tensorMap_smul_left c f g

def tensorMapLeft (g : F →L[ℂ] F') :
    (E →L[ℂ] E') →L[ℂ] (Joint E F →L[ℂ] Joint E' F') := by
  refine ⟨tensorMapLeftLinear g, ?_⟩
  exact AddMonoidHomClass.continuous_of_bound (tensorMapLeftLinear g) ‖g‖
    (fun f => (norm_tensorMap_le f g).trans_eq (mul_comm _ _))

@[simp] theorem tensorMapLeft_apply (f : E →L[ℂ] E') (g : F →L[ℂ] F') :
    tensorMapLeft g f=tensorMap f g := rfl

def tensorAtom (a : Atom ℂ E E') (b : Atom ℂ F F') :
    Nuclear ℂ (Joint E F) (Joint E' F') :=
  rankOne (tensorFunctional a.1.1 b.1.1) (tmulJoint a.2.1 b.2.1)

@[simp] theorem toOperator_tensorAtom (a : Atom ℂ E E') (b : Atom ℂ F F') :
    toOperator (tensorAtom a b)=tensorMap (atomOperator a) (atomOperator b) := by
  rw [tensorAtom,toOperator_rankOne]
  apply joint_clm_ext
  intro x y
  simp only [ContinuousLinearMap.smulRight_apply,tensorFunctional_tmul,
    tensorMap_tmul,atomOperator_apply,map_smul,ContinuousLinearMap.smul_apply,
    smul_smul, mul_comm]

theorem norm_tensorAtom_le_one (a : Atom ℂ E E') (b : Atom ℂ F F') :
    ‖tensorAtom a b‖ ≤ 1 := by
  have hp : ‖tensorFunctional a.1.1 b.1.1‖ ≤ 1 :=
    (norm_tensorFunctional_le _ _).trans (by
      simpa only [one_mul] using mul_le_mul a.1.2 b.1.2 (norm_nonneg _) zero_le_one)
  have hv : ‖tmulJoint a.2.1 b.2.1‖ ≤ 1 := by
    rw [norm_tmulJoint]
    simpa only [one_mul] using mul_le_mul a.2.2 b.2.2 (norm_nonneg _) zero_le_one
  rw [tensorAtom,norm_rankOne]
  simpa only [one_mul] using mul_le_mul hp hv (norm_nonneg _) zero_le_one

def rightTensorTerms (a : Atom ℂ E E') :
    Coefficients ℂ F F' →L[ℂ] ℓ¹(Atom ℂ F F',Nuclear ℂ (Joint E F) (Joint E' F')) :=
  lp.mapCLM 1 (fun b => ContinuousLinearMap.toSpanSingleton ℂ (tensorAtom a b))
    zero_le_one (fun b => by simpa using norm_tensorAtom_le_one a b)

theorem norm_rightTensorTerms_le_one (a : Atom ℂ E E') :
    ‖rightTensorTerms (F := F) (F' := F') a‖ ≤ 1 :=
  lp.norm_mapCLM_le 1 (fun b : Atom ℂ F F' => ContinuousLinearMap.toSpanSingleton ℂ (tensorAtom a b))
    zero_le_one (fun b => by simpa using norm_tensorAtom_le_one a b)

def rightTensorCoefficients (a : Atom ℂ E E') :
    Coefficients ℂ F F' →L[ℂ] Nuclear ℂ (Joint E F) (Joint E' F') :=
  lp.tsumCLM ℂ (Atom ℂ F F') (Nuclear ℂ (Joint E F) (Joint E' F')) ∘L rightTensorTerms a

@[simp] theorem rightTensorCoefficients_apply (a : Atom ℂ E E')
    (d : Coefficients ℂ F F') :
    rightTensorCoefficients a d=∑' b,d b • tensorAtom a b := by
  simp [rightTensorCoefficients,rightTensorTerms]

theorem norm_rightTensorCoefficients_le_one (a : Atom ℂ E E') :
    ‖rightTensorCoefficients (F := F) (F' := F') a‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  simpa only [one_mul] using mul_le_mul lp.norm_tsumCLM_le
    (norm_rightTensorTerms_le_one (F := F) (F' := F') a)
    (norm_nonneg (rightTensorTerms (F := F) (F' := F') a)) zero_le_one

theorem rightTensorCoefficients_single (a : Atom ℂ E E') (b : Atom ℂ F F') (c : ℂ) :
    rightTensorCoefficients a (lp.single 1 b c : Coefficients ℂ F F')=c • tensorAtom a b := by
  rw [rightTensorCoefficients_apply,tsum_eq_single b]
  · simp
  · intro b' hne
    simp [lp.single_apply,Pi.single_eq_of_ne hne]

theorem hasSum_rightTensorCoefficients (a : Atom ℂ E E') (d : Coefficients ℂ F F') :
    HasSum (fun b => d b • tensorAtom a b) (rightTensorCoefficients a d) := by
  simpa only [rightTensorCoefficients_single] using
    (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) d).mapL (rightTensorCoefficients a)

theorem toOperator_rightTensorCoefficients (a : Atom ℂ E E')
    (d : Coefficients ℂ F F') :
    toOperator (rightTensorCoefficients a d)=tensorMap (atomOperator a) (synthesis d) := by
  have h₁ := (hasSum_rightTensorCoefficients a d).mapL
    (toOperator (𝕜 := ℂ) (E := Joint E F) (F := Joint E' F'))
  have h₂ := ((hasSum_ofCoefficients d).mapL
    (toOperator (𝕜 := ℂ) (E := F) (F := F'))).mapL (tensorMapRight (atomOperator a))
  simp only [map_smul,toOperator_tensorAtom] at h₁
  simp only [map_smul,toOperator_ofAtom,toOperator_ofCoefficients,tensorMapRight_apply,tensorMapLeft_apply] at h₂
  exact h₁.unique h₂

theorem synthesisKernel_le_rightTensorCoefficients_ker (a : Atom ℂ E E') :
    synthesisKernel (𝕜 := ℂ) (E := F) (F := F') ≤ (rightTensorCoefficients a).ker := by
  intro d hd
  change rightTensorCoefficients a d=0
  apply toOperator_injective
  rw [toOperator_rightTensorCoefficients,map_zero]
  have hs : synthesis d=0 := hd
  simp only [hs,tensorMap_zero_right]

def rightTensorAtom (a : Atom ℂ E E') :
    Nuclear ℂ F F' →L[ℂ] Nuclear ℂ (Joint E F) (Joint E' F') :=
  synthesisKernel.liftQL (rightTensorCoefficients a)
    (synthesisKernel_le_rightTensorCoefficients_ker a)

@[simp] theorem rightTensorAtom_ofCoefficients (a : Atom ℂ E E') (d : Coefficients ℂ F F') :
    rightTensorAtom a (ofCoefficients d)=rightTensorCoefficients a d := rfl

@[simp] theorem toOperator_rightTensorAtom (a : Atom ℂ E E') (U : Nuclear ℂ F F') :
    toOperator (rightTensorAtom a U)=tensorMap (atomOperator a) (toOperator U) := by
  obtain ⟨d,rfl⟩ := ofCoefficients_surjective U
  exact toOperator_rightTensorCoefficients a d

theorem norm_rightTensorAtom_apply_le (a : Atom ℂ E E') (U : Nuclear ℂ F F') :
    ‖rightTensorAtom a U‖ ≤ ‖U‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨d,rfl,hd⟩ := exists_representation_norm_lt U hε
  rw [rightTensorAtom_ofCoefficients]
  exact ((rightTensorCoefficients a).le_of_opNorm_le
    (norm_rightTensorCoefficients_le_one a) d).trans (by simpa only [one_mul] using hd.le)

theorem norm_rightTensorAtom_le_one (a : Atom ℂ E E') :
    ‖rightTensorAtom (F := F) (F' := F') a‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun U => by
    simpa only [one_mul] using norm_rightTensorAtom_apply_le a U)

def leftTensorTerms : Coefficients ℂ E E' →L[ℂ]
    ℓ¹(Atom ℂ E E',Nuclear ℂ F F' →L[ℂ] Nuclear ℂ (Joint E F) (Joint E' F')) :=
  lp.mapCLM 1 (fun a : Atom ℂ E E' =>
    ContinuousLinearMap.toSpanSingleton ℂ (rightTensorAtom (F := F) (F' := F') a))
    zero_le_one (fun a => by simpa using norm_rightTensorAtom_le_one a)

theorem norm_leftTensorTerms_le_one :
    ‖leftTensorTerms (E := E) (F := F) (E' := E') (F' := F')‖ ≤ 1 :=
  lp.norm_mapCLM_le 1 (fun a : Atom ℂ E E' =>
    ContinuousLinearMap.toSpanSingleton ℂ (rightTensorAtom (F := F) (F' := F') a))
    zero_le_one (fun a => by simpa using norm_rightTensorAtom_le_one a)

def leftTensorCoefficients : Coefficients ℂ E E' →L[ℂ]
    Nuclear ℂ F F' →L[ℂ] Nuclear ℂ (Joint E F) (Joint E' F') :=
  lp.tsumCLM ℂ (Atom ℂ E E')
    (Nuclear ℂ F F' →L[ℂ] Nuclear ℂ (Joint E F) (Joint E' F')) ∘L leftTensorTerms

@[simp] theorem leftTensorCoefficients_apply (c : Coefficients ℂ E E') :
    leftTensorCoefficients (F := F) (F' := F') c=∑' a,c a • rightTensorAtom a := by
  simp [leftTensorCoefficients,leftTensorTerms]

theorem norm_leftTensorCoefficients_le_one :
    ‖leftTensorCoefficients (E := E) (F := F) (E' := E') (F' := F')‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  simpa only [one_mul] using mul_le_mul lp.norm_tsumCLM_le
    (norm_leftTensorTerms_le_one (E := E) (F := F) (E' := E') (F' := F'))
    (norm_nonneg (leftTensorTerms (E := E) (F := F)
      (E' := E') (F' := F'))) zero_le_one

theorem leftTensorCoefficients_single (a : Atom ℂ E E') (z : ℂ) :
    leftTensorCoefficients (F := F) (F' := F')
      (lp.single 1 a z : Coefficients ℂ E E')=z • rightTensorAtom a := by
  rw [leftTensorCoefficients_apply,tsum_eq_single a]
  · simp
  · intro a' hne
    simp [lp.single_apply,Pi.single_eq_of_ne hne]

theorem hasSum_leftTensorCoefficients (c : Coefficients ℂ E E') :
    HasSum (fun a => c a • rightTensorAtom (F := F) (F' := F') a)
      (leftTensorCoefficients c) := by
  simpa only [leftTensorCoefficients_single] using
    (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) c).mapL
      (leftTensorCoefficients (F := F) (F' := F'))

theorem toOperator_leftTensorCoefficients (c : Coefficients ℂ E E') (U : Nuclear ℂ F F') :
    toOperator (leftTensorCoefficients c U)=tensorMap (synthesis c) (toOperator U) := by
  have h₁ := ((hasSum_leftTensorCoefficients (F := F) (F' := F') c).mapL
    (ContinuousLinearMap.apply ℂ (Nuclear ℂ (Joint E F) (Joint E' F')) U)).mapL
      (toOperator (𝕜 := ℂ) (E := Joint E F) (F := Joint E' F'))
  have h₂ := ((hasSum_ofCoefficients c).mapL
    (toOperator (𝕜 := ℂ) (E := E) (F := E'))).mapL (tensorMapLeft (toOperator U))
  simp only [map_smul,ContinuousLinearMap.apply_apply,ContinuousLinearMap.smul_apply,
    toOperator_rightTensorAtom] at h₁
  simp only [map_smul,toOperator_ofAtom,toOperator_ofCoefficients,
    ContinuousLinearMap.flip_apply,tensorMapRight_apply,tensorMapLeft_apply] at h₂
  exact h₁.unique h₂

theorem synthesisKernel_le_leftTensorCoefficients_ker :
    synthesisKernel (𝕜 := ℂ) (E := E) (F := E') ≤
      (leftTensorCoefficients (F := F) (F' := F')).ker := by
  intro c hc
  change leftTensorCoefficients c=0
  apply ContinuousLinearMap.ext
  intro U
  apply toOperator_injective
  rw [toOperator_leftTensorCoefficients]
  have hs : synthesis c=0 := hc
  simp only [hs,tensorMap_zero_left,ContinuousLinearMap.zero_apply,map_zero]

def tensorNuclear : Nuclear ℂ E E' →L[ℂ]
    Nuclear ℂ F F' →L[ℂ] Nuclear ℂ (Joint E F) (Joint E' F') :=
  synthesisKernel.liftQL leftTensorCoefficients synthesisKernel_le_leftTensorCoefficients_ker

@[simp] theorem tensorNuclear_ofCoefficients (c : Coefficients ℂ E E') (U : Nuclear ℂ F F') :
    tensorNuclear (ofCoefficients c) U=leftTensorCoefficients c U := rfl

@[simp] theorem toOperator_tensorNuclear (T : Nuclear ℂ E E') (U : Nuclear ℂ F F') :
    toOperator (tensorNuclear T U)=tensorMap (toOperator T) (toOperator U) := by
  obtain ⟨c,rfl⟩ := ofCoefficients_surjective T
  exact toOperator_leftTensorCoefficients c U

@[simp] theorem tensorNuclear_ofCoefficients_map (c : Coefficients ℂ E E') :
    tensorNuclear (F := F) (F' := F') (ofCoefficients c)=leftTensorCoefficients c := rfl

theorem norm_leftTensorCoefficients_apply_le (c : Coefficients ℂ E E') :
    ‖leftTensorCoefficients (F := F) (F' := F') c‖ ≤ ‖c‖ := by
  simpa only [one_mul] using
    (leftTensorCoefficients (E := E) (F := F) (E' := E') (F' := F')).le_of_opNorm_le
      (norm_leftTensorCoefficients_le_one (E := E) (F := F) (E' := E') (F' := F')) c

theorem norm_tensorNuclear_apply_le (T : Nuclear ℂ E E') :
    ‖tensorNuclear (F := F) (F' := F') T‖ ≤ ‖T‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨c,hc,hcost⟩ := exists_representation_norm_lt T hε
  rw [← hc,tensorNuclear_ofCoefficients_map]
  exact (norm_leftTensorCoefficients_apply_le c).trans (by
    simpa only [hc] using hcost.le)

theorem norm_tensorNuclear_le (T : Nuclear ℂ E E') (U : Nuclear ℂ F F') :
    ‖tensorNuclear T U‖ ≤ ‖T‖*‖U‖ :=
  (tensorNuclear T).le_of_opNorm_le (norm_tensorNuclear_apply_le T) U

@[simp] theorem tensorNuclear_rankOne (phi : E →L[ℂ] ℂ) (y : E')
    (psi : F →L[ℂ] ℂ) (v : F') :
    tensorNuclear (rankOne phi y) (rankOne psi v)=
      rankOne (tensorFunctional phi psi) (tmulJoint y v) := by
  apply toOperator_injective
  rw [toOperator_tensorNuclear,toOperator_rankOne,toOperator_rankOne,toOperator_rankOne]
  apply joint_clm_ext
  intro x u
  simp only [tensorMap_tmul,ContinuousLinearMap.smulRight_apply,tensorFunctional_tmul,
    map_smul,ContinuousLinearMap.smul_apply,smul_smul,mul_comm]

end NuclearTensor

section NuclearExt

variable [CompleteSpace E']

theorem ofAtom_eq_rankOne (a : Atom ℂ E E') : ofAtom a=rankOne a.1.1 a.2.1 := by
  apply toOperator_injective
  simp only [toOperator_ofAtom,toOperator_rankOne,atomOperator]

theorem nuclear_clm_ext_rankOne {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {f g : Nuclear ℂ E E' →L[ℂ] Z}
    (h : ∀ phi : E →L[ℂ] ℂ,∀ y : E',f (rankOne phi y)=g (rankOne phi y)) : f=g := by
  apply ContinuousLinearMap.ext
  intro T
  obtain ⟨c,rfl⟩ := ofCoefficients_surjective T
  have h₁ := (hasSum_ofCoefficients c).mapL f
  have h₂ := (hasSum_ofCoefficients c).mapL g
  simp only [map_smul,ofAtom_eq_rankOne] at h₁ h₂
  simp_rw [h] at h₁
  exact h₁.unique h₂

end NuclearExt

section TraceProduct

variable [CompleteSpace E] [CompleteSpace F]

theorem trace_tensorNuclear (T : Nuclear ℂ E E) (U : Nuclear ℂ F F) :
    HilbertNuclearTrace.trace (tensorNuclear T U)=
      HilbertNuclearTrace.trace T*HilbertNuclearTrace.trace U := by
  have hrank (phi : E →L[ℂ] ℂ) (y : E) :
      (HilbertNuclearTrace.trace (E := Joint E F)) ∘L tensorNuclear (rankOne phi y) =
        (phi y) • (HilbertNuclearTrace.trace (E := F)) := by
    apply nuclear_clm_ext_rankOne
    intro psi v
    simp only [ContinuousLinearMap.comp_apply,tensorNuclear_rankOne,
      HilbertNuclearTrace.trace_rankOne,tensorFunctional_tmul,smul_apply,smul_eq_mul]
  have h : (HilbertNuclearTrace.trace (E := Joint E F)) ∘L tensorNuclear.flip U =
      (HilbertNuclearTrace.trace U) • (HilbertNuclearTrace.trace (E := E)) := by
    apply nuclear_clm_ext_rankOne
    intro phi y
    have hh := congrArg (fun L : Nuclear ℂ F F →L[ℂ] ℂ => L U) (hrank phi y)
    change HilbertNuclearTrace.trace (tensorNuclear (rankOne phi y) U)=
      phi y*HilbertNuclearTrace.trace U at hh
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
      smul_apply,smul_eq_mul,HilbertNuclearTrace.trace_rankOne]
    exact hh.trans (mul_comm _ _)
  have hh := congrArg (fun L : Nuclear ℂ E E →L[ℂ] ℂ => L T) h
  change HilbertNuclearTrace.trace (tensorNuclear T U)=
    HilbertNuclearTrace.trace U*HilbertNuclearTrace.trace T at hh
  exact hh.trans (mul_comm _ _)

end TraceProduct

section Sandwich

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F']
  [CompleteSpace E''] [CompleteSpace F'']
variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem tensorNuclear_compose (LA : E' →L[ℂ] E'') (RA : G →L[ℂ] E)
    (LB : F' →L[ℂ] F'') (RB : H →L[ℂ] F) (T : Nuclear ℂ E E') (U : Nuclear ℂ F F') :
    tensorNuclear (compose LA RA T) (compose LB RB U)=
      compose (tensorMap LA LB) (tensorMap RA RB) (tensorNuclear T U) := by
  apply toOperator_injective
  simp only [toOperator_tensorNuclear,toOperator_compose,tensorMap_comp]

theorem remote_sandwich_commute (LA : E →L[ℂ] E') (RA : E' →L[ℂ] E)
    (LB : F →L[ℂ] F') (RB : F' →L[ℂ] F) (W : Nuclear ℂ (Joint E F) (Joint E F)) :
    compose (tensorMap (ContinuousLinearMap.id ℂ E') LB)
      (tensorMap (ContinuousLinearMap.id ℂ E') RB)
      (compose (tensorMap LA (ContinuousLinearMap.id ℂ F))
        (tensorMap RA (ContinuousLinearMap.id ℂ F)) W)=
    compose (tensorMap LA (ContinuousLinearMap.id ℂ F'))
      (tensorMap RA (ContinuousLinearMap.id ℂ F'))
      (compose (tensorMap (ContinuousLinearMap.id ℂ E) LB)
        (tensorMap (ContinuousLinearMap.id ℂ E) RB) W) := by
  apply toOperator_injective
  simp only [toOperator_compose]
  have hL : tensorMap (ContinuousLinearMap.id ℂ E') LB ∘L
      tensorMap LA (ContinuousLinearMap.id ℂ F) =
    tensorMap LA (ContinuousLinearMap.id ℂ F') ∘L
      tensorMap (ContinuousLinearMap.id ℂ E) LB := by
    rw [← tensorMap_comp,← tensorMap_comp]
    simp
  have hR : tensorMap RA (ContinuousLinearMap.id ℂ F) ∘L
      tensorMap (ContinuousLinearMap.id ℂ E') RB =
    tensorMap (ContinuousLinearMap.id ℂ E) RB ∘L
      tensorMap RA (ContinuousLinearMap.id ℂ F') := by
    rw [← tensorMap_comp,← tensorMap_comp]
    simp
  simp only [← ContinuousLinearMap.comp_assoc]
  rw [hL]
  simp only [ContinuousLinearMap.comp_assoc]
  rw [hR]

end Sandwich

@[simp] theorem inner_tmulJoint (x v : E) (y w : F) :
    inner ℂ (tmulJoint x y) (tmulJoint v w)=inner ℂ x v*inner ℂ y w := by
  simp only [tmulJoint_apply,UniformSpace.Completion.inner_coe,TensorProduct.inner_tmul]

theorem tensorFunctional_innerSL (x : E) (y : F) :
    tensorFunctional (innerSL ℂ x) (innerSL ℂ y)=innerSL ℂ (tmulJoint x y) := by
  apply joint_clm_ext
  intro v w
  simp only [tensorFunctional_tmul,innerSL_apply_apply,inner_tmulJoint]

section PositiveProduct

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F']

theorem inner_tensorMap_adjoint (f : E →L[ℂ] E') (g : F →L[ℂ] F')
    (z : Joint E F) (w : Joint E' F') :
    inner ℂ (tensorMap f g z) w=inner ℂ z (tensorMap f.adjoint g.adjoint w) := by
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro za
  induction za using TensorProduct.inductionOn with
  | tmul x y =>
      refine UniformSpace.Completion.induction_on w
        (isClosed_eq (by fun_prop) (by fun_prop)) ?_
      intro wa
      induction wa using TensorProduct.inductionOn with
      | tmul v u =>
          change inner ℂ (tensorMap f g (tmulJoint x y)) (tmulJoint v u)=
            inner ℂ (tmulJoint x y) (tensorMap f.adjoint g.adjoint (tmulJoint v u))
          simp only [tensorMap_tmul,inner_tmulJoint,ContinuousLinearMap.adjoint_inner_right]
      | add w v hw hv =>
          simpa only [UniformSpace.Completion.coe_add,map_add,inner_add_right,hw,hv]
  | add z v hz hv =>
      simpa only [UniformSpace.Completion.coe_add,map_add,inner_add_left,hz,hv]

theorem tensorMap_adjoint (f : E →L[ℂ] E') (g : F →L[ℂ] F') :
    (tensorMap f g).adjoint=tensorMap f.adjoint g.adjoint := by
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℂ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_tensorMap_adjoint f g z w

theorem tensorMap_isPositive {f : E →L[ℂ] E} {g : F →L[ℂ] F}
    (hf : f.IsPositive) (hg : g.IsPositive) : (tensorMap f g).IsPositive := by
  obtain ⟨s,hs,-,hsq⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    hf.isSelfAdjoint hf.spectrumRestricts
  obtain ⟨t,ht,-,htq⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
    hg.isSelfAdjoint hg.spectrumRestricts
  have hsadj : s.adjoint=s := hs.star_eq
  have htadj : t.adjoint=t := ht.star_eq
  have hadj : (tensorMap s t).adjoint=tensorMap s t := by
    rw [tensorMap_adjoint,hsadj,htadj]
  rw [← hsq,← htq]
  change (tensorMap (s ∘L s) (t ∘L t)).IsPositive
  rw [tensorMap_comp]
  simpa only [hadj] using ContinuousLinearMap.isPositive_adjoint_comp_self (tensorMap s t)

theorem tensorNuclear_isPositive (T : Nuclear ℂ E E) (U : Nuclear ℂ F F)
    (hT : (toOperator T).IsPositive) (hU : (toOperator U).IsPositive) :
    (toOperator (tensorNuclear T U)).IsPositive := by
  rw [toOperator_tensorNuclear]
  exact tensorMap_isPositive hT hU

end PositiveProduct

section SimpleDensity

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F']

def rankOneLinear : (E →L[ℂ] ℂ) →ₗ[ℂ] E' →ₗ[ℂ] Nuclear ℂ E E' where
  toFun phi :=
    { toFun := rankOne phi
      map_add' := fun y z => by
        apply toOperator_injective
        ext x
        simp only [map_add,toOperator_rankOne,ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smulRight_apply,smul_add]
      map_smul' := fun c y => by
        apply toOperator_injective
        ext x
        simp only [map_smul,toOperator_rankOne,ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.smulRight_apply,smul_smul,smul_eq_mul]
        exact congrArg (fun z : ℂ => z • y) (mul_comm (phi x) c) }
  map_add' phi psi := by
    apply LinearMap.ext
    intro y
    change rankOne (phi+psi) y=rankOne phi y+rankOne psi y
    apply toOperator_injective
    ext x
    simp only [map_add,toOperator_rankOne,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply,add_smul]
  map_smul' c phi := by
    apply LinearMap.ext
    intro y
    change rankOne (c • phi) y=c • rankOne phi y
    apply toOperator_injective
    ext x
    simp only [map_smul,toOperator_rankOne,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_smul,smul_eq_mul]

local instance rankOneTargetNormedGroup : NormedAddCommGroup (Nuclear ℂ E E') := inferInstance
local instance rankOneTargetNormedSpace : NormedSpace ℂ (Nuclear ℂ E E') := inferInstance
local instance rankOneMapNormedGroup : NormedAddCommGroup (E' →L[ℂ] Nuclear ℂ E E') := inferInstance
local instance rankOneMapNormedSpace : NormedSpace ℂ (E' →L[ℂ] Nuclear ℂ E E') := inferInstance

def rankOneRight (phi : E →L[ℂ] ℂ) : E' →L[ℂ] Nuclear ℂ E E' := by
  refine ⟨rankOneLinear phi, ?_⟩
  exact AddMonoidHomClass.continuous_of_bound (rankOneLinear phi) ‖phi‖
    (fun y => by change ‖rankOne phi y‖ ≤ ‖phi‖*‖y‖; exact norm_rankOne_le phi y)

@[simp] theorem rankOneRight_apply (phi : E →L[ℂ] ℂ) (y : E') :
    rankOneRight phi y=rankOne phi y := rfl

theorem norm_rankOneRight_le (phi : E →L[ℂ] ℂ) : ‖rankOneRight (E' := E') phi‖ ≤ ‖phi‖ :=
  (rankOneRight phi).opNorm_le_bound (norm_nonneg phi) (fun y => norm_rankOne_le phi y)

def rankOneCLMLinear : (E →L[ℂ] ℂ) →ₗ[ℂ] E' →L[ℂ] Nuclear ℂ E E' where
  toFun := rankOneRight
  map_add' phi psi := by
    ext y
    exact congrArg (fun L : E' →ₗ[ℂ] Nuclear ℂ E E' => L y) ((rankOneLinear (E := E) (E' := E')).map_add phi psi)
  map_smul' c phi := by
    ext y
    exact congrArg (fun L : E' →ₗ[ℂ] Nuclear ℂ E E' => L y) ((rankOneLinear (E := E) (E' := E')).map_smul c phi)

def rankOneCLM : (E →L[ℂ] ℂ) →L[ℂ] E' →L[ℂ] Nuclear ℂ E E' := by
  refine ⟨rankOneCLMLinear, ?_⟩
  exact AddMonoidHomClass.continuous_of_bound (rankOneCLMLinear (E := E) (E' := E')) 1
    (fun phi => by change ‖rankOneRight phi‖ ≤ 1*‖phi‖
                   simpa only [one_mul] using norm_rankOneRight_le phi)

@[simp] theorem rankOneCLM_apply (phi : E →L[ℂ] ℂ) (y : E') :
    rankOneCLM phi y=rankOne phi y := rfl

theorem rankOne_add_vector (phi : E →L[ℂ] ℂ) (y z : E') :
    rankOne phi (y+z)=rankOne phi y+rankOne phi z :=
  (rankOneLinear (E := E) (E' := E') phi).map_add y z

theorem rankOne_add_functional (phi psi : E →L[ℂ] ℂ) (y : E') :
    rankOne (phi+psi) y=rankOne phi y+rankOne psi y := by
  exact congrArg (fun L : E' →ₗ[ℂ] Nuclear ℂ E E' => L y)
    ((rankOneLinear (E := E) (E' := E')).map_add phi psi)

theorem rankOne_tmul_innerSL (x : E) (u : F) (y : E') (w : F') :
    rankOne (innerSL ℂ (tmulJoint x u)) (tmulJoint y w)=
      tensorNuclear (rankOne (innerSL ℂ x) y) (rankOne (innerSL ℂ u) w) := by
  rw [tensorNuclear_rankOne,tensorFunctional_innerSL]

local instance densityJointNuclearGroup :
    NormedAddCommGroup (Nuclear ℂ (Joint E F) (Joint E' F')) := inferInstance
local instance densityJointNuclearSpace :
    NormedSpace ℂ (Nuclear ℂ (Joint E F) (Joint E' F')) := inferInstance
local instance densityJointFunctionalGroup :
    NormedAddCommGroup (Joint E F →L[ℂ] ℂ) := inferInstance
local instance densityRankOneMapGroup :
    NormedAddCommGroup (Joint E' F' →L[ℂ] Nuclear ℂ (Joint E F) (Joint E' F')) := inferInstance

def simpleNuclearSpan : Submodule ℂ (Nuclear ℂ (Joint E F) (Joint E' F')) :=
  Submodule.span ℂ {W | ∃ T : Nuclear ℂ E E',∃ U : Nuclear ℂ F F', W=tensorNuclear T U}

theorem dense_simpleNuclearSpan :
    Dense (simpleNuclearSpan (E := E) (F := F) (E' := E') (F' := F') :
      Set (Nuclear ℂ (Joint E F) (Joint E' F'))) := by
  let K := (simpleNuclearSpan (E := E) (F := F) (E' := E') (F' := F')).topologicalClosure
  have hK : IsClosed (K : Set (Nuclear ℂ (Joint E F) (Joint E' F'))) :=
    Submodule.isClosed_topologicalClosure _
  have hpure (x : E) (u : F) (v : Joint E' F') :
      rankOne (innerSL ℂ (tmulJoint x u)) v ∈ K := by
    refine UniformSpace.Completion.induction_on v
      (hK.preimage (rankOneCLM (innerSL ℂ (tmulJoint x u))).continuous) ?_
    intro va
    induction va using TensorProduct.inductionOn with
    | tmul y w =>
        change rankOne (innerSL ℂ (tmulJoint x u)) (tmulJoint y w) ∈ K
        apply (simpleNuclearSpan (E := E) (F := F) (E' := E') (F' := F')).le_topologicalClosure
        exact Submodule.subset_span ⟨rankOne (innerSL ℂ x) y,rankOne (innerSL ℂ u) w,
          rankOne_tmul_innerSL x u y w⟩
    | add y w hy hw =>
        rw [UniformSpace.Completion.coe_add]
        rw [rankOne_add_vector]
        exact K.add_mem hy hw
  have hall (z : Joint E F) (v : Joint E' F') : rankOne (innerSL ℂ z) v ∈ K := by
    have hcont : Continuous (fun z : Joint E F => rankOne (innerSL ℂ z) v) := by
      simpa only [Function.comp_def, ContinuousLinearMap.flip_apply, rankOneCLM_apply] using
        ((rankOneCLM (E := Joint E F) (E' := Joint E' F')).flip v).continuous.comp
          (innerSL ℂ : Joint E F →L⋆[ℂ] (Joint E F →L[ℂ] ℂ)).continuous
    refine UniformSpace.Completion.induction_on z (hK.preimage hcont) ?_
    intro za
    induction za using TensorProduct.inductionOn with
    | tmul x u => exact hpure x u v
    | add x u hx hu =>
        rw [UniformSpace.Completion.coe_add]
        rw [map_add,rankOne_add_functional]
        exact K.add_mem hx hu
  have hrank (phi : Joint E F →L[ℂ] ℂ) (v : Joint E' F') : rankOne phi v ∈ K := by
    let z := (InnerProductSpace.toDual ℂ (Joint E F)).symm phi
    have hz : innerSL ℂ z=phi := by
      apply ContinuousLinearMap.ext
      intro x
      change ⟪(InnerProductSpace.toDual ℂ (Joint E F)).symm phi,x⟫_ℂ=phi x
      exact InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := Joint E F)
    rw [← hz]
    exact hall z v
  have hfull (W : Nuclear ℂ (Joint E F) (Joint E' F')) : W ∈ K := by
    obtain ⟨c,rfl⟩ := ofCoefficients_surjective W
    apply hK.mem_of_tendsto (hasSum_ofCoefficients c)
    exact Filter.Eventually.of_forall (fun s => K.sum_mem (fun a ha =>
      K.smul_mem (c a) (by rw [ofAtom_eq_rankOne]; exact hrank a.1.1 a.2.1)))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro W hW
  exact hfull W

end SimpleDensity

section TensorExt

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F']

theorem nuclear_joint_clm_ext_tensors {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    {f g : Nuclear ℂ (Joint E F) (Joint E' F') →L[ℂ] Z}
    (h : ∀ T : Nuclear ℂ E E',∀ U : Nuclear ℂ F F',f (tensorNuclear T U)=g (tensorNuclear T U)) :
    f=g := by
  have hspan : simpleNuclearSpan (E := E) (F := F) (E' := E') (F' := F') ≤ (f-g).ker := by
    apply Submodule.span_le.mpr
    rintro W ⟨T,U,rfl⟩
    change f (tensorNuclear T U)-g (tensorNuclear T U)=0
    exact sub_eq_zero.mpr (h T U)
  have hclosure := (simpleNuclearSpan (E := E) (F := F) (E' := E') (F' := F')).topologicalClosure_minimal
    hspan (f-g).isClosed_ker
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mp
    (dense_simpleNuclearSpan (E := E) (F := F) (E' := E') (F' := F'))
  rw [hd] at hclosure
  apply sub_eq_zero.mp
  apply ContinuousLinearMap.ext
  intro W
  simp only [zero_apply]
  exact hclosure (Submodule.mem_top)

end TensorExt

section FiniteTensorCoordinates

variable (I J : Type*) [Fintype I] [Fintype J]

def finiteTensorEmbedding : EuclideanSpace ℂ (I×J) →ₗᵢ[ℂ]
    Joint (EuclideanSpace ℂ I) (EuclideanSpace ℂ J) :=
  UniformSpace.Completion.toComplₗᵢ.comp
    (((EuclideanSpace.basisFun I ℂ).tensorProduct (EuclideanSpace.basisFun J ℂ)).repr.symm.toLinearIsometry)

theorem finiteTensorEmbedding_norm (x : EuclideanSpace ℂ (I×J)) :
    ‖finiteTensorEmbedding I J x‖=‖x‖ := (finiteTensorEmbedding I J).norm_map x

@[simp] theorem finiteTensorEmbedding_single (i : I) (j : J) :
    finiteTensorEmbedding I J (EuclideanSpace.single (i,j) (1 : ℂ))=
      tmulJoint (EuclideanSpace.single i (1 : ℂ)) (EuclideanSpace.single j (1 : ℂ)) := by
  classical
  change (↑(((EuclideanSpace.basisFun I ℂ).tensorProduct (EuclideanSpace.basisFun J ℂ)).repr.symm
      (EuclideanSpace.single (i,j) (1 : ℂ))) : Joint (EuclideanSpace ℂ I) (EuclideanSpace ℂ J))=
    ↑(EuclideanSpace.single i (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single j (1 : ℂ))
  rw [OrthonormalBasis.repr_symm_single,OrthonormalBasis.tensorProduct_apply,
    EuclideanSpace.basisFun_apply,EuclideanSpace.basisFun_apply]

end FiniteTensorCoordinates

section AlgebraicNuclearLift

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace E'] [CompleteSpace F']

def algebraicNuclearTensor :
    (Nuclear ℂ E E' ⊗[ℂ] Nuclear ℂ F F') →ₗ[ℂ] Nuclear ℂ (Joint E F) (Joint E' F') :=
  TensorProduct.lift (tensorNuclear (E := E) (F := F) (E' := E') (F' := F')).toLinearMap₁₂

@[simp] theorem algebraicNuclearTensor_tmul (T : Nuclear ℂ E E') (U : Nuclear ℂ F F') :
    algebraicNuclearTensor (T ⊗ₜ[ℂ] U)=tensorNuclear T U := rfl

theorem range_algebraicNuclearTensor :
    (algebraicNuclearTensor (E := E) (F := F) (E' := E') (F' := F')).range=
      simpleNuclearSpan (E := E) (F := F) (E' := E') (F' := F') := by
  apply le_antisymm
  · rintro W ⟨z,rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul T U =>
        rw [algebraicNuclearTensor_tmul]
        exact Submodule.subset_span ⟨T,U,rfl⟩
    | add z w hz hw =>
        rw [map_add]
        exact Submodule.add_mem _ hz hw
  · apply Submodule.span_le.mpr
    rintro W ⟨T,U,rfl⟩
    exact ⟨T ⊗ₜ[ℂ] U,rfl⟩

theorem denseRange_algebraicNuclearTensor :
    DenseRange (algebraicNuclearTensor (E := E) (F := F) (E' := E') (F' := F')) := by
  change Dense ((algebraicNuclearTensor (E := E) (F := F) (E' := E') (F' := F')).range :
    Set (Nuclear ℂ (Joint E F) (Joint E' F')))
  rw [range_algebraicNuclearTensor]
  exact dense_simpleNuclearSpan

end AlgebraicNuclearLift

end QuantumProver.MatrixNuclearTensor
