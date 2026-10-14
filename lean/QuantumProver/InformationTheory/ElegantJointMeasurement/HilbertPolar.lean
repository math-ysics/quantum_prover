import Mathlib.Analysis.InnerProductSpace.StarOrder
import QuantumProver.InformationTheory.ElegantJointMeasurement.IConcurrence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open MeasureTheory InnerProductSpace Filter
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Topology Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.HilbertPolar

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

abbrev Source (I : Type*) [Fintype I] := EuclideanSpace ℂ I

local instance sourceComplete : CompleteSpace (Source I) :=
  PiLp.completeSpace 2 (fun _ : I => ℂ)

local instance sourceEndomorphismComplete : CompleteSpace (Source I →L[ℂ] Source I) :=
  ContinuousLinearMap.instCompleteSpace

abbrev matrixOperator : Matrix I I ℂ ≃⋆ₐ[ℂ] (Source I →L[ℂ] Source I) :=
  Matrix.toEuclideanCLM

theorem continuous_matrixOperator : Continuous (matrixOperator (I := I)) :=
  (StarAlgEquiv.isometry (matrixOperator (I := I))).continuous

theorem continuous_matrixOperator_symm : Continuous (matrixOperator (I := I)).symm :=
  (StarAlgEquiv.isometry (matrixOperator (I := I)).symm).continuous

def gram (K : Source I →L[ℂ] E) : Source I →L[ℂ] Source I := K.adjoint ∘L K

def gramMatrix (K : Source I →L[ℂ] E) : Matrix I I ℂ := matrixOperator.symm (gram K)

@[simp] theorem matrixOperator_gramMatrix (K : Source I →L[ℂ] E) :
    matrixOperator (gramMatrix K) = gram K := matrixOperator.apply_symm_apply _

theorem gram_nonneg (K : Source I →L[ℂ] E) : 0 ≤ gram K :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr K.isPositive_adjoint_comp_self

theorem gramMatrix_posSemidef (K : Source I →L[ℂ] E) : (gramMatrix K).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (map_nonneg matrixOperator.symm (gram_nonneg K))

def positiveInput (K : Source I →L[ℂ] E) : Source I →L[ℂ] Source I := CFC.sqrt (gram K)

def positiveInputMatrix (K : Source I →L[ℂ] E) : Matrix I I ℂ := CFC.sqrt (gramMatrix K)

theorem matrixOperator_positiveInputMatrix (K : Source I →L[ℂ] E) :
    matrixOperator (positiveInputMatrix K) = positiveInput K := by
  apply Eq.symm
  apply CFC.sqrt_unique
  · rw [← map_mul, positiveInputMatrix, CFC.sqrt_mul_sqrt_self _ (gramMatrix_posSemidef K).nonneg,
      matrixOperator_gramMatrix]
  · exact map_nonneg matrixOperator (CFC.sqrt_nonneg _)

theorem positiveInput_selfAdjoint (K : Source I →L[ℂ] E) :
    (positiveInput K).adjoint = positiveInput K :=
  (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (gram K))).star_eq

theorem positiveInput_square (K : Source I →L[ℂ] E) :
    positiveInput K ∘L positiveInput K = gram K :=
  CFC.sqrt_mul_sqrt_self _ (gram_nonneg K)

theorem positiveInputMatrix_spectral (K : Source I →L[ℂ] E) :
    positiveInputMatrix K = (gramMatrix_posSemidef K).isHermitian.cfc Real.sqrt := by
  unfold positiveInputMatrix
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ _ (gramMatrix_posSemidef K).nonneg,
    (gramMatrix_posSemidef K).isHermitian.cfc_eq]
  apply QuantumProver.ElegantJointMeasurement.CP.spectralReal_eq
  intro i
  simp [Real.coe_sqrt, Real.coe_toNNReal',
    max_eq_left ((gramMatrix_posSemidef K).eigenvalues_nonneg i)]

def rootPseudoInverseMatrix (K : Source I →L[ℂ] E) : Matrix I I ℂ :=
  (gramMatrix_posSemidef K).isHermitian.cfc (fun x => (Real.sqrt x)⁻¹)

def supportMatrix (K : Source I →L[ℂ] E) : Matrix I I ℂ :=
  (gramMatrix_posSemidef K).isHermitian.cfc (fun x => if Real.sqrt x = 0 then 0 else 1)

def rootPseudoInverse (K : Source I →L[ℂ] E) : Source I →L[ℂ] Source I :=
  matrixOperator (rootPseudoInverseMatrix K)

def support (K : Source I →L[ℂ] E) : Source I →L[ℂ] Source I :=
  matrixOperator (supportMatrix K)

def complement (K : Source I →L[ℂ] E) : Source I →L[ℂ] Source I := 1 - support K

theorem rootPseudoInverse_selfAdjoint (K : Source I →L[ℂ] E) :
    (rootPseudoInverse K).adjoint = rootPseudoInverse K := by
  change star (matrixOperator (rootPseudoInverseMatrix K)) = _
  rw [← map_star]
  exact congrArg matrixOperator (QuantumProver.ElegantJointMeasurement.CP.spectralReal_hermitian _ _).eq

theorem support_selfAdjoint (K : Source I →L[ℂ] E) : (support K).adjoint = support K := by
  change star (matrixOperator (supportMatrix K)) = _
  rw [← map_star]
  exact congrArg matrixOperator (QuantumProver.ElegantJointMeasurement.CP.spectralReal_hermitian _ _).eq

theorem support_square (K : Source I →L[ℂ] E) : support K ∘L support K = support K := by
  change matrixOperator (supportMatrix K) * matrixOperator (supportMatrix K) = _
  rw [← map_mul]
  apply congrArg matrixOperator
  unfold supportMatrix
  rw [QuantumProver.ElegantJointMeasurement.CP.spectralReal_mul]
  apply QuantumProver.ElegantJointMeasurement.CP.spectralReal_eq
  intro i
  split_ifs <;> simp

theorem rootPseudoInverse_comp_positiveInput (K : Source I →L[ℂ] E) :
    rootPseudoInverse K ∘L positiveInput K = support K := by
  rw [← matrixOperator_positiveInputMatrix]
  change matrixOperator (rootPseudoInverseMatrix K) * matrixOperator (positiveInputMatrix K) = _
  rw [← map_mul]
  apply congrArg matrixOperator
  rw [positiveInputMatrix_spectral]
  unfold rootPseudoInverseMatrix supportMatrix
  rw [QuantumProver.ElegantJointMeasurement.CP.spectralReal_mul]
  apply QuantumProver.ElegantJointMeasurement.CP.spectralReal_eq
  intro i
  by_cases h : Real.sqrt ((gramMatrix_posSemidef K).isHermitian.eigenvalues i) = 0 <;> simp [h]

theorem support_comp_positiveInput (K : Source I →L[ℂ] E) :
    support K ∘L positiveInput K = positiveInput K := by
  rw [← matrixOperator_positiveInputMatrix]
  change matrixOperator (supportMatrix K) * matrixOperator (positiveInputMatrix K) = _
  rw [← map_mul]
  apply congrArg matrixOperator
  rw [positiveInputMatrix_spectral]
  unfold supportMatrix
  rw [QuantumProver.ElegantJointMeasurement.CP.spectralReal_mul]
  apply QuantumProver.ElegantJointMeasurement.CP.spectralReal_eq
  intro i
  by_cases h : Real.sqrt ((gramMatrix_posSemidef K).isHermitian.eigenvalues i) = 0 <;> simp [h]

theorem rootPseudoInverse_gram_rootPseudoInverse (K : Source I →L[ℂ] E) :
    rootPseudoInverse K ∘L gram K ∘L rootPseudoInverse K = support K := by
  rw [← matrixOperator_gramMatrix]
  change matrixOperator (rootPseudoInverseMatrix K) * matrixOperator (gramMatrix K) *
    matrixOperator (rootPseudoInverseMatrix K) = _
  rw [← map_mul, ← map_mul]
  apply congrArg matrixOperator
  conv_lhs => rw [(gramMatrix_posSemidef K).isHermitian.spectral_theorem]
  change rootPseudoInverseMatrix K * (gramMatrix_posSemidef K).isHermitian.cfc (fun x => x) *
    rootPseudoInverseMatrix K = supportMatrix K
  unfold rootPseudoInverseMatrix supportMatrix
  rw [QuantumProver.ElegantJointMeasurement.CP.spectralReal_mul, QuantumProver.ElegantJointMeasurement.CP.spectralReal_mul]
  apply QuantumProver.ElegantJointMeasurement.CP.spectralReal_eq
  intro i
  have hn := (gramMatrix_posSemidef K).eigenvalues_nonneg i
  by_cases h : Real.sqrt ((gramMatrix_posSemidef K).isHermitian.eigenvalues i) = 0
  · have hz : (gramMatrix_posSemidef K).isHermitian.eigenvalues i = 0 := by
      nlinarith [Real.mul_self_sqrt hn]
    simp [hz]
  · simp only [if_neg h]
    calc
      (Real.sqrt ((gramMatrix_posSemidef K).isHermitian.eigenvalues i))⁻¹ *
          (gramMatrix_posSemidef K).isHermitian.eigenvalues i *
          (Real.sqrt ((gramMatrix_posSemidef K).isHermitian.eigenvalues i))⁻¹ =
        (Real.sqrt ((gramMatrix_posSemidef K).isHermitian.eigenvalues i))⁻¹ *
          (Real.sqrt ((gramMatrix_posSemidef K).isHermitian.eigenvalues i) *
            Real.sqrt ((gramMatrix_posSemidef K).isHermitian.eigenvalues i)) *
          (Real.sqrt ((gramMatrix_posSemidef K).isHermitian.eigenvalues i))⁻¹ := by
        rw [Real.mul_self_sqrt hn]
      _ = 1 := by field_simp

theorem complement_selfAdjoint (K : Source I →L[ℂ] E) :
    (complement K).adjoint = complement K := by
  simp only [complement, map_sub, support_selfAdjoint, ContinuousLinearMap.adjoint_one]

theorem complement_square (K : Source I →L[ℂ] E) :
    complement K ∘L complement K = complement K := by
  change (1 - support K) * (1 - support K) = _
  rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul]
  have hs : support K * support K = support K := support_square K
  rw [hs]
  unfold complement
  abel

theorem complement_comp_positiveInput (K : Source I →L[ℂ] E) :
    complement K ∘L positiveInput K = 0 := by
  change (1 - support K) * positiveInput K = 0
  rw [sub_mul, one_mul]
  exact sub_eq_zero.mpr (support_comp_positiveInput K).symm

theorem positiveInput_comp_complement (K : Source I →L[ℂ] E) :
    positiveInput K ∘L complement K = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint (complement_comp_positiveInput K)
  simpa only [ContinuousLinearMap.adjoint_comp, complement_selfAdjoint,
    positiveInput_selfAdjoint, map_zero] using h

theorem comp_complement (K : Source I →L[ℂ] E) : K ∘L complement K = 0 := by
  apply ContinuousLinearMap.adjoint_comp_self_eq_zero_iff.mp
  simp only [ContinuousLinearMap.adjoint_comp, complement_selfAdjoint,
    ContinuousLinearMap.comp_assoc]
  change complement K ∘L (gram K ∘L complement K) = 0
  rw [← positiveInput_square, ContinuousLinearMap.comp_assoc,
    positiveInput_comp_complement, ContinuousLinearMap.comp_zero, ContinuousLinearMap.comp_zero]

theorem comp_support (K : Source I →L[ℂ] E) : K ∘L support K = K := by
  have h := comp_complement K
  rw [complement, ContinuousLinearMap.comp_sub, ContinuousLinearMap.one_def,
    ContinuousLinearMap.comp_id] at h
  exact (sub_eq_zero.mp h).symm

def polar (K : Source I →L[ℂ] E) : Source I →L[ℂ] E := K ∘L rootPseudoInverse K

theorem polar_comp_positiveInput (K : Source I →L[ℂ] E) :
    polar K ∘L positiveInput K = K := by
  rw [polar, ContinuousLinearMap.comp_assoc, rootPseudoInverse_comp_positiveInput, comp_support]

theorem polar_gram (K : Source I →L[ℂ] E) : (polar K).adjoint ∘L polar K = support K := by
  unfold polar
  simp only [ContinuousLinearMap.adjoint_comp, rootPseudoInverse_selfAdjoint,
    ContinuousLinearMap.comp_assoc]
  simpa only [gram, ContinuousLinearMap.comp_assoc] using rootPseudoInverse_gram_rootPseudoInverse K

theorem support_isStarProjection (K : Source I →L[ℂ] E) : IsStarProjection (support K) :=
  ⟨support_square K, support_selfAdjoint K⟩

theorem norm_polar_le_one (K : Source I →L[ℂ] E) : ‖polar K‖ ≤ 1 := by
  have h := IsStarProjection.norm_le (support K) (support_isStarProjection K)
  rw [← polar_gram, ContinuousLinearMap.norm_adjoint_comp_self] at h
  nlinarith [norm_nonneg (polar K)]

theorem polar_comp_support (K : Source I →L[ℂ] E) : polar K ∘L support K = polar K := by
  have hzero : polar K ∘L complement K = 0 := by
    apply ContinuousLinearMap.adjoint_comp_self_eq_zero_iff.mp
    simp only [ContinuousLinearMap.adjoint_comp, complement_selfAdjoint,
      ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.comp_assoc (polar K).adjoint, polar_gram]
    change complement K * (support K * (1 - support K)) = 0
    rw [mul_sub, mul_one]
    change complement K * (support K - support K ∘L support K) = 0
    rw [support_square, sub_self, mul_zero]
  rw [complement, ContinuousLinearMap.comp_sub, ContinuousLinearMap.one_def,
    ContinuousLinearMap.comp_id] at hzero
  exact (sub_eq_zero.mp hzero).symm

theorem continuous_gram : Continuous (gram (I := I) (E := E)) :=
  (ContinuousLinearMap.adjoint.continuous.comp continuous_id).clm_comp continuous_id

theorem continuous_gramMatrix : Continuous (gramMatrix (I := I) (E := E)) :=
  continuous_matrixOperator_symm.comp continuous_gram

theorem continuous_positiveInput : Continuous (positiveInput (I := I) (E := E)) :=
  CFC.continuousOn_sqrt.comp_continuous continuous_gram (fun K => gram_nonneg K)

private theorem continuous_gram_cfc (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (fun K : Source I →L[ℂ] E => cfc f (gramMatrix K)) := by
  exact Continuous.cfc_of_mem_nhdsSet f (s := Set.univ) (by simp) continuous_gramMatrix
    (fun K => (gramMatrix_posSemidef K).isHermitian) hf.continuousOn

def regularizedRootInverseMatrix (K : Source I →L[ℂ] E) (N : ℕ) : Matrix I I ℂ :=
  cfc (fun x : ℝ => (Real.sqrt (max x 0 + QuantumProver.ElegantJointMeasurement.CP.polarEpsilon N))⁻¹) (gramMatrix K)

def regularizedPolar (K : Source I →L[ℂ] E) (N : ℕ) : Source I →L[ℂ] E :=
  K ∘L matrixOperator (regularizedRootInverseMatrix K N)

def regularizedSupportMatrix (K : Source I →L[ℂ] E) (N : ℕ) : Matrix I I ℂ :=
  cfc (fun x : ℝ => max x 0 / (max x 0 + QuantumProver.ElegantJointMeasurement.CP.polarEpsilon N)) (gramMatrix K)

def regularizedSupport (K : Source I →L[ℂ] E) (N : ℕ) : Source I →L[ℂ] Source I :=
  matrixOperator (regularizedSupportMatrix K N)

theorem continuous_regularizedRootInverseMatrix (N : ℕ) :
    Continuous (fun K : Source I →L[ℂ] E => regularizedRootInverseMatrix K N) := by
  apply continuous_gram_cfc
  apply Continuous.inv₀
  · fun_prop
  · intro x
    exact ne_of_gt (Real.sqrt_pos.mpr
      (add_pos_of_nonneg_of_pos (le_max_right x 0) (QuantumProver.ElegantJointMeasurement.CP.polarEpsilon_pos N)))

theorem continuous_regularizedPolar (N : ℕ) :
    Continuous (fun K : Source I →L[ℂ] E => regularizedPolar K N) :=
  continuous_id.clm_comp (continuous_matrixOperator.comp (continuous_regularizedRootInverseMatrix N))

theorem continuous_regularizedSupport (N : ℕ) :
    Continuous (fun K : Source I →L[ℂ] E => regularizedSupport K N) := by
  apply continuous_matrixOperator.comp
  apply continuous_gram_cfc
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact ne_of_gt (add_pos_of_nonneg_of_pos (le_max_right x 0) (QuantumProver.ElegantJointMeasurement.CP.polarEpsilon_pos N))

private theorem scalar_support_tendsto (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun N => max x 0 / (max x 0 + QuantumProver.ElegantJointMeasurement.CP.polarEpsilon N)) atTop
      (nhds (if Real.sqrt x = 0 then 0 else 1)) := by
  by_cases hz : x = 0
  · subst x
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne hx (Ne.symm hz)))
    simpa [max_eq_left hx, hs, hz] using!
      (tendsto_const_nhds.div (tendsto_const_nhds.add QuantumProver.ElegantJointMeasurement.CP.polarEpsilon_tendsto) (by simpa using hz) :
        Tendsto (fun N => x / (x + QuantumProver.ElegantJointMeasurement.CP.polarEpsilon N)) atTop (nhds (x / (x + 0))))

private theorem scalar_polar_tendsto (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun N => (if Real.sqrt x = 0 then 0 else 1) *
      (Real.sqrt (max x 0 + QuantumProver.ElegantJointMeasurement.CP.polarEpsilon N))⁻¹) atTop (nhds (Real.sqrt x)⁻¹) := by
  by_cases hs : Real.sqrt x = 0
  · simpa [hs] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · have hAdd : Tendsto (fun N => x + QuantumProver.ElegantJointMeasurement.CP.polarEpsilon N) atTop (nhds x) := by
      simpa using (tendsto_const_nhds.add QuantumProver.ElegantJointMeasurement.CP.polarEpsilon_tendsto)
    have h := (Real.continuous_sqrt.tendsto x).comp hAdd
    simpa [max_eq_left hx, hs, Function.comp_def] using h.inv₀ hs

theorem tendsto_regularizedSupport (K : Source I →L[ℂ] E) :
    Tendsto (regularizedSupport K) atTop (nhds (support K)) := by
  have hlim : Tendsto (regularizedSupportMatrix K) atTop (nhds (supportMatrix K)) := by
    unfold regularizedSupportMatrix supportMatrix
    simp_rw [(gramMatrix_posSemidef K).isHermitian.cfc_eq]
    exact QuantumProver.ElegantJointMeasurement.CP.spectralReal_tendsto _ _ _ (fun i => scalar_support_tendsto _
      ((gramMatrix_posSemidef K).eigenvalues_nonneg i))
  exact continuous_matrixOperator.tendsto (supportMatrix K) |>.comp hlim

theorem tendsto_regularizedPolar (K : Source I →L[ℂ] E) :
    Tendsto (regularizedPolar K) atTop (nhds (polar K)) := by
  have heq (N : ℕ) : regularizedPolar K N = K ∘L
      matrixOperator ((gramMatrix_posSemidef K).isHermitian.cfc (fun x =>
        (if Real.sqrt x = 0 then 0 else 1) * (Real.sqrt (max x 0 + QuantumProver.ElegantJointMeasurement.CP.polarEpsilon N))⁻¹)) := by
    calc
      _ = (K ∘L support K) ∘L matrixOperator (regularizedRootInverseMatrix K N) := by
        rw [comp_support]
        rfl
      _ = K ∘L (support K ∘L matrixOperator (regularizedRootInverseMatrix K N)) :=
        ContinuousLinearMap.comp_assoc _ _ _
      _ = _ := by
        rw [support, regularizedRootInverseMatrix, (gramMatrix_posSemidef K).isHermitian.cfc_eq]
        change K ∘L (matrixOperator (supportMatrix K) * matrixOperator _) = _
        rw [← map_mul]
        unfold supportMatrix
        rw [QuantumProver.ElegantJointMeasurement.CP.spectralReal_mul]
  have hlim : Tendsto (fun N => (gramMatrix_posSemidef K).isHermitian.cfc (fun x =>
      (if Real.sqrt x = 0 then 0 else 1) * (Real.sqrt (max x 0 + QuantumProver.ElegantJointMeasurement.CP.polarEpsilon N))⁻¹)) atTop
      (nhds (rootPseudoInverseMatrix K)) :=
    QuantumProver.ElegantJointMeasurement.CP.spectralReal_tendsto _ _ _ (fun i => scalar_polar_tendsto _
      ((gramMatrix_posSemidef K).eigenvalues_nonneg i))
  have hc : Continuous (fun M : Matrix I I ℂ => K ∘L matrixOperator M) :=
    continuous_const.clm_comp continuous_matrixOperator
  change Tendsto (fun N => regularizedPolar K N) atTop _
  simp_rw [heq]
  simpa only [Function.comp_def, polar, rootPseudoInverse] using
    (hc.tendsto (rootPseudoInverseMatrix K)).comp hlim

local instance sourceMapMeasurable : MeasurableSpace (Source I →L[ℂ] E) :=
  borel (Source I →L[ℂ] E)
local instance sourceMapBorel : BorelSpace (Source I →L[ℂ] E) := ⟨rfl⟩
local instance sourceEndomorphismMeasurable : MeasurableSpace (Source I →L[ℂ] Source I) :=
  borel (Source I →L[ℂ] Source I)
local instance sourceEndomorphismBorel : BorelSpace (Source I →L[ℂ] Source I) := ⟨rfl⟩

theorem measurable_positiveInput : Measurable (positiveInput (I := I) (E := E)) :=
  continuous_positiveInput.measurable

theorem measurable_support : Measurable (support (I := I) (E := E)) :=
  measurable_of_tendsto_metrizable (fun N => (continuous_regularizedSupport N).measurable)
    (tendsto_pi_nhds.mpr tendsto_regularizedSupport)

theorem measurable_complement : Measurable (complement (I := I) (E := E)) :=
  measurable_const.sub measurable_support

theorem measurable_polar : Measurable (polar (I := I) (E := E)) :=
  measurable_of_tendsto_metrizable (fun N => (continuous_regularizedPolar N).measurable)
    (tendsto_pi_nhds.mpr tendsto_regularizedPolar)

variable {P : Type*} [MeasurableSpace P]

theorem measurable_polar_of_measurable (K : P → Source I →L[ℂ] E) (hK : Measurable K) :
    Measurable (fun p => polar (K p)) := measurable_polar.comp hK

end QuantumProver.ElegantJointMeasurement.HilbertPolar
