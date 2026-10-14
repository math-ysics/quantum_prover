import QuantumProver.InformationTheory.WernerEndpoint.MixedPurity
import QuantumProver.InformationTheory.WernerEndpoint.ExteriorSupport

noncomputable section

namespace QuantumProver.WernerEndpoint.SchattenSupport

open scoped BigOperators ComplexOrder
open Matrix

variable {Y X : Type*} [Fintype Y] [Fintype X] [DecidableEq X]

def gramHermitian (M : Matrix Y X ℂ) : (Mᴴ * M).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_self M

def singularValue (M : Matrix Y X ℂ) (i : X) : ℝ :=
  Real.sqrt ((gramHermitian M).eigenvalues i)

def schattenOne (M : Matrix Y X ℂ) : ℝ := ∑ i, singularValue M i

def spectralSupport (M : Matrix Y X ℂ) : Finset X :=
  Finset.univ.filter (fun i => (gramHermitian M).eigenvalues i ≠ 0)

theorem singularValue_nonneg (M : Matrix Y X ℂ) (i : X) : 0 ≤ singularValue M i :=
  Real.sqrt_nonneg _

theorem singularValue_sq (M : Matrix Y X ℂ) (i : X) :
    singularValue M i ^ 2 = (gramHermitian M).eigenvalues i :=
  Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg M i)

theorem schattenOne_nonneg (M : Matrix Y X ℂ) : 0 ≤ schattenOne M := by
  unfold schattenOne
  exact Finset.sum_nonneg (fun i _ => singularValue_nonneg M i)

theorem singularValue_sq_sum (M : Matrix Y X ℂ) :
    (∑ i, singularValue M i ^ 2) = hsNormSq M := by
  simp_rw [singularValue_sq]
  have h := congrArg Complex.re (gramHermitian M).trace_eq_sum_eigenvalues
  rw [Matrix.trace_mul_comm Mᴴ M, ← hsNormSq_eq_trace M] at h
  simpa [Complex.re_sum] using h.symm

theorem spectralSupport_card (M : Matrix Y X ℂ) :
    (spectralSupport M).card = M.rank := by
  rw [← Matrix.rank_conjTranspose_mul_self M, (gramHermitian M).rank_eq_card_non_zero_eigs]
  simp [spectralSupport, Fintype.card_subtype]

theorem schattenOne_eq_support_sum (M : Matrix Y X ℂ) :
    schattenOne M = ∑ i ∈ spectralSupport M, singularValue M i := by
  unfold schattenOne
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  have hzero : (gramHermitian M).eigenvalues i = 0 := by
    simpa [spectralSupport] using hi
  simp [singularValue, hzero]

theorem singularValue_sq_support_sum (M : Matrix Y X ℂ) :
    (∑ i ∈ spectralSupport M, singularValue M i ^ 2) = hsNormSq M := by
  rw [← singularValue_sq_sum M]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  have hzero : (gramHermitian M).eigenvalues i = 0 := by
    simpa [spectralSupport] using hi
  simp [singularValue, hzero]

theorem schattenOne_sq_le_rank_hsNormSq (M : Matrix Y X ℂ) :
    schattenOne M ^ 2 ≤ (M.rank : ℝ) * hsNormSq M := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (spectralSupport M)
    (fun _ : X => (1 : ℝ)) (singularValue M)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [← schattenOne_eq_support_sum M, singularValue_sq_support_sum M,
    spectralSupport_card M] at h
  exact h

def inputEigenvector (M : Matrix Y X ℂ) (i : X) : EuclideanSpace ℂ X :=
  (gramHermitian M).eigenvectorBasis i

def singularImage (M : Matrix Y X ℂ) (i : X) : EuclideanSpace ℂ Y :=
  WithLp.toLp 2 (M.mulVec (fun x => inputEigenvector M i x))

theorem inner_mulVec_gram (M : Matrix Y X ℂ) (u v : X → ℂ) :
    inner ℂ (WithLp.toLp 2 (M.mulVec u)) (WithLp.toLp 2 (M.mulVec v)) =
      inner ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 ((Mᴴ * M).mulVec v)) := by
  simp only [EuclideanSpace.inner_toLp_toLp]
  rw [dotProduct_comm (M.mulVec v), Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, dotProduct_comm]

theorem singularImage_inner (M : Matrix Y X ℂ) (i j : X) :
    inner ℂ (singularImage M i) (singularImage M j) =
      ((gramHermitian M).eigenvalues j : ℂ) * (if i = j then 1 else 0) := by
  unfold singularImage inputEigenvector
  rw [inner_mulVec_gram, (gramHermitian M).mulVec_eigenvectorBasis]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), WithLp.toLp_smul,
    WithLp.toLp_ofLp, inner_smul_right]
  rw [orthonormal_iff_ite.mp (gramHermitian M).eigenvectorBasis.orthonormal]
  rfl

abbrev Active (M : Matrix Y X ℂ) := {i : X // (gramHermitian M).eigenvalues i ≠ 0}

def leftSingularVector (M : Matrix Y X ℂ) (i : Active M) : EuclideanSpace ℂ Y :=
  (singularValue M i.val)⁻¹ • singularImage M i.val

theorem active_singularValue_ne_zero (M : Matrix Y X ℂ) (i : Active M) :
    singularValue M i.val ≠ 0 := by
  intro hz
  have h := singularValue_sq M i.val
  rw [hz] at h
  exact i.property (by simpa using h.symm)

theorem leftSingularVector_orthonormal (M : Matrix Y X ℂ) :
    Orthonormal ℂ (leftSingularVector M) := by
  rw [orthonormal_iff_ite]
  intro i j
  unfold leftSingularVector
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, inner_smul_right,
    singularImage_inner, Complex.star_def, Complex.conj_ofReal]
  by_cases hij : i = j
  · subst j
    have hs := active_singularValue_ne_zero M i
    rw [if_pos rfl, if_pos rfl, ← singularValue_sq M i.val]
    push_cast
    simp only [map_inv₀, RCLike.conj_ofReal]
    have hsc : (singularValue M i.val : ℂ) ≠ 0 := by exact_mod_cast hs
    field_simp [hsc]
    rfl
  · have hv : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    simp [hij, hv]

theorem singularImage_eq_smul_left (M : Matrix Y X ℂ) (i : Active M) :
    singularImage M i.val = singularValue M i.val • leftSingularVector M i := by
  unfold leftSingularVector
  rw [smul_smul, mul_inv_cancel₀ (active_singularValue_ne_zero M i), one_smul]

theorem leftSingularVector_image_inner (M : Matrix Y X ℂ) (i : Active M) :
    inner ℂ (leftSingularVector M i) (singularImage M i.val) = (singularValue M i.val : ℂ) := by
  rw [singularImage_eq_smul_left, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
  rw [orthonormal_iff_ite.mp (leftSingularVector_orthonormal M) i i]
  simp

variable {J : Type*} [Fintype J]

def columnVector (U : Matrix Y J ℂ) (j : J) : EuclideanSpace ℂ Y :=
  WithLp.toLp 2 (fun y => U y j)

theorem orthonormal_column_hs_sum {K : Type*} [Fintype K]
    (U : Matrix Y J ℂ) (φ : K → EuclideanSpace ℂ Y) (hφ : Orthonormal ℂ φ) :
    (∑ i, ∑ j, ‖inner ℂ (φ i) (columnVector U j)‖ ^ 2) ≤ hsNormSq U := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j, ‖columnVector U j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact hφ.sum_inner_products_le (columnVector U j)
    _ = _ := by
      simp only [columnVector, EuclideanSpace.norm_sq_eq, WithLp.ofLp_toLp, hsNormSq]
      exact Finset.sum_comm

theorem active_input_orthonormal (M : Matrix Y X ℂ) :
    Orthonormal ℂ (fun i : Active M => inputEigenvector M i.val) := by
  exact (gramHermitian M).eigenvectorBasis.orthonormal.comp
    (fun i : Active M => i.val) Subtype.val_injective

theorem schattenOne_eq_active_sum (M : Matrix Y X ℂ) :
    schattenOne M = ∑ i : Active M, singularValue M i.val := by
  rw [schattenOne_eq_support_sum]
  symm
  simpa [spectralSupport, Active] using
    (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
      (p := fun i : X => (gramHermitian M).eigenvalues i ≠ 0) (singularValue M))

def entryConj (V : Matrix X J ℂ) : Matrix X J ℂ := fun x j => star (V x j)

theorem entryConj_hsNormSq (V : Matrix X J ℂ) : hsNormSq (entryConj V) = hsNormSq V := by
  simp [hsNormSq, entryConj, norm_star]

theorem factor_inner_sum (U : Matrix Y J ℂ) (V : Matrix X J ℂ)
    (φ : EuclideanSpace ℂ Y) (ψ : EuclideanSpace ℂ X) :
    inner ℂ φ (WithLp.toLp 2 ((U * Vᵀ).mulVec (fun x => ψ x))) =
      ∑ j, inner ℂ φ (columnVector U j) * inner ℂ (columnVector (entryConj V) j) ψ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp]
  rw [← Matrix.mulVec_mulVec]
  rw [dotProduct_comm (U.mulVec _), Matrix.dotProduct_mulVec]
  simp [dotProduct, Matrix.vecMul, Matrix.mulVec, Matrix.transpose_apply,
    columnVector, entryConj, EuclideanSpace.inner_eq_star_dotProduct,
    mul_comm, mul_left_comm, mul_assoc]

theorem schattenOne_mul_transpose_sq (U : Matrix Y J ℂ) (V : Matrix X J ℂ) :
    schattenOne (U * Vᵀ) ^ 2 ≤ hsNormSq U * hsNormSq V := by
  let M : Matrix Y X ℂ := U * Vᵀ
  let a : Active M → J → ℝ := fun i j => ‖inner ℂ (leftSingularVector M i) (columnVector U j)‖
  let b : Active M → J → ℝ := fun i j =>
    ‖inner ℂ (columnVector (entryConj V) j) (inputEigenvector M i.val)‖
  have hsum : schattenOne M ≤ ∑ i, ∑ j, a i j * b i j := by
    rw [schattenOne_eq_active_sum]
    apply Finset.sum_le_sum
    intro i _
    have hsi : singularValue M i.val =
        ‖inner ℂ (leftSingularVector M i) (singularImage M i.val)‖ := by
      rw [leftSingularVector_image_inner]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (singularValue_nonneg M i.val)]
    rw [hsi]
    change ‖inner ℂ (leftSingularVector M i)
      (WithLp.toLp 2 ((U * Vᵀ).mulVec (fun x => inputEigenvector M i.val x)))‖ ≤ _
    rw [factor_inner_sum]
    simpa only [norm_mul] using norm_sum_le Finset.univ
      (fun j => inner ℂ (leftSingularVector M i) (columnVector U j) *
        inner ℂ (columnVector (entryConj V) j) (inputEigenvector M i.val))
  have ha : (∑ i, ∑ j, a i j ^ 2) ≤ hsNormSq U :=
    orthonormal_column_hs_sum U (leftSingularVector M) (leftSingularVector_orthonormal M)
  have hb : (∑ i, ∑ j, b i j ^ 2) ≤ hsNormSq V := by
    have h := orthonormal_column_hs_sum (entryConj V)
      (fun i : Active M => inputEigenvector M i.val) (active_input_orthonormal M)
    rw [entryConj_hsNormSq] at h
    simpa only [b, norm_inner_symm] using h
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Active M × J))
    (fun ij => a ij.1 ij.2) (fun ij => b ij.1 ij.2)
  simp only [Fintype.sum_prod_type] at hcs
  have hp := mul_le_mul ha hb (by positivity) (hsNormSq_nonneg U)
  have hnonneg : 0 ≤ ∑ i, ∑ j, a i j * b i j := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hdiff := mul_nonneg (sub_nonneg.mpr hsum)
    (add_nonneg hnonneg (schattenOne_nonneg M))
  change schattenOne M ^ 2 ≤ _
  nlinarith

theorem schattenOne_mul_transpose (U : Matrix Y J ℂ) (V : Matrix X J ℂ) :
    schattenOne (U * Vᵀ) ≤ Real.sqrt (hsNormSq U) * Real.sqrt (hsNormSq V) := by
  have h := schattenOne_mul_transpose_sq U V
  have hp : (Real.sqrt (hsNormSq U) * Real.sqrt (hsNormSq V)) ^ 2 =
      hsNormSq U * hsNormSq V := by
    rw [mul_pow, Real.sq_sqrt (hsNormSq_nonneg U), Real.sq_sqrt (hsNormSq_nonneg V)]
  have hnonneg : 0 ≤ Real.sqrt (hsNormSq U) * Real.sqrt (hsNormSq V) := by positivity
  nlinarith [schattenOne_nonneg (U * Vᵀ)]

theorem schattenOne_covariance [DecidableEq Y] (U : Matrix Y X ℂ) :
    schattenOne (U * Uᵀ) ≤ hsNormSq U := by
  classical
  have h := schattenOne_mul_transpose U U
  rw [← pow_two, Real.sq_sqrt (hsNormSq_nonneg U)] at h
  exact h

end QuantumProver.WernerEndpoint.SchattenSupport
