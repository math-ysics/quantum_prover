import QuantumProver.InformationTheory.WernerEndpoint.SchattenSupport

noncomputable section

namespace QuantumProver.WernerEndpoint.TakagiAntilinear

open scoped BigOperators
open Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

local instance realInner : InnerProductSpace ℝ (EuclideanSpace ℂ X) :=
  InnerProductSpace.complexToReal

def antiLinear (M : Matrix X X ℂ) :
    EuclideanSpace ℂ X →ₗ[ℝ] EuclideanSpace ℂ X where
  toFun v := WithLp.toLp 2 (M.mulVec (fun j => star (v j)))
  map_add' u v := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib, mul_add]
  map_smul' r v := by
    ext i
    simp [Matrix.mulVec, dotProduct, RCLike.real_smul_eq_coe_smul,
      Finset.mul_sum, mul_left_comm, mul_assoc]

theorem antiLinear_apply (M : Matrix X X ℂ) (v : EuclideanSpace ℂ X) :
    antiLinear M v = WithLp.toLp 2 (M.mulVec (fun j => star (v j))) := rfl

theorem antiLinear_complex_smul (M : Matrix X X ℂ) (c : ℂ) (v : EuclideanSpace ℂ X) :
    antiLinear M (c • v) = star c • antiLinear M v := by
  ext i
  simp [antiLinear, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm, mul_assoc]

theorem antiLinear_inner_flip (M : Matrix X X ℂ) (hM : Mᵀ = M)
    (u v : EuclideanSpace ℂ X) :
    inner ℂ (antiLinear M u) v = inner ℂ (antiLinear M v) u := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i, v i * star (M.mulVec (fun j => star (u j)) i)) =
    ∑ i, u i * star (M.mulVec (fun j => star (v j)) i)
  simp only [Matrix.mulVec, dotProduct, star_sum, star_mul, star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij : M j i = M i j := congrArg (fun A : Matrix X X ℂ => A i j) hM
  rw [hij]
  ring

theorem antiLinear_symmetric (M : Matrix X X ℂ) (hM : Mᵀ = M) :
    (antiLinear M).IsSymmetric := by
  intro u v
  change (inner ℂ (antiLinear M u) v).re = (inner ℂ u (antiLinear M v)).re
  rw [antiLinear_inner_flip M hM]
  exact inner_re_symm (𝕜 := ℂ) (antiLinear M v) u

theorem antiLinear_square (M : Matrix X X ℂ) (hM : Mᵀ = M)
    (v : EuclideanSpace ℂ X) :
    antiLinear M (antiLinear M v) = WithLp.toLp 2 ((M * Mᴴ).mulVec (fun j => v j)) := by
  have hstar : (fun j => star (antiLinear M v j)) = Mᴴ.mulVec (fun j => v j) := by
    funext i
    simp only [antiLinear, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mulVec, dotProduct, star_sum, star_mul, star_star, Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hij : M i j = M j i := (congrArg (fun A : Matrix X X ℂ => A i j) hM).symm
    rw [hij]
    ring
  rw [antiLinear_apply, hstar, Matrix.mulVec_mulVec]

def realSpectralBasis (M : Matrix X X ℂ) (hM : Mᵀ = M) :
    OrthonormalBasis (Fin (Module.finrank ℝ (EuclideanSpace ℂ X))) ℝ (EuclideanSpace ℂ X) :=
  (antiLinear_symmetric M hM).eigenvectorBasis rfl

def realSpectralValue (M : Matrix X X ℂ) (hM : Mᵀ = M)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℂ X))) : ℝ :=
  (antiLinear_symmetric M hM).eigenvalues rfl i

theorem realSpectral_eigenvector (M : Matrix X X ℂ) (hM : Mᵀ = M)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℂ X))) :
    antiLinear M (realSpectralBasis M hM i) =
      realSpectralValue M hM i • realSpectralBasis M hM i :=
  (antiLinear_symmetric M hM).apply_eigenvectorBasis rfl i

abbrev PositiveIndex (M : Matrix X X ℂ) (hM : Mᵀ = M) :=
  {i : Fin (Module.finrank ℝ (EuclideanSpace ℂ X)) // 0 < realSpectralValue M hM i}

def positiveVector (M : Matrix X X ℂ) (hM : Mᵀ = M) (i : PositiveIndex M hM) :
    EuclideanSpace ℂ X := realSpectralBasis M hM i.val

theorem positiveVector_orthonormal (M : Matrix X X ℂ) (hM : Mᵀ = M) :
    Orthonormal ℂ (positiveVector M hM) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hre : (inner ℂ (positiveVector M hM i) (positiveVector M hM j)).re =
      if i = j then (1 : ℝ) else 0 := by
    have h := orthonormal_iff_ite.mp (realSpectralBasis M hM).orthonormal i.val j.val
    change (inner ℂ (positiveVector M hM i) (positiveVector M hM j)).re = _ at h
    simpa only [Subtype.val_inj] using h
  have hf := antiLinear_inner_flip M hM (positiveVector M hM i) (positiveVector M hM j)
  simp only [positiveVector, realSpectral_eigenvector] at hf
  change inner ℂ ((realSpectralValue M hM i.val : ℂ) • realSpectralBasis M hM i.val)
      (realSpectralBasis M hM j.val) =
    inner ℂ ((realSpectralValue M hM j.val : ℂ) • realSpectralBasis M hM j.val)
      (realSpectralBasis M hM i.val) at hf
  simp only [inner_smul_left, Complex.conj_ofReal] at hf
  have him := congrArg Complex.im hf
  have hc : inner ℂ (realSpectralBasis M hM j.val) (realSpectralBasis M hM i.val) =
      star (inner ℂ (realSpectralBasis M hM i.val) (realSpectralBasis M hM j.val)) :=
    (inner_conj_symm (𝕜 := ℂ) (realSpectralBasis M hM j.val)
      (realSpectralBasis M hM i.val)).symm
  rw [hc] at him
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, Complex.star_def, Complex.conj_im] at him
  have hz : (inner ℂ (positiveVector M hM i) (positiveVector M hM j)).im = 0 := by
    change (inner ℂ (realSpectralBasis M hM i.val) (realSpectralBasis M hM j.val)).im = 0
    have hp : (realSpectralValue M hM i.val + realSpectralValue M hM j.val) *
        (inner ℂ (realSpectralBasis M hM i.val) (realSpectralBasis M hM j.val)).im = 0 := by
      nlinarith [him]
    exact (mul_eq_zero.mp hp).resolve_left (ne_of_gt (add_pos i.property j.property))
  apply Complex.ext
  · by_cases hij : i = j <;> simpa [hij] using hre
  · by_cases hij : i = j <;> simpa [hij] using hz

theorem positiveVector_leftGram_eigenvector (M : Matrix X X ℂ) (hM : Mᵀ = M)
    (i : PositiveIndex M hM) :
    WithLp.toLp 2 ((M * Mᴴ).mulVec (fun x => positiveVector M hM i x)) =
      (realSpectralValue M hM i.val ^ 2) • positiveVector M hM i := by
  rw [← antiLinear_square M hM, positiveVector, realSpectral_eigenvector,
    map_smul, realSpectral_eigenvector, smul_smul]
  simp only [pow_two]

end QuantumProver.WernerEndpoint.TakagiAntilinear
