import Mathlib

/-!
# Finite block quadratic-form estimate for a positive matrix

This is the pinching/Cauchy-Schwarz ingredient for the output-dimension
Choi bound.  The estimate uses the seminorm induced by a PSD matrix and
therefore also permits singular matrices.
-/

noncomputable section

namespace VisibleCompression

open Matrix
open scoped BigOperators ComplexOrder

def matrixQuadratic {I : Type*} [Fintype I]
    (A : Matrix I I ℂ) (v : I → ℂ) : ℝ :=
  RCLike.re (star v ⬝ᵥ (A *ᵥ v))

/-- The diagonal output block, retaining the input/reference indices. -/
def outputBlock {I B : Type*} (A : Matrix (I × B) (I × B) ℂ) (b : B) :
    Matrix I I ℂ :=
  A.submatrix (fun i => (i, b)) (fun i => (i, b))

theorem outputBlock_posSemidef {I B : Type*} [Fintype I] [Fintype B]
    (A : Matrix (I × B) (I × B) ℂ) (hA : A.PosSemidef) (b : B) :
    (outputBlock A b).PosSemidef :=
  hA.submatrix (fun i => (i, b))

/-- Positive diagonal output blocks summing to the identity are individually
bounded by the identity. -/
theorem one_sub_outputBlock_posSemidef {I B : Type*}
    [Fintype I] [Fintype B] [DecidableEq I] [DecidableEq B]
    (A : Matrix (I × B) (I × B) ℂ) (hA : A.PosSemidef)
    (hmarginal : ∑ b, outputBlock A b = 1) (b : B) :
    (1 - outputBlock A b).PosSemidef := by
  have hrest := Matrix.posSemidef_sum (Finset.univ.erase b)
    (fun c _ => outputBlock_posSemidef A hA c)
  have hsum := Finset.sum_erase_add Finset.univ (outputBlock A) (Finset.mem_univ b)
  have heq : ∑ c ∈ Finset.univ.erase b, outputBlock A c = 1 - outputBlock A b :=
    eq_sub_of_add_eq (hsum.trans hmarginal)
  rwa [heq] at hrest

theorem matrixQuadratic_outputBlock_le_one {I B : Type*}
    [Fintype I] [Fintype B] [DecidableEq I] [DecidableEq B]
    (A : Matrix (I × B) (I × B) ℂ) (hA : A.PosSemidef)
    (hmarginal : ∑ b, outputBlock A b = 1) (b : B) (v : I → ℂ) :
    matrixQuadratic (outputBlock A b) v ≤ matrixQuadratic (1 : Matrix I I ℂ) v := by
  have hn := (one_sub_outputBlock_posSemidef A hA hmarginal b).re_dotProduct_nonneg v
  simp only [Matrix.sub_mulVec, dotProduct_sub, map_sub] at hn
  exact sub_nonneg.mp hn

/-- Restrict a vector to one output block, setting the other blocks to zero. -/
def outputSlice {I B : Type*} [DecidableEq B] (v : I × B → ℂ) (b : B) :
    I × B → ℂ :=
  fun ic => if ic.2 = b then v ic else 0

theorem sum_outputSlice {I B : Type*} [Fintype B] [DecidableEq B]
    (v : I × B → ℂ) : ∑ b, outputSlice v b = v := by
  ext ic
  simp [outputSlice, Finset.sum_apply]

theorem matrixQuadratic_outputSlice {I B : Type*}
    [Fintype I] [Fintype B] [DecidableEq B]
    (A : Matrix (I × B) (I × B) ℂ) (v : I × B → ℂ) (b : B) :
    matrixQuadratic A (outputSlice v b) =
      matrixQuadratic (outputBlock A b) (fun i => v (i, b)) := by
  simp only [matrixQuadratic, outputSlice, outputBlock, Matrix.submatrix_apply,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Pi.star_apply,
    apply_ite, star_zero, ite_mul, mul_ite, zero_mul, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem matrixQuadratic_one_eq_sum_blocks {I B : Type*}
    [Fintype I] [Fintype B] [DecidableEq I] [DecidableEq B]
    (v : I × B → ℂ) :
    matrixQuadratic (1 : Matrix (I × B) (I × B) ℂ) v =
      ∑ b, matrixQuadratic (1 : Matrix I I ℂ) (fun i => v (i, b)) := by
  simp only [matrixQuadratic, Matrix.one_mulVec, dotProduct,
    Fintype.sum_prod_type, map_sum, Pi.star_apply]
  rw [Finset.sum_comm]

theorem matrixQuadratic_sum_le_card_sum {I B : Type*}
    [Fintype I] [Fintype B] (A : Matrix I I ℂ) (hA : A.PosSemidef)
    (v : B → I → ℂ) :
    matrixQuadratic A (∑ b, v b) ≤
      (Fintype.card B : ℝ) * ∑ b, matrixQuadratic A (v b) := by
  classical
  letI : SeminormedAddCommGroup (I → ℂ) := A.toSeminormedAddCommGroup hA
  letI : Norm (I → ℂ) := (A.toSeminormedAddCommGroup hA).toNorm
  letI : InnerProductSpace ℂ (I → ℂ) := A.toInnerProductSpace hA
  have hnorm (x : I → ℂ) : ‖x‖ ^ 2 = matrixQuadratic A x := by
    have hi := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x
    change ‖x‖ ^ 2 = RCLike.re ((A *ᵥ x) ⬝ᵥ star x) at hi
    simpa only [matrixQuadratic, dotProduct_comm] using hi
  have htriangle := norm_sum_le Finset.univ v
  have hsum_nonneg : 0 ≤ ‖∑ b, v b‖ := by
    change 0 ≤ Real.sqrt _
    exact Real.sqrt_nonneg _
  have hsquare : ‖∑ b, v b‖ ^ 2 ≤ (∑ b, ‖v b‖) ^ 2 := by
    exact pow_le_pow_left₀ hsum_nonneg htriangle 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : B => (1 : ℝ)) (fun b => ‖v b‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hcs
  calc
    matrixQuadratic A (∑ b, v b) = ‖∑ b, v b‖ ^ 2 := (hnorm _).symm
    _ ≤ (∑ b, ‖v b‖) ^ 2 := hsquare
    _ ≤ (Fintype.card B : ℝ) * ∑ b, ‖v b‖ ^ 2 := hcs
    _ = (Fintype.card B : ℝ) * ∑ b, matrixQuadratic A (v b) := by
      simp_rw [hnorm]

/-- The genuine output-dimension quadratic-form estimate for every PSD
matrix with identity output marginal. -/
theorem matrixQuadratic_le_card_output {I B : Type*}
    [Fintype I] [Fintype B] [DecidableEq I] [DecidableEq B]
    (A : Matrix (I × B) (I × B) ℂ) (hA : A.PosSemidef)
    (hmarginal : ∑ b, outputBlock A b = 1) (v : I × B → ℂ) :
    matrixQuadratic A v ≤
      (Fintype.card B : ℝ) * matrixQuadratic (1 : Matrix (I × B) (I × B) ℂ) v := by
  have hsum := matrixQuadratic_sum_le_card_sum A hA (outputSlice v)
  rw [sum_outputSlice] at hsum
  calc
    matrixQuadratic A v ≤
        (Fintype.card B : ℝ) * ∑ b, matrixQuadratic A (outputSlice v b) := hsum
    _ ≤ (Fintype.card B : ℝ) *
        ∑ b, matrixQuadratic (1 : Matrix I I ℂ) (fun i => v (i, b)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro b _
      rw [matrixQuadratic_outputSlice]
      exact matrixQuadratic_outputBlock_le_one A hA hmarginal b _
    _ = (Fintype.card B : ℝ) *
        matrixQuadratic (1 : Matrix (I × B) (I × B) ℂ) v := by
      rw [matrixQuadratic_one_eq_sum_blocks]

theorem matrixQuadratic_one_eigenvectorBasis {I : Type*}
    [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (hA : A.IsHermitian) (i : I) :
    matrixQuadratic (1 : Matrix I I ℂ) ⇑(hA.eigenvectorBasis i) = 1 := by
  simp only [matrixQuadratic, Matrix.one_mulVec]
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
  norm_num [inner_self_eq_norm_sq_to_K, hA.eigenvectorBasis.orthonormal.1 i]

/-- Every eigenvalue is at most the output dimension. -/
theorem eigenvalues_le_card_output {I B : Type*}
    [Fintype I] [Fintype B] [DecidableEq I] [DecidableEq B]
    (A : Matrix (I × B) (I × B) ℂ) (hA : A.PosSemidef)
    (hmarginal : ∑ b, outputBlock A b = 1) (i : I × B) :
    hA.isHermitian.eigenvalues i ≤ (Fintype.card B : ℝ) := by
  have hbound := matrixQuadratic_le_card_output A hA hmarginal
    ⇑(hA.isHermitian.eigenvectorBasis i)
  rw [matrixQuadratic_one_eigenvectorBasis, mul_one] at hbound
  simpa only [matrixQuadratic, ← hA.isHermitian.eigenvalues_eq i] using hbound

/-- The output-dimensional eigenvalue estimate bounds the eigenvalue
square sum by output dimension times the actual matrix trace. -/
theorem sum_eigenvalues_sq_le_output_card_mul_trace {I B : Type*}
    [Fintype I] [Fintype B] [DecidableEq I] [DecidableEq B]
    (A : Matrix (I × B) (I × B) ℂ) (hA : A.PosSemidef)
    (hmarginal : ∑ b, outputBlock A b = 1) :
    (∑ i, hA.isHermitian.eigenvalues i ^ 2) ≤
      (Fintype.card B : ℝ) * A.trace.re := by
  have htrace : A.trace.re = ∑ i, hA.isHermitian.eigenvalues i := by
    change RCLike.re A.trace = ∑ i, hA.isHermitian.eigenvalues i
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    simp only [map_sum, RCLike.ofReal_re]
  calc
    (∑ i, hA.isHermitian.eigenvalues i ^ 2) ≤
        ∑ i, (Fintype.card B : ℝ) * hA.isHermitian.eigenvalues i := by
      apply Finset.sum_le_sum
      intro i _
      have hnonneg := hA.eigenvalues_nonneg i
      have hupper := eigenvalues_le_card_output A hA hmarginal i
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hupper hnonneg
    _ = (Fintype.card B : ℝ) * ∑ i, hA.isHermitian.eigenvalues i :=
      (Finset.mul_sum _ _ _).symm
    _ = (Fintype.card B : ℝ) * A.trace.re := by rw [htrace]

end VisibleCompression
