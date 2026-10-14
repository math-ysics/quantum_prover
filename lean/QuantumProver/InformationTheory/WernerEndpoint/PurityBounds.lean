import QuantumProver.InformationTheory.WernerEndpoint.AntisymmetricStates

noncomputable section

namespace QuantumProver.WernerEndpoint

open scoped BigOperators
open Matrix

variable {B E I : Type*} [Fintype B] [Fintype E] [Fintype I]

def hsNormSq (A : Matrix B E ℂ) : ℝ := ∑ b, ∑ e, ‖A b e‖ ^ 2

theorem hsNormSq_nonneg (A : Matrix B E ℂ) : 0 ≤ hsNormSq A := by
  unfold hsNormSq
  positivity

theorem crossLeft_eq_mul (U W : Matrix B E ℂ) : crossLeft U W = U * Wᴴ := by
  ext b c
  simp [crossLeft, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem crossRight_eq_mul_transpose (U W : Matrix B E ℂ) :
    crossRight U W = (Wᴴ * U)ᵀ := by
  ext e f
  simp [crossRight, Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]

theorem cross_square_trace_eq (U W : Matrix B E ℂ) :
    Matrix.trace (crossLeft U W * crossLeft U W) =
      Matrix.trace (crossRight U W * crossRight U W) := by
  rw [crossLeft_eq_mul, crossRight_eq_mul_transpose, ← Matrix.transpose_mul,
    Matrix.trace_transpose]
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_cycle (U * Wᴴ) U Wᴴ)

theorem hsNormSq_eq_trace (A : Matrix B E ℂ) :
    hsNormSq A = (Matrix.trace (A * Aᴴ)).re := by
  simp [hsNormSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.mul_conj, Complex.sq_norm]

theorem norm_trace_square_le_hsNormSq (Z : Matrix I I ℂ) :
    ‖Matrix.trace (Z * Z)‖ ≤ hsNormSq Z := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  calc
    ‖∑ i, ∑ j, Z i j * Z j i‖ ≤ ∑ i, ‖∑ j, Z i j * Z j i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖Z i j‖ * ‖Z j i‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_mul] using (norm_sum_le Finset.univ (fun j => Z i j * Z j i))
    _ ≤ ∑ i, ∑ j, (‖Z i j‖ ^ 2 + ‖Z j i‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      nlinarith [sq_nonneg (‖Z i j‖ - ‖Z j i‖)]
    _ = hsNormSq Z := by
      simp_rw [← Finset.sum_div, Finset.sum_add_distrib]
      have hswap : (∑ i : I, ∑ j : I, ‖Z j i‖ ^ 2) =
          ∑ i : I, ∑ j : I, ‖Z i j‖ ^ 2 := Finset.sum_comm
      rw [hswap]
      unfold hsNormSq
      ring

theorem crossLeft_hsNormSq (U W : Matrix B E ℂ) :
    hsNormSq (crossLeft U W) =
      (Matrix.trace (reducedRight U * reducedRight W)).re := by
  rw [hsNormSq_eq_trace, crossLeft_eq_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  unfold reducedRight
  rw [crossRight_eq_mul_transpose, crossRight_eq_mul_transpose,
    ← Matrix.transpose_mul, Matrix.trace_transpose]
  congr 1
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm U ((Wᴴ * W) * Uᴴ))

theorem crossRight_hsNormSq (U W : Matrix B E ℂ) :
    hsNormSq (crossRight U W) =
      (Matrix.trace (reducedLeft U * reducedLeft W)).re := by
  rw [hsNormSq_eq_trace, crossRight_eq_mul_transpose]
  simp only [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  rw [← Matrix.transpose_mul, Matrix.trace_transpose]
  unfold reducedLeft
  rw [crossLeft_eq_mul, crossLeft_eq_mul]
  congr 1
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_cycle Uᴴ (W * Wᴴ) U)

theorem transition_norm_le_complement_overlap (U W : Matrix B E ℂ) :
    ‖Matrix.trace (crossLeft U W * crossLeft U W)‖ ≤
      (Matrix.trace (reducedRight U * reducedRight W)).re := by
  rw [← crossLeft_hsNormSq]
  exact norm_trace_square_le_hsNormSq _

theorem transition_norm_le_output_overlap (U W : Matrix B E ℂ) :
    ‖Matrix.trace (crossLeft U W * crossLeft U W)‖ ≤
      (Matrix.trace (reducedLeft U * reducedLeft W)).re := by
  rw [cross_square_trace_eq, ← crossRight_hsNormSq]
  exact norm_trace_square_le_hsNormSq _

theorem crossLeft_conjTranspose (U W : Matrix B E ℂ) :
    (crossLeft U W)ᴴ = crossLeft W U := by
  rw [crossLeft_eq_mul, crossLeft_eq_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

theorem reducedLeft_conjTranspose (U : Matrix B E ℂ) :
    (reducedLeft U)ᴴ = reducedLeft U := crossLeft_conjTranspose U U

theorem purity_eq_hsNormSq_of_hermitian (R : Matrix I I ℂ) (hR : Rᴴ = R) :
    purity R = hsNormSq R := by
  rw [hsNormSq_eq_trace, hR]
  rfl

theorem purity_nonneg_of_hermitian (R : Matrix I I ℂ) (hR : Rᴴ = R) :
    0 ≤ purity R := by
  rw [purity_eq_hsNormSq_of_hermitian R hR]
  exact hsNormSq_nonneg R

theorem purity_add (R S : Matrix I I ℂ) :
    purity (R + S) = purity R + purity S + 2 * (Matrix.trace (R * S)).re := by
  classical
  simp only [purity, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  rw [Matrix.trace_mul_comm S R]
  ring

theorem purity_sub (R S : Matrix I I ℂ) :
    purity (R - S) = purity R + purity S - 2 * (Matrix.trace (R * S)).re := by
  classical
  simp only [purity, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [Matrix.trace_mul_comm S R]
  ring

theorem twice_overlap_le_purities (U W : Matrix B E ℂ) :
    2 * (Matrix.trace (reducedLeft U * reducedLeft W)).re ≤
      purity (reducedLeft U) + purity (reducedLeft W) := by
  have hherm : (reducedLeft U - reducedLeft W)ᴴ = reducedLeft U - reducedLeft W := by
    rw [Matrix.conjTranspose_sub, reducedLeft_conjTranspose, reducedLeft_conjTranspose]
  have h := purity_nonneg_of_hermitian _ hherm
  rw [purity_sub] at h
  linarith

end QuantumProver.WernerEndpoint
