import QuantumProver.InformationTheory.VisibleCompression.Definitions

/-!
# Exact trace adjoint for finite complex matrix channels

Only complex linearity is used. Positivity and Hermitian preservation of
the physical decoder are downstream obligations. The ordinary trace pairing
fixes the matrix-unit index order without a transposition convention change.
-/

noncomputable section

namespace VisibleCompression

open scoped BigOperators

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

/-- The matrix representing the dual map for the bilinear trace pairing. -/
def traceAdjoint (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (P : Matrix O O ℂ) : Matrix I I ℂ :=
  fun i j => (P * Φ (Matrix.single j i 1)).trace

theorem linearMap_matrix_unit_expansion
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (T : Matrix I I ℂ) :
    Φ T = ∑ i, ∑ j, T i j • Φ (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single T]
  have hsingle (i j : I) :
      Matrix.single i j (T i j) = T i j • Matrix.single i j (1 : ℂ) := by
    simp
  simp_rw [map_sum, hsingle, map_smul]

/-- Exact trace pairing for every encoder matrix; no density restriction. -/
theorem traceAdjoint_pairing
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (P : Matrix O O ℂ)
    (T : Matrix I I ℂ) :
    (traceAdjoint Φ P * T).trace = (P * Φ T).trace := by
  calc
    (traceAdjoint Φ P * T).trace =
        ∑ i, ∑ j, T i j * (P * Φ (Matrix.single i j 1)).trace := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceAdjoint]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    _ = (P * Φ T).trace := by
      rw [linearMap_matrix_unit_expansion Φ T]
      simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
        Matrix.trace_smul, smul_eq_mul]

/-- The two-copy matrix-unit scalar contraction is the trace-adjoint purity. -/
theorem traceAdjoint_square
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (P : Matrix O O ℂ) :
    (traceAdjoint Φ P * traceAdjoint Φ P).trace =
      ∑ i, ∑ j,
        (P * Φ (Matrix.single i j 1)).trace *
        (P * Φ (Matrix.single j i 1)).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceAdjoint]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end VisibleCompression
