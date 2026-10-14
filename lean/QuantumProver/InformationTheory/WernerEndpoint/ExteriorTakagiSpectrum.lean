import QuantumProver.InformationTheory.WernerEndpoint.SchattenUnitary
import QuantumProver.InformationTheory.WernerEndpoint.RealPositiveSchatten

noncomputable section
namespace QuantumProver.WernerEndpoint.ExteriorTakagiSpectrum

open scoped BigOperators Kronecker
open Matrix ExteriorSupport SchattenSupport SchattenUnitary RealPositiveSchatten

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

theorem orderedExterior_left_kronecker (A : Matrix Y X ℂ) (B : Matrix X Z ℂ) :
    orderedExterior (A * B) = (A ⊗ₖ A) * orderedExterior B := by
  ext ⟨i, j⟩ ⟨c, d⟩
  simp only [orderedExterior, Matrix.mul_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type]
  have hdiv (x y : ℂ) : x * (y / 2) = x * y / 2 := by ring
  simp_rw [hdiv, ← Finset.sum_div]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [sum_quad_factor, sum_quad_factor]

theorem orderedExterior_right_kronecker (A : Matrix Y X ℂ) (B : Matrix Z X ℂ) :
    orderedExterior (A * Bᵀ) = orderedExterior A * (B ⊗ₖ B)ᵀ := by
  calc
    orderedExterior (A * Bᵀ) = (orderedExterior (B * Aᵀ))ᵀ := by
      rw [← orderedExterior_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = _ := by
      rw [orderedExterior_left_kronecker, Matrix.transpose_mul,
        ← orderedExterior_transpose, Matrix.transpose_transpose]

theorem orderedExterior_kronecker_congruence (A : Matrix Y X ℂ) (B : Matrix X X ℂ) :
    orderedExterior (A * B * Aᵀ) =
      (A ⊗ₖ A) * orderedExterior B * (A ⊗ₖ A)ᵀ := by
  rw [orderedExterior_right_kronecker, orderedExterior_left_kronecker]

variable [DecidableEq X]

theorem takagi_exterior_schatten_sum (M : Matrix X X ℂ)
    (U : Matrix.unitaryGroup X ℂ) (s : X → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hM : M = (U : Matrix X X ℂ) * Matrix.diagonal (fun i => Complex.ofReal (s i)) *
      (U : Matrix X X ℂ)ᵀ) :
    schattenOne (orderedExterior M) =
      ((∑ i, s i) ^ 2 - ∑ i, s i ^ 2) / 2 := by
  rw [hM, orderedExterior_kronecker_congruence]
  change schattenOne ((kroneckerUnitary U : Matrix (X × X) (X × X) ℂ) *
      orderedExterior (Matrix.diagonal (fun i => Complex.ofReal (s i))) *
      (kroneckerUnitary U : Matrix (X × X) (X × X) ℂ)ᵀ) = _
  rw [schattenOne_unitary_congruence, orderedExterior_diagonal_schatten s hs]

end QuantumProver.WernerEndpoint.ExteriorTakagiSpectrum
