import QuantumProver.InformationTheory.WernerEndpoint.TakagiContraction
import QuantumProver.InformationTheory.WernerEndpoint.RealSymmetricFactor

noncomputable section
namespace QuantumProver.WernerEndpoint.RealPositiveSchatten

open scoped BigOperators ComplexOrder
open Matrix Unitary SchattenSupport TakagiRankSix RealSymmetricFactor ExteriorSupport
  TakagiContraction

variable {X : Type*} [Fintype X] [DecidableEq X]

def realSpectralUnitary (S : Matrix X X ℝ) (hS : S.IsHermitian) : Matrix.unitaryGroup X ℂ :=
  ⟨complexify (realEigenMatrix S hS), by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      complexify_conjTranspose, ← complexify_transpose, ← complexify_mul,
      realEigenMatrix_transpose_mul, complexify_one]⟩

theorem real_positive_schatten_trace (S : Matrix X X ℝ) (hS : S.PosSemidef) :
    schattenOne (complexify S) = Matrix.trace S := by
  let U := realSpectralUnitary S hS.isHermitian
  have hc : complexify S = (U : Matrix X X ℂ) *
      Matrix.diagonal (fun i => Complex.ofReal (hS.isHermitian.eigenvalues i)) *
        (U : Matrix X X ℂ)ᵀ := by
    have h := congrArg complexify (real_spectral_expansion S hS.isHermitian)
    simpa only [U, realSpectralUnitary, complexify_mul, complexify_diagonal,
      complexify_transpose] using h
  rw [takagi_schattenOne _ U _ hS.eigenvalues_nonneg hc]
  simpa using hS.isHermitian.trace_eq_sum_eigenvalues.symm

theorem complexify_injective {Y Z : Type*} :
    Function.Injective (@complexify Y Z) := by
  intro A B h
  ext i j
  exact Complex.ofReal_injective (congrArg (fun M : Matrix Y Z ℂ => M i j) h)

def realExterior {Y Z : Type*} (A : Matrix Y Z ℝ) : Matrix (Y × Y) (Z × Z) ℝ :=
  fun ij ab => (A ij.1 ab.1 * A ij.2 ab.2 - A ij.1 ab.2 * A ij.2 ab.1) / 2

theorem complexify_realExterior {Y Z : Type*} (A : Matrix Y Z ℝ) :
    complexify (realExterior A) = orderedExterior (complexify A) := by
  ext ij ab
  simp [realExterior, orderedExterior, complexify]

theorem realExterior_mul {Y Z W : Type*} [Fintype Y] [Fintype Z] [Fintype W]
    (A : Matrix Y Z ℝ) (B : Matrix Z W ℝ) :
    realExterior (A * B) = realExterior A * realExterior B := by
  classical
  apply complexify_injective
  rw [complexify_realExterior, complexify_mul, complexify_mul,
    complexify_realExterior, complexify_realExterior, orderedExterior_mul]

theorem realExterior_transpose {Y Z : Type*} (A : Matrix Y Z ℝ) :
    realExterior Aᵀ = (realExterior A)ᵀ := by
  ext ab ij
  simp only [realExterior, Matrix.transpose_apply]
  ring

theorem realExterior_diagonal_posSemidef (s : X → ℝ) (hs : ∀ i, 0 ≤ s i) :
    (realExterior (Matrix.diagonal s)).PosSemidef := by
  let D : Matrix X X ℝ := Matrix.diagonal (fun i => Real.sqrt (s i))
  have hD : D * Dᵀ = Matrix.diagonal s := by
    simp only [D, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hs i)
  have hE : realExterior (Matrix.diagonal s) = realExterior D * (realExterior D)ᵀ := by
    rw [← hD, realExterior_mul, realExterior_transpose]
  rw [hE]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (realExterior D)

theorem realExterior_diagonal_trace (s : X → ℝ) :
    Matrix.trace (realExterior (Matrix.diagonal s)) =
      ((∑ i, s i) ^ 2 - ∑ i, s i ^ 2) / 2 := by
  have hd (i j : X) : realExterior (Matrix.diagonal s) (i, j) (i, j) =
      (if i = j then 0 else s i * s j) / 2 := by
    by_cases h : i = j
    · subst j
      simp [realExterior]
    · simp [realExterior, Matrix.diagonal_apply, h, Ne.symm h]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, hd]
  simp_rw [← Finset.sum_div]
  rw [offdiagonal_weight_sum]

theorem orderedExterior_diagonal_schatten (s : X → ℝ) (hs : ∀ i, 0 ≤ s i) :
    schattenOne (orderedExterior (Matrix.diagonal (fun i => Complex.ofReal (s i)))) =
      ((∑ i, s i) ^ 2 - ∑ i, s i ^ 2) / 2 := by
  rw [← complexify_diagonal, ← complexify_realExterior,
    real_positive_schatten_trace _ (realExterior_diagonal_posSemidef s hs),
    realExterior_diagonal_trace]

end QuantumProver.WernerEndpoint.RealPositiveSchatten
