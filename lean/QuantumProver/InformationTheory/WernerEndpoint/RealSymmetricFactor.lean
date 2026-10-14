import QuantumProver.InformationTheory.WernerEndpoint.ExteriorSupport

noncomputable section

namespace QuantumProver.WernerEndpoint.RealSymmetricFactor

open scoped BigOperators
open Matrix Unitary

def spectralPhase (x : ℝ) : ℂ :=
  if 0 ≤ x then Complex.ofReal (Real.sqrt x) else Complex.I * Complex.ofReal (Real.sqrt (-x))

theorem spectralPhase_sq (x : ℝ) : spectralPhase x ^ 2 = Complex.ofReal x := by
  by_cases hx : 0 ≤ x
  · rw [spectralPhase, if_pos hx]
    have h := Real.sq_sqrt hx
    exact_mod_cast h
  · rw [spectralPhase, if_neg hx, mul_pow, Complex.I_sq]
    have h : Complex.ofReal (Real.sqrt (-x)) ^ 2 = Complex.ofReal (-x) := by
      exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ -x)
    rw [h]
    simp

theorem spectralPhase_normSq (x : ℝ) : Complex.normSq (spectralPhase x) = |x| := by
  by_cases hx : 0 ≤ x
  · rw [spectralPhase, if_pos hx, abs_of_nonneg hx]
    simpa [Complex.normSq_ofReal, pow_two] using Real.sq_sqrt hx
  · rw [spectralPhase, if_neg hx, Complex.normSq_mul]
    have hI : Complex.normSq Complex.I = 1 := by norm_num [Complex.normSq_apply]
    rw [hI, one_mul, abs_of_neg (by linarith : x < 0)]
    simpa [Complex.normSq_ofReal, pow_two] using Real.sq_sqrt (by linarith : 0 ≤ -x)

def complexify {Y X : Type*} (S : Matrix Y X ℝ) : Matrix Y X ℂ :=
  fun i j => Complex.ofReal (S i j)

theorem complexify_mul {Y X Z : Type*} [Fintype X]
    (S : Matrix Y X ℝ) (T : Matrix X Z ℝ) :
    complexify (S * T) = complexify S * complexify T := by
  ext i j
  simp [complexify, Matrix.mul_apply]

theorem complexify_transpose {Y X : Type*} (S : Matrix Y X ℝ) :
    complexify Sᵀ = (complexify S)ᵀ := rfl

theorem complexify_conjTranspose {Y X : Type*} (S : Matrix Y X ℝ) :
    (complexify S)ᴴ = (complexify S)ᵀ := by
  ext i j
  simp [complexify, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    RCLike.star_def, RCLike.conj_ofReal]

theorem complexify_diagonal {X : Type*} [DecidableEq X] (d : X → ℝ) :
    complexify (Matrix.diagonal d) = Matrix.diagonal (fun i => Complex.ofReal (d i)) := by
  ext i j
  by_cases hij : i = j <;> simp [complexify, Matrix.diagonal_apply, hij]

variable {X : Type*} [Fintype X] [DecidableEq X]

def realEigenMatrix (S : Matrix X X ℝ) (hS : S.IsHermitian) : Matrix X X ℝ :=
  hS.eigenvectorUnitary

theorem real_spectral_expansion (S : Matrix X X ℝ) (hS : S.IsHermitian) :
    S = realEigenMatrix S hS * Matrix.diagonal hS.eigenvalues * (realEigenMatrix S hS)ᵀ := by
  simpa [realEigenMatrix, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using hS.spectral_theorem

def covarianceFactor (S : Matrix X X ℝ) (hS : S.IsHermitian) : Matrix X X ℂ :=
  complexify (realEigenMatrix S hS) * Matrix.diagonal (fun i => spectralPhase (hS.eigenvalues i))

theorem covarianceFactor_covariance (S : Matrix X X ℝ) (hS : S.IsHermitian) :
    covarianceFactor S hS * (covarianceFactor S hS)ᵀ = complexify S := by
  let Q := complexify (realEigenMatrix S hS)
  let D : Matrix X X ℂ := Matrix.diagonal (fun i => spectralPhase (hS.eigenvalues i))
  have hd : D * D = complexify (Matrix.diagonal hS.eigenvalues) := by
    rw [complexify_diagonal]
    simp only [D, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simpa only [pow_two] using spectralPhase_sq (hS.eigenvalues i)
  calc
    _ = Q * (D * D) * Qᵀ := by
      simp only [covarianceFactor, Q, D, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    _ = complexify (realEigenMatrix S hS * Matrix.diagonal hS.eigenvalues *
        (realEigenMatrix S hS)ᵀ) := by
      rw [hd, complexify_mul, complexify_mul, complexify_transpose]
    _ = _ := congrArg complexify (real_spectral_expansion S hS).symm

theorem covarianceFactor_gram (S : Matrix X X ℝ) (hS : S.IsHermitian) :
    covarianceFactor S hS * (covarianceFactor S hS)ᴴ =
      complexify (realEigenMatrix S hS) *
        Matrix.diagonal (fun i => Complex.ofReal (|hS.eigenvalues i|)) *
          (complexify (realEigenMatrix S hS))ᵀ := by
  let Q := complexify (realEigenMatrix S hS)
  let D : Matrix X X ℂ := Matrix.diagonal (fun i => spectralPhase (hS.eigenvalues i))
  have hd : D * Dᴴ = Matrix.diagonal (fun i => Complex.ofReal (|hS.eigenvalues i|)) := by
    simp only [D, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have h := Complex.mul_conj (spectralPhase (hS.eigenvalues i))
    rw [spectralPhase_normSq] at h
    simpa only [Pi.star_apply, Complex.star_def] using h
  calc
    _ = Q * (D * Dᴴ) * Qᴴ := by
      simp only [covarianceFactor, Q, D, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hd, complexify_conjTranspose]

theorem complexify_one : complexify (1 : Matrix X X ℝ) = (1 : Matrix X X ℂ) := by
  ext i j
  by_cases hij : i = j <;> simp [complexify, Matrix.one_apply, hij]

theorem realEigenMatrix_transpose_mul (S : Matrix X X ℝ) (hS : S.IsHermitian) :
    (realEigenMatrix S hS)ᵀ * realEigenMatrix S hS = 1 := by
  simpa [realEigenMatrix, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    Unitary.coe_star_mul_self hS.eigenvectorUnitary

theorem eigenvalue_cube (S : Matrix X X ℝ) (hS : S.IsHermitian) (hcube : S ^ 3 = S) (i : X) :
    hS.eigenvalues i ^ 3 = hS.eigenvalues i := by
  have h := congrArg (Unitary.conjStarAlgAut ℝ (Matrix X X ℝ) (star hS.eigenvectorUnitary)) hcube
  simp only [map_pow, hS.conjStarAlgAut_star_eigenvectorUnitary] at h
  have hi := congrArg (fun M : Matrix X X ℝ => M i i) h
  simpa [Matrix.diagonal_pow] using hi

theorem abs_eigenvalue_eq_sq (S : Matrix X X ℝ) (hS : S.IsHermitian)
    (hcube : S ^ 3 = S) (i : X) : |hS.eigenvalues i| = hS.eigenvalues i ^ 2 := by
  let x := hS.eigenvalues i
  have hc : x ^ 3 = x := eigenvalue_cube S hS hcube i
  have hf : (x + 1) * x * (x - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with hz | hz
  · rcases mul_eq_zero.mp hz with hz | hz
    · have hx : x = -1 := by linarith
      change |x| = x ^ 2
      rw [hx]
      norm_num
    · change |x| = x ^ 2
      rw [hz]
      norm_num
  · have hx : x = 1 := by linarith
    change |x| = x ^ 2
    rw [hx]
    norm_num

theorem real_square_expansion (S : Matrix X X ℝ) (hS : S.IsHermitian) :
    S * S = realEigenMatrix S hS * Matrix.diagonal (fun i => hS.eigenvalues i ^ 2) *
      (realEigenMatrix S hS)ᵀ := by
  let Q := realEigenMatrix S hS
  let D := Matrix.diagonal hS.eigenvalues
  have hs : S = Q * D * Qᵀ := real_spectral_expansion S hS
  calc
    _ = (Q * D * Qᵀ) * (Q * D * Qᵀ) := congrArg₂ (fun A B => A * B) hs hs
    _ = Q * (D * (Qᵀ * Q) * D) * Qᵀ := by simp only [Matrix.mul_assoc]
    _ = Q * (D * D) * Qᵀ := by rw [realEigenMatrix_transpose_mul]; simp
    _ = _ := by
      simp only [D, Matrix.diagonal_mul_diagonal]
      congr 2
      funext i
      ring

theorem covarianceFactor_gram_of_cube (S : Matrix X X ℝ) (hS : S.IsHermitian)
    (hcube : S ^ 3 = S) :
    covarianceFactor S hS * (covarianceFactor S hS)ᴴ = complexify (S * S) := by
  rw [covarianceFactor_gram]
  simp_rw [abs_eigenvalue_eq_sq S hS hcube]
  rw [real_square_expansion S hS, complexify_mul, complexify_mul,
    complexify_diagonal, complexify_transpose]

theorem exists_real_partial_covariance_factor (S : Matrix X X ℝ) (hS : S.IsHermitian)
    (hcube : S ^ 3 = S) :
    ∃ W : Matrix X X ℂ, W * Wᵀ = complexify S ∧ W * Wᴴ = complexify (S * S) :=
  ⟨covarianceFactor S hS, covarianceFactor_covariance S hS,
    covarianceFactor_gram_of_cube S hS hcube⟩

end QuantumProver.WernerEndpoint.RealSymmetricFactor
