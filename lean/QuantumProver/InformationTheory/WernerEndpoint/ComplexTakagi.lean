import QuantumProver.InformationTheory.WernerEndpoint.TakagiCompletion
import QuantumProver.InformationTheory.WernerEndpoint.D5RankSix

noncomputable section

namespace QuantumProver.WernerEndpoint.ComplexTakagi

open scoped BigOperators
open Matrix Unitary TakagiAntilinear TakagiCompletion SchattenSupport D5RankSix

variable {X : Type*} [Fintype X] [DecidableEq X]

def basisUnitary (b : OrthonormalBasis X ℂ (EuclideanSpace ℂ X)) :
    Matrix.unitaryGroup X ℂ :=
  ⟨(EuclideanSpace.basisFun X ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun X ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩

theorem basisUnitary_apply (b : OrthonormalBasis X ℂ (EuclideanSpace ℂ X)) (i j : X) :
    (basisUnitary b : Matrix X X ℂ) i j = b j i := rfl

theorem unitary_left (U : Matrix.unitaryGroup X ℂ) :
    (U : Matrix X X ℂ)ᴴ * (U : Matrix X X ℂ) = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U

theorem unitary_right (U : Matrix.unitaryGroup X ℂ) :
    (U : Matrix X X ℂ) * (U : Matrix X X ℂ)ᴴ = 1 := by
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U

theorem conjugate_mul_transpose (U : Matrix.unitaryGroup X ℂ) :
    entryConj (U : Matrix X X ℂ) * (U : Matrix X X ℂ)ᵀ = 1 := by
  change (U : Matrix X X ℂ)ᴴᵀ * (U : Matrix X X ℂ)ᵀ = 1
  rw [← Matrix.transpose_mul, unitary_right, Matrix.transpose_one]

theorem transpose_mul_conjugate (U : Matrix.unitaryGroup X ℂ) :
    (U : Matrix X X ℂ)ᵀ * entryConj (U : Matrix X X ℂ) = 1 := by
  change (U : Matrix X X ℂ)ᵀ * (U : Matrix X X ℂ)ᴴᵀ = 1
  rw [← Matrix.transpose_mul, unitary_left, Matrix.transpose_one]

theorem exists_complex_symmetric_takagi (M : Matrix X X ℂ) (hM : Mᵀ = M) :
    ∃ (U : Matrix.unitaryGroup X ℂ) (s : X → ℝ), (∀ i, 0 ≤ s i) ∧
      M = (U : Matrix X X ℂ) * Matrix.diagonal (fun i => Complex.ofReal (s i)) *
        (U : Matrix X X ℂ)ᵀ := by
  obtain ⟨b, s, hs, heig⟩ := exists_antilinear_orthonormalBasis M hM
  let U := basisUnitary b
  have hd : M * entryConj (U : Matrix X X ℂ) =
      (U : Matrix X X ℂ) * Matrix.diagonal (fun i => Complex.ofReal (s i)) := by
    ext i j
    rw [Matrix.mul_diagonal]
    have h := congrArg (fun v : EuclideanSpace ℂ X => v i) (heig j)
    change (∑ k, M i k * star (b j k)) = b j i * Complex.ofReal (s j)
    simpa [antiLinear, Matrix.mulVec, dotProduct, mul_comm] using h
  refine ⟨U, s, hs, ?_⟩
  calc
    M = M * (entryConj (U : Matrix X X ℂ) * (U : Matrix X X ℂ)ᵀ) := by
      rw [conjugate_mul_transpose, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hd]

theorem takagi_leftGram (M : Matrix X X ℂ) (U : Matrix.unitaryGroup X ℂ) (s : X → ℝ)
    (hM : M = (U : Matrix X X ℂ) * Matrix.diagonal (fun i => Complex.ofReal (s i)) *
      (U : Matrix X X ℂ)ᵀ) :
    M * Mᴴ = (U : Matrix X X ℂ) * Matrix.diagonal (fun i => Complex.ofReal (s i ^ 2)) *
      (U : Matrix X X ℂ)ᴴ := by
  let Q := (U : Matrix X X ℂ)
  let D : Matrix X X ℂ := Matrix.diagonal (fun i => Complex.ofReal (s i))
  have hD : Dᴴ = D := by
    simp only [D, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  have hQ : Qᵀ * (Qᵀ)ᴴ = 1 := by
    change (U : Matrix X X ℂ)ᵀ * entryConj (U : Matrix X X ℂ) = 1
    exact transpose_mul_conjugate U
  have hDD : D * D = Matrix.diagonal (fun i => Complex.ofReal (s i ^ 2)) := by
    simp only [D, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [pow_two]
  have hm : M = Q * D * Qᵀ := hM
  calc
    _ = (Q * D * Qᵀ) * (Q * D * Qᵀ)ᴴ := congrArg₂ (fun A B => A * Bᴴ) hm hm
    _ = Q * (D * (Qᵀ * (Qᵀ)ᴴ) * D) * Qᴴ := by
      simp only [Matrix.conjTranspose_mul, hD, Matrix.mul_assoc]
    _ = Q * (D * D) * Qᴴ := by rw [hQ]; simp
    _ = _ := by rw [hDD]

theorem takagi_squared_spectrum (M : Matrix X X ℂ) (U : Matrix.unitaryGroup X ℂ) (s : X → ℝ)
    (hM : M = (U : Matrix X X ℂ) * Matrix.diagonal (fun i => Complex.ofReal (s i)) *
      (U : Matrix X X ℂ)ᵀ) :
    Multiset.map (fun i => s i ^ 2) Finset.univ.val =
      Multiset.map (gramHermitian M).eigenvalues Finset.univ.val := by
  have hl := takagi_leftGram M U s hM
  have hc : (Mᴴ * M).charpoly =
      (Matrix.diagonal (fun i => Complex.ofReal (s i ^ 2))).charpoly := by
    rw [Matrix.charpoly_mul_comm Mᴴ M, hl, Matrix.charpoly_mul_comm,
      ← Matrix.mul_assoc, unitary_left, Matrix.one_mul]
  have hr : (Matrix.diagonal (fun i => Complex.ofReal (s i ^ 2))).charpoly.roots =
      Multiset.map (fun i => Complex.ofReal (s i ^ 2)) Finset.univ.val := by
    rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _)
  have he := congrArg Polynomial.roots hc
  rw [(gramHermitian M).roots_charpoly_eq_eigenvalues, hr] at he
  have hre := congrArg (Multiset.map Complex.re) he.symm
  simp only [Multiset.map_map] at hre
  change Multiset.map (fun i => (Complex.ofReal (s i ^ 2)).re) Finset.univ.val =
    Multiset.map (fun i => (Complex.ofReal ((gramHermitian M).eigenvalues i)).re)
      Finset.univ.val at hre
  simpa only [Complex.ofReal_re] using hre

theorem takagi_nonzero_count (M : Matrix X X ℂ) (U : Matrix.unitaryGroup X ℂ) (s : X → ℝ)
    (hM : M = (U : Matrix X X ℂ) * Matrix.diagonal (fun i => Complex.ofReal (s i)) *
      (U : Matrix X X ℂ)ᵀ) :
    (Finset.univ.filter (fun i => s i ≠ 0)).card = M.rank := by
  have he := takagi_squared_spectrum M U s hM
  have hc := congrArg (fun l : Multiset ℝ => (l.filter (fun x => x ≠ 0)).card) he
  have hn : (Finset.univ.filter (fun i => s i ≠ 0)).card = (spectralSupport M).card := by
    simpa [spectralSupport, Multiset.filter_map, ← Finset.filter_val] using hc
  exact hn.trans (spectralSupport_card M)

theorem exists_complex_symmetric_takagi_with_spectrum (M : Matrix X X ℂ) (hM : Mᵀ = M) :
    ∃ (U : Matrix.unitaryGroup X ℂ) (s : X → ℝ), (∀ i, 0 ≤ s i) ∧
      M = (U : Matrix X X ℂ) * Matrix.diagonal (fun i => Complex.ofReal (s i)) *
        (U : Matrix X X ℂ)ᵀ ∧
      Multiset.map (fun i => s i ^ 2) Finset.univ.val =
        Multiset.map (gramHermitian M).eigenvalues Finset.univ.val ∧
      (Finset.univ.filter (fun i => s i ≠ 0)).card = M.rank := by
  obtain ⟨U, s, hs, he⟩ := exists_complex_symmetric_takagi M hM
  exact ⟨U, s, hs, he, takagi_squared_spectrum M U s he, takagi_nonzero_count M U s he⟩

end QuantumProver.WernerEndpoint.ComplexTakagi
