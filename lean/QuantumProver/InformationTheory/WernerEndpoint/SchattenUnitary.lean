import QuantumProver.InformationTheory.WernerEndpoint.TakagiRankSix

noncomputable section
namespace QuantumProver.WernerEndpoint.SchattenUnitary

open scoped BigOperators Kronecker
open Matrix ComplexTakagi SchattenSupport

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem unitary_congruence_leftGram (U : Matrix.unitaryGroup X ℂ) (M : Matrix X X ℂ) :
    ((U : Matrix X X ℂ) * M * (U : Matrix X X ℂ)ᵀ) *
      ((U : Matrix X X ℂ) * M * (U : Matrix X X ℂ)ᵀ)ᴴ =
      (U : Matrix X X ℂ) * (M * Mᴴ) * (U : Matrix X X ℂ)ᴴ := by
  have hu : (U : Matrix X X ℂ)ᵀ * ((U : Matrix X X ℂ)ᵀ)ᴴ = 1 :=
    transpose_mul_conjugate U
  calc
    _ = (U : Matrix X X ℂ) * (M * ((U : Matrix X X ℂ)ᵀ *
      ((U : Matrix X X ℂ)ᵀ)ᴴ) * Mᴴ) * (U : Matrix X X ℂ)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hu]; simp

theorem schattenOne_unitary_congruence (U : Matrix.unitaryGroup X ℂ) (M : Matrix X X ℂ) :
    schattenOne ((U : Matrix X X ℂ) * M * (U : Matrix X X ℂ)ᵀ) = schattenOne M := by
  let K := (U : Matrix X X ℂ) * M * (U : Matrix X X ℂ)ᵀ
  have hc : (Kᴴ * K).charpoly = (Mᴴ * M).charpoly := by
    rw [Matrix.charpoly_mul_comm Kᴴ K]
    change (((U : Matrix X X ℂ) * M * (U : Matrix X X ℂ)ᵀ) *
      ((U : Matrix X X ℂ) * M * (U : Matrix X X ℂ)ᵀ)ᴴ).charpoly = _
    rw [unitary_congruence_leftGram, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      unitary_left, Matrix.one_mul, Matrix.charpoly_mul_comm]
  have he := (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
    (gramHermitian K) (gramHermitian M)).mpr hc
  simp only [schattenOne, singularValue, he]

def kroneckerUnitary (U : Matrix.unitaryGroup X ℂ) : Matrix.unitaryGroup (X × X) ℂ :=
  ⟨(U : Matrix X X ℂ) ⊗ₖ (U : Matrix X X ℂ), by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      unitary_left, Matrix.one_kronecker_one]⟩

end QuantumProver.WernerEndpoint.SchattenUnitary
