import Mathlib

/-! Register rectangular inverse-purification matrices for reconstructing a
whole-output channel from a positive extension. No channel or extension
existence is assumed by a structure. -/

open scoped ComplexConjugate ComplexOrder BigOperators Matrix Kronecker

namespace TransposeDegradability

noncomputable section

set_option maxHeartbeats 800000

variable {R B E : Type} [Fintype R] [Fintype B] [Fintype E]
variable [DecidableEq R] [DecidableEq B] [DecidableEq E]

/-- Literal Gram of the actual purification's B columns. -/
def purificationGram (Z : Matrix R B ℂ) : Matrix B B ℂ := Zᴴ * Z

/-- Defined on the whole B algebra by the actual nonsingular Gram inverse. -/
def purificationLeftInverse (Z : Matrix R B ℂ) : Matrix B R ℂ :=
  (purificationGram Z)⁻¹ * Zᴴ

def purificationProjection (Z : Matrix R B ℂ) : Matrix R R ℂ :=
  Z * purificationLeftInverse Z

omit [DecidableEq R] in
theorem purificationLeftInverse_mul (Z : Matrix R B ℂ)
    (hZ : (purificationGram Z).PosDef) : purificationLeftInverse Z * Z = 1 := by
  unfold purificationLeftInverse purificationGram
  rw [Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ (((purificationGram Z).isUnit_iff_isUnit_det).mp hZ.isUnit)

omit [DecidableEq R] in
theorem purificationProjection_mul (Z : Matrix R B ℂ)
    (hZ : (purificationGram Z).PosDef) : purificationProjection Z * Z = Z := by
  unfold purificationProjection
  rw [Matrix.mul_assoc, purificationLeftInverse_mul Z hZ, Matrix.mul_one]

omit [DecidableEq R] in
theorem purificationProjection_idempotent (Z : Matrix R B ℂ)
    (hZ : (purificationGram Z).PosDef) :
    purificationProjection Z * purificationProjection Z = purificationProjection Z := by
  unfold purificationProjection
  calc
    _ = Z * (purificationLeftInverse Z * Z) * purificationLeftInverse Z := by
      simp only [Matrix.mul_assoc]
    _ = Z * purificationLeftInverse Z := by
      rw [purificationLeftInverse_mul Z hZ, Matrix.mul_one]

omit [DecidableEq R] in
theorem purificationProjection_isHermitian (Z : Matrix R B ℂ) :
    (purificationProjection Z).IsHermitian := by
  change (Z * ((purificationGram Z)⁻¹ * Zᴴ))ᴴ = Z * ((purificationGram Z)⁻¹ * Zᴴ)
  have hG : (purificationGram Z)⁻¹.IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_self Z).inv
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG.eq,
    Matrix.mul_assoc]

theorem purificationComplement_mul (Z : Matrix R B ℂ)
    (hZ : (purificationGram Z).PosDef) : (1 - purificationProjection Z) * Z = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, purificationProjection_mul Z hZ, sub_self]

omit [DecidableEq R] in
theorem purificationLeftInverse_marginal (Z : Matrix R B ℂ)
    (hZ : (purificationGram Z).PosDef) :
    purificationLeftInverse Z * (Z * Zᴴ) * (purificationLeftInverse Z)ᴴ = 1 := by
  calc
    _ = (purificationLeftInverse Z * Z) * (purificationLeftInverse Z * Z)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [purificationLeftInverse_mul Z hZ, Matrix.conjTranspose_one, Matrix.one_mul]

/-- Actual unnormalized Choi candidate. Its output marginal will be derived
from the original extension marginal in LemmasC. -/
def reconstructedChoi (Z : Matrix R B ℂ) (sigma : Matrix (R × E) (R × E) ℂ) :
    Matrix (B × E) (B × E) ℂ :=
  (purificationLeftInverse Z ⊗ₖ (1 : Matrix E E ℂ)) * sigma *
    (purificationLeftInverse Z ⊗ₖ (1 : Matrix E E ℂ))ᴴ

omit [DecidableEq R] in
theorem reconstructedChoi_posSemidef (Z : Matrix R B ℂ)
    (sigma : Matrix (R × E) (R × E) ℂ) (hSigma : sigma.PosSemidef) :
    (reconstructedChoi Z sigma).PosSemidef :=
  hSigma.mul_mul_conjTranspose_same _

omit [DecidableEq R] in
theorem reconstructedChoi_reproduce_of_support (Z : Matrix R B ℂ)
    (sigma : Matrix (R × E) (R × E) ℂ)
    (hSupport :
      (purificationProjection Z ⊗ₖ (1 : Matrix E E ℂ)) * sigma *
        (purificationProjection Z ⊗ₖ (1 : Matrix E E ℂ))ᴴ = sigma) :
    (Z ⊗ₖ (1 : Matrix E E ℂ)) * reconstructedChoi Z sigma *
      (Z ⊗ₖ (1 : Matrix E E ℂ))ᴴ = sigma := by
  unfold reconstructedChoi
  have hTensor :
      (Z ⊗ₖ (1 : Matrix E E ℂ)) * (purificationLeftInverse Z ⊗ₖ (1 : Matrix E E ℂ)) =
      purificationProjection Z ⊗ₖ (1 : Matrix E E ℂ) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
    rfl
  calc
    _ = ((Z ⊗ₖ (1 : Matrix E E ℂ)) * (purificationLeftInverse Z ⊗ₖ (1 : Matrix E E ℂ))) *
        sigma * ((Z ⊗ₖ (1 : Matrix E E ℂ)) *
          (purificationLeftInverse Z ⊗ₖ (1 : Matrix E E ℂ)))ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = sigma := by rw [hTensor]; exact hSupport

end
end TransposeDegradability
