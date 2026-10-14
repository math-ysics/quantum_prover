import QuantumProver.InformationTheory.WernerEndpoint.SchattenSupport
import QuantumProver.InformationTheory.WernerEndpoint.RealSymmetricFactor

noncomputable section

namespace QuantumProver.WernerEndpoint.ExteriorSchatten

open scoped BigOperators
open Matrix ExteriorSupport SchattenSupport RealSymmetricFactor

variable {Y X J : Type*} [Fintype Y] [Fintype X] [Fintype J]

theorem orderedExterior_conjTranspose (A : Matrix Y X ℂ) :
    orderedExterior Aᴴ = (orderedExterior A)ᴴ := by
  ext ab ij
  simp [orderedExterior, Matrix.conjTranspose_apply, star_sub, star_mul,
    star_div, mul_comm]

theorem hsNormSq_mul_of_gram (A : Matrix Y X ℂ) (W : Matrix X J ℂ)
    (P : Matrix X X ℂ) (hgram : W * Wᴴ = P) (hherm : Pᴴ = P)
    (hid : P * P = P) : hsNormSq (A * W) = hsNormSq (A * P) := by
  have hleft : (A * W) * (A * W)ᴴ = A * P * Aᴴ := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = A * (W * Wᴴ) * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hgram]
  have hright : (A * P) * (A * P)ᴴ = A * P * Aᴴ := by
    rw [Matrix.conjTranspose_mul, hherm]
    calc
      _ = A * (P * P) * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hid]
  rw [hsNormSq_eq_trace, hsNormSq_eq_trace, hleft, hright]

theorem exterior_covariance_support [DecidableEq Y]
    (A : Matrix Y X ℂ) (W : Matrix X J ℂ) (B P : Matrix X X ℂ)
    (hcov : W * Wᵀ = B) (hgram : W * Wᴴ = P)
    (hherm : Pᴴ = P) (hid : P * P = P) :
    schattenOne (orderedExterior (A * B * Aᵀ)) ≤ hsNormSq (orderedExterior (A * P)) := by
  classical
  have hcovA : A * B * Aᵀ = (A * W) * (A * W)ᵀ := by
    rw [← hcov, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  have hgramE : orderedExterior W * (orderedExterior W)ᴴ = orderedExterior P := by
    rw [← orderedExterior_conjTranspose, ← orderedExterior_mul, hgram]
  have hhermE : (orderedExterior P)ᴴ = orderedExterior P := by
    rw [← orderedExterior_conjTranspose, hherm]
  have hidE : orderedExterior P * orderedExterior P = orderedExterior P := by
    rw [← orderedExterior_mul, hid]
  have hh := hsNormSq_mul_of_gram (orderedExterior A) (orderedExterior W)
    (orderedExterior P) hgramE hhermE hidE
  rw [← orderedExterior_mul, ← orderedExterior_mul] at hh
  rw [hcovA, orderedExterior_mul, orderedExterior_transpose]
  rw [← hh]
  exact schattenOne_covariance (orderedExterior (A * W))

def d5SupportMask (t : Fin 5) : Matrix (Edge 5) (Edge 5) ℂ :=
  Matrix.diagonal (fun e => if t ∈ edgeVertices e then 0 else 1)

theorem d5SupportMask_hermitian (t : Fin 5) :
    (d5SupportMask t)ᴴ = d5SupportMask t := by
  simp only [d5SupportMask, Matrix.diagonal_conjTranspose]
  congr 1
  funext e
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem d5SupportMask_idempotent (t : Fin 5) :
    d5SupportMask t * d5SupportMask t = d5SupportMask t := by
  simp only [d5SupportMask, Matrix.diagonal_mul_diagonal]
  congr 1
  funext e
  split_ifs <;> simp

theorem mul_d5SupportMask (A : Matrix Y (Edge 5) ℂ) (t : Fin 5) :
    A * d5SupportMask t = d5ColumnRestriction A t := by
  ext i e
  simp [d5SupportMask, d5ColumnRestriction, Matrix.mul_diagonal]

theorem d5_exterior_schatten_sum [DecidableEq Y]
    (A : Matrix Y (Edge 5) ℂ) (B : Fin 5 → Matrix (Edge 5) (Edge 5) ℂ)
    (W : Fin 5 → Matrix (Edge 5) J ℂ)
    (hcov : ∀ t, W t * (W t)ᵀ = B t)
    (hgram : ∀ t, W t * (W t)ᴴ = d5SupportMask t) :
    (∑ t, schattenOne (orderedExterior (A * B t * Aᵀ))) ≤
      2 * hsNormSq (orderedExterior A) := by
  classical
  calc
    _ ≤ ∑ t, hsNormSq (orderedExterior (d5ColumnRestriction A t)) := by
      apply Finset.sum_le_sum
      intro t _
      have h := exterior_covariance_support A (W t) (B t) (d5SupportMask t)
        (hcov t) (hgram t) (d5SupportMask_hermitian t) (d5SupportMask_idempotent t)
      simpa only [mul_d5SupportMask] using h
    _ ≤ _ := d5_restricted_exterior_hs_sum A

theorem d5_exterior_schatten_sum_of_normalized [DecidableEq Y]
    (A : Matrix Y (Edge 5) ℂ) (B : Fin 5 → Matrix (Edge 5) (Edge 5) ℂ)
    (W : Fin 5 → Matrix (Edge 5) J ℂ)
    (hcov : ∀ t, W t * (W t)ᵀ = B t)
    (hgram : ∀ t, W t * (W t)ᴴ = d5SupportMask t) (hA : hsNormSq A = 1) :
    (∑ t, schattenOne (orderedExterior (A * B t * Aᵀ))) ≤
      1 - purity (reducedLeft A) := by
  have h := d5_exterior_schatten_sum A B W hcov hgram
  rw [orderedExterior_hsNormSq_of_normalized A hA] at h
  linarith

end QuantumProver.WernerEndpoint.ExteriorSchatten
