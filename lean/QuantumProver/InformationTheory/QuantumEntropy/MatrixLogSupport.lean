import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems

noncomputable section

open Matrix
open QuantumProver.SuperchannelDiscrimination.FlaggedStates
open QuantumProver.SuperchannelDiscrimination.TensorEntropy
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix Kronecker

namespace QuantumProver.QuantumEntropy.MatrixLogSupport

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem trace_mul_cfc_log_eq_eigenbasis_sum
    (R : Matrix I I ℂ) {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    (R * cfc Real.log A).trace =
      ∑ i, (((hA.eigenvectorUnitary : Matrix I I ℂ)ᴴ * R *
        (hA.eigenvectorUnitary : Matrix I I ℂ)) i i) * (Real.log (hA.eigenvalues i) : ℂ) := by
  rw [cfc_spectral Real.log hA]
  change (R * ((hA.eigenvectorUnitary : Matrix I I ℂ) *
    Matrix.diagonal (fun i => (Real.log (hA.eigenvalues i) : ℂ)) *
      (hA.eigenvectorUnitary : Matrix I I ℂ)ᴴ)).trace = _
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle]
  simp only [← Matrix.mul_assoc, Matrix.trace, Matrix.diag, Matrix.mul_diagonal]

theorem trace_mul_cfc_log_re_eq_eigenbasis_sum
    (R : Matrix I I ℂ) {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    (R * cfc Real.log A).trace.re =
      ∑ i, (((hA.eigenvectorUnitary : Matrix I I ℂ)ᴴ * R *
        (hA.eigenvectorUnitary : Matrix I I ℂ)) i i).re * Real.log (hA.eigenvalues i) := by
  rw [trace_mul_cfc_log_eq_eigenbasis_sum R hA]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

theorem eigenbasis_weight_nonneg {R A : Matrix I I ℂ} (hR : R.PosSemidef)
    (hA : A.IsHermitian) (i : I) :
    0 ≤ (((hA.eigenvectorUnitary : Matrix I I ℂ)ᴴ * R *
      (hA.eigenvectorUnitary : Matrix I I ℂ)) i i).re := by
  exact (Complex.nonneg_iff.mp
    ((hR.conjTranspose_mul_mul_same (hA.eigenvectorUnitary : Matrix I I ℂ)).diag_nonneg)).1

theorem cfc_log_mul_supportProjection {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    cfc Real.log A * supportProjection A = cfc Real.log A := by
  have hf : (fun x : ℝ => Real.log x * nonzeroWeight x) = Real.log := by
    funext x
    by_cases hx : x = 0 <;> simp [nonzeroWeight, hx]
  unfold supportProjection
  rw [← cfc_mul (p := IsSelfAdjoint) Real.log nonzeroWeight A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _), hf]

theorem supportProjection_mul_cfc_log {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    supportProjection A * cfc Real.log A = cfc Real.log A := by
  have hf : (fun x : ℝ => nonzeroWeight x * Real.log x) = Real.log := by
    funext x
    by_cases hx : x = 0 <;> simp [nonzeroWeight, hx]
  unfold supportProjection
  rw [← cfc_mul (p := IsSelfAdjoint) nonzeroWeight Real.log A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _), hf]

theorem mul_tensor_support_of_hasSupportIn
    {R : Matrix (I × J) (I × J) ℂ} {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hs : HasSupportIn R (A ⊗ₖ B)) :
    R * (supportProjection A ⊗ₖ supportProjection B) = R := by
  have h := (hasSupportIn_iff_mul_supportProjection (isHermitian_kronecker hA hB)).mp hs
  rwa [supportProjection_kronecker hA hB] at h

theorem weighted_left_log_support
    {R : Matrix (I × J) (I × J) ℂ} {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hs : HasSupportIn R (A ⊗ₖ B)) :
    R * (cfc Real.log A ⊗ₖ (1 : Matrix J J ℂ)) =
      R * (cfc Real.log A ⊗ₖ supportProjection B) := by
  have hR := mul_tensor_support_of_hasSupportIn hA hB hs
  calc
    R * (cfc Real.log A ⊗ₖ (1 : Matrix J J ℂ)) =
        (R * (supportProjection A ⊗ₖ supportProjection B)) *
          (cfc Real.log A ⊗ₖ (1 : Matrix J J ℂ)) := by rw [hR]
    _ = R * ((supportProjection A ⊗ₖ supportProjection B) *
          (cfc Real.log A ⊗ₖ (1 : Matrix J J ℂ))) := Matrix.mul_assoc _ _ _
    _ = R * (cfc Real.log A ⊗ₖ supportProjection B) := by
      rw [← Matrix.mul_kronecker_mul, supportProjection_mul_cfc_log hA, Matrix.mul_one]

theorem weighted_right_log_support
    {R : Matrix (I × J) (I × J) ℂ} {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hs : HasSupportIn R (A ⊗ₖ B)) :
    R * ((1 : Matrix I I ℂ) ⊗ₖ cfc Real.log B) =
      R * (supportProjection A ⊗ₖ cfc Real.log B) := by
  have hR := mul_tensor_support_of_hasSupportIn hA hB hs
  calc
    R * ((1 : Matrix I I ℂ) ⊗ₖ cfc Real.log B) =
        (R * (supportProjection A ⊗ₖ supportProjection B)) *
          ((1 : Matrix I I ℂ) ⊗ₖ cfc Real.log B) := by rw [hR]
    _ = R * ((supportProjection A ⊗ₖ supportProjection B) *
          ((1 : Matrix I I ℂ) ⊗ₖ cfc Real.log B)) := Matrix.mul_assoc _ _ _
    _ = R * (supportProjection A ⊗ₖ cfc Real.log B) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, supportProjection_mul_cfc_log hB]

theorem weighted_tensor_log
    {R : Matrix (I × J) (I × J) ℂ} {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hs : HasSupportIn R (A ⊗ₖ B)) :
    R * cfc Real.log (A ⊗ₖ B) =
      R * (cfc Real.log A ⊗ₖ (1 : Matrix J J ℂ)) +
        R * ((1 : Matrix I I ℂ) ⊗ₖ cfc Real.log B) := by
  rw [cfc_log_kronecker_support hA hB, Matrix.mul_add,
    ← weighted_left_log_support hA hB hs, ← weighted_right_log_support hA hB hs]

theorem trace_weighted_tensor_log
    {R : Matrix (I × J) (I × J) ℂ} {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hs : HasSupportIn R (A ⊗ₖ B)) :
    (R * cfc Real.log (A ⊗ₖ B)).trace =
      (R * (cfc Real.log A ⊗ₖ (1 : Matrix J J ℂ))).trace +
        (R * ((1 : Matrix I I ℂ) ⊗ₖ cfc Real.log B)).trace := by
  rw [weighted_tensor_log hA hB hs, Matrix.trace_add]

theorem trace_product_weighted_tensor_log
    (R A : Matrix I I ℂ) (S B : Matrix J J ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hs : HasSupportIn (R ⊗ₖ S) (A ⊗ₖ B)) :
    ((R ⊗ₖ S) * cfc Real.log (A ⊗ₖ B)).trace =
      (R * cfc Real.log A).trace * S.trace + R.trace * (S * cfc Real.log B).trace := by
  rw [weighted_tensor_log hA hB hs, Matrix.trace_add,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.mul_one, Matrix.mul_one, Matrix.trace_kronecker, Matrix.trace_kronecker]

theorem trace_product_weighted_tensor_log_of_trace_one
    (R A : Matrix I I ℂ) (S B : Matrix J J ℂ)
    (hR : R.trace = 1) (hS : S.trace = 1)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hRA : HasSupportIn R A) (hSB : HasSupportIn S B) :
    ((R ⊗ₖ S) * cfc Real.log (A ⊗ₖ B)).trace =
      (R * cfc Real.log A).trace + (S * cfc Real.log B).trace := by
  have hs := (hasSupportIn_kronecker_iff hR hS hA hB).mpr ⟨hRA, hSB⟩
  rw [trace_product_weighted_tensor_log R A S B hA hB hs, hR, hS, mul_one, one_mul]

end QuantumProver.QuantumEntropy.MatrixLogSupport
