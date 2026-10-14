import QuantumProver.InformationTheory.QuantumEntropy.Definitions

set_option autoImplicit false

noncomputable section

open Matrix Kronecker
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.LocalInstrumentMarginals

open QuantumProver.QuantumEntropy

variable {A B O I : Type*} [Fintype A] [Fintype B] [Fintype O] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq O]

def localLift (K : Matrix O A ℂ) : Matrix (O × B) (A × B) ℂ :=
  K ⊗ₖ (1 : Matrix B B ℂ)

def branch (K : Matrix O A ℂ) (R : Matrix (A × B) (A × B) ℂ) :
    Matrix (O × B) (O × B) ℂ :=
  localLift (B := B) K * R * (localLift (B := B) K)ᴴ

def branchProbability (K : Matrix O A ℂ)
    (R : Matrix (A × B) (A × B) ℂ) : ℝ := (branch K R).trace.re

def output (K : I → Matrix O A ℂ) (R : Matrix (A × B) (A × B) ℂ) :
    Matrix (O × B) (O × B) ℂ := ∑ i, branch (K i) R

def normalizedBranch (K : I → Matrix O A ℂ)
    (R : Matrix (A × B) (A × B) ℂ) (i : I) :
    Matrix (O × B) (O × B) ℂ :=
  if branchProbability (K i) R = 0 then output K R
  else (branchProbability (K i) R)⁻¹ • branch (K i) R

def normalizedUntouchedMarginal (K : I → Matrix O A ℂ)
    (R : Matrix (A × B) (A × B) ℂ) (i : I) : Matrix B B ℂ :=
  partialTrace_left (normalizedBranch K R i)

omit [Fintype A] [Fintype B] [Fintype O] [DecidableEq A] [DecidableEq O] in
theorem localLift_apply (K : Matrix O A ℂ) (o : O) (a : A) (b c : B) :
    localLift K (o,b) (a,c) = if b = c then K o a else 0 := by
  simp only [localLift, Matrix.kronecker_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero]

theorem localLift_mul_apply (K : Matrix O A ℂ)
    (R : Matrix (A × B) (A × B) ℂ) (o : O) (a' : A) (b b' : B) :
    (localLift (B := B) K * R) (o,b) (a',b') =
      ∑ a, K o a * R (a,b) (a',b') := by
  classical
  simp [Matrix.mul_apply, Fintype.sum_prod_type, localLift_apply, ite_mul]

theorem branch_apply (K : Matrix O A ℂ)
    (R : Matrix (A × B) (A × B) ℂ) (o o' : O) (b b' : B) :
    branch K R (o,b) (o',b') =
      ∑ a', ∑ a, K o a * R (a,b) (a',b') * star (K o' a') := by
  classical
  change (∑ ab : A × B, (localLift (B := B) K * R) (o,b) ab *
    star (localLift (B := B) K (o',b') ab)) = _
  rw [Fintype.sum_prod_type]
  simp [localLift_mul_apply, localLift_apply, apply_ite, Finset.sum_mul, mul_ite]

theorem untouchedMarginal_branch_apply (K : Matrix O A ℂ)
    (R : Matrix (A × B) (A × B) ℂ) (b b' : B) :
    partialTrace_left (branch K R) b b' =
      ∑ a', ∑ a, (Kᴴ * K) a' a * R (a,b) (a',b') := by
  classical
  simp only [partialTrace_left, branch_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  calc
    (∑ o, ∑ a', ∑ a, K o a * R (a,b) (a',b') * star (K o a')) =
        ∑ a', ∑ o, ∑ a, K o a * R (a,b) (a',b') * star (K o a') :=
      Finset.sum_comm
    _ = ∑ a', ∑ a, ∑ o, K o a * R (a,b) (a',b') * star (K o a') := by
      apply Finset.sum_congr rfl
      intro a' _
      exact Finset.sum_comm
    _ = ∑ a', ∑ a, (∑ o, star (K o a') * K o a) * R (a,b) (a',b') := by
      apply Finset.sum_congr rfl
      intro a' _
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro o _
      ring

theorem sum_untouchedMarginals (K : I → Matrix O A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1)
    (R : Matrix (A × B) (A × B) ℂ) :
    (∑ i, partialTrace_left (branch (K i) R)) = partialTrace_left R := by
  classical
  ext b b'
  simp only [Matrix.sum_apply, untouchedMarginal_branch_apply]
  calc
    (∑ i, ∑ a', ∑ a, ((K i)ᴴ * K i) a' a * R (a,b) (a',b')) =
        ∑ a', ∑ i, ∑ a, ((K i)ᴴ * K i) a' a * R (a,b) (a',b') :=
      Finset.sum_comm
    _ = ∑ a', ∑ a, ∑ i, ((K i)ᴴ * K i) a' a * R (a,b) (a',b') := by
      apply Finset.sum_congr rfl
      intro a' _
      exact Finset.sum_comm
    _ = ∑ a', ∑ a, (∑ i, (K i)ᴴ * K i) a' a * R (a,b) (a',b') := by
      simp only [Matrix.sum_apply, Finset.sum_mul]
    _ = ∑ a', ∑ a, (1 : Matrix A A ℂ) a' a * R (a,b) (a',b') := by rw [hK]
    _ = partialTrace_left R b b' := by
      simp [Matrix.one_apply, partialTrace_left, ite_mul]

omit [DecidableEq A] [DecidableEq B] in
private theorem trace_partialTrace_left (X : Matrix (A × B) (A × B) ℂ) :
    (partialTrace_left X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, partialTrace_left, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
private theorem partialTrace_left_sum (X : I → Matrix (A × B) (A × B) ℂ) :
    partialTrace_left (∑ i, X i) = ∑ i, partialTrace_left (X i) := by
  classical
  ext b b'
  simp only [partialTrace_left, Matrix.sum_apply]
  exact Finset.sum_comm

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
private theorem partialTrace_left_smul (t : ℝ) (X : Matrix (A × B) (A × B) ℂ) :
    partialTrace_left (t • X) = t • partialTrace_left X := by
  ext b b'
  simp [partialTrace_left, Matrix.smul_apply, Finset.smul_sum]

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
private theorem partialTrace_left_posSemidef
    {X : Matrix (A × B) (A × B) ℂ} (hX : X.PosSemidef) :
    (partialTrace_left X).PosSemidef := by
  classical
  have hEq : partialTrace_left X = ∑ a, X.submatrix (fun b => (a,b)) (fun b => (a,b)) := by
    ext b b'
    simp [partialTrace_left, Matrix.sum_apply, Matrix.submatrix_apply]
  rw [hEq]
  exact (Finset.sum_nonneg (fun a _ => (hX.submatrix (fun b => (a,b))).nonneg)).posSemidef

omit [DecidableEq A] [DecidableEq O] in
theorem branch_posSemidef (K : Matrix O A ℂ)
    {R : Matrix (A × B) (A × B) ℂ} (hR : R.PosSemidef) :
    (branch K R).PosSemidef := by
  simpa only [branch] using hR.mul_mul_conjTranspose_same (localLift (B := B) K)

theorem branchProbability_nonneg (K : Matrix O A ℂ)
    {R : Matrix (A × B) (A × B) ℂ} (hR : R.PosSemidef) :
    0 ≤ branchProbability K R :=
  (Complex.nonneg_iff.mp (branch_posSemidef K hR).trace_nonneg).1

theorem branch_eq_zero_of_probability_eq_zero (K : Matrix O A ℂ)
    {R : Matrix (A × B) (A × B) ℂ} (hR : R.PosSemidef)
    (hZero : branchProbability K R = 0) : branch K R = 0 := by
  have hB := branch_posSemidef K hR
  apply hB.trace_eq_zero_iff.mp
  apply Complex.ext
  · exact hZero
  · simpa only [Complex.zero_im] using (Complex.nonneg_iff.mp hB.trace_nonneg).2.symm

theorem output_untouchedMarginal (K : I → Matrix O A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1)
    (R : Matrix (A × B) (A × B) ℂ) :
    partialTrace_left (output K R) = partialTrace_left R := by
  rw [output, partialTrace_left_sum]
  exact sum_untouchedMarginals K hK R

theorem output_trace (K : I → Matrix O A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1)
    (R : Matrix (A × B) (A × B) ℂ) : (output K R).trace = R.trace := by
  calc
    (output K R).trace = (partialTrace_left (output K R)).trace :=
      (trace_partialTrace_left _).symm
    _ = (partialTrace_left R).trace := congrArg Matrix.trace (output_untouchedMarginal K hK R)
    _ = R.trace := trace_partialTrace_left R

theorem sum_branchProbabilities_eq_one (K : I → Matrix O A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1)
    {R : Matrix (A × B) (A × B) ℂ} (hR : IsDensity R) :
    ∑ i, branchProbability (K i) R = 1 := by
  have h := congrArg Complex.re ((output_trace K hK R).trans hR.2)
  simpa only [output, Matrix.trace_sum, Complex.re_sum, branchProbability, Complex.one_re] using h

theorem branchProbability_le_one (K : I → Matrix O A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1)
    {R : Matrix (A × B) (A × B) ℂ} (hR : IsDensity R) (i : I) :
    branchProbability (K i) R ≤ 1 := by
  classical
  calc
    branchProbability (K i) R ≤ ∑ j, branchProbability (K j) R :=
      Finset.single_le_sum (fun j _ => branchProbability_nonneg (K j) hR.1)
        (Finset.mem_univ i)
    _ = 1 := sum_branchProbabilities_eq_one K hK hR

theorem output_isDensity (K : I → Matrix O A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1)
    {R : Matrix (A × B) (A × B) ℂ} (hR : IsDensity R) : IsDensity (output K R) := by
  classical
  refine ⟨?_, (output_trace K hK R).trans hR.2⟩
  exact (Finset.sum_nonneg (fun i _ => (branch_posSemidef (K i) hR.1).nonneg)).posSemidef

theorem probability_smul_normalizedBranch (K : I → Matrix O A ℂ)
    {R : Matrix (A × B) (A × B) ℂ} (hR : R.PosSemidef) (i : I) :
    branchProbability (K i) R • normalizedBranch K R i = branch (K i) R := by
  classical
  by_cases hZero : branchProbability (K i) R = 0
  · rw [hZero, zero_smul, branch_eq_zero_of_probability_eq_zero (K i) hR hZero]
  · simp only [normalizedBranch, ite_eq_right hZero, smul_smul,
      mul_inv_cancel₀ hZero, one_smul]

theorem normalizedBranch_isDensity (K : I → Matrix O A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1)
    {R : Matrix (A × B) (A × B) ℂ} (hR : IsDensity R) (i : I) :
    IsDensity (normalizedBranch K R i) := by
  classical
  by_cases hZero : branchProbability (K i) R = 0
  · simpa only [normalizedBranch, ite_eq_left hZero] using output_isDensity K hK hR
  · have hPSD : ((branchProbability (K i) R)⁻¹ • branch (K i) R).PosSemidef :=
      (branch_posSemidef (K i) hR.1).smul (inv_nonneg.mpr (branchProbability_nonneg (K i) hR.1))
    have hReal : ((branchProbability (K i) R)⁻¹ • branch (K i) R).trace.re = 1 := by
      simp only [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
      change (branchProbability (K i) R)⁻¹ * branchProbability (K i) R = 1
      exact inv_mul_cancel₀ hZero
    refine ⟨by simpa only [normalizedBranch, ite_eq_right hZero] using hPSD, ?_⟩
    simp only [normalizedBranch, ite_eq_right hZero]
    apply Complex.ext
    · simpa only [Complex.one_re] using hReal
    · simpa only [Complex.one_im] using (Complex.nonneg_iff.mp hPSD.trace_nonneg).2.symm

theorem normalizedUntouchedMarginal_isDensity (K : I → Matrix O A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1)
    {R : Matrix (A × B) (A × B) ℂ} (hR : IsDensity R) (i : I) :
    IsDensity (normalizedUntouchedMarginal K R i) := by
  have hN := normalizedBranch_isDensity K hK hR i
  exact ⟨partialTrace_left_posSemidef hN.1, (trace_partialTrace_left _).trans hN.2⟩

theorem normalizedUntouchedMarginal_of_probability_eq_zero (K : I → Matrix O A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1)
    (R : Matrix (A × B) (A × B) ℂ) (i : I)
    (hZero : branchProbability (K i) R = 0) :
    normalizedUntouchedMarginal K R i = partialTrace_left R := by
  simpa only [normalizedUntouchedMarginal, normalizedBranch, ite_eq_left hZero] using
    output_untouchedMarginal K hK R

theorem probability_smul_normalizedUntouchedMarginal (K : I → Matrix O A ℂ)
    {R : Matrix (A × B) (A × B) ℂ} (hR : R.PosSemidef) (i : I) :
    branchProbability (K i) R • normalizedUntouchedMarginal K R i =
      partialTrace_left (branch (K i) R) := by
  rw [normalizedUntouchedMarginal, ← partialTrace_left_smul,
    probability_smul_normalizedBranch K hR i]

theorem weighted_normalizedUntouchedMarginals (K : I → Matrix O A ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1)
    {R : Matrix (A × B) (A × B) ℂ} (hR : R.PosSemidef) :
    (∑ i, branchProbability (K i) R • normalizedUntouchedMarginal K R i) =
      partialTrace_left R := by
  classical
  calc
    (∑ i, branchProbability (K i) R • normalizedUntouchedMarginal K R i) =
        ∑ i, partialTrace_left (branch (K i) R) := by
      apply Finset.sum_congr rfl
      intro i _
      exact probability_smul_normalizedUntouchedMarginal K hR i
    _ = partialTrace_left R := sum_untouchedMarginals K hK R

end QuantumProver.LocalInstrumentMarginals
