import Mathlib
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.LaneLimitBounds

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix
  Matrix.Norms.L2Operator

namespace QuantumProver.MatrixTracePower

open QuantumProver.AmplitudeDamping

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem rpow_smul_nonneg {A : Matrix I I ℂ} (hA : A.PosSemidef)
    {c α : ℝ} (hc : 0 ≤ c) (hα : 1 ≤ α) :
    CFC.rpow (c • A) α = (c ^ α) • CFC.rpow A α := by
  have hca : (c • A).PosSemidef := hA.smul hc
  have hp : 0 ≤ α := le_trans (by norm_num : (0 : ℝ) ≤ 1) hα
  have hcont : Continuous (fun x : ℝ => x ^ α) := Real.continuous_rpow_const hp
  calc
    CFC.rpow (c • A) α = cfc (fun x : ℝ => x ^ α) (c • A) :=
      CFC.rpow_eq_cfc_real hca.nonneg
    _ = cfc (fun x : ℝ => (c * x) ^ α) A :=
      (cfc_comp_const_mul c (fun x : ℝ => x ^ α) A
        hcont.continuousOn hA.1).symm
    _ = cfc (fun x : ℝ => c ^ α * x ^ α) A := by
      apply cfc_congr
      intro x hx
      rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact Real.mul_rpow hc (hA.eigenvalues_nonneg i)
    _ = (c ^ α) • cfc (fun x : ℝ => x ^ α) A :=
      cfc_const_mul (c ^ α) (fun x : ℝ => x ^ α) A hcont.continuousOn
    _ = (c ^ α) • CFC.rpow A α := by
      exact congrArg (fun X : Matrix I I ℂ => (c ^ α) • X)
        (CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := A) (y := α) hA.nonneg).symm

theorem trace_rpow_smul_nonneg {A : Matrix I I ℂ} (hA : A.PosSemidef)
    {c α : ℝ} (hc : 0 ≤ c) (hα : 1 ≤ α) :
    (CFC.rpow (c • A) α).trace.re = c ^ α * (CFC.rpow A α).trace.re := by
  rw [rpow_smul_nonneg hA hc hα]
  rw [Matrix.trace_smul]
  exact RCLike.smul_re (c ^ α) (CFC.rpow A α).trace

theorem trace_rpow_mono_of_posSemidef_sub {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : (B - A).PosSemidef)
    {α : ℝ} (hα : 1 ≤ α) :
    (CFC.rpow A α).trace.re ≤ (CFC.rpow B α).trace.re := by
  let U : Matrix.unitaryGroup I ℂ := hA.1.eigenvectorUnitary
  let Y : Matrix I I ℂ := (U : Matrix I I ℂ)ᴴ * B * (U : Matrix I I ℂ)
  have hY : Y.PosSemidef := hB.conjTranspose_mul_mul_same (U : Matrix I I ℂ)
  have hD : (U : Matrix I I ℂ)ᴴ * A * (U : Matrix I I ℂ) =
      Matrix.diagonal (fun i => (hA.1.eigenvalues i : ℂ)) := by
    simpa only [U, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      hA.1.conjStarAlgAut_star_eigenvectorUnitary
  have hgap : (Y - Matrix.diagonal (fun i => (hA.1.eigenvalues i : ℂ))).PosSemidef := by
    have h := hAB.conjTranspose_mul_mul_same (U : Matrix I I ℂ)
    rw [Matrix.mul_sub, Matrix.sub_mul, hD] at h
    exact h
  have hdiag (i : I) : hA.1.eigenvalues i ≤ (Y i i).re := by
    have h := (Complex.nonneg_iff.mp (hgap.diag_nonneg (i := i))).1
    simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq,
      Complex.sub_re, Complex.ofReal_re] at h
    linarith
  have hp : 0 ≤ α := le_trans (by norm_num : (0 : ℝ) ≤ 1) hα
  have hleft : ((U : Matrix I I ℂ)ᴴ)ᴴ * (U : Matrix I I ℂ)ᴴ ≤ 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact le_of_eq (Unitary.coe_mul_star_self U)
  have hright : (U : Matrix I I ℂ)ᴴ * ((U : Matrix I I ℂ)ᴴ)ᴴ ≤ 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact le_of_eq (Unitary.coe_star_mul_self U)
  calc
    (CFC.rpow A α).trace.re = ∑ i, (hA.1.eigenvalues i) ^ α :=
      TracePower.trace_rpow_eq_sum hA α
    _ ≤ ∑ i, (Y i i).re ^ α :=
      Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (hA.eigenvalues_nonneg i) (hdiag i) hp)
    _ ≤ (CFC.rpow Y α).trace.re :=
      PositiveTrace.diagonal_rpow_sum_le_trace hY hα
    _ ≤ (CFC.rpow B α).trace.re := by
      simpa only [Y, Matrix.conjTranspose_conjTranspose] using
        (TracePower.trace_rpow_contraction (C := (U : Matrix I I ℂ)ᴴ) hB hleft hright hα)

theorem trace_rpow_mono {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : A ≤ B)
    {α : ℝ} (hα : 1 ≤ α) :
    (CFC.rpow A α).trace.re ≤ (CFC.rpow B α).trace.re :=
  trace_rpow_mono_of_posSemidef_sub hA hB (Matrix.le_iff.mp hAB) hα

end QuantumProver.MatrixTracePower
