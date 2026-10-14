import Mathlib
import QuantumProver.LinearAlgebra.SandwichedDPI.ComplexPowers
import QuantumProver.LinearAlgebra.SandwichedDPI.Support

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix
  Matrix.Norms.L2Operator

namespace QuantumProver.SandwichedDPI

open QuantumProver.AmplitudeDamping.FiniteModel
open QuantumProver.SuperchannelDiscrimination
open FlaggedStates TensorEntropy OutputSupport InputSupport

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {ρ σ A : Matrix I I ℂ}

theorem complexPower_zero_eq_supportProjection (hσ : σ.PosSemidef) :
    complexPower hσ 0 = supportProjection σ := by
  rw [complexPower_zero_eq_support]
  rfl

theorem rpow_mul_neg_eq_supportProjection (hσ : σ.PosSemidef) {r : ℝ} (hr : r ≠ 0) :
    CFC.rpow σ r * CFC.rpow σ (-r) = supportProjection σ := by
  rw [← complexPower_real hσ hr, ← complexPower_real hσ (neg_ne_zero.mpr hr),
    ← complexPower_add]
  have hzero : (r : ℂ) + ((-r : ℝ) : ℂ) = 0 := by simp
  rw [hzero, complexPower_zero_eq_supportProjection hσ]

theorem rpow_neg_mul_eq_supportProjection (hσ : σ.PosSemidef) {r : ℝ} (hr : r ≠ 0) :
    CFC.rpow σ (-r) * CFC.rpow σ r = supportProjection σ := by
  simpa only [neg_neg] using rpow_mul_neg_eq_supportProjection hσ (neg_ne_zero.mpr hr)

theorem supportProjection_mul_of_supportLE (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : SupportLE ρ σ) : supportProjection σ * ρ = ρ := by
  apply supportProjection_mul_left_of_hasSupportIn hρ.1 hσ.1
  exact (supportLE_iff_kernel hρ.1 hσ.1).mp hs

theorem mul_supportProjection_of_supportLE (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : SupportLE ρ σ) : ρ * supportProjection σ = ρ := by
  apply supportProjection_mul_right_of_hasSupportIn hσ.1
  exact (supportLE_iff_kernel hρ.1 hσ.1).mp hs

theorem rpow_inverse_supported_sandwich (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : SupportLE ρ σ) {r : ℝ} (hr : r ≠ 0) :
    CFC.rpow σ (-r) * (CFC.rpow σ r * ρ * CFC.rpow σ r) * CFC.rpow σ (-r) = ρ := by
  calc
    _ = (CFC.rpow σ (-r) * CFC.rpow σ r) * ρ *
        (CFC.rpow σ r * CFC.rpow σ (-r)) := by simp only [Matrix.mul_assoc]
    _ = supportProjection σ * ρ * supportProjection σ := by
      rw [rpow_neg_mul_eq_supportProjection hσ hr, rpow_mul_neg_eq_supportProjection hσ hr]
    _ = ρ := by
      rw [supportProjection_mul_of_supportLE hρ hσ hs, mul_supportProjection_of_supportLE hρ hσ hs]

theorem rpow_supported_sandwich_ne_zero (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : SupportLE ρ σ) (hρzero : ρ ≠ 0) {r : ℝ} (hr : r ≠ 0) :
    CFC.rpow σ r * ρ * CFC.rpow σ r ≠ 0 := by
  intro hz
  have h := rpow_inverse_supported_sandwich hρ hσ hs hr
  rw [hz, Matrix.mul_zero, Matrix.zero_mul] at h
  exact hρzero h.symm

private theorem trace_rpow_re_pos (hA : A.PosSemidef) (hAzero : A ≠ 0)
    {p : ℝ} (hp : 0 < p) : 0 < (CFC.rpow A p).trace.re := by
  have hP : (CFC.rpow A p).PosSemidef :=
    (CFC.rpow_nonneg : 0 ≤ CFC.rpow A p).posSemidef
  have hnonnegative := Complex.nonneg_iff.mp hP.trace_nonneg
  apply lt_of_le_of_ne hnonnegative.1
  intro hz
  have htrace : (CFC.rpow A p).trace = 0 := by
    apply Complex.ext
    · exact hz.symm
    · simpa only [Complex.zero_im] using hnonnegative.2.symm
  have hpowzero : CFC.rpow A p = 0 := hP.trace_eq_zero_iff.mp htrace
  have hinv : (1 / p : ℝ) ≠ 0 := one_div_ne_zero hp.ne'
  have hback : CFC.rpow (CFC.rpow A p) (1 / p : ℝ) = A := by
    have h : CFC.rpow (CFC.rpow A p) (1 / p : ℝ) =
        CFC.rpow A (p * (1 / p : ℝ)) :=
      CFC.rpow_rpow_of_exponent_nonneg (A := Matrix I I ℂ) A p (1 / p : ℝ)
      hp.le (one_div_pos.mpr hp).le hA.nonneg
    have he : p * (1 / p : ℝ) = 1 := by field_simp [hp.ne']
    rw [he] at h
    exact h.trans (CFC.rpow_one (A := Matrix I I ℂ) A hA.nonneg)
  rw [hpowzero, CFC.zero_rpow hinv] at hback
  exact hAzero hback.symm

theorem sandwichedTrace_pos_of_supportLE (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : SupportLE ρ σ) (hρzero : ρ ≠ 0) {p : ℝ} (hp : 1 < p) :
    0 < sandwichedTrace p ρ σ := by
  let r : ℝ := (1 - p) / (2 * p)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hr : r ≠ 0 := ne_of_lt (div_neg_of_neg_of_pos (sub_neg.mpr hp) (by positivity))
  have hW : (CFC.rpow σ r).IsHermitian :=
    (CFC.rpow_nonneg : 0 ≤ CFC.rpow σ r).posSemidef.1
  have hB : (CFC.rpow σ r * ρ * CFC.rpow σ r).PosSemidef := by
    simpa only [hW.eq] using hρ.conjTranspose_mul_mul_same (CFC.rpow σ r)
  have hBzero := rpow_supported_sandwich_ne_zero hρ hσ hs hρzero hr
  exact trace_rpow_re_pos hB hBzero hp0

end QuantumProver.SandwichedDPI
