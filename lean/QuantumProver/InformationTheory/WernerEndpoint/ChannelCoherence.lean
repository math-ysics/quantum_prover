import QuantumProver.InformationTheory.WernerEndpoint.PhaseCoherence

noncomputable section

namespace QuantumProver.WernerEndpoint

open scoped BigOperators
open Matrix

variable {I B E : Type*} [Fintype I] [Fintype B] [Fintype E]

theorem vectorNormSq_smul (u : I → ℂ) (z : ℂ) :
    vectorNormSq (z • u) = Complex.normSq z * vectorNormSq u := by
  simp [vectorNormSq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]

theorem vectorNormSq_add_unit_phase (u v : I → ℂ) (z : ℂ) (hz : ‖z‖ = 1)
    (huv : ∑ i, u i * star (v i) = 0) :
    vectorNormSq (u + z • v) = vectorNormSq u + vectorNormSq v := by
  have hnz : Complex.normSq z = 1 := by rw [← Complex.sq_norm, hz]; norm_num
  have hc : (∑ i, (u i * star (z * v i)).re) = 0 := by
    rw [← Complex.re_sum]
    have heq : (∑ i, u i * star (z * v i)) =
        star z * (∑ i, u i * star (v i)) := by
      simp [star_mul, Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc]
    rw [heq, huv]
    simp
  calc
    vectorNormSq (u + z • v) =
        ∑ i, (Complex.normSq (u i) + Complex.normSq (v i) +
          2 * (u i * star (z * v i)).re) := by
      unfold vectorNormSq
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Complex.normSq_add, Complex.normSq_mul, hnz, one_mul, Complex.star_def]
    _ = vectorNormSq u + vectorNormSq v +
        2 * (∑ i, (u i * star (z * v i)).re) := by
      simp only [vectorNormSq, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by rw [hc]; ring

theorem phaseScale_normSq : Complex.normSq wedgeScale = (1 : ℝ) / 2 := by
  simp only [wedgeScale, Complex.normSq_ofReal]
  rw [← _root_.mul_inv_rev, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem reducedLeft_smul (U : Matrix B E ℂ) (z : ℂ) :
    reducedLeft (z • U) = (Complex.normSq z : ℂ) • reducedLeft U := by
  unfold reducedLeft
  rw [crossLeft_smul_left, crossLeft_smul_right, smul_smul]
  have h : z * star z = (Complex.normSq z : ℂ) := by
    simpa only [Complex.star_def] using Complex.mul_conj z
  rw [h]

theorem purity_real_smul (R : Matrix I I ℂ) (t : ℝ) :
    purity ((t : ℂ) • R) = t ^ 2 * purity R := by
  unfold purity
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul,
    smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero]
  ring

namespace Stinespring

variable [DecidableEq I]

theorem orthogonal_transition_coherence (N : Stinespring I B E) (β : ℝ)
    (hbound : ∀ w : I → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (u v : I → ℂ) (hu : vectorNormSq u = 1) (hv : vectorNormSq v = 1)
    (huv : ∑ i, u i * star (v i) = 0) :
    ‖Matrix.trace (N.apply (crossDensity v u) * N.apply (crossDensity v u))‖ ≤ β / 2 := by
  rw [N.apply_crossDensity]
  apply coherence_norm_le_half_of_balanced (N.amplitudes u) (N.amplitudes v) β
  intro z hz
  have hsup (a : ℂ) (ha : ‖a‖ = 1) :
      purity (reducedLeft (N.amplitudes u + a • N.amplitudes v)) ≤ 4 * β := by
    have hunit : vectorNormSq (wedgeScale • (u + a • v)) = 1 := by
      rw [vectorNormSq_smul, phaseScale_normSq, vectorNormSq_add_unit_phase u v a ha huv,
        hu, hv]
      norm_num
    have h := hbound (wedgeScale • (u + a • v)) hunit
    rw [N.apply_pureDensity, N.amplitudes_smul, reducedLeft_smul,
      phaseScale_normSq, purity_real_smul, N.amplitudes_add, N.amplitudes_smul] at h
    norm_num at h
    linarith
  have hp := hsup z hz
  have hm := hsup (-z) (by simpa using hz)
  simp only [neg_smul, ← sub_eq_add_neg] at hm
  linarith

end Stinespring
end QuantumProver.WernerEndpoint
