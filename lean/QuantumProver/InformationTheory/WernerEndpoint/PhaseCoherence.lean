import QuantumProver.InformationTheory.WernerEndpoint.PurityBounds

noncomputable section

namespace QuantumProver.WernerEndpoint

open scoped BigOperators
open Matrix

variable {B E I : Type*} [Fintype B] [Fintype E] [Fintype I]

theorem crossLeft_add_left (U W Z : Matrix B E ℂ) :
    crossLeft (U + W) Z = crossLeft U Z + crossLeft W Z := by
  ext b c
  simp [crossLeft, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem crossLeft_add_right (U W Z : Matrix B E ℂ) :
    crossLeft U (W + Z) = crossLeft U W + crossLeft U Z := by
  ext b c
  simp [crossLeft, Matrix.add_apply, star_add, mul_add, Finset.sum_add_distrib]

theorem crossLeft_smul_left (U W : Matrix B E ℂ) (z : ℂ) :
    crossLeft (z • U) W = z • crossLeft U W := by
  ext b c
  simp [crossLeft, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem crossLeft_smul_right (U W : Matrix B E ℂ) (z : ℂ) :
    crossLeft U (z • W) = star z • crossLeft U W := by
  ext b c
  simp [crossLeft, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

def phaseCross (U W : Matrix B E ℂ) (z : ℂ) : Matrix B B ℂ :=
  z • crossLeft W U + star z • crossLeft U W

theorem phase_mul_star_eq_one (z : ℂ) (hz : ‖z‖ = 1) : z * star z = 1 := by
  simpa [← Complex.sq_norm, hz] using Complex.mul_conj z

theorem reducedLeft_add_unit_phase (U W : Matrix B E ℂ) (z : ℂ) (hz : ‖z‖ = 1) :
    reducedLeft (U + z • W) = reducedLeft U + reducedLeft W + phaseCross U W z := by
  unfold reducedLeft
  rw [crossLeft_add_left, crossLeft_add_right, crossLeft_add_right,
    crossLeft_smul_left, crossLeft_smul_left, crossLeft_smul_right, crossLeft_smul_right]
  rw [smul_smul, phase_mul_star_eq_one z hz, one_smul]
  unfold phaseCross
  abel

theorem reducedLeft_sub_unit_phase (U W : Matrix B E ℂ) (z : ℂ) (hz : ‖z‖ = 1) :
    reducedLeft (U - z • W) = reducedLeft U + reducedLeft W - phaseCross U W z := by
  have h := reducedLeft_add_unit_phase U W (-z) (by simpa using hz)
  calc
    reducedLeft (U - z • W) = reducedLeft U + reducedLeft W + phaseCross U W (-z) := by
      simpa only [neg_smul, sub_eq_add_neg] using h
    _ = reducedLeft U + reducedLeft W - phaseCross U W z := by
      simp only [phaseCross, star_neg, neg_smul]
      abel

theorem purity_opposite_sum (R T : Matrix I I ℂ) :
    purity (R + T) + purity (R - T) = 2 * purity R + 2 * purity T := by
  rw [purity_add, purity_sub]
  ring

theorem trace_cross_reverse_square (U W : Matrix B E ℂ) :
    Matrix.trace (crossLeft U W * crossLeft U W) =
      star (Matrix.trace (crossLeft W U * crossLeft W U)) := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    crossLeft_conjTranspose]

theorem trace_cross_reverse_product (U W : Matrix B E ℂ) :
    Matrix.trace (crossLeft U W * crossLeft W U) =
      ((hsNormSq (crossLeft W U) : ℝ) : ℂ) := by
  rw [← crossLeft_conjTranspose W U]
  rw [Matrix.trace_mul_comm]
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    exact (hsNormSq_eq_trace _).symm
  · simp only [Complex.ofReal_im]
    have h : star (Matrix.trace (crossLeft W U * (crossLeft W U)ᴴ)) =
        Matrix.trace (crossLeft W U * (crossLeft W U)ᴴ) := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    have him := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at him
    linarith

theorem balanced_phase_identity (U W : Matrix B E ℂ) (z : ℂ) (hz : ‖z‖ = 1) :
    purity (reducedLeft (U + z • W)) + purity (reducedLeft (U - z • W)) =
      2 * purity (reducedLeft U) + 2 * purity (reducedLeft W) +
      4 * (Matrix.trace (reducedLeft U * reducedLeft W)).re +
      4 * (Matrix.trace (reducedRight U * reducedRight W)).re +
      4 * (z ^ 2 * Matrix.trace (crossLeft W U * crossLeft W U)).re := by
  rw [reducedLeft_add_unit_phase U W z hz, reducedLeft_sub_unit_phase U W z hz,
    purity_opposite_sum, purity_add]
  have hphase : purity (phaseCross U W z) =
      2 * (Matrix.trace (reducedRight U * reducedRight W)).re +
        2 * (z ^ 2 * Matrix.trace (crossLeft W U * crossLeft W U)).re := by
    unfold purity phaseCross
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    rw [trace_cross_reverse_square U W, trace_cross_reverse_product U W,
      Matrix.trace_mul_comm (crossLeft W U) (crossLeft U W),
      trace_cross_reverse_product U W]
    have hpoly (b t : ℂ) :
        z * (z * b + star z * t) + star z * (z * t + star z * star b) =
          z ^ 2 * b + star (z ^ 2 * b) + 2 * t := by
      rw [star_mul, star_pow]
      calc
        _ = z ^ 2 * b + star z ^ 2 * star b + 2 * (z * star z) * t := by ring
        _ = _ := by rw [phase_mul_star_eq_one z hz]; ring
    rw [hpoly]
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
    norm_num
    rw [crossLeft_hsNormSq W U, Matrix.trace_mul_comm (reducedRight W) (reducedRight U)]
    ring
  rw [hphase]
  ring

theorem exists_coherence_phase (b : ℂ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (z ^ 2 * b).re = ‖b‖ := by
  by_cases hb : b = 0
  · subst b
    exact ⟨1, by simp, by simp⟩
  have hbn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hbr : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hbn
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (star b / (‖b‖ : ℂ)) (by norm_num : 0 < 2)
  have hzn : ‖z‖ = 1 := by
    have hnorm := congrArg norm hz
    simp only [norm_pow, norm_div, norm_star, Complex.norm_real,
      Real.norm_eq_abs, abs_norm] at hnorm
    rw [div_self hbn] at hnorm
    nlinarith [norm_nonneg z]
  refine ⟨z, hzn, ?_⟩
  rw [hz]
  have hmul : star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    simpa [mul_comm, ← Complex.sq_norm] using Complex.mul_conj b
  have heq : star b / (‖b‖ : ℂ) * b = (‖b‖ : ℂ) := by
    calc
      _ = (star b * b) / (‖b‖ : ℂ) := by ring
      _ = ((‖b‖ ^ 2 : ℝ) : ℂ) / (‖b‖ : ℂ) := by rw [hmul]
      _ = _ := by push_cast; field_simp
  rw [heq]
  rfl

theorem coherence_norm_le_half_of_balanced (U W : Matrix B E ℂ) (β : ℝ)
    (hphase : ∀ z : ℂ, ‖z‖ = 1 →
      purity (reducedLeft (U + z • W)) + purity (reducedLeft (U - z • W)) ≤ 8 * β) :
    ‖Matrix.trace (crossLeft W U * crossLeft W U)‖ ≤ β / 2 := by
  obtain ⟨z, hz, hb⟩ := exists_coherence_phase
    (Matrix.trace (crossLeft W U * crossLeft W U))
  have h := hphase z hz
  rw [balanced_phase_identity U W z hz, hb] at h
  have ho := transition_norm_le_output_overlap W U
  have hx := transition_norm_le_complement_overlap W U
  rw [Matrix.trace_mul_comm (reducedLeft W) (reducedLeft U)] at ho
  rw [Matrix.trace_mul_comm (reducedRight W) (reducedRight U)] at hx
  have hpq := twice_overlap_le_purities U W
  linarith

end QuantumProver.WernerEndpoint
