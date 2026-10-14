import QuantumProver.InformationTheory.Equipartition.TestingBounds
import QuantumProver.InformationTheory.Equipartition.PolarBounds
import QuantumProver.LinearAlgebra.SandwichedDPI.Interpolation
import QuantumProver.LinearAlgebra.ArakiLiebThirringTrace
import QuantumProver.LinearAlgebra.SchattenHolder

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QuantumProver.RenyiStateComparison

open QuantumProver.Equipartition.FiniteModel
open QuantumProver.Equipartition.FiniteModel.Testing

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem matrixRpow_posSemidef {A : CMat I} (hA : A.PosSemidef) (r : ℝ) :
    (matrixRpow A r).PosSemidef := by
  rw [matrixRpow_eq_cfc_rpow hA]
  exact (CFC.rpow_nonneg : 0 ≤ CFC.rpow A r).posSemidef

theorem matrixRpow_comp {A : CMat I} (hA : A.PosSemidef) (r s : ℝ) :
    matrixRpow (matrixRpow A r) s = matrixRpow A (r * s) := by
  unfold matrixRpow
  rw [← cfc_comp (p := IsSelfAdjoint) (fun x : ℝ => Real.rpow x s)
    (fun x : ℝ => Real.rpow x r) A hA.1
    ((A.finite_real_spectrum.image _).continuousOn _)
    (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro x hx
  obtain ⟨i, rfl⟩ := hA.1.spectrum_real_eq_range_eigenvalues ▸ hx
  exact (Real.rpow_mul (hA.eigenvalues_nonneg i) r s).symm

theorem matrixRpow_mul {A : CMat I} (hA : A.PosSemidef) {r s : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r + s ≠ 0) :
    matrixRpow A r * matrixRpow A s = matrixRpow A (r + s) := by
  unfold matrixRpow
  rw [← cfc_mul (p := IsSelfAdjoint) _ _ A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro x hx
  obtain ⟨i, rfl⟩ := hA.1.spectrum_real_eq_range_eigenvalues ▸ hx
  by_cases hz : hA.1.eigenvalues i = 0
  · simp [hz, Real.zero_rpow hr, Real.zero_rpow hs, Real.zero_rpow hrs]
  · exact (Real.rpow_add (lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm hz)) r s).symm

theorem matrixRpow_one {A : CMat I} (hA : A.PosSemidef) :
    matrixRpow A 1 = A := by
  rw [matrixRpow_eq_cfc_rpow hA]
  exact CFC.rpow_one A hA.nonneg

theorem state_ne_zero {ρ : CMat I} (hρ : IsState ρ) : ρ ≠ 0 := by
  intro hz
  have htr := hρ.2
  rw [hz, Matrix.trace_zero] at htr
  exact zero_ne_one htr

theorem alternative_trace_pos {ρ σ : CMat I} (hρ : IsState ρ)
    (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) : 0 < σ.trace.re := by
  have hσzero : σ ≠ 0 := by
    intro hz
    have hρzero : ρ = 0 := by
      apply Matrix.ext_iff_mulVec.mpr
      intro v
      have hv : ρ *ᵥ v = 0 := hs v (by simp [hz])
      simpa only [Matrix.zero_mulVec] using hv
    exact state_ne_zero hρ hρzero
  have hnonneg := Complex.nonneg_iff.mp hσ.trace_nonneg
  apply lt_of_le_of_ne hnonneg.1
  intro hz
  have htrace : σ.trace = 0 := by
    apply Complex.ext
    · exact hz.symm
    · simpa only [Complex.zero_im] using hnonneg.2.symm
  exact hσzero (hσ.trace_eq_zero_iff.mp htrace)

theorem sandwichedMatrix_posSemidef {ρ σ : CMat I}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) :
    (matrixRpow σ ((1 - α) / (2 * α)) * ρ *
      matrixRpow σ ((1 - α) / (2 * α))).PosSemidef := by
  have hS := (matrixRpow_posSemidef hσ ((1 - α) / (2 * α))).1
  simpa only [hS.eq] using
    hρ.conjTranspose_mul_mul_same (matrixRpow σ ((1 - α) / (2 * α)))

theorem sandwichedTrace_pos_of_state {ρ σ : CMat I}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) :
    0 < sandwichedTrace ρ σ α := by
  let r : ℝ := (1 - α) / (2 * α)
  have hr : r ≠ 0 := div_ne_zero (sub_ne_zero.mpr hα1.symm) (by positivity)
  have hB := sandwichedMatrix_posSemidef hρ.1 hσ α
  have hBzero : matrixRpow σ r * ρ * matrixRpow σ r ≠ 0 := by
    simp only [matrixRpow_eq_cfc_rpow hσ]
    exact QuantumProver.SandwichedDPI.rpow_supported_sandwich_ne_zero
      hρ.1 hσ ((QuantumProver.SandwichedDPI.supportLE_iff_kernel hρ.1.1 hσ.1).mpr hs)
      (state_ne_zero hρ) hr
  have hP := matrixRpow_posSemidef hB α
  have hn := (Complex.nonneg_iff.mp hP.trace_nonneg).1
  apply lt_of_le_of_ne hn
  intro hz
  have hz' : (CFC.rpow (matrixRpow σ r * ρ * matrixRpow σ r) α).trace.re = 0 := by
    rw [← matrixRpow_eq_cfc_rpow hB]
    exact hz.symm
  exact hBzero ((QuantumProver.SandwichedDPI.trace_rpow_re_eq_zero_iff hB hα).mp hz')

theorem sandwichedDivergence_of_support {ρ σ : CMat I}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) :
    sandwichedDivergence ρ σ α =
      (logTwo (sandwichedTrace ρ σ α) / (α - 1) : EReal) := by
  have hp := sandwichedTrace_pos_of_state hρ hσ hs hα hα1
  simp [sandwichedDivergence, hα1, hs, ne_of_gt hp]

theorem schattenNorm_matrixRpow {A : CMat I} (hA : A.PosSemidef) (p r : ℝ) :
    QuantumProver.SandwichedDPI.schattenNorm p (matrixRpow A r) =
      ((matrixRpow A (r * p)).trace.re) ^ (1 / p : ℝ) := by
  unfold QuantumProver.SandwichedDPI.schattenNorm
  rw [QuantumProver.SandwichedDPI.schattenPower_of_posSemidef p (matrixRpow_posSemidef hA r),
    ← matrixRpow_eq_cfc_rpow (matrixRpow_posSemidef hA r), matrixRpow_comp hA]

theorem schattenPower_sandwichedFactor {ρ σ : CMat I}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {α : ℝ} (hα : 0 < α) :
    QuantumProver.SandwichedDPI.schattenPower (2 * α)
      (matrixRpow ρ (1 / 2 : ℝ) * matrixRpow σ ((1 - α) / (2 * α))) =
      sandwichedTrace ρ σ α := by
  let R := matrixRpow ρ (1 / 2 : ℝ)
  let S := matrixRpow σ ((1 - α) / (2 * α))
  have hR : R.IsHermitian := (matrixRpow_posSemidef hρ _).1
  have hS : S.IsHermitian := (matrixRpow_posSemidef hσ _).1
  have hRR : R * R = ρ := by
    dsimp [R]
    rw [matrixRpow_mul hρ (by norm_num) (by norm_num) (by norm_num)]
    norm_num
    exact matrixRpow_one hρ
  have hGram : (R * S)ᴴ * (R * S) = S * ρ * S := by
    rw [Matrix.conjTranspose_mul, hR.eq, hS.eq]
    calc
      _ = S * (R * R) * S := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hRR]
  rw [QuantumProver.SandwichedDPI.schattenPower_eq_gram_trace (2 * α) (by positivity), hGram]
  have he : 2 * α / 2 = α := by ring
  rw [he, ← matrixRpow_eq_cfc_rpow (sandwichedMatrix_posSemidef hρ hσ α)]
  rfl

theorem schattenNorm_sandwichedFactor {ρ σ : CMat I}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {α : ℝ} (hα : 0 < α) :
    QuantumProver.SandwichedDPI.schattenNorm (2 * α)
      (matrixRpow ρ (1 / 2 : ℝ) * matrixRpow σ ((1 - α) / (2 * α))) =
      sandwichedTrace ρ σ α ^ (1 / (2 * α) : ℝ) := by
  unfold QuantumProver.SandwichedDPI.schattenNorm
  rw [schattenPower_sandwichedFactor hρ hσ hα]

theorem schattenNorm_petzFactor {ρ σ : CMat I}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    QuantumProver.SandwichedDPI.schattenNorm 2
      (matrixRpow ρ (α / 2) * matrixRpow σ ((1 - α) / 2)) =
      petzTrace ρ σ α ^ (1 / 2 : ℝ) := by
  let R := matrixRpow ρ (α / 2)
  let S := matrixRpow σ ((1 - α) / 2)
  have hR : R.IsHermitian := (matrixRpow_posSemidef hρ _).1
  have hS : S.IsHermitian := (matrixRpow_posSemidef hσ _).1
  have hRR : R * R = matrixRpow ρ α := by
    dsimp only [R]
    rw [matrixRpow_mul hρ (ne_of_gt (by positivity : 0 < α / 2))
      (ne_of_gt (by positivity : 0 < α / 2)) (ne_of_gt (by positivity : 0 < α / 2 + α / 2))]
    congr 1
    ring
  have hSS : S * S = matrixRpow σ (1 - α) := by
    dsimp only [S]
    have hs : 0 < (1 - α) / 2 := by positivity
    rw [matrixRpow_mul hσ hs.ne' hs.ne' (add_pos hs hs).ne']
    congr 1
    ring
  have hGram : (R * S)ᴴ * (R * S) = S * matrixRpow ρ α * S := by
    rw [Matrix.conjTranspose_mul, hR.eq, hS.eq]
    calc
      _ = S * (R * R) * S := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hRR]
  unfold QuantumProver.SandwichedDPI.schattenNorm
  rw [QuantumProver.SandwichedDPI.schattenPower_eq_gram_trace 2 (by norm_num),
    show (2 : ℝ) / 2 = 1 by norm_num]
  simp only [CFC.rpow_eq_pow]
  rw [CFC.rpow_one _ (Matrix.posSemidef_conjTranspose_mul_self (R * S)).nonneg,
    hGram, Matrix.trace_mul_cycle, hSS, Matrix.trace_mul_comm]
  rfl

theorem schattenNorm_densityFactor {ρ : CMat I} (hρ : IsState ρ)
    {α : ℝ} (hα1 : α < 1) :
    QuantumProver.SandwichedDPI.schattenNorm (2 / (1 - α))
      (matrixRpow ρ ((1 - α) / 2)) = 1 := by
  rw [schattenNorm_matrixRpow hρ.1]
  have he : (1 - α) / 2 * (2 / (1 - α)) = (1 : ℝ) := by
    field_simp [(sub_pos.mpr hα1).ne']
  rw [he, matrixRpow_one hρ.1, hρ.trace_real, Real.one_rpow]

theorem schattenNorm_scaleFactor {σ : CMat I} (hσ : σ.PosSemidef)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    QuantumProver.SandwichedDPI.schattenNorm (2 * α / (1 - α) ^ (2 : ℕ))
      (matrixRpow σ ((1 - α) ^ (2 : ℕ) / (2 * α))) =
      σ.trace.re ^ ((1 - α) ^ (2 : ℕ) / (2 * α)) := by
  rw [schattenNorm_matrixRpow hσ]
  have hβ : 1 - α ≠ 0 := (sub_pos.mpr hα1).ne'
  have he : (1 - α) ^ (2 : ℕ) / (2 * α) *
      (2 * α / (1 - α) ^ (2 : ℕ)) = (1 : ℝ) := by
    field_simp [hβ, hα0.ne']
  have hinv : (1 / (2 * α / (1 - α) ^ (2 : ℕ)) : ℝ) =
      (1 - α) ^ (2 : ℕ) / (2 * α) := by
    field_simp [hβ, hα0.ne']
  rw [he, matrixRpow_one hσ, hinv]

theorem belowOne_left_factorization {ρ σ : CMat I}
    (hρ : ρ.PosSemidef) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    matrixRpow ρ ((1 - α) / 2) *
      (matrixRpow ρ (α / 2) * matrixRpow σ ((1 - α) / 2)) =
      matrixRpow ρ (1 / 2 : ℝ) * matrixRpow σ ((1 - α) / 2) := by
  rw [← Matrix.mul_assoc, matrixRpow_mul hρ
    (ne_of_gt (by positivity : 0 < (1 - α) / 2))
    (ne_of_gt (by positivity : 0 < α / 2))
    (ne_of_gt (by positivity : 0 < (1 - α) / 2 + α / 2))]
  congr 1
  congr 1
  ring

theorem belowOne_factorization {ρ σ : CMat I}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (matrixRpow ρ ((1 - α) / 2) *
      (matrixRpow ρ (α / 2) * matrixRpow σ ((1 - α) / 2))) *
      matrixRpow σ ((1 - α) ^ (2 : ℕ) / (2 * α)) =
      matrixRpow ρ (1 / 2 : ℝ) * matrixRpow σ ((1 - α) / (2 * α)) := by
  rw [belowOne_left_factorization hρ hα0 hα1, Matrix.mul_assoc]
  have hs : 0 < (1 - α) / 2 := by positivity
  have ht : 0 < (1 - α) ^ (2 : ℕ) / (2 * α) := by positivity
  rw [matrixRpow_mul hσ hs.ne' ht.ne' (add_pos hs ht).ne']
  congr 1
  congr 1
  field_simp [hα0.ne']
  <;> ring

theorem belowOne_log_comparison {a b T α : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hT : 0 < T) (hα0 : 0 < α) (hα1 : α < 1)
    (h : a ≤ b ^ α * T ^ ((1 - α) ^ (2 : ℕ))) :
    α * (logTwo b / (α - 1)) - (1 - α) * logTwo T ≤
      logTwo a / (α - 1) := by
  have hp : 0 < b ^ α := Real.rpow_pos_of_pos hb α
  have hq : 0 < T ^ ((1 - α) ^ (2 : ℕ)) := Real.rpow_pos_of_pos hT _
  have hl := logTwo_mono_pos ha h
  rw [logTwo_mul_pos hp hq, logTwo_rpow_pos hb, logTwo_rpow_pos hT] at hl
  have hneg : α - 1 < 0 := sub_neg.mpr hα1
  apply (le_div_iff_of_neg hneg).mpr
  have he : (α * (logTwo b / (α - 1)) - (1 - α) * logTwo T) * (α - 1) =
      α * logTwo b + (1 - α) ^ (2 : ℕ) * logTwo T := by
    field_simp [hneg.ne]
    <;> ring
  rw [he]
  exact hl

theorem sandwichedTrace_le_petzTrace_above_one {ρ σ : CMat I}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {α : ℝ} (hα : 1 < α) :
    sandwichedTrace ρ σ α ≤ petzTrace ρ σ α := by
  let r : ℝ := (1 - α) / (2 * α)
  let S := matrixRpow σ r
  have hS : S.PosSemidef := matrixRpow_posSemidef hσ r
  have hB : (S * ρ * S).PosSemidef := by
    simpa only [hS.1.eq] using hρ.conjTranspose_mul_mul_same S
  have h := QuantumProver.ArakiLiebThirringTrace.trace_rpow_sandwich_le hρ hS hα
  rw [← matrixRpow_eq_cfc_rpow hB, ← matrixRpow_eq_cfc_rpow hρ,
    ← matrixRpow_eq_cfc_rpow hS] at h
  have hPower : matrixRpow S (2 * α) = matrixRpow σ (1 - α) := by
    dsimp only [S]
    rw [matrixRpow_comp hσ]
    have he : r * (2 * α) = 1 - α := by
      dsimp [r]
      field_simp [ne_of_gt (lt_trans zero_lt_one hα)]
    rw [he]
  rw [hPower] at h
  exact h

theorem sandwichedDivergence_le_petz_of_gt_one {ρ σ : CMat I}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 1 < α) :
    sandwichedDivergence ρ σ α ≤ petzDivergence ρ σ α := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  rw [sandwichedDivergence_of_support hρ hσ hs hα0 (ne_of_gt hα),
    petzDivergence_of_support ρ σ hρ hσ hs hα0 (ne_of_gt hα)]
  apply EReal.coe_le_coe
  exact div_le_div_of_nonneg_right
    (logTwo_mono_pos (sandwichedTrace_pos_of_state hρ hσ hs hα0 (ne_of_gt hα))
      (sandwichedTrace_le_petzTrace_above_one hρ.1 hσ hα)) (sub_pos.mpr hα).le

theorem sandwichedDivergence_above_one_le_petz {ρ σ : CMat I}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {δ : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1 / 2) :
    sandwichedDivergence ρ σ (1 + δ) ≤ petzDivergence ρ σ (1 + δ) :=
  sandwichedDivergence_le_petz_of_gt_one hρ hσ hs (by linarith)

theorem sandwichedReal_above_one_le_petz {ρ σ : CMat I}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {δ : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1 / 2) :
    logTwo (sandwichedTrace ρ σ (1 + δ)) / δ ≤
      logTwo (petzTrace ρ σ (1 + δ)) / δ := by
  have hα : 1 < 1 + δ := by linarith
  exact div_le_div_of_nonneg_right
    (logTwo_mono_pos
      (sandwichedTrace_pos_of_state hρ hσ hs (by linarith : 0 < 1 + δ) (ne_of_gt hα))
      (sandwichedTrace_le_petzTrace_above_one hρ.1 hσ hα)) hδ0.le

theorem sandwichedTrace_le_petzTrace_scaled_below_one {ρ σ : CMat I}
    (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {α : ℝ} (hαhalf : 1 / 2 ≤ α) (hα1 : α < 1) :
    sandwichedTrace ρ σ α ≤ petzTrace ρ σ α ^ α *
      σ.trace.re ^ ((1 - α) ^ (2 : ℕ)) := by
  have hα0 : 0 < α := by linarith
  have hβ : 0 < 1 - α := sub_pos.mpr hα1
  have htden : 0 < 2 - α := by linarith
  let t : ℝ := 2 / (2 - α)
  let q : ℝ := 2 / (1 - α)
  let w : ℝ := 2 * α / (1 - α) ^ (2 : ℕ)
  have ht : 1 < t := by
    dsimp only [t]
    apply (lt_div_iff₀ htden).mpr
    linarith
  have hq : 1 < q := by
    dsimp only [q]
    apply (lt_div_iff₀ hβ).mpr
    linarith
  have hw : 1 < w := by
    dsimp only [w]
    apply (lt_div_iff₀ (sq_pos_of_pos hβ)).mpr
    nlinarith [mul_nonneg hα0.le hβ.le]
  have hp : 1 ≤ 2 * α := by linarith
  have hexp1 : 1 / t = 1 / q + 1 / (2 : ℝ) := by
    dsimp only [t, q]
    field_simp [hβ.ne', htden.ne']
    <;> ring
  have hexp2 : 1 / (2 * α) = 1 / t + 1 / w := by
    dsimp only [t, w]
    field_simp [hα0.ne', hβ.ne', htden.ne']
    <;> ring
  let U := matrixRpow ρ ((1 - α) / 2)
  let V := matrixRpow ρ (α / 2) * matrixRpow σ ((1 - α) / 2)
  let W := matrixRpow σ ((1 - α) ^ (2 : ℕ) / (2 * α))
  have hU : QuantumProver.SandwichedDPI.schattenNorm q U = 1 :=
    schattenNorm_densityFactor hρ hα1
  have hV : QuantumProver.SandwichedDPI.schattenNorm 2 V = petzTrace ρ σ α ^ (1 / 2 : ℝ) :=
    schattenNorm_petzFactor hρ.1 hσ hα0 hα1
  have hW : QuantumProver.SandwichedDPI.schattenNorm w W =
      σ.trace.re ^ ((1 - α) ^ (2 : ℕ) / (2 * α)) :=
    schattenNorm_scaleFactor hσ hα0 hα1
  have hFirst := QuantumProver.SandwichedDPI.schattenNorm_mul_le t q 2 U V ht.le hq (by norm_num) hexp1
  rw [hU, hV, one_mul] at hFirst
  have hSecond := QuantumProver.SandwichedDPI.schattenNorm_mul_le (2 * α) t w (U * V) W hp ht hw hexp2
  rw [hW] at hSecond
  have hT : 0 ≤ σ.trace.re := (Complex.nonneg_iff.mp hσ.trace_nonneg).1
  have hQ : 0 ≤ petzTrace ρ σ α :=
    tracePair_nonneg (matrixRpow_posSemidef hρ.1 α) (matrixRpow_posSemidef hσ (1 - α))
  have hBound := hSecond.trans (mul_le_mul_of_nonneg_right hFirst (Real.rpow_nonneg hT _))
  have hFactors : (U * V) * W =
      matrixRpow ρ (1 / 2 : ℝ) * matrixRpow σ ((1 - α) / (2 * α)) :=
    belowOne_factorization hρ.1 hσ hα0 hα1
  rw [hFactors] at hBound
  have hRaised := Real.rpow_le_rpow
    (QuantumProver.SandwichedDPI.schattenNorm_nonneg _ _) hBound (by positivity : 0 ≤ 2 * α)
  rw [QuantumProver.SandwichedDPI.schattenNorm_rpow (2 * α) (by positivity),
    schattenPower_sandwichedFactor hρ.1 hσ hα0] at hRaised
  have hRhs : (petzTrace ρ σ α ^ (1 / 2 : ℝ) *
      σ.trace.re ^ ((1 - α) ^ (2 : ℕ) / (2 * α))) ^ (2 * α) =
      petzTrace ρ σ α ^ α * σ.trace.re ^ ((1 - α) ^ (2 : ℕ)) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hQ _) (Real.rpow_nonneg hT _),
      ← Real.rpow_mul hQ, ← Real.rpow_mul hT]
    congr 1
    · congr 1
      ring
    · congr 1
      field_simp [hα0.ne']
  rwa [hRhs] at hRaised

theorem petzReal_below_one_scale_le_sandwiched {ρ σ : CMat I}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hαhalf : 1 / 2 ≤ α) (hα1 : α < 1) :
    α * (logTwo (petzTrace ρ σ α) / (α - 1)) - (1 - α) * logTwo σ.trace.re ≤
      logTwo (sandwichedTrace ρ σ α) / (α - 1) := by
  have hα0 : 0 < α := by linarith
  exact belowOne_log_comparison
    (sandwichedTrace_pos_of_state hρ hσ hs hα0 (ne_of_lt hα1))
    (petzTrace_pos_of_support ρ σ hρ hσ hs hα0)
    (alternative_trace_pos hρ hσ hs) hα0 hα1
    (sandwichedTrace_le_petzTrace_scaled_below_one hρ hσ hαhalf hα1)

theorem petzDivergence_below_one_scale_le_sandwiched_of_half_le {ρ σ : CMat I}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hαhalf : 1 / 2 ≤ α) (hα1 : α < 1) :
    (α : EReal) * petzDivergence ρ σ α - (((1 - α) * logTwo σ.trace.re : ℝ) : EReal) ≤
      sandwichedDivergence ρ σ α := by
  have hα0 : 0 < α := by linarith
  rw [petzDivergence_of_support ρ σ hρ hσ hs hα0 (ne_of_lt hα1),
    sandwichedDivergence_of_support hρ hσ hs hα0 (ne_of_lt hα1)]
  change (((α * (logTwo (petzTrace ρ σ α) / (α - 1)) -
    (1 - α) * logTwo σ.trace.re) : ℝ) : EReal) ≤
      ((logTwo (sandwichedTrace ρ σ α) / (α - 1) : ℝ) : EReal)
  exact EReal.coe_le_coe (petzReal_below_one_scale_le_sandwiched hρ hσ hs hαhalf hα1)

theorem petzDivergence_below_one_scale_le_sandwiched {ρ σ : CMat I}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ((1 - δ : ℝ) : EReal) * petzDivergence ρ σ (1 - δ) -
      ((δ * logTwo σ.trace.re : ℝ) : EReal) ≤ sandwichedDivergence ρ σ (1 - δ) := by
  have h := petzDivergence_below_one_scale_le_sandwiched_of_half_le hρ hσ hs
    (show (1 / 2 : ℝ) ≤ 1 - δ by linarith) (show 1 - δ < 1 by linarith)
  have he : 1 - (1 - δ) = δ := by ring
  simpa only [he] using h

theorem petzReal_below_one_scale_le_sandwiched_delta {ρ σ : CMat I}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    (1 - δ) * (logTwo (petzTrace ρ σ (1 - δ)) / (-δ)) - δ * logTwo σ.trace.re ≤
      logTwo (sandwichedTrace ρ σ (1 - δ)) / (-δ) := by
  have h := petzReal_below_one_scale_le_sandwiched hρ hσ hs
    (show (1 / 2 : ℝ) ≤ 1 - δ by linarith) (show 1 - δ < 1 by linarith)
  have hβ : 1 - (1 - δ) = δ := by ring
  have hden : 1 - δ - 1 = -δ := by ring
  simpa only [hβ, hden] using h

end QuantumProver.RenyiStateComparison
