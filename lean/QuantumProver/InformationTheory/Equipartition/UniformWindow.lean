import QuantumProver.InformationTheory.Equipartition.EndpointCurvature

noncomputable section
namespace QuantumProver.Equipartition.FiniteModel.NarrowGuard
open FixedMInduction EndpointCurvature

theorem narrowBlockBudget_mono {G zeta : ℝ} (hzeta : 0 < zeta)
    {M M' n : ℕ} (hMM' : M ≤ M') (hn : 32 ≤ n) :
    narrowBlockBudget G M zeta n ≤ narrowBlockBudget G M' zeta n := by
  have hM : (M : ℝ) ≤ (M' : ℝ) := by exact_mod_cast hMM'
  have ho := (curvatureOrder_in_smaller_window hn hzeta).1.le
  have hL : 0 ≤ (blockLog (n / 16)) ^ 3 := by
    exact pow_nonneg (blockLog_nonneg _) _
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hM ho) hL
  have hs := (narrowScale_pos (by omega : 1 ≤ n) hzeta).le
  unfold narrowBlockBudget
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hm)
    (mul_nonneg hs (Nat.cast_nonneg n))

theorem narrowFactor_mono {C G zeta : ℝ} (hzeta : 0 < zeta)
    {M M' n : ℕ} (hMM' : M ≤ M') (hn : 32 ≤ n) :
    narrowFactor C G M zeta n ≤ narrowFactor C G M' zeta n := by
  have hb := narrowBlockBudget_mono (G := G) hzeta hMM' hn
  unfold narrowFactor
  exact mul_le_mul_of_nonneg_left (by linarith)
    (Real.exp_pos _).le

theorem narrowFactor_le_curvatureFactor {C G zeta : ℝ}
    (hG : 0 ≤ G) (hzeta : 0 < zeta) (M : ℕ) {n : ℕ} (hn : 32 ≤ n) :
    narrowFactor C G M zeta n ≤
      curvatureFactor (32 * zeta * G) (zeta ^ 2 / Real.log 2)
        (8 * zeta * (C + 1) / 3) M n := by
  have hb := narrowBlockBudget_le_uniform hG hzeta M hn
  have hprod := mul_le_mul_of_nonneg_left
    (show 1 + 2 * narrowBlockBudget G M zeta n ≤
      1 + 2 * laplaceBudget (32 * zeta * G) (zeta ^ 2 / Real.log 2) M n by
        linarith)
    (Real.exp_pos (8 * zeta * (C + 1) / (3 * blockLog n))).le
  have he : (8 * zeta * (C + 1) / 3) / blockLog n =
      8 * zeta * (C + 1) / (3 * blockLog n) := by ring
  simpa only [narrowFactor, curvatureFactor, he] using hprod

theorem exists_uniform_narrow_guards {C G zeta : ℝ}
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hzeta : 0 < zeta)
    (hsmall : 8 * zeta * (C + 1) / 3 ≤ 2 / 75) :
    ∃ Nfixed : ℕ, 32 ≤ Nfixed ∧ ∀ M n : ℕ, M ^ 2 < n → Nfixed ≤ n →
      narrowBlockBudget G M zeta n ≤ 1 ∧
      narrowFactor C G M zeta n ≤ 2 ∧
      narrowFactor C G M zeta n ≤
        curvatureFactor (32 * zeta * G) (zeta ^ 2 / Real.log 2)
          (8 * zeta * (C + 1) / 3) M n := by
  obtain ⟨M0, hfactor⟩ := uniform_narrowFactor hC hG hzeta hsmall
  let Nfixed := max 32 (M0 ^ 2)
  refine ⟨Nfixed, le_max_left _ _, ?_⟩
  intro M n hnlarge hnfixed
  have hn32 : 32 ≤ n := (le_max_left _ _).trans hnfixed
  have hn0 : M0 ^ 2 ≤ n := (le_max_right _ _).trans hnfixed
  have hmax : (max M M0) ^ 2 ≤ n := by
    rcases le_total M M0 with hMM0 | hM0M
    · simpa only [max_eq_right hMM0] using hn0
    · simpa only [max_eq_left hM0M] using hnlarge.le
  have hf := hfactor (max M M0) (le_max_right _ _) n hmax hn32
  have hb := (narrowBlockBudget_mono hzeta (le_max_left M M0) hn32).trans hf.2.1
  have hH := (narrowFactor_mono (C := C) (G := G) hzeta
    (le_max_left M M0) hn32).trans hf.2.2
  have hL : 1 ≤ blockLog n := blockLog_ge_one (by omega)
  have hb1 : (1 : ℝ) / (100 * blockLog n) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 100 * blockLog n)).mpr
    nlinarith
  have hH2 : 1 + (1 : ℝ) / (4 * blockLog n) ≤ 2 := by
    have hh : (1 : ℝ) / (4 * blockLog n) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < 4 * blockLog n)).mpr
      nlinarith
    linarith
  exact ⟨hb.trans hb1, hH.trans hH2,
    narrowFactor_le_curvatureFactor hG hzeta M hn32⟩

end QuantumProver.Equipartition.FiniteModel.NarrowGuard
