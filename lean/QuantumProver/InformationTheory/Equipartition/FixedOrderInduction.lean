import QuantumProver.InformationTheory.Equipartition.TestingBounds
import QuantumProver.InformationTheory.Equipartition.PolarBounds

noncomputable section
open scoped Topology
namespace QuantumProver.Equipartition.FiniteModel.FixedMInduction

def curvatureOrder (zeta : ℝ) (n : ℕ) : ℝ :=
  zeta / ((n : ℝ) * blockLog n * Real.log 2)

def endpointWindow (zeta : ℝ) : ℝ := zeta / (8 * Real.log 2)

def laplaceBudget (A D : ℝ) (M n : ℕ) : ℝ :=
  (A + (M : ℝ) * D * blockLog n) / (n : ℝ)

def curvatureFactor (A D gamma : ℝ) (M n : ℕ) : ℝ :=
  Real.exp (gamma / blockLog n) * (1 + 2 * laplaceBudget A D M n)

theorem blockLog_ge_eight {n : ℕ} (hn : 255 ≤ n) : 8 ≤ blockLog n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnreal : (256 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hn 1
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 256) hnreal
  rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow] at hlog
  unfold blockLog logTwo
  apply (le_div_iff₀ hlog2).mpr
  norm_num at hlog ⊢
  exact hlog

theorem curvatureOrder_in_smaller_window {n : ℕ} (hn : 32 ≤ n)
    {zeta : ℝ} (hzeta : 0 < zeta) :
    0 < curvatureOrder zeta n ∧
      curvatureOrder zeta n * ((n / 16 : ℕ) : ℝ) * blockLog (n / 16) ≤
        endpointWindow zeta := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < blockLog n := lt_of_lt_of_le zero_lt_one (blockLog_ge_one hn1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · unfold curvatureOrder
    positivity
  · have h := shrunk_block_order_window hn hzeta
    have hcoef : zeta / (16 * Real.log 2) ≤ zeta / (8 * Real.log 2) := by
      apply div_le_div_of_nonneg_left hzeta.le (by positivity)
      nlinarith
    exact h.trans hcoef

theorem uniform_curvature_factor {A D gamma : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hgamma : 0 ≤ gamma) (hgammaUpper : gamma ≤ 2 / 75) :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → ∀ n : ℕ, M ^ 2 ≤ n → 1 ≤ n →
      0 ≤ laplaceBudget A D M n ∧
      laplaceBudget A D M n ≤ 1 / (100 * blockLog n) ∧
      curvatureFactor A D gamma M n ≤ 1 + 1 / (4 * blockLog n) := by
  obtain ⟨M0, hsmall⟩ := uniform_endpoint_smallness hA hD
  refine ⟨M0, ?_⟩
  intro M hM n hn hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL : 1 ≤ blockLog n := blockLog_ge_one hn1
  have hLpos : 0 < blockLog n := by linarith
  have ha0 : 0 ≤ laplaceBudget A D M n := by
    unfold laplaceBudget
    positivity
  have habudget := hsmall M hM n hn
  have ha : laplaceBudget A D M n ≤ 1 / (100 * blockLog n) := by
    apply (le_div_iff₀ (by positivity : 0 < 100 * blockLog n)).mpr
    have hid : laplaceBudget A D M n * blockLog n =
        (A * blockLog n + (M : ℝ) * D * (blockLog n) ^ 2) / (n : ℝ) := by
      unfold laplaceBudget
      ring
    have hprod : laplaceBudget A D M n * blockLog n ≤ 1 / 100 := by
      rw [hid]
      exact habudget
    nlinarith
  have he0 : 0 ≤ gamma / blockLog n := div_nonneg hgamma hLpos.le
  have he : gamma / blockLog n ≤ 2 / (75 * blockLog n) := by
    have h := div_le_div_of_nonneg_right hgammaUpper hLpos.le
    convert h using 1 <;> ring
  exact ⟨ha0, ha, endpoint_curvature_factor_bound hL ha0 ha he0 he⟩

theorem exists_single_coefficient {B A D gamma K0 : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hD : 0 ≤ D) (hgamma : 0 ≤ gamma)
    (hgammaUpper : gamma ≤ 2 / 75) (Nstar Nfixed : ℕ) :
    ∃ M : ℕ, 1 ≤ M ∧ 4 * B ^ 2 ≤ (M : ℝ) ∧ K0 ≤ 2 * (M : ℝ) ∧
      32 * Nstar ≤ M ^ 2 ∧ Nfixed ≤ M ^ 2 ∧ 255 ≤ M ^ 2 ∧
      ∀ n : ℕ, M ^ 2 ≤ n → 1 ≤ n →
        0 ≤ laplaceBudget A D M n ∧
        laplaceBudget A D M n ≤ 1 / (100 * blockLog n) ∧
        curvatureFactor A D gamma M n ≤ 1 + 1 / (4 * blockLog n) := by
  obtain ⟨M0, hfactor⟩ := uniform_curvature_factor hA hD hgamma hgammaUpper
  let M := max M0 (max (32 * Nstar + Nfixed + 256)
    (Nat.ceil (max (4 * B ^ 2) (K0 / 2))))
  have hM0 : M0 ≤ M := le_max_left _ _
  have hMfixed : 32 * Nstar + Nfixed + 256 ≤ M :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hMceil : Nat.ceil (max (4 * B ^ 2) (K0 / 2)) ≤ M :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hMr : max (4 * B ^ 2) (K0 / 2) ≤ (M : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hMceil)
  have hM1 : 1 ≤ M := by omega
  have hMself : M ≤ M ^ 2 := by nlinarith
  refine ⟨M, hM1, (le_max_left _ _).trans hMr, ?_, ?_, ?_, ?_, ?_⟩
  · have hK := (le_max_right (4 * B ^ 2) (K0 / 2)).trans hMr
    linarith
  · omega
  · omega
  · omega
  · exact hfactor M hM0

theorem fixed_coefficient_induction
    (loss : ℕ → ℝ → ℝ) {B G A D gamma K0 zeta cStar : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) (hD : 0 ≤ D) (hgamma : 0 ≤ gamma)
    (hgammaUpper : gamma ≤ 2 / 75) (hzeta : 0 < zeta)
    (hcStar : endpointWindow zeta ≤ cStar)
    (Nstar Nfixed : ℕ) (hNstar : 1 ≤ Nstar)
    (hbaseline : ∀ n : ℕ, Nstar ≤ n → ∀ delta : ℝ,
      0 < delta → delta * (n : ℝ) ≤ cStar →
      loss n delta ≤ G * blockLog n +
        (delta * (n : ℝ)) *
          (B * Real.rpow (n : ℝ) (1 / 4 : ℝ) *
            Real.rpow (blockLog n) (3 / 4 : ℝ)))
    (hstep : ∀ M n : ℕ, 1 ≤ M → M ^ 2 < n → Nfixed ≤ n →
      32 * Nstar ≤ n →
      loss (n / 16) (curvatureOrder zeta n) ≤ G * blockLog (n / 16) +
        (curvatureOrder zeta n * ((n / 16 : ℕ) : ℝ)) *
          ((M : ℝ) * (blockLog (n / 16)) ^ 3) →
      ∀ delta : ℝ, 0 < delta →
        delta * (n : ℝ) * blockLog n ≤ endpointWindow zeta →
      loss n delta ≤ G * blockLog n + (delta * (n : ℝ)) *
        (curvatureFactor A D gamma M n * (M : ℝ) * (blockLog (n / 16)) ^ 3 +
          K0 * (blockLog n) ^ 2)) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ n : ℕ, Nstar ≤ n → ∀ delta : ℝ,
      0 < delta → delta * (n : ℝ) * blockLog n ≤ endpointWindow zeta →
      loss n delta ≤ G * blockLog n +
        (delta * (n : ℝ)) * ((M : ℝ) * (blockLog n) ^ 3) := by
  obtain ⟨M, hM1, hMB, hMK, hMstar, hMfixed, hMlog, hfactor⟩ :=
    exists_single_coefficient (K0 := K0) hB hA hD hgamma hgammaUpper Nstar Nfixed
  refine ⟨M, hM1, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn delta hdelta hwindow
    have hn1 : 1 ≤ n := hNstar.trans hn
    have hdn : 0 ≤ delta * (n : ℝ) := by positivity
    by_cases hnbase : n ≤ M ^ 2
    · have hinherited : delta * (n : ℝ) ≤ cStar := by
        have h := mul_le_mul_of_nonneg_left (blockLog_ge_one hn1) hdn
        have hfirst : delta * (n : ℝ) ≤ delta * (n : ℝ) * blockLog n := by
          simpa only [mul_one] using h
        exact hfirst.trans (hwindow.trans hcStar)
      have hbase := hbaseline n hn delta hdelta hinherited
      have hMr : 1 ≤ (M : ℝ) := by exact_mod_cast hM1
      have hnMr : (n : ℝ) ≤ (M : ℝ) ^ 2 + 1 := by
        have h : (n : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hnbase
        linarith
      have habsorb := finite_baseline_absorbed hB hMr hMB hn1 hnMr
      exact hbase.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left habsorb hdn))
    · have hnlarge : M ^ 2 < n := lt_of_not_ge hnbase
      have hn32 : 32 ≤ n := by omega
      have hshrunk := shrunk_block_bounds hn32
      have hmstar : Nstar ≤ n / 16 := by omega
      have hw := curvatureOrder_in_smaller_window hn32 hzeta
      have hsmaller := ih (n / 16) hshrunk.2.1 hmstar
        (curvatureOrder zeta n) hw.1 hw.2
      have hrec := hstep M n hM1 hnlarge (by omega) (by omega)
        hsmaller delta hdelta hwindow
      have hLn : 8 ≤ blockLog n := blockLog_ge_eight (by omega)
      have hfac := (hfactor n hnlarge.le hn1).2.2
      have hclose := logarithmic_coefficient_closure hLn
        (blockLog_nonneg (n / 16)) hshrunk.2.2.2 hfac
        (Nat.cast_nonneg M : 0 ≤ (M : ℝ)) hMK
      exact hrec.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hclose hdn))

end QuantumProver.Equipartition.FiniteModel.FixedMInduction
