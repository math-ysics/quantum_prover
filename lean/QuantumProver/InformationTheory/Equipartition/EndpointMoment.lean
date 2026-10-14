import QuantumProver.InformationTheory.Equipartition.TestingBounds

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace QuantumProver.Equipartition.FiniteModel.EndpointMoment

theorem logarithmic_cube_budget_eventually {A : ℝ} (hA : 0 ≤ A) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      A * (blockLog n) ^ 3 / (n : ℝ) ≤ 1 := by
  let eps : ℝ := 1 / (A + 1)
  have heps : 0 < eps := by dsimp [eps]; positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (blockLog_square_eventually_le_sqrt heps)
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hn1)
  have hL : 1 ≤ blockLog n := blockLog_ge_one hn1
  have hL0 : 0 ≤ blockLog n := hL.trans' (by norm_num)
  have hs := hN n ((le_max_left N 1).trans hn)
  have hfour : (blockLog n) ^ 4 ≤ eps ^ 2 * (n : ℝ) := by
    calc
      (blockLog n) ^ 4 = ((blockLog n) ^ 2) ^ 2 := by ring
      _ ≤ (eps * Real.sqrt (n : ℝ)) ^ 2 :=
        (sq_le_sq₀ (sq_nonneg _) (by positivity)).mpr hs
      _ = eps ^ 2 * (n : ℝ) := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hthree : (blockLog n) ^ 3 ≤ (blockLog n) ^ 4 := by
    calc
      (blockLog n) ^ 3 = (blockLog n) ^ 3 * 1 := (mul_one _).symm
      _ ≤ (blockLog n) ^ 3 * blockLog n :=
        mul_le_mul_of_nonneg_left hL (pow_nonneg hL0 _)
      _ = _ := by ring
  have hcoeff : A * eps ^ 2 ≤ 1 := by
    calc
      A * eps ^ 2 = A / (A + 1) ^ 2 := by
        dsimp [eps]
        rw [div_pow]
        ring
      _ ≤ 1 := (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < A + 1))).mpr
        (by nlinarith)
  apply (div_le_iff₀ hnR).mpr
  calc
    A * (blockLog n) ^ 3 ≤ A * (eps ^ 2 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (hthree.trans hfour) hA
    _ = (A * eps ^ 2) * (n : ℝ) := by ring
    _ ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hcoeff hnR.le

theorem wider_ns_moment_of_logarithmic_laplace
    {C A zeta : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hzeta : 0 < zeta) :
    ∃ cutoff K : ℝ, 0 < cutoff ∧ 0 < K ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
      (ρ σ : CMat ι) (hρ : IsState ρ) (hσ : σ.PosSemidef) (center t : ℝ),
      LoewnerLE ρ ((Real.rpow 2 (C * (n : ℝ))) • σ) →
      -(C * (n : ℝ)) ≤ center → 0 ≤ umegakiReal ρ σ - center →
      0 ≤ t → t ≤ cutoff / (n : ℝ) →
      (nsLaw ρ σ hρ hσ).expect (fun z =>
        Real.exp (-(zeta / (n : ℝ)) * (nsLikelihood ρ σ z - center))) ≤
          Real.exp (A * (blockLog n) ^ 3 / (n : ℝ)) →
      nsWeightedMoment ρ σ center t ≤
        K * ((n : ℝ) * (umegakiReal ρ σ - center) +
          (n : ℝ) * (blockLog n) ^ 3) := by
  let cutoff := min (zeta / 3) (Real.log 2 / 16)
  let B : ℝ := 2 * Real.exp (8 * zeta * (C + 1) / 3) / zeta ^ 2
  let T : ℝ := 128 / (Real.log 2 / 2) ^ 2
  let K : ℝ := B * (3 * A + zeta) + T
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hcutoff : 0 < cutoff := by dsimp [cutoff]; exact lt_min (by positivity) (by positivity)
  have hB : 0 < B := by dsimp [B]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨N, hN1, hN⟩ := logarithmic_cube_budget_eventually hA
  refine ⟨cutoff, K, hcutoff, hK, N, hN1, ?_⟩
  intro n hn ι _ _ ρ σ hρ hσ center t hdom hcenter hmean ht hwindow hlap
  have hn1 : 1 ≤ n := hN1.trans hn
  have hn1R : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnR : 0 < (n : ℝ) := by linarith
  have ht0 : 0 < zeta / (n : ℝ) := div_pos hzeta hnR
  have ht3 : t ≤ (zeta / (n : ℝ)) / 3 := by
    calc
      t ≤ cutoff / (n : ℝ) := hwindow
      _ ≤ (zeta / 3) / (n : ℝ) :=
        div_le_div_of_nonneg_right (min_le_left _ _) hnR.le
      _ = _ := by ring
  have htBeta : t ≤ Real.log 2 / 16 := by
    apply hwindow.trans
    apply (div_le_iff₀ hnR).mpr
    have hprod := mul_le_mul_of_nonneg_left hn1R
      (by positivity : 0 ≤ Real.log 2 / 16)
    exact (min_le_right _ _).trans (by simpa only [mul_one] using hprod)
  have ha : 0 ≤ A * (blockLog n) ^ 3 / (n : ℝ) := by
    exact div_nonneg (mul_nonneg hA (pow_nonneg (blockLog_nonneg n) _)) hnR.le
  have hb := nsWeightedMoment_le_laplace_budget hρ hσ hC n hdom hcenter
    ht ht0 ht3 htBeta ha (hN n hn) hlap
  have hL : 1 ≤ blockLog n := blockLog_ge_one hn1
  have hL3 : 1 ≤ (blockLog n) ^ 3 := one_le_pow₀ hL
  have hNL : 1 ≤ (n : ℝ) * (blockLog n) ^ 3 := by
    simpa only [one_mul] using mul_le_mul hn1R hL3 (by norm_num) hnR.le
  have ha3 : (A * (blockLog n) ^ 3 / (n : ℝ)) *
      (1 + 2 * (A * (blockLog n) ^ 3 / (n : ℝ))) ≤
      3 * (A * (blockLog n) ^ 3 / (n : ℝ)) := by
    have hsmall := hN n hn
    nlinarith
  have hcoef : 2 * Real.exp (8 * (zeta / (n : ℝ)) * (C + 1) * (n : ℝ) / 3) /
      (zeta / (n : ℝ)) ^ 2 = B * (n : ℝ) ^ 2 := by
    have he : 8 * (zeta / (n : ℝ)) * (C + 1) * (n : ℝ) / 3 =
        8 * zeta * (C + 1) / 3 := by field_simp [hnR.ne'] <;> ring
    rw [he]
    dsimp [B]
    field_simp [hnR.ne', hzeta.ne']
    <;> ring
  have htail : Real.rpow 2 (-(n : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have htail' : T * Real.rpow 2 (-(n : ℝ)) ≤ T * ((n : ℝ) * (blockLog n) ^ 3) :=
    mul_le_mul_of_nonneg_left (htail.trans hNL) hT.le
  rw [hcoef] at hb
  have hmain : B * (n : ℝ) ^ 2 *
      (3 * (A * (blockLog n) ^ 3 / (n : ℝ)) +
        (zeta / (n : ℝ)) * (umegakiReal ρ σ - center)) =
      B * (3 * A * ((n : ℝ) * (blockLog n) ^ 3) +
        zeta * ((n : ℝ) * (umegakiReal ρ σ - center))) := by
    field_simp [hnR.ne']
    <;> ring
  have hV : 0 ≤ (n : ℝ) * (umegakiReal ρ σ - center) := mul_nonneg hnR.le hmean
  have hW : 0 ≤ (n : ℝ) * (blockLog n) ^ 3 := le_trans (by norm_num) hNL
  have hgap : 0 ≤ (B * (3 * A) + T) * ((n : ℝ) * (umegakiReal ρ σ - center)) +
      (B * zeta) * ((n : ℝ) * (blockLog n) ^ 3) := by positivity
  calc
    nsWeightedMoment ρ σ center t ≤ B * (n : ℝ) ^ 2 *
        ((A * (blockLog n) ^ 3 / (n : ℝ)) *
          (1 + 2 * (A * (blockLog n) ^ 3 / (n : ℝ))) +
            (zeta / (n : ℝ)) * (umegakiReal ρ σ - center)) +
          T * Real.rpow 2 (-(n : ℝ)) := hb
    _ ≤ B * (n : ℝ) ^ 2 *
        (3 * (A * (blockLog n) ^ 3 / (n : ℝ)) +
          (zeta / (n : ℝ)) * (umegakiReal ρ σ - center)) +
            T * ((n : ℝ) * (blockLog n) ^ 3) :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add ha3 le_rfl)
        (mul_nonneg hB.le (sq_nonneg _))) htail'
    _ ≤ K * ((n : ℝ) * (umegakiReal ρ σ - center) +
          (n : ℝ) * (blockLog n) ^ 3) := by
      rw [hmain]
      dsimp [K]
      nlinarith

end QuantumProver.Equipartition.FiniteModel.EndpointMoment
