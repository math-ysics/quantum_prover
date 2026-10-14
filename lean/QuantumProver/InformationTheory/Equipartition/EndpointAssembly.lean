import QuantumProver.InformationTheory.Equipartition.RateLimit
import QuantumProver.InformationTheory.Equipartition.EndpointCurvature
import QuantumProver.InformationTheory.Equipartition.EndpointModulus
import QuantumProver.InformationTheory.MeasuredRelativeEntropySetVariational
import QuantumProver.InformationTheory.Equipartition.EndpointPetzCoefficient
import QuantumProver.InformationTheory.Equipartition.FiniteStageBootstrap
import QuantumProver.InformationTheory.RenyiStateComparison
import QuantumProver.InformationTheory.Equipartition.UniformWindow

noncomputable section
open scoped BigOperators Topology ComplexOrder
namespace QuantumProver.Equipartition.FiniteModel.EndpointAssembly

private theorem weighted_square_split_bound {beta t J x : ℝ}
    (hbeta : 0 < beta) (ht : 0 ≤ t) (htbeta : t ≤ beta / 4) (hJ : 0 ≤ J) :
    x ^ 2 * Real.exp (t * |x|) ≤ J ^ 2 * Real.exp (t * J) +
      (32 / beta ^ 2) * Real.exp (-(beta * J / 2)) * Real.exp (beta * |x|) := by
  by_cases hx : |x| ≤ J
  · have hs : x ^ 2 ≤ J ^ 2 := by
      rw [← sq_abs x]
      exact (sq_le_sq₀ (abs_nonneg x) hJ).mpr hx
    have he : Real.exp (t * |x|) ≤ Real.exp (t * J) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx ht)
    exact (mul_le_mul hs he (Real.exp_pos _).le (sq_nonneg _)).trans
      (le_add_of_nonneg_right (by positivity))
  · have hxJ : J ≤ |x| := (lt_of_not_ge hx).le
    have hs := absolute_weighted_square_le_exp (show 0 < beta / 2 by positivity)
      (show t ≤ (beta / 2) / 2 by linarith) (x := x)
    have hcoef : 8 / (beta / 2) ^ 2 = 32 / beta ^ 2 := by
      field_simp [hbeta.ne'] <;> ring
    rw [hcoef] at hs
    have he : Real.exp ((beta / 2) * |x|) ≤
        Real.exp (-(beta * J / 2)) * Real.exp (beta * |x|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hxJ hbeta.le]
    calc
      _ ≤ (32 / beta ^ 2) *
          (Real.exp (-(beta * J / 2)) * Real.exp (beta * |x|)) :=
        hs.trans (mul_le_mul_of_nonneg_left he (by positivity))
      _ = (32 / beta ^ 2) * Real.exp (-(beta * J / 2)) *
          Real.exp (beta * |x|) := by ring
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

theorem matrix_ns_quadratic_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {C center t : ℝ} (hC : 0 ≤ C) {n : ℕ} (hn : 0 < n)
    (hdom : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ))
    (htrace : (Matrix.trace σ).re ≤ Real.rpow 2 (C * (n : ℝ)))
    (hcenter : |center| ≤ C * (n : ℝ)) (ht : 0 ≤ t)
    (htwindow : t ≤ min 1 (Real.log 2 / 8) / (n : ℝ)) :
    nsWeightedMoment ρ σ center t ≤
      (16 * (C + 1) ^ 2 * Real.exp (4 * (C + 1)) +
        64 / (Real.log 2 / 2) ^ 2) * (n : ℝ) ^ 2 := by
  let beta : ℝ := Real.log 2 / 2
  let J : ℝ := 4 * (C + 1) * (n : ℝ)
  let L := nsLaw ρ σ hρ hσ
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
  have htN : t * (n : ℝ) ≤ min 1 (Real.log 2 / 8) :=
    (le_div_iff₀ hnR).mp htwindow
  have htOne : t * (n : ℝ) ≤ 1 := htN.trans (min_le_left _ _)
  have htBeta : t ≤ beta / 4 := by
    have htn : t ≤ t * (n : ℝ) := by nlinarith
    dsimp [beta]
    linarith [htN.trans (min_le_right _ _)]
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hsplit := L.expect_mono (fun z => weighted_square_split_bound hbeta ht htBeta hJ
    (x := nsLikelihood ρ σ z - center))
  rw [L.expect_add, L.expect_const, L.expect_smul] at hsplit
  change nsWeightedMoment ρ σ center t ≤ _ at hsplit
  have ha : 0 < Real.rpow 2 (C * (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hhalf := nsLaw_absolute_half_order_bound hρ hσ ha hdom htrace center
  have hhalf' : L.expect (fun z => Real.exp (beta * |nsLikelihood ρ σ z - center|)) ≤
      2 * Real.sqrt (Real.rpow 2 (C * (n : ℝ))) * Real.exp (beta * |center|) := hhalf
  have hsqrt : Real.sqrt (Real.rpow 2 (C * (n : ℝ))) =
      Real.exp (beta * C * (n : ℝ)) := by
    have hlog : Real.log (Real.rpow 2 (C * (n : ℝ))) =
        (C * (n : ℝ)) * Real.log 2 := by
      simpa only [Real.rpow_eq_pow] using
        Real.log_rpow (by norm_num : (0 : ℝ) < 2) (C * (n : ℝ))
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ha, hlog]
    dsimp [beta]
    congr 1
    ring
  have htail : (32 / beta ^ 2) * Real.exp (-(beta * J / 2)) *
      L.expect (fun z => Real.exp (beta * |nsLikelihood ρ σ z - center|)) ≤
        64 / beta ^ 2 := by
    calc
      _ ≤ (32 / beta ^ 2) * Real.exp (-(beta * J / 2)) *
          (2 * Real.sqrt (Real.rpow 2 (C * (n : ℝ))) * Real.exp (beta * |center|)) :=
        mul_le_mul_of_nonneg_left hhalf' (by positivity)
      _ = (64 / beta ^ 2) *
          Real.exp (-(beta * J / 2) + beta * C * (n : ℝ) + beta * |center|) := by
        rw [hsqrt, Real.exp_add, Real.exp_add]
        ring
      _ ≤ (64 / beta ^ 2) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have hc := mul_le_mul_of_nonneg_left hcenter hbeta.le
        dsimp [J]
        nlinarith
      _ = _ := mul_one _
  have hnear : J ^ 2 * Real.exp (t * J) ≤
      (16 * (C + 1) ^ 2 * Real.exp (4 * (C + 1))) * (n : ℝ) ^ 2 := by
    have he : Real.exp (t * J) ≤ Real.exp (4 * (C + 1)) := by
      apply Real.exp_le_exp.mpr
      dsimp [J]
      nlinarith [mul_le_mul_of_nonneg_left htOne (show 0 ≤ 4 * (C + 1) by positivity)]
    calc
      _ ≤ J ^ 2 * Real.exp (4 * (C + 1)) :=
        mul_le_mul_of_nonneg_left he (sq_nonneg _)
      _ = _ := by dsimp [J]; ring
  have hnSq : 1 ≤ (n : ℝ) ^ 2 := by nlinarith
  have htailN : 64 / beta ^ 2 ≤ (64 / beta ^ 2) * (n : ℝ) ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hnSq
      (show 0 ≤ 64 / beta ^ 2 by positivity)
  calc
    _ ≤ J ^ 2 * Real.exp (t * J) + 64 / beta ^ 2 :=
      hsplit.trans (add_le_add le_rfl htail)
    _ ≤ (16 * (C + 1) ^ 2 * Real.exp (4 * (C + 1))) * (n : ℝ) ^ 2 +
        (64 / beta ^ 2) * (n : ℝ) ^ 2 := add_le_add hnear htailN
    _ = _ := by dsimp [beta]; ring

theorem physical_quadratic_ns_baseline {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ n : ℕ, 0 < n → ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
        ∀ t : ℝ, 0 ≤ t → t ≤ c / (n : ℝ) →
          nsWeightedMoment ρ σ ((n : ℝ) * regularizedRate F) t ≤ K * (n : ℝ) ^ 2 ∧
          nsWeightedMoment ρ σ (umegakiReal ρ σ) t ≤ K * (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, hr, hgrowth⟩ := physical_fixed_growth_entropy_rate_bounds hF
  let K := 16 * (C + 1) ^ 2 * Real.exp (4 * (C + 1)) +
    64 / (Real.log 2 / 2) ^ 2 + 1
  let c := min 1 (Real.log 2 / 8)
  have hK : 0 < K := by dsimp [K]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨K, c, hK, hc, ?_⟩
  intro n hn ρ hρ σ hσ t ht hwindow
  have hp := hgrowth n hn ρ hρ σ hσ
  have hstate := hF.null_states n hn ρ hρ
  have hpos := hF.alternative_positive n hn σ hσ
  have hdom : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ) := by
    simpa only [complex_real_smul] using hp.1
  have htracePos := trace_re_pos_of_state_domination hstate
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hp.1
  have htrace := le_two_rpow_of_logTwo_le htracePos hp.2.1
  have hrate : |(n : ℝ) * regularizedRate F| ≤ C * (n : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg n)]
  have hpad : ∀ center : ℝ, |center| ≤ C * (n : ℝ) →
      nsWeightedMoment ρ σ center t ≤ K * (n : ℝ) ^ 2 := by
    intro center hcenter
    have hm := matrix_ns_quadratic_budget hstate hpos hC hn hdom htrace hcenter ht hwindow
    refine hm.trans ?_
    dsimp [K]
    nlinarith [sq_nonneg (n : ℝ)]
  exact ⟨hpad _ hrate, hpad _ hp.2.2⟩

open scoped Kronecker

theorem physical_measured_one_superadditive {d m n : ℕ}
    {F : QuantumFamilies d} (hF : PhysicalAssumptions F) (hm : 0 < m) (hn : 0 < n) :
    setMeasuredDivergence F m 1 + setMeasuredDivergence F n 1 ≤
      setMeasuredDivergence F (m + n) 1 := by
  let e := wordSplitEquiv d m n
  let S := basisMatrixSet e.symm (F.null (m + n))
  let T := basisMatrixSet e.symm (F.alternative (m + n))
  have hmn : 0 < m + n := Nat.add_pos_left hm n
  have hSs : ∀ ρ ∈ S, IsState ρ := by
    rintro ρ ⟨ρ₀, hρ, rfl⟩
    exact basis_isState e.symm (hF.null_states _ hmn ρ₀ hρ)
  have hTp : ∀ σ ∈ T, σ.PosSemidef := by
    rintro σ ⟨σ₀, hσ, rfl⟩
    exact (hF.alternative_positive _ hmn σ₀ hσ).submatrix e.symm
  have hSpolar : ∀ X ∈ positivePolar (F.null m), ∀ Y ∈ positivePolar (F.null n),
      X ⊗ₖ Y ∈ positivePolar S := by
    intro X hX Y hY
    apply (positivePolar_basisMatrixSet_iff e.symm _ _).mpr
    exact hF.null_polar_tensor m n hm hn X hX Y hY
  have hTpolar : ∀ X ∈ positivePolar (F.alternative m), ∀ Y ∈ positivePolar (F.alternative n),
      X ⊗ₖ Y ∈ positivePolar T := by
    intro X hX Y hY
    apply (positivePolar_basisMatrixSet_iff e.symm _ _).mpr
    exact hF.alternative_polar_tensor m n hm hn X hX Y hY
  have hs := QuantumProver.MeasuredRelativeEntropySetVariational.setMeasuredDivergenceOn_one_tensor_superadditive
    (F.null m) (F.alternative m) (F.null n) (F.alternative n) S T
    (hF.null_nonempty m hm) (hF.null_nonempty n hn) ((hF.null_nonempty _ hmn).image _)
    (hF.alternative_nonempty m hm) (hF.alternative_nonempty n hn)
    ((hF.alternative_nonempty _ hmn).image _)
    (hF.null_compact m hm) (hF.null_compact n hn)
    (basisMatrixSet_compact e.symm (hF.null_compact _ hmn))
    (hF.alternative_compact m hm) (hF.alternative_compact n hn)
    (basisMatrixSet_compact e.symm (hF.alternative_compact _ hmn))
    (hF.null_convex m hm) (hF.null_convex n hn)
    (basisMatrixSet_convex e.symm (hF.null_convex _ hmn))
    (hF.alternative_convex m hm) (hF.alternative_convex n hn)
    (basisMatrixSet_convex e.symm (hF.alternative_convex _ hmn))
    (hF.null_states m hm) (hF.null_states n hn) hSs
    (hF.alternative_positive m hm) (hF.alternative_positive n hn) hTp
    hSpolar hTpolar
  change PolarTensor.matrixSetMeasuredDivergence (F.null m) (F.alternative m) 1 +
    PolarTensor.matrixSetMeasuredDivergence (F.null n) (F.alternative n) 1 ≤
      PolarTensor.matrixSetMeasuredDivergence S T 1 at hs
  rw [matrixSetMeasuredDivergence_basisMatrixSet] at hs
  exact hs

theorem physical_measured_one_real_superadditive {d m n : ℕ}
    {F : QuantumFamilies d} (hF : PhysicalAssumptions F) (hm : 0 < m) (hn : 0 < n) :
    (setMeasuredDivergence F m 1).toReal + (setMeasuredDivergence F n 1).toReal ≤
      (setMeasuredDivergence F (m + n) 1).toReal := by
  have hf₁ := physical_setMeasuredDivergence_one_finite hF hm
  have hf₂ := physical_setMeasuredDivergence_one_finite hF hn
  have hf₁₂ := physical_setMeasuredDivergence_one_finite hF (Nat.add_pos_left hm n)
  have h := physical_measured_one_superadditive hF hm hn
  rw [← EReal.coe_toReal hf₁.1 hf₁.2, ← EReal.coe_toReal hf₂.1 hf₂.2,
    ← EReal.coe_toReal hf₁₂.1 hf₁₂.2, ← EReal.coe_add] at h
  exact EReal.coe_le_coe_iff.mp h

theorem physical_measured_one_supremum_eq_rate {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : measuredRateSupremum F 1 = regularizedRate F := by
  have hlim : Filter.Tendsto
      (fun n : ℕ => (setMeasuredDivergence F n 1).toReal / (n : ℝ))
        Filter.atTop (nhds (measuredRateSupremum F 1)) := by
    obtain ⟨C, hC, hb⟩ := physical_linear_setMeasuredDivergence_one_bounds hF
    apply ScalarRate.matrix_superadditive_full_limit
      (fun n => (setMeasuredDivergence F n 1).toReal)
      (fun m n hm hn => physical_measured_one_real_superadditive hF hm hn) hC
    intro n hn
    have hf := physical_setMeasuredDivergence_one_finite hF hn
    simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal
      (hb n hn).2 hf.2 (EReal.coe_ne_top _)
  exact tendsto_nhds_unique hlim (physical_actual_measured_one_full_rate hF).2

theorem physical_measured_one_block_le_actual_rate {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) :
    (setMeasuredDivergence F n 1).toReal ≤ (n : ℝ) * regularizedRate F := by
  have h := physical_measured_one_block_le_supremum hF hn
  rw [physical_measured_one_supremum_eq_rate hF] at h
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  nlinarith [(div_le_iff₀ hnR).mp h]

theorem physical_umegaki_block_gap {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) :
    (setUmegaki F n).toReal ≤ (n : ℝ) * regularizedRate F + pinchingOverhead d n := by
  linarith [physical_setUmegaki_one_pinching_real hF hn,
    physical_measured_one_block_le_actual_rate hF hn]

theorem physical_every_exactMinimizer_mean_gap {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {ρ σ : QMat d n}
    (hmin : IsExactMinimizer F ρ σ) :
    0 ≤ umegakiReal ρ σ - (n : ℝ) * regularizedRate F ∧
      umegakiReal ρ σ - (n : ℝ) * regularizedRate F ≤ pinchingOverhead d n := by
  refine ⟨physical_pair_mean_surplus_nonneg hF hn hmin.1 hmin.2.1, ?_⟩
  have h := physical_exactMinimizer_mean_le_actual_rate_residual hF hn hmin
  simpa only [physical_measured_one_supremum_eq_rate hF, sub_self, mul_zero, add_zero] using h

theorem physical_measured_below_one_le_one {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {alpha : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    setMeasuredDivergence F n alpha ≤ setMeasuredDivergence F n 1 := by
  exact QuantumProver.MeasuredRelativeEntropySetVariational.setMeasuredDivergenceOn_le_one
    (F.null n) (F.alternative n) (hF.null_states n hn)
    (hF.alternative_positive n hn) ha ha1

theorem physical_measured_below_one_supremum_le_rate {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1) :
    measuredRateSupremum F alpha ≤ regularizedRate F := by
  apply csSup_le (measuredEntropyRates_nonempty F alpha)
  rintro x ⟨n, hn, rfl⟩
  have hf := physical_setMeasuredDivergence_finite hF hn ha ha1
  have hf1 := physical_setMeasuredDivergence_one_finite hF hn
  have hb := EReal.toReal_le_toReal (physical_measured_below_one_le_one hF hn ha ha1)
    hf.2 hf1.1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  exact (div_le_div_of_nonneg_right hb hnR.le).trans
    (by simpa only [physical_measured_one_supremum_eq_rate hF] using
      physical_measured_one_block_le_supremum hF hn)

theorem physical_quadratic_petz_baseline {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ c ≤ 1 / 2 ∧
      ∀ n : ℕ, 0 < n → ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
        ∀ delta : ℝ, 0 < delta → delta * (n : ℝ) ≤ c →
          (((n : ℝ) * regularizedRate F - B * delta * (n : ℝ) ^ 2 : ℝ) : EReal) ≤
            petzDivergence ρ σ (1 - delta) ∧
          petzDivergence ρ σ (1 + delta) ≤
            ((umegakiReal ρ σ + B * delta * (n : ℝ) ^ 2 : ℝ) : EReal) := by
  obtain ⟨K, c0, hK, hc0, hm⟩ := physical_quadratic_ns_baseline hF
  let B := Real.log 2 * K / 2
  let c := min (1 / 2) (c0 / Real.log 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨B, c, hB, hc, min_le_left _ _, ?_⟩
  intro n hn ρ hρ σ hσ delta hd hwindow
  let t := delta * Real.log 2
  let L := nsLaw ρ σ (hF.null_states n hn ρ hρ) (hF.alternative_positive n hn σ hσ)
  let X := fun z => nsLikelihood ρ σ z - (n : ℝ) * regularizedRate F
  let Y := fun z => nsLikelihood ρ σ z - umegakiReal ρ σ
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
  have ht : 0 < t := by dsimp [t]; positivity
  have htWindow : t ≤ c0 / (n : ℝ) := by
    apply (le_div_iff₀ hnR).mpr
    have hh := hwindow.trans (min_le_right (1 / 2) (c0 / Real.log 2))
    have hmul := (le_div_iff₀ hlog).mp hh
    dsimp [t]
    nlinarith
  have hdhalf : delta ≤ 1 / 2 := by
    have hh := hwindow.trans (min_le_left (1 / 2) (c0 / Real.log 2))
    nlinarith
  have ha : 0 < 1 - t / Real.log 2 := by
    dsimp [t]
    rw [mul_div_cancel_right₀ _ hlog.ne']
    linarith
  have hx := (hm n hn ρ hρ σ hσ t ht.le htWindow).1
  have hy := (hm n hn ρ hρ σ hσ t ht.le htWindow).2
  have hxm : 0 ≤ L.mean X := physical_ns_mean_surplus_nonneg hF hn hρ hσ
  have hym : L.mean Y = 0 := by
    change L.expect (fun z => nsLikelihood ρ σ z - umegakiReal ρ σ) = 0
    rw [L.expect_sub, L.expect_const]
    have hh := nsLaw_mean_eq_umegakiReal ρ σ (hF.null_states n hn ρ hρ)
      (hF.alternative_positive n hn σ hσ)
    change L.expect (nsLikelihood ρ σ) = umegakiReal ρ σ at hh
    rw [hh, sub_self]
  have hxw : L.weightedSecondMoment X 0 t ≤ K * (n : ℝ) ^ 2 := by
    simpa only [L, X, FiniteLaw.weightedSecondMoment, sub_zero, nsLaw_expect,
      nsWeightedMoment] using hx
  have hyw : L.weightedSecondMoment Y 0 t ≤ K * (n : ℝ) ^ 2 := by
    simpa only [L, Y, FiniteLaw.weightedSecondMoment, sub_zero, nsLaw_expect,
      nsWeightedMoment] using hy
  let E := (t ^ 2 / 2) * K * (n : ℝ) ^ 2
  have hneg : L.expect (fun z => Real.exp (-t * X z)) ≤ Real.exp E := by
    have hh := L.laplace_taylor_upper X ht.le
    have hbudget := mul_le_mul_of_nonneg_left hxw (show 0 ≤ t ^ 2 / 2 by positivity)
    have hs := mul_nonneg ht.le hxm
    have hle : L.expect (fun z => Real.exp (-t * X z)) ≤ 1 + E := by
      dsimp [E]
      nlinarith
    exact hle.trans (by simpa only [add_comm] using Real.add_one_le_exp E)
  have hpos : L.expect (fun z => Real.exp (t * Y z)) ≤ Real.exp E := by
    have hh := L.positive_laplace_taylor_upper Y ht.le
    rw [hym, mul_zero, add_zero] at hh
    have hbudget := mul_le_mul_of_nonneg_left hyw (show 0 ≤ t ^ 2 / 2 by positivity)
    have hle : L.expect (fun z => Real.exp (t * Y z)) ≤ 1 + E := by
      dsimp [E]
      nlinarith
    exact hle.trans (by simpa only [add_comm] using Real.add_one_le_exp E)
  have hs := physical_pair_supportLE hF hn hρ hσ
  have hlower := EndpointCurvature.petz_lower_of_negative_laplace
    (hF.null_states n hn ρ hρ) (hF.alternative_positive n hn σ hσ) hs
    ((n : ℝ) * regularizedRate F) ht ha hneg
  have hupper := EndpointCurvature.petz_upper_of_positive_laplace
    (hF.null_states n hn ρ hρ) (hF.alternative_positive n hn σ hσ) hs
    (umegakiReal ρ σ) ht hpos
  have horder : t / Real.log 2 = delta := by
    dsimp [t]
    exact mul_div_cancel_right₀ _ hlog.ne'
  have hcost : E / t = B * delta * (n : ℝ) ^ 2 := by
    dsimp [E, t, B]
    field_simp [hd.ne', hlog.ne'] <;> ring
  exact ⟨by simpa only [horder, hcost] using hlower,
    by simpa only [horder, hcost] using hupper⟩

theorem physical_pair_petz_ge_actual_measured_rate {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {ρ σ : QMat d n}
    (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n)
    {alpha : ℝ} (ha : (1 / 2 : ℝ) ≤ alpha) (ha1 : alpha < 1) :
    (((n : ℝ) * measuredRateSupremum F alpha : ℝ) : EReal) ≤
      petzDivergence ρ σ alpha := by
  have ha0 : 0 < alpha := by linarith
  have haNe : alpha ≠ 1 := ne_of_lt ha1
  let D := logTwo (petzTrace ρ σ alpha) / (alpha - 1)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmultiple : Filter.Tendsto (fun k : ℕ => k * n) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (fun k => ?_) Filter.tendsto_id
    change k ≤ k * n
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
    nlinarith
  have hlim := (physical_actual_measured_full_rate hF ha ha1).2.comp hmultiple
  have hbound : measuredRateSupremum F alpha ≤ D / (n : ℝ) := by
    apply le_of_tendsto hlim
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
    have hkp : 0 < k := Nat.zero_lt_one.trans_le hk
    have hkn : 0 < k * n := Nat.mul_pos hkp hn
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hkp
    obtain ⟨ρk, σk, hρk, hσk, hPk⟩ :=
      physical_pair_petz_repetition hF hn hρ hσ ha0 haNe k hkp
    have hs : setMeasuredDivergence F (k * n) alpha ≤ measuredDivergence ρk σk alpha :=
      sInf_le ⟨ρk, hρk, σk, hσk, rfl⟩
    have hp := QuantumProver.PetzMeasurementDPI.measuredDivergence_le_petzDivergence
      (hF.null_states (k * n) hkn ρk hρk).1
      (hF.alternative_positive (k * n) hkn σk hσk) ha0 ha1
    rw [hPk] at hp
    have hf := physical_setMeasuredDivergence_finite hF hkn ha0 ha1
    have hb : (setMeasuredDivergence F (k * n) alpha).toReal ≤ (k : ℝ) * D := by
      simpa only [EReal.toReal_coe] using
        EReal.toReal_le_toReal (hs.trans hp) hf.2 (EReal.coe_ne_top _)
    have hnknR : 0 < ((k * n : ℕ) : ℝ) := by exact_mod_cast hkn
    have hdiv := div_le_div_of_nonneg_right hb hnknR.le
    have hid : ((k : ℝ) * D) / ((k * n : ℕ) : ℝ) = D / (n : ℝ) := by
      rw [Nat.cast_mul]
      field_simp [hkR.ne', hnR.ne']
    exact hdiv.trans_eq hid
  rw [petzDivergence_real_of_support ρ σ (hF.null_states n hn ρ hρ)
    (hF.alternative_positive n hn σ hσ) (physical_pair_supportLE hF hn hρ hσ) ha0 haNe]
  apply EReal.coe_le_coe
  have hh := (le_div_iff₀ hnR).mp hbound
  dsimp [D] at hh
  nlinarith

theorem physical_lower_laplace_actual_measured_rate {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {ρ σ : QMat d n}
    (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n)
    {t : ℝ} (ht : 0 < t) (horder : (1 / 2 : ℝ) ≤ 1 - t / Real.log 2) :
    (nsLaw ρ σ (hF.null_states n hn ρ hρ)
      (hF.alternative_positive n hn σ hσ)).expect
        (fun z => Real.exp (-t * (nsLikelihood ρ σ z - (n : ℝ) * regularizedRate F))) ≤
      Real.exp (t * (n : ℝ) *
        (regularizedRate F - measuredRateSupremum F (1 - t / Real.log 2))) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : 0 < 1 - t / Real.log 2 := by linarith
  have ha1 : 1 - t / Real.log 2 < 1 := by linarith [div_pos ht hlog]
  have hp := physical_pair_petz_ge_actual_measured_rate hF hn hρ hσ horder ha1
  have hl := physical_ns_laplace_le_of_petz_lower hF hn hρ hσ ht ha0 hp
  convert hl using 1 <;> ring

theorem physical_narrow_laplace_of_smaller_block {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 32 ≤ n) {G zeta : ℝ}
    (hzeta : 0 < zeta) (hzetaSmall : zeta ≤ Real.log 2 / 8) (M : ℕ)
    (hsmaller : (((((n / 16 : ℕ) : ℝ) * regularizedRate F -
      G * blockLog (n / 16) -
      (FixedMInduction.curvatureOrder zeta n * ((n / 16 : ℕ) : ℝ)) *
        ((M : ℝ) * (blockLog (n / 16)) ^ 3)) : ℝ) : EReal) ≤
      setMeasuredDivergence F (n / 16) (1 - FixedMInduction.curvatureOrder zeta n)) :
    ∀ (ρ : QMat d n) (hρ : ρ ∈ F.null n) (σ : QMat d n) (hσ : σ ∈ F.alternative n),
      (nsLaw ρ σ (hF.null_states n (by omega) ρ hρ)
        (hF.alternative_positive n (by omega) σ hσ)).expect
        (fun z => Real.exp (-EndpointCurvature.narrowScale zeta n *
          (nsLikelihood ρ σ z - (n : ℝ) * regularizedRate F))) ≤
            Real.exp (EndpointCurvature.narrowBlockBudget G M zeta n) := by
  intro ρ hρ σ hσ
  have hnp : 0 < n := by omega
  have hmp : 0 < n / 16 := (shrunk_block_bounds hn).1
  have hmR : 0 < ((n / 16 : ℕ) : ℝ) := by exact_mod_cast hmp
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnp
  have hLn : 1 ≤ blockLog n := blockLog_ge_one (by omega)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht := EndpointCurvature.narrowScale_pos (by omega : 1 ≤ n) hzeta
  have hd : 0 < FixedMInduction.curvatureOrder zeta n :=
    (FixedMInduction.curvatureOrder_in_smaller_window hn hzeta).1
  have hdsmall : FixedMInduction.curvatureOrder zeta n ≤ 1 / 8 := by
    unfold FixedMInduction.curvatureOrder
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) * blockLog n * Real.log 2)).mpr
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hprod : 1 ≤ (n : ℝ) * blockLog n := by
      nlinarith [mul_le_mul hn1 hLn (by norm_num : (0 : ℝ) ≤ 1) hnR.le]
    nlinarith [mul_le_mul_of_nonneg_right hprod hlog.le]
  have ha : (1 / 2 : ℝ) ≤ 1 - FixedMInduction.curvatureOrder zeta n := by linarith
  have ha0 : 0 < 1 - FixedMInduction.curvatureOrder zeta n := by linarith
  have ha1 : 1 - FixedMInduction.curvatureOrder zeta n < 1 := by linarith
  have hf := physical_setMeasuredDivergence_finite hF hmp ha0 ha1
  have hsmallerR := EReal.toReal_le_toReal hsmaller (EReal.coe_ne_bot _) hf.1
  simp only [EReal.toReal_coe] at hsmallerR
  have hs := (div_le_iff₀ hmR).mp
    (physical_measured_block_le_supremum hF hmp ha0 ha1)
  have hmod : regularizedRate F -
      measuredRateSupremum F (1 - FixedMInduction.curvatureOrder zeta n) ≤
        G * blockLog (n / 16) / ((n / 16 : ℕ) : ℝ) +
          (M : ℝ) * FixedMInduction.curvatureOrder zeta n * (blockLog (n / 16)) ^ 3 := by
    have hid : G * blockLog (n / 16) / ((n / 16 : ℕ) : ℝ) +
        (M : ℝ) * FixedMInduction.curvatureOrder zeta n * (blockLog (n / 16)) ^ 3 =
      (G * blockLog (n / 16) +
        ((M : ℝ) * FixedMInduction.curvatureOrder zeta n *
          (blockLog (n / 16)) ^ 3) * ((n / 16 : ℕ) : ℝ)) /
            ((n / 16 : ℕ) : ℝ) := by field_simp [hmR.ne'] <;> ring
    rw [hid]
    apply (le_div_iff₀ hmR).mpr
    nlinarith
  have horderEq : EndpointCurvature.narrowScale zeta n / Real.log 2 =
      FixedMInduction.curvatureOrder zeta n := by
    unfold EndpointCurvature.narrowScale FixedMInduction.curvatureOrder
    rw [div_div]
  have hLap := physical_lower_laplace_actual_measured_rate hF hnp hρ hσ ht
    (by rw [horderEq]; exact ha)
  rw [horderEq] at hLap
  refine hLap.trans (Real.exp_le_exp.mpr ?_)
  exact mul_le_mul_of_nonneg_left hmod (mul_nonneg ht.le hnR.le)

theorem physical_narrow_petz_recurrence {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ C : ℝ, 0 ≤ C ∧ |regularizedRate F| ≤ C ∧
      ∀ G zeta : ℝ, 0 ≤ G → EndpointPetzCoefficient.pinchingCoefficient d ≤ G →
      0 < zeta → zeta ≤ Real.log 2 / 8 → ∀ M n : ℕ, 32 ≤ n →
      (((((n / 16 : ℕ) : ℝ) * regularizedRate F - G * blockLog (n / 16) -
        (FixedMInduction.curvatureOrder zeta n * ((n / 16 : ℕ) : ℝ)) *
          ((M : ℝ) * (blockLog (n / 16)) ^ 3)) : ℝ) : EReal) ≤
        setMeasuredDivergence F (n / 16) (1 - FixedMInduction.curvatureOrder zeta n) →
      EndpointCurvature.narrowBlockBudget G M zeta n ≤ 1 →
      EndpointCurvature.narrowFactor C G M zeta n ≤ 2 →
      ∀ delta : ℝ, 0 < delta → delta < 1 →
      delta * (n : ℝ) * blockLog n ≤ FixedMInduction.endpointWindow zeta →
      (∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
        (((n : ℝ) * regularizedRate F - (delta * (n : ℝ)) *
          (EndpointCurvature.narrowFactor C G M zeta n * (M : ℝ) * (blockLog (n / 16)) ^ 3 +
            EndpointPetzCoefficient.negativeCoefficient G zeta * (blockLog n) ^ 2) : ℝ) : EReal) ≤
          petzDivergence ρ σ (1 - delta)) ∧
      (∀ (ρ σ : QMat d n), IsExactMinimizer F ρ σ →
        petzDivergence ρ σ (1 + delta) ≤
          (((n : ℝ) * regularizedRate F + G * blockLog n + (delta * (n : ℝ)) *
            (EndpointCurvature.narrowFactor C G M zeta n * (M : ℝ) * (blockLog (n / 16)) ^ 3 +
              EndpointPetzCoefficient.positiveCoefficient G zeta * (blockLog n) ^ 2) : ℝ) : EReal)) := by
  obtain ⟨C, hC, hr, hgrowth⟩ := physical_fixed_growth_entropy_rate_bounds hF
  refine ⟨C, hC, hr, ?_⟩
  intro G zeta hG hGpinch hzeta hzetaSmall M n hn hsmaller ha1 hH delta hd hd1 hwindow
  have hnp : 0 < n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcenter : -(C * (n : ℝ)) ≤ (n : ℝ) * regularizedRate F := by
    have hlo : -C ≤ regularizedRate F := (neg_le_neg hr).trans (neg_abs_le _)
    nlinarith [mul_le_mul_of_nonneg_left hlo hnR]
  have hLap := physical_narrow_laplace_of_smaller_block hF hn hzeta hzetaSmall M hsmaller
  have hdom : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ) := by
    intro ρ hρ σ hσ
    simpa only [complex_real_smul] using (hgrowth n hnp ρ hρ σ hσ).1
  constructor
  · intro ρ hρ σ hσ
    exact EndpointPetzCoefficient.matrix_petz_lower_coefficient
      (hF.null_states n hnp ρ hρ) (hF.alternative_positive n hnp σ hσ)
      hC hG hzeta hzetaSmall M hn (hdom ρ hρ σ hσ) hcenter
      (physical_pair_mean_surplus_nonneg hF hnp hρ hσ) hd hd1 hwindow ha1 hH
      (hLap ρ hρ σ hσ)
  · intro ρ σ hmin
    have hmean := physical_every_exactMinimizer_mean_gap hF hnp hmin
    have hgap : umegakiReal ρ σ - (n : ℝ) * regularizedRate F ≤ G * blockLog n := by
      exact hmean.2.trans ((EndpointPetzCoefficient.pinchingOverhead_le_blockLog d hn1).trans
        (mul_le_mul_of_nonneg_right hGpinch (blockLog_nonneg n)))
    exact EndpointPetzCoefficient.matrix_petz_upper_coefficient
      (hF.null_states n hnp ρ hmin.1) (hF.alternative_positive n hnp σ hmin.2.1)
      hC hG hzeta hzetaSmall M hn (hdom ρ hmin.1 σ hmin.2.1) hcenter
      hmean.1 hgap hd hwindow ha1 hH (hLap ρ hmin.1 σ hmin.2.1)

theorem physical_fixed_scale_laplace_of_matrix_modulus {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {K epsilon : ℝ} (hK : 0 < K) (hepsilon : 0 < epsilon)
    (hmodulus : ∀ delta : ℝ, 0 < delta → delta < epsilon →
      regularizedRate F - measuredRateSupremum F (1 - delta) ≤
        K * delta * (logTwo (1 / delta)) ^ 3) :
    ∃ N : ℕ, ∀ (n : ℕ) (hn : 0 < n), N ≤ n →
      ∀ (ρ : QMat d n) (hρ : ρ ∈ F.null n) (σ : QMat d n) (hσ : σ ∈ F.alternative n),
        (nsLaw ρ σ (hF.null_states n hn ρ hρ)
          (hF.alternative_positive n hn σ hσ)).expect
          (fun z => Real.exp (-((Real.log 2 / 8) / (n : ℝ)) *
            (nsLikelihood ρ σ z - (n : ℝ) * regularizedRate F))) ≤
              Real.exp ((K * Real.log 2) * (blockLog n) ^ 3 / (n : ℝ)) := by
  let N := Nat.ceil (1 / (8 * epsilon)) + 1
  refine ⟨N, ?_⟩
  intro n hn hnN ρ hρ σ hσ
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
  have hLn : 1 ≤ blockLog n := blockLog_ge_one (Nat.succ_le_of_lt hn)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let delta := 1 / (8 * (n : ℝ))
  let t := (Real.log 2 / 8) / (n : ℝ)
  have hd : 0 < delta := by dsimp [delta]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hnCeil : (Nat.ceil (1 / (8 * epsilon)) : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast hnN
  have hceil : 1 / (8 * epsilon) ≤ (Nat.ceil (1 / (8 * epsilon)) : ℝ) := Nat.le_ceil _
  have hsmall : delta < epsilon := by
    have hinv : 1 / (8 * epsilon) < (n : ℝ) := by linarith
    have hprod := (div_lt_iff₀ (show 0 < 8 * epsilon by positivity)).mp hinv
    dsimp [delta]
    apply (div_lt_iff₀ (by positivity : 0 < 8 * (n : ℝ))).mpr
    nlinarith
  have hdhalf : delta ≤ 1 / 8 := by
    dsimp [delta]
    apply (div_le_iff₀ (by positivity : 0 < 8 * (n : ℝ))).mpr
    nlinarith
  have horder : t / Real.log 2 = delta := by
    dsimp [t, delta]
    field_simp [hnR.ne', hlog.ne'] <;> ring
  have hInv : 1 / delta = 8 * (n : ℝ) := by
    dsimp [delta]
    field_simp [hnR.ne']
  have hlogEight : logTwo 8 = 3 := by
    unfold logTwo
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hLdelta0 : 0 ≤ logTwo (1 / delta) := by
    rw [hInv]
    unfold logTwo
    exact div_nonneg (Real.log_nonneg (by nlinarith)) hlog.le
  have hLdelta : logTwo (1 / delta) ≤ 4 * blockLog n := by
    rw [hInv]
    have hb := converse_logTwo_mono_pos (by positivity : 0 < 8 * (n : ℝ))
      (show 8 * (n : ℝ) ≤ 8 * ((n : ℝ) + 1) by nlinarith)
    rw [represented_logTwo_mul_pos (by norm_num : (0 : ℝ) < 8)
      (by positivity : 0 < (n : ℝ) + 1), hlogEight] at hb
    change logTwo (8 * (n : ℝ)) ≤ 3 + blockLog n at hb
    linarith
  have hpow : (logTwo (1 / delta)) ^ 3 ≤ (4 * blockLog n) ^ 3 :=
    pow_le_pow_left₀ hLdelta0 hLdelta 3
  have hmod := hmodulus delta hd hsmall
  have hLap := physical_lower_laplace_actual_measured_rate hF hn hρ hσ ht
    (by rw [horder]; linarith)
  rw [horder] at hLap
  refine hLap.trans (Real.exp_le_exp.mpr ?_)
  calc
    _ ≤ t * (n : ℝ) * (K * delta * (logTwo (1 / delta)) ^ 3) :=
      mul_le_mul_of_nonneg_left hmod (mul_nonneg ht.le hnR.le)
    _ ≤ t * (n : ℝ) * (K * delta * (4 * blockLog n) ^ 3) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow (mul_nonneg hK.le hd.le))
        (mul_nonneg ht.le hnR.le)
    _ = _ := by
      dsimp [t, delta]
      field_simp [hnR.ne'] <;> ring

theorem physical_wider_allpair_moment_of_matrix_modulus {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {K epsilon : ℝ} (hK : 0 < K) (hepsilon : 0 < epsilon)
    (hmodulus : ∀ delta : ℝ, 0 < delta → delta < epsilon →
      regularizedRate F - measuredRateSupremum F (1 - delta) ≤
        K * delta * (logTwo (1 / delta)) ^ 3) :
    ∃ c K1 : ℝ, 0 < c ∧ 0 < K1 ∧ ∀ n : ℕ, 0 < n →
      ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n, ∀ t : ℝ,
        0 ≤ t → t ≤ c / (n : ℝ) →
          nsWeightedMoment ρ σ ((n : ℝ) * regularizedRate F) t ≤
            K1 * ((n : ℝ) * (umegakiReal ρ σ - (n : ℝ) * regularizedRate F) +
              (n : ℝ) * (blockLog n) ^ 3) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact physical_all_length_fixed_scale_ns_moment hF (mul_nonneg hK.le hlog.le)
    (div_pos hlog (by norm_num : (0 : ℝ) < 8))
    (physical_fixed_scale_laplace_of_matrix_modulus hF hK hepsilon hmodulus)

theorem physical_every_minimizer_moment_of_matrix_modulus {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {K epsilon : ℝ} (hK : 0 < K) (hepsilon : 0 < epsilon)
    (hmodulus : ∀ delta : ℝ, 0 < delta → delta < epsilon →
      regularizedRate F - measuredRateSupremum F (1 - delta) ≤
        K * delta * (logTwo (1 / delta)) ^ 3) : OptimizerMomentConclusion F := by
  obtain ⟨c, K1, hc, hK1, hm⟩ := physical_wider_allpair_moment_of_matrix_modulus
    hF hK hepsilon hmodulus
  let G := max 0 (EndpointPetzCoefficient.pinchingCoefficient d)
  have hG : 0 ≤ G := le_max_left _ _
  have hGpinch : EndpointPetzCoefficient.pinchingCoefficient d ≤ G := le_max_right _ _
  have hKout : 0 < K1 * (G + 1) := mul_pos hK1 (by linarith)
  refine ⟨K1 * (G + 1), c, hKout, hc, ?_⟩
  intro n hn ρ σ hmin t ht hwindow
  have hmoment := hm n hn ρ hmin.1 σ hmin.2.1 t ht hwindow
  have hmean := physical_every_exactMinimizer_mean_gap hF hn hmin
  have hs : umegakiReal ρ σ - (n : ℝ) * regularizedRate F ≤ G * blockLog n :=
    hmean.2.trans ((EndpointPetzCoefficient.pinchingOverhead_le_blockLog d
      (Nat.succ_le_of_lt hn)).trans
      (mul_le_mul_of_nonneg_right hGpinch (blockLog_nonneg n)))
  have hL := blockLog_ge_one (Nat.succ_le_of_lt hn)
  have hLcube : blockLog n ≤ (blockLog n) ^ 3 := by
    have hsq : 1 ≤ (blockLog n) ^ 2 := one_le_pow₀ hL
    nlinarith [mul_le_mul_of_nonneg_left hsq (blockLog_nonneg n)]
  have hsCube : umegakiReal ρ σ - (n : ℝ) * regularizedRate F ≤ G * (blockLog n) ^ 3 :=
    hs.trans (mul_le_mul_of_nonneg_left hLcube hG)
  have hbudget : (n : ℝ) * (umegakiReal ρ σ - (n : ℝ) * regularizedRate F) +
      (n : ℝ) * (blockLog n) ^ 3 ≤ (G + 1) * (n : ℝ) * (blockLog n) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hsCube (Nat.cast_nonneg n)]
  exact hmoment.trans (by
    have hh := mul_le_mul_of_nonneg_left hbudget hK1.le
    convert hh using 1 <;> ring)

theorem physical_testing_upper_of_matrix_modulus {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {K epsilon : ℝ} (hK : 0 < K) (hepsilon : 0 < epsilon)
    (hmodulus : ∀ delta : ℝ, 0 < delta → delta < epsilon →
      regularizedRate F - measuredRateSupremum F (1 - delta) ≤
        K * delta * (logTwo (1 / delta)) ^ 3)
    {error : ℝ} (herror0 : 0 ≤ error) (herror1 : error < 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 0 < n →
      setTestingDivergence F n error ≠ ⊤ ∧ setTestingDivergence F n error ≠ ⊥ ∧
        (setTestingDivergence F n error).toReal ≤
          (n : ℝ) * regularizedRate F + B * testingRemainder n := by
  obtain ⟨K1, c, hK1, hc, hm⟩ :=
    physical_every_minimizer_moment_of_matrix_modulus hF hK hepsilon hmodulus
  let eta := (1 - error) / 4
  let theta := (1 - error) / 2
  let loss := logTwo (((1 - eta) - (1 + theta) * error) / (1 + theta⁻¹))
  let B := Real.sqrt (K1 / eta) + |loss| + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith [Real.sqrt_nonneg (K1 / eta), abs_nonneg loss]
  refine ⟨B, hB, ?_⟩
  intro n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨ρ, σ, hmin⟩ := physical_exists_exactMinimizer hF hn
  have hmoment := hm n hn ρ σ hmin 0 le_rfl (by positivity : 0 ≤ c / (n : ℝ))
  have hu := physical_setTestingDivergence_upper_of_pair_nsMoment hF hn hmin.1 hmin.2.1
    herror0 herror1 hK1 hmoment
  change setTestingDivergence F n error ≤
    (((n : ℝ) * regularizedRate F + Real.sqrt (K1 / eta) * testingRemainder n - loss : ℝ) : EReal) at hu
  have hrem := testingRemainder_ge_one hn
  have hupper : setTestingDivergence F n error ≤
      (((n : ℝ) * regularizedRate F + B * testingRemainder n : ℝ) : EReal) := by
    refine hu.trans (EReal.coe_le_coe ?_)
    have hpad := mul_le_mul_of_nonneg_left hrem (abs_nonneg loss)
    dsimp [B]
    nlinarith [neg_le_abs loss]
  have hf := physical_setTestingDivergence_finite hF hn herror0 herror1
  refine ⟨hf.1, hf.2, ?_⟩
  simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal hupper hf.2 (EReal.coe_ne_top _)

theorem physical_matrix_modulus_of_narrow_measured {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {c G M : ℝ} (hc : 0 < c)
    (hG : 0 ≤ G) (hM : 0 ≤ M) (N : ℕ)
    (hbelow : ∀ n : ℕ, N ≤ n → 0 < n → ∀ delta : ℝ,
      0 < delta → delta < 1 / 2 → delta * (n : ℝ) * blockLog n ≤ c →
        (((n : ℝ) * regularizedRate F - G * blockLog n -
          M * delta * (n : ℝ) * (blockLog n) ^ 3 : ℝ) : EReal) ≤
            setMeasuredDivergence F n (1 - delta)) :
    ∃ K epsilon : ℝ, 0 < K ∧ 0 < epsilon ∧ epsilon ≤ 1 / 2 ∧
      ∀ delta : ℝ, 0 < delta → delta < epsilon →
        0 ≤ regularizedRate F - measuredRateSupremum F (1 - delta) ∧
        regularizedRate F - measuredRateSupremum F (1 - delta) ≤
          K * delta * (logTwo (1 / delta)) ^ 3 := by
  have hblock : ∀ delta : ℝ, 0 < delta → delta < 1 / 2 → ∀ n : ℕ,
      N ≤ n → 0 < n → delta * (n : ℝ) * blockLog n ≤ c →
      regularizedRate F - measuredRateSupremum F (1 - delta) ≤
        G * blockLog n / (n : ℝ) + M * delta * (blockLog n) ^ 3 := by
    intro delta hd hdhalf n hnN hn hwindow
    have ha0 : 0 < 1 - delta := by linarith
    have ha1 : 1 - delta < 1 := by linarith
    have hf := physical_setMeasuredDivergence_finite hF hn ha0 ha1
    have hlow := EReal.toReal_le_toReal (hbelow n hnN hn delta hd hdhalf hwindow)
      (EReal.coe_ne_bot _) hf.1
    simp only [EReal.toReal_coe] at hlow
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsup := (div_le_iff₀ hnR).mp (physical_measured_block_le_supremum hF hn ha0 ha1)
    have hid : G * blockLog n / (n : ℝ) + M * delta * (blockLog n) ^ 3 =
      (G * blockLog n + M * delta * (blockLog n) ^ 3 * (n : ℝ)) / (n : ℝ) := by
      field_simp [hnR.ne'] <;> ring
    rw [hid]
    apply (le_div_iff₀ hnR).mpr
    nlinarith
  obtain ⟨K, epsilon, hK, hepsilon, hepsilonHalf, hm⟩ :=
    EndpointModulus.scalar_modulus_of_narrow_block hc hG hM N
      (fun delta => measuredRateSupremum F (1 - delta)) hblock
  refine ⟨K, epsilon, hK, hepsilon, hepsilonHalf, ?_⟩
  intro delta hd hde
  have ha0 : 0 < 1 - delta := by linarith
  have ha1 : 1 - delta < 1 := by linarith
  exact ⟨sub_nonneg.mpr (physical_measured_below_one_supremum_le_rate hF ha0 ha1),
    hm delta hd hde⟩

private theorem logTwo_nat_pow (x : ℝ) (k : ℕ) : logTwo (x ^ k) = (k : ℝ) * logTwo x := by
  unfold logTwo
  rw [Real.log_pow]
  ring

theorem matrix_testing_radius_costs {n : ℕ} (hn : 0 < n) :
    0 ≤ logTwo (testingRemainder n) ∧
    logTwo (testingRemainder n) ≤ 4 * blockLog n ∧
    blockLog n ≤ testingRemainder n ∧
    (n : ℝ) / testingRemainder n ≤ testingRemainder n ∧
    ((n : ℝ) / testingRemainder n) * (logTwo (testingRemainder n)) ^ 3 ≤
      64 * testingRemainder n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
  have hL := blockLog_ge_one (Nat.succ_le_of_lt hn)
  have hL0 : 0 ≤ blockLog n := blockLog_nonneg n
  have hLpos : 0 < blockLog n := by linarith
  have hR := testingRemainder_ge_one hn
  have hRpos : 0 < testingRemainder n := by linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlogL : logTwo (blockLog n) ≤ 2 * blockLog n := by
    unfold logTwo
    apply (div_le_iff₀ hlog).mpr
    have hh := Real.log_le_sub_one_of_pos hLpos
    nlinarith [mul_le_mul_of_nonneg_left hlogHalf (show 0 ≤ 2 * blockLog n by positivity)]
  have hlogN : logTwo (n : ℝ) ≤ blockLog n :=
    converse_logTwo_mono_pos hnR (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
  have hid : 2 * logTwo (testingRemainder n) =
      logTwo (n : ℝ) + 3 * logTwo (blockLog n) := by
    calc
      _ = logTwo ((testingRemainder n) ^ 2) := by rw [logTwo_nat_pow]; norm_num
      _ = logTwo ((n : ℝ) * (blockLog n) ^ 3) := by rw [converse_testingRemainder_sq]
      _ = _ := by
        rw [represented_logTwo_mul_pos hnR (pow_pos hLpos _), logTwo_nat_pow]
        norm_num
  have hlogR0 : 0 ≤ logTwo (testingRemainder n) := by
    unfold logTwo
    exact div_nonneg (Real.log_nonneg hR) hlog.le
  have hlogR : logTwo (testingRemainder n) ≤ 4 * blockLog n := by
    nlinarith
  have hLsq : 1 ≤ (blockLog n) ^ 2 := one_le_pow₀ hL
  have hLcube : 1 ≤ (blockLog n) ^ 3 := one_le_pow₀ hL
  have hLsqCube : (blockLog n) ^ 2 ≤ (blockLog n) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hL (sq_nonneg (blockLog n))]
  have hRsq := converse_testingRemainder_sq n
  have hRgeL : blockLog n ≤ testingRemainder n := by
    apply (sq_le_sq₀ hL0 hRpos.le).mp
    nlinarith [mul_le_mul_of_nonneg_right hn1 (pow_nonneg hL0 3)]
  have hratio : (n : ℝ) / testingRemainder n ≤ testingRemainder n := by
    apply (div_le_iff₀ hRpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hLcube hnR.le]
  have hcost : ((n : ℝ) / testingRemainder n) * (logTwo (testingRemainder n)) ^ 3 ≤
      64 * testingRemainder n := by
    have hp := pow_le_pow_left₀ hlogR0 hlogR 3
    have hpoly : (n : ℝ) * (logTwo (testingRemainder n)) ^ 3 ≤
        64 * (testingRemainder n) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hp hnR.le]
    have hh : ((n : ℝ) * (logTwo (testingRemainder n)) ^ 3) / testingRemainder n ≤
        64 * testingRemainder n := (div_le_iff₀ hRpos).mpr (by nlinarith)
    convert hh using 1 <;> ring
  exact ⟨hlogR0, hlogR, hRgeL, hratio, hcost⟩

theorem physical_pair_sandwiched_lower_of_petz {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {ρ σ : QMat d n}
    (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n) {C P delta : ℝ}
    (hr : regularizedRate F ≤ C) (htrace : logTwo σ.trace.re ≤ C * (n : ℝ))
    (hP : 0 ≤ P) (hd : 0 < delta) (hdhalf : delta ≤ 1 / 2)
    (hpetz : (((n : ℝ) * regularizedRate F - P : ℝ) : EReal) ≤
      petzDivergence ρ σ (1 - delta)) :
    (((n : ℝ) * regularizedRate F - P - 2 * C * delta * (n : ℝ) : ℝ) : EReal) ≤
      sandwichedDivergence ρ σ (1 - delta) := by
  have hR := hF.null_states n hn ρ hρ
  have hS := hF.alternative_positive n hn σ hσ
  have hs := physical_pair_supportLE hF hn hρ hσ
  have ha0 : 0 < 1 - delta := by linarith
  have ha1 : 1 - delta < 1 := by linarith
  have hp := petzDivergence_real_of_support ρ σ hR hS hs ha0 ha1.ne
  have hsw := QuantumProver.RenyiStateComparison.sandwichedDivergence_of_support hR hS hs ha0 ha1.ne
  rw [← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_div] at hsw
  have hden : 1 - delta - 1 = -delta := by ring
  rw [hden] at hp hsw
  rw [hp] at hpetz
  have hpR := EReal.coe_le_coe_iff.mp hpetz
  have hcmp := QuantumProver.RenyiStateComparison.petzReal_below_one_scale_le_sandwiched_delta
    hR hS hs hd hdhalf
  have hscaled := mul_le_mul_of_nonneg_left hpR (show 0 ≤ 1 - delta by linarith)
  have hscale := mul_le_mul_of_nonneg_left htrace hd.le
  have hrate := mul_le_mul_of_nonneg_left hr (mul_nonneg hd.le (Nat.cast_nonneg n))
  have hnonneg := mul_nonneg hd.le hP
  rw [hsw]
  apply EReal.coe_le_coe
  nlinarith

theorem physical_set_bounds_of_petz {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {C G P Q delta : ℝ}
    (hr : regularizedRate F ≤ C)
    (htrace : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      logTwo σ.trace.re ≤ C * (n : ℝ))
    (hGpinch : EndpointPetzCoefficient.pinchingCoefficient d ≤ G)
    (hP : 0 ≤ P) (hd : 0 < delta) (hdhalf : delta ≤ 1 / 2)
    (hlower : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      (((n : ℝ) * regularizedRate F - P : ℝ) : EReal) ≤ petzDivergence ρ σ (1 - delta))
    (hupper : ∀ ρ σ : QMat d n, IsExactMinimizer F ρ σ →
      petzDivergence ρ σ (1 + delta) ≤
        (((n : ℝ) * regularizedRate F + G * blockLog n + Q : ℝ) : EReal)) :
    (((n : ℝ) * regularizedRate F - G * blockLog n - P -
      2 * C * delta * (n : ℝ) : ℝ) : EReal) ≤ setMeasuredDivergence F n (1 - delta) ∧
    setSandwichedDivergence F n (1 + delta) ≤
      (((n : ℝ) * regularizedRate F + G * blockLog n + Q : ℝ) : EReal) := by
  have ha0 : 0 < 1 - delta := by linarith
  have ha1 : 1 - delta < 1 := by linarith
  have hlow : (((n : ℝ) * regularizedRate F - P -
      2 * C * delta * (n : ℝ) : ℝ) : EReal) ≤ setSandwichedDivergence F n (1 - delta) := by
    apply le_sInf
    rintro x ⟨ρ, hρ, σ, hσ, rfl⟩
    exact physical_pair_sandwiched_lower_of_petz hF hn hρ hσ hr
      (htrace ρ hρ σ hσ) hP hd hdhalf (hlower ρ hρ σ hσ)
  have hg := (EndpointPetzCoefficient.pinchingOverhead_le_blockLog d
    (Nat.succ_le_of_lt hn)).trans
      (mul_le_mul_of_nonneg_right hGpinch (blockLog_nonneg n))
  have hlow' := EReal.sub_le_sub hlow (EReal.coe_le_coe hg)
  rw [← EReal.coe_sub] at hlow'
  constructor
  · have hpinch := PermutationMeasured.physical_set_sandwich_sub_pinchingOverhead_le_measured
      hF hn ha0 ha1
    convert hlow'.trans hpinch using 1 <;> congr 1 <;> ring
  · obtain ⟨ρ, σ, hmin⟩ := physical_exists_exactMinimizer hF hn
    have hi : setSandwichedDivergence F n (1 + delta) ≤ sandwichedDivergence ρ σ (1 + delta) :=
      sInf_le ⟨ρ, hmin.1, σ, hmin.2.1, rfl⟩
    exact hi.trans ((QuantumProver.RenyiStateComparison.sandwichedDivergence_above_one_le_petz
      (hF.null_states n hn ρ hmin.1) (hF.alternative_positive n hn σ hmin.2.1)
      (physical_pair_supportLE hF hn hmin.1 hmin.2.1) hd hdhalf).trans (hupper ρ σ hmin))

theorem physical_quadratic_set_baseline {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ G B c : ℝ,
      0 ≤ G ∧ EndpointPetzCoefficient.pinchingCoefficient d ≤ G ∧
      0 < B ∧ 0 < c ∧ c ≤ 1 / 2 ∧
      ∀ n : ℕ, 0 < n → ∀ delta : ℝ, 0 < delta → delta * (n : ℝ) ≤ c →
        (((n : ℝ) * regularizedRate F - G * blockLog n - B * delta * (n : ℝ) ^ 2 : ℝ) : EReal) ≤
          setMeasuredDivergence F n (1 - delta) ∧
        setSandwichedDivergence F n (1 + delta) ≤
          (((n : ℝ) * regularizedRate F + G * blockLog n + B * delta * (n : ℝ) ^ 2 : ℝ) : EReal) := by
  obtain ⟨C, hC, hr, hgrowth⟩ := physical_fixed_growth_entropy_rate_bounds hF
  obtain ⟨B, c, hB, hc, hchalf, hp⟩ := physical_quadratic_petz_baseline hF
  let G := max 0 (EndpointPetzCoefficient.pinchingCoefficient d)
  refine ⟨G, B + 2 * C, c, le_max_left _ _, le_max_right _ _, by linarith,
    hc, hchalf, ?_⟩
  intro n hn delta hd hwindow
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
  have hdhalf : delta ≤ 1 / 2 := by nlinarith
  have hlower : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      (((n : ℝ) * regularizedRate F - B * delta * (n : ℝ) ^ 2 : ℝ) : EReal) ≤
        petzDivergence ρ σ (1 - delta) := by
    intro ρ hρ σ hσ
    exact (hp n hn ρ hρ σ hσ delta hd hwindow).1
  have hupper : ∀ ρ σ : QMat d n, IsExactMinimizer F ρ σ →
      petzDivergence ρ σ (1 + delta) ≤
        (((n : ℝ) * regularizedRate F + G * blockLog n + B * delta * (n : ℝ) ^ 2 : ℝ) : EReal) := by
    intro ρ σ hmin
    have hm := physical_every_exactMinimizer_mean_gap hF hn hmin
    have hg := (EndpointPetzCoefficient.pinchingOverhead_le_blockLog d
      (Nat.succ_le_of_lt hn)).trans
        (mul_le_mul_of_nonneg_right (le_max_right 0 _) (blockLog_nonneg n))
    exact (hp n hn ρ hmin.1 σ hmin.2.1 delta hd hwindow).2.trans (EReal.coe_le_coe (by linarith))
  have hs := physical_set_bounds_of_petz hF hn (le_abs_self _ |>.trans hr)
    (fun ρ hρ σ hσ => (hgrowth n hn ρ hρ σ hσ).2.1)
    (le_max_right 0 _) (by positivity : 0 ≤ B * delta * (n : ℝ) ^ 2)
    hd hdhalf hlower hupper
  have hpad : 2 * C * delta * (n : ℝ) ≤ 2 * C * delta * (n : ℝ) ^ 2 := by
    have hh : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  constructor
  · exact (EReal.coe_le_coe (by nlinarith)).trans hs.1
  · exact hs.2.trans (EReal.coe_le_coe (by nlinarith [mul_nonneg hC (by positivity : 0 ≤ delta * (n : ℝ) ^ 2)]))

theorem physical_matrix_stage_modulus {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {q c G B : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hc : 0 < c) (hG : 0 ≤ G) (hB : 0 ≤ B) (N : ℕ)
    (hbelow : ∀ n : ℕ, N ≤ n → 0 < n → ∀ delta : ℝ,
      0 < delta → delta < 1 / 2 → delta * (n : ℝ) ≤ c →
        (((n : ℝ) * regularizedRate F - G * blockLog n -
          B * delta * (n : ℝ) ^ (1 + q) * (blockLog n) ^ (1 - q) : ℝ) : EReal) ≤
            setMeasuredDivergence F n (1 - delta)) :
    ∃ K epsilon : ℝ, 0 < K ∧ 0 < epsilon ∧ epsilon ≤ 1 / 2 ∧
      ∀ delta : ℝ, 0 < delta → delta < epsilon →
        0 ≤ regularizedRate F - measuredRateSupremum F (1 - delta) ∧
        regularizedRate F - measuredRateSupremum F (1 - delta) ≤
          K * FiniteStageBootstrap.stageModulus q delta := by
  have hblock : ∀ delta : ℝ, 0 < delta → delta < 1 / 2 → ∀ n : ℕ,
      N ≤ n → 0 < n → delta * (n : ℝ) ≤ c →
      regularizedRate F - measuredRateSupremum F (1 - delta) ≤
        G * blockLog n / (n : ℝ) + B * delta * (n : ℝ) ^ q * (blockLog n) ^ (1 - q) := by
    intro delta hd hdhalf n hnN hn hwindow
    have ha0 : 0 < 1 - delta := by linarith
    have ha1 : 1 - delta < 1 := by linarith
    have hf := physical_setMeasuredDivergence_finite hF hn ha0 ha1
    have hl := EReal.toReal_le_toReal (hbelow n hnN hn delta hd hdhalf hwindow)
      (EReal.coe_ne_bot _) hf.1
    simp only [EReal.toReal_coe] at hl
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsup := (div_le_iff₀ hnR).mp (physical_measured_block_le_supremum hF hn ha0 ha1)
    have hp : (n : ℝ) ^ (1 + q) = (n : ℝ) * (n : ℝ) ^ q := by
      rw [Real.rpow_add hnR, Real.rpow_one]
    rw [hp] at hl
    have hid : G * blockLog n / (n : ℝ) + B * delta * (n : ℝ) ^ q * (blockLog n) ^ (1 - q) =
      (G * blockLog n + B * delta * (n : ℝ) ^ q * (blockLog n) ^ (1 - q) * (n : ℝ)) / (n : ℝ) := by
      field_simp [hnR.ne'] <;> ring
    rw [hid]
    apply (le_div_iff₀ hnR).mpr
    nlinarith
  obtain ⟨K, epsilon, hK, hepsilon, hhalf, hm⟩ :=
    FiniteStageBootstrap.scalar_stage_modulus hq hq1 hc hG hB N
      (fun delta => measuredRateSupremum F (1 - delta)) hblock
  refine ⟨K, epsilon, hK, hepsilon, hhalf, ?_⟩
  intro delta hd hde
  exact ⟨sub_nonneg.mpr (physical_measured_below_one_supremum_le_rate hF
    (by linarith : 0 < 1 - delta) (by linarith : 1 - delta < 1)), hm delta hd hde⟩

theorem physical_stage_laplace_of_matrix_modulus {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {q K epsilon : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (hK : 0 < K) (hepsilon : 0 < epsilon)
    (hmodulus : ∀ delta : ℝ, 0 < delta → delta < epsilon →
      regularizedRate F - measuredRateSupremum F (1 - delta) ≤
        K * FiniteStageBootstrap.stageModulus q delta) :
    ∃ N : ℕ, ∀ (n : ℕ) (hn : 0 < n), N ≤ n →
      ∀ (ρ : QMat d n) (hρ : ρ ∈ F.null n) (σ : QMat d n) (hσ : σ ∈ F.alternative n),
        (nsLaw ρ σ (hF.null_states n hn ρ hρ)
          (hF.alternative_positive n hn σ hσ)).expect
          (fun z => Real.exp (-((Real.log 2 / 8) / (n : ℝ)) *
            (nsLikelihood ρ σ z - (n : ℝ) * regularizedRate F))) ≤
              Real.exp (FiniteStageBootstrap.stageLaplaceBudget ((Real.log 2 / 8) * K)
                (FiniteStageBootstrap.stageGamma q) n) := by
  let N := Nat.ceil (1 / (8 * epsilon)) + 1
  refine ⟨N, ?_⟩
  intro n hn hnN ρ hρ σ hσ
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let delta := 1 / (8 * (n : ℝ))
  let t := (Real.log 2 / 8) / (n : ℝ)
  have hd : 0 < delta := by dsimp [delta]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hnCeil : (Nat.ceil (1 / (8 * epsilon)) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnN
  have hceil : 1 / (8 * epsilon) ≤ (Nat.ceil (1 / (8 * epsilon)) : ℝ) := Nat.le_ceil _
  have hsmall : delta < epsilon := by
    have hinv : 1 / (8 * epsilon) < (n : ℝ) := by linarith
    have hprod := (div_lt_iff₀ (show 0 < 8 * epsilon by positivity)).mp hinv
    dsimp [delta]
    apply (div_lt_iff₀ (by positivity : 0 < 8 * (n : ℝ))).mpr
    nlinarith
  have hdhalf : delta ≤ 1 / 8 := by
    dsimp [delta]
    apply (div_le_iff₀ (by positivity : 0 < 8 * (n : ℝ))).mpr
    nlinarith
  have horder : t / Real.log 2 = delta := by
    dsimp [t, delta]
    field_simp [hnR.ne', hlog.ne'] <;> ring
  have hLap := physical_lower_laplace_actual_measured_rate hF hn hρ hσ ht
    (by rw [horder]; linarith)
  rw [horder] at hLap
  have hm := hmodulus delta hd hsmall
  have hs := FiniteStageBootstrap.stageModulus_inverse_eight hq hq1
    (Nat.succ_le_of_lt hn)
  change FiniteStageBootstrap.stageModulus q delta ≤ _ at hs
  refine hLap.trans (Real.exp_le_exp.mpr ?_)
  calc
    _ ≤ t * (n : ℝ) * (K * FiniteStageBootstrap.stageModulus q delta) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = ((Real.log 2 / 8) * K) * FiniteStageBootstrap.stageModulus q delta := by
      dsimp [t]
      field_simp [hnR.ne'] <;> ring
    _ ≤ ((Real.log 2 / 8) * K) *
        ((n : ℝ) ^ (-FiniteStageBootstrap.stageGamma q) *
          (blockLog n) ^ (FiniteStageBootstrap.stageGamma q)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by unfold FiniteStageBootstrap.stageLaplaceBudget; ring

def PhysicalFiniteStage {d : ℕ} (F : QuantumFamilies d) (G q : ℝ) : Prop :=
  ∃ B c : ℝ, ∃ N : ℕ, 0 < B ∧ 0 < c ∧ c ≤ 1 / 2 ∧ 1 ≤ N ∧
    ∀ n : ℕ, N ≤ n → ∀ delta : ℝ, 0 < delta → delta * (n : ℝ) ≤ c →
      (((n : ℝ) * regularizedRate F - G * blockLog n -
        B * delta * (n : ℝ) ^ (1 + q) * (blockLog n) ^ (1 - q) : ℝ) : EReal) ≤
          setMeasuredDivergence F n (1 - delta) ∧
      setSandwichedDivergence F n (1 + delta) ≤
        (((n : ℝ) * regularizedRate F + G * blockLog n +
          B * delta * (n : ℝ) ^ (1 + q) * (blockLog n) ^ (1 - q) : ℝ) : EReal)

private theorem stageLengthPower_ge_length {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ≤ FiniteStageBootstrap.stageLengthPower gamma n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hp := Real.one_le_rpow hn1 (show 0 ≤ 1 - gamma by linarith)
  have hL := Real.one_le_rpow (blockLog_ge_one hn) hgamma
  have hid : (n : ℝ) ^ (2 - gamma) = (n : ℝ) * (n : ℝ) ^ (1 - gamma) := by
    rw [show 2 - gamma = 1 + (1 - gamma) by ring, Real.rpow_add hnR, Real.rpow_one]
  unfold FiniteStageBootstrap.stageLengthPower
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_left hp hnR.le,
    mul_le_mul_of_nonneg_left hL
      (mul_nonneg hnR.le (Real.rpow_nonneg hnR.le (1 - gamma)))]

theorem physical_matrix_finite_stage_step {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {G q : ℝ} (hG : 0 ≤ G)
    (hGpinch : EndpointPetzCoefficient.pinchingCoefficient d ≤ G)
    (hq : 0 < q) (hq1 : q ≤ 1) (hstage : PhysicalFiniteStage F G q) :
    PhysicalFiniteStage F G (FiniteStageBootstrap.nextStage q) := by
  obtain ⟨B, c, N, hB, hc, hchalf, hN, hb⟩ := hstage
  have hbelow : ∀ n : ℕ, N ≤ n → 0 < n → ∀ delta : ℝ,
      0 < delta → delta < 1 / 2 → delta * (n : ℝ) ≤ c →
      (((n : ℝ) * regularizedRate F - G * blockLog n -
        B * delta * (n : ℝ) ^ (1 + q) * (blockLog n) ^ (1 - q) : ℝ) : EReal) ≤
          setMeasuredDivergence F n (1 - delta) := by
    intro n hnN hn delta hd hdhalf hw
    exact (hb n hnN delta hd hw).1
  obtain ⟨K, epsilon, hK, hepsilon, hehalf, hmod⟩ :=
    physical_matrix_stage_modulus hF hq hq1 hc hG hB.le N hbelow
  obtain ⟨N0, hLap⟩ := physical_stage_laplace_of_matrix_modulus hF hq hq1 hK hepsilon
    (fun delta hd hde => (hmod delta hd hde).2)
  obtain ⟨C, hC, hr, hgrowth⟩ := physical_fixed_growth_entropy_rate_bounds hF
  let zeta := Real.log 2 / 8
  let A := zeta * K
  let gamma := FiniteStageBootstrap.stageGamma q
  let P := FiniteStageBootstrap.stagePetzCoefficient C A zeta
  let Q := P * (1 + G * FiniteStageBootstrap.stageLogCoefficient)
  let Bnext := Q + 2 * C + 1
  let cnext := FiniteStageBootstrap.stagePetzWindow C A zeta
  have hzeta : 0 < zeta := by dsimp [zeta]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hgamma := FiniteStageBootstrap.stageGamma_bounds hq hq1
  have hg0 : 0 < gamma := hgamma.2.1
  have hg1 : gamma ≤ 1 := hgamma.2.2.1.le
  have hconst := FiniteStageBootstrap.stagePetz_constants (C := C) hA hzeta
  have hP : 0 < P := hconst.1
  have hD : 0 ≤ FiniteStageBootstrap.stageLogCoefficient := by
    unfold FiniteStageBootstrap.stageLogCoefficient; positivity
  have hPQ : P ≤ Q := by dsimp [Q]; nlinarith [mul_nonneg hG hD]
  have hQ : 0 ≤ Q := hP.le.trans hPQ
  have hBnext : 0 < Bnext := by dsimp [Bnext]; linarith
  obtain ⟨N1, hsmall⟩ := Filter.eventually_atTop.mp
    (FiniteStageBootstrap.stageLaplaceBudget_eventually_le_one hA hg0)
  let Nnext := max 1 (max N0 N1)
  refine ⟨Bnext, cnext, Nnext, hBnext, hconst.2.1, hconst.2.2, le_max_left _ _, ?_⟩
  intro n hnN delta hd hwindow
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hnN
  have hn : 0 < n := by omega
  have hn0 : N0 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hnN)
  have hnb : N1 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hnN)
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnOne : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
  have hdhalf : delta ≤ 1 / 2 := by have hh := hwindow.trans hconst.2.2; nlinarith
  have hcenter : -(C * (n : ℝ)) ≤ (n : ℝ) * regularizedRate F := by
    have hh : -C ≤ regularizedRate F := (neg_le_neg hr).trans (neg_abs_le _)
    nlinarith [mul_le_mul_of_nonneg_left hh hnR]
  have hdom : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ) := by
    intro ρ hρ σ hσ
    simpa only [complex_real_smul] using (hgrowth n hn ρ hρ σ hσ).1
  have hlower : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      (((n : ℝ) * regularizedRate F - P * delta *
        FiniteStageBootstrap.stageLengthPower gamma n : ℝ) : EReal) ≤
          petzDivergence ρ σ (1 - delta) := by
    intro ρ hρ σ hσ
    exact (FiniteStageBootstrap.matrix_stage_petz_bounds
      (hF.null_states n hn ρ hρ) (hF.alternative_positive n hn σ hσ)
      hC hA hzeta le_rfl hg0 hg1 hn1 (hdom ρ hρ σ hσ) hcenter
      (physical_pair_mean_surplus_nonneg hF hn hρ hσ)
      (hsmall n hnb) (hLap n hn hn0 ρ hρ σ hσ) hd hwindow).1
  have hupper : ∀ ρ σ : QMat d n, IsExactMinimizer F ρ σ →
      petzDivergence ρ σ (1 + delta) ≤
        (((n : ℝ) * regularizedRate F + G * blockLog n +
          Q * delta * FiniteStageBootstrap.stageLengthPower gamma n : ℝ) : EReal) := by
    intro ρ σ hmin
    have hm := physical_every_exactMinimizer_mean_gap hF hn hmin
    have hgap := hm.2.trans ((EndpointPetzCoefficient.pinchingOverhead_le_blockLog d hn1).trans
      (mul_le_mul_of_nonneg_right hGpinch (blockLog_nonneg n)))
    exact FiniteStageBootstrap.matrix_stage_petz_mean_bounded
      (hF.null_states n hn ρ hmin.1) (hF.alternative_positive n hn σ hmin.2.1)
      hC hA hG hzeta le_rfl hg0 hg1 hn1 (hdom ρ hmin.1 σ hmin.2.1) hcenter
      hm.1 hgap (hsmall n hnb) (hLap n hn hn0 ρ hmin.1 σ hmin.2.1) hd hwindow
  have hW := stageLengthPower_ge_length hg0.le hg1 hn1
  have hW0 : 0 ≤ FiniteStageBootstrap.stageLengthPower gamma n := hnR.trans hW
  have hs := physical_set_bounds_of_petz hF hn (le_abs_self _ |>.trans hr)
    (fun ρ hρ σ hσ => (hgrowth n hn ρ hρ σ hσ).2.1) hGpinch
    (by positivity : 0 ≤ P * delta * FiniteStageBootstrap.stageLengthPower gamma n)
    hd hdhalf hlower hupper
  have hpad : P * delta * FiniteStageBootstrap.stageLengthPower gamma n +
      2 * C * delta * (n : ℝ) ≤
        Bnext * delta * FiniteStageBootstrap.stageLengthPower gamma n := by
    have hmain := mul_le_mul_of_nonneg_right hPQ (mul_nonneg hd.le hW0)
    have htail := mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ 2 * C * delta)
    dsimp [Bnext]
    nlinarith [mul_nonneg hd.le hW0]
  have hpad' : Q * delta * FiniteStageBootstrap.stageLengthPower gamma n ≤
      Bnext * delta * FiniteStageBootstrap.stageLengthPower gamma n := by
    have hh : Q ≤ Bnext := by dsimp [Bnext]; linarith
    calc
      _ = Q * (delta * FiniteStageBootstrap.stageLengthPower gamma n) := by ring
      _ ≤ Bnext * (delta * FiniteStageBootstrap.stageLengthPower gamma n) :=
        mul_le_mul_of_nonneg_right hh (mul_nonneg hd.le hW0)
      _ = _ := by ring
  have hid := FiniteStageBootstrap.stageLengthPower_nextStage hq n
  change FiniteStageBootstrap.stageLengthPower gamma n = _ at hid
  constructor
  · have hh : (((n : ℝ) * regularizedRate F - G * blockLog n -
        Bnext * delta * FiniteStageBootstrap.stageLengthPower gamma n : ℝ) : EReal) ≤
          setMeasuredDivergence F n (1 - delta) :=
      (EReal.coe_le_coe (by nlinarith)).trans hs.1
    simpa only [hid, mul_assoc] using hh
  · have hh : setSandwichedDivergence F n (1 + delta) ≤
        (((n : ℝ) * regularizedRate F + G * blockLog n +
          Bnext * delta * FiniteStageBootstrap.stageLengthPower gamma n : ℝ) : EReal) :=
      hs.2.trans (EReal.coe_le_coe (by nlinarith))
    simpa only [hid, mul_assoc] using hh

theorem physical_three_finite_stage_baseline {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ G : ℝ, 0 ≤ G ∧
      EndpointPetzCoefficient.pinchingCoefficient d ≤ G ∧ PhysicalFiniteStage F G (1 / 4) := by
  obtain ⟨G, B, c, hG, hGpinch, hB, hc, hchalf, hb⟩ := physical_quadratic_set_baseline hF
  have hbase : PhysicalFiniteStage F G 1 := by
    refine ⟨B, c, 1, hB, hc, hchalf, le_rfl, ?_⟩
    intro n hn delta hd hw
    have hh := hb n (by omega) delta hd hw
    simpa only [show (1 + (1 : ℝ)) = 2 by norm_num, Real.rpow_two,
      sub_self, Real.rpow_zero, mul_one] using hh
  have hhalf := physical_matrix_finite_stage_step hF hG hGpinch
    (by norm_num : (0 : ℝ) < 1) (le_rfl : (1 : ℝ) ≤ 1) hbase
  have hehalf : FiniteStageBootstrap.nextStage 1 = 1 / 2 :=
    FiniteStageBootstrap.three_finite_stage_exponents.1
  rw [hehalf] at hhalf
  have hthird := physical_matrix_finite_stage_step hF hG hGpinch
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hhalf
  rw [FiniteStageBootstrap.three_finite_stage_exponents.2.1] at hthird
  have hquarter := physical_matrix_finite_stage_step hF hG hGpinch
    (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num : (1 / 3 : ℝ) ≤ 1) hthird
  rw [FiniteStageBootstrap.three_finite_stage_exponents.2.2] at hquarter
  exact ⟨G, hG, hGpinch, hquarter⟩

theorem physical_measured_lower_of_matrix_modulus {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {K epsilon : ℝ} (hK : 0 < K) (hepsilon : 0 < epsilon)
    (hmodulus : ∀ delta : ℝ, 0 < delta → delta < epsilon →
      regularizedRate F - measuredRateSupremum F (1 - delta) ≤
        K * delta * (logTwo (1 / delta)) ^ 3) :
    ∃ C G : ℝ, 0 ≤ C ∧ 0 ≤ G ∧ ∀ n : ℕ, 0 < n → ∀ delta : ℝ,
      0 < delta → delta < epsilon → delta ≤ 1 / 2 →
      (((n : ℝ) * regularizedRate F - G * blockLog n -
        K * delta * (n : ℝ) * (logTwo (1 / delta)) ^ 3 -
          2 * C * delta * (n : ℝ) : ℝ) : EReal) ≤ setMeasuredDivergence F n (1 - delta) := by
  obtain ⟨C, hC, hr, hgrowth⟩ := physical_fixed_growth_entropy_rate_bounds hF
  let G := max 0 (EndpointPetzCoefficient.pinchingCoefficient d)
  refine ⟨C, G, hC, le_max_left _ _, ?_⟩
  intro n hn delta hd hde hdhalf
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ha0 : 0 < 1 - delta := by linarith
  have ha1 : 1 - delta < 1 := by linarith
  have hL := EndpointModulus.inverseLog_ge_one hd hdhalf
  change 1 ≤ logTwo (1 / delta) at hL
  have hL0 : 0 ≤ logTwo (1 / delta) := by linarith
  have hP : 0 ≤ K * delta * (n : ℝ) * (logTwo (1 / delta)) ^ 3 := by positivity
  have hrate : (n : ℝ) * regularizedRate F -
      K * delta * (n : ℝ) * (logTwo (1 / delta)) ^ 3 ≤
        (n : ℝ) * measuredRateSupremum F (1 - delta) := by
    have hh := mul_le_mul_of_nonneg_left (hmodulus delta hd hde) hnR
    nlinarith
  have hlow : (((n : ℝ) * regularizedRate F -
      K * delta * (n : ℝ) * (logTwo (1 / delta)) ^ 3 -
        2 * C * delta * (n : ℝ) : ℝ) : EReal) ≤ setSandwichedDivergence F n (1 - delta) := by
    apply le_sInf
    rintro x ⟨ρ, hρ, σ, hσ, rfl⟩
    have hp := (EReal.coe_le_coe hrate).trans
      (physical_pair_petz_ge_actual_measured_rate hF hn hρ hσ (by linarith) ha1)
    exact physical_pair_sandwiched_lower_of_petz hF hn hρ hσ (le_abs_self _ |>.trans hr)
      (hgrowth n hn ρ hρ σ hσ).2.1 hP hd hdhalf hp
  have hg := (EndpointPetzCoefficient.pinchingOverhead_le_blockLog d
    (Nat.succ_le_of_lt hn)).trans
      (mul_le_mul_of_nonneg_right (le_max_right 0 _) (blockLog_nonneg n))
  have hh := EReal.sub_le_sub hlow (EReal.coe_le_coe hg)
  rw [← EReal.coe_sub] at hh
  convert hh.trans
    (PermutationMeasured.physical_set_sandwich_sub_pinchingOverhead_le_measured hF hn ha0 ha1)
      using 1 <;> congr 1 <;> ring

theorem physical_testing_lower_of_matrix_modulus {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {K epsilon : ℝ} (hK : 0 < K) (hepsilon : 0 < epsilon)
    (hmodulus : ∀ delta : ℝ, 0 < delta → delta < epsilon →
      regularizedRate F - measuredRateSupremum F (1 - delta) ≤
        K * delta * (logTwo (1 / delta)) ^ 3)
    {error : ℝ} (herror0 : 0 < error) (herror1 : error < 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 0 < n →
      setTestingDivergence F n error ≠ ⊤ ∧ setTestingDivergence F n error ≠ ⊥ ∧
        (n : ℝ) * regularizedRate F - B * testingRemainder n ≤
          (setTestingDivergence F n error).toReal := by
  obtain ⟨C, G, hC, hG, hbelow⟩ :=
    physical_measured_lower_of_matrix_modulus hF hK hepsilon hmodulus
  let Lerror := -logTwo error
  have hLerror : 0 ≤ Lerror := by
    dsimp [Lerror, logTwo]
    exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
      (Real.log_nonpos herror0.le herror1.le) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
  let J := max (1 / epsilon) 2 + 1
  let N := Nat.ceil (J ^ 2) + 1
  let B0 := G + 64 * K + 2 * C + Lerror + 1
  have hB0 : 0 < B0 := by dsimp [B0]; positivity
  have hlarge : ∀ n : ℕ, 0 < n → N ≤ n →
      (n : ℝ) * regularizedRate F - B0 * testingRemainder n ≤
        (setTestingDivergence F n error).toReal := by
    intro n hn hnN
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hR := testingRemainder_ge_one hn
    have hRp : 0 < testingRemainder n := by linarith
    have hrad := matrix_testing_radius_costs hn
    have hJ : 0 < J := by dsimp [J]; have hh := le_max_right (1 / epsilon) 2; linarith
    have hceil : J ^ 2 ≤ (Nat.ceil (J ^ 2) : ℝ) := Nat.le_ceil _
    have hnceil : (Nat.ceil (J ^ 2) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnN
    have hL := blockLog_ge_one (Nat.succ_le_of_lt hn)
    have hLcube : 1 ≤ (blockLog n) ^ 3 := one_le_pow₀ hL
    have hRsq := converse_testingRemainder_sq n
    have hRJ : J < testingRemainder n := by
      nlinarith [mul_le_mul_of_nonneg_left hLcube hnR.le]
    let delta := 1 / testingRemainder n
    have hd : 0 < delta := by dsimp [delta]; positivity
    have hde : delta < epsilon := by
      have hReps : 1 / epsilon < testingRemainder n := by
        have hh := le_max_left (1 / epsilon) 2
        dsimp [J] at hRJ
        linarith
      have hh := (div_lt_iff₀ hepsilon).mp hReps
      dsimp [delta]
      apply (div_lt_iff₀ hRp).mpr
      nlinarith
    have hdhalf : delta ≤ 1 / 2 := by
      have hh := le_max_right (1 / epsilon) 2
      dsimp [J] at hRJ
      dsimp [delta]
      apply (div_le_iff₀ hRp).mpr
      linarith
    have hInv : 1 / delta = testingRemainder n := by dsimp [delta]; field_simp [hRp.ne']
    have hm := hbelow n hn delta hd hde hdhalf
    rw [hInv] at hm
    have hcorrect : -Lerror * testingRemainder n ≤ ((1 - delta) / delta) * logTwo error := by
      have hh := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (show 1 - delta ≤ 1 by linarith) hd.le) hLerror
      rw [hInv] at hh
      dsimp [Lerror] at hh ⊢
      nlinarith
    have hone := Testing.setTestingDivergence_lower_of_measured hF hn herror0 herror1
      (by linarith : 0 < 1 - delta) (by linarith : 1 - delta < 1)
    rw [show 1 - (1 - delta) = delta by ring] at hone
    have hsum := add_le_add hm (EReal.coe_le_coe hcorrect)
    rw [← EReal.coe_add] at hsum
    have htest := hsum.trans hone
    have hcost : G * blockLog n + K * delta * (n : ℝ) * (logTwo (testingRemainder n)) ^ 3 +
        2 * C * delta * (n : ℝ) + Lerror * testingRemainder n ≤ B0 * testingRemainder n := by
      have hg := mul_le_mul_of_nonneg_left hrad.2.2.1 hG
      have hk := mul_le_mul_of_nonneg_left hrad.2.2.2.2 hK.le
      have hc := mul_le_mul_of_nonneg_left hrad.2.2.2.1 (by positivity : 0 ≤ 2 * C)
      dsimp [delta, B0]
      simp only [div_eq_mul_inv, one_div] at hk hc ⊢
      nlinarith
    have hfinal : (((n : ℝ) * regularizedRate F - B0 * testingRemainder n : ℝ) : EReal) ≤
        setTestingDivergence F n error :=
      (EReal.coe_le_coe (by nlinarith)).trans htest
    have hf := physical_setTestingDivergence_finite hF hn herror0.le herror1
    simpa only [EReal.toReal_coe] using
      EReal.toReal_le_toReal hfinal (EReal.coe_ne_bot _) hf.1
  obtain ⟨Bsmall, hBsmall, hsmall⟩ := physical_testing_finite_base hF N herror0.le herror1
  let B := max B0 Bsmall
  refine ⟨B, hB0.trans_le (le_max_left _ _), ?_⟩
  intro n hn
  have hf := physical_setTestingDivergence_finite hF hn herror0.le herror1
  have hR := (testingRemainder_ge_one hn).trans' (by norm_num : (0 : ℝ) ≤ 1)
  refine ⟨hf.1, hf.2, ?_⟩
  by_cases hnN : N ≤ n
  · have hb := mul_le_mul_of_nonneg_right (le_max_left B0 Bsmall) hR
    have hh := hlarge n hn hnN
    dsimp [B]
    linarith
  · have hh := (abs_le.mp (hsmall n hn (by omega))).1
    have hb := mul_le_mul_of_nonneg_right (le_max_right B0 Bsmall) hR
    dsimp [B]
    linarith

set_option maxHeartbeats 1000000 in

theorem physical_single_coefficient_measured_endpoint {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ G : ℝ, ∃ M N : ℕ, ∃ c : ℝ,
      0 ≤ G ∧ EndpointPetzCoefficient.pinchingCoefficient d ≤ G ∧
      1 ≤ M ∧ 1 ≤ N ∧ 0 < c ∧ c ≤ 1 / 2 ∧
      ∀ n : ℕ, N ≤ n → ∀ delta : ℝ, 0 < delta → delta * (n : ℝ) * blockLog n ≤ c →
        (((n : ℝ) * regularizedRate F - G * blockLog n -
          (delta * (n : ℝ)) * ((M : ℝ) * (blockLog n) ^ 3) : ℝ) : EReal) ≤
            setMeasuredDivergence F n (1 - delta) := by
  obtain ⟨G, hG, hGpinch, B, cStar, Nstar, hB, hcStar0, hcStarHalf, hNstar, hb⟩ :=
    physical_three_finite_stage_baseline hF
  obtain ⟨C, hC, hrC, hrec⟩ := physical_narrow_petz_recurrence hF
  obtain ⟨T, hT, hrT, hgrowth⟩ := physical_fixed_growth_entropy_rate_bounds hF
  let zeta := min (Real.log 2 / 8) (min (1 / (100 * (C + 1))) (8 * Real.log 2 * cStar))
  let A := 32 * zeta * G
  let D := zeta ^ 2 / Real.log 2
  let gamma := 8 * zeta * (C + 1) / 3
  let K0 := EndpointPetzCoefficient.negativeCoefficient G zeta + 2 * T
  let loss := fun n : ℕ => fun delta : ℝ =>
    (n : ℝ) * regularizedRate F - (setMeasuredDivergence F n (1 - delta)).toReal
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hzeta : 0 < zeta := by dsimp [zeta]; positivity
  have hzetaSmall : zeta ≤ Real.log 2 / 8 := min_le_left _ _
  have hzetaC : zeta ≤ 1 / (100 * (C + 1)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hzetaStar : zeta ≤ 8 * Real.log 2 * cStar :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hgamma : 0 ≤ gamma := by dsimp [gamma]; positivity
  have hgammaSmall : gamma ≤ 2 / 75 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 100 * (C + 1))).mp hzetaC
    dsimp [gamma]
    nlinarith
  have hwindowStar : FixedMInduction.endpointWindow zeta ≤ cStar := by
    unfold FixedMInduction.endpointWindow
    apply (div_le_iff₀ (by positivity : 0 < 8 * Real.log 2)).mpr
    nlinarith
  have hwindowHalf : FixedMInduction.endpointWindow zeta ≤ 1 / 2 :=
    hwindowStar.trans hcStarHalf
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hKneg : 0 ≤ EndpointPetzCoefficient.negativeCoefficient G zeta := by
    unfold EndpointPetzCoefficient.negativeCoefficient EndpointPetzCoefficient.tailConstant
    positivity
  obtain ⟨Nfixed, hNfixed, hguards⟩ :=
    NarrowGuard.exists_uniform_narrow_guards hC hG hzeta hgammaSmall
  have hbaseline : ∀ n : ℕ, Nstar ≤ n → ∀ delta : ℝ,
      0 < delta → delta * (n : ℝ) ≤ cStar →
      loss n delta ≤ G * blockLog n + (delta * (n : ℝ)) *
        (B * (n : ℝ) ^ (1 / 4 : ℝ) * (blockLog n) ^ (3 / 4 : ℝ)) := by
    intro n hnN delta hd hwindow
    have hn : 0 < n := by omega
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (hNstar.trans hnN)
    have hdhalf : delta ≤ 1 / 2 := by nlinarith
    have hf := physical_setMeasuredDivergence_finite hF hn
      (by linarith : 0 < 1 - delta) (by linarith : 1 - delta < 1)
    have hl := EReal.toReal_le_toReal (hb n hnN delta hd hwindow).1
      (EReal.coe_ne_bot _) hf.1
    simp only [EReal.toReal_coe] at hl
    have hp : (n : ℝ) ^ (1 + (1 / 4 : ℝ)) = (n : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) := by
      rw [Real.rpow_add hnR, Real.rpow_one]
    rw [hp, show 1 - (1 / 4 : ℝ) = 3 / 4 by norm_num] at hl
    dsimp [loss]
    nlinarith only [hl]
  have hstep : ∀ M n : ℕ, 1 ≤ M → M ^ 2 < n → Nfixed ≤ n →
      32 * Nstar ≤ n →
      loss (n / 16) (FixedMInduction.curvatureOrder zeta n) ≤ G * blockLog (n / 16) +
        (FixedMInduction.curvatureOrder zeta n * ((n / 16 : ℕ) : ℝ)) *
          ((M : ℝ) * (blockLog (n / 16)) ^ 3) →
      ∀ delta : ℝ, 0 < delta →
        delta * (n : ℝ) * blockLog n ≤ FixedMInduction.endpointWindow zeta →
      loss n delta ≤ G * blockLog n + (delta * (n : ℝ)) *
        (FixedMInduction.curvatureFactor A D gamma M n * (M : ℝ) *
          (blockLog (n / 16)) ^ 3 + K0 * (blockLog n) ^ 2) := by
    intro M n hM hnM hnFixed hnStar hsmaller delta hd hwindow
    have hn32 : 32 ≤ n := hNfixed.trans hnFixed
    have hn : 0 < n := by omega
    have hn1 : 1 ≤ n := by omega
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
    have hmN : Nstar ≤ n / 16 := by omega
    have hm1 : 1 ≤ n / 16 := hNstar.trans hmN
    have hmp : 0 < n / 16 := by omega
    have hmR : 1 ≤ ((n / 16 : ℕ) : ℝ) := by exact_mod_cast hm1
    have hLm := blockLog_ge_one hm1
    have hw := FixedMInduction.curvatureOrder_in_smaller_window hn32 hzeta
    have hcurv : 0 < FixedMInduction.curvatureOrder zeta n := hw.1
    have hcurvN : FixedMInduction.curvatureOrder zeta n * ((n / 16 : ℕ) : ℝ) ≤
        FixedMInduction.endpointWindow zeta := by
      have hh := mul_le_mul_of_nonneg_left hLm
        (by positivity : 0 ≤ FixedMInduction.curvatureOrder zeta n * ((n / 16 : ℕ) : ℝ))
      nlinarith only [hh, hw.2]
    have hcurvHalf : FixedMInduction.curvatureOrder zeta n ≤ 1 / 2 := by
      nlinarith only [hmR, hcurv, hcurvN.trans hwindowHalf]
    have hfm := physical_setMeasuredDivergence_finite hF hmp
      (by linarith : 0 < 1 - FixedMInduction.curvatureOrder zeta n)
      (by linarith [hw.1] : 1 - FixedMInduction.curvatureOrder zeta n < 1)
    have hsmallRaw :
        (((((n / 16 : ℕ) : ℝ) * regularizedRate F - G * blockLog (n / 16) -
          (FixedMInduction.curvatureOrder zeta n * ((n / 16 : ℕ) : ℝ)) *
            ((M : ℝ) * (blockLog (n / 16)) ^ 3)) : ℝ) : EReal) ≤
              setMeasuredDivergence F (n / 16) (1 - FixedMInduction.curvatureOrder zeta n) := by
      rw [← EReal.coe_toReal hfm.1 hfm.2]
      apply EReal.coe_le_coe
      dsimp [loss] at hsmaller
      linarith
    have hg := hguards M n hnM hnFixed
    have ha0 := EndpointCurvature.narrowBlockBudget_nonneg hG hzeta M n hn32
    have hH0 : 0 ≤ EndpointCurvature.narrowFactor C G M zeta n := by
      unfold EndpointCurvature.narrowFactor
      positivity
    have hdhalf : delta ≤ 1 / 2 := by
      have hLn := blockLog_ge_one hn1
      have hh := mul_le_mul_of_nonneg_left hLn (by positivity : 0 ≤ delta * (n : ℝ))
      nlinarith [hwindow.trans hwindowHalf]
    have hp := hrec G zeta hG hGpinch hzeta hzetaSmall M n hn32 hsmallRaw
      hg.1 hg.2.1 delta hd (by linarith : delta < 1) hwindow
    have hcost0 : 0 ≤ (delta * (n : ℝ)) *
        (EndpointCurvature.narrowFactor C G M zeta n * (M : ℝ) * (blockLog (n / 16)) ^ 3 +
          EndpointPetzCoefficient.negativeCoefficient G zeta * (blockLog n) ^ 2) := by positivity
    have hs := physical_set_bounds_of_petz hF hn (le_abs_self _ |>.trans hrT)
      (fun ρ hρ σ hσ => (hgrowth n hn ρ hρ σ hσ).2.1) hGpinch hcost0 hd hdhalf hp.1 hp.2
    have hf := physical_setMeasuredDivergence_finite hF hn
      (by linarith : 0 < 1 - delta) (by linarith : 1 - delta < 1)
    have hsR := EReal.toReal_le_toReal hs.1 (EReal.coe_ne_bot _) hf.1
    simp only [EReal.toReal_coe] at hsR
    have hfactor : EndpointCurvature.narrowFactor C G M zeta n ≤
        FixedMInduction.curvatureFactor A D gamma M n := hg.2.2
    have hmain := mul_le_mul_of_nonneg_right hfactor
      (by positivity : 0 ≤ (M : ℝ) * (blockLog (n / 16)) ^ 3)
    have hL := blockLog_ge_one hn1
    have hLsq : 1 ≤ (blockLog n) ^ 2 := one_le_pow₀ hL
    have herr : EndpointPetzCoefficient.negativeCoefficient G zeta * (blockLog n) ^ 2 +
        2 * T ≤ K0 * (blockLog n) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hLsq (by positivity : 0 ≤ 2 * T)
      dsimp [K0]
      nlinarith only [hh]
    have hpad := mul_le_mul_of_nonneg_left (add_le_add hmain herr)
      (by positivity : 0 ≤ delta * (n : ℝ))
    dsimp [loss]
    nlinarith only [hsR, hpad]
  obtain ⟨M, hM, hbound⟩ := FixedMInduction.fixed_coefficient_induction loss
    (B := B) (G := G) (A := A) (D := D) (gamma := gamma) (K0 := K0)
    hB.le hA hD hgamma hgammaSmall hzeta hwindowStar Nstar Nfixed hNstar hbaseline hstep
  refine ⟨G, M, Nstar, FixedMInduction.endpointWindow zeta, hG, hGpinch,
    hM, hNstar, by unfold FixedMInduction.endpointWindow; positivity, hwindowHalf, ?_⟩
  intro n hnN delta hd hwindow
  have hn : 0 < n := by omega
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (hNstar.trans hnN)
  have hL := blockLog_ge_one (hNstar.trans hnN)
  have hdhalf : delta ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ delta * (n : ℝ))
    nlinarith [hwindow.trans hwindowHalf]
  have hf := physical_setMeasuredDivergence_finite hF hn
    (by linarith : 0 < 1 - delta) (by linarith : 1 - delta < 1)
  have hl := hbound n hnN delta hd hwindow
  rw [← EReal.coe_toReal hf.1 hf.2]
  apply EReal.coe_le_coe
  dsimp [loss] at hl
  linarith

theorem physical_actual_logarithmic_rate_modulus {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ K epsilon : ℝ,
      0 < K ∧ 0 < epsilon ∧ epsilon ≤ 1 / 2 ∧
      ∀ delta : ℝ, 0 < delta → delta < epsilon →
        0 ≤ regularizedRate F - measuredRateSupremum F (1 - delta) ∧
        regularizedRate F - measuredRateSupremum F (1 - delta) ≤
          K * delta * (logTwo (1 / delta)) ^ 3 := by
  obtain ⟨G, M, N, c, hG, hGp, hM, hN, hc, hchalf, hb⟩ :=
    physical_single_coefficient_measured_endpoint hF
  exact physical_matrix_modulus_of_narrow_measured hF hc hG (Nat.cast_nonneg M) N
    (fun n hnN hn delta hd hdhalf hw => by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hb n hnN delta hd hw)

theorem physical_universal_logarithmic_equipartition {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : UniversalLogarithmicConclusion F := by
  obtain ⟨K, epsilon, hK, hepsilon, hhalf, hmod⟩ := physical_actual_logarithmic_rate_modulus hF
  have hm : ∀ delta : ℝ, 0 < delta → delta < epsilon →
      regularizedRate F - measuredRateSupremum F (1 - delta) ≤
        K * delta * (logTwo (1 / delta)) ^ 3 :=
    fun delta hd hde => (hmod delta hd hde).2
  constructor
  · intro error herror0 herror1
    obtain ⟨Bu, hBu, hu⟩ := physical_testing_upper_of_matrix_modulus hF hK hepsilon hm herror0.le herror1
    obtain ⟨Bl, hBl, hl⟩ := physical_testing_lower_of_matrix_modulus hF hK hepsilon hm herror0 herror1
    let B := max Bu Bl
    refine ⟨B, hBu.trans_le (le_max_left _ _), ?_⟩
    intro n hn
    have hub := hu n hn
    have hlb := hl n hn
    have hR : 0 ≤ testingRemainder n :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (testingRemainder_ge_one hn)
    have huu := mul_le_mul_of_nonneg_right (le_max_left Bu Bl) hR
    have hll := mul_le_mul_of_nonneg_right (le_max_right Bu Bl) hR
    refine ⟨hub.1, hub.2.1, abs_le.mpr ⟨?_, ?_⟩⟩ <;> dsimp [B] <;> linarith [hub.2.2, hlb.2.2]
  · exact physical_every_minimizer_moment_of_matrix_modulus hF hK hepsilon hm

theorem physical_fixed_error_logarithmic_testing {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : LogarithmicTestingConclusion F :=
  (physical_universal_logarithmic_equipartition hF).1

theorem physical_every_exact_minimizer_weighted_moment {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : OptimizerMomentConclusion F :=
  (physical_universal_logarithmic_equipartition hF).2

end QuantumProver.Equipartition.FiniteModel.EndpointAssembly
