import Mathlib

noncomputable section

open MeasureTheory Filter Set
open scoped Topology BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.InfiniteRecordReadout

def minimumArgmax4 (v : Fin 4 → ℝ) : Fin 4 :=
  if v 1 ≤ v 0 ∧ v 2 ≤ v 0 ∧ v 3 ≤ v 0 then 0
  else if v 2 ≤ v 1 ∧ v 3 ≤ v 1 then 1
  else if v 3 ≤ v 2 then 2 else 3

theorem le_minimumArgmax4 (v : Fin 4 → ℝ) (j : Fin 4) :
    v j ≤ v (minimumArgmax4 v) := by
  unfold minimumArgmax4
  split_ifs with h0 h1 h2
  · fin_cases j <;> simp_all
  · have h01 : v 0 ≤ v 1 := by
      by_contra h
      have hlt := lt_of_not_ge h
      exact h0 ⟨hlt.le, h1.1.trans hlt.le, h1.2.trans hlt.le⟩
    fin_cases j <;> simp_all
  · have h12 : v 1 ≤ v 2 := by
      by_contra h
      have hlt := lt_of_not_ge h
      exact h1 ⟨hlt.le, h2.trans hlt.le⟩
    have h02 : v 0 ≤ v 2 := by
      by_contra h
      have hlt := lt_of_not_ge h
      exact h0 ⟨h12.trans hlt.le, hlt.le, h2.trans hlt.le⟩
    fin_cases j <;> simp_all
  · have h23 : v 2 ≤ v 3 := le_of_not_ge h2
    have h13 : v 1 ≤ v 3 := by
      by_contra h
      have hlt := lt_of_not_ge h
      exact h1 ⟨h23.trans hlt.le, hlt.le⟩
    have h03 : v 0 ≤ v 3 := by
      by_contra h
      have hlt := lt_of_not_ge h
      exact h0 ⟨h13.trans hlt.le, h23.trans hlt.le, hlt.le⟩
    fin_cases j <;> simp_all

theorem minimumArgmax4_min (v : Fin 4 → ℝ) (j : Fin 4)
    (hj : ∀ k, v k ≤ v j) : minimumArgmax4 v ≤ j := by
  fin_cases j
  · change (∀ k, v k ≤ v 0) at hj
    simp [minimumArgmax4, hj 1, hj 2, hj 3]
  · change (∀ k, v k ≤ v 1) at hj
    have h1 : v 2 ≤ v 1 ∧ v 3 ≤ v 1 := ⟨hj 2, hj 3⟩
    unfold minimumArgmax4
    split_ifs <;> simp_all
  · change (∀ k, v k ≤ v 2) at hj
    have h2 : v 3 ≤ v 2 := hj 3
    unfold minimumArgmax4
    split_ifs <;> simp_all
  · change minimumArgmax4 v ≤ (3 : Fin 4)
    exact Fin.le_last _

theorem minimumArgmax4_eq_of_strict_max (v : Fin 4 → ℝ) (j : Fin 4)
    (hj : ∀ k, k ≠ j → v k < v j) : minimumArgmax4 v = j := by
  by_contra hne
  exact (not_lt_of_ge (le_minimumArgmax4 v j)) (hj _ hne)

theorem measurable_minimumArgmax4 {Ω : Type*} {m : MeasurableSpace Ω}
    (v : Fin 4 → Ω → ℝ) (hv : ∀ j, Measurable[m] (v j)) :
    Measurable[m] (fun ω => minimumArgmax4 (fun j => v j ω)) := by
  unfold minimumArgmax4
  exact Measurable.ite
    ((measurableSet_le (hv 1) (hv 0)).inter
      ((measurableSet_le (hv 2) (hv 0)).inter (measurableSet_le (hv 3) (hv 0))))
    measurable_const
    (Measurable.ite
      ((measurableSet_le (hv 2) (hv 1)).inter (measurableSet_le (hv 3) (hv 1)))
      measurable_const
      (Measurable.ite (measurableSet_le (hv 3) (hv 2)) measurable_const measurable_const))

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

def reportIndicator (J : Ω → Fin 4) (j : Fin 4) : Ω → ℝ :=
  {ω | J ω = j}.indicator (fun _ => 1)

theorem measurable_reportIndicator (J : Ω → Fin 4) (hJ : Measurable J) (j : Fin 4) :
    Measurable (reportIndicator J j) :=
  measurable_const.indicator (hJ (measurableSet_singleton j))

theorem integrable_reportIndicator (μ : Measure Ω) [IsFiniteMeasure μ]
    (J : Ω → Fin 4) (hJ : Measurable J) (j : Fin 4) :
    Integrable (reportIndicator J j) μ :=
  (integrable_const (1 : ℝ)).indicator (hJ (measurableSet_singleton j))

def posterior (μ : Measure Ω) (ℱ : Filtration ℕ m₀) (J : Ω → Fin 4)
    (n : ℕ) (j : Fin 4) : Ω → ℝ :=
  μ[reportIndicator J j | ℱ n]

def finiteReadout (μ : Measure Ω) (ℱ : Filtration ℕ m₀) (J : Ω → Fin 4)
    (n : ℕ) (ω : Ω) : Fin 4 :=
  minimumArgmax4 (fun j => posterior μ ℱ J n j ω)

theorem measurable_finiteReadout (μ : Measure Ω) (ℱ : Filtration ℕ m₀)
    (J : Ω → Fin 4) (n : ℕ) : Measurable[ℱ n] (finiteReadout μ ℱ J n) := by
  exact measurable_minimumArgmax4 _ (fun _ => stronglyMeasurable_condExp.measurable)

theorem ae_tendsto_posterior (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m₀) (hgen : (⨆ n, ℱ n) = m₀)
    (J : Ω → Fin 4) (hJ : Measurable J) :
    ∀ᵐ ω ∂μ, ∀ j, Tendsto (fun n => posterior μ ℱ J n j ω)
      atTop (𝓝 (reportIndicator J j ω)) := by
  rw [ae_all_iff]
  intro j
  apply (integrable_reportIndicator μ J hJ j).tendsto_ae_condExp
  rw [hgen]
  exact (measurable_reportIndicator J hJ j).stronglyMeasurable

theorem ae_eventually_finiteReadout_eq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m₀) (hgen : (⨆ n, ℱ n) = m₀)
    (J : Ω → Fin 4) (hJ : Measurable J) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, finiteReadout μ ℱ J n ω = J ω := by
  filter_upwards [ae_tendsto_posterior μ ℱ hgen J hJ] with ω hω
  have htrue : Tendsto (fun n => posterior μ ℱ J n (J ω) ω) atTop (𝓝 1) := by
    simpa [reportIndicator] using hω (J ω)
  have hlarge : ∀ᶠ n in atTop, (1 / 2 : ℝ) < posterior μ ℱ J n (J ω) ω :=
    htrue.eventually (eventually_gt_nhds (by norm_num))
  have hsmall : ∀ j, ∀ᶠ n in atTop,
      j ≠ J ω → posterior μ ℱ J n j ω < (1 / 2 : ℝ) := by
    intro j
    by_cases hj : j = J ω
    · exact Eventually.of_forall (fun _ h => False.elim (h hj))
    · have hjzero : Tendsto (fun n => posterior μ ℱ J n j ω) atTop (𝓝 0) := by
        simpa [reportIndicator, eq_comm, hj] using hω j
      exact (hjzero.eventually (eventually_lt_nhds (by norm_num))).mono
        (fun _ h _ => h)
  have hall : ∀ᶠ n in atTop, ∀ j,
      j ≠ J ω → posterior μ ℱ J n j ω < (1 / 2 : ℝ) :=
    (eventually_all).2 hsmall
  filter_upwards [hlarge, hall] with n hn hnall
  exact minimumArgmax4_eq_of_strict_max _ _ (fun j hj => (hnall j hj).trans hn)

theorem measurableSet_disagreement (μ : Measure Ω) (ℱ : Filtration ℕ m₀)
    (J : Ω → Fin 4) (hJ : Measurable J) (n : ℕ) :
    MeasurableSet {ω | finiteReadout μ ℱ J n ω ≠ J ω} := by
  exact (measurableSet_eq_fun
    ((measurable_finiteReadout μ ℱ J n).mono (ℱ.le n) le_rfl) hJ).compl

theorem tendsto_disagreement_mass (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m₀) (hgen : (⨆ n, ℱ n) = m₀)
    (J : Ω → Fin 4) (hJ : Measurable J) :
    Tendsto (fun n => μ {ω | finiteReadout μ ℱ J n ω ≠ J ω}) atTop (𝓝 0) := by
  have hlim : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ω ∈ {ω | finiteReadout μ ℱ J n ω ≠ J ω} ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [ae_eventually_finiteReadout_eq μ ℱ hgen J hJ] with ω hω
    exact hω.mono (fun n hn => by simp [hn])
  simpa using tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    MeasurableSet.empty (measurableSet_disagreement μ ℱ J hJ) hlim

theorem tendsto_disagreement_real (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m₀) (hgen : (⨆ n, ℱ n) = m₀)
    (J : Ω → Fin 4) (hJ : Measurable J) :
    Tendsto (fun n => (μ {ω | finiteReadout μ ℱ J n ω ≠ J ω}).toReal)
      atTop (𝓝 0) := by
  exact (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).2
    (tendsto_disagreement_mass μ ℱ hgen J hJ)

theorem finiteReadout_factors_through_prefix (μ : Measure Ω) (ℱ : Filtration ℕ m₀)
    (J : Ω → Fin 4) (n : ℕ) {H : Type*} [mH : MeasurableSpace H]
    (historyMap : Ω → H) (hprefix : ℱ n = mH.comap historyMap) :
    ∃ g : H → Fin 4, Measurable g ∧ finiteReadout μ ℱ J n = g ∘ historyMap := by
  have hm := measurable_finiteReadout μ ℱ J n
  rw [hprefix] at hm
  exact hm.exists_eq_measurable_comp

theorem posSemidef_norm_le_trace {α : Type*} [Fintype α] [DecidableEq α]
    (R : Matrix α α ℂ) (hR : R.PosSemidef) : ‖R‖ ≤ R.trace.re := by
  have hnorm : ‖R‖ = ‖fun i => (hR.isHermitian.eigenvalues i : ℂ)‖ := by
    conv_lhs => rw [hR.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
    rfl
  have ht : R.trace.re = ∑ i, hR.isHermitian.eigenvalues i := by
    rw [hR.isHermitian.trace_eq_sum_eigenvalues]
    simp
  rw [hnorm, ht]
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg
    (fun i _ => hR.eigenvalues_nonneg i))).mpr
  intro i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hR.eigenvalues_nonneg i)]
  exact Finset.single_le_sum (fun k _ => hR.eigenvalues_nonneg k) (Finset.mem_univ i)

variable {d : ℕ}

theorem ae_norm_density_le (μ : Measure Ω) (W : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hpos : ∀ᵐ ω ∂μ, (W ω).PosSemidef)
    (htrace : ∀ᵐ ω ∂μ, (W ω).trace = (d : ℂ)) :
    ∀ᵐ ω ∂μ, ‖W ω‖ ≤ (d : ℝ) := by
  filter_upwards [hpos, htrace] with ω hp ht
  simpa [ht] using posSemidef_norm_le_trace (W ω) hp

theorem integrable_density (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Matrix (Fin d) (Fin d) ℂ) (hW : Measurable W)
    (hpos : ∀ᵐ ω ∂μ, (W ω).PosSemidef)
    (htrace : ∀ᵐ ω ∂μ, (W ω).trace = (d : ℂ)) : Integrable W μ := by
  exact (integrable_const (d : ℝ)).mono' hW.aestronglyMeasurable
    (ae_norm_density_le μ W hpos htrace)

def reportEffect (μ : Measure Ω) (W : Ω → Matrix (Fin d) (Fin d) ℂ)
    (J : Ω → Fin 4) (j : Fin 4) : Matrix (Fin d) (Fin d) ℂ :=
  ∫ ω, {ω | J ω = j}.indicator W ω ∂μ

theorem reportEffect_posSemidef (μ : Measure Ω)
    (W : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hpos : ∀ᵐ ω ∂μ, (W ω).PosSemidef) (J : Ω → Fin 4) (j : Fin 4) :
    (reportEffect μ W J j).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply integral_nonneg_of_ae
  filter_upwards [hpos] with ω hp
  by_cases hj : J ω = j
  · simpa [Set.indicator, hj] using hp.nonneg
  · simp [Set.indicator, hj]

theorem reportEffect_sum (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Matrix (Fin d) (Fin d) ℂ) (hW : Measurable W)
    (hpos : ∀ᵐ ω ∂μ, (W ω).PosSemidef)
    (htrace : ∀ᵐ ω ∂μ, (W ω).trace = (d : ℂ))
    (htotal : (∫ ω, W ω ∂μ) = 1) (J : Ω → Fin 4) (hJ : Measurable J) :
    ∑ j, reportEffect μ W J j = 1 := by
  have hWi := integrable_density μ W hW hpos htrace
  have hJi : ∀ j ∈ (Finset.univ : Finset (Fin 4)),
      Integrable (fun ω => {ω | J ω = j}.indicator W ω) μ := by
    intro j _
    exact hWi.indicator ((measurableSet_singleton j).preimage hJ)
  unfold reportEffect
  rw [← integral_finsetSum _ hJi]
  have heq : (fun ω => ∑ j, {ω | J ω = j}.indicator W ω) = W := by
    funext ω
    simp [Set.indicator, eq_comm]
  rw [heq]
  exact htotal

theorem reportEffect_le_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Matrix (Fin d) (Fin d) ℂ) (hW : Measurable W)
    (hpos : ∀ᵐ ω ∂μ, (W ω).PosSemidef)
    (htrace : ∀ᵐ ω ∂μ, (W ω).trace = (d : ℂ))
    (htotal : (∫ ω, W ω ∂μ) = 1) (J : Ω → Fin 4) (hJ : Measurable J) (j : Fin 4) :
    reportEffect μ W J j ≤ 1 := by
  rw [← reportEffect_sum μ W hW hpos htrace htotal J hJ]
  exact Finset.single_le_sum
    (fun k _ => (reportEffect_posSemidef μ W hpos J k).nonneg) (Finset.mem_univ j)

theorem reportEffect_error_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Matrix (Fin d) (Fin d) ℂ) (hW : Measurable W)
    (hpos : ∀ᵐ ω ∂μ, (W ω).PosSemidef)
    (htrace : ∀ᵐ ω ∂μ, (W ω).trace = (d : ℂ))
    (L J : Ω → Fin 4) (hL : Measurable L) (hJ : Measurable J) (j : Fin 4) :
    ‖reportEffect μ W L j - reportEffect μ W J j‖ ≤
      (d : ℝ) * (μ {ω | L ω ≠ J ω}).toReal := by
  have hmis : MeasurableSet {ω | L ω ≠ J ω} := (measurableSet_eq_fun hL hJ).compl
  have hWi := integrable_density μ W hW hpos htrace
  have hsL : MeasurableSet {ω | L ω = j} := (measurableSet_singleton j).preimage hL
  have hsJ : MeasurableSet {ω | J ω = j} := (measurableSet_singleton j).preimage hJ
  have hLi : Integrable (fun ω => {ω | L ω = j}.indicator W ω) μ := hWi.indicator hsL
  have hJi : Integrable (fun ω => {ω | J ω = j}.indicator W ω) μ := hWi.indicator hsJ
  rw [reportEffect, reportEffect, ← integral_sub hLi hJi]
  calc
    ‖∫ ω, ({ω | L ω = j}.indicator W ω - {ω | J ω = j}.indicator W ω) ∂μ‖
        ≤ ∫ ω, {ω | L ω ≠ J ω}.indicator (fun _ => (d : ℝ)) ω ∂μ := by
      apply norm_integral_le_of_norm_le ((integrable_const (d : ℝ)).indicator hmis)
      filter_upwards [ae_norm_density_le μ W hpos htrace] with ω hn
      by_cases heq : L ω = J ω
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, heq, sub_self, norm_zero, ne_eq,
          not_true_eq_false, ite_false]
        exact le_rfl
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ne_eq, heq, not_false_eq_true,
          ite_true]
        by_cases hl : L ω = j <;> by_cases hj : J ω = j <;>
          simp only [hl, hj, ite_true, ite_false, sub_self, sub_zero, zero_sub,
            norm_neg, norm_zero]
        all_goals first | exact hn | positivity
    _ = (d : ℝ) * (μ {ω | L ω ≠ J ω}).toReal := by
      rw [integral_indicator_const _ hmis]
      simp [measureReal_def, mul_comm]

theorem finiteReadout_effect_error_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m₀) (J : Ω → Fin 4) (hJ : Measurable J)
    (W : Ω → Matrix (Fin d) (Fin d) ℂ) (hW : Measurable W)
    (hpos : ∀ᵐ ω ∂μ, (W ω).PosSemidef)
    (htrace : ∀ᵐ ω ∂μ, (W ω).trace = (d : ℂ)) (n : ℕ) (j : Fin 4) :
    ‖reportEffect μ W (finiteReadout μ ℱ J n) j - reportEffect μ W J j‖ ≤
      (d : ℝ) * (μ {ω | finiteReadout μ ℱ J n ω ≠ J ω}).toReal :=
  reportEffect_error_le μ W hW hpos htrace _ J
    ((measurable_finiteReadout μ ℱ J n).mono (ℱ.le n) le_rfl) hJ j

theorem finiteReadout_euclidean_operator_error_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m₀) (J : Ω → Fin 4) (hJ : Measurable J)
    (W : Ω → Matrix (Fin d) (Fin d) ℂ) (hW : Measurable W)
    (hpos : ∀ᵐ ω ∂μ, (W ω).PosSemidef)
    (htrace : ∀ᵐ ω ∂μ, (W ω).trace = (d : ℂ)) (n : ℕ) (j : Fin 4) :
    ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
      (reportEffect μ W (finiteReadout μ ℱ J n) j - reportEffect μ W J j)‖ ≤
      (d : ℝ) * (μ {ω | finiteReadout μ ℱ J n ω ≠ J ω}).toReal := by
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  exact finiteReadout_effect_error_le μ ℱ J hJ W hW hpos htrace n j

theorem tendsto_finiteReadout_effect (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m₀) (hgen : (⨆ n, ℱ n) = m₀)
    (J : Ω → Fin 4) (hJ : Measurable J)
    (W : Ω → Matrix (Fin d) (Fin d) ℂ) (hW : Measurable W)
    (hpos : ∀ᵐ ω ∂μ, (W ω).PosSemidef)
    (htrace : ∀ᵐ ω ∂μ, (W ω).trace = (d : ℂ)) (j : Fin 4) :
    Tendsto (fun n => reportEffect μ W (finiteReadout μ ℱ J n) j)
      atTop (𝓝 (reportEffect μ W J j)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => finiteReadout_effect_error_le μ ℱ J hJ W hW hpos htrace n j)
  simpa using (tendsto_disagreement_real μ ℱ hgen J hJ).const_mul (d : ℝ)

theorem tendsto_finiteReadout_effect_family (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m₀) (hgen : (⨆ n, ℱ n) = m₀)
    (J : Ω → Fin 4) (hJ : Measurable J)
    (W : Ω → Matrix (Fin d) (Fin d) ℂ) (hW : Measurable W)
    (hpos : ∀ᵐ ω ∂μ, (W ω).PosSemidef)
    (htrace : ∀ᵐ ω ∂μ, (W ω).trace = (d : ℂ)) :
    Tendsto (fun n j => reportEffect μ W (finiteReadout μ ℱ J n) j)
      atTop (𝓝 (fun j => reportEffect μ W J j)) :=
  tendsto_pi_nhds.2 (tendsto_finiteReadout_effect μ ℱ hgen J hJ W hW hpos htrace)

theorem tendsto_finiteReadout_effect_entry (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m₀) (hgen : (⨆ n, ℱ n) = m₀)
    (J : Ω → Fin 4) (hJ : Measurable J)
    (W : Ω → Matrix (Fin d) (Fin d) ℂ) (hW : Measurable W)
    (hpos : ∀ᵐ ω ∂μ, (W ω).PosSemidef)
    (htrace : ∀ᵐ ω ∂μ, (W ω).trace = (d : ℂ)) (j : Fin 4) (a b : Fin d) :
    Tendsto (fun n => reportEffect μ W (finiteReadout μ ℱ J n) j a b)
      atTop (𝓝 (reportEffect μ W J j a b)) :=
  (continuous_apply b).tendsto _ |>.comp
    ((continuous_apply a).tendsto _ |>.comp
      (tendsto_finiteReadout_effect μ ℱ hgen J hJ W hW hpos htrace j))

theorem actual_infinite_record_readout (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m₀) (hgen : (⨆ n, ℱ n) = m₀)
    (J : Ω → Fin 4) (hJ : Measurable J)
    (W : Ω → Matrix (Fin d) (Fin d) ℂ) (hW : Measurable W)
    (hpos : ∀ᵐ ω ∂μ, (W ω).PosSemidef)
    (htrace : ∀ᵐ ω ∂μ, (W ω).trace = (d : ℂ))
    (htotal : (∫ ω, W ω ∂μ) = 1) :
    (∀ n, Measurable[ℱ n] (finiteReadout μ ℱ J n)) ∧
    (∀ᵐ ω ∂μ, ∀ᶠ n in atTop, finiteReadout μ ℱ J n ω = J ω) ∧
    Tendsto (fun n => μ {ω | finiteReadout μ ℱ J n ω ≠ J ω}) atTop (𝓝 0) ∧
    (∀ j, (reportEffect μ W J j).PosSemidef) ∧
    (∑ j, reportEffect μ W J j) = 1 ∧
    (∀ n, (∀ j, (reportEffect μ W (finiteReadout μ ℱ J n) j).PosSemidef) ∧
      (∑ j, reportEffect μ W (finiteReadout μ ℱ J n) j) = 1 ∧
      ∀ j, ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
        (reportEffect μ W (finiteReadout μ ℱ J n) j - reportEffect μ W J j)‖ ≤
        (d : ℝ) * (μ {ω | finiteReadout μ ℱ J n ω ≠ J ω}).toReal) ∧
    Tendsto (fun n j => reportEffect μ W (finiteReadout μ ℱ J n) j)
      atTop (𝓝 (fun j => reportEffect μ W J j)) := by
  refine ⟨measurable_finiteReadout μ ℱ J, ae_eventually_finiteReadout_eq μ ℱ hgen J hJ,
    tendsto_disagreement_mass μ ℱ hgen J hJ, reportEffect_posSemidef μ W hpos J,
    reportEffect_sum μ W hW hpos htrace htotal J hJ, ?_,
    tendsto_finiteReadout_effect_family μ ℱ hgen J hJ W hW hpos htrace⟩
  intro n
  refine ⟨reportEffect_posSemidef μ W hpos _, ?_,
    finiteReadout_euclidean_operator_error_le μ ℱ J hJ W hW hpos htrace n⟩
  exact reportEffect_sum μ W hW hpos htrace htotal _
    ((measurable_finiteReadout μ ℱ J n).mono (ℱ.le n) le_rfl)

end QuantumProver.ElegantJointMeasurement.InfiniteRecordReadout
