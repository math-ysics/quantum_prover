import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYCompositeTesting
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTestingMinimax

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Filter Set
open scoped Topology

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYDiagonalTests

open BCYRelativeEntropy BCYCompositeTesting BCYTestingMinimax

def errorLevel (k : ℕ) : ℝ := 1 / ((k : ℝ) + 2)

theorem errorLevel_pos (k : ℕ) : 0 < errorLevel k := by
  unfold errorLevel
  positivity

theorem errorLevel_lt_one (k : ℕ) : errorLevel k < 1 := by
  unfold errorLevel
  apply (div_lt_one (by positivity : (0 : ℝ) < (k : ℝ) + 2)).mpr
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem errorLevel_tendsto : Tendsto errorLevel atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    (tendsto_add_atTop_iff_nat 2).2 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))

def approximatingRate (R : ℝ) (k : ℕ) : ℝ := R - 1 / ((k : ℝ) + 1)

theorem approximatingRate_lt (R : ℝ) (k : ℕ) : approximatingRate R k < R := by
  unfold approximatingRate
  apply sub_lt_self
  positivity

theorem approximatingRate_tendsto (R : ℝ) :
    Tendsto (approximatingRate R) atTop (𝓝 R) := by
  change Tendsto (fun k : ℕ => R - 1 / ((k : ℝ) + 1)) atTop (𝓝 R)
  simpa only [sub_zero] using
    (tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

def cutoff (N : ℕ → ℕ) : ℕ → ℕ
  | 0 => N 0 + 1
  | k + 1 => max (cutoff N k + 1) (N (k + 1) + (k + 1) + 1)

theorem cutoff_ge_start (N : ℕ → ℕ) (k : ℕ) : N k ≤ cutoff N k := by
  cases k with
  | zero => simp only [cutoff]; omega
  | succ k =>
      apply le_trans (show N (k + 1) ≤ N (k + 1) + (k + 1) + 1 by omega)
      exact le_max_right _ _

theorem cutoff_ge_index (N : ℕ → ℕ) (k : ℕ) : k + 1 ≤ cutoff N k := by
  cases k with
  | zero => simp only [cutoff]; omega
  | succ k =>
      apply le_trans (show k + 1 + 1 ≤ N (k + 1) + (k + 1) + 1 by omega)
      exact le_max_right _ _

theorem cutoff_strictMono (N : ℕ → ℕ) : StrictMono (cutoff N) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact (Nat.lt_succ_self (cutoff N k)).trans_le (le_max_left _ _)

def stage (N : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => cutoff N k ≤ n) n

theorem stage_le (N : ℕ → ℕ) (n : ℕ) : stage N n ≤ n :=
  Nat.findGreatest_le n

theorem stage_cutoff_le (N : ℕ → ℕ) (n : ℕ) (hn : cutoff N 0 ≤ n) :
    cutoff N (stage N n) ≤ n :=
  Nat.findGreatest_spec (P := fun k => cutoff N k ≤ n) (Nat.zero_le n) hn

theorem stage_monotone (N : ℕ → ℕ) : Monotone (stage N) := by
  intro n m hnm
  exact Nat.findGreatest_mono (fun k hk => hk.trans hnm) hnm

theorem stage_tendsto (N : ℕ → ℕ) : Tendsto (stage N) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (cutoff N k)] with n hn
  have hk := cutoff_ge_index N k
  exact Nat.le_findGreatest (by omega : k ≤ n) hn

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem exists_optimal_fixed_error_effect (rho : Density (A × B))
    (epsilon : ℝ) (he : 0 ≤ epsilon) :
    ∃ T : BinaryEffect (A × B), 1 - epsilon ≤ acceptance rho T ∧
      fixedErrorBeta rho epsilon = ENNReal.ofReal (worstSeparableBeta T) := by
  obtain ⟨T, sigma, haccept, hbeta, hfixed, _⟩ := exists_fixedError_optimizers rho he
  refine ⟨T, haccept, ?_⟩
  rw [hbeta]
  exact hfixed

def optimalFixedErrorEffect (rho : Density (A × B)) (epsilon : ℝ)
    (he : 0 ≤ epsilon) : BinaryEffect (A × B) :=
  (exists_optimal_fixed_error_effect rho epsilon he).choose

theorem optimalFixedErrorEffect_acceptance (rho : Density (A × B))
    (epsilon : ℝ) (he : 0 ≤ epsilon) :
    1 - epsilon ≤ acceptance rho (optimalFixedErrorEffect rho epsilon he) :=
  (exists_optimal_fixed_error_effect rho epsilon he).choose_spec.1

theorem optimalFixedErrorEffect_beta (rho : Density (A × B))
    (epsilon : ℝ) (he : 0 ≤ epsilon) :
    fixedErrorBeta rho epsilon =
      ENNReal.ofReal (worstSeparableBeta (optimalFixedErrorEffect rho epsilon he)) :=
  (exists_optimal_fixed_error_effect rho epsilon he).choose_spec.2

theorem optimalFixedErrorEffect_copy_rate (rho : Density (A × B)) (n : ℕ)
    (epsilon : ℝ) (he : 0 ≤ epsilon) :
    copyTestRateNat rho (optimalFixedErrorEffect (tensorCopies rho n) epsilon he) =
      hypothesisTestingNat (tensorCopies rho n) epsilon *
        ((1 / (n : ℝ) : ℝ) : EReal) := by
  by_cases hn : n = 0
  · subst n
    simp only [copyTestRateNat, ite_true, Nat.cast_zero, div_zero, EReal.coe_zero, mul_zero]
  · rw [copyTestRateNat, ite_eq_right hn, hypothesisTestingNat,
      optimalFixedErrorEffect_beta]
    rfl

theorem achievableAllRate_of_fixed_error_lower_bound (rho : Density (A × B)) (R : ℝ)
    (hFixed : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      (R : EReal) ≤ liminf (fun n => hypothesisTestingNat (tensorCopies rho n) epsilon *
        ((1 / (n : ℝ) : ℝ) : EReal)) atTop) :
    AchievableAllRate rho (R : EReal) := by
  classical
  let F : ℕ → ℕ → EReal := fun k n =>
    hypothesisTestingNat (tensorCopies rho n) (errorLevel k) *
      ((1 / (n : ℝ) : ℝ) : EReal)
  have htail : ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (approximatingRate R k : EReal) ≤ F k n := by
    intro k
    have hstrict : (approximatingRate R k : EReal) < liminf (F k) atTop :=
      (EReal.coe_lt_coe_iff.mpr (approximatingRate_lt R k)).trans_le
        (hFixed (errorLevel k) (errorLevel_pos k) (errorLevel_lt_one k))
    have hev : ∀ᶠ n in atTop, (approximatingRate R k : EReal) < F k n :=
      eventually_lt_of_lt_liminf hstrict
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    exact ⟨N, fun n hn => (hN n hn).le⟩
  choose N hN using htail
  let T : (n : ℕ) → BinaryEffect (CopyIndex A n × CopyIndex B n) := fun n =>
    optimalFixedErrorEffect (tensorCopies rho n) (errorLevel (stage N n))
      (errorLevel_pos (stage N n)).le
  have herror : Tendsto (fun n => errorLevel (stage N n)) atTop (𝓝 0) :=
    errorLevel_tendsto.comp (stage_tendsto N)
  have haccept : Tendsto (fun n => acceptance (tensorCopies rho n) (T n)) atTop (𝓝 1) := by
    have hlow : Tendsto (fun n => 1 - errorLevel (stage N n)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub herror)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    · intro n
      exact optimalFixedErrorEffect_acceptance (tensorCopies rho n)
        (errorLevel (stage N n)) (errorLevel_pos (stage N n)).le
    · intro n
      exact (acceptance_bounds (tensorCopies rho n) (T n)).2
  have hrate : ∀ᶠ n in atTop,
      (approximatingRate R (stage N n) : EReal) ≤ copyTestRateNat rho (T n) := by
    filter_upwards [eventually_ge_atTop (cutoff N 0)] with n hn
    have hstart : N (stage N n) ≤ n :=
      (cutoff_ge_start N (stage N n)).trans (stage_cutoff_le N n hn)
    have h := hN (stage N n) n hstart
    simpa only [F, T, optimalFixedErrorEffect_copy_rate] using h
  have hlimit : Tendsto (fun n => (approximatingRate R (stage N n) : EReal))
      atTop (𝓝 (R : EReal)) :=
    EReal.tendsto_coe.mpr ((approximatingRate_tendsto R).comp (stage_tendsto N))
  refine ⟨T, haccept, ?_⟩
  have h := liminf_le_liminf hrate
  rw [hlimit.liminf_eq] at h
  exact h

theorem allEffectsTestingRateNat_ge_of_fixed_error_lower_bound
    (rho : Density (A × B)) (R : ℝ)
    (hFixed : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      (R : EReal) ≤ liminf (fun n => hypothesisTestingNat (tensorCopies rho n) epsilon *
        ((1 / (n : ℝ) : ℝ) : EReal)) atTop) :
    (R : EReal) ≤ allEffectsTestingRateNat rho :=
  le_sSup (achievableAllRate_of_fixed_error_lower_bound rho R hFixed)

end QuantumProver.DepolarizingSquashedEntanglement.BCYDiagonalTests
