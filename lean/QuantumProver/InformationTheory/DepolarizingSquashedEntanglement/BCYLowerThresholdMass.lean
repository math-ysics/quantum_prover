import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYCompositeTesting
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTestingMinimax
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTestingPrimitives
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYCommutingTests
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYScalarThresholdMass

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix Filter Set
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal NNReal

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYLowerThresholdMass

open BCYRelativeEntropy BCYCompositeTesting BCYTestingPrimitives

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem fixedErrorBeta_le_one (rho : Density (A × B)) {epsilon : ℝ}
    (he0 : 0 ≤ epsilon) : fixedErrorBeta rho epsilon ≤ 1 := by
  apply iInf_le_of_le
    ⟨acceptAllEffect _, by simpa only [acceptance_acceptAll] using sub_le_self 1 he0⟩
  simp only [worstSeparableBeta_acceptAll rho, ENNReal.ofReal_one]
  exact le_rfl

theorem fixedErrorBeta_pos (rho : Density (A × B)) {epsilon : ℝ}
    (he1 : epsilon < 1) : 0 < fixedErrorBeta rho epsilon :=
  (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).trans_le
    (fixedErrorBeta_probability_floor rho he1)

theorem hypothesisTestingNat_nonneg (rho : Density (A × B)) {epsilon : ℝ}
    (he0 : 0 ≤ epsilon) : 0 ≤ hypothesisTestingNat rho epsilon := by
  have h := EReal.neg_le_neg_iff.mpr
    (ENNReal.log_monotone (fixedErrorBeta_le_one rho he0))
  simpa only [hypothesisTestingNat, ENNReal.log_one, neg_zero] using h

theorem hypothesisTestingNat_ne_top (rho : Density (A × B)) {epsilon : ℝ}
    (he1 : epsilon < 1) : hypothesisTestingNat rho epsilon ≠ ⊤ :=
  ne_of_lt ((hypothesisTestingNat_le rho he1).trans_lt (EReal.coe_lt_top _))

theorem hypothesisTestingNat_ne_bot (rho : Density (A × B)) {epsilon : ℝ}
    (he0 : 0 ≤ epsilon) : hypothesisTestingNat rho epsilon ≠ ⊥ :=
  ne_of_gt ((EReal.bot_lt_coe 0).trans_le (hypothesisTestingNat_nonneg rho he0))

theorem coe_hypothesisTestingNat_toReal (rho : Density (A × B)) {epsilon : ℝ}
    (he0 : 0 ≤ epsilon) (he1 : epsilon < 1) :
    ((hypothesisTestingNat rho epsilon).toReal : EReal) = hypothesisTestingNat rho epsilon :=
  EReal.coe_toReal (hypothesisTestingNat_ne_top rho he1) (hypothesisTestingNat_ne_bot rho he0)

def compositeFixedErrorRateReal (rho : Density (A × B)) (epsilon : ℝ) (n : ℕ) : ℝ :=
  (hypothesisTestingNat (tensorCopies rho n) epsilon).toReal / (n : ℝ)

@[simp] theorem compositeFixedErrorRateReal_zero (rho : Density (A × B)) (epsilon : ℝ) :
    compositeFixedErrorRateReal rho epsilon 0 = 0 := by
  simp [compositeFixedErrorRateReal]

theorem coe_compositeFixedErrorRateReal (rho : Density (A × B)) {epsilon : ℝ}
    (he0 : 0 ≤ epsilon) (he1 : epsilon < 1) (n : ℕ) :
    (compositeFixedErrorRateReal rho epsilon n : EReal) =
      hypothesisTestingNat (tensorCopies rho n) epsilon * ((1 / (n : ℝ) : ℝ) : EReal) := by
  rw [← coe_hypothesisTestingNat_toReal (tensorCopies rho n) he0 he1, ← EReal.coe_mul]
  congr 1
  exact div_eq_mul_one_div _ _

theorem exists_worst_comparator_family (rho : Density (A × B)) {epsilon : ℝ}
    (he0 : 0 ≤ epsilon) :
    ∃ sigmaStar : (n : ℕ) → SeparableDensity (CopyIndex A n) (CopyIndex B n),
      ∀ n, hypothesisTestingNat (tensorCopies rho n) epsilon =
        hypothesisTestingSingleNat (tensorCopies rho n) (sigmaStar n).val epsilon := by
  classical
  choose sigmaStar hWorst using
    (fun n => BCYTestingMinimax.exists_hypothesisTestingNat_eq_singleAlternative
      (tensorCopies rho n) he0)
  exact ⟨sigmaStar, hWorst⟩

theorem finite_threshold_testing_bound (rho : Density (A × B))
    (sigmaStar : SeparableDensity A B) (S : Density (A × B)) (hS : S.matrix.PosDef)
    {epsilon c t : ℝ} (he0 : 0 ≤ epsilon) (he1 : epsilon < 1)
    (hWorst : hypothesisTestingNat rho epsilon =
      hypothesisTestingSingleNat rho sigmaStar.val epsilon)
    (hc : 0 < c) (hOrder : sigmaStar.val.matrix ≤ c • S.matrix)
    (hMass : 1 - epsilon ≤ acceptance rho (BCYCommutingTests.likelihoodTest rho S hS t)) :
    t ≤ (hypothesisTestingNat rho epsilon).toReal + Real.log c := by
  have hTest := hypothesisTestingSingleNat_ge_of_beta_bound rho S
    (BCYCommutingTests.likelihoodTest rho S hS t) hMass
    (BCYCommutingTests.likelihoodTest_beta_le_exp rho S hS t)
  have hPenalty := hypothesisTestingSingleNat_le_add_log_of_alternative_le
    rho sigmaStar.val S he0 hc hOrder
  rw [← hWorst, ← coe_hypothesisTestingNat_toReal rho he0 he1, ← EReal.coe_add] at hPenalty
  exact EReal.coe_le_coe_iff.mp (hTest.trans hPenalty)

theorem finite_copy_threshold_rate_implication (rho : Density (A × B))
    {epsilon c Re slack : ℝ} (he0 : 0 ≤ epsilon) (he1 : epsilon < 1)
    {n : ℕ} (hn : 0 < n)
    (sigmaStar : SeparableDensity (CopyIndex A n) (CopyIndex B n))
    (S : Density (CopyIndex A n × CopyIndex B n)) (hS : S.matrix.PosDef)
    (hWorst : hypothesisTestingNat (tensorCopies rho n) epsilon =
      hypothesisTestingSingleNat (tensorCopies rho n) sigmaStar.val epsilon)
    (hc : 0 < c) (hOrder : sigmaStar.val.matrix ≤ c • S.matrix)
    (hMass : 1 - epsilon ≤ acceptance (tensorCopies rho n)
      (BCYCommutingTests.likelihoodTest (tensorCopies rho n) S hS ((n : ℝ) * (Re + slack)))) :
    Re + slack - Real.log c / (n : ℝ) ≤ compositeFixedErrorRateReal rho epsilon n := by
  have h := finite_threshold_testing_bound (tensorCopies rho n) sigmaStar S hS he0 he1
    hWorst hc hOrder hMass
  have hPos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold compositeFixedErrorRateReal
  apply (le_div_iff₀ hPos).mpr
  rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hPos)]
  nlinarith

private theorem log_constant_div_nat_tendsto_zero (c : ℝ) :
    Tendsto (fun n : ℕ => Real.log c / (n : ℝ)) atTop (𝓝 0) := by
  simpa only [mul_one_div, mul_zero] using
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log c)

theorem lower_threshold_mass_liminf_le (rho : Density (A × B))
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon < 1)
    (sigmaStar : (n : ℕ) → SeparableDensity (CopyIndex A n) (CopyIndex B n))
    (S : (n : ℕ) → Density (CopyIndex A n × CopyIndex B n))
    (hS : ∀ n, (S n).matrix.PosDef)
    (hWorst : ∀ n, hypothesisTestingNat (tensorCopies rho n) epsilon =
      hypothesisTestingSingleNat (tensorCopies rho n) (sigmaStar n).val epsilon)
    (c : ℝ) (hc : 0 < c)
    (hOrder : ∀ n, (sigmaStar n).val.matrix ≤ c • (S n).matrix)
    (Re : ℝ)
    (hRe : liminf (fun n => hypothesisTestingNat (tensorCopies rho n) epsilon *
      ((1 / (n : ℝ) : ℝ) : EReal)) atTop = (Re : EReal))
    (slack : ℝ) (hs : 0 < slack) :
    liminf (fun n => (acceptance (tensorCopies rho n)
      (BCYCommutingTests.likelihoodTest (tensorCopies rho n) (S n) (hS n)
        ((n : ℝ) * (Re + slack))) : EReal)) atTop ≤ ((1 - epsilon : ℝ) : EReal) := by
  apply BCYScalarThresholdMass.scalar_threshold_mass_liminf_le
    (fun n => acceptance (tensorCopies rho n)
      (BCYCommutingTests.likelihoodTest (tensorCopies rho n) (S n) (hS n)
        ((n : ℝ) * (Re + slack))))
    (compositeFixedErrorRateReal rho epsilon)
    (fun n => Real.log c / (n : ℝ)) Re slack epsilon hs
    (log_constant_div_nat_tendsto_zero c)
  · simpa only [coe_compositeFixedErrorRateReal rho he0 he1] using hRe
  · filter_upwards [eventually_ge_atTop 1] with n hn
    intro hMass
    exact finite_copy_threshold_rate_implication rho he0 he1 (by omega)
      (sigmaStar n) (S n) (hS n) (hWorst n) hc (hOrder n) hMass

end QuantumProver.DepolarizingSquashedEntanglement.BCYLowerThresholdMass
