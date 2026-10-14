import Mathlib

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumProver.SuperchannelDiscrimination

structure BinaryTest where
  alpha : ℝ
  beta : ℝ
  alpha_nonneg : 0 ≤ alpha
  alpha_le_one : alpha ≤ 1
  beta_nonneg : 0 ≤ beta
  beta_le_one : beta ≤ 1

abbrev StrategyFamily := ℕ → Set BinaryTest

def acceptAll : BinaryTest := ⟨0, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

def HasAcceptAll (S : StrategyFamily) : Prop := ∀ n, acceptAll ∈ S n

def Feasible (S : StrategyFamily) (epsilon : ℝ) (n : ℕ) (T : BinaryTest) : Prop :=
  T ∈ S n ∧ T.alpha ≤ epsilon

def optimalBeta (S : StrategyFamily) (epsilon : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨅ T : {T : BinaryTest // Feasible S epsilon n T}, ENNReal.ofReal T.val.beta

def optimalBetaReal (S : StrategyFamily) (epsilon : ℝ) (n : ℕ) : ℝ :=
  ⨅ T : {T : BinaryTest // Feasible S epsilon n T}, T.val.beta

def negLogTwo (q : ℝ≥0∞) : EReal :=
  (-ENNReal.log q) * ((1 / Real.log 2 : ℝ) : EReal)

def positiveBlockRate (S : StrategyFamily) (epsilon : ℝ) (k : ℕ) : EReal :=
  negLogTwo (optimalBeta S epsilon (k + 1)) * ((1 / ((k + 1 : ℕ) : ℝ) : ℝ) : EReal)

def blockRate (S : StrategyFamily) (epsilon : ℝ) (n : ℕ) : EReal :=
  negLogTwo (optimalBeta S epsilon n) * ((1 / (n : ℝ) : ℝ) : EReal)

def testPositiveBlockRate (T : BinaryTest) (k : ℕ) : EReal :=
  negLogTwo (ENNReal.ofReal T.beta) * ((1 / ((k + 1 : ℕ) : ℝ) : ℝ) : EReal)

def fixedErrorLowerRate (S : StrategyFamily) (epsilon : ℝ) : EReal :=
  Filter.liminf (positiveBlockRate S epsilon) atTop

def orderedSteinExponent (S : StrategyFamily) : EReal :=
  sInf (fixedErrorLowerRate S '' Ioo (0 : ℝ) 1)

theorem fixedErrorLowerRate_eq_liminf_blockRate (S : StrategyFamily) (epsilon : ℝ) :
    fixedErrorLowerRate S epsilon = Filter.liminf (blockRate S epsilon) atTop := by
  exact Filter.liminf_nat_add (blockRate S epsilon) 1

theorem optimalBeta_le_of_feasible {S : StrategyFamily} {epsilon : ℝ} {n : ℕ}
    {T : BinaryTest} (hT : Feasible S epsilon n T) :
    optimalBeta S epsilon n ≤ ENNReal.ofReal T.beta := by
  exact iInf_le_of_le ⟨T, hT⟩ le_rfl

theorem le_optimalBeta {S : StrategyFamily} {epsilon : ℝ} {n : ℕ} {q : ℝ≥0∞}
    (h : ∀ T, Feasible S epsilon n T → q ≤ ENNReal.ofReal T.beta) :
    q ≤ optimalBeta S epsilon n := by
  exact le_iInf fun T => h T.val T.property

theorem optimalBeta_le_one {S : StrategyFamily} (hS : HasAcceptAll S)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (n : ℕ) :
    optimalBeta S epsilon n ≤ 1 := by
  simpa [acceptAll] using
    (optimalBeta_le_of_feasible (S := S) (epsilon := epsilon) (n := n)
      (T := acceptAll) ⟨hS n, hepsilon⟩)

theorem optimalBeta_eq_ofReal_realInf {S : StrategyFamily} (hS : HasAcceptAll S)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (n : ℕ) :
    optimalBeta S epsilon n = ENNReal.ofReal (optimalBetaReal S epsilon n) := by
  letI : Nonempty {T : BinaryTest // Feasible S epsilon n T} :=
    ⟨⟨acceptAll, hS n, hepsilon⟩⟩
  exact (ENNReal.ofReal_iInf (fun T : {T : BinaryTest // Feasible S epsilon n T} =>
    T.val.beta)).symm

theorem optimalBeta_toReal_eq_realInf {S : StrategyFamily} (hS : HasAcceptAll S)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (n : ℕ) :
    (optimalBeta S epsilon n).toReal = optimalBetaReal S epsilon n := by
  rw [optimalBeta_eq_ofReal_realInf hS hepsilon n]
  exact ENNReal.toReal_ofReal (Real.iInf_nonneg (fun T => T.val.beta_nonneg))

theorem optimalBeta_antitone_family {P N : StrategyFamily}
    (hPN : ∀ n, P n ⊆ N n) (epsilon : ℝ) (n : ℕ) :
    optimalBeta N epsilon n ≤ optimalBeta P epsilon n := by
  refine le_iInf fun T => ?_
  exact optimalBeta_le_of_feasible ⟨hPN n T.property.1, T.property.2⟩

theorem optimalBeta_antitone_epsilon (S : StrategyFamily) {epsilon delta : ℝ}
    (h : epsilon ≤ delta) (n : ℕ) :
    optimalBeta S delta n ≤ optimalBeta S epsilon n := by
  refine le_iInf fun T => ?_
  exact optimalBeta_le_of_feasible ⟨T.property.1, T.property.2.trans h⟩

theorem negLogTwo_antitone : Antitone negLogTwo := by
  intro q r hqr
  apply mul_le_mul_of_nonneg_right
  · exact EReal.neg_le_neg_iff.mpr (ENNReal.log_monotone hqr)
  · exact EReal.coe_nonneg.mpr (by positivity)

theorem testPositiveBlockRate_le {S : StrategyFamily} {epsilon : ℝ} {k : ℕ}
    {T : BinaryTest} (hT : Feasible S epsilon (k + 1) T) :
    testPositiveBlockRate T k ≤ positiveBlockRate S epsilon k := by
  apply mul_le_mul_of_nonneg_right
  · exact negLogTwo_antitone (optimalBeta_le_of_feasible hT)
  · exact EReal.coe_nonneg.mpr (by positivity)

@[simp] theorem negLogTwo_one : negLogTwo 1 = 0 := by
  simp [negLogTwo]

@[simp] theorem negLogTwo_zero : negLogTwo 0 = ⊤ := by
  rw [negLogTwo, ENNReal.log_zero, EReal.neg_bot]
  exact EReal.top_mul_coe_of_pos (by positivity)

theorem negLogTwo_ofReal {q : ℝ} (hq : 0 < q) :
    negLogTwo (ENNReal.ofReal q) = ((-Real.log q / Real.log 2 : ℝ) : EReal) := by
  rw [negLogTwo, ENNReal.log_ofReal_of_pos hq, ← EReal.coe_neg, ← EReal.coe_mul]
  congr 1
  simp [div_eq_mul_inv]

theorem negLogTwo_exp (c : ℝ) :
    negLogTwo (ENNReal.ofReal (Real.exp (-c * Real.log 2))) = (c : EReal) := by
  rw [negLogTwo_ofReal (Real.exp_pos _), Real.log_exp]
  congr 1
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

theorem positiveBlockRate_eq_coe_of_beta_ne_zero {S : StrategyFamily}
    (hS : HasAcceptAll S) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (k : ℕ)
    (hq : optimalBeta S epsilon (k + 1) ≠ 0) :
    positiveBlockRate S epsilon k =
      ((-Real.log (optimalBeta S epsilon (k + 1)).toReal / Real.log 2 /
        ((k + 1 : ℕ) : ℝ) : ℝ) : EReal) := by
  have hqTop : optimalBeta S epsilon (k + 1) ≠ ⊤ :=
    ne_of_lt ((optimalBeta_le_one hS hepsilon (k + 1)).trans_lt (by simp))
  rw [positiveBlockRate, negLogTwo, ENNReal.log_pos_real hq hqTop,
    ← EReal.coe_neg, ← EReal.coe_mul, ← EReal.coe_mul]
  congr 1
  simp [div_eq_mul_inv, mul_assoc]

theorem positiveBlockRate_eq_top_of_beta_zero {S : StrategyFamily} {epsilon : ℝ} {k : ℕ}
    (hq : optimalBeta S epsilon (k + 1) = 0) :
    positiveBlockRate S epsilon k = ⊤ := by
  rw [positiveBlockRate, hq, negLogTwo_zero]
  exact EReal.top_mul_coe_of_pos (by positivity)

theorem positiveBlockRate_nonneg {S : StrategyFamily} (hS : HasAcceptAll S)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (k : ℕ) :
    0 ≤ positiveBlockRate S epsilon k := by
  apply EReal.mul_nonneg
  · simpa using negLogTwo_antitone (optimalBeta_le_one hS hepsilon (k + 1))
  · exact EReal.coe_nonneg.mpr (by positivity)

theorem positiveBlockRate_mono_family {P N : StrategyFamily}
    (hPN : ∀ n, P n ⊆ N n) (epsilon : ℝ) (k : ℕ) :
    positiveBlockRate P epsilon k ≤ positiveBlockRate N epsilon k := by
  apply mul_le_mul_of_nonneg_right
  · exact negLogTwo_antitone (optimalBeta_antitone_family hPN epsilon (k + 1))
  · exact EReal.coe_nonneg.mpr (by positivity)

theorem positiveBlockRate_mono_epsilon (S : StrategyFamily) {epsilon delta : ℝ}
    (h : epsilon ≤ delta) (k : ℕ) :
    positiveBlockRate S epsilon k ≤ positiveBlockRate S delta k := by
  apply mul_le_mul_of_nonneg_right
  · exact negLogTwo_antitone (optimalBeta_antitone_epsilon S h (k + 1))
  · exact EReal.coe_nonneg.mpr (by positivity)

theorem fixedErrorLowerRate_mono_family {P N : StrategyFamily}
    (hPN : ∀ n, P n ⊆ N n) (epsilon : ℝ) :
    fixedErrorLowerRate P epsilon ≤ fixedErrorLowerRate N epsilon := by
  exact Filter.liminf_le_liminf (.of_forall (positiveBlockRate_mono_family hPN epsilon))

theorem fixedErrorLowerRate_monotone (S : StrategyFamily) :
    Monotone (fixedErrorLowerRate S) := by
  intro epsilon delta h
  exact Filter.liminf_le_liminf (.of_forall (positiveBlockRate_mono_epsilon S h))

theorem fixedErrorLowerRate_nonneg {S : StrategyFamily} (hS : HasAcceptAll S)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    0 ≤ fixedErrorLowerRate S epsilon := by
  exact Filter.le_liminf_of_le (h := .of_forall (positiveBlockRate_nonneg hS hepsilon))

theorem le_fixedErrorLowerRate_of_eventual_tests {S : StrategyFamily} {epsilon : ℝ}
    {r : EReal} (h : ∀ᶠ k in atTop, ∃ T : BinaryTest,
      Feasible S epsilon (k + 1) T ∧ r ≤ testPositiveBlockRate T k) :
    r ≤ fixedErrorLowerRate S epsilon := by
  apply Filter.le_liminf_of_le (h := ?_)
  filter_upwards [h] with k hk
  rcases hk with ⟨T, hT, hr⟩
  exact hr.trans (testPositiveBlockRate_le hT)

theorem tendsto_fixedErrorLowerRate (S : StrategyFamily) :
    Tendsto (fixedErrorLowerRate S) (𝓝[>] (0 : ℝ))
      (𝓝 (orderedSteinExponent S)) := by
  apply MonotoneOn.tendsto_nhdsWithin_Ioo_right
  · exact ⟨1 / 2, by norm_num, by norm_num⟩
  · exact (fixedErrorLowerRate_monotone S).monotoneOn _
  · exact OrderBot.bddBelow _

theorem orderedSteinExponent_le_fixedErrorLowerRate (S : StrategyFamily)
    {epsilon : ℝ} (hepsilon : epsilon ∈ Ioo (0 : ℝ) 1) :
    orderedSteinExponent S ≤ fixedErrorLowerRate S epsilon := by
  exact sInf_le ⟨epsilon, hepsilon, rfl⟩

theorem orderedSteinExponent_mono_family {P N : StrategyFamily}
    (hPN : ∀ n, P n ⊆ N n) :
    orderedSteinExponent P ≤ orderedSteinExponent N := by
  apply le_sInf
  rintro x ⟨epsilon, hepsilon, rfl⟩
  exact (orderedSteinExponent_le_fixedErrorLowerRate P hepsilon).trans
    (fixedErrorLowerRate_mono_family hPN epsilon)

theorem orderedSteinExponent_nonneg {S : StrategyFamily} (hS : HasAcceptAll S) :
    0 ≤ orderedSteinExponent S := by
  apply le_sInf
  rintro x ⟨epsilon, hepsilon, rfl⟩
  exact fixedErrorLowerRate_nonneg hS hepsilon.1.le

theorem le_orderedSteinExponent_of_eventual_tests {S : StrategyFamily} {r : EReal}
    (h : ∀ epsilon ∈ Ioo (0 : ℝ) 1, ∀ᶠ k in atTop, ∃ T : BinaryTest,
      Feasible S epsilon (k + 1) T ∧ r ≤ testPositiveBlockRate T k) :
    r ≤ orderedSteinExponent S := by
  apply le_sInf
  rintro x ⟨epsilon, hepsilon, rfl⟩
  exact le_fixedErrorLowerRate_of_eventual_tests (h epsilon hepsilon)

end QuantumProver.SuperchannelDiscrimination
