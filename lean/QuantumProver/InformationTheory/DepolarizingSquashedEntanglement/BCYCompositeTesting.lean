import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTensorRegularization
import QuantumProver.InformationTheory.SuperchannelDiscrimination.QuantumTestingPowerBound
import QuantumProver.InformationTheory.SuperchannelDiscrimination.BinaryTesting

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix Set Filter
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal NNReal

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYCompositeTesting

open BCYRelativeEntropy

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

structure BinaryEffect (I : Type*) [Fintype I] [DecidableEq I] where
  matrix : QMatrix I
  positive : matrix.PosSemidef
  complement_positive : (1 - matrix).PosSemidef

theorem BinaryEffect.represented (T : BinaryEffect I) :
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.IsEffect T.matrix :=
  ⟨T.positive, T.complement_positive⟩

def acceptance (ρ : Density I) (T : BinaryEffect I) : ℝ :=
  (ρ.matrix * T.matrix).trace.re

theorem acceptance_bounds (ρ : Density I) (T : BinaryEffect I) :
    0 ≤ acceptance ρ T ∧ acceptance ρ T ≤ 1 :=
  QuantumProver.SuperchannelDiscrimination.FlaggedStates.acceptanceProbability_bounds
    (density_matrix ρ) T.represented

def acceptAllEffect (I : Type*) [Fintype I] [DecidableEq I] : BinaryEffect I where
  matrix := 1
  positive := Matrix.PosSemidef.one
  complement_positive := by simpa using (Matrix.PosSemidef.zero : (0 : QMatrix I).PosSemidef)

def rejectAllEffect (I : Type*) [Fintype I] [DecidableEq I] : BinaryEffect I where
  matrix := 0
  positive := Matrix.PosSemidef.zero
  complement_positive := by simpa using (Matrix.PosSemidef.one : (1 : QMatrix I).PosSemidef)

@[simp] theorem acceptance_acceptAll (ρ : Density I) :
    acceptance ρ (acceptAllEffect I) = 1 := by
  simp [acceptance, acceptAllEffect, ρ.trace_one]

@[simp] theorem acceptance_rejectAll (ρ : Density I) :
    acceptance ρ (rejectAllEffect I) = 0 := by
  simp [acceptance, rejectAllEffect]

def worstSeparableBeta (T : BinaryEffect (A × B)) : ℝ :=
  sSup (range (fun σ : SeparableDensity A B => acceptance σ.val T))

private theorem worstSeparableBeta_bdd (T : BinaryEffect (A × B)) :
    BddAbove (range (fun σ : SeparableDensity A B => acceptance σ.val T)) := by
  refine ⟨1, ?_⟩
  rintro x ⟨σ, rfl⟩
  exact (acceptance_bounds σ.val T).2

private theorem separableRange_nonempty (ρ : Density (A × B))
    (T : BinaryEffect (A × B)) :
    (range (fun σ : SeparableDensity A B => acceptance σ.val T)).Nonempty := by
  let σ : SeparableDensity A B :=
    ⟨productDensity (leftMarginal ρ) (rightMarginal ρ), productDensity_separable _ _⟩
  exact ⟨acceptance σ.val T, σ, rfl⟩

theorem acceptance_le_worstSeparableBeta (T : BinaryEffect (A × B))
    (σ : SeparableDensity A B) : acceptance σ.val T ≤ worstSeparableBeta T :=
  le_csSup (worstSeparableBeta_bdd T) ⟨σ, rfl⟩

theorem worstSeparableBeta_bounds (ρ : Density (A × B))
    (T : BinaryEffect (A × B)) :
    0 ≤ worstSeparableBeta T ∧ worstSeparableBeta T ≤ 1 := by
  constructor
  · let σ : SeparableDensity A B :=
      ⟨productDensity (leftMarginal ρ) (rightMarginal ρ), productDensity_separable _ _⟩
    exact (acceptance_bounds σ.val T).1.trans (acceptance_le_worstSeparableBeta T σ)
  · apply csSup_le (separableRange_nonempty ρ T)
    rintro x ⟨σ, rfl⟩
    exact (acceptance_bounds σ.val T).2

theorem worstSeparableBeta_le (ρ : Density (A × B)) (T : BinaryEffect (A × B))
    {q : ℝ} (hq : ∀ σ : SeparableDensity A B, acceptance σ.val T ≤ q) :
    worstSeparableBeta T ≤ q := by
  apply csSup_le (separableRange_nonempty ρ T)
  rintro x ⟨σ, rfl⟩
  exact hq σ

@[simp] theorem worstSeparableBeta_acceptAll (ρ : Density (A × B)) :
    worstSeparableBeta (acceptAllEffect (A × B)) = 1 := by
  apply le_antisymm (worstSeparableBeta_bounds ρ _).2
  let σ : SeparableDensity A B :=
    ⟨productDensity (leftMarginal ρ) (rightMarginal ρ), productDensity_separable _ _⟩
  simpa only [acceptance_acceptAll] using acceptance_le_worstSeparableBeta (acceptAllEffect _) σ

@[simp] theorem worstSeparableBeta_rejectAll (ρ : Density (A × B)) :
    worstSeparableBeta (rejectAllEffect (A × B)) = 0 := by
  apply le_antisymm ?_ (worstSeparableBeta_bounds ρ _).1
  apply csSup_le (separableRange_nonempty ρ _)
  rintro x ⟨σ, rfl⟩
  simp

def binaryMeasurementChannel (T : BinaryEffect I) :
    QuantumProver.SuperchannelDiscrimination.KrausCompletion.FiniteCPTP I
      QuantumProver.SuperchannelDiscrimination.BinaryMeasurement.Outcome where
  map := QuantumProver.SuperchannelDiscrimination.BinaryMeasurement.measurement T.matrix
  completelyPositive :=
    QuantumProver.SuperchannelDiscrimination.BinaryMeasurement.measurement_completelyPositive T.represented
  tracePreserving :=
    QuantumProver.SuperchannelDiscrimination.BinaryMeasurement.measurement_tracePreserving T.matrix

theorem binary_umegaki_dpi (ρ σ : Density I) (T : BinaryEffect I) :
    QuantumProver.SuperchannelDiscrimination.extendedBinaryRelativeEntropyBits
      (acceptance ρ T) (acceptance σ T) ≤
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits ρ.matrix σ.matrix := by
  have h := QuantumProver.SuperchannelDiscrimination.AbstractDPI.relativeEntropyBits_cptp_dpi
    (binaryMeasurementChannel T) ρ.positive σ.positive
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits
    (QuantumProver.SuperchannelDiscrimination.BinaryMeasurement.measurement T.matrix ρ.matrix)
    (QuantumProver.SuperchannelDiscrimination.BinaryMeasurement.measurement T.matrix σ.matrix) ≤ _ at h
  rw [QuantumProver.SuperchannelDiscrimination.BinaryMeasurement.measurement_relativeEntropyBits
    (density_matrix ρ) (density_matrix σ) T.represented] at h
  exact h

theorem worstSeparableBeta_pos (ρ : Density (A × B)) (T : BinaryEffect (A × B))
    (hp : 0 < acceptance ρ T) : 0 < worstSeparableBeta T := by
  by_contra h
  have hb : worstSeparableBeta T = 0 :=
    le_antisymm (le_of_not_gt h) (worstSeparableBeta_bounds ρ T).1
  let σ : SeparableDensity A B :=
    ⟨productDensity (leftMarginal ρ) (rightMarginal ρ), productDensity_separable _ _⟩
  have hq : acceptance σ.val T = 0 :=
    le_antisymm (by simpa [hb] using acceptance_le_worstSeparableBeta T σ)
      (acceptance_bounds σ.val T).1
  have hd := mul_le_mul_of_nonneg_right (binary_umegaki_dpi ρ σ.val T)
    (EReal.coe_nonneg.mpr (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).le)
  have ht : (⊤ : EReal) ≤ umegakiNats ρ.matrix σ.val.matrix := by
    simpa [hq, QuantumProver.SuperchannelDiscrimination.extendedBinaryRelativeEntropyBits,
      ne_of_gt hp, umegakiNats,
      EReal.top_mul_coe_of_pos (Real.log_pos (show (1 : ℝ) < 2 by norm_num))] using hd
  change (⊤ : EReal) ≤ umegakiNats ρ.matrix
    (productDensity (leftMarginal ρ) (rightMarginal ρ)).matrix at ht
  rw [umegakiNats_marginal_product] at ht
  exact (not_le_of_gt (EReal.coe_lt_top _) ht).elim

private theorem binary_one_sided_nats {p q beta : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (_hb0 : 0 < beta) (hb1 : beta ≤ 1) (hqb : q ≤ beta) :
    ((p * (-Real.log beta) - Real.log 2 : ℝ) : EReal) ≤
      QuantumProver.SuperchannelDiscrimination.extendedBinaryRelativeEntropyBits p q *
        (Real.log 2 : EReal) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hqz : q = 0
  · by_cases hpz : p = 0
    · simp [QuantumProver.SuperchannelDiscrimination.extendedBinaryRelativeEntropyBits, hqz, hpz,
        hlog2.le]
    · simp [QuantumProver.SuperchannelDiscrimination.extendedBinaryRelativeEntropyBits, hqz, hpz,
        EReal.top_mul_coe_of_pos hlog2]
  · by_cases hqo : q = 1
    · have hb : beta = 1 := le_antisymm hb1 (by simpa [hqo] using hqb)
      by_cases hpo : p = 1
      · simp [QuantumProver.SuperchannelDiscrimination.extendedBinaryRelativeEntropyBits, hqo, hpo,
          hb, hlog2.le]
      · simp [QuantumProver.SuperchannelDiscrimination.extendedBinaryRelativeEntropyBits, hqo,
          hpo, EReal.top_mul_coe_of_pos hlog2]
    · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
      have hqlt : q < 1 := lt_of_le_of_ne hq1 hqo
      have h := mul_le_mul_of_nonneg_right
        (QuantumProver.SuperchannelDiscrimination.binary_relative_entropy_ge hp1 hqpos hqlt)
        hlog2.le
      have hl : Real.log q ≤ Real.log beta := Real.log_le_log hqpos hqb
      have hm : p * (-Real.log beta) ≤ p * (-Real.log q) :=
        mul_le_mul_of_nonneg_left (neg_le_neg hl) hp0
      have hf : p * (-Real.log beta) - Real.log 2 ≤
          QuantumProver.SuperchannelDiscrimination.binaryRelativeEntropyBits p q * Real.log 2 := by
        simp only [Real.logb, one_div, Real.log_inv] at h
        have he : (p * (-Real.log q / Real.log 2) - 1) * Real.log 2 =
            p * (-Real.log q) - Real.log 2 := by
          field_simp [ne_of_gt hlog2]
        rw [he] at h
        linarith
      simpa [QuantumProver.SuperchannelDiscrimination.extendedBinaryRelativeEntropyBits, hqz, hqo]
        using EReal.coe_le_coe_iff.mpr hf

theorem worstSeparableBeta_testing_bound (ρ : Density (A × B))
    (T : BinaryEffect (A × B)) (hp : 0 < acceptance ρ T) :
    acceptance ρ T * (-Real.log (worstSeparableBeta T)) ≤
      relativeEntropyEntanglementReal ρ + Real.log 2 := by
  have hb0 := worstSeparableBeta_pos ρ T hp
  have hb1 := (worstSeparableBeta_bounds ρ T).2
  have h : ((acceptance ρ T * (-Real.log (worstSeparableBeta T)) - Real.log 2 : ℝ) : EReal) ≤
      relativeEntropyEntanglementNat ρ := by
    apply le_iInf
    intro σ
    exact (binary_one_sided_nats (acceptance_bounds ρ T).1 (acceptance_bounds ρ T).2
      (acceptance_bounds σ.val T).1 (acceptance_bounds σ.val T).2 hb0 hb1
      (acceptance_le_worstSeparableBeta T σ)).trans
      (mul_le_mul_of_nonneg_right (binary_umegaki_dpi ρ σ.val T)
        (EReal.coe_nonneg.mpr (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).le))
  rw [← coe_relativeEntropyEntanglementReal] at h
  have hh := EReal.coe_le_coe_iff.mp h
  linarith

theorem worstSeparableBeta_log_bound (ρ : Density (A × B))
    (T : BinaryEffect (A × B)) {epsilon : ℝ} (he : epsilon < 1)
    (ha : 1 - epsilon ≤ acceptance ρ T) :
    -Real.log (worstSeparableBeta T) ≤
      (relativeEntropyEntanglementReal ρ + Real.log 2) / (1 - epsilon) := by
  have hp : 0 < acceptance ρ T := (sub_pos.mpr he).trans_le ha
  have hb : 0 ≤ -Real.log (worstSeparableBeta T) :=
    neg_nonneg.mpr (Real.log_nonpos (worstSeparableBeta_pos ρ T hp).le
      (worstSeparableBeta_bounds ρ T).2)
  apply (le_div_iff₀ (sub_pos.mpr he)).mpr
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_right ha hb).trans (worstSeparableBeta_testing_bound ρ T hp)

theorem worstSeparableBeta_probability_floor (ρ : Density (A × B))
    (T : BinaryEffect (A × B)) {epsilon : ℝ} (he : epsilon < 1)
    (ha : 1 - epsilon ≤ acceptance ρ T) :
    Real.exp (-(relativeEntropyEntanglementReal ρ + Real.log 2) / (1 - epsilon)) ≤
      worstSeparableBeta T := by
  apply (Real.le_log_iff_exp_le
    (worstSeparableBeta_pos ρ T ((sub_pos.mpr he).trans_le ha))).mp
  have h := worstSeparableBeta_log_bound ρ T he ha
  rw [neg_div]
  linarith

def fixedErrorBeta (ρ : Density (A × B)) (epsilon : ℝ) : ℝ≥0∞ :=
  ⨅ T : {T : BinaryEffect (A × B) // 1 - epsilon ≤ acceptance ρ T},
    ENNReal.ofReal (worstSeparableBeta T.val)

def fixedErrorBetaReal (ρ : Density (A × B)) (epsilon : ℝ) : ℝ :=
  ⨅ T : {T : BinaryEffect (A × B) // 1 - epsilon ≤ acceptance ρ T},
    worstSeparableBeta T.val

def singleAlternativeBeta (ρ σ : Density (A × B)) (epsilon : ℝ) : ℝ≥0∞ :=
  ⨅ T : {T : BinaryEffect (A × B) // 1 - epsilon ≤ acceptance ρ T},
    ENNReal.ofReal (acceptance σ T.val)

def singleAlternativeBetaReal (ρ σ : Density (A × B)) (epsilon : ℝ) : ℝ :=
  ⨅ T : {T : BinaryEffect (A × B) // 1 - epsilon ≤ acceptance ρ T},
    acceptance σ T.val

def hypothesisTestingNat (ρ : Density (A × B)) (epsilon : ℝ) : EReal :=
  -ENNReal.log (fixedErrorBeta ρ epsilon)

def hypothesisTestingSingleNat (ρ σ : Density (A × B)) (epsilon : ℝ) : EReal :=
  -ENNReal.log (singleAlternativeBeta ρ σ epsilon)

theorem fixedErrorBeta_eq_ofReal (ρ : Density (A × B)) {epsilon : ℝ}
    (he : 0 ≤ epsilon) :
    fixedErrorBeta ρ epsilon = ENNReal.ofReal (fixedErrorBetaReal ρ epsilon) := by
  letI : Nonempty {T : BinaryEffect (A × B) // 1 - epsilon ≤ acceptance ρ T} :=
    ⟨⟨acceptAllEffect _, by simpa only [acceptance_acceptAll] using sub_le_self 1 he⟩⟩
  exact (ENNReal.ofReal_iInf (fun T : {T : BinaryEffect (A × B) //
    1 - epsilon ≤ acceptance ρ T} => worstSeparableBeta T.val)).symm

theorem singleAlternativeBeta_eq_ofReal (ρ σ : Density (A × B)) {epsilon : ℝ}
    (he : 0 ≤ epsilon) :
    singleAlternativeBeta ρ σ epsilon = ENNReal.ofReal (singleAlternativeBetaReal ρ σ epsilon) := by
  letI : Nonempty {T : BinaryEffect (A × B) // 1 - epsilon ≤ acceptance ρ T} :=
    ⟨⟨acceptAllEffect _, by simpa only [acceptance_acceptAll] using sub_le_self 1 he⟩⟩
  exact (ENNReal.ofReal_iInf (fun T : {T : BinaryEffect (A × B) //
    1 - epsilon ≤ acceptance ρ T} => acceptance σ T.val)).symm

theorem singleAlternativeBeta_le_fixedErrorBeta (ρ : Density (A × B))
    (σ : SeparableDensity A B) (epsilon : ℝ) :
    singleAlternativeBeta ρ σ.val epsilon ≤ fixedErrorBeta ρ epsilon := by
  apply le_iInf
  intro T
  exact iInf_le_of_le T (ENNReal.ofReal_le_ofReal (acceptance_le_worstSeparableBeta T.val σ))

theorem fixedErrorBeta_probability_floor (ρ : Density (A × B)) {epsilon : ℝ}
    (he : epsilon < 1) :
    ENNReal.ofReal (Real.exp (-(relativeEntropyEntanglementReal ρ + Real.log 2) / (1 - epsilon))) ≤
      fixedErrorBeta ρ epsilon := by
  apply le_iInf
  intro T
  exact ENNReal.ofReal_le_ofReal (worstSeparableBeta_probability_floor ρ T.val he T.property)

theorem hypothesisTestingNat_le (ρ : Density (A × B)) {epsilon : ℝ}
    (he : epsilon < 1) :
    hypothesisTestingNat ρ epsilon ≤
      ((relativeEntropyEntanglementReal ρ + Real.log 2) / (1 - epsilon) : ℝ) := by
  have h := EReal.neg_le_neg_iff.mpr (ENNReal.log_monotone (fixedErrorBeta_probability_floor ρ he))
  simpa only [hypothesisTestingNat, ENNReal.log_ofReal_of_pos (Real.exp_pos _),
    Real.log_exp, ← EReal.coe_neg, neg_div, neg_neg] using h

def negLogNat (q : ℝ) : EReal := -ENNReal.log (ENNReal.ofReal q)

theorem negLogNat_antitone : Antitone negLogNat := by
  intro p q hpq
  exact EReal.neg_le_neg_iff.mpr (ENNReal.log_monotone (ENNReal.ofReal_le_ofReal hpq))

theorem negLogNat_of_pos {q : ℝ} (hq : 0 < q) :
    negLogNat q = (-Real.log q : ℝ) := by
  rw [negLogNat, ENNReal.log_ofReal_of_pos hq, ← EReal.coe_neg]

@[simp] theorem negLogNat_zero : negLogNat 0 = ⊤ := by
  simp [negLogNat]

theorem negLogNat_exp (r : ℝ) : negLogNat (Real.exp (-r)) = (r : EReal) := by
  rw [negLogNat_of_pos (Real.exp_pos _), Real.log_exp]
  simp

def copyTestRateNat (ρ : Density (A × B)) {n : ℕ}
    (T : BinaryEffect (CopyIndex A n × CopyIndex B n)) : EReal :=
  if n = 0 then 0 else negLogNat (worstSeparableBeta T) * ((1 / (n : ℝ) : ℝ) : EReal)

@[simp] theorem copyTestRateNat_acceptAll (ρ : Density (A × B)) (n : ℕ) :
    copyTestRateNat ρ (acceptAllEffect (CopyIndex A n × CopyIndex B n)) = 0 := by
  simp [copyTestRateNat, worstSeparableBeta_acceptAll (tensorCopies ρ n), negLogNat]

theorem copyTestRateNat_eq_top_of_worstBeta_zero (ρ : Density (A × B))
    {n : ℕ} (hn : 0 < n) (T : BinaryEffect (CopyIndex A n × CopyIndex B n))
    (hb : worstSeparableBeta T = 0) : copyTestRateNat ρ T = ⊤ := by
  rw [copyTestRateNat, ite_eq_right (ne_of_gt hn), hb, negLogNat_zero]
  exact EReal.top_mul_coe_of_pos (by positivity)

theorem copyTestRateNat_ge_of_beta_bound (ρ : Density (A × B))
    {n : ℕ} (hn : 0 < n) (T : BinaryEffect (CopyIndex A n × CopyIndex B n))
    {r : ℝ} (hb : worstSeparableBeta T ≤ Real.exp (-(n : ℝ) * r)) :
    (r : EReal) ≤ copyTestRateNat ρ T := by
  have h := negLogNat_antitone hb
  rw [show -(n : ℝ) * r = -((n : ℝ) * r) by ring, negLogNat_exp] at h
  have hm := mul_le_mul_of_nonneg_right h
    (EReal.coe_nonneg.mpr (show 0 ≤ (1 / (n : ℝ) : ℝ) by positivity))
  rw [copyTestRateNat, ite_eq_right (ne_of_gt hn)]
  convert hm using 1
  rw [← EReal.coe_mul]
  congr 1
  field_simp [ne_of_gt (show (0 : ℝ) < n by exact_mod_cast hn)]

theorem copyTestRateNat_le (ρ : Density (A × B)) {n : ℕ} (hn : 0 < n)
    (T : BinaryEffect (CopyIndex A n × CopyIndex B n)) {epsilon : ℝ}
    (he : epsilon < 1) (ha : 1 - epsilon ≤ acceptance (tensorCopies ρ n) T) :
    copyTestRateNat ρ T ≤
      (((relativeEntropyEntanglementReal (tensorCopies ρ n) / (n : ℝ) +
        Real.log 2 / (n : ℝ)) / (1 - epsilon) : ℝ) : EReal) := by
  have hb := worstSeparableBeta_pos (tensorCopies ρ n) T ((sub_pos.mpr he).trans_le ha)
  rw [copyTestRateNat, ite_eq_right (ne_of_gt hn), negLogNat_of_pos hb, ← EReal.coe_mul]
  apply EReal.coe_le_coe_iff.mpr
  have h := mul_le_mul_of_nonneg_right (worstSeparableBeta_log_bound (tensorCopies ρ n) T he ha)
    (show 0 ≤ (1 / (n : ℝ) : ℝ) by positivity)
  convert h using 1 <;> field_simp [ne_of_gt (show (0 : ℝ) < n by exact_mod_cast hn),
    ne_of_gt (sub_pos.mpr he)]

def AchievableAllRate (ρ : Density (A × B)) (r : EReal) : Prop :=
  ∃ T : (n : ℕ) → BinaryEffect (CopyIndex A n × CopyIndex B n),
    Tendsto (fun n => acceptance (tensorCopies ρ n) (T n)) atTop (𝓝 1) ∧
      r ≤ Filter.liminf (fun n => copyTestRateNat ρ (T n)) atTop

def allEffectsTestingRateNat (ρ : Density (A × B)) : EReal :=
  sSup {r : EReal | AchievableAllRate ρ r}

theorem achievableAllRate_zero (ρ : Density (A × B)) : AchievableAllRate ρ 0 := by
  refine ⟨fun n => acceptAllEffect _, ?_, ?_⟩
  · simpa only [acceptance_acceptAll] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  · simp only [copyTestRateNat_acceptAll]
    simp

theorem allEffectsTestingRateNat_nonneg (ρ : Density (A × B)) :
    0 ≤ allEffectsTestingRateNat ρ :=
  le_sSup (achievableAllRate_zero ρ)

theorem achievableAllRate_of_uniform_separable_bound (ρ : Density (A × B)) (r : ℝ)
    (T : (n : ℕ) → BinaryEffect (CopyIndex A n × CopyIndex B n))
    (ha : Tendsto (fun n => acceptance (tensorCopies ρ n) (T n)) atTop (𝓝 1))
    (hb : ∀ n, 0 < n → ∀ σ : SeparableDensity (CopyIndex A n) (CopyIndex B n),
      acceptance σ.val (T n) ≤ Real.exp (-(n : ℝ) * r)) :
    AchievableAllRate ρ (r : EReal) := by
  refine ⟨T, ha, ?_⟩
  apply Filter.le_liminf_of_le (h := ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact copyTestRateNat_ge_of_beta_bound ρ (by omega) (T n)
    (worstSeparableBeta_le (tensorCopies ρ n) (T n) (hb n (by omega)))

theorem copyTestRateNat_limsup_le_of_acceptance_tendsto (ρ : Density (A × B))
    (T : (n : ℕ) → BinaryEffect (CopyIndex A n × CopyIndex B n))
    (ha : Tendsto (fun n => acceptance (tensorCopies ρ n) (T n)) atTop (𝓝 1)) :
    Filter.limsup (fun n => copyTestRateNat ρ (T n)) atTop ≤
      (regularizedRelativeEntropyEntanglementNat ρ : EReal) := by
  have hf : ∀ epsilon ∈ Ioo (0 : ℝ) 1,
      Filter.limsup (fun n => copyTestRateNat ρ (T n)) atTop ≤
        ((regularizedRelativeEntropyEntanglementNat ρ / (1 - epsilon) : ℝ) : EReal) := by
    intro epsilon he
    have hevent : ∀ᶠ n in atTop, 1 - epsilon ≤ acceptance (tensorCopies ρ n) (T n) := by
      filter_upwards [ha.eventually (Ioi_mem_nhds (show (1 - epsilon : ℝ) < 1 by linarith [he.1]))]
        with n hn using hn.le
    have hbound : ∀ᶠ n in atTop, copyTestRateNat ρ (T n) ≤
        (((relativeEntropyEntanglementReal (tensorCopies ρ n) / (n : ℝ) +
          Real.log 2 / (n : ℝ)) / (1 - epsilon) : ℝ) : EReal) := by
      filter_upwards [hevent, eventually_ge_atTop 1] with n hn hpos
      exact copyTestRateNat_le ρ (by omega) (T n) he.2 hn
    have hzero : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_one_div, mul_zero] using
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log 2)
    have hlimR : Tendsto
        (fun n : ℕ => (relativeEntropyEntanglementReal (tensorCopies ρ n) / (n : ℝ) +
          Real.log 2 / (n : ℝ)) / (1 - epsilon)) atTop
        (𝓝 (regularizedRelativeEntropyEntanglementNat ρ / (1 - epsilon))) := by
      simpa only [add_zero] using ((tendsto_relativeEntropyEntanglement_rate ρ).add hzero).div_const
        (1 - epsilon)
    exact (Filter.limsup_le_limsup hbound).trans_eq (EReal.tendsto_coe.mpr hlimR).limsup_eq
  have hlimR : Tendsto
      (fun epsilon : ℝ => regularizedRelativeEntropyEntanglementNat ρ / (1 - epsilon))
      (𝓝[>] 0) (𝓝 (regularizedRelativeEntropyEntanglementNat ρ)) := by
    have hcont : ContinuousAt
        (fun epsilon : ℝ => regularizedRelativeEntropyEntanglementNat ρ / (1 - epsilon)) 0 :=
      continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)
    simpa using hcont.continuousWithinAt.tendsto
  apply ge_of_tendsto (EReal.tendsto_coe.mpr hlimR)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with epsilon he
  exact hf epsilon he

theorem achievableAllRate_le_regularizedER (ρ : Density (A × B)) {r : EReal}
    (hr : AchievableAllRate ρ r) :
    r ≤ (regularizedRelativeEntropyEntanglementNat ρ : EReal) := by
  rcases hr with ⟨T, ha, hr⟩
  exact hr.trans ((Filter.liminf_le_limsup).trans
    (copyTestRateNat_limsup_le_of_acceptance_tendsto ρ T ha))

theorem allEffectsTestingRateNat_le_regularizedER (ρ : Density (A × B)) :
    allEffectsTestingRateNat ρ ≤ (regularizedRelativeEntropyEntanglementNat ρ : EReal) := by
  apply sSup_le
  intro r hr
  exact achievableAllRate_le_regularizedER ρ hr

theorem allEffectsTestingRateNat_ne_top (ρ : Density (A × B)) :
    allEffectsTestingRateNat ρ ≠ ⊤ :=
  ne_of_lt ((allEffectsTestingRateNat_le_regularizedER ρ).trans_lt (EReal.coe_lt_top _))

theorem allEffectsTestingRateNat_ne_bot (ρ : Density (A × B)) :
    allEffectsTestingRateNat ρ ≠ ⊥ :=
  ne_of_gt ((EReal.bot_lt_coe 0).trans_le (allEffectsTestingRateNat_nonneg ρ))

def allEffectsTestingRateReal (ρ : Density (A × B)) : ℝ :=
  (allEffectsTestingRateNat ρ).toReal

theorem coe_allEffectsTestingRateReal (ρ : Density (A × B)) :
    (allEffectsTestingRateReal ρ : EReal) = allEffectsTestingRateNat ρ :=
  EReal.coe_toReal (allEffectsTestingRateNat_ne_top ρ) (allEffectsTestingRateNat_ne_bot ρ)

theorem allEffectsTestingRateReal_le_regularizedER (ρ : Density (A × B)) :
    allEffectsTestingRateReal ρ ≤ regularizedRelativeEntropyEntanglementNat ρ := by
  apply EReal.coe_le_coe_iff.mp
  rw [coe_allEffectsTestingRateReal]
  exact allEffectsTestingRateNat_le_regularizedER ρ

end QuantumProver.DepolarizingSquashedEntanglement.BCYCompositeTesting
