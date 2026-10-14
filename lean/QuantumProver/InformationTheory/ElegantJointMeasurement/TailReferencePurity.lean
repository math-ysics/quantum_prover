import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.IConcurrence
import QuantumProver.InformationTheory.ElegantJointMeasurement.ResourceEntropy
import QuantumProver.InformationTheory.ElegantJointMeasurement.ProtocolEffects
import QuantumProver.InformationTheory.ElegantJointMeasurement.CountableInstruments

namespace QuantumProver.ElegantJointMeasurement.TailReference

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

abbrev LocalIndex (κ : Type*) := (Fin 2 × κ) × Fin 2

def tailMass (γ : κ → ℝ) : ℝ := ∑ k, (γ k) ^ 2

def initialCoefficient (γ : κ → ℝ) : Matrix (LocalIndex κ) (LocalIndex κ) ℂ :=
  fun z w => if z.1.1 = z.2 ∧ w.1.1 = w.2 ∧ z.1.2 = w.1.2 then
    ((γ z.1.2 / (2 * Real.sqrt (tailMass γ)) : ℝ) : ℂ) else 0

def initialGram (γ : κ → ℝ) : Matrix (LocalIndex κ) (LocalIndex κ) ℂ :=
  (initialCoefficient γ)ᴴ * initialCoefficient γ

def normalizedWeight (γ : κ → ℝ) (k : κ) : ℝ := (γ k) ^ 2 / tailMass γ

theorem initialCoefficient_apply (γ : κ → ℝ) (a b r s : Fin 2) (k l : κ) :
    initialCoefficient γ ((a, k), r) ((b, l), s) =
      if a = r ∧ b = s ∧ k = l then
        ((γ k / (2 * Real.sqrt (tailMass γ)) : ℝ) : ℂ) else 0 := rfl

theorem initialCoefficient_eq_scaled_physicalReferenceInput (γ : κ → ℝ) :
    initialCoefficient γ =
      (Real.sqrt (tailMass γ))⁻¹ • QuantumProver.ElegantJointMeasurement.Concurrence.physicalReferenceInput γ := by
  ext ⟨⟨a, k⟩, r⟩ ⟨⟨b, l⟩, s⟩
  exact (QuantumProver.ElegantJointMeasurement.Concurrence.physical_reference_scaled_input_apply γ (tailMass γ)
    a r b s k l).symm

omit [DecidableEq κ] in
theorem twice_amplitude_square (γ : κ → ℝ) (ht : 0 < tailMass γ) (k : κ) :
    2 * (γ k / (2 * Real.sqrt (tailMass γ))) ^ 2 =
      (γ k) ^ 2 / (2 * tailMass γ) := by
  rw [div_pow, mul_pow, Real.sq_sqrt ht.le]
  field_simp [ht.ne']

set_option maxHeartbeats 800000 in

theorem initialGram_apply (γ : κ → ℝ) (ht : 0 < tailMass γ)
    (b b' s s' : Fin 2) (l l' : κ) :
    initialGram γ ((b, l), s) ((b', l'), s') =
      if l = l' ∧ b = s ∧ b' = s' then
        (((γ l) ^ 2 / (2 * tailMass γ) : ℝ) : ℂ) else 0 := by
  have hsc : (2 : ℂ) * ((γ l / (2 * Real.sqrt (tailMass γ)) : ℝ) : ℂ) ^ 2 =
      (((γ l) ^ 2 / (2 * tailMass γ) : ℝ) : ℂ) := by
    exact_mod_cast twice_amplitude_square γ ht l
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    apply Complex.ext <;> norm_num
  by_cases hll : l = l'
  · subst l'
    by_cases hbs : b = s <;> by_cases hb's' : b' = s'
    all_goals
      simp [initialGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, initialCoefficient,
        hbs, hb's', mul_ite, ← pow_two, ← two_mul]
    rw [htwo]
    simpa [pow_two] using hsc
  · by_cases hbs : b = s <;> by_cases hb's' : b' = s'
    all_goals
      simp [initialGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, initialCoefficient,
        hbs, hb's', hll, Ne.symm hll, mul_ite]

omit [DecidableEq κ] in
theorem normalizedWeight_nonneg (γ : κ → ℝ) (ht : 0 < tailMass γ) (k : κ) :
    0 ≤ normalizedWeight γ k := div_nonneg (sq_nonneg _) ht.le

omit [DecidableEq κ] in
theorem normalizedWeight_sum (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    ∑ k, normalizedWeight γ k = 1 := by
  simp only [normalizedWeight]
  rw [← Finset.sum_div, ← tailMass]
  exact div_self ht.ne'

theorem initialGram_trace (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    Matrix.trace (initialGram γ) = 1 := by
  have hsum : ∑ k, (γ k : ℂ) ^ 2 / (2 * (tailMass γ : ℂ)) = 1 / 2 := by
    have hr : ∑ k, (γ k) ^ 2 / (2 * tailMass γ) = 1 / 2 := by
      rw [← Finset.sum_div, ← tailMass]
      field_simp [ht.ne']
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
    push_cast at hc
    exact hc
  simp [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type,
    initialGram_apply γ ht]
  rw [hsum]
  norm_num

theorem initialGram_isDensity (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    QuantumProver.ElegantJointMeasurement.Concurrence.IsDensity (initialGram γ) :=
  ⟨Matrix.posSemidef_conjTranspose_mul_self _, initialGram_trace γ ht⟩

set_option maxHeartbeats 800000 in

theorem initialGram_square_apply (γ : κ → ℝ) (ht : 0 < tailMass γ)
    (b b' s s' : Fin 2) (l l' : κ) :
    (initialGram γ * initialGram γ) ((b, l), s) ((b', l'), s') =
      if l = l' ∧ b = s ∧ b' = s' then
        ((((γ l) ^ 2 / tailMass γ) ^ 2 / 2 : ℝ) : ℂ) else 0 := by
  have hsc : (2 : ℂ) * (((γ l) ^ 2 / (2 * tailMass γ) : ℝ) : ℂ) ^ 2 =
      ((((γ l) ^ 2 / tailMass γ) ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  by_cases hll : l = l'
  · subst l'
    by_cases hbs : b = s <;> by_cases hb's' : b' = s'
    all_goals
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        initialGram_apply γ ht, hbs, hb's', mul_ite, ite_mul,
        ← pow_two, ← two_mul]
    simpa [pow_two] using hsc
  · by_cases hbs : b = s <;> by_cases hb's' : b' = s'
    all_goals
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        initialGram_apply γ ht, hbs, hb's', hll, mul_ite, ite_mul]

theorem initialGram_trace_square (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    Matrix.trace (initialGram γ * initialGram γ) =
      ((∑ k, ((γ k) ^ 2 / tailMass γ) ^ 2 : ℝ) : ℂ) := by
  simp [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type,
    initialGram_square_apply γ ht]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem initialGram_purity (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    QuantumProver.ElegantJointMeasurement.Concurrence.purity (initialGram γ) =
      ∑ k, ((γ k) ^ 2 / tailMass γ) ^ 2 := by
  rw [QuantumProver.ElegantJointMeasurement.Concurrence.purity, initialGram_trace_square γ ht]
  exact Complex.ofReal_re _

theorem initialCoefficient_budget (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget (initialCoefficient γ) =
      Real.sqrt (2 * (1 - ∑ k, ((γ k) ^ 2 / tailMass γ) ^ 2)) := by
  rw [QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget_of_normalized _ (initialGram_trace γ ht)]
  change Real.sqrt (2 * (1 - QuantumProver.ElegantJointMeasurement.Concurrence.purity (initialGram γ))) = _
  rw [initialGram_purity γ ht]

theorem scaled_physicalReferenceInput_budget (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget
        ((Real.sqrt (tailMass γ))⁻¹ • QuantumProver.ElegantJointMeasurement.Concurrence.physicalReferenceInput γ) =
      Real.sqrt (2 * (1 - ∑ k, ((γ k) ^ 2 / tailMass γ) ^ 2)) := by
  rw [← initialCoefficient_eq_scaled_physicalReferenceInput]
  exact initialCoefficient_budget γ ht

theorem normalizedWeight_purity_le_one (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    ∑ k, (normalizedWeight γ k) ^ 2 ≤ 1 := by
  have h := QuantumProver.ElegantJointMeasurement.Concurrence.density_purity_le_one _ (initialGram_isDensity γ ht)
  simpa only [initialGram_purity γ ht, normalizedWeight] using h

theorem initialCoefficient_reindex_budget {α : Type*} [Fintype α] [DecidableEq α]
    (e : LocalIndex κ ≃ α) (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget (Matrix.reindex e e (initialCoefficient γ)) =
      Real.sqrt (2 * (1 - ∑ k, ((γ k) ^ 2 / tailMass γ) ^ 2)) := by
  rw [QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget_reindex_equiv, initialCoefficient_budget γ ht]

theorem tailMass_omittedCoefficient (β : κ → ℝ) (k : κ) :
    tailMass (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) = tailMass β - (β k) ^ 2 := by
  have hz : (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k k) ^ 2 = 0 := by
    simp [QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient]
  have heq : tailMass (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) =
      ∑ z ∈ Finset.univ.erase k, (β z) ^ 2 := by
    unfold tailMass
    rw [← Finset.sum_erase Finset.univ
      (f := fun z => (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k z) ^ 2) hz]
    apply Finset.sum_congr rfl
    intro z hz
    simp [QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient, Finset.ne_of_mem_erase hz]
  rw [heq]
  have hsum := Finset.sum_erase_add Finset.univ (fun z => (β z) ^ 2) (Finset.mem_univ k)
  change (∑ z ∈ Finset.univ.erase k, (β z) ^ 2) + (β k) ^ 2 = tailMass β at hsum
  linarith

theorem normalized_omitted_mass (β : κ → ℝ) (k : κ) (hβ : ∑ z, (β z) ^ 2 = 1) :
    tailMass (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) = 1 - (β k) ^ 2 := by
  rw [tailMass_omittedCoefficient]
  exact congrArg (fun x => x - (β k) ^ 2) hβ

theorem omittedWeight_at_selected (β : κ → ℝ) (k : κ) :
    normalizedWeight (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) k = 0 := by
  simp [normalizedWeight, QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient]

theorem omittedWeight_at_other (β : κ → ℝ) (k z : κ) (hzk : z ≠ k)
    (hβ : ∑ u, (β u) ^ 2 = 1) :
    normalizedWeight (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) z =
      (β z) ^ 2 / (1 - (β k) ^ 2) := by
  simp [normalizedWeight, QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient, hzk,
    normalized_omitted_mass β k hβ]

def referenceTailCost (γ : κ → ℝ) : ℝ :=
  2 * tailMass γ * QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget
    ((Real.sqrt (tailMass γ))⁻¹ • QuantumProver.ElegantJointMeasurement.Concurrence.physicalReferenceInput γ)

theorem referenceTailCost_eq (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    referenceTailCost γ =
      2 * tailMass γ * Real.sqrt (2 * (1 - ∑ z, (normalizedWeight γ z) ^ 2)) := by
  unfold referenceTailCost
  rw [scaled_physicalReferenceInput_budget γ ht]
  rfl

theorem referenceTailCost_nonneg (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    0 ≤ referenceTailCost γ :=
  mul_nonneg (mul_nonneg (by norm_num) ht.le) (QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget_nonneg _)

theorem normalizedWeight_concurrence_radicand_nonneg (γ : κ → ℝ)
    (ht : 0 < tailMass γ) :
    0 ≤ 2 * (1 - ∑ z, (normalizedWeight γ z) ^ 2) :=
  mul_nonneg (by norm_num) (sub_nonneg.mpr (normalizedWeight_purity_le_one γ ht))

theorem referenceTailCost_sq (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    (referenceTailCost γ) ^ 2 =
      8 * (tailMass γ) ^ 2 * (1 - ∑ z, (normalizedWeight γ z) ^ 2) := by
  rw [referenceTailCost_eq γ ht, mul_pow,
    Real.sq_sqrt (normalizedWeight_concurrence_radicand_nonneg γ ht)]
  ring

theorem normalized_omitted_weights (β : κ → ℝ) (k : κ)
    (hβ : ∑ z, (β z) ^ 2 = 1) (ht : 0 < 1 - (β k) ^ 2) :
    (∀ z, 0 ≤ normalizedWeight (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) z) ∧
      (∑ z, normalizedWeight (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) z) = 1 ∧
      (∑ z, (normalizedWeight (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) z) ^ 2) ≤ 1 := by
  have hm : 0 < tailMass (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) := by
    rwa [normalized_omitted_mass β k hβ]
  exact ⟨normalizedWeight_nonneg _ hm, normalizedWeight_sum _ hm,
    normalizedWeight_purity_le_one _ hm⟩

theorem normalized_omitted_physical_cost (β : κ → ℝ) (k : κ)
    (hβ : ∑ z, (β z) ^ 2 = 1) :
    2 * (1 - (β k) ^ 2) * QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget
      ((Real.sqrt (1 - (β k) ^ 2))⁻¹ •
        QuantumProver.ElegantJointMeasurement.Concurrence.physicalReferenceInput (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k)) =
      referenceTailCost (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) := by
  simp only [referenceTailCost, normalized_omitted_mass β k hβ]

theorem omitted_tail_cost_eq (β : κ → ℝ) (k : κ)
    (hβ : ∑ z, (β z) ^ 2 = 1) (ht : 0 < 1 - (β k) ^ 2) :
    2 * (1 - (β k) ^ 2) * QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget
      ((Real.sqrt (1 - (β k) ^ 2))⁻¹ •
        QuantumProver.ElegantJointMeasurement.Concurrence.physicalReferenceInput (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k)) =
      2 * (1 - (β k) ^ 2) * Real.sqrt
        (2 * (1 - ∑ z, (normalizedWeight (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) z) ^ 2)) := by
  have hm : 0 < tailMass (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) := by
    rwa [normalized_omitted_mass β k hβ]
  rw [normalized_omitted_physical_cost β k hβ, referenceTailCost_eq _ hm,
    normalized_omitted_mass β k hβ]

theorem omitted_tail_cost_nonneg (β : κ → ℝ) (k : κ)
    (hβ : ∑ z, (β z) ^ 2 = 1) (ht : 0 < 1 - (β k) ^ 2) :
    0 ≤ 2 * (1 - (β k) ^ 2) * QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget
      ((Real.sqrt (1 - (β k) ^ 2))⁻¹ •
        QuantumProver.ElegantJointMeasurement.Concurrence.physicalReferenceInput (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k)) := by
  have hm : 0 < tailMass (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) := by
    rwa [normalized_omitted_mass β k hβ]
  rw [normalized_omitted_physical_cost β k hβ]
  exact referenceTailCost_nonneg _ hm

theorem omitted_tail_cost_sq (β : κ → ℝ) (k : κ)
    (hβ : ∑ z, (β z) ^ 2 = 1) (ht : 0 < 1 - (β k) ^ 2) :
    (2 * (1 - (β k) ^ 2) * QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget
      ((Real.sqrt (1 - (β k) ^ 2))⁻¹ •
        QuantumProver.ElegantJointMeasurement.Concurrence.physicalReferenceInput (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k))) ^ 2 =
      8 * (1 - (β k) ^ 2) ^ 2 *
        (1 - ∑ z, (normalizedWeight (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) z) ^ 2) := by
  have hm : 0 < tailMass (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) := by
    rwa [normalized_omitted_mass β k hβ]
  rw [normalized_omitted_physical_cost β k hβ, referenceTailCost_sq _ hm,
    normalized_omitted_mass β k hβ]

theorem omitted_tail_quadratic_necessary (β : κ → ℝ) (k : κ) (cost : ℝ)
    (hβ : ∑ z, (β z) ^ 2 = 1) (ht : 0 < 1 - (β k) ^ 2)
    (hlower : |1 - 2 * (β k) ^ 2| ≤ cost)
    (hupper : cost ≤ 2 * (1 - (β k) ^ 2) * QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget
      ((Real.sqrt (1 - (β k) ^ 2))⁻¹ •
        QuantumProver.ElegantJointMeasurement.Concurrence.physicalReferenceInput (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k))) :
    (2 * (β k) ^ 2 - 1) ^ 2 ≤ 8 * (1 - (β k) ^ 2) ^ 2 *
      (1 - ∑ z, (normalizedWeight (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) z) ^ 2) := by
  have hsq := (sq_le_sq₀ (abs_nonneg (1 - 2 * (β k) ^ 2))
    (omitted_tail_cost_nonneg β k hβ ht)).mpr (hlower.trans hupper)
  rw [sq_abs, omitted_tail_cost_sq β k hβ ht] at hsq
  nlinarith

def tailPairMass (γ : κ → ℝ) : ℝ :=
  (∑ k, ∑ l ∈ Finset.univ.erase k, (γ k) ^ 2 * (γ l) ^ 2) / 2

theorem tailPairMass_nonneg (γ : κ → ℝ) : 0 ≤ tailPairMass γ := by
  unfold tailPairMass
  exact div_nonneg (Finset.sum_nonneg (fun k hk => Finset.sum_nonneg
    (fun l hl => mul_nonneg (sq_nonneg _) (sq_nonneg _)))) (by norm_num)

theorem twice_tailPairMass (γ : κ → ℝ) :
    2 * tailPairMass γ = (tailMass γ) ^ 2 - ∑ k, (γ k) ^ 4 := by
  have hrow (k : κ) : (γ k) ^ 2 * tailMass γ =
      (γ k) ^ 4 + ∑ l ∈ Finset.univ.erase k, (γ k) ^ 2 * (γ l) ^ 2 := by
    have h := Finset.sum_erase_add Finset.univ
      (fun l => (γ k) ^ 2 * (γ l) ^ 2) (Finset.mem_univ k)
    have hfull : (∑ l, (γ k) ^ 2 * (γ l) ^ 2) = (γ k) ^ 2 * tailMass γ := by
      rw [← Finset.mul_sum]
      rfl
    rw [hfull] at h
    nlinarith
  have htotal : (tailMass γ) ^ 2 = (∑ k, (γ k) ^ 4) +
      ∑ k, ∑ l ∈ Finset.univ.erase k, (γ k) ^ 2 * (γ l) ^ 2 := by
    calc
      (tailMass γ) ^ 2 = (∑ k, (γ k) ^ 2) * tailMass γ := by rw [← tailMass, pow_two]
      _ = ∑ k, (γ k) ^ 2 * tailMass γ := by rw [Finset.sum_mul]
      _ = _ := by simp_rw [hrow]; rw [Finset.sum_add_distrib]
  unfold tailPairMass
  linarith

omit [DecidableEq κ] in
theorem tailMass_sq_mul_normalized_purity (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    (tailMass γ) ^ 2 * (∑ k, (normalizedWeight γ k) ^ 2) = ∑ k, (γ k) ^ 4 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold normalizedWeight
  field_simp [ht.ne']

theorem referenceTailCost_sq_pairs (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    (referenceTailCost γ) ^ 2 = 16 * tailPairMass γ := by
  rw [referenceTailCost_sq γ ht]
  nlinarith [tailMass_sq_mul_normalized_purity γ ht, twice_tailPairMass γ]

theorem referenceTailCost_four_sqrt_pairs (γ : κ → ℝ) (ht : 0 < tailMass γ) :
    referenceTailCost γ = 4 * Real.sqrt (tailPairMass γ) := by
  have hsq : (referenceTailCost γ) ^ 2 = (4 * Real.sqrt (tailPairMass γ)) ^ 2 := by
    rw [referenceTailCost_sq_pairs γ ht, mul_pow,
      Real.sq_sqrt (tailPairMass_nonneg γ)]
    norm_num
  exact (sq_eq_sq₀ (referenceTailCost_nonneg γ ht)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp hsq

theorem omitted_tail_cost_four_sqrt_pairs (β : κ → ℝ) (k : κ)
    (hβ : ∑ z, (β z) ^ 2 = 1) (ht : 0 < 1 - (β k) ^ 2) :
    2 * (1 - (β k) ^ 2) * QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget
      ((Real.sqrt (1 - (β k) ^ 2))⁻¹ •
        QuantumProver.ElegantJointMeasurement.Concurrence.physicalReferenceInput (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k)) =
      4 * Real.sqrt (tailPairMass (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k)) := by
  have hm : 0 < tailMass (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) := by
    rwa [normalized_omitted_mass β k hβ]
  rw [normalized_omitted_physical_cost β k hβ, referenceTailCost_four_sqrt_pairs _ hm]

theorem squared_amplitude_eq_omitted_split (β : κ → ℝ) (k : κ)
    (hβ : ∑ z, (β z) ^ 2 = 1) (ht : 0 < 1 - (β k) ^ 2) (i : κ) :
    (β i) ^ 2 = if i = k then (β k) ^ 2 else
      (1 - (β k) ^ 2) * normalizedWeight (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) i := by
  by_cases hi : i = k
  · simp [hi]
  · rw [ite_eq_right hi, omittedWeight_at_other β k i hi hβ]
    field_simp [ht.ne']

theorem omitted_scaled_negMulLog_sum (β : κ → ℝ) (k : κ)
    (hβ : ∑ z, (β z) ^ 2 = 1) (ht : 0 < 1 - (β k) ^ 2) :
    ∑ i, Real.negMulLog
      ((1 - (β k) ^ 2) * normalizedWeight (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) i) =
      ∑ i ∈ Finset.univ.erase k, Real.negMulLog ((β i) ^ 2) := by
  have hz : Real.negMulLog ((1 - (β k) ^ 2) *
      normalizedWeight (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) k) = 0 := by
    rw [omittedWeight_at_selected]
    simp
  rw [← Finset.sum_erase Finset.univ
    (f := fun i => Real.negMulLog ((1 - (β k) ^ 2) *
      normalizedWeight (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k) i)) hz]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≠ k := Finset.ne_of_mem_erase hi
  have hp := squared_amplitude_eq_omitted_split β k hβ ht i
  rw [ite_eq_right hik] at hp
  rw [← hp]

theorem squared_amplitude_entropy_eq_split (β : κ → ℝ) (k : κ)
    (hβ : ∑ z, (β z) ^ 2 = 1) (ht : 0 < 1 - (β k) ^ 2) :
    QuantumProver.ElegantJointMeasurement.Entropy.entropyBits (fun i => (β i) ^ 2) =
      QuantumProver.ElegantJointMeasurement.Entropy.entropyBits (QuantumProver.ElegantJointMeasurement.Entropy.splitWeights ((β k) ^ 2)
        (normalizedWeight (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k))) := by
  have hsum := Finset.add_sum_erase Finset.univ
    (fun i => Real.negMulLog ((β i) ^ 2)) (Finset.mem_univ k)
  unfold QuantumProver.ElegantJointMeasurement.Entropy.entropyBits
  rw [Fintype.sum_option]
  simp only [QuantumProver.ElegantJointMeasurement.Entropy.splitWeights]
  rw [omitted_scaled_negMulLog_sum β k hβ ht]
  congr 1
  exact hsum.symm

section ResourceEntropy

open scoped Matrix.Norms.L2Operator ContinuousFunctionalCalculus

def resourceCoefficient (β : κ → ℝ) : Matrix κ κ ℂ :=
  fun k l => if k = l then (β k : ℂ) else 0

def resourceGram (β : κ → ℝ) : Matrix κ κ ℂ :=
  (resourceCoefficient β)ᴴ * resourceCoefficient β

omit [Fintype κ] in
theorem resourceCoefficient_eq_diagonal (β : κ → ℝ) :
    resourceCoefficient β = Matrix.diagonal (fun k => (β k : ℂ)) := rfl

theorem resourceGram_eq_diagonal (β : κ → ℝ) :
    resourceGram β = Matrix.diagonal (fun k => (((β k) ^ 2 : ℝ) : ℂ)) := by
  unfold resourceGram
  rw [resourceCoefficient_eq_diagonal, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  congr 1
  ext k
  simp [pow_two]

omit [Fintype κ] in
theorem resourceCoefficient_conjTranspose (β : κ → ℝ) :
    (resourceCoefficient β)ᴴ = resourceCoefficient β := by
  rw [resourceCoefficient_eq_diagonal, Matrix.diagonal_conjTranspose]
  simp

theorem resource_leftGram_eq_resourceGram (β : κ → ℝ) :
    resourceCoefficient β * (resourceCoefficient β)ᴴ = resourceGram β := by
  unfold resourceGram
  rw [resourceCoefficient_conjTranspose]

theorem resourceGram_posSemidef (β : κ → ℝ) : (resourceGram β).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

theorem resourceGram_trace (β : κ → ℝ) (hβ : ∑ k, (β k) ^ 2 = 1) :
    Matrix.trace (resourceGram β) = 1 := by
  rw [resourceGram_eq_diagonal, Matrix.trace_diagonal]
  have h := congrArg (fun x : ℝ => (x : ℂ)) hβ
  push_cast at h
  simpa only [Complex.ofReal_pow] using h

theorem resourceGram_isDensity (β : κ → ℝ) (hβ : ∑ k, (β k) ^ 2 = 1) :
    QuantumProver.ElegantJointMeasurement.Concurrence.IsDensity (resourceGram β) :=
  ⟨resourceGram_posSemidef β, resourceGram_trace β hβ⟩

private def diagonalRealStarAlgHom : (κ → ℂ) →⋆ₐ[ℝ] Matrix κ κ ℂ :=
  { Matrix.diagonalAlgHom (n := κ) (α := ℂ) ℝ with
    map_star' := by
      intro p
      change Matrix.diagonal (star p) = (Matrix.diagonal p)ᴴ
      rw [Matrix.diagonal_conjTranspose] }

private theorem diagonalRealStarAlgHom_continuous :
    Continuous (diagonalRealStarAlgHom (κ := κ)) := by
  change Continuous (Matrix.diagonal : (κ → ℂ) → Matrix κ κ ℂ)
  fun_prop

theorem cfc_real_diagonal (p : κ → ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f (Matrix.diagonal (fun k => (p k : ℂ))) =
      Matrix.diagonal (fun k => ((f (p k) : ℝ) : ℂ)) := by
  have : ContinuousFunctionalCalculus ℂ (κ → ℂ) IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  have : ContinuousFunctionalCalculus ℝ (κ → ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let a : κ → ℂ := fun k => (p k : ℂ)
  have ha : IsSelfAdjoint a := by
    ext k
    simp [a]
  have hd : IsSelfAdjoint (diagonalRealStarAlgHom a) := by
    exact ha.map diagonalRealStarAlgHom
  have hm := (diagonalRealStarAlgHom (κ := κ)).map_cfc f a hf.continuousOn
    diagonalRealStarAlgHom_continuous ha hd
  rw [cfc_map_pi (S := ℝ) f a hf.continuousOn ha (fun k => by
    simp [a, IsSelfAdjoint])] at hm
  have hs (k : κ) : cfc f (a k) = (f (p k) : ℂ) := by
    exact cfc_algebraMap (A := ℂ) (p k) f
  simp_rw [hs] at hm
  exact hm.symm

def vonNeumannEntropyBits (ρ : Matrix κ κ ℂ) : ℝ :=
  (Matrix.trace (cfc Real.negMulLog ρ)).re / Real.log 2

theorem resource_vonNeumannEntropy_eq_entropyBits (β : κ → ℝ) :
    vonNeumannEntropyBits (resourceGram β) =
      QuantumProver.ElegantJointMeasurement.Entropy.entropyBits (fun k => (β k) ^ 2) := by
  unfold vonNeumannEntropyBits
  rw [resourceGram_eq_diagonal,
    cfc_real_diagonal (fun k => (β k) ^ 2) Real.negMulLog Real.continuous_negMulLog,
    Matrix.trace_diagonal]
  change (∑ k, ((Real.negMulLog ((β k) ^ 2) : ℝ) : ℂ)).re / Real.log 2 = _
  rw [← Complex.ofReal_sum]
  rfl

theorem resource_left_vonNeumannEntropy_eq_entropyBits (β : κ → ℝ) :
    vonNeumannEntropyBits (resourceCoefficient β * (resourceCoefficient β)ᴴ) =
      QuantumProver.ElegantJointMeasurement.Entropy.entropyBits (fun k => (β k) ^ 2) := by
  rw [resource_leftGram_eq_resourceGram, resource_vonNeumannEntropy_eq_entropyBits]

theorem cfc_unitary_conjugate (U : unitary (Matrix κ κ ℂ))
    (ρ : Matrix κ κ ℂ) (hρ : IsSelfAdjoint ρ) (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f ((U : Matrix κ κ ℂ) * ρ * (U : Matrix κ κ ℂ)ᴴ) =
      (U : Matrix κ κ ℂ) * cfc f ρ * (U : Matrix κ κ ℂ)ᴴ := by
  let φ : Matrix κ κ ℂ →⋆ₐ[ℝ] Matrix κ κ ℂ :=
    (Unitary.conjStarAlgAut ℝ (Matrix κ κ ℂ) U).toStarAlgHom
  have hφ : Continuous φ := by
    change Continuous (fun X : Matrix κ κ ℂ =>
      (U : Matrix κ κ ℂ) * X * (U : Matrix κ κ ℂ)ᴴ)
    fun_prop
  have hφρ : IsSelfAdjoint (φ ρ) := hρ.map φ
  have hm := φ.map_cfc f ρ hf.continuousOn hφ hρ hφρ
  exact hm.symm

theorem trace_unitary_conjugate (U : unitary (Matrix κ κ ℂ)) (X : Matrix κ κ ℂ) :
    Matrix.trace ((U : Matrix κ κ ℂ) * X * (U : Matrix κ κ ℂ)ᴴ) =
      Matrix.trace X := by
  have hU : (U : Matrix κ κ ℂ)ᴴ * (U : Matrix κ κ ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem vonNeumannEntropy_unitary_conjugate (U : unitary (Matrix κ κ ℂ))
    (ρ : Matrix κ κ ℂ) (hρ : IsSelfAdjoint ρ) :
    vonNeumannEntropyBits ((U : Matrix κ κ ℂ) * ρ * (U : Matrix κ κ ℂ)ᴴ) =
      vonNeumannEntropyBits ρ := by
  unfold vonNeumannEntropyBits
  rw [cfc_unitary_conjugate U ρ hρ Real.negMulLog Real.continuous_negMulLog,
    trace_unitary_conjugate]

variable {η : Type*} [Fintype η] [DecidableEq η]

def localUnitaryCoefficient (U : unitary (Matrix κ κ ℂ))
    (V : unitary (Matrix η η ℂ)) (Ψ : Matrix κ η ℂ) : Matrix κ η ℂ :=
  (U : Matrix κ κ ℂ) * Ψ * (V : Matrix η η ℂ)ᵀ

theorem localUnitary_leftGram (U : unitary (Matrix κ κ ℂ))
    (V : unitary (Matrix η η ℂ)) (Ψ : Matrix κ η ℂ) :
    localUnitaryCoefficient U V Ψ * (localUnitaryCoefficient U V Ψ)ᴴ =
      (U : Matrix κ κ ℂ) * (Ψ * Ψᴴ) * (U : Matrix κ κ ℂ)ᴴ := by
  have hV : (V : Matrix η η ℂ)ᴴ * (V : Matrix η η ℂ) = 1 :=
    Unitary.coe_star_mul_self V
  have hVT : (V : Matrix η η ℂ)ᵀ * ((V : Matrix η η ℂ)ᵀ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      ← Matrix.transpose_mul, hV, Matrix.transpose_one]
  unfold localUnitaryCoefficient
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc
    _ = (U : Matrix κ κ ℂ) * Ψ *
        ((V : Matrix η η ℂ)ᵀ * ((V : Matrix η η ℂ)ᵀ)ᴴ) * Ψᴴ *
        (U : Matrix κ κ ℂ)ᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hVT, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem localUnitary_leftGram_trace (U : unitary (Matrix κ κ ℂ))
    (V : unitary (Matrix η η ℂ)) (Ψ : Matrix κ η ℂ) :
    Matrix.trace (localUnitaryCoefficient U V Ψ * (localUnitaryCoefficient U V Ψ)ᴴ) =
      Matrix.trace (Ψ * Ψᴴ) := by
  rw [localUnitary_leftGram, trace_unitary_conjugate]

theorem localUnitary_leftGram_isDensity (U : unitary (Matrix κ κ ℂ))
    (V : unitary (Matrix η η ℂ)) (Ψ : Matrix κ η ℂ)
    (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1) :
    QuantumProver.ElegantJointMeasurement.Concurrence.IsDensity
      (localUnitaryCoefficient U V Ψ * (localUnitaryCoefficient U V Ψ)ᴴ) := by
  exact ⟨Matrix.posSemidef_self_mul_conjTranspose _,
    (localUnitary_leftGram_trace U V Ψ).trans hΨ⟩

theorem localUnitary_vonNeumannEntropy (U : unitary (Matrix κ κ ℂ))
    (V : unitary (Matrix η η ℂ)) (Ψ : Matrix κ η ℂ) :
    vonNeumannEntropyBits
      (localUnitaryCoefficient U V Ψ * (localUnitaryCoefficient U V Ψ)ᴴ) =
      vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  rw [localUnitary_leftGram]
  exact vonNeumannEntropy_unitary_conjugate U (Ψ * Ψᴴ)
    (Matrix.posSemidef_self_mul_conjTranspose Ψ).isHermitian.isSelfAdjoint

theorem localUnitary_resource_entropy (U V : unitary (Matrix κ κ ℂ)) (β : κ → ℝ) :
    vonNeumannEntropyBits
      (localUnitaryCoefficient U V (resourceCoefficient β) *
        (localUnitaryCoefficient U V (resourceCoefficient β))ᴴ) =
      QuantumProver.ElegantJointMeasurement.Entropy.entropyBits (fun k => (β k) ^ 2) := by
  rw [localUnitary_vonNeumannEntropy, resource_left_vonNeumannEntropy_eq_entropyBits]

def reducedSchmidtAmplitude (Ψ : Matrix κ η ℂ) : κ → ℝ :=
  fun k => Real.sqrt ((Matrix.isHermitian_mul_conjTranspose_self Ψ).eigenvalues k)

def reducedSchmidtUnitary (Ψ : Matrix κ η ℂ) : unitary (Matrix κ κ ℂ) :=
  (Matrix.isHermitian_mul_conjTranspose_self Ψ).eigenvectorUnitary

omit [DecidableEq η] in
theorem reducedSchmidtAmplitude_nonneg (Ψ : Matrix κ η ℂ) (k : κ) :
    0 ≤ reducedSchmidtAmplitude Ψ k := Real.sqrt_nonneg _

omit [DecidableEq η] in
theorem reducedSchmidtAmplitude_sq (Ψ : Matrix κ η ℂ) (k : κ) :
    (reducedSchmidtAmplitude Ψ k) ^ 2 =
      (Matrix.isHermitian_mul_conjTranspose_self Ψ).eigenvalues k := by
  exact Real.sq_sqrt (Matrix.eigenvalues_self_mul_conjTranspose_nonneg Ψ k)

omit [DecidableEq η] in
theorem reducedSchmidtAmplitude_normalized (Ψ : Matrix κ η ℂ)
    (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1) :
    ∑ k, (reducedSchmidtAmplitude Ψ k) ^ 2 = 1 := by
  have htr := (Matrix.isHermitian_mul_conjTranspose_self Ψ).trace_eq_sum_eigenvalues
  rw [hΨ] at htr
  apply Complex.ofReal_injective
  change ((∑ k, (reducedSchmidtAmplitude Ψ k) ^ 2 : ℝ) : ℂ) = (1 : ℂ)
  rw [Complex.ofReal_sum]
  simp_rw [reducedSchmidtAmplitude_sq]
  exact htr.symm

omit [DecidableEq η] in

theorem leftGram_eq_reducedSchmidt_conjugate (Ψ : Matrix κ η ℂ) :
    Ψ * Ψᴴ = (reducedSchmidtUnitary Ψ : Matrix κ κ ℂ) *
      resourceGram (reducedSchmidtAmplitude Ψ) *
      (reducedSchmidtUnitary Ψ : Matrix κ κ ℂ)ᴴ := by
  rw [resourceGram_eq_diagonal]
  simp_rw [reducedSchmidtAmplitude_sq]
  exact (Matrix.isHermitian_mul_conjTranspose_self Ψ).spectral_theorem

omit [DecidableEq η] in

theorem rectangular_resource_entropy (Ψ : Matrix κ η ℂ) :
    vonNeumannEntropyBits (Ψ * Ψᴴ) =
      QuantumProver.ElegantJointMeasurement.Entropy.entropyBits (fun k => (reducedSchmidtAmplitude Ψ k) ^ 2) := by
  rw [leftGram_eq_reducedSchmidt_conjugate,
    vonNeumannEntropy_unitary_conjugate (reducedSchmidtUnitary Ψ)
      (resourceGram (reducedSchmidtAmplitude Ψ))
      (resourceGram_posSemidef _).isHermitian.isSelfAdjoint,
    resource_vonNeumannEntropy_eq_entropyBits]

omit [DecidableEq η] in

theorem exists_reducedSchmidtRepresentation (Ψ : Matrix κ η ℂ)
    (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1) :
    ∃ (β : κ → ℝ) (U : unitary (Matrix κ κ ℂ)),
      (∀ k, 0 ≤ β k) ∧ (∑ k, (β k) ^ 2 = 1) ∧
      (Ψ * Ψᴴ = (U : Matrix κ κ ℂ) * resourceGram β * (U : Matrix κ κ ℂ)ᴴ) ∧
      vonNeumannEntropyBits (Ψ * Ψᴴ) = QuantumProver.ElegantJointMeasurement.Entropy.entropyBits (fun k => (β k) ^ 2) := by
  exact ⟨reducedSchmidtAmplitude Ψ, reducedSchmidtUnitary Ψ,
    reducedSchmidtAmplitude_nonneg Ψ, reducedSchmidtAmplitude_normalized Ψ hΨ,
    leftGram_eq_reducedSchmidt_conjugate Ψ, rectangular_resource_entropy Ψ⟩

end ResourceEntropy

section OperationalBasisChange

open scoped Kronecker
open QuantumProver.ElegantJointMeasurement.Concurrence

variable {m n : ℕ}

def localPartyUnitary (U : unitary (Matrix κ κ ℂ)) :
    Matrix (Fin 2 × κ) (Fin 2 × κ) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (U : Matrix κ κ ℂ)

def globalResourceUnitary (U V : unitary (Matrix κ κ ℂ)) :
    Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ :=
  localPartyUnitary U ⊗ₖ localPartyUnitary V

theorem localPartyUnitary_star_mul_self (U : unitary (Matrix κ κ ℂ)) :
    (localPartyUnitary U)ᴴ * localPartyUnitary U = 1 := by
  have hU : (U : Matrix κ κ ℂ)ᴴ * (U : Matrix κ κ ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  unfold localPartyUnitary
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, hU, Matrix.one_kronecker_one]

theorem localPartyUnitary_mul_star_self (U : unitary (Matrix κ κ ℂ)) :
    localPartyUnitary U * (localPartyUnitary U)ᴴ = 1 := by
  have hU : (U : Matrix κ κ ℂ) * (U : Matrix κ κ ℂ)ᴴ = 1 :=
    Unitary.coe_mul_star_self U
  unfold localPartyUnitary
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, hU, Matrix.one_kronecker_one]

theorem globalResourceUnitary_star_mul_self (U V : unitary (Matrix κ κ ℂ)) :
    (globalResourceUnitary U V)ᴴ * globalResourceUnitary U V = 1 := by
  unfold globalResourceUnitary
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    localPartyUnitary_star_mul_self, localPartyUnitary_star_mul_self,
    Matrix.one_kronecker_one]

theorem globalResourceUnitary_mul_star_self (U V : unitary (Matrix κ κ ℂ)) :
    globalResourceUnitary U V * (globalResourceUnitary U V)ᴴ = 1 := by
  unfold globalResourceUnitary
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    localPartyUnitary_mul_star_self, localPartyUnitary_mul_star_self,
    Matrix.one_kronecker_one]

def reindexedPartyUnitary (U : unitary (Matrix κ κ ℂ))
    (e : (Fin 2 × κ) ≃ Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.reindex e e (localPartyUnitary U)

theorem reindexedPartyUnitary_complete (U : unitary (Matrix κ κ ℂ))
    (e : (Fin 2 × κ) ≃ Fin m) :
    (reindexedPartyUnitary U e)ᴴ * reindexedPartyUnitary U e = 1 := by
  unfold reindexedPartyUnitary
  rw [Matrix.conjTranspose_reindex]
  change (Matrix.reindexRingEquiv ℂ e (localPartyUnitary U)ᴴ) *
    (Matrix.reindexRingEquiv ℂ e (localPartyUnitary U)) = 1
  rw [← map_mul, localPartyUnitary_star_mul_self, map_one]

def prependResourceUnitaries (U V : unitary (Matrix κ κ ℂ))
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : FiniteLocalKrausTree m n) : FiniteLocalKrausTree m n :=
  .alice m n m 1 (fun _ => reindexedPartyUnitary U ea)
    (by simpa using reindexedPartyUnitary_complete U ea)
    (fun _ => .bob m n n 1 (fun _ => reindexedPartyUnitary V eb)
      (by simpa using reindexedPartyUnitary_complete V eb) (fun _ => T))

def precomposeResourceBra (U V : unitary (Matrix κ κ ℂ))
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (q : SystemBraPair m n) : SystemBraPair m n :=
  (q.precomposeRight (reindexedPartyUnitary V eb)).precomposeLeft
    (reindexedPartyUnitary U ea)

theorem terminalBraPairs_prependResourceUnitaries (U V : unitary (Matrix κ κ ℂ))
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : FiniteLocalKrausTree m n) :
    (prependResourceUnitaries U V ea eb T).terminalBraPairs =
      T.terminalBraPairs.map (precomposeResourceBra U V ea eb) := by
  simp [prependResourceUnitaries, FiniteLocalKrausTree.terminalBraPairs,
    List.ofFn_succ, List.map_map, precomposeResourceBra, Function.comp_def]

theorem terminalBraPairs_length_prependResourceUnitaries (U V : unitary (Matrix κ κ ℂ))
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : FiniteLocalKrausTree m n) :
    (prependResourceUnitaries U V ea eb T).terminalBraPairs.length =
      T.terminalBraPairs.length := by
  rw [terminalBraPairs_prependResourceUnitaries, List.length_map]

def prependOccurrenceEquiv (U V : unitary (Matrix κ κ ℂ))
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : FiniteLocalKrausTree m n) :
    Fin (prependResourceUnitaries U V ea eb T).terminalBraPairs.length ≃
      Fin T.terminalBraPairs.length :=
  finCongr (terminalBraPairs_length_prependResourceUnitaries U V ea eb T)

def prependReport (U V : unitary (Matrix κ κ ℂ))
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : FiniteLocalKrausTree m n) (report : Fin T.terminalBraPairs.length → Fin 4) :
    Fin (prependResourceUnitaries U V ea eb T).terminalBraPairs.length → Fin 4 :=
  report ∘ prependOccurrenceEquiv U V ea eb T

theorem terminalBraPair_get_prependResourceUnitaries (U V : unitary (Matrix κ κ ℂ))
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : FiniteLocalKrausTree m n)
    (i : Fin (prependResourceUnitaries U V ea eb T).terminalBraPairs.length) :
    (prependResourceUnitaries U V ea eb T).terminalBraPairs.get i =
      precomposeResourceBra U V ea eb
        (T.terminalBraPairs.get (prependOccurrenceEquiv U V ea eb T i)) := by
  simp only [List.get_eq_getElem, prependOccurrenceEquiv, finCongr_apply_coe,
    terminalBraPairs_prependResourceUnitaries, List.getElem_map]

private theorem productEffect_precomposeBoth (q : SystemBraPair m n)
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    ((q.precomposeRight B).precomposeLeft A).productEffect =
      (A ⊗ₖ B)ᴴ * q.productEffect * (A ⊗ₖ B) := by
  rw [SystemBraPair.productEffect_precomposeLeft, SystemBraPair.productEffect_precomposeRight]
  have hp : ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ B) *
      (A ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) = A ⊗ₖ B := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  calc
    _ = (((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ B) *
        (A ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)))ᴴ * q.productEffect *
        (((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ B) *
        (A ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))) := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hp]

private theorem reindexedPartyUnitary_tensor_pullback (U V : unitary (Matrix κ κ ℂ))
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n) :
    (reindexedPartyUnitary U ea ⊗ₖ reindexedPartyUnitary V eb).submatrix
      (ea.prodCongr eb) (ea.prodCongr eb) = globalResourceUnitary U V := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [reindexedPartyUnitary, Matrix.reindex_apply,
    globalResourceUnitary, Matrix.submatrix_apply]

theorem physicalEffect_precomposeResourceBra (U V : unitary (Matrix κ κ ℂ))
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (q : SystemBraPair m n) :
    QuantumProver.ElegantJointMeasurement.ProtocolEffects.physicalEffect (precomposeResourceBra U V ea eb q) ea eb =
      (globalResourceUnitary U V)ᴴ * QuantumProver.ElegantJointMeasurement.ProtocolEffects.physicalEffect q ea eb *
        globalResourceUnitary U V := by
  rw [QuantumProver.ElegantJointMeasurement.ProtocolEffects.physicalEffect_eq_pullback, precomposeResourceBra,
    productEffect_precomposeBoth, QuantumProver.ElegantJointMeasurement.ProtocolEffects.physicalEffect_eq_pullback]
  change ((_ * q.productEffect * _).submatrix (ea.prodCongr eb) (ea.prodCongr eb)) = _
  rw [← Matrix.submatrix_mul_equiv _ _ (ea.prodCongr eb) (ea.prodCongr eb) (ea.prodCongr eb),
    ← Matrix.submatrix_mul_equiv _ _ (ea.prodCongr eb) (ea.prodCongr eb) (ea.prodCongr eb),
    ← Matrix.conjTranspose_submatrix, reindexedPartyUnitary_tensor_pullback]
  rfl

theorem groupedEffect_prependResourceUnitaries (U V : unitary (Matrix κ κ ℂ))
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : FiniteLocalKrausTree m n) (report : Fin T.terminalBraPairs.length → Fin 4)
    (j : Fin 4) :
    QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect (prependResourceUnitaries U V ea eb T) ea eb
      (prependReport U V ea eb T report) j =
      (globalResourceUnitary U V)ᴴ * QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect T ea eb report j *
        globalResourceUnitary U V := by
  unfold QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect QuantumProver.ElegantJointMeasurement.ProtocolEffects.outcomeSum prependReport
  simp only [Function.comp_apply, terminalBraPair_get_prependResourceUnitaries,
    physicalEffect_precomposeResourceBra]
  rw [(prependOccurrenceEquiv U V ea eb T).sum_comp (fun i : Fin T.terminalBraPairs.length =>
    if report i = j then
      (globalResourceUnitary U V)ᴴ *
        QuantumProver.ElegantJointMeasurement.ProtocolEffects.physicalEffect (T.terminalBraPairs.get i) ea eb *
        globalResourceUnitary U V else 0)]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

theorem groupedEffect_limit_prependResourceUnitaries
    {δ : Type*} {l : Filter δ}
    (U V : unitary (Matrix κ κ ℂ))
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : δ → FiniteLocalKrausTree m n)
    (report : (a : δ) → Fin (T a).terminalBraPairs.length → Fin 4)
    (F : Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ)
    (hlim : Filter.Tendsto (fun a j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect (T a) ea eb
      (report a) j) l (nhds F)) :
    Filter.Tendsto (fun a j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect
      (prependResourceUnitaries U V ea eb (T a)) ea eb
      (prependReport U V ea eb (T a) (report a)) j) l
      (nhds (fun j => (globalResourceUnitary U V)ᴴ * F j * globalResourceUnitary U V)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  simp_rw [groupedEffect_prependResourceUnitaries]
  exact (tendsto_const_nhds.mul ((tendsto_pi_nhds.mp hlim) j)).mul tendsto_const_nhds

end OperationalBasisChange

section ActualTreeEffectClosure

open QuantumProver.ElegantJointMeasurement.Concurrence

variable {m n : ℕ}

def finiteTreeEffectSet (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n) :
    Set (Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ) :=
  {G | ∃ (T : FiniteLocalKrausTree m n)
    (report : Fin T.terminalBraPairs.length → Fin 4),
    G = fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect T ea eb report j}

omit [Fintype κ] [DecidableEq κ] in
theorem groupedEffect_mem_finiteTreeEffectSet
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : FiniteLocalKrausTree m n) (report : Fin T.terminalBraPairs.length → Fin 4) :
    (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect T ea eb report j) ∈
      finiteTreeEffectSet ea eb := ⟨T, report, rfl⟩

omit [DecidableEq κ] in

theorem finiteTreeEffectSet_closure_sequence
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (F : Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ)
    (hF : F ∈ closure (finiteTreeEffectSet ea eb)) :
    ∃ (T : ℕ → FiniteLocalKrausTree m n)
      (report : (a : ℕ) → Fin (T a).terminalBraPairs.length → Fin 4),
      Filter.Tendsto (fun a j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect (T a) ea eb
        (report a) j) Filter.atTop (nhds F) := by
  have : FirstCountableTopology (Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ) :=
    inferInstanceAs (FirstCountableTopology (QuantumProver.ElegantJointMeasurement.Augmented.Index κ → QuantumProver.ElegantJointMeasurement.Augmented.Index κ → ℂ))
  obtain ⟨G, hG, hlim⟩ := mem_closure_iff_seq_limit.mp hF
  change ∀ a : ℕ, ∃ (T : FiniteLocalKrausTree m n)
    (report : Fin T.terminalBraPairs.length → Fin 4),
    G a = fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect T ea eb report j at hG
  choose T report hEq using hG
  refine ⟨T, report, ?_⟩
  have hEqFun : G = fun a j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect (T a) ea eb (report a) j :=
    funext hEq
  rwa [← hEqFun]

omit [Fintype κ] [DecidableEq κ] in

theorem finiteTreeEffectSet_mem_closure_of_tendsto
    {δ : Type*} {l : Filter δ} [l.NeBot]
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : δ → FiniteLocalKrausTree m n)
    (report : (a : δ) → Fin (T a).terminalBraPairs.length → Fin 4)
    (F : Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ)
    (hlim : Filter.Tendsto (fun a j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect (T a) ea eb
      (report a) j) l (nhds F)) :
    F ∈ closure (finiteTreeEffectSet ea eb) := by
  apply isClosed_closure.mem_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun a =>
    subset_closure (groupedEffect_mem_finiteTreeEffectSet ea eb (T a) (report a)))

omit [DecidableEq κ] in
theorem finiteTreeEffectSet_closure_iff_sequence
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (F : Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ) :
    F ∈ closure (finiteTreeEffectSet ea eb) ↔
      ∃ (T : ℕ → FiniteLocalKrausTree m n)
        (report : (a : ℕ) → Fin (T a).terminalBraPairs.length → Fin 4),
        Filter.Tendsto (fun a j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect (T a) ea eb
          (report a) j) Filter.atTop (nhds F) := by
  constructor
  · exact finiteTreeEffectSet_closure_sequence ea eb F
  · rintro ⟨T, report, hlim⟩
    exact finiteTreeEffectSet_mem_closure_of_tendsto ea eb T report F hlim

theorem finiteTreeEffectSet_closure_unitary
    (U V : unitary (Matrix κ κ ℂ))
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (F : Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ)
    (hF : F ∈ closure (finiteTreeEffectSet ea eb)) :
    (fun j => (globalResourceUnitary U V)ᴴ * F j * globalResourceUnitary U V) ∈
      closure (finiteTreeEffectSet ea eb) := by
  obtain ⟨T, report, hlim⟩ := finiteTreeEffectSet_closure_sequence ea eb F hF
  exact finiteTreeEffectSet_mem_closure_of_tendsto ea eb
    (fun a => prependResourceUnitaries U V ea eb (T a))
    (fun a => prependReport U V ea eb (T a) (report a)) _
    (groupedEffect_limit_prependResourceUnitaries U V ea eb T report F hlim)

end ActualTreeEffectClosure

namespace DiscreteProtocol

open QuantumProver.ElegantJointMeasurement.Concurrence
open scoped Kronecker

set_option maxHeartbeats 600000

@[reducible] def LeafReports : {m n : ℕ} → FiniteLocalKrausTree m n → Type
  | _, _, .leaf _ _ => Fin 4
  | _, _, .alice _ _ _ _ _ _ next => ∀ s, LeafReports (next s)
  | _, _, .bob _ _ _ _ _ _ next => ∀ s, LeafReports (next s)

def reportedBras : {m n : ℕ} → (T : FiniteLocalKrausTree m n) →
    LeafReports T → List (SystemBraPair m n × Fin 4)
  | _, _, .leaf m n, label =>
      ((FiniteLocalKrausTree.leaf m n).terminalBraPairs).map (fun q => (q, label))
  | _, _, .alice _ _ _ _ A _ next, label =>
      (List.ofFn fun s => (reportedBras (next s) (label s)).map
        (fun p => (p.1.precomposeLeft (A s), p.2))).flatten
  | _, _, .bob _ _ _ _ B _ next, label =>
      (List.ofFn fun s => (reportedBras (next s) (label s)).map
        (fun p => (p.1.precomposeRight (B s), p.2))).flatten

theorem reportedBras_fst {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (label : LeafReports T) :
    (reportedBras T label).map Prod.fst = T.terminalBraPairs := by
  induction T with
  | leaf m n => simp [reportedBras, List.map_map, Function.comp_def]
  | alice m n out outcomes A complete next ih =>
    simp only [reportedBras, FiniteLocalKrausTree.terminalBraPairs,
      List.map_flatten, List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext s
    simp only [List.map_map, Function.comp_def]
    have h := congrArg (List.map (fun q => q.precomposeLeft (A s))) (ih s (label s))
    simpa only [List.map_map, Function.comp_def] using h
  | bob m n out outcomes B complete next ih =>
    simp only [reportedBras, FiniteLocalKrausTree.terminalBraPairs,
      List.map_flatten, List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext s
    simp only [List.map_map, Function.comp_def]
    have h := congrArg (List.map (fun q => q.precomposeRight (B s))) (ih s (label s))
    simpa only [List.map_map, Function.comp_def] using h

theorem reportedBras_length {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (label : LeafReports T) : (reportedBras T label).length = T.terminalBraPairs.length := by
  simpa using congrArg List.length (reportedBras_fst T label)

def occurrence {m n : ℕ} (T : FiniteLocalKrausTree m n) (label : LeafReports T) :
    Fin T.terminalBraPairs.length ≃ Fin (reportedBras T label).length :=
  (finCongr (reportedBras_length T label)).symm

def report {m n : ℕ} (T : FiniteLocalKrausTree m n) (label : LeafReports T)
    (i : Fin T.terminalBraPairs.length) : Fin 4 :=
  ((reportedBras T label).get (occurrence T label i)).2

theorem reportedBras_get_fst {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (label : LeafReports T) (i : Fin T.terminalBraPairs.length) :
    ((reportedBras T label).get (occurrence T label i)).1 = T.terminalBraPairs.get i := by
  have hi : i.val < (reportedBras T label).length := by
    rw [reportedBras_length T label]
    exact i.isLt
  have h := congrArg (fun l : List (SystemBraPair m n) => l[i.val]?)
    (reportedBras_fst T label)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem i.isLt, Option.map_some, Option.some.injEq] at h
  simpa [List.get_eq_getElem, occurrence] using h

def reportedEffect {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (label : LeafReports T) (j : Fin 4) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  ((reportedBras T label).map (fun p => if p.2 = j then p.1.productEffect else 0)).sum

theorem reportedEffect_eq_occurrence_sum {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (label : LeafReports T) (j : Fin 4) :
    reportedEffect T label j = ∑ i : Fin T.terminalBraPairs.length,
      if report T label i = j then (T.terminalBraPairs.get i).productEffect else 0 := by
  rw [reportedEffect, ← QuantumProver.ElegantJointMeasurement.ProtocolEffects.sum_get_map]
  rw [← Equiv.sum_comp (occurrence T label)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [report, reportedBras_get_fst]
  rfl

theorem groupedEffect_eq_pullback {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (T : FiniteLocalKrausTree m n) (label : LeafReports T) (j : Fin 4) :
    QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect T ea eb (report T label) j =
      QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (reportedEffect T label j) := by
  rw [reportedEffect_eq_occurrence_sum, map_sum]
  unfold QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect QuantumProver.ElegantJointMeasurement.ProtocolEffects.outcomeSum
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp [QuantumProver.ElegantJointMeasurement.ProtocolEffects.physicalEffect_eq_pullback]

theorem reportedEffect_leaf (m n : ℕ) (label j : Fin 4) :
    reportedEffect (.leaf m n) label j = if label = j then 1 else 0 := by
  by_cases h : label = j
  · simp only [reportedEffect, reportedBras, List.map_map, Function.comp_def, h, ite_true]
    exact FiniteLocalKrausTree.terminalProductEffect_leaf m n
  · simp [reportedEffect, reportedBras, List.map_map, Function.comp_def, h]

theorem reportedEffect_alice (m n out outcomes : ℕ)
    (A : Fin outcomes → Matrix (Fin out) (Fin m) ℂ)
    (complete : ∑ s, (A s)ᴴ * A s = 1)
    (next : Fin outcomes → FiniteLocalKrausTree out n)
    (label : ∀ s, LeafReports (next s)) (j : Fin 4) :
    reportedEffect (.alice m n out outcomes A complete next) label j =
      ∑ s, (A s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ *
        reportedEffect (next s) (label s) j * (A s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  simp only [reportedEffect, reportedBras, List.map_flatten, List.sum_flatten,
    List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← QuantumProver.ElegantJointMeasurement.Concurrence.list_sum_map_sandwich]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  split_ifs
  · exact SystemBraPair.productEffect_precomposeLeft p.1 (A s)
  · simp

theorem reportedEffect_bob (m n out outcomes : ℕ)
    (B : Fin outcomes → Matrix (Fin out) (Fin n) ℂ)
    (complete : ∑ s, (B s)ᴴ * B s = 1)
    (next : Fin outcomes → FiniteLocalKrausTree m out)
    (label : ∀ s, LeafReports (next s)) (j : Fin 4) :
    reportedEffect (.bob m n out outcomes B complete next) label j =
      ∑ s, ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ B s)ᴴ *
        reportedEffect (next s) (label s) j * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ B s) := by
  simp only [reportedEffect, reportedBras, List.map_flatten, List.sum_flatten,
    List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← QuantumProver.ElegantJointMeasurement.Concurrence.list_sum_map_sandwich]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  split_ifs
  · exact SystemBraPair.productEffect_precomposeRight p.1 (B s)
  · simp

structure ReportedTree (m n : ℕ) where
  tree : FiniteLocalKrausTree m n
  label : LeafReports tree

inductive CountableNode (m n : ℕ) where
  | terminal (j : Fin 4)
  | alice (K : ℕ → Matrix (Fin m) (Fin m) ℂ)
      (summable : Summable (fun s => (K s)ᴴ * K s))
      (complete : (∑' s, (K s)ᴴ * K s) = 1)
  | bob (K : ℕ → Matrix (Fin n) (Fin n) ℂ)
      (summable : Summable (fun s => (K s)ᴴ * K s))
      (complete : (∑' s, (K s)ᴴ * K s) = 1)

structure CountableProtocol (m n : ℕ) where
  node : List ℕ → CountableNode m n

def terminalLabel {m n : ℕ} (P : CountableProtocol m n) (h : List ℕ) : Option (Fin 4) :=
  match P.node h with
  | .terminal j => some j
  | .alice _ _ _ => none
  | .bob _ _ _ => none

def stepOperator {m n : ℕ} (P : CountableProtocol m n) (h : List ℕ) (s : ℕ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  match P.node h with
  | .terminal _ => 0
  | .alice K _ _ => K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)
  | .bob K _ _ => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s

def pathOperator {m n : ℕ} (P : CountableProtocol m n) : List ℕ → List ℕ →
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ
  | _, [] => 1
  | h, s :: w => pathOperator P (h ++ [s]) w * stepOperator P h s

def terminalEffect {m n : ℕ} (P : CountableProtocol m n) (h w : List ℕ) (j : Fin 4) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  if terminalLabel P (h ++ w) = some j then
    (pathOperator P h w)ᴴ * pathOperator P h w else 0

theorem terminalEffect_posSemidef {m n : ℕ} (P : CountableProtocol m n)
    (h w : List ℕ) (j : Fin 4) : (terminalEffect P h w j).PosSemidef := by
  unfold terminalEffect
  split_ifs
  · exact Matrix.posSemidef_conjTranspose_mul_self _
  · exact Matrix.PosSemidef.zero

def terminalEffects {m n : ℕ} (P : CountableProtocol m n) (h : List ℕ) (j : Fin 4) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ := ∑' w, terminalEffect P h w j

def GloballyDeterministic {m n : ℕ} (P : CountableProtocol m n) (h : List ℕ) : Prop :=
  (∀ j, Summable (fun w => terminalEffect P h w j)) ∧ ∑ j, terminalEffects P h j = 1

theorem terminalEffect_cons {m n : ℕ} (P : CountableProtocol m n)
    (h w : List ℕ) (s : ℕ) (j : Fin 4) :
    terminalEffect P h (s :: w) j = (stepOperator P h s)ᴴ *
      terminalEffect P (h ++ [s]) w j * stepOperator P h s := by
  have happ : h ++ s :: w = (h ++ [s]) ++ w := by simp
  simp only [terminalEffect, happ, pathOperator, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]
  split_ifs <;> simp [Matrix.mul_assoc]

def boundedWords (S : Finset ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | d + 1 => insert [] (S.biUnion fun s => (boundedWords S d).image (List.cons s))

theorem mem_boundedWords (S : Finset ℕ) (d : ℕ) (w : List ℕ) :
    w ∈ boundedWords S d ↔ w.length ≤ d ∧ ∀ s ∈ w, s ∈ S := by
  induction d generalizing w with
  | zero => cases w <;> simp [boundedWords]
  | succ d ih =>
    cases w with
    | nil => simp [boundedWords]
    | cons s w =>
      simp [boundedWords, Finset.mem_biUnion, ih, List.length_cons,
        and_assoc, and_left_comm, and_comm]

theorem boundedWords_sum {M : Type*} [AddCommMonoid M]
    (S : Finset ℕ) (d : ℕ) (f : List ℕ → M) :
    (∑ w ∈ boundedWords S (d + 1), f w) =
      f [] + ∑ s ∈ S, ∑ w ∈ boundedWords S d, f (s :: w) := by
  have hnil : [] ∉ S.biUnion (fun s => (boundedWords S d).image (List.cons s)) := by
    simp
  have hdis : Set.PairwiseDisjoint (↑S)
      (fun s => (boundedWords S d).image (List.cons s)) := by
    intro s hs t ht hst
    apply Finset.disjoint_left.mpr
    intro w hw hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hv
    exact hst (List.cons.inj heq).1.symm
  rw [boundedWords, Finset.sum_insert hnil, Finset.sum_biUnion hdis]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_image (by intro u hu v hv h; exact List.cons.inj h |>.2)]

theorem boundedWords_exhaust :
    Filter.Tendsto (fun N => boundedWords (Finset.range N) N)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_finset_of_monotone
  · intro N M hNM w hw
    rw [mem_boundedWords] at hw ⊢
    exact ⟨hw.1.trans hNM, fun s hs =>
      Finset.mem_range.mpr ((Finset.mem_range.mp (hw.2 s hs)).trans_le hNM)⟩
  · intro w
    refine ⟨w.length + w.toFinset.sup id + 1, ?_⟩
    rw [mem_boundedWords]
    refine ⟨by omega, ?_⟩
    intro s hs
    apply Finset.mem_range.mpr
    have hle : s ≤ w.toFinset.sup id := Finset.le_sup (f := id) (by simpa using hs)
    omega

def selectedEffects {m n : ℕ} (P : CountableProtocol m n) (S : Finset ℕ) :
    ℕ → List ℕ → Fin 4 → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ
  | 0, h, j => if terminalLabel P h = some j then 1 else 0
  | d + 1, h, j => match P.node h with
      | .terminal ell => if ell = j then 1 else 0
      | .alice K _ _ => ∑ s ∈ S,
          (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ *
            selectedEffects P S d (h ++ [s]) j * (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
      | .bob K _ _ => ∑ s ∈ S,
          ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s)ᴴ *
            selectedEffects P S d (h ++ [s]) j * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s)

theorem selectedEffects_eq_terminal_sum {m n : ℕ} (P : CountableProtocol m n)
    (S : Finset ℕ) (d : ℕ) (h : List ℕ) (j : Fin 4) :
    selectedEffects P S d h j = ∑ w ∈ boundedWords S d, terminalEffect P h w j := by
  induction d generalizing h with
  | zero => simp [selectedEffects, boundedWords, terminalEffect, pathOperator]
  | succ d ih =>
    rw [boundedWords_sum]
    simp only [terminalEffect_cons]
    cases hn : P.node h with
    | terminal ell =>
      simp [selectedEffects, hn, terminalLabel, stepOperator, terminalEffect, pathOperator]
    | alice K hs hc =>
      simp only [selectedEffects, stepOperator, terminalEffect, pathOperator,
        List.append_nil, terminalLabel, hn, reduceCtorEq, ite_false, zero_add]
      apply Finset.sum_congr rfl
      intro s hs
      rw [ih, Matrix.mul_sum, Matrix.sum_mul]
      rfl
    | bob K hs hc =>
      simp only [selectedEffects, stepOperator, terminalEffect, pathOperator,
        List.append_nil, terminalLabel, hn, reduceCtorEq, ite_false, zero_add]
      apply Finset.sum_congr rfl
      intro s hs
      rw [ih, Matrix.mul_sum, Matrix.sum_mul]
      rfl

theorem selectedEffects_tendsto {m n : ℕ} (P : CountableProtocol m n)
    (h : List ℕ) (hs : ∀ j, Summable (fun w => terminalEffect P h w j)) :
    Filter.Tendsto (fun N j => selectedEffects P (Finset.range N) N h j)
      Filter.atTop (nhds (terminalEffects P h)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  simp_rw [selectedEffects_eq_terminal_sum]
  exact (hs j).hasSum.comp boundedWords_exhaust

def completeEffects {a : Type*} [Fintype a] [DecidableEq a]
    (F : Fin 4 → Matrix a a ℂ) (abort j : Fin 4) : Matrix a a ℂ :=
  F j + if abort = j then 1 - ∑ ell, F ell else 0

theorem sum_sandwich_completeEffects {a ι : Type*}
    [Fintype a] [DecidableEq a] [Fintype ι]
    (L : ι → Matrix a a ℂ) (hL : ∑ s, (L s)ᴴ * L s = 1)
    (F : ι → Fin 4 → Matrix a a ℂ) (abort j : Fin 4) :
    (∑ s, (L s)ᴴ * completeEffects (F s) abort j * L s) =
      completeEffects (fun ell => ∑ s, (L s)ᴴ * F s ell * L s) abort j := by
  by_cases hj : abort = j
  · have hsum : (∑ s, (L s)ᴴ * (∑ ell, F s ell) * L s) =
        ∑ ell, ∑ s, (L s)ᴴ * F s ell * L s := by
      simp_rw [Matrix.mul_sum, Matrix.sum_mul]
      exact Finset.sum_comm
    simp only [completeEffects, hj, ite_true, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, hL, hsum]
  · simp [completeEffects, hj]

namespace ReportedTree

def leaf (m n : ℕ) (label : Fin 4) : ReportedTree m n := ⟨.leaf m n, label⟩

def alice {m n out outcomes : ℕ}
    (K : Fin outcomes → Matrix (Fin out) (Fin m) ℂ)
    (complete : ∑ s, (K s)ᴴ * K s = 1)
    (next : Fin outcomes → ReportedTree out n) : ReportedTree m n :=
  ⟨.alice m n out outcomes K complete (fun s => (next s).tree), fun s => (next s).label⟩

def bob {m n out outcomes : ℕ}
    (K : Fin outcomes → Matrix (Fin out) (Fin n) ℂ)
    (complete : ∑ s, (K s)ᴴ * K s = 1)
    (next : Fin outcomes → ReportedTree m out) : ReportedTree m n :=
  ⟨.bob m n out outcomes K complete (fun s => (next s).tree), fun s => (next s).label⟩

def effect {m n : ℕ} (T : ReportedTree m n) (j : Fin 4) :=
  reportedEffect T.tree T.label j

@[simp] theorem effect_leaf (m n : ℕ) (ell j : Fin 4) :
    (leaf m n ell).effect j = if ell = j then 1 else 0 := reportedEffect_leaf m n ell j

theorem effect_alice {m n out outcomes : ℕ}
    (K : Fin outcomes → Matrix (Fin out) (Fin m) ℂ)
    (complete : ∑ s, (K s)ᴴ * K s = 1)
    (next : Fin outcomes → ReportedTree out n) (j : Fin 4) :
    (alice K complete next).effect j = ∑ s,
      (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ * (next s).effect j *
        (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) :=
  reportedEffect_alice m n out outcomes K complete (fun s => (next s).tree)
    (fun s => (next s).label) j

theorem effect_bob {m n out outcomes : ℕ}
    (K : Fin outcomes → Matrix (Fin out) (Fin n) ℂ)
    (complete : ∑ s, (K s)ᴴ * K s = 1)
    (next : Fin outcomes → ReportedTree m out) (j : Fin 4) :
    (bob K complete next).effect j = ∑ s,
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s)ᴴ * (next s).effect j *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s) :=
  reportedEffect_bob m n out outcomes K complete (fun s => (next s).tree)
    (fun s => (next s).label) j

end ReportedTree

open QuantumProver.ElegantJointMeasurement.CountableInstruments

def truncation {m n : ℕ} (P : CountableProtocol m n) (bA : Fin m) (bB : Fin n)
    (S : Finset ℕ) (abort : Fin 4) : ℕ → List ℕ → ReportedTree m n
  | 0, h => ReportedTree.leaf m n ((terminalLabel P h).getD abort)
  | d + 1, h => match P.node h with
      | .terminal j => ReportedTree.leaf m n j
      | .alice K hs hc =>
        ReportedTree.alice (finiteCutoffKraus K S bA)
          (finiteCutoffKraus_complete K hs hc S bA)
          (fun q => match (cutoffLabelEquiv S).symm q with
            | .inl s => truncation P bA bB S abort d (h ++ [(s : ℕ)])
            | .inr _ => ReportedTree.leaf m n abort)
      | .bob K hs hc =>
        ReportedTree.bob (finiteCutoffKraus K S bB)
          (finiteCutoffKraus_complete K hs hc S bB)
          (fun q => match (cutoffLabelEquiv S).symm q with
            | .inl s => truncation P bA bB S abort d (h ++ [(s : ℕ)])
            | .inr _ => ReportedTree.leaf m n abort)

theorem completeEffects_terminal {a : Type*} [Fintype a] [DecidableEq a]
    (ell abort j : Fin 4) :
    completeEffects (fun k => if ell = k then (1 : Matrix a a ℂ) else 0) abort j =
      if ell = j then 1 else 0 := by
  simp [completeEffects]

theorem cutoff_sandwich_selected {a : Type*} [Fintype a] [DecidableEq a]
    {input : ℕ} (S : Finset ℕ) (L : ℕ → Matrix a a ℂ)
    (abortL : Fin input → Matrix a a ℂ) (F : ℕ → Matrix a a ℂ) :
    (∑ q : Fin (S.card + input),
      (Sum.elim (fun s : S => L s) abortL ((cutoffLabelEquiv S).symm q))ᴴ *
        (Sum.elim (fun s : S => F s) (fun _ => 0) ((cutoffLabelEquiv S).symm q)) *
        (Sum.elim (fun s : S => L s) abortL ((cutoffLabelEquiv S).symm q))) =
      ∑ s ∈ S, (L s)ᴴ * F s * L s := by
  rw [← (cutoffLabelEquiv S).sum_comp]
  simp [Fintype.sum_sum_type]
  exact Finset.sum_attach S (fun s => (L s)ᴴ * F s * L s)

theorem truncation_effect {m n : ℕ} (P : CountableProtocol m n)
    (bA : Fin m) (bB : Fin n) (S : Finset ℕ) (abort : Fin 4)
    (d : ℕ) (h : List ℕ) (j : Fin 4) :
    (truncation P bA bB S abort d h).effect j =
      completeEffects (selectedEffects P S d h) abort j := by
  induction d generalizing h with
  | zero =>
    cases hn : P.node h with
    | terminal ell =>
      simpa [truncation, terminalLabel, hn, selectedEffects, ReportedTree.effect_leaf]
        using (completeEffects_terminal (a := Fin m × Fin n) ell abort j).symm
    | alice K hs hc => simp [truncation, terminalLabel, hn, selectedEffects, completeEffects]
    | bob K hs hc => simp [truncation, terminalLabel, hn, selectedEffects, completeEffects]
  | succ d ih =>
    cases hn : P.node h with
    | terminal ell =>
      simpa [truncation, hn, selectedEffects] using
        (completeEffects_terminal (a := Fin m × Fin n) ell abort j).symm
    | alice K hs hc =>
      let E := cutoffLabelEquiv (input := m) S
      let A := finiteCutoffKraus K S bA
      let next : Fin (S.card + m) → ReportedTree m n := fun q => match E.symm q with
        | .inl s => truncation P bA bB S abort d (h ++ [(s : ℕ)])
        | .inr _ => ReportedTree.leaf m n abort
      let F : Fin (S.card + m) → Fin 4 → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
        fun q ell => match E.symm q with
          | .inl s => selectedEffects P S d (h ++ [(s : ℕ)]) ell
          | .inr _ => 0
      have ht : truncation P bA bB S abort (d + 1) h =
          ReportedTree.alice A (finiteCutoffKraus_complete K hs hc S bA) next := by
        simp only [truncation, hn]
        rfl
      have heff (q : Fin (S.card + m)) :
          (next q).effect j = completeEffects (F q) abort j := by
        cases hq : E.symm q with
        | inl s => simpa only [next, F, hq] using ih (h ++ [(s : ℕ)])
        | inr t => simp [next, F, hq, completeEffects]
      rw [ht, ReportedTree.effect_alice]
      simp_rw [heff]
      rw [sum_sandwich_completeEffects _
        (kronecker_left_complete A (finiteCutoffKraus_complete K hs hc S bA))]
      apply congrArg (fun G => completeEffects G abort j)
      funext ell
      simp only [selectedEffects, hn]
      rw [← E.sum_comp]
      simp [E, A, F, finiteCutoffKraus, cutoffKraus, Fintype.sum_sum_type]
      exact Finset.sum_attach S (fun s => (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ *
        selectedEffects P S d (h ++ [s]) ell * (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)))
    | bob K hs hc =>
      let E := cutoffLabelEquiv (input := n) S
      let B := finiteCutoffKraus K S bB
      let next : Fin (S.card + n) → ReportedTree m n := fun q => match E.symm q with
        | .inl s => truncation P bA bB S abort d (h ++ [(s : ℕ)])
        | .inr _ => ReportedTree.leaf m n abort
      let F : Fin (S.card + n) → Fin 4 → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
        fun q ell => match E.symm q with
          | .inl s => selectedEffects P S d (h ++ [(s : ℕ)]) ell
          | .inr _ => 0
      have ht : truncation P bA bB S abort (d + 1) h =
          ReportedTree.bob B (finiteCutoffKraus_complete K hs hc S bB) next := by
        simp only [truncation, hn]
        rfl
      have heff (q : Fin (S.card + n)) :
          (next q).effect j = completeEffects (F q) abort j := by
        cases hq : E.symm q with
        | inl s => simpa only [next, F, hq] using ih (h ++ [(s : ℕ)])
        | inr t => simp [next, F, hq, completeEffects]
      rw [ht, ReportedTree.effect_bob]
      simp_rw [heff]
      rw [sum_sandwich_completeEffects _
        (kronecker_right_complete B (finiteCutoffKraus_complete K hs hc S bB))]
      apply congrArg (fun G => completeEffects G abort j)
      funext ell
      simp only [selectedEffects, hn]
      rw [← E.sum_comp]
      simp [E, B, F, finiteCutoffKraus, cutoffKraus, Fintype.sum_sum_type]
      exact Finset.sum_attach S (fun s => ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s)ᴴ *
        selectedEffects P S d (h ++ [s]) ell * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s))

theorem truncation_effect_tendsto {m n : ℕ} (P : CountableProtocol m n)
    (bA : Fin m) (bB : Fin n) (abort : Fin 4) (h : List ℕ)
    (hP : GloballyDeterministic P h) :
    Filter.Tendsto (fun N j => (truncation P bA bB (Finset.range N) abort N h).effect j)
      Filter.atTop (nhds (terminalEffects P h)) := by
  have hc : Continuous (fun F : Fin 4 → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ =>
      fun j => completeEffects F abort j) := by
    apply continuous_pi
    intro j
    unfold completeEffects
    split_ifs <;> fun_prop
  have hlim := (hc.tendsto (terminalEffects P h)).comp (selectedEffects_tendsto P h hP.1)
  simp only [completeEffects, hP.2, sub_self, ite_self, add_zero] at hlim
  simpa only [truncation_effect, completeEffects, Function.comp_def] using hlim

theorem countableProtocol_mem_finiteTreeEffectSet_closure {m n : ℕ}
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : CountableProtocol m n) (bA : Fin m) (bB : Fin n) (abort : Fin 4)
    (h : List ℕ) (hP : GloballyDeterministic P h) :
    (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffects P h j)) ∈
      closure (finiteTreeEffectSet ea eb) := by
  let T := fun N => truncation P bA bB (Finset.range N) abort N h
  have hc : Continuous (fun F : Fin 4 → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ =>
      fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (F j)) := by
    unfold QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect
    fun_prop
  apply finiteTreeEffectSet_mem_closure_of_tendsto (l := Filter.atTop) ea eb
    (fun N => (T N).tree) (fun N => report (T N).tree (T N).label)
  simp_rw [groupedEffect_eq_pullback]
  exact (hc.tendsto (terminalEffects P h)).comp
    (truncation_effect_tendsto P bA bB abort h hP)

theorem terminalEffects_posSemidef {m n : ℕ} (P : CountableProtocol m n)
    (h : List ℕ) (j : Fin 4) : (terminalEffects P h j).PosSemidef := by
  exact Matrix.nonneg_iff_posSemidef.mp (tsum_nonneg
    (fun w => (terminalEffect_posSemidef P h w j).nonneg))

theorem selectedEffects_le_terminalEffects {m n : ℕ} (P : CountableProtocol m n)
    (h : List ℕ) (hs : ∀ j, Summable (fun w => terminalEffect P h w j))
    (S : Finset ℕ) (d : ℕ) (j : Fin 4) :
    selectedEffects P S d h j ≤ terminalEffects P h j := by
  rw [selectedEffects_eq_terminal_sum]
  exact (hs j).sum_le_tsum (boundedWords S d)
    (fun w _ => (terminalEffect_posSemidef P h w j).nonneg)

def abortResidual {m n : ℕ} (P : CountableProtocol m n)
    (S : Finset ℕ) (d : ℕ) (h : List ℕ) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  1 - ∑ j, selectedEffects P S d h j

theorem abortResidual_posSemidef {m n : ℕ} (P : CountableProtocol m n)
    (h : List ℕ) (hP : GloballyDeterministic P h) (S : Finset ℕ) (d : ℕ) :
    (abortResidual P S d h).PosSemidef := by
  have hle := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    selectedEffects_le_terminalEffects P h hP.1 S d j)
  rw [hP.2] at hle
  exact hle

theorem omittedOutcome_le_abortResidual {m n : ℕ} (P : CountableProtocol m n)
    (h : List ℕ) (hP : GloballyDeterministic P h) (S : Finset ℕ) (d : ℕ) (j : Fin 4) :
    terminalEffects P h j - selectedEffects P S d h j ≤ abortResidual P S d h := by
  have hle := Finset.single_le_sum
    (fun ell (_ : ell ∈ Finset.univ) =>
      sub_nonneg.mpr (selectedEffects_le_terminalEffects P h hP.1 S d ell))
    (Finset.mem_univ j)
  simpa only [Finset.sum_sub_distrib, hP.2, abortResidual] using hle

theorem abortResidual_tendsto_zero {m n : ℕ} (P : CountableProtocol m n)
    (h : List ℕ) (hP : GloballyDeterministic P h) :
    Filter.Tendsto (fun N => abortResidual P (Finset.range N) N h)
      Filter.atTop (nhds 0) := by
  have hc : Continuous (fun F : Fin 4 → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ =>
      1 - ∑ j, F j) := by fun_prop
  simpa [abortResidual, hP.2, Function.comp_def] using
    (hc.tendsto (terminalEffects P h)).comp (selectedEffects_tendsto P h hP.1)

section OperatorError

open scoped Matrix.Norms.L2Operator

theorem posSemidef_norm_le_trace {a : Type*} [Fintype a] [DecidableEq a]
    (R : Matrix a a ℂ) (hR : R.PosSemidef) : ‖R‖ ≤ R.trace.re := by
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

theorem truncation_effect_norm_error {m n : ℕ} (P : CountableProtocol m n)
    (bA : Fin m) (bB : Fin n) (abort : Fin 4) (h : List ℕ)
    (hP : GloballyDeterministic P h) (S : Finset ℕ) (d : ℕ) (j : Fin 4) :
    ‖(truncation P bA bB S abort d h).effect j - terminalEffects P h j‖ ≤
      (abortResidual P S d h).trace.re := by
  have hD : 0 ≤ terminalEffects P h j - selectedEffects P S d h j :=
    sub_nonneg.mpr (selectedEffects_le_terminalEffects P h hP.1 S d j)
  have hDR := omittedOutcome_le_abortResidual P h hP S d j
  have hn : ‖(truncation P bA bB S abort d h).effect j - terminalEffects P h j‖ ≤
      ‖abortResidual P S d h‖ := by
    rw [truncation_effect, completeEffects]
    by_cases hj : abort = j
    · simp only [hj, ite_true]
      have heq : selectedEffects P S d h j + (1 - ∑ ell, selectedEffects P S d h ell) -
          terminalEffects P h j = abortResidual P S d h -
            (terminalEffects P h j - selectedEffects P S d h j) := by
        unfold abortResidual
        abel
      rw [heq]
      exact CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_le_self _ hD)
        (sub_nonneg.mpr hDR)
    · simp only [hj, ite_false, add_zero]
      have heq : selectedEffects P S d h j - terminalEffects P h j =
          -(terminalEffects P h j - selectedEffects P S d h j) := by abel
      rw [heq, norm_neg]
      exact CStarAlgebra.norm_le_norm_of_le_of_nonneg hDR hD
  exact hn.trans (posSemidef_norm_le_trace _ (abortResidual_posSemidef P h hP S d))

end OperatorError

def matrixReportedEvaluation {m n : ℕ} (P : CountableProtocol m n)
    (h : List ℕ) (j : Fin 4) (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : ℂ :=
  ∑' w, (terminalEffect P h w j * X).trace

theorem matrixReportedEvaluation_eq_trace {m n : ℕ} (P : CountableProtocol m n)
    (h : List ℕ) (j : Fin 4) (hs : Summable (fun w => terminalEffect P h w j))
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    matrixReportedEvaluation P h j X = (terminalEffects P h j * X).trace := by
  let f : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →+ ℂ :=
    { toFun := fun E => (E * X).trace
      map_zero' := by simp
      map_add' := by intro E G; simp [Matrix.add_mul, Matrix.trace_add] }
  have hf : Continuous f := by change Continuous (fun E => (E * X).trace); fun_prop
  exact (hs.hasSum.map f hf).tsum_eq

theorem matrixBornProbability_nonneg {m n : ℕ} (P : CountableProtocol m n)
    (h : List ℕ) (hP : GloballyDeterministic P h) (j : Fin 4)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hX : X.PosSemidef) :
    0 ≤ (matrixReportedEvaluation P h j X).re := by
  rw [matrixReportedEvaluation_eq_trace P h j (hP.1 j) X]
  exact (Complex.nonneg_iff.mp
    (QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.trace_product_posSemidef_nonneg _ X
      (terminalEffects_posSemidef P h j) hX)).1

theorem matrixBornProbability_sum_one {m n : ℕ} (P : CountableProtocol m n)
    (h : List ℕ) (hP : GloballyDeterministic P h)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hX : X.trace = 1) :
    (∑ j, (matrixReportedEvaluation P h j X).re) = 1 := by
  simp_rw [matrixReportedEvaluation_eq_trace P h _ (hP.1 _) X]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, hP.2,
    Matrix.one_mul, hX]
  rfl

end DiscreteProtocol

end

end QuantumProver.ElegantJointMeasurement.TailReference

namespace QuantumProver.ElegantJointMeasurement.TailReference.DiscreteCPProtocol

open QuantumProver.ElegantJointMeasurement.CP
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
open scoped Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 800000

abbrev Map (input out : ℕ) :=
  Matrix (Fin input) (Fin input) ℂ →ₗ[ℂ] Matrix (Fin out) (Fin out) ℂ

def refinedKraus {σ : Type*} {input out : ℕ} (Φ : σ → Map input out)
    (q : σ × (Fin input × Fin out)) : Matrix (Fin out) (Fin input) ℂ :=
  krausOperator (Φ q.1) q.2

theorem reported_gram_trace {σ : Type*} {input out : ℕ}
    (Φ : σ → Map input out) (hΦ : ∀ s, CompletelyPositive (Φ s)) (s : σ)
    (X : Matrix (Fin input) (Fin input) ℂ) :
    ((∑ q : Fin input × Fin out, (refinedKraus Φ (s, q))ᴴ * refinedKraus Φ (s, q)) * X).trace =
      (Φ s X).trace := by
  rw [← krausMap_trace]
  exact congrArg Matrix.trace
    (congrArg (fun Ψ : Map input out => Ψ X) (completelyPositive_eq_krausMap (Φ s) (hΦ s))).symm

theorem reported_gram_hasSum {σ : Type*} {input out : ℕ}
    (Φ : σ → Map input out) (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin input) (Fin input) ℂ,
      HasSum (fun s => (Φ s X).trace) X.trace) :
    HasSum (fun s => ∑ q : Fin input × Fin out,
      (refinedKraus Φ (s, q))ᴴ * refinedKraus Φ (s, q)) 1 := by
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro j
  have h := htrace (Matrix.single j i 1)
  have heq (s : σ) : (Φ s (Matrix.single j i 1)).trace =
      (∑ q : Fin input × Fin out, (refinedKraus Φ (s, q))ᴴ * refinedKraus Φ (s, q)) i j := by
    rw [← reported_gram_trace Φ hΦ s]
    simp [Matrix.trace_mul_single]
  simp_rw [heq] at h
  by_cases hij : i = j
  · subst j
    simpa [Matrix.trace_single_eq_same, Matrix.one_apply] using h
  · simpa [Matrix.trace_single_eq_of_ne j i (1 : ℂ) (Ne.symm hij), Matrix.one_apply, hij] using h

theorem refined_gram_summable {σ : Type*} {input out : ℕ}
    (Φ : σ → Map input out) (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin input) (Fin input) ℂ,
      HasSum (fun s => (Φ s X).trace) X.trace) :
    Summable (fun q : σ × (Fin input × Fin out) =>
      (refinedKraus Φ q)ᴴ * refinedKraus Φ q) := by
  let G := fun q : σ × (Fin input × Fin out) => (refinedKraus Φ q)ᴴ * refinedKraus Φ q
  let g := fun q : σ × (Fin input × Fin out) => (G q).trace.re
  have hg0 (q : σ × (Fin input × Fin out)) : 0 ≤ g q :=
    (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (refinedKraus Φ q)).trace_nonneg).1
  have heq (s : σ) : (∑ q : Fin input × Fin out, g (s, q)) = (Φ s 1).trace.re := by
    rw [← reported_gram_trace Φ hΦ s]
    simp [g, G, Matrix.trace_sum]
  let reHom : ℂ →+ ℝ :=
    { toFun := Complex.re
      map_zero' := rfl
      map_add' := Complex.add_re }
  have hre : HasSum (fun s => (Φ s 1).trace.re) ((1 : Matrix (Fin input) (Fin input) ℂ).trace.re) :=
    (htrace 1).map reHom Complex.continuous_re
  have hg : Summable g := (summable_prod_of_nonneg hg0).mpr ⟨fun s => (hasSum_fintype _).summable, by
    simpa only [tsum_fintype, heq] using hre.summable⟩
  exact hg.of_norm_bounded (fun q => DiscreteProtocol.posSemidef_norm_le_trace _
    (Matrix.posSemidef_conjTranspose_mul_self (refinedKraus Φ q)))

theorem refined_gram_hasSum {σ : Type*} {input out : ℕ}
    (Φ : σ → Map input out) (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin input) (Fin input) ℂ,
      HasSum (fun s => (Φ s X).trace) X.trace) :
    HasSum (fun q : σ × (Fin input × Fin out) =>
      (refinedKraus Φ q)ᴴ * refinedKraus Φ q) 1 := by
  have hs := refined_gram_summable Φ hΦ htrace
  have heq : (∑' q : σ × (Fin input × Fin out),
      (refinedKraus Φ q)ᴴ * refinedKraus Φ q) = 1 := by
    rw [hs.tsum_prod]
    simp only [tsum_fintype]
    exact (reported_gram_hasSum Φ hΦ htrace).tsum_eq
  simpa only [heq] using hs.hasSum

inductive MatrixNode (m n : ℕ) where
  | terminal (j : Fin 4)
  | alice (Φ : ℕ → Map m m) (positive : ∀ s, CompletelyPositive (Φ s))
      (traceSum : ∀ X : Matrix (Fin m) (Fin m) ℂ,
        HasSum (fun s => (Φ s X).trace) X.trace)
  | bob (Φ : ℕ → Map n n) (positive : ∀ s, CompletelyPositive (Φ s))
      (traceSum : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        HasSum (fun s => (Φ s X).trace) X.trace)

structure MatrixProtocol (m n : ℕ) where
  node : List ℕ → MatrixNode m n

abbrev Hidden (m n : ℕ) := (Fin m × Fin m) ⊕ (Fin n × Fin n)

def aliceKraus {m n : ℕ} (Φ : ℕ → Map m m) : ℕ × Hidden m n → Matrix (Fin m) (Fin m) ℂ
  | (s, .inl q) => krausOperator (Φ s) q
  | (_, .inr _) => 0

def bobKraus {m n : ℕ} (Φ : ℕ → Map n n) : ℕ × Hidden m n → Matrix (Fin n) (Fin n) ℂ
  | (_, .inl _) => 0
  | (s, .inr q) => krausOperator (Φ s) q

theorem aliceKraus_hasSum {m n : ℕ} (Φ : ℕ → Map m m)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, HasSum (fun s => (Φ s X).trace) X.trace) :
    HasSum (fun q : ℕ × Hidden m n => (aliceKraus Φ q)ᴴ * aliceKraus Φ q) 1 := by
  let f : (ℕ × (Fin m × Fin m)) ⊕ (ℕ × (Fin n × Fin n)) → Matrix (Fin m) (Fin m) ℂ :=
    Sum.elim (fun q => (refinedKraus Φ q)ᴴ * refinedKraus Φ q) (fun _ => 0)
  have hf : HasSum f (1 + 0) := HasSum.sum (refined_gram_hasSum Φ hΦ htrace) hasSum_zero
  have h := (Equiv.prodSumDistrib ℕ (Fin m × Fin m) (Fin n × Fin n)).hasSum_iff.mpr hf
  convert h using 1
  · funext q
    rcases q with ⟨s, q | q⟩ <;> simp [aliceKraus, f, refinedKraus]
  · simp

theorem bobKraus_hasSum {m n : ℕ} (Φ : ℕ → Map n n)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin n) (Fin n) ℂ, HasSum (fun s => (Φ s X).trace) X.trace) :
    HasSum (fun q : ℕ × Hidden m n => (bobKraus Φ q)ᴴ * bobKraus Φ q) 1 := by
  let f : (ℕ × (Fin m × Fin m)) ⊕ (ℕ × (Fin n × Fin n)) → Matrix (Fin n) (Fin n) ℂ :=
    Sum.elim (fun _ => 0) (fun q => (refinedKraus Φ q)ᴴ * refinedKraus Φ q)
  have hf : HasSum f (0 + 1) := HasSum.sum hasSum_zero (refined_gram_hasSum Φ hΦ htrace)
  have h := (Equiv.prodSumDistrib ℕ (Fin m × Fin m) (Fin n × Fin n)).hasSum_iff.mpr hf
  convert h using 1
  · funext q
    rcases q with ⟨s, q | q⟩ <;> simp [bobKraus, f, refinedKraus]
  · simp

def functionalMatrix {a : Type*} [Fintype a] [DecidableEq a]
    (f : Matrix a a ℂ →ₗ[ℂ] ℂ) : Matrix a a ℂ := fun i j => f (Matrix.single j i 1)

theorem trace_functionalMatrix_mul {a : Type*} [Fintype a] [DecidableEq a]
    (f : Matrix a a ℂ →ₗ[ℂ] ℂ) (X : Matrix a a ℂ) :
    (functionalMatrix f * X).trace = f X := by
  have hX : (∑ i : a, ∑ j : a, (X i j) • Matrix.single i j (1 : ℂ)) = X := by
    simp_rw [Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.sum_sum_single X
  calc
    _ = ∑ i : a, ∑ j : a, f (Matrix.single j i 1) * X j i := by
      simp [Matrix.trace, Matrix.mul_apply, functionalMatrix]
    _ = ∑ j : a, ∑ i : a, X j i * f (Matrix.single j i 1) := by
      rw [Finset.sum_comm]
      simp only [mul_comm]
    _ = f (∑ j : a, ∑ i : a, X j i • Matrix.single j i (1 : ℂ)) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = f X := by rw [hX]

def traceFunctional {a : Type*} [Fintype a]
    (Φ : Matrix a a ℂ →ₗ[ℂ] Matrix a a ℂ) (F : Matrix a a ℂ) : Matrix a a ℂ →ₗ[ℂ] ℂ where
  toFun X := (F * Φ X).trace
  map_add' X Y := by simp [map_add, Matrix.mul_add, Matrix.trace_add]
  map_smul' z X := by simp [map_smul, Matrix.mul_smul, Matrix.trace_smul]

def dualMap {a : Type*} [Fintype a] [DecidableEq a]
    (Φ : Matrix a a ℂ →ₗ[ℂ] Matrix a a ℂ) : Matrix a a ℂ →ₗ[ℂ] Matrix a a ℂ where
  toFun F := functionalMatrix (traceFunctional Φ F)
  map_add' F G := by ext i j; simp [functionalMatrix, traceFunctional, Matrix.add_mul, Matrix.trace_add]
  map_smul' z F := by ext i j; simp [functionalMatrix, traceFunctional, Matrix.trace_smul]

theorem trace_dualMap_mul {a : Type*} [Fintype a] [DecidableEq a]
    (Φ : Matrix a a ℂ →ₗ[ℂ] Matrix a a ℂ) (F X : Matrix a a ℂ) :
    (dualMap Φ F * X).trace = (F * Φ X).trace :=
  trace_functionalMatrix_mul (traceFunctional Φ F) X

@[simp] theorem dualMap_zero {a : Type*} [Fintype a] [DecidableEq a] (F : Matrix a a ℂ) :
    dualMap (0 : Matrix a a ℂ →ₗ[ℂ] Matrix a a ℂ) F = 0 := by
  ext i j
  simp [dualMap, functionalMatrix, traceFunctional]

theorem dualMap_kraus {a ι : Type*} [Fintype a] [DecidableEq a] [Fintype ι]
    (K : ι → Matrix a a ℂ) (F : Matrix a a ℂ) :
    dualMap (krausMap K) F = ∑ q, (K q)ᴴ * F * K q := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [trace_dualMap_mul]
  change (F * (∑ q, K q * X * (K q)ᴴ)).trace = _
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_cycle F (K q * X) (K q)ᴴ)

def aliceLift {m n : ℕ} (Φ : ℕ → Map m m) (s : ℕ) (q : Hidden m n) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  aliceKraus Φ (s, q) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)

def bobLift {m n : ℕ} (Φ : ℕ → Map n n) (s : ℕ) (q : Hidden m n) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ bobKraus Φ (s, q)

theorem leftApplication_eq_commonKraus {m n : ℕ} (Φ : ℕ → Map m m)
    (positive : ∀ s, CompletelyPositive (Φ s)) (s : ℕ) :
    leftApplication (n := n) (Φ s) = krausMap (aliceLift Φ s) := by
  ext X
  rw [leftApplication_eq_kraus (Φ s) (positive s)]
  simp [krausMap, aliceLift, aliceKraus, Fintype.sum_sum_type, leftKrausApplication]

theorem rightApplication_eq_commonKraus {m n : ℕ} (Φ : ℕ → Map n n)
    (positive : ∀ s, CompletelyPositive (Φ s)) (s : ℕ) :
    rightApplication (m := m) (Φ s) = krausMap (bobLift Φ s) := by
  ext X
  rw [rightApplication_eq_kraus (Φ s) (positive s)]
  simp [krausMap, bobLift, bobKraus, Fintype.sum_sum_type, rightKrausApplication]

def terminalLabel {m n : ℕ} (P : MatrixProtocol m n) (h : List ℕ) : Option (Fin 4) :=
  match P.node h with
  | .terminal j => some j
  | .alice _ _ _ => none
  | .bob _ _ _ => none

def branchApplication {m n : ℕ} (P : MatrixProtocol m n) (h : List ℕ) (s : ℕ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  match P.node h with
  | .terminal _ => 0
  | .alice Φ _ _ => leftApplication (Φ s)
  | .bob Φ _ _ => rightApplication (Φ s)

def pathApplication {m n : ℕ} (P : MatrixProtocol m n) : List ℕ → List ℕ →
    (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
  | _, [] => LinearMap.id
  | h, s :: w => (pathApplication P (h ++ [s]) w).comp (branchApplication P h s)

def terminalEffect {m n : ℕ} (P : MatrixProtocol m n) : List ℕ → List ℕ → Fin 4 →
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ
  | h, [], j => if terminalLabel P h = some j then 1 else 0
  | h, s :: w, j => dualMap (branchApplication P h s) (terminalEffect P (h ++ [s]) w j)

theorem terminalEffect_trace {m n : ℕ} (P : MatrixProtocol m n)
    (h w : List ℕ) (j : Fin 4) (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (terminalEffect P h w j * X).trace =
      if terminalLabel P (h ++ w) = some j then (pathApplication P h w X).trace else 0 := by
  induction w generalizing h X with
  | nil => split_ifs <;> simp_all [terminalEffect, pathApplication]
  | cons s w ih =>
    rw [terminalEffect, trace_dualMap_mul, ih]
    simp [pathApplication, List.append_assoc]

def terminalEffects {m n : ℕ} (P : MatrixProtocol m n) (h : List ℕ) (j : Fin 4) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ := ∑' w, terminalEffect P h w j

def GloballyDeterministic {m n : ℕ} (P : MatrixProtocol m n) (h : List ℕ) : Prop :=
  (∀ j, Summable (fun w => terminalEffect P h w j)) ∧ ∑ j, terminalEffects P h j = 1

def selectedEffects {m n : ℕ} (P : MatrixProtocol m n) (S : Finset ℕ)
    (d : ℕ) (h : List ℕ) (j : Fin 4) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  ∑ w ∈ DiscreteProtocol.boundedWords S d, terminalEffect P h w j

theorem selectedEffects_succ {m n : ℕ} (P : MatrixProtocol m n) (S : Finset ℕ)
    (d : ℕ) (h : List ℕ) (j : Fin 4) :
    selectedEffects P S (d + 1) h j = terminalEffect P h [] j +
      ∑ s ∈ S, dualMap (branchApplication P h s) (selectedEffects P S d (h ++ [s]) j) := by
  rw [selectedEffects, DiscreteProtocol.boundedWords_sum]
  simp only [terminalEffect, selectedEffects, map_sum]

theorem selectedEffects_tendsto {m n : ℕ} (P : MatrixProtocol m n)
    (h : List ℕ) (hs : ∀ j, Summable (fun w => terminalEffect P h w j)) :
    Filter.Tendsto (fun N j => selectedEffects P (Finset.range N) N h j)
      Filter.atTop (nhds (terminalEffects P h)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  exact (hs j).hasSum.comp DiscreteProtocol.boundedWords_exhaust

def matrixReportedEvaluation {m n : ℕ} (P : MatrixProtocol m n)
    (h : List ℕ) (j : Fin 4) (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : ℂ :=
  ∑' w, if terminalLabel P (h ++ w) = some j then (pathApplication P h w X).trace else 0

theorem matrixReportedEvaluation_eq_trace {m n : ℕ} (P : MatrixProtocol m n)
    (h : List ℕ) (j : Fin 4) (hs : Summable (fun w => terminalEffect P h w j))
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    matrixReportedEvaluation P h j X = (terminalEffects P h j * X).trace := by
  unfold matrixReportedEvaluation
  simp_rw [← terminalEffect_trace]
  let f : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →+ ℂ :=
    { toFun := fun E => (E * X).trace
      map_zero' := by simp
      map_add' := by intro E G; simp [Matrix.add_mul, Matrix.trace_add] }
  have hf : Continuous f := by change Continuous (fun E => (E * X).trace); fun_prop
  exact (hs.hasSum.map f hf).tsum_eq

theorem matrixBornProbability_sum_one {m n : ℕ} (P : MatrixProtocol m n)
    (h : List ℕ) (hP : GloballyDeterministic P h)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hX : X.trace = 1) :
    (∑ j, (matrixReportedEvaluation P h j X).re) = 1 := by
  simp_rw [matrixReportedEvaluation_eq_trace P h _ (hP.1 _) X]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, hP.2,
    Matrix.one_mul, hX]
  rfl

section PositiveDimensions

variable {m n : ℕ} [NeZero m] [NeZero n]

def indexEquiv (m n : ℕ) [NeZero m] [NeZero n] : ℕ ≃ ℕ × Hidden m n := by
  have : NeZero (Fintype.card (Hidden m n)) := ⟨Fintype.card_ne_zero⟩
  exact (Nat.divModEquiv (Fintype.card (Hidden m n))).trans
    (Equiv.prodCongr (Equiv.refl ℕ) (Fintype.equivFin (Hidden m n)).symm)

def physicalReport (m n : ℕ) [NeZero m] [NeZero n] (q : ℕ) : ℕ := (indexEquiv m n q).1

def natAliceKraus (Φ : ℕ → Map m m) (q : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  aliceKraus (n := n) Φ (indexEquiv m n q)

def natBobKraus (Φ : ℕ → Map n n) (q : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  bobKraus (m := m) Φ (indexEquiv m n q)

theorem natAliceKraus_hasSum (Φ : ℕ → Map m m) (positive : ∀ s, CompletelyPositive (Φ s))
    (traceSum : ∀ X : Matrix (Fin m) (Fin m) ℂ, HasSum (fun s => (Φ s X).trace) X.trace) :
    HasSum (fun q => (natAliceKraus (n := n) Φ q)ᴴ * natAliceKraus (n := n) Φ q) 1 := by
  have h := (indexEquiv m n).hasSum_iff
    (f := fun q : ℕ × Hidden m n => (aliceKraus Φ q)ᴴ * aliceKraus Φ q)
    (a := (1 : Matrix (Fin m) (Fin m) ℂ))
  simpa only [natAliceKraus, Function.comp_def] using
    h.mpr (aliceKraus_hasSum (n := n) Φ positive traceSum)

theorem natBobKraus_hasSum (Φ : ℕ → Map n n) (positive : ∀ s, CompletelyPositive (Φ s))
    (traceSum : ∀ X : Matrix (Fin n) (Fin n) ℂ, HasSum (fun s => (Φ s X).trace) X.trace) :
    HasSum (fun q => (natBobKraus (m := m) Φ q)ᴴ * natBobKraus (m := m) Φ q) 1 := by
  have h := (indexEquiv m n).hasSum_iff
    (f := fun q : ℕ × Hidden m n => (bobKraus Φ q)ᴴ * bobKraus Φ q)
    (a := (1 : Matrix (Fin n) (Fin n) ℂ))
  simpa only [natBobKraus, Function.comp_def] using
    h.mpr (bobKraus_hasSum (m := m) Φ positive traceSum)

def refinement (P : MatrixProtocol m n) : DiscreteProtocol.CountableProtocol m n where
  node h := match P.node (h.map (physicalReport m n)) with
    | .terminal j => .terminal j
    | .alice Φ positive traceSum =>
      .alice (natAliceKraus (n := n) Φ)
        (natAliceKraus_hasSum (n := n) Φ positive traceSum).summable
        (natAliceKraus_hasSum (n := n) Φ positive traceSum).tsum_eq
    | .bob Φ positive traceSum =>
      .bob (natBobKraus (m := m) Φ)
        (natBobKraus_hasSum (m := m) Φ positive traceSum).summable
        (natBobKraus_hasSum (m := m) Φ positive traceSum).tsum_eq

def refinedCutoff (S : Finset ℕ) : Finset ℕ :=
  (S.product (Finset.univ : Finset (Hidden m n))).image (indexEquiv m n).symm

theorem mem_refinedCutoff (S : Finset ℕ) (q : ℕ) :
    q ∈ refinedCutoff (m := m) (n := n) S ↔ physicalReport m n q ∈ S := by
  constructor
  · intro hq
    obtain ⟨⟨s, k⟩, hp, heq⟩ := Finset.mem_image.mp hq
    have hs := (Finset.mem_product.mp hp).1
    simpa [← heq, physicalReport] using hs
  · intro hq
    exact Finset.mem_image.mpr ⟨indexEquiv m n q,
      Finset.mem_product.mpr ⟨hq, Finset.mem_univ _⟩, (indexEquiv m n).symm_apply_apply q⟩

theorem sum_refinedCutoff {M : Type*} [AddCommMonoid M]
    (S : Finset ℕ) (f : ℕ → M) :
    (∑ q ∈ refinedCutoff (m := m) (n := n) S, f q) =
      ∑ s ∈ S, ∑ k : Hidden m n, f ((indexEquiv m n).symm (s, k)) := by
  rw [refinedCutoff, Finset.sum_image (by intro a ha b hb h; exact (indexEquiv m n).symm.injective h)]
  exact Finset.sum_product S Finset.univ (fun p => f ((indexEquiv m n).symm p))

theorem selectedEffects_refinement (P : MatrixProtocol m n) (S : Finset ℕ)
    (d : ℕ) (h : List ℕ) (j : Fin 4) :
    DiscreteProtocol.selectedEffects (refinement P) (refinedCutoff (m := m) (n := n) S) d h j =
      selectedEffects P S d (h.map (physicalReport m n)) j := by
  induction d generalizing h with
  | zero =>
    simp only [DiscreteProtocol.selectedEffects, selectedEffects,
      DiscreteProtocol.boundedWords, Finset.sum_singleton, terminalEffect]
    cases hn : P.node (h.map (physicalReport m n)) <;>
      simp [refinement, DiscreteProtocol.terminalLabel, terminalLabel, hn]
  | succ d ih =>
    rw [selectedEffects_succ]
    cases hn : P.node (h.map (physicalReport m n)) with
    | terminal ell =>
      simp [DiscreteProtocol.selectedEffects, refinement, hn, terminalEffect,
        terminalLabel, branchApplication]
    | alice Φ positive traceSum =>
      have hnode : (refinement P).node h =
          DiscreteProtocol.CountableNode.alice (natAliceKraus (n := n) Φ)
            (natAliceKraus_hasSum (n := n) Φ positive traceSum).summable
            (natAliceKraus_hasSum (n := n) Φ positive traceSum).tsum_eq := by
        simp only [refinement, hn]
      simp only [DiscreteProtocol.selectedEffects, hnode, hn,
        terminalEffect, terminalLabel, branchApplication, reduceCtorEq, ite_false, zero_add]
      simp only [ih, List.map_append, List.map_singleton]
      rw [sum_refinedCutoff (m := m) (n := n)]
      simp only [natAliceKraus, physicalReport, Equiv.apply_symm_apply]
      apply Finset.sum_congr rfl
      intro s hs
      rw [leftApplication_eq_commonKraus Φ positive s, dualMap_kraus]
      rfl
    | bob Φ positive traceSum =>
      have hnode : (refinement P).node h =
          DiscreteProtocol.CountableNode.bob (natBobKraus (m := m) Φ)
            (natBobKraus_hasSum (m := m) Φ positive traceSum).summable
            (natBobKraus_hasSum (m := m) Φ positive traceSum).tsum_eq := by
        simp only [refinement, hn]
      simp only [DiscreteProtocol.selectedEffects, hnode, hn,
        terminalEffect, terminalLabel, branchApplication, reduceCtorEq, ite_false, zero_add]
      simp only [ih, List.map_append, List.map_singleton]
      rw [sum_refinedCutoff (m := m) (n := n)]
      simp only [natBobKraus, physicalReport, Equiv.apply_symm_apply]
      apply Finset.sum_congr rfl
      intro s hs
      rw [rightApplication_eq_commonKraus Φ positive s, dualMap_kraus]
      rfl

def fineWords (N : ℕ) : Finset (List ℕ) :=
  DiscreteProtocol.boundedWords (refinedCutoff (m := m) (n := n) (Finset.range N)) N

theorem fineWords_monotone : Monotone (fineWords (m := m) (n := n)) := by
  intro N M hNM w hw
  rw [fineWords, DiscreteProtocol.mem_boundedWords] at hw ⊢
  refine ⟨hw.1.trans hNM, ?_⟩
  intro q hq
  have h_old := hw.2 q hq
  rw [mem_refinedCutoff, Finset.mem_range] at h_old ⊢
  exact h_old.trans_le hNM

theorem fineWords_exhaust : Filter.Tendsto (fineWords (m := m) (n := n))
    Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_finset_of_monotone fineWords_monotone
  intro w
  let N := w.length + (w.map (physicalReport m n)).toFinset.sup id + 1
  refine ⟨N, ?_⟩
  rw [fineWords, DiscreteProtocol.mem_boundedWords]
  refine ⟨by dsimp [N]; omega, ?_⟩
  intro q hq
  rw [mem_refinedCutoff, Finset.mem_range]
  have hle : physicalReport m n q ≤ (w.map (physicalReport m n)).toFinset.sup id :=
    Finset.le_sup (f := id) (by simp only [List.mem_toFinset]; exact List.mem_map.mpr ⟨q, hq, rfl⟩)
  dsimp [N]
  omega

theorem fine_terminal_sum_tendsto (P : MatrixProtocol m n) (h : List ℕ)
    (hs : ∀ j, Summable (fun w => terminalEffect P (h.map (physicalReport m n)) w j)) (j : Fin 4) :
    Filter.Tendsto (fun N => ∑ w ∈ fineWords (m := m) (n := n) N,
      DiscreteProtocol.terminalEffect (refinement P) h w j) Filter.atTop
      (nhds (terminalEffects P (h.map (physicalReport m n)) j)) := by
  simp_rw [fineWords, ← DiscreteProtocol.selectedEffects_eq_terminal_sum,
    selectedEffects_refinement]
  exact tendsto_pi_nhds.mp (selectedEffects_tendsto P _ hs) j

theorem positive_cofinal_hasSum {σ a : Type*} [Fintype a] [DecidableEq a]
    (f : σ → Matrix a a ℂ) (hf : ∀ s, (f s).PosSemidef)
    (W : ℕ → Finset σ) (hW : Filter.Tendsto W Filter.atTop Filter.atTop)
    (F : Matrix a a ℂ)
    (hlim : Filter.Tendsto (fun N => ∑ s ∈ W N, f s) Filter.atTop (nhds F)) :
    HasSum f F := by
  classical
  let g := fun s => (f s).trace.re
  have hg0 (s : σ) : 0 ≤ g s := (Complex.nonneg_iff.mp (hf s).trace_nonneg).1
  have hc : Continuous (fun R : Matrix a a ℂ => R.trace.re) := by fun_prop
  have hglim : Filter.Tendsto (fun N => ∑ s ∈ W N, g s) Filter.atTop (nhds F.trace.re) := by
    simpa only [Function.comp_def, Matrix.trace_sum, Complex.re_sum] using (hc.tendsto F).comp hlim
  have hbound (S : Finset σ) : (∑ s ∈ S, g s) ≤ F.trace.re := by
    apply ge_of_tendsto hglim
    filter_upwards [hW.eventually (Filter.eventually_ge_atTop S)] with N hN
    exact Finset.sum_le_sum_of_subset_of_nonneg hN (fun s hs hnot => hg0 s)
  have hg : Summable g := summable_of_sum_le hg0 hbound
  have hsf : Summable f := hg.of_norm_bounded
    (fun s => DiscreteProtocol.posSemidef_norm_le_trace (f s) (hf s))
  have heq : (∑' s, f s) = F := tendsto_nhds_unique (hsf.hasSum.comp hW) hlim
  simpa only [heq] using hsf.hasSum

theorem refined_terminal_hasSum (P : MatrixProtocol m n) (h : List ℕ)
    (hs : ∀ j, Summable (fun w => terminalEffect P (h.map (physicalReport m n)) w j)) (j : Fin 4) :
    HasSum (fun w => DiscreteProtocol.terminalEffect (refinement P) h w j)
      (terminalEffects P (h.map (physicalReport m n)) j) :=
  positive_cofinal_hasSum _ (fun w => DiscreteProtocol.terminalEffect_posSemidef (refinement P) h w j)
    fineWords fineWords_exhaust _ (fine_terminal_sum_tendsto P h hs j)

theorem terminalEffects_refinement (P : MatrixProtocol m n) (h : List ℕ)
    (hs : ∀ j, Summable (fun w => terminalEffect P (h.map (physicalReport m n)) w j)) (j : Fin 4) :
    DiscreteProtocol.terminalEffects (refinement P) h j =
      terminalEffects P (h.map (physicalReport m n)) j := (refined_terminal_hasSum P h hs j).tsum_eq

theorem refinement_globallyDeterministic (P : MatrixProtocol m n) (h : List ℕ)
    (hP : GloballyDeterministic P (h.map (physicalReport m n))) :
    DiscreteProtocol.GloballyDeterministic (refinement P) h := by
  refine ⟨fun j => (refined_terminal_hasSum P h hP.1 j).summable, ?_⟩
  simp_rw [terminalEffects_refinement P h hP.1]
  exact hP.2

theorem matrixReportedEvaluation_eq_refinement (P : MatrixProtocol m n) (h : List ℕ)
    (hs : ∀ j, Summable (fun w => terminalEffect P (h.map (physicalReport m n)) w j))
    (j : Fin 4) (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    matrixReportedEvaluation P (h.map (physicalReport m n)) j X =
      DiscreteProtocol.matrixReportedEvaluation (refinement P) h j X := by
  rw [matrixReportedEvaluation_eq_trace P _ j (hs j) X,
    DiscreteProtocol.matrixReportedEvaluation_eq_trace (refinement P) h j
      (refined_terminal_hasSum P h hs j).summable X,
    terminalEffects_refinement P h hs j]

theorem matrixBornProbability_nonneg (P : MatrixProtocol m n) (h : List ℕ)
    (hP : GloballyDeterministic P (h.map (physicalReport m n))) (j : Fin 4)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hX : X.PosSemidef) :
    0 ≤ (matrixReportedEvaluation P (h.map (physicalReport m n)) j X).re := by
  rw [matrixReportedEvaluation_eq_refinement P h hP.1 j X]
  exact DiscreteProtocol.matrixBornProbability_nonneg (refinement P) h
    (refinement_globallyDeterministic P h hP) j X hX

theorem truncation_matrix_effect_tendsto (P : MatrixProtocol m n)
    (bA : Fin m) (bB : Fin n) (abort : Fin 4) (h : List ℕ)
    (hP : GloballyDeterministic P (h.map (physicalReport m n))) :
    Filter.Tendsto (fun N j =>
      (DiscreteProtocol.truncation (refinement P) bA bB (Finset.range N) abort N h).effect j)
      Filter.atTop (nhds (terminalEffects P (h.map (physicalReport m n)))) := by
  have hR := DiscreteProtocol.truncation_effect_tendsto (refinement P) bA bB abort h
    (refinement_globallyDeterministic P h hP)
  have heq : DiscreteProtocol.terminalEffects (refinement P) h =
      terminalEffects P (h.map (physicalReport m n)) :=
    funext (terminalEffects_refinement P h hP.1)
  rw [heq] at hR
  exact hR

theorem matrixProtocol_mem_finiteTreeEffectSet_closure {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixProtocol m n) (bA : Fin m) (bB : Fin n) (abort : Fin 4)
    (hP : GloballyDeterministic P []) :
    (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffects P [] j)) ∈
      closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb) := by
  have hR : DiscreteProtocol.GloballyDeterministic (refinement P) [] :=
    refinement_globallyDeterministic P [] hP
  have h := DiscreteProtocol.countableProtocol_mem_finiteTreeEffectSet_closure
    ea eb (refinement P) bA bB abort [] hR
  simpa only [terminalEffects_refinement P [] hP.1, List.map_nil] using h

end PositiveDimensions

end

end QuantumProver.ElegantJointMeasurement.TailReference.DiscreteCPProtocol

namespace QuantumProver.ElegantJointMeasurement.TailReference.VaryingProtocol

open QuantumProver.ElegantJointMeasurement.CP
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 1000000

abbrev Joint (m n : ℕ) := Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ

inductive MatrixNode (S : ℕ → ℕ → Type*) (m n : ℕ) where
  | terminal (j : Fin 4)
  | alice (dims : ℕ → ℕ)
      (Φ : ∀ s, DiscreteCPProtocol.Map m (dims s))
      (positive : ∀ s, CompletelyPositive (Φ s))
      (traceSum : ∀ X, HasSum (fun s => (Φ s X).trace) X.trace)
      (next : ∀ s, S (dims s) n)
  | bob (dims : ℕ → ℕ)
      (Φ : ∀ s, DiscreteCPProtocol.Map n (dims s))
      (positive : ∀ s, CompletelyPositive (Φ s))
      (traceSum : ∀ X, HasSum (fun s => (Φ s X).trace) X.trace)
      (next : ∀ s, S m (dims s))

structure MatrixMachine (S : ℕ → ℕ → Type*) where
  node : ∀ {m n}, S m n → MatrixNode S m n

def rectangularTraceFunctional {i o : Type*} [Fintype i] [Fintype o]
    (Φ : Matrix i i ℂ →ₗ[ℂ] Matrix o o ℂ) (F : Matrix o o ℂ) :
    Matrix i i ℂ →ₗ[ℂ] ℂ where
  toFun X := (F * Φ X).trace
  map_add' X Y := by simp [map_add, Matrix.mul_add, Matrix.trace_add]
  map_smul' z X := by simp [map_smul, Matrix.mul_smul, Matrix.trace_smul]

def rectangularDual {i o : Type*} [Fintype i] [DecidableEq i] [Fintype o]
    (Φ : Matrix i i ℂ →ₗ[ℂ] Matrix o o ℂ) : Matrix o o ℂ →ₗ[ℂ] Matrix i i ℂ where
  toFun F := DiscreteCPProtocol.functionalMatrix (rectangularTraceFunctional Φ F)
  map_add' F G := by
    ext i j
    simp [DiscreteCPProtocol.functionalMatrix, rectangularTraceFunctional, Matrix.add_mul, Matrix.trace_add]
  map_smul' z F := by
    ext i j
    simp [DiscreteCPProtocol.functionalMatrix, rectangularTraceFunctional, Matrix.trace_smul]

theorem trace_rectangularDual_mul {i o : Type*} [Fintype i] [DecidableEq i] [Fintype o]
    (Φ : Matrix i i ℂ →ₗ[ℂ] Matrix o o ℂ) (F : Matrix o o ℂ) (X : Matrix i i ℂ) :
    (rectangularDual Φ F * X).trace = (F * Φ X).trace :=
  DiscreteCPProtocol.trace_functionalMatrix_mul (rectangularTraceFunctional Φ F) X

def terminalEffect {S : ℕ → ℕ → Type*} (P : MatrixMachine S) :
    ∀ {m n}, S m n → List ℕ → Fin 4 → Joint m n
  | _, _, z, [], j => match P.node z with
      | .terminal ell => if ell = j then 1 else 0
      | .alice _ _ _ _ _ => 0
      | .bob _ _ _ _ _ => 0
  | _, _, z, s :: w, j => match P.node z with
      | .terminal _ => 0
      | .alice _ Φ _ _ next => rectangularDual (leftApplication (Φ s)) (terminalEffect P (next s) w j)
      | .bob _ Φ _ _ next => rectangularDual (rightApplication (Φ s)) (terminalEffect P (next s) w j)

def pathEvaluation {S : ℕ → ℕ → Type*} (P : MatrixMachine S) :
    ∀ {m n}, S m n → List ℕ → Fin 4 → Joint m n → ℂ
  | _, _, z, [], j, X => match P.node z with
      | .terminal ell => if ell = j then X.trace else 0
      | .alice _ _ _ _ _ => 0
      | .bob _ _ _ _ _ => 0
  | _, _, z, s :: w, j, X => match P.node z with
      | .terminal _ => 0
      | .alice _ Φ _ _ next => pathEvaluation P (next s) w j (leftApplication (Φ s) X)
      | .bob _ Φ _ _ next => pathEvaluation P (next s) w j (rightApplication (Φ s) X)

theorem terminalEffect_trace {S : ℕ → ℕ → Type*} (P : MatrixMachine S)
    {m n : ℕ} (z : S m n) (w : List ℕ) (j : Fin 4) (X : Joint m n) :
    (terminalEffect P z w j * X).trace = pathEvaluation P z w j X := by
  induction w generalizing m n with
  | nil =>
    cases hn : P.node z with
    | terminal ell => by_cases hj : ell = j <;> simp [terminalEffect, pathEvaluation, hn, hj]
    | alice => simp [terminalEffect, pathEvaluation, hn]
    | bob => simp [terminalEffect, pathEvaluation, hn]
  | cons s w ih =>
    cases hn : P.node z <;> simp only [terminalEffect, pathEvaluation, hn, Matrix.zero_mul, Matrix.trace_zero]
    · rw [trace_rectangularDual_mul, ih]
    · rw [trace_rectangularDual_mul, ih]

def terminalEffects {S : ℕ → ℕ → Type*} (P : MatrixMachine S)
    {m n : ℕ} (z : S m n) (j : Fin 4) : Joint m n := ∑' w, terminalEffect P z w j

def GloballyDeterministic {S : ℕ → ℕ → Type*} (P : MatrixMachine S)
    {m n : ℕ} (z : S m n) : Prop :=
  (∀ j, Summable (fun w => terminalEffect P z w j)) ∧ ∑ j, terminalEffects P z j = 1

def hiddenCode (counts : ℕ → ℕ) (q : Σ s, Fin (counts s)) : ℕ := Nat.pair q.1 q.2.val

theorem hiddenCode_injective (counts : ℕ → ℕ) : Function.Injective (hiddenCode counts) := by
  intro x y hxy
  rcases x with ⟨s, q⟩
  rcases y with ⟨t, r⟩
  change Nat.pair s q.val = Nat.pair t r.val at hxy
  obtain ⟨hst, hqr⟩ := Nat.pair_eq_pair.mp hxy
  subst t
  congr
  exact Fin.ext hqr

def paddedNat {M : Type*} [Zero M] (counts : ℕ → ℕ)
    (f : (Σ s, Fin (counts s)) → M) (q : ℕ) : M :=
  if h : (Nat.unpair q).2 < counts (Nat.unpair q).1 then
    f ⟨(Nat.unpair q).1, ⟨(Nat.unpair q).2, h⟩⟩ else 0

@[simp] theorem paddedNat_hiddenCode {M : Type*} [Zero M] (counts : ℕ → ℕ)
    (f : (Σ s, Fin (counts s)) → M) (q : Σ s, Fin (counts s)) :
    paddedNat counts f (hiddenCode counts q) = f q := by
  rcases q with ⟨s, q⟩
  change paddedNat counts f (Nat.pair s q.val) = f ⟨s, q⟩
  unfold paddedNat
  rw [Nat.unpair_pair]
  simp only [dite_eq_left q.isLt]

theorem paddedNat_zero_outside {M : Type*} [Zero M] (counts : ℕ → ℕ)
    (f : (Σ s, Fin (counts s)) → M) (q : ℕ) (hq : q ∉ Set.range (hiddenCode counts)) :
    paddedNat counts f q = 0 := by
  unfold paddedNat
  split_ifs with h
  · exact False.elim (hq ⟨⟨(Nat.unpair q).1, ⟨(Nat.unpair q).2, h⟩⟩, Nat.pair_unpair q⟩)
  · rfl

theorem paddedNat_hasSum {M : Type*} [TopologicalSpace M] [AddCommMonoid M]
    (counts : ℕ → ℕ) (f : (Σ s, Fin (counts s)) → M) (x : M) (hs : HasSum f x) :
    HasSum (paddedNat counts f) x := by
  apply (hiddenCode_injective counts).hasSum_iff
    (f := paddedNat counts f) (a := x) (paddedNat_zero_outside counts f) |>.mp
  simpa only [Function.comp_def, paddedNat_hiddenCode] using hs

theorem paddedNat_gram_hasSum {a : Type*} [Fintype a] [DecidableEq a]
    (counts : ℕ → ℕ) (K : (Σ s, Fin (counts s)) → Matrix a a ℂ)
    (hs : HasSum (fun q => (K q)ᴴ * K q) 1) :
    HasSum (fun q => (paddedNat counts K q)ᴴ * paddedNat counts K q) 1 := by
  have h := paddedNat_hasSum counts (fun q => (K q)ᴴ * K q) 1 hs
  convert h using 1
  funext q
  unfold paddedNat
  split_ifs <;> simp

structure Frame (S : ℕ → ℕ → Type*) (a b : ℕ) where
  m : ℕ
  n : ℕ
  state : S m n
  RA : LocalRecovery a m
  RB : LocalRecovery b n
  coarse : List ℕ

def initialFrame {S : ℕ → ℕ → Type*} {a b : ℕ} (z : S a b) : Frame S a b :=
  ⟨a, b, z, LocalRecovery.identity a, LocalRecovery.identity b, []⟩

def frameNode {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S)
    (abort : Fin 4) (F : Option (Frame S a b)) : DiscreteProtocol.CountableNode a b :=
  match F with
  | none => .terminal abort
  | some f => match P.node f.state with
    | .terminal j => .terminal j
    | .alice dims Φ positive traceSum _ =>
      let K := paddedNat (fun s => a * dims s)
        (HeterogeneousCPInstrument.positiveKraus dims (HeterogeneousCPInstrument.absorbed f.RA dims Φ))
      let hc := paddedNat_gram_hasSum (fun s => a * dims s) _
        (HeterogeneousCPInstrument.absorbed_positive_gram_hasSum f.RA dims Φ positive traceSum)
      .alice K hc.summable hc.tsum_eq
    | .bob dims Φ positive traceSum _ =>
      let K := paddedNat (fun s => b * dims s)
        (HeterogeneousCPInstrument.positiveKraus dims (HeterogeneousCPInstrument.absorbed f.RB dims Φ))
      let hc := paddedNat_gram_hasSum (fun s => b * dims s) _
        (HeterogeneousCPInstrument.absorbed_positive_gram_hasSum f.RB dims Φ positive traceSum)
      .bob K hc.summable hc.tsum_eq

def nextFrame {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S)
    (F : Option (Frame S a b)) (q : ℕ) : Option (Frame S a b) :=
  match Nat.unpair q with
  | (s, t) =>
  match F with
  | none => none
  | some f => match P.node f.state with
    | .terminal _ => none
    | .alice dims Φ _ _ next =>
      if h : t < a * dims s then
        some ⟨dims s, f.n, next s,
          HeterogeneousCPInstrument.recovery dims (HeterogeneousCPInstrument.absorbed f.RA dims Φ)
            ⟨s, ⟨t, h⟩⟩,
          f.RB, f.coarse ++ [s]⟩
      else none
    | .bob dims Φ _ _ next =>
      if h : t < b * dims s then
        some ⟨f.m, dims s, next s, f.RA,
          HeterogeneousCPInstrument.recovery dims (HeterogeneousCPInstrument.absorbed f.RB dims Φ)
            ⟨s, ⟨t, h⟩⟩,
          f.coarse ++ [s]⟩
      else none

def frameAfter {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S)
    (F : Option (Frame S a b)) (u : List ℕ) : Option (Frame S a b) :=
  u.foldl (nextFrame P) F

theorem frameAfter_append {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S)
    (F : Option (Frame S a b)) (u v : List ℕ) :
    frameAfter P F (u ++ v) = frameAfter P (frameAfter P F u) v := List.foldl_append

@[simp] theorem frameAfter_singleton {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S)
    (F : Option (Frame S a b)) (q : ℕ) : frameAfter P F [q] = nextFrame P F q := rfl

def refinementFrom {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S)
    (abort : Fin 4) (F : Option (Frame S a b)) : DiscreteProtocol.CountableProtocol a b where
  node u := frameNode P abort (frameAfter P F u)

def refinement {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S)
    (z : S a b) (abort : Fin 4) : DiscreteProtocol.CountableProtocol a b :=
  refinementFrom P abort (some (initialFrame z))

def aliceChild {S : ℕ → ℕ → Type*} {a b : ℕ} (f : Frame S a b)
    (dims : ℕ → ℕ) (Φ : ∀ s, DiscreteCPProtocol.Map f.m (dims s))
    (next : ∀ s, S (dims s) f.n) (s : ℕ) (q : Fin (a * dims s)) : Frame S a b :=
  ⟨dims s, f.n, next s,
    HeterogeneousCPInstrument.recovery dims (HeterogeneousCPInstrument.absorbed f.RA dims Φ) ⟨s, q⟩,
    f.RB, f.coarse ++ [s]⟩

def bobChild {S : ℕ → ℕ → Type*} {a b : ℕ} (f : Frame S a b)
    (dims : ℕ → ℕ) (Φ : ∀ s, DiscreteCPProtocol.Map f.n (dims s))
    (next : ∀ s, S f.m (dims s)) (s : ℕ) (q : Fin (b * dims s)) : Frame S a b :=
  ⟨f.m, dims s, next s, f.RA,
    HeterogeneousCPInstrument.recovery dims (HeterogeneousCPInstrument.absorbed f.RB dims Φ) ⟨s, q⟩,
    f.coarse ++ [s]⟩

def aliceStep {S : ℕ → ℕ → Type*} {a b : ℕ} (f : Frame S a b)
    (dims : ℕ → ℕ) (Φ : ∀ s, DiscreteCPProtocol.Map f.m (dims s))
    (s : ℕ) (q : Fin (a * dims s)) : Joint a b :=
  HeterogeneousCPInstrument.positiveKraus dims (HeterogeneousCPInstrument.absorbed f.RA dims Φ) ⟨s, q⟩ ⊗ₖ 1

def bobStep {S : ℕ → ℕ → Type*} {a b : ℕ} (f : Frame S a b)
    (dims : ℕ → ℕ) (Φ : ∀ s, DiscreteCPProtocol.Map f.n (dims s))
    (s : ℕ) (q : Fin (b * dims s)) : Joint a b :=
  1 ⊗ₖ HeterogeneousCPInstrument.positiveKraus dims (HeterogeneousCPInstrument.absorbed f.RB dims Φ) ⟨s, q⟩

theorem nextFrame_alice {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S) (f : Frame S a b)
    (dims : ℕ → ℕ) (Φ : ∀ s, DiscreteCPProtocol.Map f.m (dims s))
    (positive : ∀ s, CompletelyPositive (Φ s))
    (traceSum : ∀ X, HasSum (fun s => (Φ s X).trace) X.trace)
    (next : ∀ s, S (dims s) f.n) (hn : P.node f.state = .alice dims Φ positive traceSum next)
    (s : ℕ) (q : Fin (a * dims s)) :
    nextFrame P (some f) (Nat.pair s q.val) = some (aliceChild f dims Φ next s q) := by
  unfold nextFrame
  rw [Nat.unpair_pair]
  simp only [hn, dite_eq_left q.isLt]
  rfl

theorem nextFrame_bob {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S) (f : Frame S a b)
    (dims : ℕ → ℕ) (Φ : ∀ s, DiscreteCPProtocol.Map f.n (dims s))
    (positive : ∀ s, CompletelyPositive (Φ s))
    (traceSum : ∀ X, HasSum (fun s => (Φ s X).trace) X.trace)
    (next : ∀ s, S f.m (dims s)) (hn : P.node f.state = .bob dims Φ positive traceSum next)
    (s : ℕ) (q : Fin (b * dims s)) :
    nextFrame P (some f) (Nat.pair s q.val) = some (bobChild f dims Φ next s q) := by
  unfold nextFrame
  rw [Nat.unpair_pair]
  simp only [hn, dite_eq_left q.isLt]
  rfl

theorem stepOperator_alice {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S) (f : Frame S a b)
    (abort : Fin 4) (dims : ℕ → ℕ) (Φ : ∀ s, DiscreteCPProtocol.Map f.m (dims s))
    (positive : ∀ s, CompletelyPositive (Φ s))
    (traceSum : ∀ X, HasSum (fun s => (Φ s X).trace) X.trace)
    (next : ∀ s, S (dims s) f.n) (hn : P.node f.state = .alice dims Φ positive traceSum next)
    (s : ℕ) (q : Fin (a * dims s)) :
    DiscreteProtocol.stepOperator (refinementFrom P abort (some f)) [] (Nat.pair s q.val) =
      aliceStep f dims Φ s q := by
  simp only [DiscreteProtocol.stepOperator, refinementFrom, frameAfter, List.foldl_nil, frameNode, hn]
  change paddedNat (fun s => a * dims s) _ (hiddenCode (fun s => a * dims s) ⟨s, q⟩) ⊗ₖ 1 = _
  rw [paddedNat_hiddenCode]
  rfl

theorem stepOperator_bob {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S) (f : Frame S a b)
    (abort : Fin 4) (dims : ℕ → ℕ) (Φ : ∀ s, DiscreteCPProtocol.Map f.n (dims s))
    (positive : ∀ s, CompletelyPositive (Φ s))
    (traceSum : ∀ X, HasSum (fun s => (Φ s X).trace) X.trace)
    (next : ∀ s, S f.m (dims s)) (hn : P.node f.state = .bob dims Φ positive traceSum next)
    (s : ℕ) (q : Fin (b * dims s)) :
    DiscreteProtocol.stepOperator (refinementFrom P abort (some f)) [] (Nat.pair s q.val) =
      bobStep f dims Φ s q := by
  simp only [DiscreteProtocol.stepOperator, refinementFrom, frameAfter, List.foldl_nil, frameNode, hn]
  change 1 ⊗ₖ paddedNat (fun s => b * dims s) _ (hiddenCode (fun s => b * dims s) ⟨s, q⟩) = _
  rw [paddedNat_hiddenCode]
  rfl

abbrev Test (S : ℕ → ℕ → Type*) := ∀ {m n}, S m n → (Joint m n →ₗ[ℂ] ℂ)

def pathTestMap {S : ℕ → ℕ → Type*} (P : MatrixMachine S) (test : Test S) :
    ∀ {m n}, S m n → List ℕ → (Joint m n →ₗ[ℂ] ℂ)
  | _, _, z, [] => test z
  | _, _, z, s :: w => match P.node z with
    | .terminal _ => 0
    | .alice _ Φ _ _ next => (pathTestMap P test (next s) w).comp (leftApplication (Φ s))
    | .bob _ Φ _ _ next => (pathTestMap P test (next s) w).comp (rightApplication (Φ s))

structure FinePath (S : ℕ → ℕ → Type*) (a b : ℕ) where
  frame : Frame S a b
  word : List ℕ
  coefficient : Joint a b

def prependPath {S : ℕ → ℕ → Type*} {a b : ℕ}
    (q : ℕ) (K : Joint a b) (p : FinePath S a b) : FinePath S a b :=
  { p with word := q :: p.word, coefficient := p.coefficient * K }

def hiddenPrefixes {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S) :
    Frame S a b → List ℕ → List (FinePath S a b)
  | f, [] => [⟨f, [], 1⟩]
  | f, s :: w => match P.node f.state with
    | .terminal _ => []
    | .alice dims Φ _ _ next =>
      (List.ofFn fun q : Fin (a * dims s) =>
        (hiddenPrefixes P (aliceChild f dims Φ next s q) w).map
          (prependPath (Nat.pair s q.val) (aliceStep f dims Φ s q))).flatten
    | .bob dims Φ _ _ next =>
      (List.ofFn fun q : Fin (b * dims s) =>
        (hiddenPrefixes P (bobChild f dims Φ next s q) w).map
          (prependPath (Nat.pair s q.val) (bobStep f dims Φ s q))).flatten

theorem hiddenPrefixes_action_test {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (test : Test S) (f : Frame S a b) (w : List ℕ) (X : Joint a b) :
    pathTestMap P test f.state w (pendingApplication f.RA f.RB X) =
      ((hiddenPrefixes P f w).map (fun p =>
        test p.frame.state (pendingApplication p.frame.RA p.frame.RB
          (p.coefficient * X * p.coefficientᴴ)))).sum := by
  induction w generalizing f X with
  | nil => simp [pathTestMap, hiddenPrefixes]
  | cons s w ih =>
    cases hn : P.node f.state with
    | terminal ell => simp [pathTestMap, hiddenPrefixes, hn]
    | alice dims Φ positive traceSum next =>
      simp only [pathTestMap, hn, LinearMap.comp_apply]
      rw [HeterogeneousCPInstrument.left_pending_report_action f.RA f.RB dims Φ positive s X, map_sum]
      simp only [hiddenPrefixes, hn, List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn,
        Function.comp_def, List.map_map, prependPath]
      apply Finset.sum_congr rfl
      intro q hq
      have h := ih (aliceChild f dims Φ next s q) (aliceStep f dims Φ s q * X * (aliceStep f dims Φ s q)ᴴ)
      convert h using 1 <;> simp only [aliceChild, aliceStep, leftKrausApplication,
        Matrix.conjTranspose_mul, Matrix.mul_assoc] <;> rfl
    | bob dims Φ positive traceSum next =>
      simp only [pathTestMap, hn, LinearMap.comp_apply]
      rw [HeterogeneousCPInstrument.right_pending_report_action f.RA f.RB dims Φ positive s X, map_sum]
      simp only [hiddenPrefixes, hn, List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn,
        Function.comp_def, List.map_map, prependPath]
      apply Finset.sum_congr rfl
      intro q hq
      have h := ih (bobChild f dims Φ next s q) (bobStep f dims Φ s q * X * (bobStep f dims Φ s q)ᴴ)
      convert h using 1 <;> simp only [bobChild, bobStep, rightKrausApplication,
        Matrix.conjTranspose_mul, Matrix.mul_assoc] <;> rfl

theorem pathOperator_node_congr {a b : ℕ} (T U : DiscreteProtocol.CountableProtocol a b)
    (h k : List ℕ) (hc : ∀ u, T.node (h ++ u) = U.node (k ++ u)) (w : List ℕ) :
    DiscreteProtocol.pathOperator T h w = DiscreteProtocol.pathOperator U k w := by
  induction w generalizing h k with
  | nil => rfl
  | cons q w ih =>
    simp only [DiscreteProtocol.pathOperator]
    apply congrArg₂ (fun A B : Joint a b => A * B)
    · apply ih
      intro u
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using hc ([q] ++ u)
    · have hn : T.node h = U.node k := by simpa only [List.append_nil] using hc []
      simp only [DiscreteProtocol.stepOperator, hn]

theorem pathOperator_frameAfter {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (abort : Fin 4) (F : Option (Frame S a b)) (h w : List ℕ) :
    DiscreteProtocol.pathOperator (refinementFrom P abort F) h w =
      DiscreteProtocol.pathOperator (refinementFrom P abort (frameAfter P F h)) [] w := by
  apply pathOperator_node_congr
  intro u
  simp only [refinementFrom, List.nil_append, frameAfter_append]

theorem hiddenPrefixes_actual {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (abort : Fin 4) (f : Frame S a b) (w : List ℕ)
    (p : FinePath S a b) (hp : p ∈ hiddenPrefixes P f w) :
    frameAfter P (some f) p.word = some p.frame ∧
      p.frame.coarse = f.coarse ++ w ∧
      p.word.map (fun q => (Nat.unpair q).1) = w ∧
      DiscreteProtocol.pathOperator (refinementFrom P abort (some f)) [] p.word = p.coefficient := by
  induction w generalizing f p with
  | nil =>
    simp only [hiddenPrefixes, List.mem_singleton] at hp
    subst p
    simp [frameAfter, DiscreteProtocol.pathOperator]
  | cons s w ih =>
    cases hn : P.node f.state with
    | terminal ell => simp [hiddenPrefixes, hn] at hp
    | alice dims Φ positive traceSum next =>
      simp only [hiddenPrefixes, hn] at hp
      obtain ⟨l, hl, hp⟩ := List.mem_flatten.mp hp
      obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hl
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
      have hi := ih (aliceChild f dims Φ next s q) p₀ hp₀
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [prependPath, frameAfter, List.foldl_cons]
        rw [nextFrame_alice P f dims Φ positive traceSum next hn s q]
        exact hi.1
      · simpa only [prependPath, aliceChild, List.append_assoc, List.cons_append, List.nil_append] using hi.2.1
      · simp only [prependPath, List.map_cons, Nat.unpair_pair, hi.2.2.1]
      · simp only [prependPath, DiscreteProtocol.pathOperator, List.nil_append]
        rw [pathOperator_frameAfter, frameAfter_singleton,
          nextFrame_alice P f dims Φ positive traceSum next hn s q,
          hi.2.2.2, stepOperator_alice P f abort dims Φ positive traceSum next hn s q]
    | bob dims Φ positive traceSum next =>
      simp only [hiddenPrefixes, hn] at hp
      obtain ⟨l, hl, hp⟩ := List.mem_flatten.mp hp
      obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hl
      obtain ⟨p₀, hp₀, rfl⟩ := List.mem_map.mp hp
      have hi := ih (bobChild f dims Φ next s q) p₀ hp₀
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [prependPath, frameAfter, List.foldl_cons]
        rw [nextFrame_bob P f dims Φ positive traceSum next hn s q]
        exact hi.1
      · simpa only [prependPath, bobChild, List.append_assoc, List.cons_append, List.nil_append] using hi.2.1
      · simp only [prependPath, List.map_cons, Nat.unpair_pair, hi.2.2.1]
      · simp only [prependPath, DiscreteProtocol.pathOperator, List.nil_append]
        rw [pathOperator_frameAfter, frameAfter_singleton,
          nextFrame_bob P f dims Φ positive traceSum next hn s q,
          hi.2.2.2, stepOperator_bob P f abort dims Φ positive traceSum next hn s q]

def traceLinear {i : Type*} [Fintype i] : Matrix i i ℂ →ₗ[ℂ] ℂ where
  toFun X := X.trace
  map_add' X Y := Matrix.trace_add X Y
  map_smul' z X := Matrix.trace_smul z X

def terminalTest {S : ℕ → ℕ → Type*} (P : MatrixMachine S) (j : Fin 4) : Test S :=
  fun z => match P.node z with
  | .terminal ell => if ell = j then traceLinear else 0
  | .alice _ _ _ _ _ => 0
  | .bob _ _ _ _ _ => 0

theorem pathTestMap_terminal {S : ℕ → ℕ → Type*} (P : MatrixMachine S)
    {m n : ℕ} (z : S m n) (w : List ℕ) (j : Fin 4) (X : Joint m n) :
    pathTestMap P (terminalTest P j) z w X = pathEvaluation P z w j X := by
  induction w generalizing m n with
  | nil =>
    cases hn : P.node z with
    | terminal ell => by_cases hj : ell = j <;> simp [pathTestMap, terminalTest, hn, hj, pathEvaluation, traceLinear]
    | alice => simp [pathTestMap, terminalTest, hn, pathEvaluation]
    | bob => simp [pathTestMap, terminalTest, hn, pathEvaluation]
  | cons s w ih =>
    cases hn : P.node z <;> simp [pathTestMap, pathEvaluation, hn, ih]

def prefixTerminalEffect {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S)
    (j : Fin 4) (p : FinePath S a b) : Joint a b := match P.node p.frame.state with
  | .terminal ell => if ell = j then p.coefficientᴴ * p.coefficient else 0
  | .alice _ _ _ _ _ => 0
  | .bob _ _ _ _ _ => 0

theorem prefixTerminalEffect_trace {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S)
    (j : Fin 4) (p : FinePath S a b) (X : Joint a b) :
    (prefixTerminalEffect P j p * X).trace = terminalTest P j p.frame.state
      (pendingApplication p.frame.RA p.frame.RB (p.coefficient * X * p.coefficientᴴ)) := by
  cases hn : P.node p.frame.state with
  | terminal ell =>
    by_cases hj : ell = j
    · simp only [prefixTerminalEffect, terminalTest, hn, ite_eq_left hj]
      change (p.coefficientᴴ * p.coefficient * X).trace =
        (pendingApplication p.frame.RA p.frame.RB (p.coefficient * X * p.coefficientᴴ)).trace
      rw [pendingApplication_trace]
      exact (Matrix.trace_mul_cycle p.coefficient X p.coefficientᴴ).symm
    · simp [prefixTerminalEffect, terminalTest, hn, hj]
  | alice => simp [prefixTerminalEffect, terminalTest, hn]
  | bob => simp [prefixTerminalEffect, terminalTest, hn]

theorem prefixTerminalEffect_posSemidef {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (j : Fin 4) (p : FinePath S a b) : (prefixTerminalEffect P j p).PosSemidef := by
  cases hn : P.node p.frame.state <;> simp only [prefixTerminalEffect, hn]
  · split_ifs <;> first | exact Matrix.posSemidef_conjTranspose_mul_self p.coefficient | exact Matrix.PosSemidef.zero
  · exact Matrix.PosSemidef.zero
  · exact Matrix.PosSemidef.zero

theorem trace_list_sum_mul {a : Type*} [Fintype a] (L : List (Matrix a a ℂ)) (X : Matrix a a ℂ) :
    (L.sum * X).trace = (L.map (fun E => (E * X).trace)).sum := by
  induction L with
  | nil => simp
  | cons E L ih => simp [Matrix.add_mul, Matrix.trace_add, ih]

theorem terminalEffect_eq_prefixes {S : ℕ → ℕ → Type*} (P : MatrixMachine S)
    {a b : ℕ} (z : S a b) (w : List ℕ) (j : Fin 4) :
    terminalEffect P z w j = ((hiddenPrefixes P (initialFrame z) w).map (prefixTerminalEffect P j)).sum := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [terminalEffect_trace, trace_list_sum_mul, List.map_map]
  have h := hiddenPrefixes_action_test P (terminalTest P j) (initialFrame z) w X
  change pathTestMap P (terminalTest P j) z w
    (pendingApplication (LocalRecovery.identity a) (LocalRecovery.identity b) X) = _ at h
  rw [pendingApplication_identity, pathTestMap_terminal] at h
  rw [h]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  exact (prefixTerminalEffect_trace P j p X).symm

theorem hiddenPrefixes_terminalEffect {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (abort : Fin 4) (f : Frame S a b) (w : List ℕ)
    (p : FinePath S a b) (hp : p ∈ hiddenPrefixes P f w) (j : Fin 4) :
    DiscreteProtocol.terminalEffect (refinementFrom P abort (some f)) [] p.word j =
      prefixTerminalEffect P j p := by
  have hi := hiddenPrefixes_actual P abort f w p hp
  rw [DiscreteProtocol.terminalEffect, hi.2.2.2]
  simp only [List.nil_append,
    DiscreteProtocol.terminalLabel, refinementFrom, hi.1]
  cases hn : P.node p.frame.state <;> simp [frameNode, prefixTerminalEffect, hn]

theorem nodup_tagged_words {N : ℕ} (L : Fin N → List (List ℕ))
    (code : Fin N → ℕ) (hc : Function.Injective code) (hL : ∀ q, (L q).Nodup) :
    ((List.ofFn fun q => (L q).map (List.cons (code q))).flatten).Nodup := by
  apply List.nodup_flatten.mpr
  constructor
  · intro l hl
    obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hl
    exact (hL q).map (by intro u v h; exact (List.cons.inj h).2)
  · rw [List.pairwise_ofFn]
    intro i j hij
    apply List.disjoint_left.mpr
    intro w hwi hwj
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hwi
    obtain ⟨v, hv, heq⟩ := List.mem_map.mp hwj
    have he : code i = code j := (List.cons.inj heq).1.symm
    exact (ne_of_lt hij) (hc he)

theorem hiddenPrefixes_words_nodup {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (f : Frame S a b) (w : List ℕ) :
    ((hiddenPrefixes P f w).map FinePath.word).Nodup := by
  induction w generalizing f with
  | nil => simp [hiddenPrefixes]
  | cons s w ih =>
    cases hn : P.node f.state with
    | terminal ell => simp [hiddenPrefixes, hn]
    | alice dims Φ positive traceSum next =>
      have h := nodup_tagged_words
        (fun q : Fin (a * dims s) => (hiddenPrefixes P (aliceChild f dims Φ next s q) w).map FinePath.word)
        (fun q => Nat.pair s q.val)
        (by intro i j h; exact Fin.ext (Nat.pair_eq_pair.mp h).2)
        (fun q => ih (aliceChild f dims Φ next s q))
      convert h using 1
      simp only [hiddenPrefixes, hn, List.map_flatten, List.map_ofFn,
        List.map_map, prependPath, Function.comp_def]
    | bob dims Φ positive traceSum next =>
      have h := nodup_tagged_words
        (fun q : Fin (b * dims s) => (hiddenPrefixes P (bobChild f dims Φ next s q) w).map FinePath.word)
        (fun q => Nat.pair s q.val)
        (by intro i j h; exact Fin.ext (Nat.pair_eq_pair.mp h).2)
        (fun q => ih (bobChild f dims Φ next s q))
      convert h using 1
      simp only [hiddenPrefixes, hn, List.map_flatten, List.map_ofFn,
        List.map_map, prependPath, Function.comp_def]

def projection (u : List ℕ) : List ℕ := u.map (fun q => (Nat.unpair q).1)

theorem terminalEffect_frameAfter {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (abort : Fin 4) (F : Option (Frame S a b)) (h w : List ℕ) (j : Fin 4) :
    DiscreteProtocol.terminalEffect (refinementFrom P abort F) h w j =
      DiscreteProtocol.terminalEffect (refinementFrom P abort (frameAfter P F h)) [] w j := by
  unfold DiscreteProtocol.terminalEffect
  rw [pathOperator_frameAfter P abort F h w]
  simp only [DiscreteProtocol.terminalLabel, refinementFrom, List.nil_append, frameAfter_append]
  rfl

theorem terminalEffect_cons_frame {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (abort : Fin 4) (F : Option (Frame S a b))
    (q : ℕ) (u : List ℕ) (j : Fin 4) :
    DiscreteProtocol.terminalEffect (refinementFrom P abort F) [] (q :: u) j =
      (DiscreteProtocol.stepOperator (refinementFrom P abort F) [] q)ᴴ *
      DiscreteProtocol.terminalEffect (refinementFrom P abort (nextFrame P F q)) [] u j *
      DiscreteProtocol.stepOperator (refinementFrom P abort F) [] q := by
  rw [DiscreteProtocol.terminalEffect_cons, terminalEffect_frameAfter]
  simp only [List.nil_append, frameAfter_singleton]

theorem terminalEffect_support_prefixes {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (abort : Fin 4) (f : Frame S a b) (u : List ℕ) (j : Fin 4)
    (hu : DiscreteProtocol.terminalEffect (refinementFrom P abort (some f)) [] u j ≠ 0) :
    ∃ p ∈ hiddenPrefixes P f (projection u), p.word = u := by
  induction u generalizing f with
  | nil => exact ⟨⟨f, [], 1⟩, by simp [hiddenPrefixes, projection], rfl⟩
  | cons q u ih =>
    obtain ⟨⟨s, t⟩, hq⟩ := Nat.pairEquiv.surjective q
    change Nat.pair s t = q at hq
    subst q
    have he := terminalEffect_cons_frame P abort (some f) (Nat.pair s t) u j
    cases hn : P.node f.state with
    | terminal ell =>
      have hz : DiscreteProtocol.stepOperator (refinementFrom P abort (some f)) [] (Nat.pair s t) = 0 := by
        simp [DiscreteProtocol.stepOperator, refinementFrom, frameAfter, frameNode, hn]
      exact False.elim (hu (by rw [he, hz]; simp))
    | alice dims Φ positive traceSum next =>
      by_cases ht : t < a * dims s
      · let r : Fin (a * dims s) := ⟨t, ht⟩
        have hnxt := nextFrame_alice P f dims Φ positive traceSum next hn s r
        have hstep := stepOperator_alice P f abort dims Φ positive traceSum next hn s r
        rw [hnxt, hstep] at he
        have hchild : DiscreteProtocol.terminalEffect
            (refinementFrom P abort (some (aliceChild f dims Φ next s r))) [] u j ≠ 0 := by
          intro hz
          exact hu (by rw [he, hz]; simp)
        obtain ⟨p, hp, hw⟩ := ih (aliceChild f dims Φ next s r) hchild
        refine ⟨prependPath (Nat.pair s r.val) (aliceStep f dims Φ s r) p, ?_, ?_⟩
        · simp only [projection, List.map_cons, Nat.unpair_pair, hiddenPrefixes, hn]
          apply List.mem_flatten.mpr
          refine ⟨_, List.mem_ofFn.mpr ⟨r, rfl⟩, ?_⟩
          exact List.mem_map.mpr ⟨p, hp, rfl⟩
        · simp [prependPath, hw, r]
      · have hz : DiscreteProtocol.stepOperator (refinementFrom P abort (some f)) [] (Nat.pair s t) = 0 := by
          simp only [DiscreteProtocol.stepOperator, refinementFrom, frameAfter, List.foldl_nil, frameNode, hn]
          change paddedNat (fun s => a * dims s) _ (Nat.pair s t) ⊗ₖ 1 = 0
          unfold paddedNat
          rw [Nat.unpair_pair]
          simp [ht]
        exact False.elim (hu (by rw [he, hz]; simp))

    | bob dims Φ positive traceSum next =>
      by_cases ht : t < b * dims s
      · let r : Fin (b * dims s) := ⟨t, ht⟩
        have hnxt := nextFrame_bob P f dims Φ positive traceSum next hn s r
        have hstep := stepOperator_bob P f abort dims Φ positive traceSum next hn s r
        rw [hnxt, hstep] at he
        have hchild : DiscreteProtocol.terminalEffect
            (refinementFrom P abort (some (bobChild f dims Φ next s r))) [] u j ≠ 0 := by
          intro hz
          exact hu (by rw [he, hz]; simp)
        obtain ⟨p, hp, hw⟩ := ih (bobChild f dims Φ next s r) hchild
        refine ⟨prependPath (Nat.pair s r.val) (bobStep f dims Φ s r) p, ?_, ?_⟩
        · simp only [projection, List.map_cons, Nat.unpair_pair, hiddenPrefixes, hn]
          apply List.mem_flatten.mpr
          refine ⟨_, List.mem_ofFn.mpr ⟨r, rfl⟩, ?_⟩
          exact List.mem_map.mpr ⟨p, hp, rfl⟩
        · simp [prependPath, hw, r]
      · have hz : DiscreteProtocol.stepOperator (refinementFrom P abort (some f)) [] (Nat.pair s t) = 0 := by
          simp only [DiscreteProtocol.stepOperator, refinementFrom, frameAfter, List.foldl_nil, frameNode, hn]
          change 1 ⊗ₖ paddedNat (fun s => b * dims s) _ (Nat.pair s t) = 0
          unfold paddedNat
          rw [Nat.unpair_pair]
          simp [ht]
        exact False.elim (hu (by rw [he, hz]; simp))

def prefixFiberCode {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (abort : Fin 4) (f : Frame S a b) (w : List ℕ)
    (i : Fin (hiddenPrefixes P f w).length) : {u : List ℕ // projection u = w} :=
  ⟨((hiddenPrefixes P f w).get i).word,
    (hiddenPrefixes_actual P abort f w _ (List.get_mem _ _)).2.2.1⟩

theorem prefixFiberCode_injective {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (abort : Fin 4) (f : Frame S a b) (w : List ℕ) :
    Function.Injective (prefixFiberCode P abort f w) := by
  intro i j hij
  have he := congrArg Subtype.val hij
  change ((hiddenPrefixes P f w).get i).word = ((hiddenPrefixes P f w).get j).word at he
  let L := hiddenPrefixes P f w
  have hN : (L.map FinePath.word).Nodup := hiddenPrefixes_words_nodup P f w
  have hi : i.val < (L.map FinePath.word).length := by simpa only [List.length_map] using i.isLt
  have hj : j.val < (L.map FinePath.word).length := by simpa only [List.length_map] using j.isLt
  change L[i.val].word = L[j.val].word at he
  have hget : (L.map FinePath.word)[i.val] = (L.map FinePath.word)[j.val] := by
    simpa only [List.getElem_map] using he
  exact Fin.ext (hN.getElem_inj_iff.mp hget)

theorem sum_get_map {α M : Type*} [AddCommMonoid M] (L : List α) (f : α → M) :
    (∑ i : Fin L.length, f (L.get i)) = (L.map f).sum := by
  rw [← List.sum_ofFn]
  rw [List.ofFn_comp', List.ofFn_get]

theorem terminal_fiber_hasSum {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (abort : Fin 4) (w : List ℕ) (j : Fin 4) :
    HasSum (fun u : {u : List ℕ // projection u = w} =>
      DiscreteProtocol.terminalEffect (refinement P z abort) [] u.val j) (terminalEffect P z w j) := by
  let f := initialFrame z
  let L := hiddenPrefixes P f w
  let g := prefixFiberCode P abort f w
  have hg : Function.Injective g := prefixFiberCode_injective P abort f w
  have hz (u : {u : List ℕ // projection u = w}) (hu : u ∉ Set.range g) :
      DiscreteProtocol.terminalEffect (refinement P z abort) [] u.val j = 0 := by
    by_contra hn
    obtain ⟨p, hp, hword⟩ := terminalEffect_support_prefixes P abort f u.val j hn
    rw [u.property] at hp
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
    apply hu
    refine ⟨i, Subtype.ext ?_⟩
    change (L.get i).word = u.val
    rw [hi]
    exact hword
  apply (hg.hasSum_iff (f := fun u : {u : List ℕ // projection u = w} =>
    DiscreteProtocol.terminalEffect (refinement P z abort) [] u.val j)
    (a := terminalEffect P z w j) hz).mp
  have heq : (∑ i : Fin L.length,
      DiscreteProtocol.terminalEffect (refinement P z abort) [] (g i).val j) = terminalEffect P z w j := by
    calc
      _ = ∑ i : Fin L.length, prefixTerminalEffect P j (L.get i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hiddenPrefixes_terminalEffect P abort f w _ (List.get_mem _ _) j
      _ = (L.map (prefixTerminalEffect P j)).sum := sum_get_map L _
      _ = terminalEffect P z w j := (terminalEffect_eq_prefixes P z w j).symm
  simpa only [Function.comp_def, heq] using
    (hasSum_fintype (fun i : Fin L.length =>
      DiscreteProtocol.terminalEffect (refinement P z abort) [] (g i).val j))

theorem refined_terminal_summable {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (abort : Fin 4) (j : Fin 4)
    (hs : Summable (fun w => terminalEffect P z w j)) :
    Summable (fun u => DiscreteProtocol.terminalEffect (refinement P z abort) [] u j) := by
  let F := fun u => DiscreteProtocol.terminalEffect (refinement P z abort) [] u j
  let g := fun u => (F u).trace.re
  let e : (Σ w : List ℕ, {u : List ℕ // projection u = w}) ≃ List ℕ :=
    Equiv.sigmaFiberEquiv projection
  let reTrace : Joint a b →+ ℝ :=
    { toFun E := E.trace.re
      map_zero' := by simp
      map_add' := by intro E G; simp [Matrix.trace_add] }
  have hc : Continuous reTrace := by change Continuous (fun E : Joint a b => E.trace.re); fun_prop
  have hg0 (u) : 0 ≤ g u :=
    (Complex.nonneg_iff.mp (DiscreteProtocol.terminalEffect_posSemidef (refinement P z abort) [] u j).trace_nonneg).1
  have hfiber (w : List ℕ) : HasSum (fun u : {u // projection u = w} => g u.val)
      (terminalEffect P z w j).trace.re := (terminal_fiber_hasSum P z abort w j).map reTrace hc
  have represented_hmatrix : Summable (fun w => (terminalEffect P z w j).trace.re) :=
    (hs.hasSum.map reTrace hc).summable
  have houter : Summable (fun w : List ℕ => ∑' u : {u // projection u = w}, g u.val) := by
    have heq : (fun w : List ℕ => ∑' u : {u // projection u = w}, g u.val) =
        (fun w => (terminalEffect P z w j).trace.re) := by
      funext w
      exact (hfiber w).tsum_eq
    rw [heq]
    exact represented_hmatrix
  have hsig : Summable (fun q : Σ w : List ℕ, {u // projection u = w} => g q.2.val) :=
    (summable_sigma_of_nonneg
      (f := fun q : Σ w : List ℕ, {u : List ℕ // projection u = w} => g q.2.val)
      (fun q => hg0 q.2.val)).mpr
      ⟨fun w => (hfiber w).summable, houter⟩
  have hg : Summable g := (e.summable_iff (f := g)).mp hsig
  exact hg.of_norm_bounded (fun u => DiscreteProtocol.posSemidef_norm_le_trace _
    (DiscreteProtocol.terminalEffect_posSemidef (refinement P z abort) [] u j))

theorem refined_terminal_hasSum {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (abort : Fin 4) (j : Fin 4)
    (hs : Summable (fun w => terminalEffect P z w j)) :
    HasSum (fun u => DiscreteProtocol.terminalEffect (refinement P z abort) [] u j)
      (terminalEffects P z j) := by
  let F := fun u => DiscreteProtocol.terminalEffect (refinement P z abort) [] u j
  let e := Equiv.sigmaFiberEquiv projection
  have hsf : Summable F := refined_terminal_summable P z abort j hs
  have hsig : Summable (F ∘ e) := (e.summable_iff (f := F)).mpr hsf
  have heq : (∑' u, F u) = terminalEffects P z j := by
    rw [← e.tsum_eq F]
    change (∑' q, (F ∘ e) q) = terminalEffects P z j
    rw [hsig.tsum_sigma]
    change (∑' w, ∑' u : {u // projection u = w},
      DiscreteProtocol.terminalEffect (refinement P z abort) [] u.val j) = terminalEffects P z j
    simp_rw [(terminal_fiber_hasSum P z abort _ j).tsum_eq]
    rfl
  simpa only [heq] using hsf.hasSum

theorem terminalEffects_refinement {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (abort : Fin 4)
    (hs : ∀ j, Summable (fun w => terminalEffect P z w j)) (j : Fin 4) :
    DiscreteProtocol.terminalEffects (refinement P z abort) [] j = terminalEffects P z j :=
  (refined_terminal_hasSum P z abort j (hs j)).tsum_eq

theorem refinement_globallyDeterministic {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (abort : Fin 4) (hP : GloballyDeterministic P z) :
    DiscreteProtocol.GloballyDeterministic (refinement P z abort) [] := by
  refine ⟨fun j => (refined_terminal_hasSum P z abort j (hP.1 j)).summable, ?_⟩
  simp_rw [terminalEffects_refinement P z abort hP.1]
  exact hP.2

def matrixReportedEvaluation {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (j : Fin 4) (X : Joint a b) : ℂ :=
  ∑' w, pathEvaluation P z w j X

theorem matrixReportedEvaluation_eq_trace {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (j : Fin 4)
    (hs : Summable (fun w => terminalEffect P z w j)) (X : Joint a b) :
    matrixReportedEvaluation P z j X = (terminalEffects P z j * X).trace := by
  unfold matrixReportedEvaluation
  simp_rw [← terminalEffect_trace]
  let f : Joint a b →+ ℂ :=
    { toFun := fun E => (E * X).trace
      map_zero' := by simp
      map_add' := by intro E G; simp [Matrix.add_mul, Matrix.trace_add] }
  have hf : Continuous f := by change Continuous (fun E : Joint a b => (E * X).trace); fun_prop
  exact (hs.hasSum.map f hf).tsum_eq

theorem matrixReportedEvaluation_eq_refinement {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (abort : Fin 4)
    (hs : ∀ j, Summable (fun w => terminalEffect P z w j)) (j : Fin 4) (X : Joint a b) :
    matrixReportedEvaluation P z j X =
      DiscreteProtocol.matrixReportedEvaluation (refinement P z abort) [] j X := by
  rw [matrixReportedEvaluation_eq_trace P z j (hs j) X,
    DiscreteProtocol.matrixReportedEvaluation_eq_trace (refinement P z abort) [] j
      (refined_terminal_hasSum P z abort j (hs j)).summable X,
    terminalEffects_refinement P z abort hs j]

theorem matrixBornProbability_nonneg {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (abort : Fin 4) (hP : GloballyDeterministic P z)
    (j : Fin 4) (X : Joint a b) (hX : X.PosSemidef) :
    0 ≤ (matrixReportedEvaluation P z j X).re := by
  rw [matrixReportedEvaluation_eq_refinement P z abort hP.1 j X]
  exact DiscreteProtocol.matrixBornProbability_nonneg (refinement P z abort) []
    (refinement_globallyDeterministic P z abort hP) j X hX

theorem matrixBornProbability_sum_one {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (hP : GloballyDeterministic P z)
    (X : Joint a b) (hX : X.trace = 1) :
    (∑ j, (matrixReportedEvaluation P z j X).re) = 1 := by
  simp_rw [matrixReportedEvaluation_eq_trace P z _ (hP.1 _) X]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, hP.2, Matrix.one_mul, hX]
  rfl

theorem truncation_matrix_effect_tendsto {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (bA : Fin a) (bB : Fin b) (abort : Fin 4)
    (hP : GloballyDeterministic P z) :
    Filter.Tendsto (fun N j =>
      (DiscreteProtocol.truncation (refinement P z abort) bA bB (Finset.range N) abort N []).effect j)
      Filter.atTop (nhds (terminalEffects P z)) := by
  have hR := DiscreteProtocol.truncation_effect_tendsto (refinement P z abort) bA bB abort []
    (refinement_globallyDeterministic P z abort hP)
  have heq : DiscreteProtocol.terminalEffects (refinement P z abort) [] = terminalEffects P z :=
    funext (terminalEffects_refinement P z abort hP.1)
  rw [heq] at hR
  exact hR

theorem varyingProtocol_mem_finiteTreeEffectSet_closure {S : ℕ → ℕ → Type*} {a b : ℕ}
    {κ : Type*} [Fintype κ] [DecidableEq κ] (ea : (Fin 2 × κ) ≃ Fin a) (eb : (Fin 2 × κ) ≃ Fin b)
    (P : MatrixMachine S) (z : S a b) (bA : Fin a) (bB : Fin b) (abort : Fin 4)
    (hP : GloballyDeterministic P z) :
    (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (terminalEffects P z j)) ∈
      closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb) := by
  have h := DiscreteProtocol.countableProtocol_mem_finiteTreeEffectSet_closure
    ea eb (refinement P z abort) bA bB abort [] (refinement_globallyDeterministic P z abort hP)
  simpa only [terminalEffects_refinement P z abort hP.1] using h

end

end QuantumProver.ElegantJointMeasurement.TailReference.VaryingProtocol

namespace QuantumProver.ElegantJointMeasurement.TailReference.DiscreteProtocol

open QuantumProver.ElegantJointMeasurement.Concurrence
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1000000

theorem sandwich_mono {i o : Type*} [Fintype i] [DecidableEq i]
    [Fintype o] [DecidableEq o] {A B : Matrix i i ℂ} (hAB : A ≤ B)
    (L : Matrix i o ℂ) : Lᴴ * A * L ≤ Lᴴ * B * L := by
  have hp := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hAB)).conjTranspose_mul_mul_same L
  exact sub_nonneg.mp (by simpa only [Matrix.mul_sub, Matrix.sub_mul] using hp.nonneg)

theorem trace_re_mono {i : Type*} [Fintype i] [DecidableEq i]
    {A B : Matrix i i ℂ} (hAB : A ≤ B) : A.trace.re ≤ B.trace.re := by
  have ht := (Complex.nonneg_iff.mp
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hAB)).trace_nonneg).1
  have hreal : 0 ≤ B.trace.re - A.trace.re := by
    simpa only [Matrix.trace_sub, Complex.sub_re] using ht
  exact sub_nonneg.mp hreal

theorem kept_left_gram_le_one {m n : ℕ} (K : ℕ → Matrix (Fin m) (Fin m) ℂ)
    (hs : Summable (fun s => (K s)ᴴ * K s)) (hc : ∑' s, (K s)ᴴ * K s = 1)
    (S : Finset ℕ) :
    (∑ s ∈ S, (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ *
      (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))) ≤ 1 := by
  have hle : (∑ s ∈ S, (K s)ᴴ * K s) ≤ 1 := by
    rw [← hc]
    exact hs.sum_le_tsum S (fun s _ => (Matrix.posSemidef_conjTranspose_mul_self (K s)).nonneg)
  have hp := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hle)).kronecker
    (Matrix.PosSemidef.one : (1 : Matrix (Fin n) (Fin n) ℂ).PosSemidef)
  apply sub_nonneg.mp
  apply Matrix.nonneg_iff_posSemidef.mpr
  convert hp using 1
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  ext ⟨i,r⟩ ⟨j,t⟩
  by_cases hrt : r = t <;> simp [hrt, Matrix.sum_apply, Matrix.sub_apply, Matrix.one_apply]

theorem kept_right_gram_le_one {m n : ℕ} (K : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (hs : Summable (fun s => (K s)ᴴ * K s)) (hc : ∑' s, (K s)ᴴ * K s = 1)
    (S : Finset ℕ) :
    (∑ s ∈ S, ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s)ᴴ *
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s)) ≤ 1 := by
  have hle : (∑ s ∈ S, (K s)ᴴ * K s) ≤ 1 := by
    rw [← hc]
    exact hs.sum_le_tsum S (fun s _ => (Matrix.posSemidef_conjTranspose_mul_self (K s)).nonneg)
  have hp := (Matrix.PosSemidef.one : (1 : Matrix (Fin m) (Fin m) ℂ).PosSemidef).kronecker
    (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hle))
  apply sub_nonneg.mp
  apply Matrix.nonneg_iff_posSemidef.mpr
  convert hp using 1
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  ext ⟨i,r⟩ ⟨j,t⟩
  by_cases hij : i = j <;> simp [hij, Matrix.sum_apply, Matrix.sub_apply, Matrix.one_apply]

theorem selected_total_le_one {m n : ℕ} (P : CountableProtocol m n)
    (S : Finset ℕ) (d : ℕ) (h : List ℕ) :
    (∑ j, selectedEffects P S d h j) ≤ 1 := by
  induction d generalizing h with
  | zero =>
    cases hn : P.node h <;> simp [selectedEffects, terminalLabel, hn]
  | succ d ih =>
    cases hn : P.node h with
    | terminal ell => simp [selectedEffects, hn]
    | alice K hs hc =>
      simp only [selectedEffects, hn]
      rw [Finset.sum_comm]
      calc
        _ = ∑ s ∈ S, (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ *
            (∑ j, selectedEffects P S d (h ++ [s]) j) *
            (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
          simp only [Matrix.mul_sum, Matrix.sum_mul]
        _ ≤ ∑ s ∈ S, (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ *
            (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
          apply Finset.sum_le_sum
          intro s _
          simpa only [Matrix.mul_one] using sandwich_mono (ih (h ++ [s]))
            (K s ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))
        _ ≤ 1 := kept_left_gram_le_one K hs hc S
    | bob K hs hc =>
      simp only [selectedEffects, hn]
      rw [Finset.sum_comm]
      calc
        _ = ∑ s ∈ S, ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s)ᴴ *
            (∑ j, selectedEffects P S d (h ++ [s]) j) *
            ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s) := by
          simp only [Matrix.mul_sum, Matrix.sum_mul]
        _ ≤ ∑ s ∈ S, ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s)ᴴ *
            ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s) := by
          apply Finset.sum_le_sum
          intro s _
          simpa only [Matrix.mul_one] using sandwich_mono (ih (h ++ [s]))
            ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K s)
        _ ≤ 1 := kept_right_gram_le_one K hs hc S

theorem selectedEffects_nonneg {m n : ℕ} (P : CountableProtocol m n)
    (S : Finset ℕ) (d : ℕ) (h : List ℕ) (j : Fin 4) :
    0 ≤ selectedEffects P S d h j := by
  rw [selectedEffects_eq_terminal_sum]
  exact Finset.sum_nonneg (fun w _ => (terminalEffect_posSemidef P h w j).nonneg)

theorem selectedEffects_le_one {m n : ℕ} (P : CountableProtocol m n)
    (S : Finset ℕ) (d : ℕ) (h : List ℕ) (j : Fin 4) :
    selectedEffects P S d h j ≤ 1 :=
  (Finset.single_le_sum (fun ell _ => selectedEffects_nonneg P S d h ell)
    (Finset.mem_univ j)).trans (selected_total_le_one P S d h)

theorem terminal_summable {m n : ℕ} (P : CountableProtocol m n)
    (h : List ℕ) (j : Fin 4) :
    Summable (fun w => terminalEffect P h w j) := by
  let g := fun w => (terminalEffect P h w j).trace.re
  have hg0 (w) : 0 ≤ g w :=
    (Complex.nonneg_iff.mp (terminalEffect_posSemidef P h w j).trace_nonneg).1
  have hbound (W : Finset (List ℕ)) :
      (∑ w ∈ W, g w) ≤ (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ).trace.re := by
    have he := boundedWords_exhaust.eventually (Filter.eventually_ge_atTop W)
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
    have hsub : W ⊆ boundedWords (Finset.range N) N := hN N le_rfl
    calc
      _ ≤ ∑ w ∈ boundedWords (Finset.range N) N, g w :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => hg0 w)
      _ = (selectedEffects P (Finset.range N) N h j).trace.re := by
        simp only [selectedEffects_eq_terminal_sum, g, Matrix.trace_sum, Complex.re_sum]
      _ ≤ _ := trace_re_mono (selectedEffects_le_one P (Finset.range N) N h j)
  have hg : Summable g := summable_of_sum_le hg0 hbound
  exact hg.of_norm_bounded (fun w => posSemidef_norm_le_trace _
    (terminalEffect_posSemidef P h w j))

theorem terminal_total_le_one {m n : ℕ} (P : CountableProtocol m n) (h : List ℕ) :
    (∑ j, terminalEffects P h j) ≤ 1 := by
  have hc : Continuous (fun F : Fin 4 → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ => ∑ j, F j) := by fun_prop
  have hl := (hc.tendsto (terminalEffects P h)).comp
    (selectedEffects_tendsto P h (terminal_summable P h))
  exact le_of_tendsto hl (Filter.Eventually.of_forall (fun N => selected_total_le_one P (Finset.range N) N h))

theorem truncation_completed_effect_tendsto {m n : ℕ} (P : CountableProtocol m n)
    (bA : Fin m) (bB : Fin n) (abort : Fin 4) (h : List ℕ) :
    Filter.Tendsto (fun N j => (truncation P bA bB (Finset.range N) abort N h).effect j)
      Filter.atTop (nhds (fun j => completeEffects (terminalEffects P h) abort j)) := by
  have hc : Continuous (fun F : Fin 4 → Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ =>
      fun j => completeEffects F abort j) := by
    apply continuous_pi
    intro j
    unfold completeEffects
    split_ifs <;> fun_prop
  simpa only [truncation_effect, Function.comp_def] using
    (hc.tendsto (terminalEffects P h)).comp (selectedEffects_tendsto P h (terminal_summable P h))

end
end QuantumProver.ElegantJointMeasurement.TailReference.DiscreteProtocol

namespace QuantumProver.ElegantJointMeasurement.TailReference.VaryingProtocol

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000

theorem terminal_summable {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (abort : Fin 4) (j : Fin 4) :
    Summable (fun w => terminalEffect P z w j) := by
  let F := fun u => DiscreteProtocol.terminalEffect (refinement P z abort) [] u j
  let e : (Σ w : List ℕ, {u : List ℕ // projection u = w}) ≃ List ℕ := Equiv.sigmaFiberEquiv projection
  have hF : Summable F := DiscreteProtocol.terminal_summable (refinement P z abort) [] j
  have hsig : Summable (F ∘ e) := (e.summable_iff (f := F)).mpr hF
  have hout := hsig.sigma' (fun w => (terminal_fiber_hasSum P z abort w j).summable)
  change Summable (fun w => ∑' u : {u : List ℕ // projection u = w},
    DiscreteProtocol.terminalEffect (refinement P z abort) [] u.val j) at hout
  simpa only [(terminal_fiber_hasSum P z abort _ j).tsum_eq] using hout

theorem terminalEffects_refinement_unconditional {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (abort j : Fin 4) :
    DiscreteProtocol.terminalEffects (refinement P z abort) [] j = terminalEffects P z j :=
  terminalEffects_refinement P z abort (terminal_summable P z abort) j

theorem terminal_total_le_one {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (abort : Fin 4) :
    (∑ j, terminalEffects P z j) ≤ 1 := by
  have h := DiscreteProtocol.terminal_total_le_one (refinement P z abort) []
  simpa only [terminalEffects_refinement_unconditional P z abort] using h

def matrixResidual {S : ℕ → ℕ → Type*} {a b : ℕ} (P : MatrixMachine S) (z : S a b) : Joint a b :=
  1 - ∑ j, terminalEffects P z j

theorem matrixResidual_posSemidef {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (abort : Fin 4) :
    (matrixResidual P z).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (terminal_total_le_one P z abort))

def matrixCompletedEffects {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (abort j : Fin 4) : Joint a b :=
  DiscreteProtocol.completeEffects (terminalEffects P z) abort j

theorem truncation_completed_matrix_effect_tendsto {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (bA : Fin a) (bB : Fin b) (abort : Fin 4) :
    Filter.Tendsto (fun N j =>
      (DiscreteProtocol.truncation (refinement P z abort) bA bB (Finset.range N) abort N []).effect j)
      Filter.atTop (nhds (matrixCompletedEffects P z abort)) := by
  have h := DiscreteProtocol.truncation_completed_effect_tendsto (refinement P z abort) bA bB abort []
  have heq : DiscreteProtocol.terminalEffects (refinement P z abort) [] = terminalEffects P z :=
    funext (terminalEffects_refinement_unconditional P z abort)
  rw [heq] at h
  exact h

theorem matrixCompletedEffects_mem_finiteTreeEffectSet_closure {S : ℕ → ℕ → Type*} {a b : ℕ}
    {κ : Type*} [Fintype κ] [DecidableEq κ] (ea : (Fin 2 × κ) ≃ Fin a) (eb : (Fin 2 × κ) ≃ Fin b)
    (P : MatrixMachine S) (z : S a b) (bA : Fin a) (bB : Fin b) (abort : Fin 4) :
    (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (matrixCompletedEffects P z abort j)) ∈
      closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb) := by
  let T := fun N => DiscreteProtocol.truncation (refinement P z abort) bA bB (Finset.range N) abort N []
  have hc : Continuous (fun F : Fin 4 → Joint a b =>
      fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (F j)) := by
    unfold QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect
    fun_prop
  apply QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet_mem_closure_of_tendsto (l := Filter.atTop) ea eb
    (fun N => (T N).tree) (fun N => DiscreteProtocol.report (T N).tree (T N).label)
  simp_rw [DiscreteProtocol.groupedEffect_eq_pullback]
  exact (hc.tendsto (matrixCompletedEffects P z abort)).comp
    (truncation_completed_matrix_effect_tendsto P z bA bB abort)

theorem matrixResidual_code_zero {S : ℕ → ℕ → Type*} {a b : ℕ}
    {c : Type*} [Fintype c] [DecidableEq c] (P : MatrixMachine S) (z : S a b)
    (J : Matrix (Fin a × Fin b) c ℂ)
    (hcode : Jᴴ * (∑ j, terminalEffects P z j) * J = Jᴴ * J) :
    Jᴴ * matrixResidual P z * J = 0 := by
  simp only [matrixResidual, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hcode, sub_self]

theorem matrixCompletedEffects_code_eq {S : ℕ → ℕ → Type*} {a b : ℕ}
    {c : Type*} [Fintype c] [DecidableEq c] (P : MatrixMachine S) (z : S a b) (abort j : Fin 4)
    (J : Matrix (Fin a × Fin b) c ℂ)
    (hcode : Jᴴ * (∑ j, terminalEffects P z j) * J = Jᴴ * J) :
    Jᴴ * matrixCompletedEffects P z abort j * J = Jᴴ * terminalEffects P z j * J := by
  have hz := matrixResidual_code_zero P z J hcode
  unfold matrixCompletedEffects DiscreteProtocol.completeEffects
  by_cases hj : abort = j
  · simp only [hj, ite_true, Matrix.mul_add, Matrix.add_mul]
    change Jᴴ * terminalEffects P z j * J + Jᴴ * matrixResidual P z * J = _
    rw [hz, add_zero]
  · simp [hj]

theorem truncation_promised_code_effect_tendsto {S : ℕ → ℕ → Type*} {a b : ℕ}
    {c : Type*} [Fintype c] [DecidableEq c] (P : MatrixMachine S) (z : S a b)
    (bA : Fin a) (bB : Fin b) (abort : Fin 4) (J : Matrix (Fin a × Fin b) c ℂ)
    (hcode : Jᴴ * (∑ j, terminalEffects P z j) * J = Jᴴ * J) :
    Filter.Tendsto (fun N j => Jᴴ *
      (DiscreteProtocol.truncation (refinement P z abort) bA bB (Finset.range N) abort N []).effect j * J)
      Filter.atTop (nhds (fun j => Jᴴ * terminalEffects P z j * J)) := by
  have hc : Continuous (fun F : Fin 4 → Joint a b => fun j => Jᴴ * F j * J) := by fun_prop
  have hl := (hc.tendsto (matrixCompletedEffects P z abort)).comp
    (truncation_completed_matrix_effect_tendsto P z bA bB abort)
  have heq : (fun j => Jᴴ * matrixCompletedEffects P z abort j * J) =
      (fun j => Jᴴ * terminalEffects P z j * J) := by
    funext j
    exact matrixCompletedEffects_code_eq P z abort j J hcode
  rw [heq] at hl
  exact hl

theorem matrixCompletedEffects_posSemidef {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (abort j : Fin 4) :
    (matrixCompletedEffects P z abort j).PosSemidef := by
  have hF : (terminalEffects P z j).PosSemidef := by
    rw [← terminalEffects_refinement_unconditional P z abort j]
    exact DiscreteProtocol.terminalEffects_posSemidef (refinement P z abort) [] j
  unfold matrixCompletedEffects DiscreteProtocol.completeEffects
  by_cases hj : abort = j
  · simp only [hj, ite_true]
    exact hF.add (matrixResidual_posSemidef P z abort)
  · simpa only [hj, ite_false, add_zero] using hF

theorem matrixCompletedEffects_sum {S : ℕ → ℕ → Type*} {a b : ℕ}
    (P : MatrixMachine S) (z : S a b) (abort : Fin 4) :
    (∑ j, matrixCompletedEffects P z abort j) = 1 := by
  simp [matrixCompletedEffects, DiscreteProtocol.completeEffects, Finset.sum_add_distrib]

theorem exists_complete_closure_extension_on_code {S : ℕ → ℕ → Type*} {a b : ℕ}
    {κ : Type*} {c : Type*} [Fintype κ] [DecidableEq κ] [Fintype c] [DecidableEq c]
    (ea : (Fin 2 × κ) ≃ Fin a) (eb : (Fin 2 × κ) ≃ Fin b)
    (P : MatrixMachine S) (z : S a b) (bA : Fin a) (bB : Fin b) (abort : Fin 4)
    (J : Matrix (Fin a × Fin b) c ℂ)
    (hcode : Jᴴ * (∑ j, terminalEffects P z j) * J = Jᴴ * J) :
    ∃ G : Fin 4 → Joint a b,
      (∀ j, (G j).PosSemidef) ∧ (∑ j, G j) = 1 ∧
      (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (G j)) ∈
        closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb) ∧
      ∀ j, Jᴴ * G j * J = Jᴴ * terminalEffects P z j * J := by
  exact ⟨matrixCompletedEffects P z abort,
    matrixCompletedEffects_posSemidef P z abort,
    matrixCompletedEffects_sum P z abort,
    matrixCompletedEffects_mem_finiteTreeEffectSet_closure ea eb P z bA bB abort,
    fun j => matrixCompletedEffects_code_eq P z abort j J hcode⟩

end
end QuantumProver.ElegantJointMeasurement.TailReference.VaryingProtocol
