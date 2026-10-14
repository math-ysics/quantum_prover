import QuantumProver.InformationTheory.WernerEndpoint.FormationTheorems
import QuantumProver.InformationTheory.WernerEndpoint.WernerFlatOutput

set_option autoImplicit false

noncomputable section

namespace QuantumProver.WernerEndpoint.WernerCoefficientSharpness

open scoped BigOperators ComplexOrder Matrix

def flatScale (d : ℕ) : ℂ := ((Real.sqrt (Fintype.card (Edge d) : ℝ))⁻¹ : ℝ)

def flatCompanionInput (d : ℕ) : Edge d × Edge d → ℂ :=
  fun xy => flatScale d * (if xy.1 = xy.2 then 1 else 0)

theorem edge_card_real (d : ℕ) :
    (Fintype.card (Edge d) : ℝ) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  rw [QuantumProver.WernerEndpoint.SlaterMoments.edge_card_choose, Nat.cast_choose_two ℝ]

theorem edge_card_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < (Fintype.card (Edge d) : ℝ) := by
  letI : Nonempty (Edge d) := ⟨firstEndpointEdge d hd⟩
  exact_mod_cast Fintype.card_pos

theorem edge_card_gt_one {d : ℕ} (hd : 3 ≤ d) :
    1 < (Fintype.card (Edge d) : ℝ) := by
  rw [edge_card_real]
  have h : (3 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith [sq_nonneg ((d : ℝ) - 3)]

theorem flatScale_mul_star (d : ℕ) :
    flatScale d * star (flatScale d) = (Fintype.card (Edge d) : ℂ)⁻¹ := by
  have hr : (Real.sqrt (Fintype.card (Edge d) : ℝ))⁻¹ *
      (Real.sqrt (Fintype.card (Edge d) : ℝ))⁻¹ =
        (Fintype.card (Edge d) : ℝ)⁻¹ := by
    rw [← mul_inv, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg _)]
  simpa [flatScale] using congrArg (fun t : ℝ => (t : ℂ)) hr

theorem flatScale_normSq (d : ℕ) :
    Complex.normSq (flatScale d) = (Fintype.card (Edge d) : ℝ)⁻¹ := by
  simp only [flatScale, Complex.normSq_ofReal, ← sq, inv_pow]
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]

theorem flatCompanionInput_normSq {d : ℕ} (hd : 2 ≤ d) :
    vectorNormSq (flatCompanionInput d) = 1 := by
  have hD : (Fintype.card (Edge d) : ℝ) ≠ 0 := ne_of_gt (edge_card_pos hd)
  simp only [vectorNormSq, flatCompanionInput, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, apply_ite, Complex.normSq_zero]
  simp [flatScale_normSq, eq_comm] <;> field_simp [hD]

theorem flatCompanionInput_marginal (d : ℕ) :
    companionMarginal (flatCompanionInput d) =
      Matrix.diagonal (fun _ : Edge d => (Fintype.card (Edge d) : ℂ)⁻¹) := by
  have hleft : companionMarginal (flatCompanionInput d) =
      partialTraceLeft (pureDensity (flatCompanionInput d)) := by
    ext y z
    simp only [companionMarginal, companionCoefficient, reducedLeft, crossLeft,
      partialTraceLeft, pureDensity, crossDensity, flatCompanionInput]
    simp only [eq_comm]
  rw [hleft]
  change partialTraceLeft (pureDensity (fun xy : Edge d × Edge d =>
    flatScale d * (if xy.1 = xy.2 then 1 else 0))) = _
  rw [equalLabel_partialTrace, flatScale_mul_star]

theorem flatCompanionInput_marginal_purity {d : ℕ} (hd : 2 ≤ d) :
    purity (companionMarginal (flatCompanionInput d)) =
      1 / (Fintype.card (Edge d) : ℝ) := by
  have hD : (Fintype.card (Edge d) : ℝ) ≠ 0 := ne_of_gt (edge_card_pos hd)
  rw [flatCompanionInput_marginal]
  simp only [purity, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  field_simp [hD]

theorem flatCompanionInput_marginal_purity_lt_one {d : ℕ} (hd : 3 ≤ d) :
    purity (companionMarginal (flatCompanionInput d)) < 1 := by
  rw [flatCompanionInput_marginal_purity (by omega : 2 ≤ d)]
  exact (div_lt_iff₀ (edge_card_pos (by omega : 2 ≤ d))).2
    (by simpa using edge_card_gt_one hd)

theorem diagonal_const_eq_smul_one {I : Type*} [DecidableEq I] (c : ℂ) :
    Matrix.diagonal (fun _ : I => c) = c • (1 : Matrix I I ℂ) := by
  ext i j
  by_cases hij : i = j <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply, Matrix.smul_apply, hij]

theorem antisymmetric_identity_output (d : ℕ) :
    (antisymmetricStinespring d).apply 1 = (((d : ℂ) - 1) / 2) •
      (1 : Matrix (Fin d) (Fin d) ℂ) := by
  change partialTraceLeft (wedgeInclusion d * 1 * (wedgeInclusion d).conjTranspose) = _
  rw [Matrix.mul_one]
  change partialTraceLeft (wedgeProjector d) = _
  rw [wedgeProjector_eq_antisymmetrizer]
  ext a b
  by_cases hab : a = b
  · subst b
    simp [partialTraceLeft, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      physicalSwap, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_mul, Prod.mk.injEq, mul_sub, sub_mul, mul_ite, ite_mul,
      smul_eq_mul, eq_comm] <;> ring
  · simp [partialTraceLeft, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      physicalSwap, Finset.sum_sub_distrib, Finset.mul_sum, Prod.mk.injEq,
      smul_eq_mul, hab, Ne.symm hab, ite_and, mul_sub, sub_mul, mul_ite, ite_mul]

theorem flatCompanionInput_companion_output {d : ℕ} (hd : 2 ≤ d) :
    (antisymmetricStinespring d).apply (companionMarginal (flatCompanionInput d)) =
      (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  rw [flatCompanionInput_marginal, diagonal_const_eq_smul_one,
    Stinespring.apply_scalar, antisymmetric_identity_output, smul_smul,
    QuantumProver.WernerEndpoint.SlaterMoments.edge_card_complex]
  have hd0 : (d : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : d ≠ 0)
  have hd1 : (d : ℂ) - 1 ≠ 0 := by
    have hne : d ≠ 1 := by omega
    simpa only [sub_ne_zero] using (by exact_mod_cast hne : (d : ℂ) ≠ 1)
  congr 1
  field_simp [hd0, hd1] <;> ring

theorem flatCompanionInput_companion_complement {d : ℕ} (hd : 2 ≤ d) :
    (antisymmetricStinespring d).complement (companionMarginal (flatCompanionInput d)) =
      (d : ℂ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  change antisymmetricComplement d (companionMarginal (flatCompanionInput d)) = _
  rw [← antisymmetricChannel_eq_complement, antisymmetricChannel_eq_stinespring]
  exact flatCompanionInput_companion_output hd

theorem flatCompanionInput_companion_output_purity {d : ℕ} (hd : 2 ≤ d) :
    purity ((antisymmetricStinespring d).apply
      (companionMarginal (flatCompanionInput d))) = 1 / (d : ℝ) := by
  rw [flatCompanionInput_companion_output hd]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hs : (d : ℂ)⁻¹ = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hs, matrix_purity_real_scalar]
  simp only [purity, Matrix.one_mul, Matrix.trace_one, Fintype.card_fin, Complex.natCast_re]
  field_simp [hd0]

theorem flatCompanionInput_companion_complement_purity {d : ℕ} (hd : 2 ≤ d) :
    purity ((antisymmetricStinespring d).complement
      (companionMarginal (flatCompanionInput d))) = 1 / (d : ℝ) := by
  rw [flatCompanionInput_companion_complement hd, ← flatCompanionInput_companion_output hd]
  exact flatCompanionInput_companion_output_purity hd

theorem antisymmetric_purityMaximum_eq_half {d : ℕ} (hd : 2 ≤ d) :
    CompanionMaximum.pureOutputPurityMaximum
      (Corollaries.stinespringLinearMap (antisymmetricStinespring d)) = 1 / 2 := by
  letI : Nonempty (Edge d) := ⟨firstEndpointEdge d hd⟩
  apply le_antisymm
  · apply csSup_le (CompanionMaximum.pureOutputPurityRange_nonempty _)
    rintro p ⟨v, hv, rfl⟩
    exact antisymmetric_oneCopy_purity_le_half d v hv
  · apply le_csSup (CompanionMaximum.pureOutputPurityRange_bddAbove _)
    refine ⟨coordinateSlater (firstEndpointEdge d hd), coordinateSlater_normSq _, ?_⟩
    exact antisymmetricChannel_slater_purity _

theorem diagonalVector_normSq (d : ℕ) :
    vectorNormSq (WernerFlatOutput.diagonalVector d) = (d : ℝ) := by
  simp only [vectorNormSq, Fintype.sum_prod_type, WernerFlatOutput.diagonalVector]
  simp [apply_ite, eq_comm]

theorem diagonalVector_dot_self (d : ℕ) :
    dotProduct (star (WernerFlatOutput.diagonalVector d))
      (WernerFlatOutput.diagonalVector d) = (d : ℂ) := by
  simp only [dotProduct, Fintype.sum_prod_type, WernerFlatOutput.diagonalVector, Pi.star_apply]
  simp [apply_ite, eq_comm]

theorem identity_rankOne_trace_square (d : ℕ) (t : ℂ) :
    Matrix.trace ((1 + t • pureDensity (WernerFlatOutput.diagonalVector d)) *
      (1 + t • pureDensity (WernerFlatOutput.diagonalVector d))) =
        (d : ℂ) ^ 2 + 2 * t * d + t ^ 2 * (d : ℂ) ^ 2 := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul, Matrix.trace_one, Fintype.card_prod, Fintype.card_fin,
    pureDensity_trace, diagonalVector_normSq,
    AntisymmetricEnsembleCost.pureDensity_mul_trace, diagonalVector_dot_self]
  simp only [Complex.normSq_natCast]
  push_cast
  ring

theorem identity_rankOne_purity (d : ℕ) (t : ℝ) :
    purity (1 + (t : ℂ) • pureDensity (WernerFlatOutput.diagonalVector d)) =
      (d : ℝ) ^ 2 + 2 * t * d + t ^ 2 * (d : ℝ) ^ 2 := by
  have ht : Matrix.trace ((1 + (t : ℂ) • pureDensity (WernerFlatOutput.diagonalVector d)) *
      (1 + (t : ℂ) • pureDensity (WernerFlatOutput.diagonalVector d))) =
        (((d : ℝ) ^ 2 + 2 * t * d + t ^ 2 * (d : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [identity_rankOne_trace_square]
    push_cast
    ring
  simp only [purity, ht, Complex.ofReal_re]

theorem flatCompanionInput_output_matrix (d : ℕ) :
    ((antisymmetricStinespring d).tensor (antisymmetricStinespring d)).apply
      (pureDensity (flatCompanionInput d)) =
        ((1 / (4 * (Fintype.card (Edge d) : ℝ)) : ℝ) : ℂ) •
          (1 + (((d : ℝ) - 2 : ℝ) : ℂ) •
            pureDensity (WernerFlatOutput.diagonalVector d)) := by
  unfold flatCompanionInput
  rw [WernerFlatOutput.equalLabel_joint_output, flatScale_mul_star]
  congr 1 <;> push_cast <;> simp [div_eq_mul_inv, mul_inv_rev, mul_comm]

theorem flatCompanionInput_output_purity {d : ℕ} (hd : 2 ≤ d) :
    purity (((antisymmetricStinespring d).tensor (antisymmetricStinespring d)).apply
      (pureDensity (flatCompanionInput d))) =
        ((d : ℝ) ^ 2 - 3 * d + 4) / (4 * d * ((d : ℝ) - 1)) := by
  rw [flatCompanionInput_output_matrix, matrix_purity_real_scalar, identity_rankOne_purity,
    edge_card_real]
  have hd0 : (d : ℝ) ≠ 0 := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  field_simp [hd0, hd1]
  ring

theorem flatCompanionInput_saturates {d : ℕ} (hd : 2 ≤ d) :
    purity (((antisymmetricStinespring d).tensor (antisymmetricStinespring d)).apply
      (pureDensity (flatCompanionInput d))) =
        (1 / 2 : ℝ) / 2 - (1 / 2 : ℝ) / ((d : ℝ) + 1) *
          (1 - purity (companionMarginal (flatCompanionInput d))) := by
  rw [flatCompanionInput_output_purity hd, flatCompanionInput_marginal_purity hd,
    edge_card_real]
  have hd0 : (d : ℝ) ≠ 0 := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hdp : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hd0, hd1, hdp]
  ring

theorem impurity_coefficient_le {d : ℕ} (hd : 3 ≤ d) (k : ℝ)
    (h : ∀ Ψ : Edge d × Edge d → ℂ, vectorNormSq Ψ = 1 →
      purity (((antisymmetricStinespring d).tensor (antisymmetricStinespring d)).apply
        (pureDensity Ψ)) ≤ 1 / 4 - k * (1 - purity (companionMarginal Ψ))) :
    k ≤ 1 / (2 * ((d : ℝ) + 1)) := by
  have hb := h (flatCompanionInput d) (flatCompanionInput_normSq (by omega : 2 ≤ d))
  rw [flatCompanionInput_saturates (by omega : 2 ≤ d)] at hb
  have hs := flatCompanionInput_marginal_purity_lt_one hd
  have hmul : k * (1 - purity (companionMarginal (flatCompanionInput d))) ≤
      (1 / (2 * ((d : ℝ) + 1))) *
        (1 - purity (companionMarginal (flatCompanionInput d))) := by
    have hc : (1 / 2 : ℝ) / ((d : ℝ) + 1) = 1 / (2 * ((d : ℝ) + 1)) := by
      simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
    rw [hc] at hb
    linarith
  exact le_of_mul_le_mul_right hmul (by linarith)

def IsUniversalImpurityCoefficient (d : ℕ) (c : ℝ) : Prop :=
  ∀ (Y B E : Type) [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y] [Nonempty Y]
    (N : Stinespring Y B E) (Ψ : Edge d × Y → ℂ), vectorNormSq Ψ = 1 →
      purity (((antisymmetricStinespring d).tensor N).apply (pureDensity Ψ)) ≤
        CompanionMaximum.pureOutputPurityMaximum (Corollaries.stinespringLinearMap N) / 2 -
          CompanionMaximum.pureOutputPurityMaximum (Corollaries.stinespringLinearMap N) *
            c * (1 - purity (companionMarginal Ψ))

theorem impurity_coefficient_valid {d : ℕ} (hd : 2 ≤ d) :
    IsUniversalImpurityCoefficient d (1 / ((d : ℝ) + 1)) := by
  intro Y B E _ _ _ _ _ N Ψ hΨ
  have h := antisymmetric_companion_purity_strong hd N
    (CompanionMaximum.pureOutputPurityMaximum (Corollaries.stinespringLinearMap N))
    (CompanionMaximum.pureOutputPurity_le_maximum
      (Corollaries.stinespringLinearMap N)) Ψ hΨ
  simpa only [div_eq_mul_inv, one_mul, mul_assoc] using h

theorem universal_impurity_coefficient_le {d : ℕ} (hd : 3 ≤ d) (c : ℝ)
    (h : IsUniversalImpurityCoefficient d c) : c ≤ 1 / ((d : ℝ) + 1) := by
  letI : Nonempty (Edge d) := ⟨firstEndpointEdge d (by omega)⟩
  have hk := impurity_coefficient_le hd (c / 2) (by
    intro Ψ hΨ
    have hb := h (Edge d) (Fin d) (Fin d) (antisymmetricStinespring d) Ψ hΨ
    rw [antisymmetric_purityMaximum_eq_half (by omega : 2 ≤ d)] at hb
    convert hb using 1 <;> ring)
  have heq : 1 / (2 * ((d : ℝ) + 1)) = (1 / ((d : ℝ) + 1)) / 2 := by
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
  rw [heq] at hk
  linarith

theorem impurity_coefficient_sharp {d : ℕ} (hd : 3 ≤ d) :
    IsUniversalImpurityCoefficient d (1 / ((d : ℝ) + 1)) ∧
      ∀ c : ℝ, IsUniversalImpurityCoefficient d c → c ≤ 1 / ((d : ℝ) + 1) :=
  ⟨impurity_coefficient_valid (by omega), universal_impurity_coefficient_le hd⟩

theorem flatCompanionInput_sharpness {d : ℕ} (hd : 3 ≤ d) :
    vectorNormSq (flatCompanionInput d) = 1 ∧
      purity (companionMarginal (flatCompanionInput d)) =
        1 / (Fintype.card (Edge d) : ℝ) ∧
      purity (companionMarginal (flatCompanionInput d)) < 1 ∧
      CompanionMaximum.pureOutputPurityMaximum
        (Corollaries.stinespringLinearMap (antisymmetricStinespring d)) = 1 / 2 ∧
      purity (((antisymmetricStinespring d).tensor (antisymmetricStinespring d)).apply
        (pureDensity (flatCompanionInput d))) =
          (1 / 2 : ℝ) / 2 - (1 / 2 : ℝ) / ((d : ℝ) + 1) *
            (1 - purity (companionMarginal (flatCompanionInput d))) ∧
      IsUniversalImpurityCoefficient d (1 / ((d : ℝ) + 1)) ∧
      ∀ c : ℝ, IsUniversalImpurityCoefficient d c → c ≤ 1 / ((d : ℝ) + 1) := by
  have hd2 : 2 ≤ d := by omega
  exact ⟨flatCompanionInput_normSq hd2, flatCompanionInput_marginal_purity hd2,
    flatCompanionInput_marginal_purity_lt_one hd, antisymmetric_purityMaximum_eq_half hd2,
    flatCompanionInput_saturates hd2, impurity_coefficient_sharp hd⟩

end QuantumProver.WernerEndpoint.WernerCoefficientSharpness
