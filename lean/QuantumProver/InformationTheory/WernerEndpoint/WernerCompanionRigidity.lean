import QuantumProver.InformationTheory.WernerEndpoint.FormationTheorems
import QuantumProver.InformationTheory.WernerEndpoint.WernerProductFactorization
import QuantumProver.InformationTheory.WernerEndpoint.WernerSlaterRigidity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators ComplexOrder

namespace QuantumProver.WernerEndpoint

private theorem stinespring_normalized_output_purity_pos
    {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (v : Y → ℂ) (hv : vectorNormSq v = 1) :
    0 < purity (N.apply (pureDensity v)) := by
  classical
  apply AntisymmetricEntropyCost.density_purity_pos
    (N.apply (pureDensity v)) (N.apply_posSemidef _ (pureDensity_posSemidef v))
  rw [N.apply_trace, pureDensity_trace, hv]
  norm_num

theorem cptp_purityMaximum_pos
    {Y B : Type*} [Fintype Y] [Fintype B] [DecidableEq Y] [DecidableEq B]
    [Nonempty Y] (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ) :
    0 < CompanionMaximum.pureOutputPurityMaximum Φ := by
  obtain ⟨v, hv, hmax⟩ := CompanionMaximum.exists_pureOutputPurity_eq_maximum Φ
  have hp : 0 < purity (Φ (pureDensity v)) := by
    rw [← stinespringOfCPTP_apply Φ hCP hTP (pureDensity v)]
    exact stinespring_normalized_output_purity_pos (stinespringOfCPTP Φ hCP hTP) v hv
  rwa [hmax] at hp

theorem antisymmetric_companion_maximizer_iff_product {d : ℕ} (hd : 2 ≤ d)
    {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) (β : ℝ) (hβ : 0 < β)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (N.apply (pureDensity v)) ≤ β)
    (Ψ : Edge d × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (((antisymmetricStinespring d).tensor N).apply (pureDensity Ψ)) = β / 2 ↔
      ∃ x : Edge d → ℂ, ∃ y : Y → ℂ,
        vectorNormSq x = 1 ∧ vectorNormSq y = 1 ∧ IsNormalizedSlater x ∧
        purity (N.apply (pureDensity y)) = β ∧
        ∀ xy, Ψ xy = x xy.1 * y xy.2 := by
  classical
  constructor
  · intro hmax
    have hsUpper : purity (companionMarginal Ψ) ≤ 1 :=
      normalized_coefficient_purity_le_one (companionCoefficient Ψ)
        (by rw [companionCoefficient_hsNormSq, hΨ])
    have hStrict := antisymmetric_companion_purity_strong hd N β hbound Ψ hΨ
    have hCoef : 0 < β / ((d : ℝ) + 1) := div_pos hβ (by positivity)
    have hsLower : 1 ≤ purity (companionMarginal Ψ) := by
      by_contra hnot
      have hs : purity (companionMarginal Ψ) < 1 := lt_of_not_ge hnot
      have hz : 0 < β / ((d : ℝ) + 1) * (1 - purity (companionMarginal Ψ)) :=
        mul_pos hCoef (sub_pos.mpr hs)
      rw [hmax] at hStrict
      linarith
    have hsOne : purity (companionMarginal Ψ) = 1 := le_antisymm hsUpper hsLower
    have hMarginal : companionMarginal Ψ = partialTraceRight (pureDensity Ψ) := by
      ext y y'
      rfl
    rw [hMarginal] at hsOne
    obtain ⟨x, y, hx, hy, hProduct⟩ :=
      (WernerProductFactorization.marginal_purity_eq_one_iff_exists_product Ψ hΨ).mp hsOne
    have hFunction : Ψ = fun xy => x xy.1 * y xy.2 := funext hProduct
    rw [hFunction, Stinespring.tensor_product_purity,
      ← antisymmetricChannel_eq_stinespring] at hmax
    have hxUpper := antisymmetric_oneCopy_purity_le_half d x hx
    rw [← antisymmetricChannel_eq_stinespring] at hxUpper
    have hyUpper := hbound y hy
    have hyPositive := stinespring_normalized_output_purity_pos N y hy
    have hProductUpper := mul_le_mul_of_nonneg_right hxUpper (le_of_lt hyPositive)
    have hyLower : β ≤ purity (N.apply (pureDensity y)) := by linarith
    have hyMax : purity (N.apply (pureDensity y)) = β := le_antisymm hyUpper hyLower
    rw [hyMax] at hmax
    have hxLower : (1 / 2 : ℝ) ≤ purity (antisymmetricChannel d (pureDensity x)) := by
      by_contra hnot
      have hxStrict : purity (antisymmetricChannel d (pureDensity x)) < (1 / 2 : ℝ) :=
        lt_of_not_ge hnot
      have hz := mul_lt_mul_of_pos_right hxStrict hβ
      linarith
    have hxMax : purity (antisymmetricChannel d (pureDensity x)) = (1 / 2 : ℝ) :=
      le_antisymm hxUpper hxLower
    exact ⟨x, y, hx, hy, (antisymmetric_purity_half_iff_slater x hx).mp hxMax,
      hyMax, hProduct⟩
  · rintro ⟨x, y, hx, hy, hSlater, hyMax, hProduct⟩
    have hFunction : Ψ = fun xy => x xy.1 * y xy.2 := funext hProduct
    rw [hFunction, Stinespring.tensor_product_purity,
      ← antisymmetricChannel_eq_stinespring,
      (antisymmetric_purity_half_iff_slater x hx).mpr hSlater, hyMax]
    ring

theorem antisymmetric_cptp_maximizer_iff_product {d : ℕ} (hd : 2 ≤ d)
    {Y B : Type*} [Fintype Y] [Fintype B] [DecidableEq Y] [DecidableEq B]
    [Nonempty Y] (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ)
    (Ψ : Edge d × Y → ℂ) (hΨ : vectorNormSq Ψ = 1) :
    purity (((antisymmetricStinespring d).tensor (stinespringOfCPTP Φ hCP hTP)).apply
      (pureDensity Ψ)) = CompanionMaximum.pureOutputPurityMaximum Φ / 2 ↔
      ∃ x : Edge d → ℂ, ∃ y : Y → ℂ,
        vectorNormSq x = 1 ∧ vectorNormSq y = 1 ∧ IsNormalizedSlater x ∧
        purity (Φ (pureDensity y)) = CompanionMaximum.pureOutputPurityMaximum Φ ∧
        ∀ xy, Ψ xy = x xy.1 * y xy.2 := by
  have hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 →
      purity ((stinespringOfCPTP Φ hCP hTP).apply (pureDensity v)) ≤
        CompanionMaximum.pureOutputPurityMaximum Φ := by
    intro v hv
    rw [stinespringOfCPTP_apply]
    exact CompanionMaximum.pureOutputPurity_le_maximum Φ v hv
  simpa only [stinespringOfCPTP_apply] using
    antisymmetric_companion_maximizer_iff_product hd (stinespringOfCPTP Φ hCP hTP)
      (CompanionMaximum.pureOutputPurityMaximum Φ) (cptp_purityMaximum_pos Φ hCP hTP)
      hbound Ψ hΨ

end QuantumProver.WernerEndpoint
