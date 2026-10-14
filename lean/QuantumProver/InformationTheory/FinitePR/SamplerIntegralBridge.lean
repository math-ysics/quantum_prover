import Mathlib

/-! Exact real-integral consequences of a proved sampler pushforward law.
No compactness, probability normalization or integrability input is needed.
Mathlib's Bochner convention covers the nonintegrable branches. -/

namespace FinitePR.SamplerIntegral

open MeasureTheory
open scoped ENNReal

theorem integral_comp_eq_density_mul_of_ae_nonneg
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) (q : Measure B) (g : A → B) (hg : Measurable g)
    (f : B → ℝ) (hf : Measurable f) (hnonneg : ∀ᵐ b ∂q, 0 ≤ f b)
    (hlaw : P.map g = q.withDensity (fun b => ENNReal.ofReal (f b)))
    (k : B → ℝ) (hk : Measurable k) :
    (∫ a, k (g a) ∂P) = ∫ b, f b * k b ∂q := by
  have hfm : Measurable (fun b => ENNReal.ofReal (f b)) := hf.ennreal_ofReal
  have hfinite : ∀ᵐ b ∂q, ENNReal.ofReal (f b) < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  calc
    (∫ a, k (g a) ∂P) = ∫ b, k b ∂P.map g :=
      (integral_map hg.aemeasurable hk.aestronglyMeasurable).symm
    _ = ∫ b, k b ∂q.withDensity (fun b => ENNReal.ofReal (f b)) := by rw [hlaw]
    _ = ∫ b, f b * k b ∂q := by
      rw [integral_withDensity_eq_integral_toReal_smul hfm hfinite k]
      apply integral_congr_ae
      filter_upwards [hnonneg] with b hb
      simp only [ENNReal.toReal_ofReal hb, smul_eq_mul]

/-- The exact sampler-law bridge with the actual pointwise density bounds. -/
theorem integral_comp_eq_density_mul
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) (q : Measure B) (g : A → B) (hg : Measurable g)
    (f : B → ℝ) (hf : Measurable f) (hnonneg : ∀ b, 0 ≤ f b)
    (hlaw : P.map g = q.withDensity (fun b => ENNReal.ofReal (f b)))
    (k : B → ℝ) (hk : Measurable k) :
    (∫ a, k (g a) ∂P) = ∫ b, f b * k b ∂q :=
  integral_comp_eq_density_mul_of_ae_nonneg P q g hg f hf
    (Filter.Eventually.of_forall hnonneg) hlaw k hk

end FinitePR.SamplerIntegral
