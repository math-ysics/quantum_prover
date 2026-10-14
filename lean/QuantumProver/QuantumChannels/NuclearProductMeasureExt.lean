import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.MeasurableSpace.Prod

noncomputable section
set_option autoImplicit false

open MeasureTheory Set

namespace QuantumProver.ElegantJointMeasurement.NuclearProductMeasureExt

variable {X B R V : Type*}
  [MeasurableSpace X] [MeasurableSpace B] [MeasurableSpace R]
  [NormedAddCommGroup V]

theorem vectorMeasure_eq_of_rectangles
    {σ τ : VectorMeasure (B × R) V}
    (hrect : ∀ (s : Set B) (t : Set R), MeasurableSet s → MeasurableSet t →
      σ (s ×ˢ t) = τ (s ×ˢ t)) : σ = τ := by
  refine VectorMeasure.ext_of_generateFrom
    (image2 (· ×ˢ ·) {s : Set B | MeasurableSet s} {t : Set R | MeasurableSet t})
    ?_ generateFrom_prod.symm isPiSystem_prod ?_
  · rintro _ ⟨s, hs, t, ht, rfl⟩
    exact hrect s t hs ht
  · simpa only [univ_prod_univ] using
      hrect univ univ MeasurableSet.univ MeasurableSet.univ

variable [NormedSpace ℝ V]

theorem map_withDensity_eq_of_rectangles [CompleteSpace V]
    {μ : Measure X} {ν : Measure (B × R)}
    {e : X → B × R} {u : X → V} {v : B × R → V}
    (he : Measurable e) (hu : Integrable u μ) (hv : Integrable v ν)
    (hrect : ∀ (s : Set B) (t : Set R), MeasurableSet s → MeasurableSet t →
      (∫ x in e ⁻¹' (s ×ˢ t), u x ∂μ) = ∫ y in s ×ˢ t, v y ∂ν) :
    (μ.withDensityᵥ u).map e = ν.withDensityᵥ v := by
  apply vectorMeasure_eq_of_rectangles
  intro s t hs ht
  rw [VectorMeasure.map_apply _ he (hs.prod ht),
    withDensityᵥ_apply hu (he (hs.prod ht)), withDensityᵥ_apply hv (hs.prod ht)]
  exact hrect s t hs ht

theorem setIntegral_preimage_eq_of_rectangles [CompleteSpace V]
    {μ : Measure X} {ν : Measure (B × R)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {e : X → B × R} {u : X → V} {v : B × R → V}
    (he : Measurable e) (hu : Integrable u μ) (hv : Integrable v ν)
    (hrect : ∀ (s : Set B) (t : Set R), MeasurableSet s → MeasurableSet t →
      (∫ x in e ⁻¹' (s ×ˢ t), u x ∂μ) = ∫ y in s ×ˢ t, v y ∂ν) :
    ∀ (S : Set (B × R)), MeasurableSet S →
      (∫ x in e ⁻¹' S, u x ∂μ) = ∫ y in S, v y ∂ν := by
  intro S hS
  have hmeasure := map_withDensity_eq_of_rectangles he hu hv hrect
  have hSmeasure := congrArg (fun m : VectorMeasure (B × R) V => m S) hmeasure
  simpa only [VectorMeasure.map_apply _ he hS,
    withDensityᵥ_apply hu (he hS), withDensityᵥ_apply hv hS] using hSmeasure

end QuantumProver.ElegantJointMeasurement.NuclearProductMeasureExt
