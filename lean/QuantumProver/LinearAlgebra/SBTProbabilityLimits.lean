import QuantumProver.LinearAlgebra.SBTProbabilityWeight
import QuantumProver.InformationTheory.ConditionalEntropy.ProbabilityMixtures

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace QuantumProver.SBTProbabilityLimits

open QuantumProver.ConditionalEntropy

variable {I κ Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]

theorem aestronglyMeasurable_limit_of_eventually
    (μ : Measure Ω) (ℓ : Filter κ) [NeBot ℓ] [ℓ.IsCountablyGenerated]
    {F : κ → Ω → Matrix I I ℂ} {G : Ω → Matrix I I ℂ}
    (hF : ∀ᶠ δ in ℓ, AEStronglyMeasurable (F δ) μ)
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun δ => F δ t) ℓ (𝓝 (G t))) :
    AEStronglyMeasurable G μ := by
  classical
  let H : κ → Ω → Matrix I I ℂ := fun δ t =>
    if AEStronglyMeasurable (F δ) μ then F δ t else 0
  have hH : ∀ δ, AEStronglyMeasurable (H δ) μ := by
    intro δ
    by_cases hδ : AEStronglyMeasurable (F δ) μ
    · simpa only [H, ite_eq_left hδ] using hδ
    · simpa only [H, ite_eq_right hδ] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω => (0 : Matrix I I ℂ)) μ)
  apply aestronglyMeasurable_of_tendsto_ae ℓ hH
  filter_upwards [hlim] with t ht
  apply ht.congr'
  filter_upwards [hF] with δ hδ
  simp only [H, ite_eq_left hδ]

theorem ae_isDensity_limit (μ : Measure Ω) (ℓ : Filter κ) [NeBot ℓ]
    {F : κ → Ω → Matrix I I ℂ} {G : Ω → Matrix I I ℂ}
    (hF : ∀ᶠ δ in ℓ, ∀ t, IsDensity (F δ t))
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun δ => F δ t) ℓ (𝓝 (G t))) :
    ∀ᵐ t ∂μ, IsDensity (G t) := by
  filter_upwards [hlim] with t ht
  exact ProbabilityMixtures.isClosed_isDensity.mem_of_tendsto ht
    (hF.mono (fun _ hδ => hδ t))

theorem integrable_limit_densityFamily
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℓ : Filter κ) [NeBot ℓ] [ℓ.IsCountablyGenerated]
    {F : κ → Ω → Matrix I I ℂ} {G : Ω → Matrix I I ℂ}
    (hF : ∀ᶠ δ in ℓ, AEStronglyMeasurable (F δ) μ ∧ ∀ t, IsDensity (F δ t))
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun δ => F δ t) ℓ (𝓝 (G t))) :
    Integrable G μ :=
  ProbabilityMixtures.integrable_densityFamily μ G
    (aestronglyMeasurable_limit_of_eventually μ ℓ (hF.mono fun _ h => h.1) hlim)
    (ae_isDensity_limit μ ℓ (hF.mono fun _ h => h.2) hlim)

theorem tendsto_integral_densityFamily
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℓ : Filter κ) [ℓ.IsCountablyGenerated]
    {F : κ → Ω → Matrix I I ℂ} {G : Ω → Matrix I I ℂ}
    (hF : ∀ᶠ δ in ℓ, AEStronglyMeasurable (F δ) μ ∧ ∀ t, IsDensity (F δ t))
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun δ => F δ t) ℓ (𝓝 (G t))) :
    Tendsto (fun δ => ∫ t, F δ t ∂μ) ℓ (𝓝 (∫ t, G t ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
  · exact hF.mono fun _ h => h.1
  · exact hF.mono fun _ h => Eventually.of_forall fun t =>
      ProbabilityMixtures.isDensity_norm_le_one (h.2 t)
  · exact integrable_const (1 : ℝ)
  · exact hlim

theorem integral_limit_isDensity
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℓ : Filter κ) [NeBot ℓ] [ℓ.IsCountablyGenerated]
    {F : κ → Ω → Matrix I I ℂ} {G : Ω → Matrix I I ℂ}
    (hF : ∀ᶠ δ in ℓ, AEStronglyMeasurable (F δ) μ ∧ ∀ t, IsDensity (F δ t))
    (hlim : ∀ᵐ t ∂μ, Tendsto (fun δ => F δ t) ℓ (𝓝 (G t))) :
    IsDensity (∫ t, G t ∂μ) :=
  ProbabilityMixtures.integral_isDensity μ G
    (aestronglyMeasurable_limit_of_eventually μ ℓ (hF.mono fun _ h => h.1) hlim)
    (ae_isDensity_limit μ ℓ (hF.mono fun _ h => h.2) hlim)

section Beta

open SBTProbabilityWeight

theorem tendsto_beta0Probability_integral_density_at_zero
    {F : ℝ → ℝ → Matrix I I ℂ} {G : ℝ → Matrix I I ℂ}
    (hMeas : ∀ δ : ℝ, 0 < δ → AEStronglyMeasurable (F δ) beta0Probability)
    (hDensity : ∀ δ : ℝ, 0 < δ → ∀ t, IsDensity (F δ t))
    (hlim : ∀ᵐ t ∂beta0Probability,
      Tendsto (fun δ : ℝ => F δ t) (𝓝[>] 0) (𝓝 (G t))) :
    Tendsto (fun δ : ℝ => ∫ t : ℝ, F δ t ∂beta0Probability) (𝓝[>] 0)
      (𝓝 (∫ t : ℝ, G t ∂beta0Probability)) := by
  apply tendsto_integral_densityFamily beta0Probability (𝓝[>] (0 : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ⟨hMeas δ hδ, hDensity δ hδ⟩
  · exact hlim

theorem beta0Probability_density_limit_properties
    {F : ℝ → ℝ → Matrix I I ℂ} {G : ℝ → Matrix I I ℂ}
    (hMeas : ∀ δ : ℝ, 0 < δ → AEStronglyMeasurable (F δ) beta0Probability)
    (hDensity : ∀ δ : ℝ, 0 < δ → ∀ t, IsDensity (F δ t))
    (hlim : ∀ᵐ t ∂beta0Probability,
      Tendsto (fun δ : ℝ => F δ t) (𝓝[>] 0) (𝓝 (G t))) :
    AEStronglyMeasurable G beta0Probability ∧
      (∀ᵐ t ∂beta0Probability, IsDensity (G t)) ∧
      Integrable G beta0Probability ∧ IsDensity (∫ t : ℝ, G t ∂beta0Probability) := by
  have hF : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (F δ) beta0Probability ∧ ∀ t, IsDensity (F δ t) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ⟨hMeas δ hδ, hDensity δ hδ⟩
  exact ⟨aestronglyMeasurable_limit_of_eventually beta0Probability _ (hF.mono fun _ h => h.1) hlim,
    ae_isDensity_limit beta0Probability _ (hF.mono fun _ h => h.2) hlim,
    integrable_limit_densityFamily beta0Probability _ hF hlim,
    integral_limit_isDensity beta0Probability _ hF hlim⟩

theorem tendsto_integral_beta0_smul_density_at_zero
    {F : ℝ → ℝ → Matrix I I ℂ} {G : ℝ → Matrix I I ℂ}
    (hMeas : ∀ δ : ℝ, 0 < δ → AEStronglyMeasurable (F δ) beta0Probability)
    (hDensity : ∀ δ : ℝ, 0 < δ → ∀ t, IsDensity (F δ t))
    (hlim : ∀ᵐ t ∂beta0Probability,
      Tendsto (fun δ : ℝ => F δ t) (𝓝[>] 0) (𝓝 (G t))) :
    Tendsto (fun δ : ℝ => ∫ t : ℝ, beta0 t • F δ t ∂volume) (𝓝[>] 0)
      (𝓝 (∫ t : ℝ, beta0 t • G t ∂volume)) := by
  simpa only [integral_beta0Probability] using
    tendsto_beta0Probability_integral_density_at_zero hMeas hDensity hlim

theorem integrable_limit_beta0_smul_density
    {F : ℝ → ℝ → Matrix I I ℂ} {G : ℝ → Matrix I I ℂ}
    (hMeas : ∀ δ : ℝ, 0 < δ → AEStronglyMeasurable (F δ) beta0Probability)
    (hDensity : ∀ δ : ℝ, 0 < δ → ∀ t, IsDensity (F δ t))
    (hlim : ∀ᵐ t ∂beta0Probability,
      Tendsto (fun δ : ℝ => F δ t) (𝓝[>] 0) (𝓝 (G t))) :
    Integrable (fun t : ℝ => beta0 t • G t) volume :=
  (integrable_beta0Probability_iff G).mp
    (beta0Probability_density_limit_properties hMeas hDensity hlim).2.2.1

theorem tendsto_beta0Probability_integral_density_of_continuous
    {F : ℝ → ℝ → Matrix I I ℂ} {G : ℝ → Matrix I I ℂ}
    (hContinuous : ∀ δ : ℝ, 0 < δ → Continuous (F δ))
    (hDensity : ∀ δ : ℝ, 0 < δ → ∀ t, IsDensity (F δ t))
    (hlim : ∀ᵐ t ∂beta0Probability,
      Tendsto (fun δ : ℝ => F δ t) (𝓝[>] 0) (𝓝 (G t))) :
    Tendsto (fun δ : ℝ => ∫ t : ℝ, F δ t ∂beta0Probability) (𝓝[>] 0)
      (𝓝 (∫ t : ℝ, G t ∂beta0Probability)) :=
  tendsto_beta0Probability_integral_density_at_zero
    (fun δ hδ => (hContinuous δ hδ).aestronglyMeasurable) hDensity hlim

end Beta
end QuantumProver.SBTProbabilityLimits
