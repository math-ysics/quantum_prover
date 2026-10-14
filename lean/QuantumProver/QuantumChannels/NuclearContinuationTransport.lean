import QuantumProver.QuantumChannels.NuclearKernelTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Set InnerProductSpace
open scoped BigOperators Topology InnerProduct

namespace QuantumProver.MatrixNuclearContinuationTransport

open QuantumProver.NuclearOperator QuantumProver.HilbertNuclearCompression
open QuantumProver.MatrixNuclearInstrumentTestIntegral
open QuantumProver.MatrixNuclearTraceDuality
open QuantumProver.MatrixNuclearCoarseTestIntegral
open QuantumProver.MatrixNuclearKernelTransport

variable {E F A B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [MeasurableSpace A] [MeasurableSpace B]

local instance inputNuclearNormedGroup : NormedAddCommGroup (Nuclear ℂ E E) := inferInstance
local instance inputNuclearNormedSpace : NormedSpace ℂ (Nuclear ℂ E E) := inferInstance
local instance outputNuclearNormedGroup : NormedAddCommGroup (Nuclear ℂ F F) := inferInstance
local instance outputNuclearNormedSpace : NormedSpace ℂ (Nuclear ℂ F F) := inferInstance

theorem aestronglyMeasurable_continuation_field
    {μ : Measure A} {c : A → B} (hc : Measurable c)
    {f : A → Nuclear ℂ E E} (hf : AEStronglyMeasurable f μ)
    (Ψ : B → Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (hΨ : ∀ T, StronglyMeasurable (fun b => Ψ b T)) :
    AEStronglyMeasurable (fun a => Ψ (c a) (f a)) μ := by
  have hs : StronglyMeasurable (fun a => Ψ (c a) (hf.mk f a)) :=
    QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.stronglyMeasurable_variable_apply
      (fun a => Ψ (c a)) (fun T => (hΨ T).comp_measurable hc)
      (hf.mk f) hf.stronglyMeasurable_mk
  exact hs.aestronglyMeasurable.congr (by
    filter_upwards [hf.ae_eq_mk] with a ha
    rw [ha])

theorem integrable_continuation_field
    {μ : Measure A} {c : A → B} (hc : Measurable c)
    {f : A → Nuclear ℂ E E} (hf : Integrable f μ)
    (Ψ : B → Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (hΨ : ∀ T, StronglyMeasurable (fun b => Ψ b T))
    {C : ℝ} (hbound : ∀ b, ‖Ψ b‖ ≤ C) :
    Integrable (fun a => Ψ (c a) (f a)) μ := by
  apply (hf.norm.const_mul C).mono'
    (aestronglyMeasurable_continuation_field hc hf.aestronglyMeasurable Ψ hΨ)
  exact ae_of_all _ fun a =>
    ((Ψ (c a)).le_opNorm (f a)).trans
      (mul_le_mul_of_nonneg_right (hbound (c a)) (norm_nonneg (f a)))

theorem integral_continuation_eq_of_preimage_setIntegral_eq
    {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c : A → B} (hc : Measurable c)
    {f : A → Nuclear ℂ E E} {g : B → Nuclear ℂ E E}
    (hf : Integrable f μ) (hg : Integrable g ν)
    (hset : ∀ s : Set B, MeasurableSet s →
      (∫ a in c ⁻¹' s, f a ∂μ) = ∫ b in s, g b ∂ν)
    (Ψ : B → Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (hΨ : ∀ T, StronglyMeasurable (fun b => Ψ b T))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ b, ‖Ψ b‖ ≤ C) :
    (∫ a, Ψ (c a) (f a) ∂μ) = ∫ b, Ψ b (g b) ∂ν := by
  have hfi := integrable_continuation_field hc hf Ψ hΨ hbound
  have hgi : Integrable (fun b => Ψ b (g b)) ν := by
    simpa only [id_eq] using
      integrable_continuation_field measurable_id hg Ψ hΨ hbound
  apply nuclear_eq_of_tracePair_eq
  intro W
  have hweak (x y : E) : Measurable
      (fun b => inner ℂ x (pullback (Ψ b) W y)) :=
    measurable_inner_pullback_of_strong Ψ hΨ (fun _ => W)
      (fun _ _ => measurable_const) x y
  have htestbound (b : B) : ‖pullback (Ψ b) W‖ ≤ C * ‖W‖ :=
    (norm_pullback_le (Ψ b) W).trans
      (mul_le_mul_of_nonneg_right (hbound b) (norm_nonneg W))
  obtain ⟨_, _, heq⟩ :=
    integrable_tests_and_integral_tracePair_eq_of_preimage_setIntegral_eq hc hf hg hset
      (fun b => pullback (Ψ b) W) hweak (mul_nonneg hC (norm_nonneg W)) htestbound
  simp_rw [tracePair_pullback] at heq
  change tracePairCLM W (∫ a, Ψ (c a) (f a) ∂μ) =
    tracePairCLM W (∫ b, Ψ b (g b) ∂ν)
  rw [← (tracePairCLM W).integral_comp_comm hfi,
    ← (tracePairCLM W).integral_comp_comm hgi]
  exact heq

theorem integrable_continuations_and_integral_eq_of_preimage_setIntegral_eq
    {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c : A → B} (hc : Measurable c)
    {f : A → Nuclear ℂ E E} {g : B → Nuclear ℂ E E}
    (hf : Integrable f μ) (hg : Integrable g ν)
    (hset : ∀ s : Set B, MeasurableSet s →
      (∫ a in c ⁻¹' s, f a ∂μ) = ∫ b in s, g b ∂ν)
    (Ψ : B → Nuclear ℂ E E →L[ℂ] Nuclear ℂ F F)
    (hΨ : ∀ T, StronglyMeasurable (fun b => Ψ b T))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ b, ‖Ψ b‖ ≤ C) :
    Integrable (fun a => Ψ (c a) (f a)) μ ∧
      Integrable (fun b => Ψ b (g b)) ν ∧
      ((∫ a, Ψ (c a) (f a) ∂μ) = ∫ b, Ψ b (g b) ∂ν) := by
  refine ⟨integrable_continuation_field hc hf Ψ hΨ hbound, ?_, ?_⟩
  · simpa only [id_eq] using
      integrable_continuation_field measurable_id hg Ψ hΨ hbound
  · exact integral_continuation_eq_of_preimage_setIntegral_eq hc hf hg hset Ψ hΨ hC hbound

end QuantumProver.MatrixNuclearContinuationTransport
