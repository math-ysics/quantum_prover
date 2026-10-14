import QuantumProver.QuantumChannels.NuclearTraceDuality
import QuantumProver.QuantumChannels.NuclearCoarseTestIntegral
import QuantumProver.QuantumChannels.NuclearProductMeasureExt

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory ProbabilityTheory Set InnerProductSpace
open scoped BigOperators Topology InnerProduct

namespace QuantumProver.MatrixNuclearKernelTransport

open QuantumProver.NuclearOperator QuantumProver.HilbertNuclearCompression
open QuantumProver.MatrixNuclearInstrumentTestIntegral
open QuantumProver.MatrixNuclearTraceDuality
open QuantumProver.MatrixNuclearCoarseTestIntegral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance nuclearNormedGroup : NormedAddCommGroup (Nuclear ℂ E E) := inferInstance
local instance nuclearNormedSpace : NormedSpace ℂ (Nuclear ℂ E E) := inferInstance

theorem tracePair_rankOne_test (x y : E) (T : Nuclear ℂ E E) :
    tracePair ((innerSL ℂ x).smulRight y) T = inner ℂ x (toOperator T y) := by
  have he : compose ((innerSL ℂ x).smulRight y) (ContinuousLinearMap.id ℂ E) T =
      rankOne ((innerSL ℂ x).comp (toOperator T)) y := by
    apply toOperator_injective
    ext z
    simp only [toOperator_compose, toOperator_rankOne,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply]
  change QuantumProver.HilbertNuclearTrace.trace
    (compose ((innerSL ℂ x).smulRight y) (ContinuousLinearMap.id ℂ E) T) = _
  rw [he, QuantumProver.HilbertNuclearTrace.trace_rankOne]
  rfl

theorem nuclear_eq_of_tracePair_eq {T S : Nuclear ℂ E E}
    (h : ∀ W : E →L[ℂ] E, tracePair W T = tracePair W S) : T = S := by
  apply toOperator_injective
  ext y
  apply ext_inner_left ℂ
  intro x
  simpa only [tracePair_rankOne_test] using h ((innerSL ℂ x).smulRight y)

section RawEvent

variable {A B R : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace R]

theorem norm_event_operation_le_one
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E B R)
    (b : B) (t : Set R) (ht : MeasurableSet t) : ‖P.operation b t‖ ≤ 1 := by
  apply (P.operation b t).opNorm_le_bound zero_le_one
  intro T
  simpa only [one_mul] using
    QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.normalOperation_norm_le_of_cp_trace_nonincreasing
      (P.operation b t) (P.completelyPositive b t ht)
      (QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.Instrument.traceNonincreasing P b t ht) T

theorem integrable_event_operation_field [TopologicalSpace.SeparableSpace E]
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E B R)
    {μ : Measure A} {c : A → B} (hc : Measurable c)
    (t : Set R) (ht : MeasurableSet t)
    {f : A → Nuclear ℂ E E} (hf : Integrable f μ) :
    Integrable (fun a => P.operation (c a) t (f a)) μ := by
  have hsm : StronglyMeasurable (fun a => P.operation (c a) t
      (hf.aestronglyMeasurable.mk f a)) :=
    QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.stronglyMeasurable_variable_apply
      (fun a => P.operation (c a) t)
      (fun T =>
        (QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument.stronglyMeasurable_operation
          P t ht T).comp_measurable hc)
      (hf.aestronglyMeasurable.mk f) hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hae : AEStronglyMeasurable (fun a => P.operation (c a) t (f a)) μ :=
    hsm.aestronglyMeasurable.congr (by
      filter_upwards [hf.aestronglyMeasurable.ae_eq_mk] with a ha
      rw [ha])
  apply hf.norm.mono' hae
  exact ae_of_all _ fun a =>
    ((P.operation (c a) t).le_opNorm (f a)).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (norm_event_operation_le_one P (c a) t ht) (norm_nonneg (f a)))

theorem setIntegral_event_operation_eq_of_preimage_setIntegral_eq
    [TopologicalSpace.SeparableSpace E]
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E B R)
    {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c : A → B} (hc : Measurable c)
    {f : A → Nuclear ℂ E E} {g : B → Nuclear ℂ E E}
    (hf : Integrable f μ) (hg : Integrable g ν)
    (hset : ∀ s : Set B, MeasurableSet s →
      (∫ a in c ⁻¹' s, f a ∂μ) = ∫ b in s, g b ∂ν)
    (s : Set B) (hs : MeasurableSet s) (t : Set R) (ht : MeasurableSet t) :
    (∫ a in c ⁻¹' s, P.operation (c a) t (f a) ∂μ) =
      ∫ b in s, P.operation b t (g b) ∂ν := by
  have hfi := integrable_event_operation_field P hc t ht hf
  have hgi : Integrable (fun b => P.operation b t (g b)) ν := by
    simpa only [id_eq] using integrable_event_operation_field P measurable_id t ht hg
  apply nuclear_eq_of_tracePair_eq
  intro W
  let V : B → E →L[ℂ] E := s.indicator (fun b => pullback (P.operation b t) W)
  have hweak (x y : E) : Measurable (fun b => inner ℂ x (V b y)) := by
    have heq : (fun b => inner ℂ x (V b y)) =
        s.indicator (fun b => inner ℂ x (pullback (P.operation b t) W y)) := by
      funext b
      by_cases hb : b ∈ s <;> simp [V, hb]
    rw [heq]
    exact (measurable_inner_pullback_of_strong (fun b => P.operation b t)
      (fun T => QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument.stronglyMeasurable_operation
        P t ht T) (fun _ => W) (fun _ _ => measurable_const) x y).indicator hs
  have hbound (b : B) : ‖V b‖ ≤ ‖W‖ := by
    by_cases hb : b ∈ s
    · simpa only [V, indicator_of_mem hb, one_mul] using
        (norm_pullback_le (P.operation b t) W).trans
          (mul_le_mul_of_nonneg_right (norm_event_operation_le_one P b t ht)
            (norm_nonneg W))
    · simp [V, hb]
  obtain ⟨_, _, heq⟩ :=
    integrable_tests_and_integral_tracePair_eq_of_preimage_setIntegral_eq hc hf hg hset
      V hweak (norm_nonneg W) hbound
  have hleft : (fun a => tracePair (V (c a)) (f a)) =
      (c ⁻¹' s).indicator (fun a => tracePair W (P.operation (c a) t (f a))) := by
    funext a
    by_cases ha : c a ∈ s <;> simp [V, ha, tracePair_pullback]
  have hright : (fun b => tracePair (V b) (g b)) =
      s.indicator (fun b => tracePair W (P.operation b t (g b))) := by
    funext b
    by_cases hb : b ∈ s <;> simp [V, hb, tracePair_pullback]
  rw [hleft, hright, integral_indicator (hc hs), integral_indicator hs] at heq
  change tracePairCLM W (∫ a in c ⁻¹' s, P.operation (c a) t (f a) ∂μ) =
    tracePairCLM W (∫ b in s, P.operation b t (g b) ∂ν)
  rw [← (tracePairCLM W).integral_comp_comm hfi.integrableOn,
    ← (tracePairCLM W).integral_comp_comm hgi.integrableOn]
  exact heq

end RawEvent

section KernelStep

variable {A B Q R : Type*}
  [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Q] [MeasurableSpace R]

theorem measurable_productMap {c : A → B} {d : Q → R}
    (hc : Measurable c) (hd : Measurable d) : Measurable (Prod.map c d) := hc.prodMap hd

omit [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Q] [MeasurableSpace R] in
theorem productMap_preimage_prod (c : A → B) (d : Q → R) (s : Set B) (t : Set R) :
    Prod.map c d ⁻¹' (s ×ˢ t) = (c ⁻¹' s) ×ˢ (d ⁻¹' t) := by
  ext p
  rfl

theorem setIntegral_kernel_rectangle_transport [TopologicalSpace.SeparableSpace E]
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E B R)
    {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c : A → B} {d : Q → R} (hc : Measurable c) (hd : Measurable d)
    {f : A → Nuclear ℂ E E} {g : B → Nuclear ℂ E E}
    (hf : Integrable f μ) (hg : Integrable g ν)
    (hset : ∀ s : Set B, MeasurableSet s →
      (∫ a in c ⁻¹' s, f a ∂μ) = ∫ b in s, g b ∂ν)
    (κ : Kernel A Q) (η : Kernel B R) [IsMarkovKernel κ] [IsMarkovKernel η]
    {F : A × Q → Nuclear ℂ E E} {G : B × R → Nuclear ℂ E E}
    (hF : Integrable F (μ.compProd κ)) (hG : Integrable G (ν.compProd η))
    (hFlocal : ∀ a (t : Set R), MeasurableSet t →
      (∫ q in d ⁻¹' t, F (a, q) ∂κ a) = P.operation (c a) t (f a))
    (hGlocal : ∀ b (t : Set R), MeasurableSet t →
      (∫ r in t, G (b, r) ∂η b) = P.operation b t (g b))
    (s : Set B) (hs : MeasurableSet s) (t : Set R) (ht : MeasurableSet t) :
    (∫ p in Prod.map c d ⁻¹' (s ×ˢ t), F p ∂μ.compProd κ) =
      ∫ p in s ×ˢ t, G p ∂ν.compProd η := by
  rw [productMap_preimage_prod,
    Measure.setIntegral_compProd (hc hs) (hd ht) hF.integrableOn,
    Measure.setIntegral_compProd hs ht hG.integrableOn]
  have hleft : (fun a => ∫ q in d ⁻¹' t, F (a, q) ∂κ a) =
      fun a => P.operation (c a) t (f a) := funext fun a => hFlocal a t ht
  have hright : (fun b => ∫ r in t, G (b, r) ∂η b) =
      fun b => P.operation b t (g b) := funext fun b => hGlocal b t ht
  rw [hleft, hright]
  exact setIntegral_event_operation_eq_of_preimage_setIntegral_eq P hc hf hg hset s hs t ht

theorem setIntegral_kernel_transport [TopologicalSpace.SeparableSpace E]
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument E E B R)
    {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c : A → B} {d : Q → R} (hc : Measurable c) (hd : Measurable d)
    {f : A → Nuclear ℂ E E} {g : B → Nuclear ℂ E E}
    (hf : Integrable f μ) (hg : Integrable g ν)
    (hset : ∀ s : Set B, MeasurableSet s →
      (∫ a in c ⁻¹' s, f a ∂μ) = ∫ b in s, g b ∂ν)
    (κ : Kernel A Q) (η : Kernel B R) [IsMarkovKernel κ] [IsMarkovKernel η]
    {F : A × Q → Nuclear ℂ E E} {G : B × R → Nuclear ℂ E E}
    (hF : Integrable F (μ.compProd κ)) (hG : Integrable G (ν.compProd η))
    (hFlocal : ∀ a (t : Set R), MeasurableSet t →
      (∫ q in d ⁻¹' t, F (a, q) ∂κ a) = P.operation (c a) t (f a))
    (hGlocal : ∀ b (t : Set R), MeasurableSet t →
      (∫ r in t, G (b, r) ∂η b) = P.operation b t (g b)) :
    ∀ (S : Set (B × R)), MeasurableSet S →
      (∫ p in Prod.map c d ⁻¹' S, F p ∂μ.compProd κ) =
        ∫ p in S, G p ∂ν.compProd η := by
  apply QuantumProver.ElegantJointMeasurement.NuclearProductMeasureExt.setIntegral_preimage_eq_of_rectangles
    (hc.prodMap hd) hF hG
  intro s t hs ht
  exact setIntegral_kernel_rectangle_transport P hc hd hf hg hset κ η hF hG
    hFlocal hGlocal s hs t ht

end KernelStep

end QuantumProver.MatrixNuclearKernelTransport
