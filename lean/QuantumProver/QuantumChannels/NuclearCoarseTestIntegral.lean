import Mathlib
import QuantumProver.QuantumChannels.NuclearInstrumentTestIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter Set InnerProductSpace
open scoped BigOperators Topology InnerProduct

namespace QuantumProver.MatrixNuclearCoarseTestIntegral

open QuantumProver.NuclearOperator QuantumProver.HilbertNuclearCompression
open QuantumProver.MatrixNuclearInstrumentTestIntegral

variable {E A B : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [MeasurableSpace A] [MeasurableSpace B]

local instance nuclearNormedGroup : NormedAddCommGroup (Nuclear ℂ E E) := inferInstance
local instance nuclearNormedSpace : NormedSpace ℂ (Nuclear ℂ E E) := inferInstance

@[simp] theorem tracePair_zero_left (T : Nuclear ℂ E E) :
    tracePair (0 : E →L[ℂ] E) T = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using norm_tracePair_le (0 : E →L[ℂ] E) T)
    (norm_nonneg _)

theorem tracePair_add_left (V W : E →L[ℂ] E) (T : Nuclear ℂ E E) :
    tracePair (V + W) T = tracePair V T + tracePair W T := by
  have h : compose (V + W) (ContinuousLinearMap.id ℂ E) T =
      compose V (ContinuousLinearMap.id ℂ E) T +
        compose W (ContinuousLinearMap.id ℂ E) T := by
    apply toOperator_injective
    simp only [toOperator_compose, map_add]
    ext x
    simp
  change QuantumProver.HilbertNuclearTrace.trace
    (compose (V + W) (ContinuousLinearMap.id ℂ E) T) = _
  rw [h, map_add]
  rfl

omit [CompleteSpace E] in
theorem measurable_simple_weak_coordinates (W : SimpleFunc B (E →L[ℂ] E)) :
    ∀ x y : E, Measurable (fun b => inner ℂ x (W b y)) := by
  intro x y
  exact (W.map (fun V => inner ℂ x (V y))).measurable

theorem integrable_simple_tracePair {ν : Measure B}
    {g : B → Nuclear ℂ E E} (hg : Integrable g ν)
    (W : SimpleFunc B (E →L[ℂ] E)) :
    Integrable (fun b => tracePair (W b) (g b)) ν := by
  classical
  apply integrable_tracePair W (measurable_simple_weak_coordinates W)
    (C := ∑ V ∈ W.range, ‖V‖) ?_ hg
  intro b
  exact Finset.single_le_sum (fun V _ => norm_nonneg V) (W.mem_range_self b)

theorem integral_simple_tracePair_eq_of_preimage_setIntegral_eq
    {μ : Measure A} {ν : Measure B} {c : A → B} (hc : Measurable c)
    {f : A → Nuclear ℂ E E} {g : B → Nuclear ℂ E E}
    (hf : Integrable f μ) (hg : Integrable g ν)
    (hset : ∀ s : Set B, MeasurableSet s →
      (∫ a in c ⁻¹' s, f a ∂μ) = ∫ b in s, g b ∂ν)
    (W : SimpleFunc B (E →L[ℂ] E)) :
    (∫ a, tracePair (W (c a)) (f a) ∂μ) =
      ∫ b, tracePair (W b) (g b) ∂ν := by
  classical
  apply SimpleFunc.induction (motive := fun W : SimpleFunc B (E →L[ℂ] E) =>
    (∫ a, tracePair (W (c a)) (f a) ∂μ) =
      ∫ b, tracePair (W b) (g b) ∂ν) ?_ ?_ W
  · intro V s hs
    have hleft : (fun a => tracePair
        ((SimpleFunc.piecewise s hs (SimpleFunc.const B V)
          (SimpleFunc.const B 0)) (c a)) (f a)) =
        (c ⁻¹' s).indicator (fun a => tracePair V (f a)) := by
      funext a
      by_cases ha : c a ∈ s <;> simp [ha]
    have hright : (fun b => tracePair
        ((SimpleFunc.piecewise s hs (SimpleFunc.const B V)
          (SimpleFunc.const B 0)) b) (g b)) =
        s.indicator (fun b => tracePair V (g b)) := by
      funext b
      by_cases hb : b ∈ s <;> simp [hb]
    rw [hleft, hright, integral_indicator (hc hs), integral_indicator hs]
    change (∫ a in c ⁻¹' s, tracePairCLM V (f a) ∂μ) =
      ∫ b in s, tracePairCLM V (g b) ∂ν
    rw [(tracePairCLM V).integral_comp_comm hf.integrableOn,
      (tracePairCLM V).integral_comp_comm hg.integrableOn, hset s hs]
  · intro U V _ hU hV
    have hUμ : Integrable (fun a => tracePair (U (c a)) (f a)) μ := by
      simpa only [SimpleFunc.coe_comp, Function.comp_apply] using
        integrable_simple_tracePair hf (U.comp c hc)
    have hVμ : Integrable (fun a => tracePair (V (c a)) (f a)) μ := by
      simpa only [SimpleFunc.coe_comp, Function.comp_apply] using
        integrable_simple_tracePair hf (V.comp c hc)
    simp only [SimpleFunc.coe_add, Pi.add_apply, tracePair_add_left]
    rw [integral_add hUμ hVμ,
      integral_add (integrable_simple_tracePair hg U) (integrable_simple_tracePair hg V),
      hU, hV]

theorem equicontinuous_tracePair_of_bound {ι : Type*} (W : ι → E →L[ℂ] E)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ i, ‖W i‖ ≤ C) :
    Equicontinuous (fun i (T : Nuclear ℂ E E) => tracePair (W i) T) := by
  apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => C * r)
    (by simpa using (tendsto_const_nhds.mul (tendsto_id :
      Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0))))
  intro T S i
  have hop : ‖tracePairCLM (W i)‖ ≤ C :=
    (tracePairCLM (W i)).opNorm_le_bound hC fun X =>
      (norm_tracePair_le _ _).trans
        (mul_le_mul_of_nonneg_right (hbound i) (norm_nonneg X))
  exact ((tracePairCLM (W i)).dist_le_opNorm T S).trans
    (mul_le_mul_of_nonneg_right hop (dist_nonneg : 0 ≤ dist T S))

theorem exists_bounded_simple_tests_on_separable_set
    (W : B → E →L[ℂ] E)
    (hW : ∀ x y : E, Measurable (fun b => inner ℂ x (W b y)))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ b, ‖W b‖ ≤ C)
    (s : Set (Nuclear ℂ E E)) (hs : TopologicalSpace.IsSeparable s) :
    ∃ Q : ℕ → SimpleFunc B (E →L[ℂ] E),
      (∀ n b, ‖Q n b‖ ≤ C) ∧
      ∀ b T, T ∈ s → Tendsto (fun n => tracePair (Q n b) T)
        atTop (𝓝 (tracePair (W b) T)) := by
  classical
  obtain ⟨t, hts, htc, hst⟩ := hs.exists_countable_dense_subset
  have : Countable t := htc.to_subtype
  letI : PseudoMetricSpace (t → ℂ) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric (t → ℂ)
  let φ : B → t → ℂ := fun b T => tracePair (W b) T.1
  have hφ : Measurable φ :=
    measurable_pi_iff.mpr fun T => measurable_tracePair_fixed W hW T.1
  let r : Set (t → ℂ) := Set.range φ ∪ {0}
  have h0 : (0 : t → ℂ) ∈ r := by simp [r]
  let R : (t → ℂ) → (E →L[ℂ] E) := fun v =>
    if h : v ∈ Set.range φ then W h.choose else 0
  have hRbound (v : t → ℂ) : ‖R v‖ ≤ C := by
    dsimp only [R]
    split_ifs with hv
    · exact hbound _
    · simpa using hC
  have hRcoord (v : t → ℂ) (hv : v ∈ r) (T : t) :
      tracePair (R v) T.1 = v T := by
    dsimp only [R]
    split_ifs with hr
    · exact congrFun hr.choose_spec T
    · have hz : v = 0 := by
        rcases hv with hv | hv
        · exact (hr hv).elim
        · exact hv
      simp [hz]
  let P : ℕ → SimpleFunc B (t → ℂ) :=
    SimpleFunc.approxOn φ hφ r 0 h0
  let Q : ℕ → SimpleFunc B (E →L[ℂ] E) := fun n => (P n).map R
  refine ⟨Q, fun n b => hRbound _, ?_⟩
  intro b T hT
  have hcoord (S : t) : Tendsto (fun n => tracePair (Q n b) S.1)
      atTop (𝓝 (tracePair (W b) S.1)) := by
    have hP : Tendsto (fun n => P n b) atTop (𝓝 (φ b)) :=
      SimpleFunc.tendsto_approxOn hφ h0
        (subset_closure (Or.inl (mem_range_self b)))
    have heval := (continuous_apply S).continuousAt.tendsto.comp hP
    convert heval using 1
    funext n
    exact hRcoord (P n b) (SimpleFunc.approxOn_mem hφ h0 n b) S
  have hclosed : IsClosed {X : Nuclear ℂ E E |
      Tendsto (fun n => tracePair (Q n b) X) atTop (𝓝 (tracePair (W b) X))} :=
    (equicontinuous_tracePair_of_bound (fun n => Q n b) hC
      (fun n => hRbound _)).isClosed_setOfPred_tendsto (tracePairCLM (W b)).continuous
  apply closure_minimal (s := t) (t := {X : Nuclear ℂ E E |
      Tendsto (fun n => tracePair (Q n b) X) atTop (𝓝 (tracePair (W b) X))}) ?_ hclosed
    (hst hT)
  intro X hX
  exact hcoord ⟨X, hX⟩

theorem integral_simple_tests_tendsto {μ : Measure A}
    {f : A → Nuclear ℂ E E} (hf : Integrable f μ)
    (Q : ℕ → SimpleFunc A (E →L[ℂ] E)) (W : A → E →L[ℂ] E)
    {C : ℝ} (hbound : ∀ n a, ‖Q n a‖ ≤ C)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n => tracePair (Q n a) (f a))
      atTop (𝓝 (tracePair (W a) (f a)))) :
    Tendsto (fun n => ∫ a, tracePair (Q n a) (f a) ∂μ)
      atTop (𝓝 (∫ a, tracePair (W a) (f a) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun a => C * ‖f a‖)
  · intro n
    exact (integrable_simple_tracePair hf (Q n)).aestronglyMeasurable
  · exact hf.norm.const_mul C
  · intro n
    exact ae_of_all _ (norm_tracePair_le_of_bound (Q n) (hbound n) f)
  · exact hlim

theorem integral_tracePair_eq_of_preimage_setIntegral_eq
    {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c : A → B} (hc : Measurable c)
    {f : A → Nuclear ℂ E E} {g : B → Nuclear ℂ E E}
    (hf : Integrable f μ) (hg : Integrable g ν)
    (hset : ∀ s : Set B, MeasurableSet s →
      (∫ a in c ⁻¹' s, f a ∂μ) = ∫ b in s, g b ∂ν)
    (W : B → E →L[ℂ] E)
    (hW : ∀ x y : E, Measurable (fun b => inner ℂ x (W b y)))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ b, ‖W b‖ ≤ C) :
    (∫ a, tracePair (W (c a)) (f a) ∂μ) =
      ∫ b, tracePair (W b) (g b) ∂ν := by
  let fm := hf.aestronglyMeasurable.mk f
  let gm := hg.aestronglyMeasurable.mk g
  let s : Set (Nuclear ℂ E E) := Set.range fm ∪ Set.range gm
  have hs : TopologicalSpace.IsSeparable s :=
    hf.aestronglyMeasurable.stronglyMeasurable_mk.isSeparable_range.union
      hg.aestronglyMeasurable.stronglyMeasurable_mk.isSeparable_range
  obtain ⟨Q, hQbound, hQlim⟩ :=
    exists_bounded_simple_tests_on_separable_set W hW hC hbound s hs
  have hleft := integral_simple_tests_tendsto hf (fun n => (Q n).comp c hc)
    (fun a => W (c a)) (fun n a => hQbound n (c a)) (by
      filter_upwards [hf.aestronglyMeasurable.ae_eq_mk] with a ha
      rw [ha]
      exact hQlim (c a) (fm a) (Or.inl (mem_range_self a)))
  have hright := integral_simple_tests_tendsto hg Q W hQbound (by
    filter_upwards [hg.aestronglyMeasurable.ae_eq_mk] with b hb
    rw [hb]
    exact hQlim b (gm b) (Or.inr (mem_range_self b)))
  have hseq : (fun n => ∫ a, tracePair (((Q n).comp c hc) a) (f a) ∂μ) =
      fun n => ∫ b, tracePair (Q n b) (g b) ∂ν := by
    funext n
    exact integral_simple_tracePair_eq_of_preimage_setIntegral_eq hc hf hg hset (Q n)
  rw [← hseq] at hright
  exact tendsto_nhds_unique hleft hright

theorem integrable_tests_and_integral_tracePair_eq_of_preimage_setIntegral_eq
    {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {c : A → B} (hc : Measurable c)
    {f : A → Nuclear ℂ E E} {g : B → Nuclear ℂ E E}
    (hf : Integrable f μ) (hg : Integrable g ν)
    (hset : ∀ s : Set B, MeasurableSet s →
      (∫ a in c ⁻¹' s, f a ∂μ) = ∫ b in s, g b ∂ν)
    (W : B → E →L[ℂ] E)
    (hW : ∀ x y : E, Measurable (fun b => inner ℂ x (W b y)))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ b, ‖W b‖ ≤ C) :
    Integrable (fun a => tracePair (W (c a)) (f a)) μ ∧
      Integrable (fun b => tracePair (W b) (g b)) ν ∧
      ((∫ a, tracePair (W (c a)) (f a) ∂μ) =
        ∫ b, tracePair (W b) (g b) ∂ν) :=
  ⟨integrable_tracePair (fun a => W (c a)) (fun x y => (hW x y).comp hc)
      (fun a => hbound (c a)) hf,
    integrable_tracePair W hW hbound hg,
    integral_tracePair_eq_of_preimage_setIntegral_eq hc hf hg hset W hW hC hbound⟩

end QuantumProver.MatrixNuclearCoarseTestIntegral
