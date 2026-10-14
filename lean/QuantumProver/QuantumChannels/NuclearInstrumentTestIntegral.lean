import Mathlib
import QuantumProver.LinearAlgebra.HilbertNuclearCompression

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Filter Set InnerProductSpace
open scoped BigOperators Topology InnerProduct

namespace QuantumProver.MatrixNuclearInstrumentTestIntegral

open QuantumProver.NuclearOperator QuantumProver.HilbertNuclearCompression

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [MeasurableSpace Ω]

local instance nuclearNormedGroup : NormedAddCommGroup (Nuclear ℂ E E) := inferInstance
local instance nuclearNormedSpace : NormedSpace ℂ (Nuclear ℂ E E) := inferInstance

def tracePairCLM (W : E →L[ℂ] E) : Nuclear ℂ E E →L[ℂ] ℂ :=
  (QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ) (E := E)).comp
    (compose W (ContinuousLinearMap.id ℂ E))

def tracePair (W : E →L[ℂ] E) (T : Nuclear ℂ E E) : ℂ :=
  tracePairCLM W T

@[simp] theorem tracePair_zero (W : E →L[ℂ] E) : tracePair W 0 = 0 :=
  (tracePairCLM W).map_zero

@[simp] theorem tracePair_add (W : E →L[ℂ] E) (T S : Nuclear ℂ E E) :
    tracePair W (T + S) = tracePair W T + tracePair W S :=
  (tracePairCLM W).map_add T S

@[simp] theorem tracePair_smul (W : E →L[ℂ] E) (c : ℂ) (T : Nuclear ℂ E E) :
    tracePair W (c • T) = c • tracePair W T :=
  (tracePairCLM W).map_smul c T

@[simp] theorem tracePair_real_smul (W : E →L[ℂ] E) (r : ℝ) (T : Nuclear ℂ E E) :
    tracePair W (r • T) = r • tracePair W T :=
  ((tracePairCLM W).restrictScalars ℝ).map_smul r T

theorem tracePair_rankOne (W : E →L[ℂ] E) (φ : E →L[ℂ] ℂ) (y : E) :
    tracePair W (rankOne φ y) = φ (W y) := by
  simp only [tracePair, tracePairCLM, ContinuousLinearMap.comp_apply,
    compose_rankOne, QuantumProver.HilbertNuclearTrace.trace_rankOne,
    ContinuousLinearMap.id_apply]

theorem norm_tracePair_le (W : E →L[ℂ] E) (T : Nuclear ℂ E E) :
    ‖tracePair W T‖ ≤ ‖W‖ * ‖T‖ := by
  refine (QuantumProver.HilbertNuclearTrace.norm_trace_apply_le _).trans
    ((norm_compose_apply_le W (ContinuousLinearMap.id ℂ E) T).trans ?_)
  calc
    (‖W‖ * ‖ContinuousLinearMap.id ℂ E‖) * ‖T‖ ≤ (‖W‖ * 1) * ‖T‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg W))
        (norm_nonneg T)
    _ = ‖W‖ * ‖T‖ := by ring

omit [MeasurableSpace Ω] in
theorem norm_tracePair_le_of_bound (W : Ω → E →L[ℂ] E) {C : ℝ}
    (hbound : ∀ ω, ‖W ω‖ ≤ C) (f : Ω → Nuclear ℂ E E) (ω : Ω) :
    ‖tracePair (W ω) (f ω)‖ ≤ C * ‖f ω‖ :=
  (norm_tracePair_le _ _).trans
    (mul_le_mul_of_nonneg_right (hbound ω) (norm_nonneg _))

theorem measurable_tracePair_atom (W : Ω → E →L[ℂ] E)
    (hW : ∀ x y : E, Measurable (fun ω => inner ℂ x (W ω y)))
    (a : Atom ℂ E E) :
    Measurable (fun ω => tracePair (W ω) (ofAtom a)) := by
  let v := (InnerProductSpace.toDual ℂ E).symm a.1.1
  have hv (z : E) : inner ℂ v z = a.1.1 z :=
    InnerProductSpace.toDual_symm_apply
  have heq : (fun ω => tracePair (W ω) (ofAtom a)) =
      fun ω => inner ℂ v (W ω a.2.1) := by
    funext ω
    rw [← rankOne_atom_eq_ofAtom a, tracePair_rankOne, hv]
  rw [heq]
  exact hW v a.2.1

theorem measurable_tracePair_fixed (W : Ω → E →L[ℂ] E)
    (hW : ∀ x y : E, Measurable (fun ω => inner ℂ x (W ω y)))
    (T : Nuclear ℂ E E) : Measurable (fun ω => tracePair (W ω) T) := by
  classical
  obtain ⟨c, rfl⟩ := ofCoefficients_surjective T
  let S : Set (Atom ℂ E E) := Function.support (fun a => c a)
  have hS : S.Countable := (Memℓp.summable_of_one (lp.memℓp c)).countable_support
  have : Countable S := hS.to_subtype
  have hseries : HasSum (fun a : S => c a.1 • ofAtom a.1) (ofCoefficients c) := by
    apply (hasSum_subtype_iff_of_support_subset (s := S) ?_).mpr
      (hasSum_ofCoefficients c)
    intro a ha
    show c a ≠ 0
    intro hz
    exact ha (by simp [hz])
  have hvalue (ω : Ω) :
      (∑' a : S, c a.1 * tracePair (W ω) (ofAtom a.1)) =
        tracePair (W ω) (ofCoefficients c) := by
    have hmap := hseries.mapL (tracePairCLM (W ω))
    simpa only [tracePair, map_smul, smul_eq_mul] using hmap.tsum_eq
  have hm : Measurable (fun ω => ∑' a : S,
      c a.1 * tracePair (W ω) (ofAtom a.1)) :=
    Measurable.tsum fun a : S =>
      measurable_const.mul (measurable_tracePair_atom W hW a.1)
  convert hm using 1
  funext ω
  exact (hvalue ω).symm

theorem measurable_tracePair_simple (W : Ω → E →L[ℂ] E)
    (hW : ∀ x y : E, Measurable (fun ω => inner ℂ x (W ω y)))
    (f : SimpleFunc Ω (Nuclear ℂ E E)) :
    Measurable (fun ω => tracePair (W ω) (f ω)) := by
  classical
  apply SimpleFunc.induction (motive := fun f : SimpleFunc Ω (Nuclear ℂ E E) =>
    Measurable (fun ω => tracePair (W ω) (f ω))) ?_ ?_ f
  · intro T s hs
    have heq : (fun ω => tracePair (W ω)
        ((SimpleFunc.piecewise s hs (SimpleFunc.const Ω T)
          (SimpleFunc.const Ω 0)) ω)) =
        s.indicator (fun ω => tracePair (W ω) T) := by
      funext ω
      by_cases hω : ω ∈ s <;> simp [hω]
    rw [heq]
    exact (measurable_tracePair_fixed W hW T).indicator hs
  · intro f g _ hf hg
    convert hf.add hg using 1
    funext ω
    simp only [SimpleFunc.coe_add, Pi.add_apply, tracePair_add]

theorem stronglyMeasurable_tracePair (W : Ω → E →L[ℂ] E)
    (hW : ∀ x y : E, Measurable (fun ω => inner ℂ x (W ω y)))
    {f : Ω → Nuclear ℂ E E} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun ω => tracePair (W ω) (f ω)) := by
  apply stronglyMeasurable_of_tendsto (Filter.atTop : Filter ℕ)
    (fun n => (measurable_tracePair_simple W hW (hf.approx n)).stronglyMeasurable)
  apply tendsto_pi_nhds.mpr
  intro ω
  exact (tracePairCLM (W ω)).continuous.tendsto (f ω) |>.comp (hf.tendsto_approx ω)

theorem aestronglyMeasurable_tracePair {μ : Measure Ω} (W : Ω → E →L[ℂ] E)
    (hW : ∀ x y : E, Measurable (fun ω => inner ℂ x (W ω y)))
    {f : Ω → Nuclear ℂ E E} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun ω => tracePair (W ω) (f ω)) μ := by
  have hm : AEStronglyMeasurable
      (fun ω => tracePair (W ω) (hf.mk f ω)) μ :=
    (stronglyMeasurable_tracePair W hW hf.stronglyMeasurable_mk).aestronglyMeasurable
  apply hm.congr
  filter_upwards [hf.ae_eq_mk] with ω hω
  exact congrArg (tracePair (W ω)) hω.symm

theorem integrable_tracePair {μ : Measure Ω} (W : Ω → E →L[ℂ] E)
    (hW : ∀ x y : E, Measurable (fun ω => inner ℂ x (W ω y)))
    {C : ℝ} (hbound : ∀ ω, ‖W ω‖ ≤ C)
    {f : Ω → Nuclear ℂ E E} (hf : Integrable f μ) :
    Integrable (fun ω => tracePair (W ω) (f ω)) μ :=
  (hf.norm.const_mul C).mono' (aestronglyMeasurable_tracePair W hW hf.aestronglyMeasurable)
    (ae_of_all _ (norm_tracePair_le_of_bound W hbound f))

theorem integral_tracePair_tendsto_of_dominated {μ : Measure Ω}
    (W : Ω → E →L[ℂ] E)
    (hW : ∀ x y : E, Measurable (fun ω => inner ℂ x (W ω y)))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ ω, ‖W ω‖ ≤ C)
    (F : ℕ → Ω → Nuclear ℂ E E) (f : Ω → Nuclear ℂ E E) (b : Ω → ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hb : Integrable b μ)
    (hdom : ∀ n, ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ b ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (f ω))) :
    Tendsto (fun n => ∫ ω, tracePair (W ω) (F n ω) ∂μ)
      atTop (𝓝 (∫ ω, tracePair (W ω) (f ω) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun ω => C * b ω)
  · intro n
    exact aestronglyMeasurable_tracePair W hW (hF n)
  · exact hb.const_mul C
  · intro n
    filter_upwards [hdom n] with ω hω
    exact (norm_tracePair_le_of_bound W hbound (F n) ω).trans
      (mul_le_mul_of_nonneg_left hω hC)
  · filter_upwards [hlim] with ω hω
    exact (tracePairCLM (W ω)).continuous.tendsto (f ω) |>.comp hω

private theorem left_reference_ac (μ ν : Measure Ω) : μ ≪ μ + ν := by
  intro s hs
  simp only [Measure.add_apply, add_eq_zero] at hs
  exact hs.1

private theorem right_reference_ac (μ ν : Measure Ω) : ν ≪ μ + ν := by
  intro s hs
  simp only [Measure.add_apply, add_eq_zero] at hs
  exact hs.2

theorem commonReference_density_ae_eq_of_setIntegral_eq
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f g : Ω → Nuclear ℂ E E} (hf : Integrable f μ) (hg : Integrable g ν)
    (hset : ∀ s : Set Ω, MeasurableSet s →
      (∫ ω in s, f ω ∂μ) = ∫ ω in s, g ω ∂ν) :
    (fun ω => (μ.rnDeriv (μ + ν) ω).toReal • f ω) =ᵐ[μ + ν]
      fun ω => (ν.rnDeriv (μ + ν) ω).toReal • g ω := by
  have hμ := left_reference_ac μ ν
  have hν := right_reference_ac μ ν
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((integrable_rnDeriv_smul_iff hμ).mpr hf)
    ((integrable_rnDeriv_smul_iff hν).mpr hg)
  intro s hs _
  rw [setIntegral_rnDeriv_smul hμ hs,
    setIntegral_rnDeriv_smul hν hs, hset s hs]

private theorem integral_tracePair_eq_aux
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f g : Ω → Nuclear ℂ E E} (hf : Integrable f μ) (hg : Integrable g ν)
    (hset : ∀ s : Set Ω, MeasurableSet s →
      (∫ ω in s, f ω ∂μ) = ∫ ω in s, g ω ∂ν)
    (W : Ω → E →L[ℂ] E) :
    (∫ ω, tracePair (W ω) (f ω) ∂μ) = ∫ ω, tracePair (W ω) (g ω) ∂ν := by
  have hμ := left_reference_ac μ ν
  have hν := right_reference_ac μ ν
  have hfg := commonReference_density_ae_eq_of_setIntegral_eq hf hg hset
  calc
    (∫ ω, tracePair (W ω) (f ω) ∂μ) =
        ∫ ω, (μ.rnDeriv (μ + ν) ω).toReal • tracePair (W ω) (f ω) ∂(μ + ν) :=
      (integral_rnDeriv_smul hμ).symm
    _ = ∫ ω, tracePair (W ω) ((μ.rnDeriv (μ + ν) ω).toReal • f ω) ∂(μ + ν) := by
      simp only [tracePair_real_smul]
    _ = ∫ ω, tracePair (W ω) ((ν.rnDeriv (μ + ν) ω).toReal • g ω) ∂(μ + ν) := by
      apply integral_congr_ae
      filter_upwards [hfg] with ω hω
      exact congrArg (tracePair (W ω)) hω
    _ = ∫ ω, (ν.rnDeriv (μ + ν) ω).toReal • tracePair (W ω) (g ω) ∂(μ + ν) := by
      simp only [tracePair_real_smul]
    _ = ∫ ω, tracePair (W ω) (g ω) ∂ν :=
      integral_rnDeriv_smul hν

theorem integrable_tests_and_integral_tracePair_eq_of_setIntegral_eq
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f g : Ω → Nuclear ℂ E E} (hf : Integrable f μ) (hg : Integrable g ν)
    (hset : ∀ s : Set Ω, MeasurableSet s →
      (∫ ω in s, f ω ∂μ) = ∫ ω in s, g ω ∂ν)
    (W : Ω → E →L[ℂ] E)
    (hW : ∀ x y : E, Measurable (fun ω => inner ℂ x (W ω y)))
    {C : ℝ} (_hC : 0 ≤ C) (hbound : ∀ ω, ‖W ω‖ ≤ C) :
    Integrable (fun ω => tracePair (W ω) (f ω)) μ ∧
      Integrable (fun ω => tracePair (W ω) (g ω)) ν ∧
      ((∫ ω, tracePair (W ω) (f ω) ∂μ) = ∫ ω, tracePair (W ω) (g ω) ∂ν) :=
  ⟨integrable_tracePair W hW hbound hf, integrable_tracePair W hW hbound hg,
    integral_tracePair_eq_aux hf hg hset W⟩

theorem integral_tracePair_eq_of_setIntegral_eq
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f g : Ω → Nuclear ℂ E E} (hf : Integrable f μ) (hg : Integrable g ν)
    (hset : ∀ s : Set Ω, MeasurableSet s →
      (∫ ω in s, f ω ∂μ) = ∫ ω in s, g ω ∂ν)
    (W : Ω → E →L[ℂ] E)
    (hW : ∀ x y : E, Measurable (fun ω => inner ℂ x (W ω y)))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ ω, ‖W ω‖ ≤ C) :
    (∫ ω, tracePair (W ω) (f ω) ∂μ) = ∫ ω, tracePair (W ω) (g ω) ∂ν :=
  (integrable_tests_and_integral_tracePair_eq_of_setIntegral_eq hf hg hset W hW hC hbound).2.2

end QuantumProver.MatrixNuclearInstrumentTestIntegral
