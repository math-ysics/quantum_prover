import Mathlib

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace QuantumProver.ElegantJointMeasurement.HilbertInstrumentTestIntegral

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ ν : Measure Ω} {f g w : Ω → ℂ}

theorem integrable_bounded_mul (hf : Integrable f μ) (hw : Measurable w)
    {C : ℝ} (hbound : ∀ x, ‖w x‖ ≤ C) :
    Integrable (fun x => w x * f x) μ :=
  hf.bdd_mul hw.aestronglyMeasurable (ae_of_all _ hbound)

theorem integrable_simple_mul (hf : Integrable f μ) (s : SimpleFunc Ω ℂ) :
    Integrable (fun x => s x * f x) μ := by
  classical
  apply integrable_bounded_mul hf s.measurable
    (C := ∑ z ∈ s.range, ‖z‖)
  intro x
  exact Finset.single_le_sum (fun z _ => norm_nonneg z) (s.mem_range_self x)

theorem integral_simple_mul_eq_of_setIntegral_eq
    (hf : Integrable f μ) (hg : Integrable g ν)
    (hset : ∀ s : Set Ω, MeasurableSet s →
      (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂ν)
    (w : SimpleFunc Ω ℂ) :
    (∫ x, w x * f x ∂μ) = ∫ x, w x * g x ∂ν := by
  classical
  apply SimpleFunc.induction (motive := fun w : SimpleFunc Ω ℂ =>
    (∫ x, w x * f x ∂μ) = ∫ x, w x * g x ∂ν) ?_ ?_ w
  · intro c s hs
    have hprod (h : Ω → ℂ) :
        (fun x => (SimpleFunc.piecewise s hs (SimpleFunc.const Ω c)
          (SimpleFunc.const Ω 0)) x * h x) = s.indicator (fun x => c * h x) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hprod f, hprod g, integral_indicator hs, integral_indicator hs,
      integral_const_mul, integral_const_mul, hset s hs]
  · intro u v _ hu hv
    simp only [SimpleFunc.coe_add, Pi.add_apply, add_mul]
    rw [integral_add (integrable_simple_mul hf u) (integrable_simple_mul hf v),
      integral_add (integrable_simple_mul hg u) (integrable_simple_mul hg v), hu, hv]

theorem integral_simple_approx_mul_tendsto (hf : Integrable f μ)
    (hw : StronglyMeasurable w) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖w x‖ ≤ C) :
    Tendsto (fun n : ℕ => ∫ x, hw.approxBounded C n x * f x ∂μ)
      atTop (𝓝 (∫ x, w x * f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => C * ‖f x‖)
  · intro n
    exact (hw.approxBounded C n).stronglyMeasurable.aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · exact hf.norm.const_mul C
  · intro n
    exact ae_of_all _ fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hw.norm_approxBounded_le hC n x) (norm_nonneg _)
  · exact ae_of_all _ fun x =>
      (hw.tendsto_approxBounded_of_norm_le (hbound x)).mul tendsto_const_nhds

theorem integral_bounded_mul_eq_of_setIntegral_eq
    (hf : Integrable f μ) (hg : Integrable g ν)
    (hset : ∀ s : Set Ω, MeasurableSet s →
      (∫ x in s, f x ∂μ) = ∫ x in s, g x ∂ν)
    (hw : Measurable w) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖w x‖ ≤ C) :
    (∫ x, w x * f x ∂μ) = ∫ x, w x * g x ∂ν := by
  let hwm : StronglyMeasurable w := hw.stronglyMeasurable
  have hμ := integral_simple_approx_mul_tendsto hf hwm hC hbound
  have hν := integral_simple_approx_mul_tendsto hg hwm hC hbound
  have hseq : (fun n : ℕ => ∫ x, hwm.approxBounded C n x * f x ∂μ) =
      (fun n : ℕ => ∫ x, hwm.approxBounded C n x * g x ∂ν) := by
    funext n
    exact integral_simple_mul_eq_of_setIntegral_eq hf hg hset _
  rw [← hseq] at hν
  exact tendsto_nhds_unique hμ hν

end QuantumProver.ElegantJointMeasurement.HilbertInstrumentTestIntegral

namespace QuantumProver.ElegantJointMeasurement.HilbertInstrumentTestIntegral
section MatrixPairing
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
variable {μ ν : Measure Ω} {F G W : Ω → Matrix I I ℂ}

theorem integrable_trace_mul_of_entries
    (hF : ∀ i j, Integrable (fun x => F x i j) μ)
    (hW : ∀ i j, Measurable (fun x => W x i j))
    (C : I → I → ℝ) (hbound : ∀ i j x, ‖W x i j‖ ≤ C i j) :
    Integrable (fun x => (W x * F x).trace) μ := by
  change Integrable (fun x => ∑ i, ∑ j, W x i j * F x j i) μ
  exact integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ =>
      integrable_bounded_mul (hF j i) (hW i j) (hbound i j)

theorem integral_trace_mul_eq_sum_entries
    (hF : ∀ i j, Integrable (fun x => F x i j) μ)
    (hW : ∀ i j, Measurable (fun x => W x i j))
    (C : I → I → ℝ) (hbound : ∀ i j x, ‖W x i j‖ ≤ C i j) :
    (∫ x, (W x * F x).trace ∂μ) = ∑ i, ∑ j, ∫ x, W x i j * F x j i ∂μ := by
  change (∫ x, ∑ i, ∑ j, W x i j * F x j i ∂μ) = _
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ fun j _ =>
      integrable_bounded_mul (hF j i) (hW i j) (hbound i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finsetSum Finset.univ fun j _ =>
    integrable_bounded_mul (hF j i) (hW i j) (hbound i j)

theorem integral_trace_mul_eq_of_entry_setIntegral_eq
    (hF : ∀ i j, Integrable (fun x => F x i j) μ)
    (hG : ∀ i j, Integrable (fun x => G x i j) ν)
    (hset : ∀ i j (s : Set Ω), MeasurableSet s →
      (∫ x in s, F x i j ∂μ) = ∫ x in s, G x i j ∂ν)
    (hW : ∀ i j, Measurable (fun x => W x i j))
    (C : I → I → ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hbound : ∀ i j x, ‖W x i j‖ ≤ C i j) :
    (∫ x, (W x * F x).trace ∂μ) = ∫ x, (W x * G x).trace ∂ν := by
  rw [integral_trace_mul_eq_sum_entries hF hW C hbound,
    integral_trace_mul_eq_sum_entries hG hW C hbound]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact integral_bounded_mul_eq_of_setIntegral_eq (hF j i) (hG j i)
    (hset j i) (hW i j) (hC i j) (hbound i j)

open scoped Matrix.Norms.L2Operator
variable [DecidableEq I]

def matrixEntryCLM (i j : I) : Matrix I I ℂ →L[ℂ] ℂ := by
  classical
  exact ({ toFun := fun X => X i j
           map_add' := by intros; rfl
           map_smul' := by intros; rfl } : Matrix I I ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

@[simp] theorem matrixEntryCLM_apply (i j : I) (X : Matrix I I ℂ) :
    matrixEntryCLM i j X = X i j := rfl

theorem integrable_matrix_entry (hF : Integrable F μ) (i j : I) :
    Integrable (fun x => F x i j) μ :=
  (matrixEntryCLM i j).integrable_comp hF

theorem integral_matrix_entry (hF : Integrable F μ) (i j : I) :
    (∫ x, F x i j ∂μ) = (∫ x, F x ∂μ) i j := by
  simpa only [matrixEntryCLM_apply] using (matrixEntryCLM i j).integral_comp_comm hF

theorem integral_trace_mul_eq_of_setIntegral_eq
    (hF : Integrable F μ) (hG : Integrable G ν)
    (hset : ∀ s : Set Ω, MeasurableSet s →
      (∫ x in s, F x ∂μ) = ∫ x in s, G x ∂ν)
    (hW : ∀ i j, Measurable (fun x => W x i j))
    (C : I → I → ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (hbound : ∀ i j x, ‖W x i j‖ ≤ C i j) :
    (∫ x, (W x * F x).trace ∂μ) = ∫ x, (W x * G x).trace ∂ν := by
  apply integral_trace_mul_eq_of_entry_setIntegral_eq
    (fun i j => integrable_matrix_entry hF i j)
    (fun i j => integrable_matrix_entry hG i j) ?_ hW C hC hbound
  intro i j s hs
  rw [integral_matrix_entry hF.integrableOn i j,
    integral_matrix_entry hG.integrableOn i j, hset s hs]

end MatrixPairing
end QuantumProver.ElegantJointMeasurement.HilbertInstrumentTestIntegral
