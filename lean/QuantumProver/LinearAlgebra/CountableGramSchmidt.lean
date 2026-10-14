import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped BigOperators ComplexConjugate Classical
open Submodule

namespace QuantumProver.CountableGramSchmidt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

abbrev residual (v : ℕ → E) (n : ℕ) : E := InnerProductSpace.gramSchmidt ℂ v n

abbrev frame (v : ℕ → E) (n : ℕ) : E := InnerProductSpace.gramSchmidtNormed ℂ v n

theorem frame_def (v : ℕ → E) (n : ℕ) :
    frame v n = (‖residual v n‖ : ℂ)⁻¹ • residual v n := rfl

theorem residual_decomposition (v : ℕ → E) (n : ℕ) :
    v n = residual v n + ∑ i ∈ Finset.Iio n,
      (inner ℂ (residual v i) (v n) / (‖residual v i‖ : ℂ) ^ 2) • residual v i :=
  InnerProductSpace.gramSchmidt_def'' ℂ v n

theorem frame_eq_zero_iff (v : ℕ → E) (n : ℕ) : frame v n = 0 ↔ residual v n = 0 := by
  simp only [frame_def, smul_eq_zero, inv_eq_zero, Complex.ofReal_eq_zero,
    norm_eq_zero, or_self]

theorem frame_norm_zero_or_one (v : ℕ → E) (n : ℕ) :
    ‖frame v n‖ = 0 ∨ ‖frame v n‖ = 1 := by
  by_cases h : frame v n = 0
  · exact Or.inl (by rw [h, norm_zero])
  · exact Or.inr (InnerProductSpace.gramSchmidtNormed_unit_length' h)

theorem frame_pairwise_orthogonal (v : ℕ → E) :
    Pairwise (fun i j => inner ℂ (frame v i) (frame v j) = 0) := by
  intro i j hij
  simp [frame_def, InnerProductSpace.gramSchmidt_orthogonal ℂ v hij]

theorem span_frame (v : ℕ → E) :
    span ℂ (Set.range (frame v)) = span ℂ (Set.range v) :=
  (InnerProductSpace.span_gramSchmidtNormed_range v).trans
    (InnerProductSpace.span_gramSchmidt ℂ v)

theorem closure_span_frame (v : ℕ → E) :
    (span ℂ (Set.range (frame v))).topologicalClosure =
      (span ℂ (Set.range v)).topologicalClosure := by rw [span_frame]

abbrev NonzeroIndex (v : ℕ → E) := {n : ℕ // frame v n ≠ 0}

abbrev nonzeroFrame (v : ℕ → E) (i : NonzeroIndex v) : E := frame v i.val

theorem nonzeroFrame_orthonormal (v : ℕ → E) : Orthonormal ℂ (nonzeroFrame v) :=
  InnerProductSpace.gramSchmidtNormed_orthonormal' v

theorem span_nonzeroFrame (v : ℕ → E) :
    span ℂ (Set.range (nonzeroFrame v)) = span ℂ (Set.range (frame v)) := by
  apply le_antisymm
  · apply span_mono
    rintro x ⟨i, rfl⟩
    exact ⟨i.val, rfl⟩
  · apply span_le.mpr
    rintro x ⟨n, rfl⟩
    by_cases h : frame v n = 0
    · rw [h]
      exact zero_mem _
    · exact subset_span ⟨⟨n, h⟩, rfl⟩

theorem frame_inner_self (v : ℕ → E) (n : ℕ) :
    inner ℂ (frame v n) (frame v n) = if frame v n = 0 then 0 else 1 := by
  classical
  by_cases h : frame v n = 0
  · simp [h]
  · simpa [nonzeroFrame, h] using
      orthonormal_iff_ite.mp (nonzeroFrame_orthonormal v) (⟨n, h⟩ : NonzeroIndex v) ⟨n, h⟩

theorem frame_inner (v : ℕ → E) (m n : ℕ) :
    inner ℂ (frame v m) (frame v n) =
      if m = n then (if frame v n = 0 then 0 else 1) else 0 := by
  by_cases h : m = n
  · subst m
    rw [ite_eq_left rfl, frame_inner_self]
  · rw [ite_eq_right h]
    exact frame_pairwise_orthogonal v h

private theorem coefficient_support (v : ℕ → E) (x : E) :
    Function.support (fun n => ‖inner ℂ (frame v n) x‖ ^ 2) ⊆ {n | frame v n ≠ 0} := by
  intro n hn hZero
  exact hn (by simp [hZero])

theorem coefficients_summable (v : ℕ → E) (x : E) :
    Summable (fun n => ‖inner ℂ (frame v n) x‖ ^ 2) := by
  have h : Summable (fun i : NonzeroIndex v => ‖inner ℂ (frame v i.val) x‖ ^ 2) :=
    (nonzeroFrame_orthonormal v).inner_products_summable x
  exact ((hasSum_subtype_iff_of_support_subset (coefficient_support v x)).mp h.hasSum).summable

theorem coefficients_memℓp (v : ℕ → E) (x : E) :
    Memℓp (fun n => inner ℂ (frame v n) x) 2 := by
  apply memℓp_gen
  simpa using coefficients_summable v x

def coefficientVector (v : ℕ → E) (x : E) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun n => inner ℂ (frame v n) x, coefficients_memℓp v x⟩

theorem coefficientVector_apply (v : ℕ → E) (x : E) (n : ℕ) :
    coefficientVector v x n = inner ℂ (frame v n) x := rfl

def coordinateLinearMap (v : ℕ → E) : E →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2 where
  toFun := coefficientVector v
  map_add' x y := by
    apply lp.ext
    funext n
    exact inner_add_right _ _ _
  map_smul' c x := by
    apply lp.ext
    funext n
    exact inner_smul_right _ _ _

theorem dense_frame (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) :
    (span ℂ (Set.range (frame v))).topologicalClosure = ⊤ := by
  rw [closure_span_frame, hDense]

theorem dense_nonzeroFrame (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) :
    (span ℂ (Set.range (nonzeroFrame v))).topologicalClosure = ⊤ := by
  rw [span_nonzeroFrame, dense_frame v hDense]

section Complete

variable [CompleteSpace E]

private def activeBasis (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) :
    HilbertBasis (NonzeroIndex v) ℂ E :=
  HilbertBasis.mk (nonzeroFrame_orthonormal v)
    (by rw [dense_nonzeroFrame v hDense])

private theorem activeBasis_apply (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) (i : NonzeroIndex v) :
    activeBasis v hDense i = frame v i.val := by simp [activeBasis]

theorem parseval_hasSum (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) (x : E) :
    HasSum (fun n => ‖inner ℂ (frame v n) x‖ ^ 2) (‖x‖ ^ 2) := by
  have h : HasSum (fun i : NonzeroIndex v => ‖inner ℂ (frame v i.val) x‖ ^ 2) (‖x‖ ^ 2) := by
    have h := lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal)
      ((activeBasis v hDense).repr x)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
      HilbertBasis.repr_apply_apply, activeBasis_apply] using h
  exact (hasSum_subtype_iff_of_support_subset (coefficient_support v x)).mp h

theorem parseval (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) (x : E) :
    ∑' n, ‖inner ℂ (frame v n) x‖ ^ 2 = ‖x‖ ^ 2 :=
  (parseval_hasSum v hDense x).tsum_eq

theorem coefficientVector_norm (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) (x : E) :
    ‖coefficientVector v x‖ = ‖x‖ := by
  have h : ‖coefficientVector v x‖ ^ 2 = ‖x‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)
      (coefficientVector v x)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, coefficientVector_apply,
      parseval v hDense x] using h
  nlinarith [norm_nonneg (coefficientVector v x), norm_nonneg x]

def coordinateEmbedding (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) :
    E →ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 where
  toLinearMap := coordinateLinearMap v
  norm_map' := coefficientVector_norm v hDense

theorem coordinateEmbedding_apply (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) (x : E) (n : ℕ) :
    coordinateEmbedding v hDense x n = inner ℂ (frame v n) x := rfl

theorem coordinateEmbedding_zero_slot (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) (x : E) (n : ℕ)
    (hZero : frame v n = 0) : coordinateEmbedding v hDense x n = 0 := by
  rw [coordinateEmbedding_apply, hZero, inner_zero_left]

theorem coordinateEmbedding_frame (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) (m n : ℕ) :
    coordinateEmbedding v hDense (frame v n) m =
      if m = n then (if frame v n = 0 then 0 else 1) else 0 := by
  rw [coordinateEmbedding_apply, frame_inner]

omit [CompleteSpace E] in
private theorem reconstruction_support (v : ℕ → E) (x : E) :
    Function.support (fun n => inner ℂ (frame v n) x • frame v n) ⊆ {n | frame v n ≠ 0} := by
  intro n hn hZero
  exact hn (by simp [hZero])

theorem hasSum_reconstruction (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) (x : E) :
    HasSum (fun n => inner ℂ (frame v n) x • frame v n) x := by
  have h : HasSum (fun i : NonzeroIndex v => inner ℂ (frame v i.val) x • frame v i.val) x := by
    simpa only [HilbertBasis.repr_apply_apply, activeBasis_apply] using
      (activeBasis v hDense).hasSum_repr x
  exact (hasSum_subtype_iff_of_support_subset (reconstruction_support v x)).mp h

theorem reconstruction (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) (x : E) :
    ∑' n, inner ℂ (frame v n) x • frame v n = x :=
  (hasSum_reconstruction v hDense x).tsum_eq

theorem coefficients_complete (v : ℕ → E)
    (hDense : (span ℂ (Set.range v)).topologicalClosure = ⊤) (x : E)
    (hZero : ∀ n, inner ℂ (frame v n) x = 0) : x = 0 := by
  simpa only [hZero, zero_smul, tsum_zero] using (reconstruction v hDense x).symm

end Complete

end QuantumProver.CountableGramSchmidt
