import Mathlib

open scoped BigOperators ComplexConjugate
open InnerProductSpace

namespace QuantumProver.ElegantJointMeasurement.RankOne

noncomputable section

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sum_norm_inner_sq_eq (s : Finset ι) (w : ι → H) (u : H) :
    ((∑ i ∈ s, ‖inner ℂ (w i) u‖ ^ 2 : ℝ) : ℂ) =
      inner ℂ u ((∑ i ∈ s, rankOne ℂ (w i) (w i)) u) := by
  calc
    ((∑ i ∈ s, ‖inner ℂ (w i) u‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ s, conj (inner ℂ (w i) u) * inner ℂ (w i) u := by
      simp only [Complex.conj_mul']
      push_cast
      rfl
    _ = ∑ i ∈ s, inner ℂ u (rankOne ℂ (w i) (w i) u) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [inner_right_rankOne_apply, ← inner_conj_symm u (w i)]
    _ = inner ℂ u ((∑ i ∈ s, rankOne ℂ (w i) (w i)) u) := by
      simp only [_root_.sum_apply, inner_sum]

theorem rankOne_sum_collinear (s : Finset ι) (w : ι → H) (e : H)
    (he : ‖e‖ = 1)
    (hsum : ∑ i ∈ s, rankOne ℂ (w i) (w i) = rankOne ℂ e e) :
    ∀ i ∈ s, w i = inner ℂ e (w i) • e := by
  have heinner : inner ℂ e e = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]
    norm_num
  intro i hi
  let u := w i - inner ℂ e (w i) • e
  have horth : inner ℂ e u = 0 := by
    simp only [u, inner_sub_right, inner_smul_right, heinner, mul_one, sub_self]
  have hcomplex := sum_norm_inner_sq_eq s w u
  rw [hsum, inner_right_rankOne_apply, horth, mul_zero] at hcomplex
  have hreal : ∑ k ∈ s, ‖inner ℂ (w k) u‖ ^ 2 = 0 := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_zero] using hcomplex
  have hnorm : ‖inner ℂ (w i) u‖ = 0 :=
    (Finset.sum_sq_eq_zero_iff s (fun k => ‖inner ℂ (w k) u‖)).mp hreal i hi
  have hinner : inner ℂ (w i) u = 0 := norm_eq_zero.mp hnorm
  have hdecomp : w i = u + inner ℂ e (w i) • e := by
    dsimp [u]
    exact (sub_add_cancel _ _).symm
  rw [hdecomp, inner_add_left, inner_smul_left, horth, mul_zero, add_zero] at hinner
  have hu : u = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp hinner
  dsimp [u] at hu
  exact sub_eq_zero.mp hu

theorem rankOne_sum_normalization (s : Finset ι) (w : ι → H) (e : H)
    (he : ‖e‖ = 1)
    (hsum : ∑ i ∈ s, rankOne ℂ (w i) (w i) = rankOne ℂ e e) :
    ∑ i ∈ s, ‖inner ℂ e (w i)‖ ^ 2 = 1 := by
  have heinner : inner ℂ e e = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]
    norm_num
  have hcomplex := sum_norm_inner_sq_eq s w e
  rw [hsum, inner_right_rankOne_apply, heinner, mul_one] at hcomplex
  have hreal : ∑ i ∈ s, ‖inner ℂ (w i) e‖ ^ 2 = 1 := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_one] using hcomplex
  calc
    ∑ i ∈ s, ‖inner ℂ e (w i)‖ ^ 2 = ∑ i ∈ s, ‖inner ℂ (w i) e‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_inner_symm]
    _ = 1 := hreal

theorem eigenvector_sum_moment (s : Finset ι) (w : ι → H) (u : H)
    (hfix : (∑ i ∈ s, rankOne ℂ (w i) (w i)) u = u) :
    ∑ i ∈ s, conj (inner ℂ u (w i)) • w i = u := by
  calc
    ∑ i ∈ s, conj (inner ℂ u (w i)) • w i =
        ∑ i ∈ s, inner ℂ (w i) u • w i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [inner_conj_symm]
    _ = (∑ i ∈ s, rankOne ℂ (w i) (w i)) u := by
      simp only [_root_.sum_apply, rankOne_apply]
    _ = u := hfix

theorem eigenvector_projected_moment {V : Type*} [AddCommGroup V] [Module ℂ V]
    (s : Finset ι) (w : ι → H) (u : H) (C : H →ₗ[ℂ] V)
    (hfix : (∑ i ∈ s, rankOne ℂ (w i) (w i)) u = u) :
    ∑ i ∈ s, conj (inner ℂ u (w i)) • C (w i) = C u := by
  have h := congrArg C (eigenvector_sum_moment s w u hfix)
  simpa only [map_sum, map_smul] using h

theorem positive_apply_eq_zero_of_inner_eq_zero [FiniteDimensional ℂ H]
    (T : H →L[ℂ] H) (hT : T.IsPositive) (u : H)
    (hzero : inner ℂ u (T u) = 0) : T u = 0 := by
  obtain ⟨m, w, hw⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hT
  have hcomplex := sum_norm_inner_sq_eq Finset.univ w u
  rw [← hw, hzero] at hcomplex
  have hreal : ∑ i : Fin m, ‖inner ℂ (w i) u‖ ^ 2 = 0 := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_zero] using hcomplex
  have hinner (i : Fin m) : inner ℂ (w i) u = 0 := by
    apply norm_eq_zero.mp
    exact (Finset.sum_sq_eq_zero_iff Finset.univ
      (fun k => ‖inner ℂ (w k) u‖)).mp hreal i (Finset.mem_univ i)
  calc
    T u = ∑ i : Fin m, inner ℂ (w i) u • w i := by
      rw [hw]
      simp only [_root_.sum_apply, rankOne_apply]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hinner i, zero_smul]

theorem saturation_eigenvector [FiniteDimensional ℂ H]
    (F : H →L[ℂ] H) (u : H)
    (hupper : (ContinuousLinearMap.id ℂ H - F).IsPositive)
    (hu : ‖u‖ = 1) (hexpect : inner ℂ u (F u) = 1) : F u = u := by
  have hquadratic : inner ℂ u ((ContinuousLinearMap.id ℂ H - F) u) = 0 := by
    rw [_root_.sub_apply, ContinuousLinearMap.id_apply,
      inner_sub_right, inner_self_eq_norm_sq_to_K, hu, hexpect]
    norm_num
  have hzero := positive_apply_eq_zero_of_inner_eq_zero
    (ContinuousLinearMap.id ℂ H - F) hupper u hquadratic
  have hfix : u - F u = 0 := by
    simpa only [_root_.sub_apply, ContinuousLinearMap.id_apply] using hzero
  exact (sub_eq_zero.mp hfix).symm

section Domination

variable [CompleteSpace H]

theorem positive_domination_of_fixed_unit (F : H →L[ℂ] H) (u : H)
    (hF : F.IsPositive) (hu : ‖u‖ = 1) (hfix : F u = u) :
    (F - rankOne ℂ u u).IsPositive := by
  let P := rankOne ℂ u u
  let Q := ContinuousLinearMap.id ℂ H - P
  have heinner : inner ℂ u u = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]
    norm_num
  have hinner (z : H) : inner ℂ u (F z) = inner ℂ u z := by
    rw [← hF.inner_left_eq_inner_right, hfix]
  have hQadjoint : Q.adjoint = Q := by
    dsimp [Q, P]
    rw [map_sub, ContinuousLinearMap.adjoint_id, adjoint_rankOne]
  have heq : Q.adjoint ∘L F ∘L Q = F - P := by
    rw [hQadjoint]
    ext z
    simp [Q, P, ContinuousLinearMap.comp_apply, rankOne_apply, hfix, hinner, hu]
  have hpositive := hF.adjoint_conj Q
  rw [heq] at hpositive
  exact hpositive

end Domination

section Compression

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace H] [CompleteSpace K]

theorem compressed_rankOne_sum (s : Finset ι) (a : ι → K) (J : H →L[ℂ] K) :
    J.adjoint ∘L ((∑ i ∈ s, rankOne ℂ (a i) (a i)) ∘L J) =
      ∑ i ∈ s, rankOne ℂ (J.adjoint (a i)) (J.adjoint (a i)) := by
  rw [ContinuousLinearMap.finsetSum_comp, ContinuousLinearMap.comp_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [rankOne_comp, comp_rankOne]

theorem compressed_branch_collinear (s : Finset ι) (a : ι → K) (J : H →L[ℂ] K)
    (e : H) (he : ‖e‖ = 1)
    (hcompression : J.adjoint ∘L ((∑ i ∈ s, rankOne ℂ (a i) (a i)) ∘L J) =
      rankOne ℂ e e) :
    ∀ i ∈ s, J.adjoint (a i) = inner ℂ (J e) (a i) • e := by
  have hsum : ∑ i ∈ s, rankOne ℂ (J.adjoint (a i)) (J.adjoint (a i)) =
      rankOne ℂ e e := by
    rw [← compressed_rankOne_sum s a J]
    exact hcompression
  have h := rankOne_sum_collinear s (fun i => J.adjoint (a i)) e he hsum
  intro i hi
  simpa only [ContinuousLinearMap.adjoint_inner_right] using h i hi

theorem compressed_branch_normalization (s : Finset ι) (a : ι → K) (J : H →L[ℂ] K)
    (e : H) (he : ‖e‖ = 1)
    (hcompression : J.adjoint ∘L ((∑ i ∈ s, rankOne ℂ (a i) (a i)) ∘L J) =
      rankOne ℂ e e) :
    ∑ i ∈ s, ‖inner ℂ (J e) (a i)‖ ^ 2 = 1 := by
  have hsum : ∑ i ∈ s, rankOne ℂ (J.adjoint (a i)) (J.adjoint (a i)) =
      rankOne ℂ e e := by
    rw [← compressed_rankOne_sum s a J]
    exact hcompression
  simpa only [ContinuousLinearMap.adjoint_inner_right] using
    rankOne_sum_normalization s (fun i => J.adjoint (a i)) e he hsum

end Compression

end

end QuantumProver.ElegantJointMeasurement.RankOne
