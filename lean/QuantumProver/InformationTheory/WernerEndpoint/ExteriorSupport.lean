import QuantumProver.InformationTheory.WernerEndpoint.PurityBounds

noncomputable section

namespace QuantumProver.WernerEndpoint.ExteriorSupport

open scoped BigOperators
open Matrix

variable {Y X : Type*} [Fintype Y] [Fintype X]

def orderedExterior (A : Matrix Y X ℂ) : Matrix (Y × Y) (X × X) ℂ :=
  fun ij ab => (A ij.1 ab.1 * A ij.2 ab.2 - A ij.1 ab.2 * A ij.2 ab.1) / 2

theorem normSq_minor (a b c d : ℂ) :
    Complex.normSq (a * b - c * d) =
      Complex.normSq a * Complex.normSq b + Complex.normSq c * Complex.normSq d -
        2 * (a * b * star (c * d)).re := by
  simp only [Complex.normSq_sub, Complex.normSq_mul, Complex.star_def]

theorem sum_quad_product (f g : Y → X → ℝ) :
    (∑ i, ∑ j, ∑ a, ∑ b, f i a * g j b) =
      (∑ i, ∑ a, f i a) * (∑ j, ∑ b, g j b) := by
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

theorem minor_cross_sum (A : Matrix Y X ℂ) :
    (∑ i, ∑ j, ∑ a, ∑ b,
      (A i a * A j b * star (A i b * A j a)).re) = purity (reducedLeft A) := by
  simp only [purity, reducedLeft, crossLeft, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  rw [star_mul]
  ring

theorem orderedExterior_hsNormSq (A : Matrix Y X ℂ) :
    hsNormSq (orderedExterior A) =
      (hsNormSq A ^ 2 - purity (reducedLeft A)) / 2 := by
  have hnorm : hsNormSq (orderedExterior A) =
      (∑ i, ∑ j, ∑ a, ∑ b,
        Complex.normSq (A i a * A j b - A i b * A j a)) / 4 := by
    simp only [hsNormSq, orderedExterior, Fintype.sum_prod_type,
      Complex.sq_norm, Complex.normSq_div, map_ofNat]
    norm_num
    simp_rw [← Finset.sum_div]
  rw [hnorm]
  simp_rw [normSq_minor, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hswap : (∑ i, ∑ j, ∑ a, ∑ b,
      Complex.normSq (A i b) * Complex.normSq (A j a)) =
      (∑ i, ∑ j, ∑ a, ∑ b,
      Complex.normSq (A i a) * Complex.normSq (A j b)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_comm
  rw [sum_quad_product, hswap, sum_quad_product]
  simp_rw [← Finset.mul_sum]
  rw [minor_cross_sum]
  simp only [hsNormSq, Complex.sq_norm]
  ring

theorem orderedExterior_hsNormSq_of_normalized (A : Matrix Y X ℂ)
    (hA : hsNormSq A = 1) :
    hsNormSq (orderedExterior A) = (1 - purity (reducedLeft A)) / 2 := by
  rw [orderedExterior_hsNormSq, hA]
  norm_num

def edgeVertices {d : ℕ} (e : Edge d) : Finset (Fin d) := {e.val.1, e.val.2}

theorem edgeVertices_card {d : ℕ} (e : Edge d) : (edgeVertices e).card = 2 := by
  simp [edgeVertices, e.property.ne]

theorem edge_eq_of_vertices_subset {d : ℕ} (e f : Edge d)
    (h : edgeVertices f ⊆ edgeVertices e) : e = f := by
  have hf1 : f.val.1 = e.val.1 ∨ f.val.1 = e.val.2 := by
    simpa [edgeVertices] using h (by simp [edgeVertices] : f.val.1 ∈ edgeVertices f)
  have hf2 : f.val.2 = e.val.1 ∨ f.val.2 = e.val.2 := by
    simpa [edgeVertices] using h (by simp [edgeVertices] : f.val.2 ∈ edgeVertices f)
  have he := e.property
  have hf := f.property
  have h1 : e.val.1 = f.val.1 := by omega
  have h2 : e.val.2 = f.val.2 := by omega
  exact Subtype.ext (Prod.ext h1 h2)

theorem edge_union_card_ge_three {d : ℕ} (e f : Edge d) (hne : e ≠ f) :
    3 ≤ (edgeVertices e ∪ edgeVertices f).card := by
  by_contra hh
  have hcard : (edgeVertices e ∪ edgeVertices f).card ≤ (edgeVertices e).card := by
    rw [edgeVertices_card]
    omega
  have heq := Finset.eq_of_subset_of_card_le
    (Finset.subset_union_left : edgeVertices e ⊆ edgeVertices e ∪ edgeVertices f) hcard
  have hfsub : edgeVertices f ⊆ edgeVertices e := by
    rw [heq]
    exact Finset.subset_union_right
  exact hne (edge_eq_of_vertices_subset e f hfsub)

theorem d5_outer_support_count (e f : Edge 5) (hne : e ≠ f) :
    (Finset.univ \ (edgeVertices e ∪ edgeVertices f)).card ≤ 2 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  have h := edge_union_card_ge_three e f hne
  omega

theorem sum_separated_complex (f g : X → ℂ) :
    (∑ a, ∑ b, f a * g b) = (∑ a, f a) * (∑ b, g b) := by
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

theorem sum_quad_factor (f g h k : X → ℂ) :
    (∑ a, ∑ b, (f a * g b) * (h a * k b)) =
      (∑ a, f a * h a) * (∑ b, g b * k b) := by
  have hm (a b : X) : (f a * g b) * (h a * k b) = (f a * h a) * (g b * k b) := by ring
  simp_rw [hm]
  exact sum_separated_complex _ _

theorem sum_quad_swap (f g h k : X → ℂ) :
    (∑ a, ∑ b, (f b * g a) * (h a * k b)) =
      (∑ a, f a * k a) * (∑ b, g b * h b) := by
  calc
    _ = ∑ b, ∑ a, (f b * g a) * (h a * k b) := Finset.sum_comm
    _ = ∑ b, ∑ a, (f b * k b) * (g a * h a) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := sum_separated_complex _ _

theorem orderedExterior_mul {Z : Type*} [Fintype Z]
    (A : Matrix Y X ℂ) (B : Matrix X Z ℂ) :
    orderedExterior (A * B) = orderedExterior A * orderedExterior B := by
  ext ⟨i, j⟩ ⟨c, d⟩
  simp only [orderedExterior, Matrix.mul_apply, Fintype.sum_prod_type]
  have hdiv (x y : ℂ) : x / 2 * (y / 2) = x * y / 4 := by ring
  simp_rw [hdiv, ← Finset.sum_div]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [sum_quad_factor, sum_quad_factor, sum_quad_swap, sum_quad_swap]
  ring

theorem orderedExterior_transpose (A : Matrix Y X ℂ) :
    orderedExterior Aᵀ = (orderedExterior A)ᵀ := by
  ext ⟨a, b⟩ ⟨i, j⟩
  simp only [orderedExterior, Matrix.transpose_apply]
  ring

theorem orderedExterior_common_covariance (A : Matrix Y X ℂ) (B : Matrix X X ℂ) :
    orderedExterior (A * B * Aᵀ) =
      orderedExterior A * orderedExterior B * (orderedExterior A)ᵀ := by
  rw [orderedExterior_mul, orderedExterior_mul, orderedExterior_transpose]

def d5ColumnRestriction (A : Matrix Y (Edge 5) ℂ) (t : Fin 5) : Matrix Y (Edge 5) ℂ :=
  fun i e => if t ∈ edgeVertices e then 0 else A i e

theorem orderedExterior_d5ColumnRestriction (A : Matrix Y (Edge 5) ℂ)
    (t : Fin 5) (ij : Y × Y) (e f : Edge 5) :
    orderedExterior (d5ColumnRestriction A t) ij (e, f) =
      if t ∈ edgeVertices e ∪ edgeVertices f then 0 else orderedExterior A ij (e, f) := by
  by_cases he : t ∈ edgeVertices e <;> by_cases hf : t ∈ edgeVertices f <;>
    simp [orderedExterior, d5ColumnRestriction, he, hf]

theorem orderedExterior_diagonal_column (A : Matrix Y X ℂ) (ij : Y × Y) (a : X) :
    orderedExterior A ij (a, a) = 0 := by
  simp [orderedExterior]

theorem d5_restricted_column_sum (A : Matrix Y (Edge 5) ℂ)
    (ij : Y × Y) (e f : Edge 5) :
    (∑ t : Fin 5, ‖orderedExterior (d5ColumnRestriction A t) ij (e, f)‖ ^ 2) ≤
      2 * ‖orderedExterior A ij (e, f)‖ ^ 2 := by
  simp_rw [orderedExterior_d5ColumnRestriction]
  by_cases hef : e = f
  · subst f
    simp [orderedExterior_diagonal_column]
  · have hsum : (∑ t : Fin 5,
        ‖if t ∈ edgeVertices e ∪ edgeVertices f then (0 : ℂ) else
          orderedExterior A ij (e, f)‖ ^ 2) =
        ((Finset.univ \ (edgeVertices e ∪ edgeVertices f)).card : ℝ) *
          ‖orderedExterior A ij (e, f)‖ ^ 2 := by
      have hset : Finset.univ.filter (fun t : Fin 5 => t ∉ edgeVertices e ∪ edgeVertices f) =
          Finset.univ \ (edgeVertices e ∪ edgeVertices f) := by
        ext t
        simp
      calc
        _ = ∑ t : Fin 5, if t ∉ edgeVertices e ∪ edgeVertices f then
            ‖orderedExterior A ij (e, f)‖ ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro t _
          by_cases ht : t ∈ edgeVertices e ∪ edgeVertices f <;> simp [ht]
        _ = _ := by rw [← Finset.sum_filter, hset]; simp
    rw [hsum]
    have hcount : ((Finset.univ \ (edgeVertices e ∪ edgeVertices f)).card : ℝ) ≤ 2 := by
      exact_mod_cast d5_outer_support_count e f hef
    exact mul_le_mul_of_nonneg_right hcount (sq_nonneg _)

theorem d5_restricted_exterior_hs_sum (A : Matrix Y (Edge 5) ℂ) :
    (∑ t : Fin 5, hsNormSq (orderedExterior (d5ColumnRestriction A t))) ≤
      2 * hsNormSq (orderedExterior A) := by
  unfold hsNormSq
  have hreorder : (∑ t : Fin 5, ∑ ij : Y × Y, ∑ ef : Edge 5 × Edge 5,
      ‖orderedExterior (d5ColumnRestriction A t) ij ef‖ ^ 2) =
      ∑ ij : Y × Y, ∑ ef : Edge 5 × Edge 5, ∑ t : Fin 5,
      ‖orderedExterior (d5ColumnRestriction A t) ij ef‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ij _
    exact Finset.sum_comm
  rw [hreorder]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ij _
  apply Finset.sum_le_sum
  rintro ⟨e, f⟩ _
  exact d5_restricted_column_sum A ij e f

theorem d5_restricted_exterior_hs_sum_of_normalized (A : Matrix Y (Edge 5) ℂ)
    (hA : hsNormSq A = 1) :
    (∑ t : Fin 5, hsNormSq (orderedExterior (d5ColumnRestriction A t))) ≤
      1 - purity (reducedLeft A) := by
  have h := d5_restricted_exterior_hs_sum A
  rw [orderedExterior_hsNormSq_of_normalized A hA] at h
  linarith

end QuantumProver.WernerEndpoint.ExteriorSupport
