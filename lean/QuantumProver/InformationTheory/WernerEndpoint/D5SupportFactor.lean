import QuantumProver.InformationTheory.WernerEndpoint.ExteriorSchatten

noncomputable section

namespace QuantumProver.WernerEndpoint.D5SupportFactor

open scoped BigOperators
open Matrix ExteriorSupport ExteriorSchatten RealSymmetricFactor SchattenSupport

theorem fourSetEdge_eq_iff {d : ℕ} (S : FourSet d)
    (i j k l : Fin 4) (hij : i < j) (hkl : k < l) :
    fourSetEdge S i j hij = fourSetEdge S k l hkl ↔ i = k ∧ j = l := by
  constructor
  · intro h
    have h1 := congrArg (fun e : Edge d => e.val.1) h
    have h2 := congrArg (fun e : Edge d => e.val.2) h
    exact ⟨(S.val.orderEmbOfFin S.property).injective h1,
      (S.val.orderEmbOfFin S.property).injective h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

def realFourFormMatrix {d : ℕ} (S : FourSet d) : Matrix (Edge d) (Edge d) ℝ :=
  let ab := fourSetEdge S 0 1 (by decide)
  let ac := fourSetEdge S 0 2 (by decide)
  let ad := fourSetEdge S 0 3 (by decide)
  let bc := fourSetEdge S 1 2 (by decide)
  let bd := fourSetEdge S 1 3 (by decide)
  let cd := fourSetEdge S 2 3 (by decide)
  Matrix.single ab cd 1 + Matrix.single cd ab 1 -
    Matrix.single ac bd 1 - Matrix.single bd ac 1 +
    Matrix.single ad bc 1 + Matrix.single bc ad 1

def fourSupportMatrix {d : ℕ} (S : FourSet d) : Matrix (Edge d) (Edge d) ℝ :=
  let ab := fourSetEdge S 0 1 (by decide)
  let ac := fourSetEdge S 0 2 (by decide)
  let ad := fourSetEdge S 0 3 (by decide)
  let bc := fourSetEdge S 1 2 (by decide)
  let bd := fourSetEdge S 1 3 (by decide)
  let cd := fourSetEdge S 2 3 (by decide)
  Matrix.single ab ab 1 + Matrix.single cd cd 1 +
    Matrix.single ac ac 1 + Matrix.single bd bd 1 +
    Matrix.single ad ad 1 + Matrix.single bc bc 1

theorem complexify_realFourFormMatrix {d : ℕ} (S : FourSet d) :
    complexify (realFourFormMatrix S) = fourFormMatrix S := by
  ext e f
  have hcast (p : Prop) [Decidable p] :
      Complex.ofReal (if p then (1 : ℝ) else 0) = (if p then (1 : ℂ) else 0) := by
    by_cases hp : p <;> simp [hp]
  simp only [complexify, realFourFormMatrix, fourFormMatrix, fourFormOmega,
    Matrix.add_apply, Matrix.sub_apply, Complex.ofReal_add, Complex.ofReal_sub,
    Matrix.single_apply, hcast, Pi.add_apply, Pi.sub_apply, Pi.single_apply,
    Prod.mk.injEq]
  simp only [eq_comm]

theorem realFourFormMatrix_symmetric {d : ℕ} (S : FourSet d) :
    (realFourFormMatrix S)ᵀ = realFourFormMatrix S := by
  simp only [realFourFormMatrix, Matrix.transpose_add, Matrix.transpose_sub,
    Matrix.transpose_single]
  abel

theorem realFourFormMatrix_hermitian {d : ℕ} (S : FourSet d) :
    (realFourFormMatrix S).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact realFourFormMatrix_symmetric S

theorem single_mul_single_ite {X : Type*} [Fintype X] [DecidableEq X]
    (i j k l : X) (a b : ℝ) :
    Matrix.single i j a * Matrix.single k l b =
      if j = k then Matrix.single i l (a * b) else 0 := by
  by_cases h : j = k
  · subst k
    simp
  · rw [if_neg h]
    exact Matrix.single_mul_single_of_ne a i j k h b

theorem realFourFormMatrix_square {d : ℕ} (S : FourSet d) :
    realFourFormMatrix S * realFourFormMatrix S = fourSupportMatrix S := by
  simp only [realFourFormMatrix, fourSupportMatrix, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_add, Matrix.mul_sub, single_mul_single_ite]
  simp [fourSetEdge_eq_iff]
  all_goals abel

theorem fourSupportMatrix_mul {d : ℕ} (S : FourSet d) :
    fourSupportMatrix S * realFourFormMatrix S = realFourFormMatrix S := by
  simp only [realFourFormMatrix, fourSupportMatrix, Matrix.add_mul,
    Matrix.mul_add, Matrix.mul_sub, single_mul_single_ite]
  simp [fourSetEdge_eq_iff]
  all_goals abel

theorem realFourFormMatrix_cube {d : ℕ} (S : FourSet d) :
    realFourFormMatrix S ^ 3 = realFourFormMatrix S := by
  rw [pow_succ, pow_two, realFourFormMatrix_square, fourSupportMatrix_mul]

theorem fourFormMatrix_symmetric {d : ℕ} (S : FourSet d) :
    (fourFormMatrix S)ᵀ = fourFormMatrix S := by
  rw [← complexify_realFourFormMatrix, ← complexify_transpose,
    realFourFormMatrix_symmetric]

theorem fourFormOmega_normSq {d : ℕ} (S : FourSet d) :
    vectorNormSq (fourFormOmega S) = 6 := by
  have hn : vectorNormSq (fourFormOmega S) = hsNormSq (fourFormMatrix S) := by
    simp [vectorNormSq, hsNormSq, fourFormMatrix, Fintype.sum_prod_type, Complex.sq_norm]
  rw [hn, ← complexify_realFourFormMatrix, hsNormSq_eq_trace,
    complexify_conjTranspose, ← complexify_transpose, realFourFormMatrix_symmetric,
    ← complexify_mul, realFourFormMatrix_square]
  simp [complexify, fourSupportMatrix, Matrix.trace, Matrix.single_apply,
    Finset.sum_add_distrib, eq_comm]
  norm_num

theorem fourSet_eq_vertices {d : ℕ} (S : FourSet d) :
    S.val = {(S.val.orderEmbOfFin S.property) 0, (S.val.orderEmbOfFin S.property) 1,
      (S.val.orderEmbOfFin S.property) 2, (S.val.orderEmbOfFin S.property) 3} := by
  let E := S.val.orderEmbOfFin S.property
  let T : Finset (Fin d) := {E 0, E 1, E 2, E 3}
  have hsub : T ⊆ S.val := by
    intro x hx
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact S.val.orderEmbOfFin_mem S.property _
  have hc : T.card = 4 := by
    norm_num [T, Finset.card_insert_of_notMem, E.injective.eq_iff]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [S.property, hc])).symm

theorem fourFormOmega_support {d : ℕ} (S : FourSet d) (ij : Edge d × Edge d)
    (hne : fourFormOmega S ij ≠ 0) :
    edgeVertices ij.1 ∪ edgeVertices ij.2 = S.val := by
  let ab := fourSetEdge S 0 1 (by decide)
  let ac := fourSetEdge S 0 2 (by decide)
  let ad := fourSetEdge S 0 3 (by decide)
  let bc := fourSetEdge S 1 2 (by decide)
  let bd := fourSetEdge S 1 3 (by decide)
  let cd := fourSetEdge S 2 3 (by decide)
  have hs : ij = (ab, cd) ∨ ij = (cd, ab) ∨ ij = (ac, bd) ∨ ij = (bd, ac) ∨
      ij = (ad, bc) ∨ ij = (bc, ad) := by
    by_contra hh
    push_neg at hh
    exact hne (by simp_all [fourFormOmega, ab, ac, ad, bc, bd, cd, Pi.single_apply])
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [fourSet_eq_vertices S] <;>
    ext x <;>
    simp only [ab, ac, ad, bc, bd, cd, edgeVertices, fourSetEdge,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] <;> tauto

theorem d5FourFormOmega_disjoint (t u : Fin 5) (htu : t ≠ u)
    (ij : Edge 5 × Edge 5) : d5FourFormOmega t ij = 0 ∨ d5FourFormOmega u ij = 0 := by
  by_contra hh
  push_neg at hh
  have ht := fourFormOmega_support (omittedFourSet t) ij hh.1
  have hu := fourFormOmega_support (omittedFourSet u) ij hh.2
  have he : (Finset.univ : Finset (Fin 5)).erase t = Finset.univ.erase u := by
    exact ht.symm.trans hu
  have hm : t ∈ (Finset.univ : Finset (Fin 5)).erase u := by simp [htu]
  rw [← he] at hm
  simpa using hm

theorem d5FourFormOmega_gram (t u : Fin 5) :
    (∑ ij : Edge 5 × Edge 5, star (d5FourFormOmega t ij) * d5FourFormOmega u ij) =
      if t = u then (6 : ℂ) else 0 := by
  by_cases h : t = u
  · subst u
    rw [if_pos rfl]
    have hn := fourFormOmega_normSq (omittedFourSet t)
    have hs : (∑ ij : Edge 5 × Edge 5,
        star (d5FourFormOmega t ij) * d5FourFormOmega t ij) =
        Complex.ofReal (vectorNormSq (fourFormOmega (omittedFourSet t))) := by
      simp [vectorNormSq, d5FourFormOmega, mul_comm, Complex.mul_conj]
    rw [hs, hn]
    norm_num
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro ij _
    rcases d5FourFormOmega_disjoint t u h ij with hz | hz <;> simp [hz]

end QuantumProver.WernerEndpoint.D5SupportFactor
