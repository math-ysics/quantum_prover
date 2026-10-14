import QuantumProver.InformationTheory.WernerEndpoint.TakagiAntilinear

noncomputable section

namespace QuantumProver.WernerEndpoint.TakagiCompletion

open scoped BigOperators
open Matrix TakagiAntilinear

variable {X : Type*} [Fintype X] [DecidableEq X]

local instance realInner : InnerProductSpace ℝ (EuclideanSpace ℂ X) :=
  InnerProductSpace.complexToReal

theorem spectral_repr_eigenvector (M : Matrix X X ℂ) (hM : Mᵀ = M)
    (w : EuclideanSpace ℂ X) (μ : ℝ) (hw : antiLinear M w = μ • w)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℂ X))) :
    realSpectralValue M hM i * (realSpectralBasis M hM).repr w i =
      μ * (realSpectralBasis M hM).repr w i := by
  have h := (antiLinear_symmetric M hM).eigenvectorBasis_apply_self_apply rfl w i
  rw [hw, map_smul] at h
  simpa [realSpectralBasis, realSpectralValue, PiLp.smul_apply, smul_eq_mul] using h.symm

theorem inner_positive_eigenvector_zero (M : Matrix X X ℂ) (hM : Mᵀ = M)
    (w v : EuclideanSpace ℂ X) (μ : ℝ) (hμ : 0 < μ)
    (hw : antiLinear M w = μ • w)
    (hv : ∀ i : PositiveIndex M hM, inner ℂ (positiveVector M hM i) v = 0) :
    inner ℂ w v = 0 := by
  let b := realSpectralBasis M hM
  calc
    _ = inner ℂ (∑ i, b.repr w i • b i) v := by rw [b.sum_repr]
    _ = ∑ i, inner ℂ (b.repr w i • b i) v := sum_inner _ _ _
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : 0 < realSpectralValue M hM i
      · have hz := hv ⟨i, hi⟩
        change inner ℂ ((b.repr w i : ℂ) • b i) v = 0
        rw [inner_smul_left]
        change _ * inner ℂ (positiveVector M hM ⟨i, hi⟩) v = 0
        rw [hz, mul_zero]
      · have he := spectral_repr_eigenvector M hM w μ hw i
        have hp : (μ - realSpectralValue M hM i) * b.repr w i = 0 := by
          change realSpectralValue M hM i * b.repr w i = μ * b.repr w i at he
          nlinarith
        have hn : μ - realSpectralValue M hM i ≠ 0 := by linarith
        have hz : b.repr w i = 0 := (mul_eq_zero.mp hp).resolve_left hn
        rw [hz, zero_smul, inner_zero_left]

theorem positive_orthogonal_kernel (M : Matrix X X ℂ) (hM : Mᵀ = M)
    (v : EuclideanSpace ℂ X)
    (hv : ∀ i : PositiveIndex M hM, inner ℂ (positiveVector M hM i) v = 0) :
    antiLinear M v = 0 := by
  let b := realSpectralBasis M hM
  calc
    _ = antiLinear M (∑ i, b.repr v i • b i) := by rw [b.sum_repr]
    _ = ∑ i, b.repr v i • antiLinear M (b i) := by simp only [map_sum, map_smul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hz : realSpectralValue M hM i = 0
      · rw [realSpectral_eigenvector, hz, zero_smul, smul_zero]
      · have hi : inner ℂ (b i) v = 0 := by
          by_cases hp : 0 < realSpectralValue M hM i
          · exact hv ⟨i, hp⟩
          · have hn : 0 < -realSpectralValue M hM i :=
              neg_pos.mpr ((lt_or_eq_of_le (le_of_not_gt hp)).resolve_right hz)
            have hw : antiLinear M (Complex.I • b i) =
                (-realSpectralValue M hM i) • (Complex.I • b i) := by
              rw [antiLinear_complex_smul, realSpectral_eigenvector]
              ext x
              simp [b, Complex.star_def, smul_smul]
              ring
            have hh := inner_positive_eigenvector_zero M hM (Complex.I • b i) v
              (-realSpectralValue M hM i) hn hw hv
            rw [inner_smul_left] at hh
            exact (mul_eq_zero.mp hh).resolve_left (by simp)
        have hc : b.repr v i = 0 := by
          rw [b.repr_apply_apply]
          change (inner ℂ (b i) v).re = 0
          rw [hi]
          rfl
        rw [hc, zero_smul]

theorem exists_antilinear_orthonormalBasis (M : Matrix X X ℂ) (hM : Mᵀ = M) :
    ∃ (b : OrthonormalBasis X ℂ (EuclideanSpace ℂ X)) (s : X → ℝ),
      (∀ i, 0 ≤ s i) ∧ ∀ i, antiLinear M (b i) = s i • b i := by
  classical
  let v := positiveVector M hM
  let V : Set (EuclideanSpace ℂ X) := Set.range v
  have hv := positiveVector_orthonormal M hM
  have hV : Orthonormal ℂ ((↑) : V → EuclideanSpace ℂ X) := by
    rw [orthonormal_subtype_range hv.linearIndependent.injective]
    exact hv
  obtain ⟨u, b, hsub, hb⟩ := hV.exists_orthonormalBasis_extension
  have hbval (k : u) : b k = k.val := congrFun hb k
  let s : u → ℝ := fun k => if hk : k.val ∈ V then
    realSpectralValue M hM (Classical.choose hk).val else 0
  have hs (k : u) : 0 ≤ s k := by
    by_cases hk : k.val ∈ V
    · simp only [s, dif_pos hk]
      exact le_of_lt (Classical.choose hk).property
    · simp [s, hk]
  have heig (k : u) : antiLinear M (b k) = s k • b k := by
    rw [hbval]
    by_cases hk : k.val ∈ V
    · simp only [s, dif_pos hk]
      have hh := Classical.choose_spec hk
      have he := realSpectral_eigenvector M hM (Classical.choose hk).val
      exact (congrArg (antiLinear M) hh).symm.trans
        (he.trans (congrArg (fun w => realSpectralValue M hM (Classical.choose hk).val • w) hh))
    · simp only [s, dif_neg hk, zero_smul]
      apply positive_orthogonal_kernel M hM k.val
      intro i
      have hi : v i ∈ u := hsub ⟨i, rfl⟩
      let j : u := ⟨v i, hi⟩
      have hjk : j ≠ k := by
        intro h
        apply hk
        exact ⟨i, congrArg Subtype.val h⟩
      have hh := orthonormal_iff_ite.mp b.orthonormal j k
      rw [if_neg hjk, hbval, hbval] at hh
      exact hh
  have hc : u.card = Fintype.card X :=
    (Module.finrank_eq_card_finset_basis b.toBasis).symm.trans
      (finrank_euclideanSpace (𝕜 := ℂ) (ι := X))
  let e : u ≃ X := Fintype.equivOfCardEq (by simpa using hc)
  refine ⟨b.reindex e, fun i => s (e.symm i), ?_, ?_⟩
  · intro i
    exact hs (e.symm i)
  · intro i
    simpa only [OrthonormalBasis.reindex_apply] using heig (e.symm i)

end QuantumProver.WernerEndpoint.TakagiCompletion
