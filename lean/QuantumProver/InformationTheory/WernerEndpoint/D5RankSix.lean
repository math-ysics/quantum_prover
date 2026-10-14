import QuantumProver.InformationTheory.WernerEndpoint.D5NuclearControl

noncomputable section

namespace QuantumProver.WernerEndpoint.D5RankSix

open scoped BigOperators
open Matrix ExteriorSupport SchattenSupport D5SupportFactor D5NuclearControl

theorem fourFormMatrix_rank_le_six {d : ℕ} (S : FourSet d) :
    (fourFormMatrix S).rank ≤ 6 := by
  classical
  let rows : Finset (Edge d) :=
    [fourSetEdge S 0 1 (by decide), fourSetEdge S 2 3 (by decide),
      fourSetEdge S 0 2 (by decide), fourSetEdge S 1 3 (by decide),
      fourSetEdge S 0 3 (by decide), fourSetEdge S 1 2 (by decide)].toFinset
  have hs : Function.support (fourFormMatrix S).row ⊆ rows := by
    rw [Function.support_subset_iff']
    intro e he
    funext f
    by_contra hn
    have hu := fourFormOmega_support S (e, f) hn
    have hv : edgeVertices e ⊆ S.val := by
      rw [← hu]
      exact Finset.subset_union_left
    have hh := (edge_subset_fourSet_iff S e).mp hv
    exact he (by simpa [rows] using hh)
  have hc : rows.card ≤ 6 := by
    simpa only [rows, List.length_cons, List.length_nil, Nat.reduceAdd] using
      (List.toFinset_card_le
        [fourSetEdge S 0 1 (by decide), fourSetEdge S 2 3 (by decide),
          fourSetEdge S 0 2 (by decide), fourSetEdge S 1 3 (by decide),
          fourSetEdge S 0 3 (by decide), fourSetEdge S 1 2 (by decide)])
  exact (Matrix.rank_le_card_of_support_subset (fourFormMatrix S) rows hs).trans hc

theorem contracted_fourForm_rank_le_six {Y : Type*} [Fintype Y] {d : ℕ}
    (A : Matrix Y (Edge d) ℂ) (S : FourSet d) :
    (A * fourFormMatrix S * Aᵀ).rank ≤ 6 :=
  (Matrix.rank_mul_le_left (A * fourFormMatrix S) Aᵀ).trans
    ((Matrix.rank_mul_le_right A (fourFormMatrix S)).trans (fourFormMatrix_rank_le_six S))

theorem actual_d5_spectralSupport_le_six {Y : Type*} [Fintype Y] [DecidableEq Y]
    (A : Matrix Y (Edge 5) ℂ) (t : Fin 5) :
    (spectralSupport (A * d5FourFormMatrix t * Aᵀ)).card ≤ 6 := by
  rw [spectralSupport_card]
  exact contracted_fourForm_rank_le_six A (omittedFourSet t)

theorem actual_d5_schatten_rank_bound {Y : Type*} [Fintype Y] [DecidableEq Y]
    (A : Matrix Y (Edge 5) ℂ) (t : Fin 5) :
    schattenOne (A * d5FourFormMatrix t * Aᵀ) ^ 2 ≤
      6 * hsNormSq (A * d5FourFormMatrix t * Aᵀ) := by
  have h := schattenOne_sq_le_rank_hsNormSq (A * d5FourFormMatrix t * Aᵀ)
  have hr : ((A * d5FourFormMatrix t * Aᵀ).rank : ℝ) ≤ 6 := by
    exact_mod_cast contracted_fourForm_rank_le_six A (omittedFourSet t)
  exact h.trans (mul_le_mul_of_nonneg_right hr (hsNormSq_nonneg _))

end QuantumProver.WernerEndpoint.D5RankSix
