import QuantumProver.InformationTheory.WernerEndpoint.ComplexTakagi

noncomputable section

namespace QuantumProver.WernerEndpoint.TakagiRankSix

open scoped BigOperators
open Matrix ComplexTakagi D5RankSix D5SupportFactor SchattenSupport

theorem takagi_schattenOne {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix X X ℂ) (U : Matrix.unitaryGroup X ℂ) (s : X → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hM : M = (U : Matrix X X ℂ) * Matrix.diagonal (fun i => Complex.ofReal (s i)) *
      (U : Matrix X X ℂ)ᵀ) : schattenOne M = ∑ i, s i := by
  have he := takagi_squared_spectrum M U s hM
  have hh := congrArg (fun l : Multiset ℝ => (l.map Real.sqrt).sum) he
  simp only [Multiset.map_map, Function.comp_def] at hh
  have ha (i) : Real.sqrt (s i ^ 2) = s i := Real.sqrt_sq (hs i)
  simp_rw [ha] at hh
  simpa only [Finset.sum_eq_multiset_sum, schattenOne, singularValue] using hh.symm

theorem contracted_fourForm_symmetric {Y : Type*} [Fintype Y] {d : ℕ}
    (A : Matrix Y (Edge d) ℂ) (S : FourSet d) :
    (A * fourFormMatrix S * Aᵀ)ᵀ = A * fourFormMatrix S * Aᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    fourFormMatrix_symmetric]
  simp only [Matrix.mul_assoc]

theorem exists_actual_d5_takagi_rank_six {Y : Type*} [Fintype Y] [DecidableEq Y]
    (A : Matrix Y (Edge 5) ℂ) (t : Fin 5) :
    ∃ (U : Matrix.unitaryGroup Y ℂ) (s : Y → ℝ), (∀ i, 0 ≤ s i) ∧
      A * d5FourFormMatrix t * Aᵀ =
        (U : Matrix Y Y ℂ) * Matrix.diagonal (fun i => Complex.ofReal (s i)) *
          (U : Matrix Y Y ℂ)ᵀ ∧
      Multiset.map (fun i => s i ^ 2) Finset.univ.val =
        Multiset.map (gramHermitian (A * d5FourFormMatrix t * Aᵀ)).eigenvalues Finset.univ.val ∧
      (Finset.univ.filter (fun i => s i ≠ 0)).card ≤ 6 ∧
      schattenOne (A * d5FourFormMatrix t * Aᵀ) = ∑ i, s i := by
  let M := A * d5FourFormMatrix t * Aᵀ
  have hM : Mᵀ = M := contracted_fourForm_symmetric A (omittedFourSet t)
  obtain ⟨U, s, hs, he, hspec, hcount⟩ := exists_complex_symmetric_takagi_with_spectrum M hM
  have hr : (Finset.univ.filter (fun i => s i ≠ 0)).card ≤ 6 := by
    rw [hcount]
    exact contracted_fourForm_rank_le_six A (omittedFourSet t)
  exact ⟨U, s, hs, he, hspec, hr, takagi_schattenOne M U s hs he⟩

end QuantumProver.WernerEndpoint.TakagiRankSix
