import QuantumProver.InformationTheory.WernerEndpoint.AntisymmetricEnsembleCost
import QuantumProver.InformationTheory.WernerEndpoint.TakagiContraction

noncomputable section
namespace QuantumProver.WernerEndpoint.DensityEnsembleExistence

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix Unitary AntisymmetricEntropyCost AntisymmetricEnsembleCost TakagiContraction

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem hermitian_spectral_density_expansion (ρ : Matrix X X ℂ) (hρ : ρ.IsHermitian) :
    ρ = ∑ i, (hρ.eigenvalues i : ℂ) • pureDensity (unitaryColumn hρ.eigenvectorUnitary i) := by
  calc
    ρ = (hρ.eigenvectorUnitary : Matrix X X ℂ) *
      Matrix.diagonal (fun i => Complex.ofReal (hρ.eigenvalues i)) *
        (hρ.eigenvectorUnitary : Matrix X X ℂ)ᴴ := by
      simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def,
        Matrix.star_eq_conjTranspose, rclike_complex_cast] using hρ.spectral_theorem
    _ = _ := by
      ext i j
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul, pureDensity, crossDensity, unitaryColumn,
        rclike_complex_cast]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem density_has_finitePureEnsemble (ρ : Matrix X X ℂ) (hρ : ρ.PosSemidef)
    (htrace : Matrix.trace ρ = 1) : Nonempty (FinitePureEnsemble ρ) := by
  let e : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  obtain ⟨hp, hs⟩ := density_spectral_probability ρ hρ htrace
  refine ⟨{
    count := Fintype.card X
    weight := fun j => hρ.isHermitian.eigenvalues (e j)
    weight_nonneg := fun j => hp (e j)
    weight_sum := ?_
    vector := fun j => unitaryColumn hρ.isHermitian.eigenvectorUnitary (e j)
    normalized := fun j => unitaryColumn_normSq hρ.isHermitian.eigenvectorUnitary (e j)
    barycenter := ?_ }⟩
  · rw [e.sum_comp]
    exact hs
  · exact (hermitian_spectral_density_expansion ρ hρ.isHermitian).trans (e.sum_comp _).symm

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem density_finiteConvexRoof_ne_top (ρ : Matrix (A × B) (A × B) ℂ)
    (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ = 1) : finiteConvexRoof ρ ≠ ⊤ := by
  obtain ⟨E⟩ := density_has_finitePureEnsemble ρ hρ htrace
  exact ne_of_lt (lt_of_le_of_lt (iInf_le (fun E : FinitePureEnsemble ρ =>
    (E.averageAliceEntropy : EReal)) E) (EReal.coe_lt_top E.averageAliceEntropy))

theorem density_supported_finiteConvexRoof_lower
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ = 1)
    (P : Matrix (A × B) (A × B) ℂ) (hP : P * P = P)
    (hsupp : ρ = P * ρ * P) (n : ℕ)
    (hpur : ∀ ψ : A × B → ℂ, vectorNormSq ψ = 1 → P.mulVec ψ = ψ →
      purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n) :
    ∃ c : ℝ, (n : ℝ) ≤ c ∧ finiteConvexRoof ρ = (c : EReal) := by
  have hl := finiteConvexRoof_lower_from_range_purity ρ P hP hsupp n hpur
  have htop := density_finiteConvexRoof_ne_top ρ hρ htrace
  have hbot : finiteConvexRoof ρ ≠ ⊥ := by
    intro h
    rw [h] at hl
    exact (not_le_of_gt (EReal.bot_lt_coe (n : ℝ))) hl
  have hc := EReal.coe_toReal htop hbot
  refine ⟨(finiteConvexRoof ρ).toReal, ?_, hc.symm⟩
  rw [← hc] at hl
  exact_mod_cast hl

end QuantumProver.WernerEndpoint.DensityEnsembleExistence
