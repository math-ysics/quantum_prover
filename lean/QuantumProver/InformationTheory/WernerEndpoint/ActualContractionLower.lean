import QuantumProver.InformationTheory.WernerEndpoint.TakagiContraction
import QuantumProver.InformationTheory.WernerEndpoint.ExteriorTakagiSpectrum

noncomputable section
namespace QuantumProver.WernerEndpoint.ActualContractionLower

open scoped BigOperators
open Matrix ComplexTakagi SchattenSupport ExteriorSupport TakagiContraction
  ExteriorTakagiSpectrum RealSymmetricFactor D5SupportFactor ExteriorSchatten

variable {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]

theorem actual_symmetric_replica_lower (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ w : Y → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (M : Matrix Y Y ℂ) (hM : Mᵀ = M) :
    -β * schattenOne (orderedExterior M) ≤
      (dotProduct (star (fun ij : Y × Y => M ij.1 ij.2))
        (N.replicaKernel.mulVec (fun ij : Y × Y => M ij.1 ij.2))).re := by
  obtain ⟨U, s, hs, hf⟩ := exists_complex_symmetric_takagi M hM
  rw [takagi_exterior_schatten_sum M U s hs hf,
    actual_takagi_contraction_expansion N M U s hf]
  have h := takagi_weighted_trace_lower N β hbound U s hs
  nlinarith

theorem actual_takagi_hs_sum (M : Matrix Y Y ℂ)
    (U : Matrix.unitaryGroup Y ℂ) (s : Y → ℝ)
    (hf : M = (U : Matrix Y Y ℂ) * Matrix.diagonal (fun i => Complex.ofReal (s i)) *
      (U : Matrix Y Y ℂ)ᵀ) :
    (∑ i, s i ^ 2) = hsNormSq M := by
  have hspec := takagi_squared_spectrum M U s hf
  have hsum : (∑ i, s i ^ 2) = ∑ i, (gramHermitian M).eigenvalues i := by
    simpa only [Finset.sum_eq_multiset_sum] using congrArg Multiset.sum hspec
  have htrace := congrArg Complex.re (gramHermitian M).trace_eq_sum_eigenvalues
  rw [Matrix.trace_mul_comm Mᴴ M, ← hsNormSq_eq_trace M] at htrace
  exact hsum.trans (by simpa [Complex.re_sum] using htrace.symm)

theorem actual_symmetric_rank_six_retained_lower (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ w : Y → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (M : Matrix Y Y ℂ) (hM : Mᵀ = M) (hRank : M.rank ≤ 6) :
    -(4 * β / 5) * schattenOne (orderedExterior M) ≤
      (dotProduct (star (fun ij : Y × Y => M ij.1 ij.2))
        (N.replicaKernel.mulVec (fun ij : Y × Y => M ij.1 ij.2))).re := by
  obtain ⟨U, s, hs, hf, hspec, hcount⟩ := exists_complex_symmetric_takagi_with_spectrum M hM
  have hc : (Finset.univ.filter (fun i => s i ≠ 0)).card ≤ 6 := hcount.le.trans hRank
  rw [takagi_exterior_schatten_sum M U s hs hf,
    actual_takagi_contraction_expansion N M U s hf]
  have h := rank_six_weighted_trace_exterior_lower N β hbound U s hs hc
  nlinarith

theorem actual_rank_six_replica_hs_lower
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ w : Y → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (M : Matrix Y Y ℂ) (hM : Mᵀ = M) (hRank : M.rank ≤ 6) :
    -2 * β * hsNormSq M ≤
      (dotProduct (star (fun ij : Y × Y => M ij.1 ij.2))
        (N.replicaKernel.mulVec (fun ij : Y × Y => M ij.1 ij.2))).re := by
  classical
  rcases isEmpty_or_nonempty Y with hY | hY
  · letI := hY
    simp [hsNormSq, dotProduct]
  · letI := hY
    obtain ⟨U, s, hs, hf, hspec, hcount⟩ := exists_complex_symmetric_takagi_with_spectrum M hM
    have hc : (Finset.univ.filter (fun i => s i ≠ 0)).card ≤ 6 := hcount.le.trans hRank
    rw [actual_takagi_contraction_expansion N M U s hf, ← actual_takagi_hs_sum M U s hf]
    exact rank_six_weighted_trace_hs_lower N β hbound U s hs hc

theorem actual_fourForm_replica_hs_lower {d : ℕ}
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ w : Y → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (A : Matrix Y (Edge d) ℂ) (S : FourSet d) :
    -2 * β * hsNormSq (A * fourFormMatrix S * Aᵀ) ≤
      (dotProduct (star (fun ij : Y × Y => (A * fourFormMatrix S * Aᵀ) ij.1 ij.2))
        (N.replicaKernel.mulVec
          (fun ij : Y × Y => (A * fourFormMatrix S * Aᵀ) ij.1 ij.2))).re :=
  actual_rank_six_replica_hs_lower N β hbound _
    (TakagiRankSix.contracted_fourForm_symmetric A S)
    (D5RankSix.contracted_fourForm_rank_le_six A S)

theorem actual_fourForm_replica_retained_lower {d : ℕ}
    (N : Stinespring Y B E) (β : ℝ)
    (hbound : ∀ w : Y → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (A : Matrix Y (Edge d) ℂ) (S : FourSet d) :
    -(4 * β / 5) * schattenOne (orderedExterior (A * fourFormMatrix S * Aᵀ)) ≤
      (dotProduct (star (fun ij : Y × Y => (A * fourFormMatrix S * Aᵀ) ij.1 ij.2))
        (N.replicaKernel.mulVec
          (fun ij : Y × Y => (A * fourFormMatrix S * Aᵀ) ij.1 ij.2))).re :=
  actual_symmetric_rank_six_retained_lower N β hbound _
    (TakagiRankSix.contracted_fourForm_symmetric A S)
    (D5RankSix.contracted_fourForm_rank_le_six A S)

def fourCovarianceFactor {d : ℕ} (S : FourSet d) : Matrix (Edge d) (Edge d) ℂ :=
  covarianceFactor (realFourFormMatrix S) (realFourFormMatrix_hermitian S)

def fourSupportProjector {d : ℕ} (S : FourSet d) : Matrix (Edge d) (Edge d) ℂ :=
  complexify (fourSupportMatrix S)

theorem fourCovarianceFactor_covariance {d : ℕ} (S : FourSet d) :
    fourCovarianceFactor S * (fourCovarianceFactor S)ᵀ = fourFormMatrix S := by
  rw [fourCovarianceFactor, covarianceFactor_covariance, complexify_realFourFormMatrix]

theorem fourCovarianceFactor_gram {d : ℕ} (S : FourSet d) :
    fourCovarianceFactor S * (fourCovarianceFactor S)ᴴ = fourSupportProjector S := by
  rw [fourCovarianceFactor, covarianceFactor_gram_of_cube _ _ (realFourFormMatrix_cube S),
    realFourFormMatrix_square]
  rfl

theorem fourSupportProjector_hermitian {d : ℕ} (S : FourSet d) :
    (fourSupportProjector S)ᴴ = fourSupportProjector S := by
  rw [fourSupportProjector, D5NuclearControl.fourSupportMatrix_diagonal,
    complexify_diagonal]
  simp only [Matrix.diagonal_conjTranspose]
  congr 1
  funext e
  split_ifs <;> simp_all

theorem fourSupportProjector_idempotent {d : ℕ} (S : FourSet d) :
    fourSupportProjector S * fourSupportProjector S = fourSupportProjector S := by
  rw [fourSupportProjector, D5NuclearControl.fourSupportMatrix_diagonal,
    complexify_diagonal]
  simp only [Matrix.diagonal_mul_diagonal]
  congr 1
  funext e
  split_ifs <;> simp_all

theorem actual_fourForm_exterior_nuclear_support_bound {d : ℕ}
    (A : Matrix Y (Edge d) ℂ) (S : FourSet d) :
    schattenOne (orderedExterior (A * fourFormMatrix S * Aᵀ)) ≤
      hsNormSq (orderedExterior (A * fourSupportProjector S)) :=
  exterior_covariance_support A (fourCovarianceFactor S)
    (fourFormMatrix S) (fourSupportProjector S)
    (fourCovarianceFactor_covariance S) (fourCovarianceFactor_gram S)
    (fourSupportProjector_hermitian S) (fourSupportProjector_idempotent S)

end QuantumProver.WernerEndpoint.ActualContractionLower
