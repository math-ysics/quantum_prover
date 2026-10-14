import QuantumProver.InformationTheory.WernerEndpoint.EnsemblePhase

noncomputable section

namespace QuantumProver.WernerEndpoint.MixedPurity

open scoped BigOperators ComplexOrder
open Matrix Unitary

variable {I B E : Type*} [Fintype I] [Fintype B] [Fintype E] [DecidableEq I]

theorem spectral_vectors_gram (σ : Matrix I I ℂ) (hσ : σ.IsHermitian) (i j : I) :
    (∑ x, (hσ.eigenvectorBasis i) x * star ((hσ.eigenvectorBasis j) x)) =
      if i = j then 1 else 0 := by
  have h := congrArg (fun M : Matrix I I ℂ => M j i)
    (Unitary.coe_star_mul_self hσ.eigenvectorUnitary)
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, mul_comm, eq_comm] using h

theorem spectral_projector_sum (σ : Matrix I I ℂ) (hσ : σ.IsHermitian) :
    σ = ∑ i, (hσ.eigenvalues i : ℂ) • pureDensity (fun x => (hσ.eigenvectorBasis i) x) := by
  conv_lhs => rw [hσ.spectral_theorem]
  ext x y
  simp [Unitary.conjStarAlgAut_apply, Matrix.diagonal_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
    pureDensity, crossDensity, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc]

theorem eigenvalues_sum_one (σ : Matrix I I ℂ) (hσ : σ.IsHermitian)
    (htrace : Matrix.trace σ = 1) : ∑ i, hσ.eigenvalues i = 1 := by
  have h := congrArg Complex.re hσ.trace_eq_sum_eigenvalues
  rw [htrace] at h
  simpa [Complex.re_sum] using h.symm

theorem mixed_marginal_purity (N : Stinespring I B E) (β : ℝ)
    (hbound : ∀ w : I → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (σ : Matrix I I ℂ) (hσ : σ.PosSemidef) (htrace : Matrix.trace σ = 1) :
    purity (N.apply σ) + purity (N.complement σ) ≤ β * (1 + purity σ) := by
  let ψ : I → I → ℂ := fun i x => (hσ.isHermitian.eigenvectorBasis i) x
  let t : I → ℝ := fun i => Real.sqrt (hσ.isHermitian.eigenvalues i)
  have hgram : ∀ i j, (∑ x, ψ i x * star (ψ j x)) = if i = j then 1 else 0 :=
    spectral_vectors_gram σ hσ.isHermitian
  have htsq (i : I) : t i ^ 2 = hσ.isHermitian.eigenvalues i :=
    Real.sq_sqrt (hσ.eigenvalues_nonneg i)
  have ht : ∑ i, t i ^ 2 = 1 := by
    simp_rw [htsq]
    exact eigenvalues_sum_one σ hσ.isHermitian htrace
  have hdecomp : EnsemblePhase.weightedDensity t ψ = σ := by
    rw [EnsemblePhase.weightedDensity]
    simp_rw [htsq]
    exact (spectral_projector_sum σ hσ.isHermitian).symm
  have h := EnsemblePhase.orthogonal_ensemble_purity_marginal N β hbound t ψ hgram ht
  rw [hdecomp] at h
  exact h

theorem reducedLeft_trace (A : Matrix I E ℂ) :
    Matrix.trace (reducedLeft A) = (hsNormSq A : ℂ) := by
  simp [reducedLeft, crossLeft, Matrix.trace, Matrix.diag,
    Complex.mul_conj, hsNormSq, Complex.sq_norm]

theorem actual_purification_purity {X : Type*} [Fintype X]
    (N : Stinespring I B E) (β : ℝ)
    (hbound : ∀ w : I → ℂ, vectorNormSq w = 1 → purity (N.apply (pureDensity w)) ≤ β)
    (A : Matrix I X ℂ) (hA : hsNormSq A = 1) :
    purity (N.apply (reducedLeft A)) + purity (N.complement (reducedLeft A)) ≤
      β * (1 + purity (reducedLeft A)) := by
  apply mixed_marginal_purity N β hbound (reducedLeft A)
  · rw [reducedLeft, crossLeft_eq_mul]
    exact Matrix.posSemidef_self_mul_conjTranspose A
  · rw [reducedLeft_trace, hA]
    rfl

end QuantumProver.WernerEndpoint.MixedPurity
