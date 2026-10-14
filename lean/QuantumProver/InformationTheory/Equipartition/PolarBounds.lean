import QuantumProver.InformationTheory.Equipartition.Definitions
import QuantumProver.InformationTheory.Equipartition.UniversalEntropyBounds

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace QuantumProver.Equipartition.FiniteModel.Testing

section MatrixTests

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tracePair_nonneg {A Q : CMat ι} (hA : A.PosSemidef) (hQ : Q.PosSemidef) :
    0 ≤ tracePair A Q := by
  have hs : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).posSemidef.1
  have hp : (CFC.sqrt A * Q * CFC.sqrt A).PosSemidef := by
    simpa only [hs] using hQ.mul_mul_conjTranspose_same (CFC.sqrt A)
  have ht : (CFC.sqrt A * Q * CFC.sqrt A).trace = (A * Q).trace := by
    rw [Matrix.trace_mul_cycle, ← pow_two, CFC.sq_sqrt A hA.nonneg]
  exact (Complex.nonneg_iff.mp (ht ▸ hp.trace_nonneg)).1

theorem tracePair_smul_left (c : ℝ) (A Q : CMat ι) :
    tracePair ((c : ℂ) • A) Q = c * tracePair A Q := by
  simp [tracePair, Matrix.smul_mul, Matrix.trace_smul, Complex.mul_re]

theorem tracePair_comm (A B : CMat ι) : tracePair A B = tracePair B A := by
  exact congrArg Complex.re (Matrix.trace_mul_comm A B)

theorem tracePair_sum_left {κ : Type*} (s : Finset κ) (A : κ → CMat ι) (Q : CMat ι) :
    tracePair (∑ k ∈ s, A k) Q = ∑ k ∈ s, tracePair (A k) Q := by
  simp [tracePair, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]

theorem tracePair_sum_right {κ : Type*} (s : Finset κ) (A : CMat ι) (Q : κ → CMat ι) :
    tracePair A (∑ k ∈ s, Q k) = ∑ k ∈ s, tracePair A (Q k) := by
  simp [tracePair, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

theorem tracePair_loewner_mono {A B Q : CMat ι}
    (hAB : LoewnerLE A B) (hQ : Q.PosSemidef) : tracePair A Q ≤ tracePair B Q := by
  have hp := tracePair_nonneg hAB hQ
  simp only [tracePair, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at hp
  unfold tracePair
  linarith

theorem effect_cost_bounds {σ Q : CMat ι} (hσ : σ.PosSemidef) (hQ : IsEffect Q) :
    0 ≤ tracePair σ Q ∧ tracePair σ Q ≤ (Matrix.trace σ).re := by
  constructor
  · exact tracePair_nonneg hσ hQ.1
  · have hp := tracePair_nonneg hσ hQ.2
    simp only [tracePair, Matrix.mul_sub, Matrix.mul_one,
      Matrix.trace_sub, Complex.sub_re] at hp
    unfold tracePair
    linarith

theorem effect_acceptance_bounds {ρ Q : CMat ι} (hρ : IsState ρ) (hQ : IsEffect Q) :
    0 ≤ tracePair ρ Q ∧ tracePair ρ Q ≤ 1 := by
  simpa only [hρ.trace_real] using effect_cost_bounds hρ.1 hQ

theorem testingCosts_bddBelow {ε : ℝ} {ρ σ : CMat ι} (hσ : σ.PosSemidef) :
    BddBelow (testingCosts ε ρ σ) := by
  refine ⟨0, ?_⟩
  rintro b ⟨Q, hQ, hacc, rfl⟩
  exact tracePair_nonneg hσ hQ.1

theorem testingBeta_nonneg {ε : ℝ} (hε : 0 ≤ ε) {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) : 0 ≤ testingBeta ε ρ σ := by
  unfold testingBeta
  apply le_csInf (testingCosts_nonempty hε hρ)
  rintro b ⟨Q, hQ, hacc, rfl⟩
  exact tracePair_nonneg hσ hQ.1

theorem testingBeta_le_cost {ε : ℝ} {ρ σ Q : CMat ι}
    (hσ : σ.PosSemidef) (hQ : IsEffect Q) (hacc : 1 - ε ≤ tracePair ρ Q) :
    testingBeta ε ρ σ ≤ tracePair σ Q := by
  unfold testingBeta
  exact csInf_le (testingCosts_bddBelow hσ) ⟨Q, hQ, hacc, rfl⟩

theorem testingBeta_le_trace {ε : ℝ} (hε : 0 ≤ ε) {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) :
    testingBeta ε ρ σ ≤ (Matrix.trace σ).re := by
  have ha : 1 - ε ≤ tracePair ρ 1 := by
    rw [tracePair_one_right, hρ.trace_real]
    linarith
  simpa only [tracePair_one_right] using testingBeta_le_cost hσ isEffect_one ha

theorem feasible_cost_ge_of_domination {ε c : ℝ} (hc : 0 < c)
    {ρ σ Q : CMat ι} (hdom : LoewnerLE ρ ((c : ℂ) • σ))
    (hQ : IsEffect Q) (hacc : 1 - ε ≤ tracePair ρ Q) :
    (1 - ε) / c ≤ tracePair σ Q := by
  have hm := tracePair_loewner_mono hdom hQ.1
  rw [tracePair_smul_left] at hm
  apply (div_le_iff₀ hc).mpr
  simpa only [mul_comm] using hacc.trans hm

theorem testingBeta_ge_of_domination {ε c : ℝ} (hε : 0 ≤ ε) (hc : 0 < c)
    {ρ σ : CMat ι} (hρ : IsState ρ) (hdom : LoewnerLE ρ ((c : ℂ) • σ)) :
    (1 - ε) / c ≤ testingBeta ε ρ σ := by
  unfold testingBeta
  apply le_csInf (testingCosts_nonempty hε hρ)
  rintro b ⟨Q, hQ, hacc, rfl⟩
  exact feasible_cost_ge_of_domination hc hdom hQ hacc

theorem testingBeta_pos_of_domination {ε c : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hc : 0 < c)
    {ρ σ : CMat ι} (hρ : IsState ρ) (hdom : LoewnerLE ρ ((c : ℂ) • σ)) :
    0 < testingBeta ε ρ σ :=
  (div_pos (sub_pos.mpr hε1) hc).trans_le
    (testingBeta_ge_of_domination hε0 hc hρ hdom)

theorem testingDivergence_eq_of_domination {ε c : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hc : 0 < c)
    {ρ σ : CMat ι} (hρ : IsState ρ) (hdom : LoewnerLE ρ ((c : ℂ) • σ)) :
    testingDivergence ε ρ σ = (-logTwo (testingBeta ε ρ σ) : EReal) := by
  have hp := testingBeta_pos_of_domination hε0 hε1 hc hρ hdom
  simp only [testingDivergence, ne_of_gt hp, if_false]

theorem logTwo_mono_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    logTwo a ≤ logTwo b := by
  unfold logTwo
  exact div_le_div_of_nonneg_right (Real.log_le_log ha hab)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem testingDivergence_lower_of_cost {ε b : ℝ} (hε : 0 ≤ ε) (hb : 0 < b)
    {ρ σ Q : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    (hQ : IsEffect Q) (hacc : 1 - ε ≤ tracePair ρ Q)
    (hcost : tracePair σ Q ≤ b) :
    (-logTwo b : EReal) ≤ testingDivergence ε ρ σ := by
  have hβ : testingBeta ε ρ σ ≤ b := (testingBeta_le_cost hσ hQ hacc).trans hcost
  by_cases hz : testingBeta ε ρ σ = 0
  · simp [testingDivergence, hz]
  have hpos : 0 < testingBeta ε ρ σ :=
    lt_of_le_of_ne (testingBeta_nonneg hε hρ hσ) (Ne.symm hz)
  simp only [testingDivergence, hz, if_false]
  exact_mod_cast neg_le_neg (logTwo_mono_pos hpos hβ)

theorem testingDivergence_upper_of_all_costs {ε b : ℝ} (hε : 0 ≤ ε) (hb : 0 < b)
    {ρ σ : CMat ι} (hρ : IsState ρ)
    (hcost : ∀ Q : CMat ι, IsEffect Q → 1 - ε ≤ tracePair ρ Q →
      b ≤ tracePair σ Q) :
    testingDivergence ε ρ σ ≤ (-logTwo b : EReal) := by
  have hβ : b ≤ testingBeta ε ρ σ := by
    unfold testingBeta
    apply le_csInf (testingCosts_nonempty hε hρ)
    rintro x ⟨Q, hQ, hacc, rfl⟩
    exact hcost Q hQ hacc
  have hpos : 0 < testingBeta ε ρ σ := hb.trans_le hβ
  simp only [testingDivergence, ne_of_gt hpos, if_false]
  exact_mod_cast neg_le_neg (logTwo_mono_pos hb hβ)

theorem logTwo_rpow_two (x : ℝ) : logTwo (Real.rpow 2 x) = x := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  simp only [logTwo, Real.rpow_eq_pow]
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  field_simp [hlog]

theorem testingDivergence_lower_of_threshold_test {ε a : ℝ} (hε : 0 ≤ ε)
    {ρ σ Q : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    (hQ : IsEffect Q) (hacc : 1 - ε ≤ tracePair ρ Q)
    (hcost : tracePair σ Q ≤ Real.rpow 2 (-a)) :
    (a : EReal) ≤ testingDivergence ε ρ σ := by
  have h := testingDivergence_lower_of_cost hε
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-a))
      hρ hσ hQ hacc hcost
  have hl := logTwo_rpow_two (-a)
  simp only [Real.rpow_eq_pow] at hl
  simpa only [hl, EReal.coe_neg, neg_neg] using h

end MatrixTests

section MatrixSubspaceTests

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def projectionMatrix (K : Submodule ℂ (EuclideanSpace ℂ ι)) : CMat ι :=
  (K.starProjection : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι).toMatrix
    (EuclideanSpace.basisFun ι ℂ).toBasis (EuclideanSpace.basisFun ι ℂ).toBasis

theorem projectionMatrix_posSemidef (K : Submodule ℂ (EuclideanSpace ℂ ι)) :
    (projectionMatrix K).PosSemidef := by
  unfold projectionMatrix
  exact (LinearMap.posSemidef_toMatrix_iff (EuclideanSpace.basisFun ι ℂ)).mpr
    (Submodule.isSymmetricProjection_starProjection K).isPositive

theorem projectionMatrix_orthogonal (K : Submodule ℂ (EuclideanSpace ℂ ι)) :
    projectionMatrix Kᗮ = 1 - projectionMatrix K := by
  unfold projectionMatrix
  rw [Submodule.starProjection_orthogonal]
  simp [← OrthonormalBasis.coe_toBasis, Module.Basis.toMatrix_self]

theorem projectionMatrix_isEffect (K : Submodule ℂ (EuclideanSpace ℂ ι)) :
    IsEffect (projectionMatrix K) := by
  refine ⟨projectionMatrix_posSemidef K, ?_⟩
  rw [← projectionMatrix_orthogonal]
  exact projectionMatrix_posSemidef Kᗮ

theorem projectionMatrix_toEuclideanLin (K : Submodule ℂ (EuclideanSpace ℂ ι)) :
    (projectionMatrix K).toEuclideanLin =
      (K.starProjection : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.toLin_toMatrix
    (EuclideanSpace.basisFun ι ℂ).toBasis
    (EuclideanSpace.basisFun ι ℂ).toBasis
    (K.starProjection : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)

def quadraticForm (A : CMat ι) (v : EuclideanSpace ℂ ι) : ℝ :=
  (inner ℂ v (A.toEuclideanLin v)).re

theorem tracePair_rankOne (A : CMat ι) (v : EuclideanSpace ℂ ι) :
    tracePair A (Matrix.vecMulVec (⇑v) (star (⇑v))) = quadraticForm A v := by
  simp only [tracePair, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, quadraticForm,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]

theorem spectral_rankOne_decomposition {A : CMat ι} (hA : A.IsHermitian) :
    A = ∑ i, (hA.eigenvalues i : ℂ) •
      Matrix.vecMulVec (⇑(hA.eigenvectorBasis i)) (star (⇑(hA.eigenvectorBasis i))) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, RCLike.ofReal_eq_complex_ofReal, Function.comp_def]
  change ((hA.eigenvectorUnitary : CMat ι) *
    Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
      (hA.eigenvectorUnitary : CMat ι)ᴴ) = _
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    Pi.star_apply, hA.eigenvectorUnitary_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem quadraticForm_rankOne (u v : EuclideanSpace ℂ ι) :
    quadraticForm (Matrix.vecMulVec (⇑u) (star (⇑u))) v = ‖inner ℂ u v‖ ^ 2 := by
  have hm : (Matrix.vecMulVec (⇑u) (star (⇑u))).toEuclideanLin =
      (InnerProductSpace.rankOne ℂ u u :
        EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) := by
    have h := congrArg Matrix.toEuclideanLin
      (InnerProductSpace.symm_toEuclideanLin_rankOne u u)
    simpa only [LinearEquiv.apply_symm_apply] using h.symm
  rw [quadraticForm, hm]
  change (inner ℂ v ((inner ℂ u v) • u)).re = _
  rw [inner_smul_right]
  change RCLike.re (inner ℂ u v * inner ℂ v u) = _
  rw [inner_mul_symm_re_eq_norm]
  rw [norm_mul]
  have hn : ‖inner ℂ v u‖ = ‖inner ℂ u v‖ := by
    rw [← inner_conj_symm v u]
    exact norm_star _
  rw [hn, pow_two]

theorem quadraticForm_eq_spectral_sum {A : CMat ι} (hA : A.IsHermitian)
    (v : EuclideanSpace ℂ ι) :
    quadraticForm A v =
      ∑ i, hA.eigenvalues i * ‖inner ℂ (hA.eigenvectorBasis i) v‖ ^ 2 := by
  rw [← tracePair_rankOne]
  conv_lhs => rw [spectral_rankOne_decomposition hA, tracePair_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tracePair_smul_left, tracePair_rankOne, quadraticForm_rankOne]

theorem tracePair_eq_spectral_quadraticForm {A : CMat ι} (hA : A.IsHermitian)
    (Q : CMat ι) :
    tracePair A Q = ∑ i, hA.eigenvalues i * quadraticForm Q (hA.eigenvectorBasis i) := by
  conv_lhs => rw [spectral_rankOne_decomposition hA]
  simp only [tracePair_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tracePair_smul_left, tracePair_comm, tracePair_rankOne]

theorem quadraticForm_projection (K : Submodule ℂ (EuclideanSpace ℂ ι))
    (v : EuclideanSpace ℂ ι) :
    quadraticForm (projectionMatrix K) v = ‖K.orthogonalProjectionOnto v‖ ^ 2 := by
  rw [quadraticForm, projectionMatrix_toEuclideanLin]
  change RCLike.re (inner ℂ v (K.starProjection v)) = _
  rw [inner_re_symm]
  exact Submodule.re_inner_starProjection_eq_normSq K v

theorem projection_distance_le (K : Submodule ℂ (EuclideanSpace ℂ ι))
    (u v : EuclideanSpace ℂ ι) (hv : v ∈ K) :
    ‖u - K.starProjection u‖ ≤ ‖u - v‖ := by
  rw [Submodule.starProjection_minimal]
  apply ciInf_le (c := (⟨v, hv⟩ : K))
  refine ⟨0, ?_⟩
  rintro b ⟨x, rfl⟩
  exact norm_nonneg _

theorem projection_rejection_eq {ρ : CMat ι} (hρ : IsState ρ)
    (K : Submodule ℂ (EuclideanSpace ℂ ι)) :
    1 - tracePair ρ (projectionMatrix K) =
      ∑ i, hρ.1.1.eigenvalues i *
        ‖hρ.1.1.eigenvectorBasis i - K.starProjection (hρ.1.1.eigenvectorBasis i)‖ ^ 2 := by
  have hsum : ∑ i, hρ.1.1.eigenvalues i = 1 := by
    rw [← Spectral.trace_eq_sum_eigenvalues_re hρ.1.1, hρ.trace_real]
  rw [tracePair_eq_spectral_quadraticForm hρ.1.1]
  rw [← hsum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [quadraticForm_projection]
  have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection (hρ.1.1.eigenvectorBasis i) K
  have hn : ‖hρ.1.1.eigenvectorBasis i‖ = 1 := hρ.1.1.eigenvectorBasis.orthonormal.1 i
  rw [Submodule.starProjection_orthogonal_val] at hp
  have hp' : 1 = ‖K.orthogonalProjectionOnto (hρ.1.1.eigenvectorBasis i)‖ ^ 2 +
      ‖hρ.1.1.eigenvectorBasis i - K.starProjection (hρ.1.1.eigenvectorBasis i)‖ ^ 2 := by
    change 1 = ‖K.starProjection (hρ.1.1.eigenvectorBasis i)‖ ^ 2 +
      ‖hρ.1.1.eigenvectorBasis i - K.starProjection (hρ.1.1.eigenvectorBasis i)‖ ^ 2
    simpa only [hn, one_pow] using hp
  have hres : 1 - ‖K.orthogonalProjectionOnto (hρ.1.1.eigenvectorBasis i)‖ ^ 2 =
      ‖hρ.1.1.eigenvectorBasis i - K.starProjection (hρ.1.1.eigenvectorBasis i)‖ ^ 2 := by
    linarith only [hp']
  calc
    _ = hρ.1.1.eigenvalues i *
        (1 - ‖K.orthogonalProjectionOnto (hρ.1.1.eigenvectorBasis i)‖ ^ 2) := by ring
    _ = _ := by rw [hres]

theorem projection_rejection_le_distances {ρ : CMat ι} (hρ : IsState ρ)
    (K : Submodule ℂ (EuclideanSpace ℂ ι)) (f : ι → EuclideanSpace ℂ ι)
    (hf : ∀ i, f i ∈ K) :
    1 - tracePair ρ (projectionMatrix K) ≤
      ∑ i, hρ.1.1.eigenvalues i * ‖hρ.1.1.eigenvectorBasis i - f i‖ ^ 2 := by
  rw [projection_rejection_eq hρ]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hρ.1.eigenvalues_nonneg i)
  gcongr
  exact projection_distance_le K _ _ (hf i)

theorem projectionMatrix_eq_sum_rankOne {κ : Type*} [Fintype κ]
    (K : Submodule ℂ (EuclideanSpace ℂ ι)) (b : OrthonormalBasis κ ℂ K) :
    projectionMatrix K = ∑ j, Matrix.vecMulVec (⇑(b j : EuclideanSpace ℂ ι))
      (star (⇑(b j : EuclideanSpace ℂ ι))) := by
  unfold projectionMatrix
  rw [b.starProjection_eq_sum_rankOne]
  simp only [ContinuousLinearMap.toLinearMap_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hr : ((EuclideanSpace.basisFun ι ℂ).toBasis.repr
      (b j : EuclideanSpace ℂ ι) : ι → ℂ) = ⇑(b j : EuclideanSpace ℂ ι) := by
    ext i
    rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  have hr' : (EuclideanSpace.basisFun ι ℂ).repr (b j : EuclideanSpace ℂ ι) =
      (b j : EuclideanSpace ℂ ι) := by
    ext i
    rfl
  simpa only [hr, hr'] using
    InnerProductSpace.toMatrix_rankOne (b j : EuclideanSpace ℂ ι)
      (b j : EuclideanSpace ℂ ι) (EuclideanSpace.basisFun ι ℂ).toBasis
        (EuclideanSpace.basisFun ι ℂ)

theorem projection_cost_eq_sum {κ : Type*} [Fintype κ]
    (σ : CMat ι) (K : Submodule ℂ (EuclideanSpace ℂ ι))
    (b : OrthonormalBasis κ ℂ K) :
    tracePair σ (projectionMatrix K) =
      ∑ j, quadraticForm σ (b j : EuclideanSpace ℂ ι) := by
  rw [projectionMatrix_eq_sum_rankOne K b]
  simp only [tracePair_sum_right, tracePair_rankOne]

theorem projection_cost_le_of_basis {κ : Type*} [Fintype κ]
    (σ : CMat ι) (K : Submodule ℂ (EuclideanSpace ℂ ι))
    (b : OrthonormalBasis κ ℂ K) (p : κ → ℝ)
    (hp : ∀ j, quadraticForm σ (b j : EuclideanSpace ℂ ι) ≤ p j) :
    tracePair σ (projectionMatrix K) ≤ ∑ j, p j := by
  rw [projection_cost_eq_sum σ K b]
  exact Finset.sum_le_sum fun j hj => hp j

def lowSpectralSubspace {σ : CMat ι} (hσ : σ.IsHermitian) (a : ℝ) :
    Submodule ℂ (EuclideanSpace ℂ ι) :=
  Submodule.span ℂ (hσ.eigenvectorBasis '' {j | hσ.eigenvalues j ≤ a})

theorem lowSpectralSubspace_mono {σ : CMat ι} (hσ : σ.IsHermitian) :
    Monotone (lowSpectralSubspace hσ) := by
  intro a b hab
  apply Submodule.span_mono
  apply Set.image_mono
  intro j hj
  exact hj.trans hab

theorem inner_eq_zero_above_lowSpectralSubspace {σ : CMat ι} (hσ : σ.IsHermitian)
    {a : ℝ} {v : EuclideanSpace ℂ ι} (hv : v ∈ lowSpectralSubspace hσ a)
    {j : ι} (hj : a < hσ.eigenvalues j) : inner ℂ (hσ.eigenvectorBasis j) v = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · rintro x ⟨i, hi, rfl⟩
    have hji : j ≠ i := by
      intro he
      subst i
      exact (not_le_of_gt hj) hi
    exact hσ.eigenvectorBasis.orthonormal.2 hji
  · simp
  · intro x y hx hy hxi hyi
    simp [inner_add_right, hxi, hyi]
  · intro c x hx hxi
    simp [inner_smul_right, hxi]

theorem quadraticForm_le_lowSpectralSubspace {σ : CMat ι} (hσ : σ.IsHermitian)
    {a : ℝ} {v : EuclideanSpace ℂ ι} (hv : v ∈ lowSpectralSubspace hσ a) :
    quadraticForm σ v ≤ a * ‖v‖ ^ 2 := by
  rw [quadraticForm_eq_spectral_sum hσ,
    ← hσ.eigenvectorBasis.sum_sq_norm_inner_right v, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hc : hσ.eigenvalues j ≤ a
  · exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  · rw [inner_eq_zero_above_lowSpectralSubspace hσ hv (lt_of_not_ge hc)]
    simp

theorem lowSpectralSubspace_projection_eigenvector {σ : CMat ι}
    (hσ : σ.IsHermitian) (a : ℝ) (j : ι) :
    (lowSpectralSubspace hσ a).starProjection (hσ.eigenvectorBasis j) =
      if hσ.eigenvalues j ≤ a then hσ.eigenvectorBasis j else 0 := by
  classical
  split_ifs with hj
  · apply Submodule.starProjection_eq_self_iff.mpr
    exact Submodule.subset_span ⟨j, hj, rfl⟩
  · apply (Submodule.starProjection_apply_eq_zero_iff
      (K := lowSpectralSubspace hσ a)).mpr
    rw [Submodule.mem_orthogonal']
    intro v hv
    exact inner_eq_zero_above_lowSpectralSubspace hσ hv (lt_of_not_ge hj)

theorem inner_lowSpectralSubspace_residual {σ : CMat ι}
    (hσ : σ.IsHermitian) (a : ℝ) (v : EuclideanSpace ℂ ι) (j : ι) :
    inner ℂ (hσ.eigenvectorBasis j)
      (v - (lowSpectralSubspace hσ a).starProjection v) =
        if hσ.eigenvalues j ≤ a then 0 else inner ℂ (hσ.eigenvectorBasis j) v := by
  classical
  rw [inner_sub_right, ← Submodule.inner_starProjection_left_eq_right,
    lowSpectralSubspace_projection_eigenvector]
  split_ifs <;> simp

theorem lowSpectralSubspace_residual_norm_sq {σ : CMat ι}
    (hσ : σ.IsHermitian) (a : ℝ) (v : EuclideanSpace ℂ ι) :
    ‖v - (lowSpectralSubspace hσ a).starProjection v‖ ^ 2 =
      ∑ j, if hσ.eigenvalues j ≤ a then 0 else ‖inner ℂ (hσ.eigenvectorBasis j) v‖ ^ 2 := by
  classical
  rw [← hσ.eigenvectorBasis.sum_sq_norm_inner_right]
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_lowSpectralSubspace_residual]
  split_ifs <;> simp

end MatrixSubspaceTests

section NestedGramSchmidt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {m : ℕ}

theorem gramSchmidtNormed_mem_prefix (f : Fin m → E) (i : Fin m) :
    InnerProductSpace.gramSchmidtNormed ℂ f i ∈
      Submodule.span ℂ (f '' Set.Iic i) := by
  unfold InnerProductSpace.gramSchmidtNormed
  apply Submodule.smul_mem
  exact InnerProductSpace.gramSchmidt_mem_span ℂ f le_rfl

theorem gramSchmidtNormed_mem_nested (f : Fin m → E) (K : Fin m → Submodule ℂ E)
    (hK : Monotone K) (hf : ∀ i, f i ∈ K i) (i : Fin m) :
    InnerProductSpace.gramSchmidtNormed ℂ f i ∈ K i := by
  apply (Submodule.span_le.mpr ?_) (gramSchmidtNormed_mem_prefix f i)
  rintro x ⟨j, hji, rfl⟩
  exact hK hji (hf j)

theorem span_nonzero_range_eq (v : Fin m → E) :
    Submodule.span ℂ (Set.range fun i : {i // v i ≠ 0} => v i) =
      Submodule.span ℂ (Set.range v) := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    by_cases hi : v i = 0
    · rw [hi]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

abbrev GramSchmidtIndex (f : Fin m → E) : Type :=
  {i : Fin m // InnerProductSpace.gramSchmidtNormed ℂ f i ≠ 0}

noncomputable instance gramSchmidtIndex_fintype (f : Fin m → E) :
    Fintype (GramSchmidtIndex f) := by
  classical
  unfold GramSchmidtIndex
  infer_instance

def gramSchmidtRetained (f : Fin m → E) (i : GramSchmidtIndex f) :
    Submodule.span ℂ (Set.range f) :=
  ⟨InnerProductSpace.gramSchmidtNormed ℂ f i,
    (Submodule.span_mono (Set.image_subset_range f (Set.Iic (i : Fin m))))
      (gramSchmidtNormed_mem_prefix f i)⟩

theorem gramSchmidtRetained_orthonormal (f : Fin m → E) :
    Orthonormal ℂ (gramSchmidtRetained f) := by
  have hon := InnerProductSpace.gramSchmidtNormed_orthonormal' (𝕜 := ℂ) f
  refine ⟨fun i => hon.1 i, fun i j hij => hon.2 hij⟩

theorem gramSchmidtRetained_span (f : Fin m → E) :
    Submodule.span ℂ (Set.range (gramSchmidtRetained f)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff
    (Submodule.span ℂ (Set.range f))
      (fun i : GramSchmidtIndex f => (gramSchmidtRetained f i).property)).mpr
  change Submodule.span ℂ (Set.range fun i :
    {i // InnerProductSpace.gramSchmidtNormed ℂ f i ≠ 0} =>
      InnerProductSpace.gramSchmidtNormed ℂ f i) = Submodule.span ℂ (Set.range f)
  rw [span_nonzero_range_eq, InnerProductSpace.span_gramSchmidtNormed_range,
    InnerProductSpace.span_gramSchmidt]

def gramSchmidtBasis (f : Fin m → E) :
    OrthonormalBasis (GramSchmidtIndex f) ℂ (Submodule.span ℂ (Set.range f)) :=
  OrthonormalBasis.mk (gramSchmidtRetained_orthonormal f)
    (by rw [gramSchmidtRetained_span])

theorem gramSchmidtBasis_coe (f : Fin m → E) (i : GramSchmidtIndex f) :
    (gramSchmidtBasis f i : E) = InnerProductSpace.gramSchmidtNormed ℂ f i := by
  simp [gramSchmidtBasis, gramSchmidtRetained]

theorem gramSchmidt_projection_cost_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : CMat ι) (f : Fin m → EuclideanSpace ℂ ι)
    (K : Fin m → Submodule ℂ (EuclideanSpace ℂ ι))
    (hK : Monotone K) (hf : ∀ i, f i ∈ K i) (w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hquad : ∀ i v, v ∈ K i → quadraticForm σ v ≤ w i * ‖v‖ ^ 2) :
    tracePair σ (projectionMatrix (Submodule.span ℂ (Set.range f))) ≤ ∑ i, w i := by
  classical
  have hc : tracePair σ (projectionMatrix (Submodule.span ℂ (Set.range f))) ≤
      ∑ j : GramSchmidtIndex f, w j := by
    apply projection_cost_le_of_basis σ _ (gramSchmidtBasis f) (fun j => w j)
    intro j
    have hj : (gramSchmidtBasis f j : EuclideanSpace ℂ ι) ∈ K j := by
      rw [gramSchmidtBasis_coe]
      exact gramSchmidtNormed_mem_nested f K hK hf j
    have hn : ‖(gramSchmidtBasis f j : EuclideanSpace ℂ ι)‖ = 1 :=
      (gramSchmidtBasis f).orthonormal.1 j
    simpa only [hn, one_pow, mul_one] using
      hquad j (gramSchmidtBasis f j : EuclideanSpace ℂ ι) hj
  refine hc.trans ?_
  have hfilter : (∑ j : GramSchmidtIndex f, w j) =
      ∑ i ∈ Finset.univ.filter
        (fun i => InnerProductSpace.gramSchmidtNormed ℂ f i ≠ 0), w i := by
    exact (Finset.sum_subtype _ (by simp) w).symm
  rw [hfilter]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i hi hni => hw i)

end NestedGramSchmidt

section MatrixThresholdTest

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_monotone_enumeration (p : ι → ℝ) :
    ∃ e : Fin (Fintype.card ι) ≃ ι, Monotone (p ∘ e) := by
  classical
  let index := Fintype.equivFin ι
  let tag : ι → ℝ ×ₗ Fin (Fintype.card ι) := fun i => toLex (p i, index i)
  have hinj : Function.Injective tag := by
    intro i j hij
    apply index.injective
    exact congrArg (fun x => (ofLex x).2) hij
  letI : LinearOrder ι := LinearOrder.lift' tag hinj
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  have h := e.monotone hij
  change tag (e i) ≤ tag (e j) at h
  exact (Prod.Lex.le_iff'.mp h).1

def thresholdVector {ρ σ : CMat ι} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (a : ℝ) (i : ι) : EuclideanSpace ℂ ι :=
  (lowSpectralSubspace hσ (hρ.eigenvalues i * Real.rpow 2 (-a))).starProjection
    (hρ.eigenvectorBasis i)

def thresholdSubspace {ρ σ : CMat ι} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (a : ℝ) : Submodule ℂ (EuclideanSpace ℂ ι) :=
  Submodule.span ℂ (Set.range (thresholdVector hρ hσ a))

theorem threshold_projection_cost_le {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.IsHermitian) (a : ℝ) :
    tracePair σ (projectionMatrix (thresholdSubspace hρ.1.1 hσ a)) ≤
      Real.rpow 2 (-a) := by
  classical
  obtain ⟨e, he⟩ := exists_monotone_enumeration hρ.1.1.eigenvalues
  let f := thresholdVector hρ.1.1 hσ a
  let K := fun i : Fin (Fintype.card ι) =>
    lowSpectralSubspace hσ (hρ.1.1.eigenvalues (e i) * Real.rpow 2 (-a))
  have hK : Monotone K := by
    intro i j hij
    apply lowSpectralSubspace_mono hσ
    exact mul_le_mul_of_nonneg_right (he hij)
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-a)).le
  have hf : ∀ i, (f ∘ e) i ∈ K i := by
    intro i
    exact Submodule.starProjection_apply_mem _ _
  have hc := gramSchmidt_projection_cost_le σ (f ∘ e) K hK hf
    (fun i => hρ.1.1.eigenvalues (e i) * Real.rpow 2 (-a))
    (fun i => mul_nonneg (hρ.1.eigenvalues_nonneg (e i))
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-a)).le)
    (fun i v hv => quadraticForm_le_lowSpectralSubspace hσ hv)
  have hrange : Set.range (f ∘ e) = Set.range f := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp⟩
  rw [hrange, ← Finset.sum_mul, e.sum_comp hρ.1.1.eigenvalues,
    ← Spectral.trace_eq_sum_eigenvalues_re hρ.1.1, hρ.trace_real, one_mul] at hc
  exact hc

theorem threshold_projection_rejection_le {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.IsHermitian) (a : ℝ) :
    1 - tracePair ρ (projectionMatrix (thresholdSubspace hρ.1.1 hσ a)) ≤
      ∑ i, hρ.1.1.eigenvalues i *
        ∑ j, if hσ.eigenvalues j ≤ hρ.1.1.eigenvalues i * Real.rpow 2 (-a)
          then 0 else ‖inner ℂ (hσ.eigenvectorBasis j) (hρ.1.1.eigenvectorBasis i)‖ ^ 2 := by
  have h := projection_rejection_le_distances hρ
    (thresholdSubspace hρ.1.1 hσ a) (thresholdVector hρ.1.1 hσ a)
    (fun i => Submodule.subset_span ⟨i, rfl⟩)
  simpa only [thresholdVector, lowSpectralSubspace_residual_norm_sq] using h

theorem spectral_overlap_eq_inner {ρ σ : CMat ι}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (i j : ι) :
    Spectral.overlapWeight (Spectral.overlapUnitary hρ hσ) i j =
      ‖inner ℂ (hσ.eigenvectorBasis j) (hρ.eigenvectorBasis i)‖ ^ 2 := by
  have he : (Spectral.overlapUnitary hρ hσ : CMat ι) i j =
      inner ℂ (hρ.eigenvectorBasis i) (hσ.eigenvectorBasis j) := by
    change (((hρ.eigenvectorUnitary : CMat ι)ᴴ *
      (hσ.eigenvectorUnitary : CMat ι)) i j) = _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      hρ.eigenvectorUnitary_apply, hσ.eigenvectorUnitary_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, Complex.star_def]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [Spectral.overlapWeight, he, Complex.normSq_eq_norm_sq, norm_inner_symm]

theorem logTwo_mul_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    logTwo (p * q) = logTwo p + logTwo q := by
  unfold logTwo
  rw [Real.log_mul hp.ne' hq.ne', add_div]

theorem logTwo_lt_logTwo_pos {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    logTwo p < logTwo q := by
  unfold logTwo
  exact div_lt_div_of_pos_right (Real.log_lt_log hp hpq)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))

theorem threshold_projection_rejection_le_nsExpectation {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (a : ℝ) :
    1 - tracePair ρ (projectionMatrix (thresholdSubspace hρ.1.1 hσ.1 a)) ≤
      nsExpectation ρ σ (fun z => if nsLikelihood ρ σ z < a then 1 else 0) := by
  apply (threshold_projection_rejection_le hρ hσ.1 a).trans
  unfold nsExpectation
  rw [Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  change hρ.1.1.eigenvalues i *
    (if hσ.1.eigenvalues j ≤ hρ.1.1.eigenvalues i * Real.rpow 2 (-a) then 0
      else ‖inner ℂ (hσ.1.eigenvectorBasis j) (hρ.1.1.eigenvectorBasis i)‖ ^ 2) ≤
        nsWeight ρ σ (i, j) * (if nsLikelihood ρ σ (i, j) < a then 1 else 0)
  have hweight : 0 ≤ nsWeight ρ σ (i, j) := nsWeight_nonneg hρ.1 (i, j)
  by_cases hcut : hσ.1.eigenvalues j ≤ hρ.1.1.eigenvalues i * Real.rpow 2 (-a)
  · rw [if_pos hcut, mul_zero]
    exact mul_nonneg hweight (by split_ifs <;> norm_num)
  by_cases hp : hρ.1.1.eigenvalues i = 0
  · simp [hp, nsWeight_eq_overlap hρ.1.1 hσ.1]
  have hppos : 0 < hρ.1.1.eigenvalues i :=
    lt_of_le_of_ne (hρ.1.eigenvalues_nonneg i) (Ne.symm hp)
  have hpow : 0 < Real.rpow 2 (-a) := Real.rpow_pos_of_pos (by norm_num) _
  have hbad : nsLikelihood ρ σ (i, j) < a := by
    have hl := logTwo_lt_logTwo_pos (mul_pos hppos hpow) (lt_of_not_ge hcut)
    rw [logTwo_mul_pos hppos hpow, logTwo_rpow_two] at hl
    simp only [nsLikelihood, spectrumValue_of_isHermitian hρ.1.1,
      spectrumValue_of_isHermitian hσ.1]
    linarith
  rw [if_neg hcut, if_pos hbad, mul_one, nsWeight_eq_overlap hρ.1.1 hσ.1,
    spectral_overlap_eq_inner hρ.1.1 hσ.1]

theorem nsExpectation_indicator_eq_mass {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (P : ι × ι → Prop) [DecidablePred P] :
    nsExpectation ρ σ (fun z => if P z then 1 else 0) =
      (nsLaw ρ σ hρ hσ).mass (Finset.univ.filter P) := by
  classical
  simp only [nsExpectation, FiniteLaw.mass, nsLaw, Finset.sum_filter,
    mul_ite, mul_one, mul_zero]

theorem threshold_projection_rejection_le_nsMass {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (a : ℝ) :
    1 - tracePair ρ (projectionMatrix (thresholdSubspace hρ.1.1 hσ.1 a)) ≤
      (nsLaw ρ σ hρ hσ).mass (Finset.univ.filter (fun z => nsLikelihood ρ σ z < a)) := by
  rw [← nsExpectation_indicator_eq_mass hρ hσ]
  exact threshold_projection_rejection_le_nsExpectation hρ hσ a

theorem exists_ns_threshold_test {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (a : ℝ) :
    ∃ Q : CMat ι, IsEffect Q ∧
      1 - tracePair ρ Q ≤
        (nsLaw ρ σ hρ hσ).mass (Finset.univ.filter (fun z => nsLikelihood ρ σ z < a)) ∧
      tracePair σ Q ≤ Real.rpow 2 (-a) := by
  exact ⟨projectionMatrix (thresholdSubspace hρ.1.1 hσ.1 a),
    projectionMatrix_isEffect _, threshold_projection_rejection_le_nsMass hρ hσ a,
    threshold_projection_cost_le hρ hσ.1 a⟩

theorem testingDivergence_lower_of_nsTail {ρ σ : CMat ι} {ε a : ℝ}
    (hε : 0 ≤ ε) (hρ : IsState ρ) (hσ : σ.PosSemidef)
    (htail : (nsLaw ρ σ hρ hσ).mass
      (Finset.univ.filter (fun z => nsLikelihood ρ σ z < a)) ≤ ε) :
    (a : EReal) ≤ testingDivergence ε ρ σ := by
  obtain ⟨Q, hQ, hreject, hcost⟩ := exists_ns_threshold_test hρ hσ a
  apply testingDivergence_lower_of_threshold_test hε hρ hσ hQ _ hcost
  linarith

theorem testingDivergence_lower_of_nsSecondMoment {ρ σ : CMat ι} {ε c a : ℝ}
    (hε : 0 ≤ ε) (ha : 0 < a) (hρ : IsState ρ) (hσ : σ.PosSemidef)
    (hbudget : (nsLaw ρ σ hρ hσ).secondMoment (nsLikelihood ρ σ) c ≤ ε * a ^ 2) :
    ((c - a : ℝ) : EReal) ≤ testingDivergence ε ρ σ := by
  apply testingDivergence_lower_of_nsTail hε hρ hσ
  exact (nsLaw ρ σ hρ hσ).mass_le_of_secondMoment
    (FiniteLaw.lowerTail (nsLikelihood ρ σ) c a) (nsLikelihood ρ σ) c ha
    (by
      intro z hz
      have hb : nsLikelihood ρ σ z < c - a := (Finset.mem_filter.mp hz).2
      linarith [neg_le_abs (nsLikelihood ρ σ z - c)]) hbudget

theorem testingDivergence_lower_of_nsWeightedMoment {ρ σ : CMat ι} {ε c a t : ℝ}
    (hε : 0 ≤ ε) (ha : 0 < a) (ht : 0 ≤ t)
    (hρ : IsState ρ) (hσ : σ.PosSemidef)
    (hbudget : nsWeightedMoment ρ σ c t ≤ ε * a ^ 2) :
    ((c - a : ℝ) : EReal) ≤ testingDivergence ε ρ σ := by
  apply testingDivergence_lower_of_nsSecondMoment hε ha hρ hσ
  exact ((nsLaw ρ σ hρ hσ).secondMoment_le_weightedSecondMoment
    (nsLikelihood ρ σ) c ht).trans hbudget

theorem testingDivergence_lower_of_nsLaplace {ρ σ : CMat ι} {ε c a t : ℝ}
    (hε : 0 ≤ ε) (ht : 0 ≤ t) (hρ : IsState ρ) (hσ : σ.PosSemidef)
    (hs : SupportLE ρ σ) (hα : 0 < 1 - t / Real.log 2)
    (hbudget : Real.exp (-t * a) *
      (Real.exp (t * c) * petzTrace ρ σ (1 - t / Real.log 2)) ≤ ε) :
    ((c - a : ℝ) : EReal) ≤ testingDivergence ε ρ σ := by
  apply testingDivergence_lower_of_nsTail hε hρ hσ
  have hm := (nsLaw ρ σ hρ hσ).lowerTail_mass_le_laplace
    (nsLikelihood ρ σ) c a ht
  rw [nsLaw_laplace_centered ρ σ hρ hσ hs c t hα] at hm
  exact hm.trans hbudget

end MatrixThresholdTest

section MatrixMeasurementTest

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}

theorem measurementMass_nonneg (M : FinitePOVM ι L) {ρ : CMat ι}
    (hρ : ρ.PosSemidef) (i : Fin L) : 0 ≤ measurementMass M ρ i :=
  tracePair_nonneg hρ (M.positive i)

theorem measurementMass_sum (M : FinitePOVM ι L) {ρ : CMat ι} (hρ : IsState ρ) :
    ∑ i, measurementMass M ρ i = 1 := by
  change (∑ i, tracePair ρ (M.outcome i)) = 1
  rw [← tracePair_sum_right, M.sum_outcome, tracePair_one_right, hρ.trace_real]

theorem povm_subset_isEffect (M : FinitePOVM ι L) (S : Finset (Fin L)) :
    IsEffect (∑ i ∈ S, M.outcome i) := by
  constructor
  · exact (Finset.sum_nonneg (fun i hi => (M.positive i).nonneg)).posSemidef
  · rw [← M.sum_outcome, ← Finset.sum_sdiff_eq_sub (Finset.subset_univ S)]
    exact (Finset.sum_nonneg (fun i hi => (M.positive i).nonneg)).posSemidef

theorem scalar_bad_mass_le_renyi {p q α a : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hα : 0 < α) (hα1 : α < 1) (hbad : p ≤ Real.rpow 2 a * q) :
    p ≤ Real.rpow 2 (a * (1 - α)) *
      (Real.rpow p α * Real.rpow q (1 - α)) := by
  simp only [Real.rpow_eq_pow] at *
  have hsplit : p = p ^ α * p ^ (1 - α) := by
    rw [← Real.rpow_add' hp (by ring_nf; norm_num : α + (1 - α) ≠ 0)]
    convert (Real.rpow_one p).symm using 1 <;> ring
  have hpow := Real.rpow_le_rpow hp hbad (sub_nonneg.mpr hα1.le)
  calc
    p = p ^ α * p ^ (1 - α) := hsplit
    _ ≤ p ^ α * (2 ^ a * q) ^ (1 - α) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hp _)
    _ = _ := by
      rw [Real.mul_rpow (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) a).le hq,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring

def measurementThresholdSet (M : FinitePOVM ι L) (ρ σ : CMat ι) (a : ℝ) :
    Finset (Fin L) :=
  Finset.univ.filter (fun i => Real.rpow 2 a * measurementMass M σ i ≤ measurementMass M ρ i)

def measurementThresholdEffect (M : FinitePOVM ι L) (ρ σ : CMat ι) (a : ℝ) : CMat ι :=
  ∑ i ∈ measurementThresholdSet M ρ σ a, M.outcome i

theorem measurementThresholdEffect_isEffect (M : FinitePOVM ι L)
    (ρ σ : CMat ι) (a : ℝ) : IsEffect (measurementThresholdEffect M ρ σ a) :=
  povm_subset_isEffect M _

theorem measurementThresholdEffect_cost_le (M : FinitePOVM ι L)
    {ρ σ : CMat ι} (hρ : IsState ρ) (a : ℝ) :
    tracePair σ (measurementThresholdEffect M ρ σ a) ≤ Real.rpow 2 (-a) := by
  have hpow : 0 < Real.rpow 2 a := Real.rpow_pos_of_pos (by norm_num) _
  have hc : tracePair σ (measurementThresholdEffect M ρ σ a) ≤
      (∑ i ∈ measurementThresholdSet M ρ σ a, measurementMass M ρ i) * Real.rpow 2 (-a) := by
    rw [measurementThresholdEffect, tracePair_sum_right, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hgood := (Finset.mem_filter.mp hi).2
    have hm : measurementMass M σ i ≤ measurementMass M ρ i / Real.rpow 2 a :=
      (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hgood)
    simpa only [measurementMass, div_eq_mul_inv, Real.rpow_eq_pow,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] using hm
  have hs : (∑ i ∈ measurementThresholdSet M ρ σ a, measurementMass M ρ i) ≤ 1 := by
    rw [← measurementMass_sum M hρ]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i hi hni => measurementMass_nonneg M hρ.1 i)
  have hlast := mul_le_mul_of_nonneg_right hs
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-a)).le
  exact hc.trans (by simpa only [one_mul, Real.rpow_eq_pow] using hlast)

theorem measurementThresholdEffect_rejection_le (M : FinitePOVM ι L)
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (a : ℝ) :
    1 - tracePair ρ (measurementThresholdEffect M ρ σ a) ≤
      Real.rpow 2 (a * (1 - α)) *
        classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α := by
  let bad := Finset.univ.filter (fun i =>
    ¬(Real.rpow 2 a * measurementMass M σ i ≤ measurementMass M ρ i))
  have hr : 1 - tracePair ρ (measurementThresholdEffect M ρ σ a) =
      ∑ i ∈ bad, measurementMass M ρ i := by
    have hs := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => Real.rpow 2 a * measurementMass M σ i ≤ measurementMass M ρ i)
        (measurementMass M ρ)
    rw [measurementMass_sum M hρ] at hs
    change 1 - tracePair ρ (∑ i ∈ measurementThresholdSet M ρ σ a, M.outcome i) = _
    rw [tracePair_sum_right]
    exact (eq_sub_iff_add_eq.mpr (by simpa only [bad, measurementThresholdSet,
      measurementMass, add_comm] using hs)).symm
  rw [hr, classicalRenyiTrace, Finset.mul_sum]
  calc
    (∑ i ∈ bad, measurementMass M ρ i) ≤ ∑ i ∈ bad,
        Real.rpow 2 (a * (1 - α)) *
          (Real.rpow (measurementMass M ρ i) α * Real.rpow (measurementMass M σ i) (1 - α)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact scalar_bad_mass_le_renyi (measurementMass_nonneg M hρ.1 i)
        (measurementMass_nonneg M hσ i) hα hα1
          (lt_of_not_ge (Finset.mem_filter.mp hi).2).le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ bad)
      (fun i hi hni => by
        exact mul_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
          (mul_nonneg (Real.rpow_nonneg (measurementMass_nonneg M hρ.1 i) _)
            (Real.rpow_nonneg (measurementMass_nonneg M hσ i) _)))

theorem testingDivergence_lower_of_measurementTrace (M : FinitePOVM ι L)
    {ρ σ : CMat ι} {ε α a : ℝ} (hε : 0 ≤ ε)
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hα : 0 < α) (hα1 : α < 1)
    (hbudget : Real.rpow 2 (a * (1 - α)) *
      classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α ≤ ε) :
    (a : EReal) ≤ testingDivergence ε ρ σ := by
  apply testingDivergence_lower_of_threshold_test hε hρ hσ
    (measurementThresholdEffect_isEffect M ρ σ a) _
      (measurementThresholdEffect_cost_le M hρ a)
  have hr := (measurementThresholdEffect_rejection_le M hρ hσ hα hα1 a).trans hbudget
  linarith

end MatrixMeasurementTest

section PhysicalPairInfima

theorem setTestingDivergence_lower_of_pairwise {d n : ℕ}
    (F : QuantumFamilies d) (ε : ℝ) {a : EReal}
    (h : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      a ≤ testingDivergence ε ρ σ) :
    a ≤ setTestingDivergence F n ε := by
  unfold setTestingDivergence
  apply le_sInf
  rintro x ⟨ρ, hρ, σ, hσ, rfl⟩
  exact h ρ hρ σ hσ

theorem setTestingDivergence_le_pair {d n : ℕ} (F : QuantumFamilies d) (ε : ℝ)
    {ρ σ : QMat d n} (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n) :
    setTestingDivergence F n ε ≤ testingDivergence ε ρ σ := by
  unfold setTestingDivergence
  exact sInf_le ⟨ρ, hρ, σ, hσ, rfl⟩

theorem setTestingDivergence_upper_of_pair {d n : ℕ} (F : QuantumFamilies d) (ε : ℝ)
    {ρ σ : QMat d n} (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n)
    {a : EReal} (h : testingDivergence ε ρ σ ≤ a) :
    setTestingDivergence F n ε ≤ a :=
  (setTestingDivergence_le_pair F ε hρ hσ).trans h

theorem setTestingDivergence_lower_of_threshold_tests {d n : ℕ}
    (F : QuantumFamilies d) (ε a : ℝ) (hε : 0 ≤ ε)
    (hnull : ∀ ρ ∈ F.null n, IsState ρ)
    (halt : ∀ σ ∈ F.alternative n, σ.PosSemidef)
    (htests : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      ∃ Q : QMat d n, IsEffect Q ∧ 1 - ε ≤ tracePair ρ Q ∧
        tracePair σ Q ≤ Real.rpow 2 (-a)) :
    (a : EReal) ≤ setTestingDivergence F n ε := by
  apply setTestingDivergence_lower_of_pairwise
  intro ρ hρ σ hσ
  obtain ⟨Q, hQ, hacc, hcost⟩ := htests ρ hρ σ hσ
  exact testingDivergence_lower_of_threshold_test hε (hnull ρ hρ)
    (halt σ hσ) hQ hacc hcost

theorem physical_pair_testing_finite {d n : ℕ} (F : QuantumFamilies d)
    (hF : PhysicalAssumptions F) (hn : 0 < n) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) {ρ σ : QMat d n}
    (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n) :
    ∃ v : ℝ, testingDivergence ε ρ σ = (v : EReal) := by
  obtain ⟨C, hC⟩ := hF.linear_growth
  have hdom := (hC n hn ρ hρ σ hσ).1
  exact ⟨-logTwo (testingBeta ε ρ σ),
    testingDivergence_eq_of_domination hε0 hε1
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (C * (n : ℝ)))
        (hF.null_states n hn ρ hρ) hdom⟩

end PhysicalPairInfima

theorem scalar_renyi_cost_of_budget {p q α c : ℝ}
    (hp : 0 < p) (hq : 0 ≤ q) (hα : 0 < α) (hα1 : α < 1) (hc : 0 < c)
    (hbudget : c * (p ^ α * q ^ (1 - α)) ≤ p) :
    q ≤ c ^ (-α / (1 - α)) * (p ^ α * q ^ (1 - α)) := by
  have hb : 0 < 1 - α := sub_pos.mpr hα1
  have hd : 0 ≤ α / (1 - α) := (div_pos hα hb).le
  have hcancel : (1 - α) * (α / (1 - α)) = α := by
    field_simp [hb.ne']
  have hsplit : p = p ^ α * p ^ (1 - α) := by
    rw [← Real.rpow_add hp]
    convert (Real.rpow_one p).symm using 1 <;> ring
  have hbase : c * q ^ (1 - α) ≤ p ^ (1 - α) := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hp α)).mp
    calc
      p ^ α * (c * q ^ (1 - α)) = c * (p ^ α * q ^ (1 - α)) := by ring
      _ ≤ p := hbudget
      _ = p ^ α * p ^ (1 - α) := hsplit
  have hdiv : q ^ (1 - α) ≤ p ^ (1 - α) / c := by
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using hbase
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hq _) hdiv hd
  rw [← Real.rpow_mul hq, hcancel,
    Real.div_rpow (Real.rpow_nonneg hp.le _) hc.le,
    ← Real.rpow_mul hp.le, hcancel, div_eq_mul_inv,
    ← Real.rpow_neg hc.le] at hpow
  have he : -(α / (1 - α)) = -α / (1 - α) := by ring
  rw [he] at hpow
  calc
    q = q ^ α * q ^ (1 - α) := by
      rw [← Real.rpow_add' hq (by ring_nf; norm_num : α + (1 - α) ≠ 0)]
      convert (Real.rpow_one q).symm using 1 <;> ring
    _ ≤ (p ^ α * c ^ (-α / (1 - α))) * q ^ (1 - α) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hq _)
    _ = _ := by ring

def softAccept (p R c : ℝ) : ℝ := if p = 0 then 0 else max 0 (1 - c * R / p)

theorem softAccept_bounds {p R c : ℝ} (hp : 0 ≤ p) (hR : 0 ≤ R) (hc : 0 ≤ c) :
    0 ≤ softAccept p R c ∧ softAccept p R c ≤ 1 := by
  by_cases hz : p = 0
  · simp [softAccept, hz]
  rw [softAccept, if_neg hz]
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  have hdiv := div_nonneg (mul_nonneg hc hR) hp
  linarith

theorem softAccept_rejection_le {p R c : ℝ} (hp : 0 ≤ p) (hR : 0 ≤ R) (hc : 0 ≤ c) :
    p * (1 - softAccept p R c) ≤ c * R := by
  by_cases hz : p = 0
  · simp only [hz, zero_mul]
    exact mul_nonneg hc hR
  have hpos : 0 < p := lt_of_le_of_ne hp (Ne.symm hz)
  have hmax : 1 - c * R / p ≤ softAccept p R c := by
    rw [softAccept, if_neg hz]
    exact le_max_right _ _
  have hmul : p * (1 - softAccept p R c) ≤ p * (c * R / p) := by
    apply mul_le_mul_of_nonneg_left _ hp
    linarith
  have hcancel : p * (c * R / p) = c * R := by field_simp
  exact hcancel ▸ hmul

theorem softAccept_renyi_cost_le {p q α c : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hα : 0 < α) (hα1 : α < 1) (hc : 0 < c) :
    q * softAccept p (p ^ α * q ^ (1 - α)) c ≤
      c ^ (-α / (1 - α)) * (p ^ α * q ^ (1 - α)) := by
  have hR : 0 ≤ p ^ α * q ^ (1 - α) :=
    mul_nonneg (Real.rpow_nonneg hp _) (Real.rpow_nonneg hq _)
  have hcoef : 0 ≤ c ^ (-α / (1 - α)) := Real.rpow_nonneg hc.le _
  by_cases hz : p = 0
  · simp only [softAccept, if_pos hz, mul_zero]
    exact mul_nonneg hcoef hR
  have hpos : 0 < p := lt_of_le_of_ne hp (Ne.symm hz)
  by_cases hw : softAccept p (p ^ α * q ^ (1 - α)) c = 0
  · rw [hw, mul_zero]
    exact mul_nonneg hcoef hR
  have hwp : 0 < softAccept p (p ^ α * q ^ (1 - α)) c :=
    lt_of_le_of_ne (softAccept_bounds hp hR hc.le).1 (Ne.symm hw)
  rw [softAccept, if_neg hz, lt_max_iff] at hwp
  have hinner : 0 < 1 - c * (p ^ α * q ^ (1 - α)) / p :=
    hwp.resolve_left (lt_irrefl 0)
  have hb : c * (p ^ α * q ^ (1 - α)) ≤ p := by
    apply (div_le_one hpos).mp
    linarith
  calc
    q * softAccept p (p ^ α * q ^ (1 - α)) c ≤ q := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (softAccept_bounds hp hR hc.le).2 hq
    _ ≤ _ := scalar_renyi_cost_of_budget hpos hq hα hα1 hc hb

section PhysicalPOVM
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}

def weightedPOVMEffect (M : FinitePOVM ι L) (w : Fin L → ℝ) : CMat ι :=
  ∑ i, (w i : ℂ) • M.outcome i

theorem weightedPOVMEffect_isEffect (M : FinitePOVM ι L) (w : Fin L → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) : IsEffect (weightedPOVMEffect M w) := by
  have hpsd (i : Fin L) : ((w i : ℂ) • M.outcome i).PosSemidef := by
    exact (M.positive i).smul (by exact_mod_cast (hw i).1)
  have hrest (i : Fin L) : (((1 - w i : ℝ) : ℂ) • M.outcome i).PosSemidef := by
    exact (M.positive i).smul (by exact_mod_cast sub_nonneg.mpr (hw i).2)
  refine ⟨Matrix.posSemidef_sum _ (fun i hi => hpsd i), ?_⟩
  have he : 1 - weightedPOVMEffect M w =
      ∑ i, (((1 - w i : ℝ) : ℂ) • M.outcome i) := by
    rw [← M.sum_outcome, weightedPOVMEffect, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    rw [sub_smul, one_smul]
  rw [he]
  exact Matrix.posSemidef_sum _ (fun i hi => hrest i)

theorem weightedPOVMEffect_mass (M : FinitePOVM ι L) (w : Fin L → ℝ) (ρ : CMat ι) :
    tracePair ρ (weightedPOVMEffect M w) = ∑ i, w i * measurementMass M ρ i := by
  rw [weightedPOVMEffect, tracePair_sum_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tracePair_comm, tracePair_smul_left, tracePair_comm]
  rfl

def measurementSoftWeights (M : FinitePOVM ι L) (ρ σ : CMat ι) (α c : ℝ) : Fin L → ℝ :=
  fun i => softAccept (measurementMass M ρ i)
    ((measurementMass M ρ i) ^ α * (measurementMass M σ i) ^ (1 - α)) c

theorem measurementSoftWeights_bounds (M : FinitePOVM ι L) {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ∀ i, 0 ≤ measurementSoftWeights M ρ σ α c i ∧
      measurementSoftWeights M ρ σ α c i ≤ 1 := by
  intro i
  exact softAccept_bounds (measurementMass_nonneg M hρ i)
    (mul_nonneg (Real.rpow_nonneg (measurementMass_nonneg M hρ i) _)
      (Real.rpow_nonneg (measurementMass_nonneg M hσ i) _)) hc

theorem measurementSoftEffect_rejection_le (M : FinitePOVM ι L) {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (α : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    1 - tracePair ρ (weightedPOVMEffect M (measurementSoftWeights M ρ σ α c)) ≤
      c * classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α := by
  rw [weightedPOVMEffect_mass]
  have he : 1 - (∑ i, measurementSoftWeights M ρ σ α c i * measurementMass M ρ i) =
      ∑ i, measurementMass M ρ i * (1 - measurementSoftWeights M ρ σ α c i) := by
    conv_lhs => rw [← measurementMass_sum M hρ]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he, classicalRenyiTrace, Finset.mul_sum]
  simp only [Real.rpow_eq_pow]
  apply Finset.sum_le_sum
  intro i hi
  exact softAccept_rejection_le (measurementMass_nonneg M hρ.1 i)
    (mul_nonneg (Real.rpow_nonneg (measurementMass_nonneg M hρ.1 i) _)
      (Real.rpow_nonneg (measurementMass_nonneg M hσ i) _)) hc

theorem measurementSoftEffect_cost_le (M : FinitePOVM ι L) {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α c : ℝ} (hα : 0 < α) (hα1 : α < 1) (hc : 0 < c) :
    tracePair σ (weightedPOVMEffect M (measurementSoftWeights M ρ σ α c)) ≤
      c ^ (-α / (1 - α)) *
        classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α := by
  rw [weightedPOVMEffect_mass, classicalRenyiTrace, Finset.mul_sum]
  simp only [Real.rpow_eq_pow]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [measurementSoftWeights, mul_comm] using softAccept_renyi_cost_le
    (measurementMass_nonneg M hρ i) (measurementMass_nonneg M hσ i) hα hα1 hc

theorem exists_measurement_soft_test (M : FinitePOVM ι L) {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {α c : ℝ} (hα : 0 < α) (hα1 : α < 1) (hc : 0 < c) :
    ∃ Q : CMat ι, IsEffect Q ∧
      1 - tracePair ρ Q ≤
        c * classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α ∧
      tracePair σ Q ≤ c ^ (-α / (1 - α)) *
        classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α := by
  exact ⟨weightedPOVMEffect M (measurementSoftWeights M ρ σ α c),
    weightedPOVMEffect_isEffect M _ (measurementSoftWeights_bounds M hρ.1 hσ α hc.le),
    measurementSoftEffect_rejection_le M hρ hσ α hc.le,
    measurementSoftEffect_cost_le M hρ.1 hσ hα hα1 hc⟩

theorem testingDivergence_lower_of_measurement_soft (M : FinitePOVM ι L)
    {ρ σ : CMat ι} {ε α : ℝ} (hε : 0 < ε)
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α) :
    (-logTwo ((ε / classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α) ^
      (-α / (1 - α)) *
        classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α) : EReal) ≤
      testingDivergence ε ρ σ := by
  let T := classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α
  let c := ε / T
  have hc : 0 < c := div_pos hε hT
  obtain ⟨Q, hQ, hreject, hcost⟩ := exists_measurement_soft_test M hρ hσ hα hα1 hc
  apply testingDivergence_lower_of_cost hε.le
    (mul_pos (Real.rpow_pos_of_pos hc _) hT) hρ hσ hQ _ hcost
  have he : c * T = ε := div_mul_cancel₀ ε hT.ne'
  change 1 - tracePair ρ Q ≤ c * T at hreject
  rw [he] at hreject
  linarith

theorem measurementMass_domination (M : FinitePOVM ι L) {ρ σ : CMat ι} {a : ℝ}
    (hdom : LoewnerLE ρ ((a : ℂ) • σ)) (i : Fin L) :
    measurementMass M ρ i ≤ a * measurementMass M σ i := by
  have h := tracePair_loewner_mono hdom (M.positive i)
  rw [tracePair_smul_left] at h
  exact h

theorem classicalRenyiTrace_pos_of_domination (M : FinitePOVM ι L)
    {ρ σ : CMat ι} {a α : ℝ} (ha : 0 < a)
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hdom : LoewnerLE ρ ((a : ℂ) • σ)) :
    0 < classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α := by
  let P : FiniteLaw (Fin L) :=
    { weight := measurementMass M ρ
      nonneg := measurementMass_nonneg M hρ.1
      sum_weight := measurementMass_sum M hρ }
  obtain ⟨i, hi⟩ := P.exists_weight_pos
  have hpi : 0 < measurementMass M ρ i := hi
  have hqi : 0 < measurementMass M σ i := by
    by_contra hn
    have hq := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hn)
    have hm := measurementMass_domination M hdom i
    linarith
  apply Finset.sum_pos'
    (fun j hj => mul_nonneg (Real.rpow_nonneg (measurementMass_nonneg M hρ.1 j) _)
      (Real.rpow_nonneg (measurementMass_nonneg M hσ j) _))
  exact ⟨i, Finset.mem_univ i,
    mul_pos (Real.rpow_pos_of_pos hpi _) (Real.rpow_pos_of_pos hqi _)⟩

theorem logTwo_rpow_pos {x : ℝ} (hx : 0 < x) (y : ℝ) :
    logTwo (x ^ y) = y * logTwo x := by
  unfold logTwo
  rw [Real.log_rpow hx]
  ring

theorem logTwo_div_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    logTwo (x / y) = logTwo x - logTwo y := by
  unfold logTwo
  rw [Real.log_div hx.ne' hy.ne', sub_div]

theorem logTwo_soft_cost {T ε α : ℝ} (hT : 0 < T) (hε : 0 < ε) (hα1 : α < 1) :
    -logTwo ((ε / T) ^ (-α / (1 - α)) * T) =
      logTwo T / (α - 1) + (α / (1 - α)) * logTwo ε := by
  rw [logTwo_mul_pos (Real.rpow_pos_of_pos (div_pos hε hT) _) hT,
    logTwo_rpow_pos (div_pos hε hT), logTwo_div_pos hε hT]
  have hb : 1 - α ≠ 0 := (sub_pos.mpr hα1).ne'
  have hb' : α - 1 ≠ 0 := (sub_neg.mpr hα1).ne
  field_simp [hb, hb']
  <;> ring

theorem testingDivergence_lower_of_measurement_renyi (M : FinitePOVM ι L)
    {ρ σ : CMat ι} {ε α : ℝ} (hε : 0 < ε)
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hα : 0 < α) (hα1 : α < 1)
    (hT : 0 < classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α) :
    ((logTwo (classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α) /
      (α - 1) + (α / (1 - α)) * logTwo ε : ℝ) : EReal) ≤
      testingDivergence ε ρ σ := by
  have h := testingDivergence_lower_of_measurement_soft M hε hρ hσ hα hα1 hT
  rw [← EReal.coe_neg, logTwo_soft_cost hT hε hα1] at h
  exact h

theorem measuredDivergence_le_testing_corrected {ρ σ : CMat ι} {ε α a : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hρ : IsState ρ) (hσ : σ.PosSemidef)
    (hα : 0 < α) (hα1 : α < 1) (ha : 0 < a)
    (hdom : LoewnerLE ρ ((a : ℂ) • σ)) :
    measuredDivergence ρ σ α ≤
      ((-logTwo (testingBeta ε ρ σ) - (α / (1 - α)) * logTwo ε : ℝ) : EReal) := by
  unfold measuredDivergence
  apply sSup_le
  rintro x ⟨L, M, rfl⟩
  have hT := classicalRenyiTrace_pos_of_domination M ha hρ hσ hdom (α := α)
  have h := testingDivergence_lower_of_measurement_renyi M hε hρ hσ hα hα1 hT
  rw [testingDivergence_eq_of_domination hε.le hε1 ha hρ hdom] at h
  have hreal :
      logTwo (classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α) /
        (α - 1) + (α / (1 - α)) * logTwo ε ≤ -logTwo (testingBeta ε ρ σ) := by
    exact_mod_cast h
  have hguard : classicalRenyiDivergence (measurementMass M ρ) (measurementMass M σ) α =
      ((logTwo (classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α) /
        (α - 1) : ℝ) : EReal) := by
    simp only [classicalRenyiDivergence, ne_of_lt hα1, if_false,
      not_lt_of_ge hα1.le, false_and, hT.ne']
    rw [← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_div]
  rw [hguard]
  exact_mod_cast (by linarith :
    logTwo (classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α) /
      (α - 1) ≤ -logTwo (testingBeta ε ρ σ) - (α / (1 - α)) * logTwo ε)

end PhysicalPOVM

section PhysicalPairInfimum

theorem setTestingDivergence_lower_of_measured {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {n : ℕ} (hn : 0 < n) {ε α : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hα : 0 < α) (hα1 : α < 1) :
    setMeasuredDivergence F n α +
        (((α / (1 - α)) * logTwo ε : ℝ) : EReal) ≤
      setTestingDivergence F n ε := by
  obtain ⟨C, hC⟩ := hF.linear_growth
  unfold setTestingDivergence
  apply le_sInf
  rintro x ⟨ρ, hρ, σ, hσ, rfl⟩
  have hr := hF.null_states n hn ρ hρ
  have hs := hF.alternative_positive n hn σ hσ
  have hd := (hC n hn ρ hρ σ hσ).1
  have hc : 0 < Real.rpow 2 (C * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hp := measuredDivergence_le_testing_corrected hε hε1 hr hs hα hα1 hc hd
  have hi : setMeasuredDivergence F n α ≤ measuredDivergence ρ σ α :=
    sInf_le ⟨ρ, hρ, σ, hσ, rfl⟩
  have h := add_le_add (hi.trans hp)
    (le_refl (((α / (1 - α)) * logTwo ε : ℝ) : EReal))
  rw [← EReal.coe_add, sub_add_cancel] at h
  rw [testingDivergence_eq_of_domination hε.le hε1 hc hr hd]
  exact h

end PhysicalPairInfimum

section SingleOutcome
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def singleOutcomePOVM : FinitePOVM ι 1 where
  outcome := fun _ => 1
  positive := fun _ => Matrix.PosSemidef.one
  sum_outcome := by simp

theorem measurementMass_singleOutcome (A : CMat ι) (i : Fin 1) :
    measurementMass (singleOutcomePOVM (ι := ι)) A i = (Matrix.trace A).re := by
  simp only [measurementMass, singleOutcomePOVM, tracePair_one_right]

theorem classicalRenyiTrace_singleOutcome {ρ : CMat ι} (hρ : IsState ρ)
    (σ : CMat ι) (α : ℝ) :
    classicalRenyiTrace (measurementMass singleOutcomePOVM ρ)
      (measurementMass singleOutcomePOVM σ) α = (Matrix.trace σ).re ^ (1 - α) := by
  simp only [classicalRenyiTrace, measurementMass_singleOutcome, hρ.trace_real,
    Real.rpow_eq_pow, Real.one_rpow, one_mul, Fin.sum_univ_one]

theorem classicalRenyiDivergence_singleOutcome {ρ σ : CMat ι} (hρ : IsState ρ)
    (htr : 0 < (Matrix.trace σ).re) (α : ℝ) :
    classicalRenyiDivergence (measurementMass singleOutcomePOVM ρ)
        (measurementMass singleOutcomePOVM σ) α =
      (-logTwo (Matrix.trace σ).re : EReal) := by
  classical
  have hs : classicalSupportLE (measurementMass singleOutcomePOVM ρ)
      (measurementMass singleOutcomePOVM σ) := by
    intro i hi
    have hz : (Matrix.trace σ).re = 0 := by
      simpa only [measurementMass_singleOutcome] using hi
    exact (htr.ne' hz).elim
  by_cases hα : α = 1
  · subst α
    simp [classicalRenyiDivergence, classicalUmegaki, hs,
      measurementMass_singleOutcome, hρ.trace_real, logTwo]
  · have hT : 0 < (Matrix.trace σ).re ^ (1 - α) :=
      Real.rpow_pos_of_pos htr _
    have hb : ¬(1 < α ∧ ¬classicalSupportLE
        (measurementMass singleOutcomePOVM ρ)
          (measurementMass singleOutcomePOVM σ)) := by simp only [hs, not_true_eq_false,
      and_false, not_false_eq_true]
    rw [classicalRenyiDivergence, if_neg hα, if_neg hb,
      classicalRenyiTrace_singleOutcome hρ, if_neg hT.ne']
    rw [← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_div]
    apply congrArg (fun x : ℝ => (x : EReal))
    rw [logTwo_rpow_pos htr]
    have hden : α - 1 ≠ 0 := sub_ne_zero.mpr hα
    field_simp [hden]
    <;> ring

theorem measuredDivergence_ge_neg_log_trace {ρ σ : CMat ι} (hρ : IsState ρ)
    (htr : 0 < (Matrix.trace σ).re) (α : ℝ) :
    (-logTwo (Matrix.trace σ).re : EReal) ≤ measuredDivergence ρ σ α := by
  rw [← classicalRenyiDivergence_singleOutcome hρ htr α]
  exact le_sSup ⟨1, singleOutcomePOVM, rfl⟩

theorem alternative_trace_pos_of_domination {ρ σ : CMat ι} (hρ : IsState ρ)
    {a : ℝ} (ha : 0 < a) (hdom : LoewnerLE ρ ((a : ℂ) • σ)) :
    0 < (Matrix.trace σ).re := by
  have h := tracePair_loewner_mono hdom (Matrix.PosSemidef.one : (1 : CMat ι).PosSemidef)
  rw [tracePair_smul_left, tracePair_one_right, tracePair_one_right, hρ.trace_real] at h
  by_contra hn
  have hneg := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hn)
  linarith

theorem measuredDivergence_ge_neg_log_trace_of_domination {ρ σ : CMat ι}
    (hρ : IsState ρ) {a : ℝ} (ha : 0 < a)
    (hdom : LoewnerLE ρ ((a : ℂ) • σ)) (α : ℝ) :
    (-logTwo (Matrix.trace σ).re : EReal) ≤ measuredDivergence ρ σ α := by
  exact measuredDivergence_ge_neg_log_trace hρ
    (alternative_trace_pos_of_domination hρ ha hdom) α

end SingleOutcome

section FinitePinching
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def pinchingSandwich (P : κ → CMat ι) (A : CMat ι) : CMat ι :=
  ∑ k, P k * A * P k

theorem pinchingSandwich_posSemidef (P : κ → CMat ι) {A : CMat ι}
    (hA : A.PosSemidef) (hP : ∀ k, (P k).IsHermitian) :
    (pinchingSandwich P A).PosSemidef := by
  classical
  exact Matrix.posSemidef_sum _ fun k _ => by
    simpa only [(hP k).eq] using hA.mul_mul_conjTranspose_same (P k)

theorem pinchingSandwich_domination (P : κ → CMat ι) {A : CMat ι}
    (hA : A.PosSemidef) (hP : ∀ k, (P k).IsHermitian)
    (hsum : ∑ k, P k = 1) :
    LoewnerLE A ((Fintype.card κ : ℂ) • pinchingSandwich P A) := by
  classical
  have hexp (i j : κ) : (P i - P j) * A * (P i - P j) =
      P i * A * P i + P j * A * P j - P i * A * P j - P j * A * P i := by
    noncomm_ring
  have hd1 : (∑ i : κ, ∑ _j : κ, P i * A * P i) =
      (Fintype.card κ : ℂ) • pinchingSandwich P A := by
    ext r s
    simp only [pinchingSandwich, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hd2 : (∑ _i : κ, ∑ j : κ, P j * A * P j) =
      (Fintype.card κ : ℂ) • pinchingSandwich P A := by
    change (∑ _i : κ, pinchingSandwich P A) = _
    ext r s
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc1 : (∑ i : κ, ∑ j : κ, P i * A * P j) = A := by
    simp_rw [← Finset.mul_sum]
    simp only [hsum, Matrix.mul_one]
    rw [← Finset.sum_mul, hsum, Matrix.one_mul]
  have hc2 : (∑ i : κ, ∑ j : κ, P j * A * P i) = A := by
    simp_rw [← Finset.sum_mul]
    simp only [hsum, Matrix.one_mul]
    rw [← Finset.mul_sum, hsum, Matrix.mul_one]
  have hid : (∑ i : κ, ∑ j : κ, (P i - P j) * A * (P i - P j)) =
      (2 : ℂ) • ((Fintype.card κ : ℂ) • pinchingSandwich P A - A) := by
    simp_rw [hexp]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hd1, hd2, hc1, hc2]
    ext r s
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hp : (∑ i : κ, ∑ j : κ, (P i - P j) * A * (P i - P j)).PosSemidef := by
    refine Matrix.posSemidef_sum _ fun i _ => Matrix.posSemidef_sum _ fun j _ => ?_
    simpa only [Matrix.conjTranspose_sub, (hP i).eq, (hP j).eq]
      using hA.mul_mul_conjTranspose_same (P i - P j)
  have hhalf : (0 : ℂ) ≤ 1 / 2 := by
    exact Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩
  have htwo : (1 / 2 : ℂ) * (2 : ℂ) = 1 := by norm_num
  have hh := hp.smul hhalf
  change ((Fintype.card κ : ℂ) • pinchingSandwich P A - A).PosSemidef
  simpa only [hid, smul_smul, htwo, one_smul] using hh

theorem trace_pinchingSandwich (P : κ → CMat ι) (A : CMat ι)
    (hsum : ∑ k, P k = 1) (hidem : ∀ k, P k * P k = P k) :
    Matrix.trace (pinchingSandwich P A) = Matrix.trace A := by
  have ht (k : κ) : Matrix.trace (P k * A * P k) = Matrix.trace (A * P k) := by
    calc
      Matrix.trace (P k * A * P k) = Matrix.trace (P k * (P k * A)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (P k * P k * A) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (P k * A) := by rw [hidem k]
      _ = Matrix.trace (A * P k) := Matrix.trace_mul_comm _ _
  simp only [pinchingSandwich, Matrix.trace_sum, ht]
  rw [← Matrix.trace_sum, ← Finset.mul_sum, hsum, Matrix.mul_one]

theorem pinchingSandwich_isState (P : κ → CMat ι) {ρ : CMat ι}
    (hρ : IsState ρ) (hP : ∀ k, (P k).IsHermitian)
    (hsum : ∑ k, P k = 1) (hidem : ∀ k, P k * P k = P k) :
    IsState (pinchingSandwich P ρ) := by
  exact ⟨pinchingSandwich_posSemidef P hρ.1 hP,
    (trace_pinchingSandwich P ρ hsum hidem).trans hρ.2⟩

end FinitePinching

section UnitaryPartition
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

def diagonalSelector (label : ι → κ) (k : κ) : CMat ι :=
  Matrix.diagonal (fun j => if label j = k then 1 else 0)

theorem diagonalSelector_posSemidef (label : ι → κ) (k : κ) :
    (diagonalSelector label k).PosSemidef := by
  rw [diagonalSelector, Matrix.posSemidef_diagonal_iff]
  intro j
  split_ifs <;> norm_num

theorem diagonalSelector_idempotent (label : ι → κ) (k : κ) :
    diagonalSelector label k * diagonalSelector label k = diagonalSelector label k := by
  rw [diagonalSelector, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  split_ifs <;> norm_num

theorem sum_diagonalSelector (label : ι → κ) : ∑ k, diagonalSelector label k = 1 := by
  ext r s
  by_cases hrs : r = s
  · subst s
    simp [diagonalSelector, Matrix.sum_apply, Matrix.diagonal_apply]
  · simp [diagonalSelector, Matrix.sum_apply, Matrix.diagonal_apply, hrs]

def unitaryPartitionProjection (U : Matrix.unitaryGroup ι ℂ) (label : ι → κ)
    (k : κ) : CMat ι :=
  (U : CMat ι) * diagonalSelector label k * (U : CMat ι)ᴴ

theorem unitaryPartitionProjection_posSemidef (U : Matrix.unitaryGroup ι ℂ)
    (label : ι → κ) (k : κ) : (unitaryPartitionProjection U label k).PosSemidef := by
  exact (diagonalSelector_posSemidef label k).mul_mul_conjTranspose_same (U : CMat ι)

theorem unitaryPartitionProjection_idempotent (U : Matrix.unitaryGroup ι ℂ)
    (label : ι → κ) (k : κ) :
    unitaryPartitionProjection U label k * unitaryPartitionProjection U label k =
      unitaryPartitionProjection U label k := by
  have hu : (U : CMat ι)ᴴ * (U : CMat ι) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  let V : CMat ι := U
  let D : CMat ι := diagonalSelector label k
  change (V * D * Vᴴ) * (V * D * Vᴴ) = V * D * Vᴴ
  calc
    (V * D * Vᴴ) * (V * D * Vᴴ) = (V * D) * (Vᴴ * V) * (D * Vᴴ) := by
      noncomm_ring
    _ = (V * D) * (D * Vᴴ) := by rw [hu, Matrix.mul_one]
    _ = V * (D * D) * Vᴴ := by noncomm_ring
    _ = V * D * Vᴴ := by rw [diagonalSelector_idempotent label k]

theorem sum_unitaryPartitionProjection (U : Matrix.unitaryGroup ι ℂ)
    (label : ι → κ) : ∑ k, unitaryPartitionProjection U label k = 1 := by
  have hu : (U : CMat ι) * (U : CMat ι)ᴴ = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  simp only [unitaryPartitionProjection]
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_diagonalSelector, Matrix.mul_one, hu]

end UnitaryPartition

section SpectralPinching
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def distinctEigenvalues {σ : CMat ι} (hσ : σ.IsHermitian) : Finset ℝ := by
  classical
  exact Finset.univ.image hσ.eigenvalues

abbrev SpectralLabels {σ : CMat ι} (hσ : σ.IsHermitian) := ↥(distinctEigenvalues hσ)

def spectralLabel {σ : CMat ι} (hσ : σ.IsHermitian) (j : ι) : SpectralLabels hσ := by
  classical
  exact ⟨hσ.eigenvalues j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩

def spectralPinchingProjection {σ : CMat ι} (hσ : σ.IsHermitian)
    (k : SpectralLabels hσ) : CMat ι := by
  classical
  exact unitaryPartitionProjection hσ.eigenvectorUnitary (spectralLabel hσ) k

def spectralPinching {σ : CMat ι} (hσ : σ.IsHermitian) (A : CMat ι) : CMat ι :=
  pinchingSandwich (spectralPinchingProjection hσ) A

def spectralBlockCount {σ : CMat ι} (hσ : σ.IsHermitian) : ℕ :=
  Fintype.card (SpectralLabels hσ)

theorem spectralBlockCount_eq {σ : CMat ι} (hσ : σ.IsHermitian) :
    spectralBlockCount hσ = (distinctEigenvalues hσ).card := by
  exact Fintype.card_coe _

theorem spectralBlockCount_le_dimension {σ : CMat ι} (hσ : σ.IsHermitian) :
    spectralBlockCount hσ ≤ Fintype.card ι := by
  classical
  rw [spectralBlockCount_eq]
  exact (Finset.card_image_le).trans_eq Finset.card_univ

theorem spectralPinchingProjection_posSemidef {σ : CMat ι} (hσ : σ.IsHermitian)
    (k : SpectralLabels hσ) : (spectralPinchingProjection hσ k).PosSemidef := by
  classical
  exact unitaryPartitionProjection_posSemidef _ _ _

theorem spectralPinchingProjection_idempotent {σ : CMat ι} (hσ : σ.IsHermitian)
    (k : SpectralLabels hσ) :
    spectralPinchingProjection hσ k * spectralPinchingProjection hσ k =
      spectralPinchingProjection hσ k := by
  classical
  exact unitaryPartitionProjection_idempotent _ _ _

theorem sum_spectralPinchingProjection {σ : CMat ι} (hσ : σ.IsHermitian) :
    ∑ k, spectralPinchingProjection hσ k = 1 := by
  classical
  exact sum_unitaryPartitionProjection _ _

theorem spectralPinching_posSemidef {σ A : CMat ι} (hσ : σ.IsHermitian)
    (hA : A.PosSemidef) : (spectralPinching hσ A).PosSemidef := by
  exact pinchingSandwich_posSemidef _ hA
    (fun k => (spectralPinchingProjection_posSemidef hσ k).isHermitian)

theorem trace_spectralPinching {σ : CMat ι} (hσ : σ.IsHermitian) (A : CMat ι) :
    Matrix.trace (spectralPinching hσ A) = Matrix.trace A := by
  exact trace_pinchingSandwich _ _ (sum_spectralPinchingProjection hσ)
    (spectralPinchingProjection_idempotent hσ)

theorem spectralPinching_isState {σ ρ : CMat ι} (hσ : σ.IsHermitian)
    (hρ : IsState ρ) : IsState (spectralPinching hσ ρ) := by
  exact ⟨spectralPinching_posSemidef hσ hρ.1, (trace_spectralPinching hσ ρ).trans hρ.2⟩

theorem spectralPinching_domination {σ A : CMat ι} (hσ : σ.IsHermitian)
    (hA : A.PosSemidef) :
    LoewnerLE A ((spectralBlockCount hσ : ℂ) • spectralPinching hσ A) := by
  exact pinchingSandwich_domination _ hA
    (fun k => (spectralPinchingProjection_posSemidef hσ k).isHermitian)
    (sum_spectralPinchingProjection hσ)

end SpectralPinching

end QuantumProver.Equipartition.FiniteModel.Testing
