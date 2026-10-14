import QuantumProver.InformationTheory.IsotropicFormation.Definitions
import QuantumProver.InformationTheory.IsotropicFormation.EnsembleBounds

noncomputable section

namespace QuantumProver.IsotropicFormation

open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
  ContinuousFunctionalCalculus

variable {α β : Type*} [Fintype α] [DecidableEq α]

def diagonalSqrtCoeff (p : α → ℝ) : Coeff α α :=
  realDiagonal (fun a => Real.sqrt (p a))

omit [Fintype α] in
theorem diagonalSqrtCoeff_sq (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) :
    diagonalSqrtCoeff (fun i => p i ^ 2) = realDiagonal p := by
  unfold diagonalSqrtCoeff
  congr 1
  ext i
  exact Real.sqrt_sq (hp i)

theorem vonNeumannEntropyNat_realDiagonal (p : α → ℝ) :
    vonNeumannEntropyNat (realDiagonal p) = classicalEntropy p := by
  rw [vonNeumannEntropyNat, cfc_realDiagonal]
  simp [realDiagonal, classicalEntropy, Matrix.trace]

theorem aliceReduced_diagonalSqrtCoeff (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    aliceReduced (diagonalSqrtCoeff p) = realDiagonal p := by
  have hgram : aliceReduced (diagonalSqrtCoeff p) =
      diagonalSqrtCoeff p * (diagonalSqrtCoeff p)ᴴ := by
    ext i j
    simp only [aliceReduced, ptraceRight, pureDensity, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
  rw [hgram]
  change Matrix.diagonal (fun i => (Real.sqrt (p i) : ℂ)) *
    (Matrix.diagonal (fun i => (Real.sqrt (p i) : ℂ)))ᴴ = Matrix.diagonal (fun i => (p i : ℂ))
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hp i)]

theorem pureEntropyNat_diagonalSqrtCoeff (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    pureEntropyNat (diagonalSqrtCoeff p) = classicalEntropy p := by
  rw [pureEntropyNat, aliceReduced_diagonalSqrtCoeff p hp,
    vonNeumannEntropyNat_realDiagonal]

theorem hsSq_diagonalSqrtCoeff (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    hsSq (diagonalSqrtCoeff p) = ∑ a, p a := by
  simp [hsSq, diagonalSqrtCoeff, realDiagonal, Matrix.diagonal_apply, apply_ite,
    Complex.normSq_ofReal, hp]

theorem diagonalSqrtCoeff_normalized (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) : IsNormalizedCoeff (diagonalSqrtCoeff p) := by
  rw [IsNormalizedCoeff, hsSq_diagonalSqrtCoeff p hp, hsum]

theorem hsSq_realDiagonal (p : α → ℝ) :
    hsSq (realDiagonal p) = ∑ a, p a ^ 2 := by
  simp [hsSq, realDiagonal, Matrix.diagonal_apply, apply_ite, Complex.normSq_ofReal,
    pow_two]

section ProductDiagonal

variable [Fintype β] [DecidableEq β]

omit [Fintype β] in
theorem ptraceLeft_diagonalSqrtCoeff (p : α × β → ℝ) :
    ptraceLeft (diagonalSqrtCoeff p) =
      realDiagonal (fun b => ∑ a, Real.sqrt (p (a, b))) := by
  ext j k
  by_cases hjk : j = k
  · subst k
    simp [ptraceLeft, diagonalSqrtCoeff, realDiagonal]
  · simp [ptraceLeft, diagonalSqrtCoeff, realDiagonal, hjk]

omit [Fintype α] in
theorem ptraceRight_diagonalSqrtCoeff (p : α × β → ℝ) :
    ptraceRight (diagonalSqrtCoeff p) =
      realDiagonal (fun a => ∑ b, Real.sqrt (p (a, b))) := by
  ext i k
  by_cases hik : i = k
  · subst k
    simp [ptraceRight, diagonalSqrtCoeff, realDiagonal]
  · simp [ptraceRight, diagonalSqrtCoeff, realDiagonal, hik]

theorem bellFidelityLeft_diagonalSqrtCoeff (p : α × β → ℝ) :
    bellFidelityLeft (diagonalSqrtCoeff p) = diagonalBellFidelityLeft p := by
  rw [bellFidelityLeft, ptraceLeft_diagonalSqrtCoeff, hsSq_realDiagonal]
  rfl

theorem bellFidelityRight_diagonalSqrtCoeff (p : α × β → ℝ) :
    bellFidelityRight (diagonalSqrtCoeff p) = diagonalBellFidelityRight p := by
  rw [bellFidelityRight, ptraceRight_diagonalSqrtCoeff, hsSq_realDiagonal]
  rfl

theorem diagonalSqrtCoeff_twoFactor_affine_lower (p : α × β → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) (a1 b1 a2 b2 : ℝ)
    (h1 : ∀ q : α → ℝ, (∀ x, 0 ≤ q x) → (∑ x, q x = 1) →
      a1 + b1 * classicalBellFidelity q ≤ classicalEntropy q)
    (h2 : ∀ q : β → ℝ, (∀ y, 0 ≤ q y) → (∑ y, q y = 1) →
      a2 + b2 * classicalBellFidelity q ≤ classicalEntropy q) :
    a1 + a2 + b1 * bellFidelityLeft (diagonalSqrtCoeff p) +
        b2 * bellFidelityRight (diagonalSqrtCoeff p) ≤
      pureEntropyNat (diagonalSqrtCoeff p) := by
  rw [bellFidelityLeft_diagonalSqrtCoeff, bellFidelityRight_diagonalSqrtCoeff,
    pureEntropyNat_diagonalSqrtCoeff p hp]
  exact diagonal_twoFactor_affine_lower p hp hsum a1 b1 a2 b2 h1 h2

end ProductDiagonal

theorem vonNeumannEntropyNat_spectral (ρ : Matrix α α ℂ) (hρ : ρ.IsHermitian) :
    vonNeumannEntropyNat ρ = classicalEntropy hρ.eigenvalues := by
  rw [vonNeumannEntropyNat, trace_cfc_eq_sum ρ hρ]
  simp only [Complex.re_sum, Complex.ofReal_re, classicalEntropy]

theorem vonNeumannEntropyNat_eq_of_charpoly_eq (ρ σ : Matrix α α ℂ)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hc : ρ.charpoly = σ.charpoly) :
    vonNeumannEntropyNat ρ = vonNeumannEntropyNat σ :=
  congrArg Complex.re (trace_cfc_eq_of_charpoly_eq ρ σ hρ hσ hc Real.negMulLog)

omit [Fintype α] in
theorem realDiagonal_isHermitian (p : α → ℝ) : (realDiagonal p).IsHermitian := by
  change (Matrix.diagonal (fun i => (p i : ℂ)))ᴴ = Matrix.diagonal (fun i => (p i : ℂ))
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  simp

theorem vonNeumannEntropyNat_unitary_conj (ρ : Matrix α α ℂ) (hρ : ρ.IsHermitian)
    (U : Matrix.unitaryGroup α ℂ) :
    vonNeumannEntropyNat ((U : Matrix α α ℂ) * ρ * (U : Matrix α α ℂ)ᴴ) =
      vonNeumannEntropyNat ρ := by
  have hU : (U : Matrix α α ℂ)ᴴ * (U : Matrix α α ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  apply vonNeumannEntropyNat_eq_of_charpoly_eq _ _
    (Matrix.isHermitian_mul_mul_conjTranspose _ hρ) hρ
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem realDiagonal_mul_self (p : α → ℝ) :
    realDiagonal p * realDiagonal p = realDiagonal (fun i => p i ^ 2) := by
  simp only [realDiagonal, Matrix.diagonal_mul_diagonal, pow_two, Complex.ofReal_mul]

theorem vonNeumannEntropyNat_square_spectral (P : Matrix α α ℂ) (hP : P.IsHermitian) :
    vonNeumannEntropyNat (P * P) = classicalEntropy (fun i => hP.eigenvalues i ^ 2) := by
  let U := hP.eigenvectorUnitary
  let p := hP.eigenvalues
  have hU : (U : Matrix α α ℂ)ᴴ * (U : Matrix α α ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hdiag : P = (U : Matrix α α ℂ) * realDiagonal p * (U : Matrix α α ℂ)ᴴ := by
    simpa only [U, p, realDiagonal, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Function.comp_def, rclikeComplexCast] using hP.spectral_theorem
  have hsq : P * P = (U : Matrix α α ℂ) *
      realDiagonal (fun i => p i ^ 2) * (U : Matrix α α ℂ)ᴴ := by
    calc
      _ = (U : Matrix α α ℂ) *
          (realDiagonal p * ((U : Matrix α α ℂ)ᴴ * (U : Matrix α α ℂ)) * realDiagonal p) *
          (U : Matrix α α ℂ)ᴴ := by rw [hdiag]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU]; simp only [Matrix.mul_one, realDiagonal_mul_self]
  rw [hsq, vonNeumannEntropyNat_unitary_conj _ (realDiagonal_isHermitian _) U,
    vonNeumannEntropyNat_realDiagonal]

theorem vonNeumannEntropyNat_perm_diagonal_square (p : α → ℝ) (σ : Equiv.Perm α) :
    vonNeumannEntropyNat (realDiagonal (p ∘ σ) * realDiagonal (p ∘ σ)) =
      classicalEntropy (fun i => p i ^ 2) := by
  rw [realDiagonal_mul_self, vonNeumannEntropyNat_realDiagonal]
  exact Equiv.sum_comp σ (fun i => Real.negMulLog (p i ^ 2))

theorem hsSq_hermitian_spectral (P : Matrix α α ℂ) (hP : P.IsHermitian) :
    hsSq P = ∑ i, hP.eigenvalues i ^ 2 := by
  rw [hsSq_eq_trace_self_mul_conjTranspose, hP.eq]
  have htrace := trace_cfc_eq_sum P hP (fun x => x ^ 2)
  rw [cfc_pow_id (R := ℝ) P 2 hP.isSelfAdjoint, pow_two] at htrace
  simpa only [Complex.re_sum, Complex.ofReal_re] using congrArg Complex.re htrace

theorem hsSq_perm_diagonal_spectrum (P : Matrix α α ℂ) (hP : P.IsHermitian)
    (σ : Equiv.Perm α) : hsSq (realDiagonal (hP.eigenvalues ∘ σ)) = hsSq P := by
  rw [hsSq_realDiagonal, hsSq_hermitian_spectral P hP]
  exact Equiv.sum_comp σ (fun i => hP.eigenvalues i ^ 2)

theorem vonNeumannEntropyNat_square_eq_of_charpoly_eq (P Q : Matrix α α ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hc : P.charpoly = Q.charpoly) :
    vonNeumannEntropyNat (P * P) = vonNeumannEntropyNat (Q * Q) := by
  rw [vonNeumannEntropyNat_square_spectral P hP,
    vonNeumannEntropyNat_square_spectral Q hQ, (hP.eigenvalues_eq_eigenvalues_iff hQ).mpr hc]

theorem vonNeumannEntropyNat_gram (M : Coeff α α) :
    vonNeumannEntropyNat (Mᴴ * M) = vonNeumannEntropyNat (M * Mᴴ) :=
  vonNeumannEntropyNat_eq_of_charpoly_eq _ _
    (Matrix.isHermitian_conjTranspose_mul_self M)
    (Matrix.isHermitian_mul_conjTranspose_self M)
    (Matrix.charpoly_mul_comm Mᴴ M)

theorem vonNeumannEntropyNat_nonneg (ρ : Matrix α α ℂ) (hρ : IsDensity ρ) :
    0 ≤ vonNeumannEntropyNat ρ := by
  rw [vonNeumannEntropyNat_spectral ρ hρ.1.isHermitian]
  obtain ⟨hp, hs⟩ := density_spectral_probability ρ hρ.1 hρ.2
  exact classicalEntropy_nonneg _ hp hs

theorem pureEntropyNat_nonneg [Fintype β] (M : Coeff α β)
    (hM : IsNormalizedCoeff M) : 0 ≤ pureEntropyNat M :=
  vonNeumannEntropyNat_nonneg _ (normalizedCoeff_alice_isDensity M hM)

section TensorEntropy

open scoped Kronecker

variable {γ δ : Type*} [Fintype γ] [DecidableEq γ]

omit [DecidableEq α] [DecidableEq γ] in
theorem classicalEntropy_product (p : α → ℝ) (q : γ → ℝ)
    (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) :
    classicalEntropy (fun z : α × γ => p z.1 * q z.2) =
      classicalEntropy p + classicalEntropy q := by
  simp only [classicalEntropy, Fintype.sum_prod_type, Real.negMulLog_mul,
    Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [hp, hq]
  ring

omit [Fintype α] [Fintype γ] in
theorem realDiagonal_kronecker (p : α → ℝ) (q : γ → ℝ) :
    realDiagonal p ⊗ₖ realDiagonal q = realDiagonal (fun z : α × γ => p z.1 * q z.2) := by
  simp only [realDiagonal, Matrix.diagonal_kronecker_diagonal, Complex.ofReal_mul]

theorem vonNeumannEntropyNat_kronecker (ρ : Matrix α α ℂ) (σ : Matrix γ γ ℂ)
    (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    vonNeumannEntropyNat (ρ ⊗ₖ σ) = vonNeumannEntropyNat ρ + vonNeumannEntropyNat σ := by
  let U := hρ.1.isHermitian.eigenvectorUnitary
  let V := hσ.1.isHermitian.eigenvectorUnitary
  let W : Matrix.unitaryGroup (α × γ) ℂ :=
    ⟨(U : Matrix α α ℂ) ⊗ₖ (V : Matrix γ γ ℂ),
      Matrix.kronecker_mem_unitary U.property V.property⟩
  let p := hρ.1.isHermitian.eigenvalues
  let q := hσ.1.isHermitian.eigenvalues
  have hρdiag : ρ = (U : Matrix α α ℂ) * realDiagonal p * (U : Matrix α α ℂ)ᴴ := by
    simpa only [U, p, realDiagonal, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Function.comp_def, rclikeComplexCast] using
      hρ.1.isHermitian.spectral_theorem
  have hσdiag : σ = (V : Matrix γ γ ℂ) * realDiagonal q * (V : Matrix γ γ ℂ)ᴴ := by
    simpa only [V, q, realDiagonal, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Function.comp_def, rclikeComplexCast] using
      hσ.1.isHermitian.spectral_theorem
  have htensor : ρ ⊗ₖ σ =
      (W : Matrix (α × γ) (α × γ) ℂ) *
        realDiagonal (fun z : α × γ => p z.1 * q z.2) *
        (W : Matrix (α × γ) (α × γ) ℂ)ᴴ := by
    rw [hρdiag, hσdiag, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
      realDiagonal_kronecker, ← Matrix.conjTranspose_kronecker]
  obtain ⟨_, hp⟩ := density_spectral_probability ρ hρ.1 hρ.2
  obtain ⟨_, hq⟩ := density_spectral_probability σ hσ.1 hσ.2
  rw [htensor, vonNeumannEntropyNat_unitary_conj _ (realDiagonal_isHermitian _) W,
    vonNeumannEntropyNat_realDiagonal, classicalEntropy_product p q hp hq,
    vonNeumannEntropyNat_spectral ρ hρ.1.isHermitian,
    vonNeumannEntropyNat_spectral σ hσ.1.isHermitian]

omit [Fintype α] [DecidableEq α] [Fintype γ] [DecidableEq γ] in
theorem aliceReduced_tensorCoeff [Fintype β] [Fintype δ]
    (M : Coeff α β) (N : Coeff γ δ) :
    aliceReduced (tensorCoeff M N) = aliceReduced M ⊗ₖ aliceReduced N := by
  ext i j
  simp only [aliceReduced, ptraceRight, pureDensity, tensorCoeff, Matrix.kroneckerMap_apply,
    star_mul, Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem pureEntropyNat_tensorCoeff [Fintype β] [Fintype δ]
    (M : Coeff α β) (N : Coeff γ δ) (hM : IsNormalizedCoeff M) (hN : IsNormalizedCoeff N) :
    pureEntropyNat (tensorCoeff M N) = pureEntropyNat M + pureEntropyNat N := by
  rw [pureEntropyNat, aliceReduced_tensorCoeff]
  exact vonNeumannEntropyNat_kronecker _ _
    (normalizedCoeff_alice_isDensity M hM) (normalizedCoeff_alice_isDensity N hN)

end TensorEntropy

theorem FinitePureEnsemble.averageEntropy_nonneg [Fintype β]
    {ρ : Matrix (α × β) (α × β) ℂ} (E : FinitePureEnsemble ρ) :
    0 ≤ E.averageEntropy :=
  Finset.sum_nonneg fun j _ =>
    mul_nonneg (E.weight_nonneg j) (pureEntropyNat_nonneg (E.coeff j) (E.normalized j))

theorem entanglementOfFormationNat_nonneg [Fintype β]
    (ρ : Matrix (α × β) (α × β) ℂ) : 0 ≤ entanglementOfFormationNat ρ := by
  rw [entanglementOfFormationNat]
  refine le_iInf fun E => ?_
  exact_mod_cast E.averageEntropy_nonneg

theorem entanglementOfFormationNat_ne_bot [Fintype β]
    (ρ : Matrix (α × β) (α × β) ℂ) : entanglementOfFormationNat ρ ≠ ⊥ :=
  ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe (0 : ℝ))
    (entanglementOfFormationNat_nonneg ρ))

theorem entanglementOfFormationNat_finite [Fintype β] [DecidableEq β]
    (ρ : Matrix (α × β) (α × β) ℂ) (hρ : IsDensity ρ) :
    (⊥ : EReal) < entanglementOfFormationNat ρ ∧ entanglementOfFormationNat ρ < ⊤ := by
  refine ⟨lt_of_lt_of_le (EReal.bot_lt_coe (0 : ℝ))
    (entanglementOfFormationNat_nonneg ρ), ?_⟩
  exact lt_top_iff_ne_top.mpr (density_entanglementOfFormationNat_ne_top ρ hρ)

theorem entanglementOfFormationNat_coe_toReal [Fintype β] [DecidableEq β]
    (ρ : Matrix (α × β) (α × β) ℂ) (hρ : IsDensity ρ) :
    ((entanglementOfFormationNat ρ).toReal : EReal) = entanglementOfFormationNat ρ :=
  EReal.coe_toReal (density_entanglementOfFormationNat_ne_top ρ hρ)
    (entanglementOfFormationNat_ne_bot ρ)

theorem FinitePureEnsemble.affine_lower [Fintype β]
    {ρ : Matrix (α × β) (α × β) ℂ} (E : FinitePureEnsemble ρ)
    (a : ℝ) (f : Matrix (α × β) (α × β) ℂ →ₗ[ℝ] ℝ)
    (hpure : ∀ M : Coeff α β, IsNormalizedCoeff M →
      a + f (pureDensity M) ≤ pureEntropyNat M) :
    a + f ρ ≤ E.averageEntropy := by
  have hmean : (∑ j, E.weight j * f (pureDensity (E.coeff j))) = f ρ := by
    calc
      _ = ∑ j, f ((E.weight j : ℂ) • pureDensity (E.coeff j)) := by
        apply Finset.sum_congr rfl
        intro j _
        have hcast : (E.weight j : ℂ) • pureDensity (E.coeff j) =
            E.weight j • pureDensity (E.coeff j) :=
          algebraMap_smul ℂ (E.weight j) (pureDensity (E.coeff j))
        rw [hcast, map_smul]
        rfl
      _ = f (∑ j, (E.weight j : ℂ) • pureDensity (E.coeff j)) := by rw [map_sum]
      _ = f ρ := (congrArg f E.barycenter).symm
  calc
    a + f ρ = ∑ j, E.weight j * (a + f (pureDensity (E.coeff j))) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [E.weight_sum, one_mul, hmean]
    _ ≤ E.averageEntropy :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hpure (E.coeff j) (E.normalized j)) (E.weight_nonneg j)

theorem affine_lower_le_entanglementOfFormationNat [Fintype β]
    (ρ : Matrix (α × β) (α × β) ℂ) (a : ℝ)
    (f : Matrix (α × β) (α × β) ℂ →ₗ[ℝ] ℝ)
    (hpure : ∀ M : Coeff α β, IsNormalizedCoeff M →
      a + f (pureDensity M) ≤ pureEntropyNat M) :
    ((a + f ρ : ℝ) : EReal) ≤ entanglementOfFormationNat ρ := by
  rw [entanglementOfFormationNat]
  refine le_iInf fun E => ?_
  exact_mod_cast E.affine_lower a f hpure

end QuantumProver.IsotropicFormation
