import QuantumProver.InformationTheory.IsotropicFormation.EntropyBounds

noncomputable section

namespace QuantumProver.IsotropicFormation

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator ContinuousFunctionalCalculus

variable {α β γ δ : Type*}

abbrev Coeff (α β : Type*) := Matrix α β ℂ

abbrev StateIndex (α β : Type*) := α × β

def pureDensity (M : Coeff α β) : Matrix (StateIndex α β) (StateIndex α β) ℂ :=
  fun x y => M x.1 x.2 * star (M y.1 y.2)

def aliceReduced [Fintype β] (M : Coeff α β) : Matrix α α ℂ :=
  ptraceRight (pureDensity M)

def IsDensity [Fintype α] (ρ : Matrix α α ℂ) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

def IsNormalizedCoeff [Fintype α] [Fintype β] (M : Coeff α β) : Prop :=
  hsSq M = 1

def vonNeumannEntropyNat [Fintype α] [DecidableEq α] (ρ : Matrix α α ℂ) : ℝ :=
  (Matrix.trace (cfc Real.negMulLog ρ)).re

def pureEntropyNat [Fintype α] [Fintype β] [DecidableEq α]
    (M : Coeff α β) : ℝ :=
  vonNeumannEntropyNat (aliceReduced M)

def bellVector [Fintype α] [DecidableEq α] (x : α × α) : ℂ :=
  if x.1 = x.2 then ((Real.sqrt (Fintype.card α) : ℝ) : ℂ)⁻¹ else 0

def bellProjector [Fintype α] [DecidableEq α] : Matrix (α × α) (α × α) ℂ :=
  fun x y => bellVector x * star (bellVector y)

def isotropicState (α : Type*) [Fintype α] [DecidableEq α] (F : ℝ) :
    Matrix (α × α) (α × α) ℂ :=
  (F : ℂ) • bellProjector +
    (((1 - F) / ((Fintype.card α : ℝ) ^ 2 - 1) : ℝ) : ℂ) • (1 - bellProjector)

def tensorState (ρ : Matrix (α × β) (α × β) ℂ)
    (σ : Matrix (γ × δ) (γ × δ) ℂ) :
    Matrix ((α × γ) × (β × δ)) ((α × γ) × (β × δ)) ℂ :=
  fun x y => ρ (x.1.1, x.2.1) (y.1.1, y.2.1) *
    σ (x.1.2, x.2.2) (y.1.2, y.2.2)

def tensorCoeff (M : Coeff α β) (N : Coeff γ δ) : Coeff (α × γ) (β × δ) :=
  fun x y => M x.1 y.1 * N x.2 y.2

def pairBellProjectorLeft [Fintype α] [DecidableEq α] [DecidableEq β] :
    Matrix ((α × β) × (α × β)) ((α × β) × (α × β)) ℂ :=
  fun x y => bellProjector (x.1.1, x.2.1) (y.1.1, y.2.1) *
    (if (x.1.2, x.2.2) = (y.1.2, y.2.2) then 1 else 0)

def pairBellProjectorRight [Fintype β] [DecidableEq α] [DecidableEq β] :
    Matrix ((α × β) × (α × β)) ((α × β) × (α × β)) ℂ :=
  fun x y => (if (x.1.1, x.2.1) = (y.1.1, y.2.1) then 1 else 0) *
    bellProjector (x.1.2, x.2.2) (y.1.2, y.2.2)

def physicalFidelityLeft [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (ρ : Matrix ((α × β) × (α × β)) ((α × β) × (α × β)) ℂ) : ℝ :=
  (Matrix.trace (ρ * pairBellProjectorLeft)).re

def physicalFidelityRight [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (ρ : Matrix ((α × β) × (α × β)) ((α × β) × (α × β)) ℂ) : ℝ :=
  (Matrix.trace (ρ * pairBellProjectorRight)).re

structure FinitePureEnsemble [Fintype α] [Fintype β]
    (ρ : Matrix (α × β) (α × β) ℂ) where
  count : ℕ
  weight : Fin count → ℝ
  weight_nonneg : ∀ j, 0 ≤ weight j
  weight_sum : ∑ j, weight j = 1
  coeff : Fin count → Coeff α β
  normalized : ∀ j, IsNormalizedCoeff (coeff j)
  barycenter : ρ = ∑ j, (weight j : ℂ) • pureDensity (coeff j)

def FinitePureEnsemble.averageEntropy [Fintype α] [Fintype β] [DecidableEq α]
    {ρ : Matrix (α × β) (α × β) ℂ} (E : FinitePureEnsemble ρ) : ℝ :=
  ∑ j, E.weight j * pureEntropyNat (E.coeff j)

def entanglementOfFormationNat [Fintype α] [Fintype β] [DecidableEq α]
    (ρ : Matrix (α × β) (α × β) ℂ) : EReal :=
  ⨅ E : FinitePureEnsemble ρ, (E.averageEntropy : EReal)

def isotropicEOFNat (α : Type*) [Fintype α] [DecidableEq α] (F : ℝ) : EReal :=
  entanglementOfFormationNat (isotropicState α F)

def TwoFactorEOFAdditivity : Prop :=
  ∀ (d1 d2 : ℕ), 2 ≤ d1 → 2 ≤ d2 →
    ∀ (F1 F2 : ℝ), 0 ≤ F1 → F1 ≤ 1 → 0 ≤ F2 → F2 ≤ 1 →
      entanglementOfFormationNat
        (tensorState (isotropicState (Fin d1) F1) (isotropicState (Fin d2) F2)) =
      isotropicEOFNat (Fin d1) F1 + isotropicEOFNat (Fin d2) F2

theorem pureDensity_posSemidef [Fintype α] [Fintype β] (M : Coeff α β) :
    (pureDensity M).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (fun x : α × β => M x.1 x.2)

theorem bellProjector_posSemidef [Fintype α] [DecidableEq α] :
    (bellProjector : Matrix (α × α) (α × α) ℂ).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star bellVector

theorem bellProjector_apply [Fintype α] [DecidableEq α] (x y : α × α) :
    bellProjector x y =
      if x.1 = x.2 ∧ y.1 = y.2 then (((Fintype.card α : ℝ)⁻¹ : ℝ) : ℂ) else 0 := by
  have hi : ((Real.sqrt (Fintype.card α) : ℂ)⁻¹) *
      star ((Real.sqrt (Fintype.card α) : ℂ)⁻¹) =
      (((Fintype.card α : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_inv,
      Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  by_cases hx : x.1 = x.2 <;> by_cases hy : y.1 = y.2
  · simpa [bellProjector, bellVector, hx, hy] using hi
  · simp [bellProjector, bellVector, hx, hy]
  · simp [bellProjector, bellVector, hx, hy]
  · simp [bellProjector, bellVector, hx, hy]

theorem bellVector_normSq [Fintype α] [DecidableEq α]
    (hα : 0 < Fintype.card α) :
    (∑ x : α × α, Complex.normSq (bellVector x)) = 1 := by
  have hi : Complex.normSq ((Real.sqrt (Fintype.card α) : ℂ)⁻¹) =
      (Fintype.card α : ℝ)⁻¹ := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
  calc
    (∑ x : α × α, Complex.normSq (bellVector x)) =
        (Fintype.card α : ℝ) * (Fintype.card α : ℝ)⁻¹ := by
      simp [Fintype.sum_prod_type, bellVector, apply_ite Complex.normSq, hi]
    _ = 1 := mul_inv_cancel₀ (by exact_mod_cast Nat.ne_of_gt hα)

theorem bellProjector_trace [Fintype α] [DecidableEq α]
    (hα : 0 < Fintype.card α) :
    Matrix.trace (bellProjector : Matrix (α × α) (α × α) ℂ) = 1 := by
  have ht : Matrix.trace (bellProjector : Matrix (α × α) (α × α) ℂ) =
      ((∑ x : α × α, Complex.normSq (bellVector x) : ℝ) : ℂ) := by
    simp [Matrix.trace, bellProjector, Complex.mul_conj]
  rw [ht, bellVector_normSq hα]
  rfl

theorem bellProjector_idempotent [Fintype α] [DecidableEq α]
    (hα : 0 < Fintype.card α) :
    (bellProjector : Matrix (α × α) (α × α) ℂ) * bellProjector = bellProjector := by
  have hd : (star (bellVector : α × α → ℂ)) ⬝ᵥ bellVector = (1 : ℂ) := by
    have ht := bellProjector_trace hα
    simpa [Matrix.trace, bellProjector, dotProduct, mul_comm] using ht
  change Matrix.vecMulVec bellVector (star bellVector) *
    Matrix.vecMulVec bellVector (star bellVector) = Matrix.vecMulVec bellVector (star bellVector)
  rw [Matrix.vecMulVec_mul_vecMulVec, hd, one_smul]

theorem bellProjector_complement_posSemidef [Fintype α] [DecidableEq α]
    (hα : 0 < Fintype.card α) :
    (1 - (bellProjector : Matrix (α × α) (α × α) ℂ)).PosSemidef := by
  have hh : Matrix.conjTranspose (bellProjector : Matrix (α × α) (α × α) ℂ) =
      bellProjector := bellProjector_posSemidef.isHermitian
  have hi := bellProjector_idempotent hα
  have heq : (1 - (bellProjector : Matrix (α × α) (α × α) ℂ)) *
      Matrix.conjTranspose (1 - bellProjector) = 1 - bellProjector := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hh]
    simp [Matrix.mul_sub, Matrix.sub_mul, hi]
  rw [← heq]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem isotropicState_isDensity (α : Type*) [Fintype α] [DecidableEq α]
    (hcard : 2 ≤ Fintype.card α) (F : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    IsDensity (isotropicState α F) := by
  have hα : 0 < Fintype.card α := lt_of_lt_of_le (by norm_num) hcard
  have hd : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hcard
  have hden : 0 < (Fintype.card α : ℝ) ^ 2 - 1 := by nlinarith
  have hc : 0 ≤ (1 - F) / ((Fintype.card α : ℝ) ^ 2 - 1) :=
    div_nonneg (sub_nonneg.mpr hF1) hden.le
  refine ⟨?_, ?_⟩
  · apply Matrix.PosSemidef.add
    · apply bellProjector_posSemidef.smul
      exact_mod_cast hF0
    · apply (bellProjector_complement_posSemidef hα).smul
      exact_mod_cast hc
  · have hr : F + ((1 - F) / ((Fintype.card α : ℝ) ^ 2 - 1)) *
        ((Fintype.card α : ℝ) * Fintype.card α - 1) = 1 := by
      rw [← pow_two, div_mul_cancel₀ _ hden.ne']
      ring
    change Matrix.trace (isotropicState α F) = 1
    simp only [isotropicState, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_sub, Matrix.trace_one, bellProjector_trace hα, Fintype.card_prod,
      smul_eq_mul, mul_one]
    exact_mod_cast hr

theorem pureDensity_trace [Fintype α] [Fintype β] (M : Coeff α β) :
    Matrix.trace (pureDensity M) = (hsSq M : ℂ) := by
  simp [pureDensity, Matrix.trace, hsSq, Fintype.sum_prod_type, Complex.mul_conj]

theorem aliceReduced_posSemidef [Fintype α] [Fintype β] (M : Coeff α β) :
    (aliceReduced M).PosSemidef :=
  ptraceRight_posSemidef (pureDensity M) (pureDensity_posSemidef M)

theorem aliceReduced_trace [Fintype α] [Fintype β] (M : Coeff α β) :
    Matrix.trace (aliceReduced M) = (hsSq M : ℂ) := by
  rw [aliceReduced, ptraceRight_trace, pureDensity_trace]

theorem normalizedCoeff_isDensity [Fintype α] [Fintype β]
    (M : Coeff α β) (hM : IsNormalizedCoeff M) : IsDensity (pureDensity M) := by
  refine ⟨pureDensity_posSemidef M, ?_⟩
  rw [pureDensity_trace, show hsSq M = 1 from hM]
  rfl

theorem normalizedCoeff_alice_isDensity [Fintype α] [Fintype β]
    (M : Coeff α β) (hM : IsNormalizedCoeff M) : IsDensity (aliceReduced M) := by
  refine ⟨aliceReduced_posSemidef M, ?_⟩
  rw [aliceReduced_trace, show hsSq M = 1 from hM]
  rfl

theorem pureDensity_tensorCoeff (M : Coeff α β) (N : Coeff γ δ) :
    pureDensity (tensorCoeff M N) = tensorState (pureDensity M) (pureDensity N) := by
  ext x y
  simp only [pureDensity, tensorCoeff, tensorState, star_mul]
  ring

theorem hsSq_tensorCoeff [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (M : Coeff α β) (N : Coeff γ δ) :
    hsSq (tensorCoeff M N) = hsSq M * hsSq N := by
  simp only [hsSq, tensorCoeff, Fintype.sum_prod_type, Complex.normSq_mul]
  calc
    (∑ a, ∑ c, ∑ b, ∑ d, Complex.normSq (M a b) * Complex.normSq (N c d)) =
        ∑ a, ∑ b, ∑ c, ∑ d, Complex.normSq (M a b) * Complex.normSq (N c d) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := by simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

theorem tensorCoeff_normalized [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (M : Coeff α β) (N : Coeff γ δ)
    (hM : IsNormalizedCoeff M) (hN : IsNormalizedCoeff N) :
    IsNormalizedCoeff (tensorCoeff M N) := by
  change hsSq (tensorCoeff M N) = 1
  rw [hsSq_tensorCoeff, show hsSq M = 1 from hM, show hsSq N = 1 from hN]
  exact one_mul 1

theorem FinitePureEnsemble.isDensity [Fintype α] [Fintype β]
    {ρ : Matrix (α × β) (α × β) ℂ} (E : FinitePureEnsemble ρ) : IsDensity ρ := by
  refine ⟨?_, ?_⟩
  · rw [E.barycenter]
    apply Matrix.posSemidef_sum
    intro j _
    apply (pureDensity_posSemidef (E.coeff j)).smul
    exact_mod_cast E.weight_nonneg j
  · have hnorm (j : Fin E.count) : hsSq (E.coeff j) = 1 := E.normalized j
    rw [E.barycenter]
    simp [Matrix.trace_sum, Matrix.trace_smul, pureDensity_trace, hnorm,
      ← Complex.ofReal_sum, E.weight_sum]

def singletonPureEnsemble [Fintype α] [Fintype β]
    (M : Coeff α β) (hM : IsNormalizedCoeff M) : FinitePureEnsemble (pureDensity M) where
  count := 1
  weight := fun _ => 1
  weight_nonneg := fun _ => zero_le_one
  weight_sum := by simp
  coeff := fun _ => M
  normalized := fun _ => hM
  barycenter := by simp

theorem singletonPureEnsemble_averageEntropy [Fintype α] [Fintype β] [DecidableEq α]
    (M : Coeff α β) (hM : IsNormalizedCoeff M) :
    (singletonPureEnsemble M hM).averageEntropy = pureEntropyNat M := by
  change (∑ _j : Fin 1, (1 : ℝ) * pureEntropyNat M) = pureEntropyNat M
  simp

theorem entanglementOfFormationNat_le_ensemble [Fintype α] [Fintype β] [DecidableEq α]
    {ρ : Matrix (α × β) (α × β) ℂ} (E : FinitePureEnsemble ρ) :
    entanglementOfFormationNat ρ ≤ (E.averageEntropy : EReal) :=
  iInf_le (fun E : FinitePureEnsemble ρ => (E.averageEntropy : EReal)) E

theorem entanglementOfFormationNat_pure_le [Fintype α] [Fintype β] [DecidableEq α]
    (M : Coeff α β) (hM : IsNormalizedCoeff M) :
    entanglementOfFormationNat (pureDensity M) ≤ (pureEntropyNat M : EReal) := by
  have h := entanglementOfFormationNat_le_ensemble (singletonPureEnsemble M hM)
  rwa [singletonPureEnsemble_averageEntropy] at h

def ensembleProductIndex (m n : ℕ) : Fin (m * n) → Fin m × Fin n :=
  (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).symm

theorem ensembleProductIndex_sum (m n : ℕ) {η : Type*} [AddCommMonoid η]
    (f : Fin m × Fin n → η) :
    (∑ k : Fin (m * n), f (ensembleProductIndex m n k)) = ∑ jk, f jk :=
  (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).symm.sum_comp f

def FinitePureEnsemble.tensor [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    {ρ : Matrix (α × β) (α × β) ℂ} {σ : Matrix (γ × δ) (γ × δ) ℂ}
    (E : FinitePureEnsemble ρ) (F : FinitePureEnsemble σ) :
    FinitePureEnsemble (tensorState ρ σ) where
  count := E.count * F.count
  weight := fun k => E.weight (ensembleProductIndex E.count F.count k).1 *
    F.weight (ensembleProductIndex E.count F.count k).2
  weight_nonneg := fun k => mul_nonneg
    (E.weight_nonneg (ensembleProductIndex E.count F.count k).1)
    (F.weight_nonneg (ensembleProductIndex E.count F.count k).2)
  weight_sum := by
    change (∑ k, E.weight (ensembleProductIndex E.count F.count k).1 *
      F.weight (ensembleProductIndex E.count F.count k).2) = 1
    rw [ensembleProductIndex_sum E.count F.count
      (fun jk => E.weight jk.1 * F.weight jk.2)]
    simp only [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [E.weight_sum, F.weight_sum]
    exact one_mul 1
  coeff := fun k => tensorCoeff (E.coeff (ensembleProductIndex E.count F.count k).1)
    (F.coeff (ensembleProductIndex E.count F.count k).2)
  normalized := fun k => tensorCoeff_normalized _ _
    (E.normalized (ensembleProductIndex E.count F.count k).1)
    (F.normalized (ensembleProductIndex E.count F.count k).2)
  barycenter := by
    change tensorState ρ σ = ∑ k,
      ((E.weight (ensembleProductIndex E.count F.count k).1 *
        F.weight (ensembleProductIndex E.count F.count k).2 : ℝ) : ℂ) •
      pureDensity (tensorCoeff (E.coeff (ensembleProductIndex E.count F.count k).1)
        (F.coeff (ensembleProductIndex E.count F.count k).2))
    rw [ensembleProductIndex_sum E.count F.count
      (fun jk => ((E.weight jk.1 * F.weight jk.2 : ℝ) : ℂ) •
        pureDensity (tensorCoeff (E.coeff jk.1) (F.coeff jk.2)))]
    simp_rw [pureDensity_tensorCoeff]
    calc
      tensorState ρ σ =
          tensorState (∑ j, (E.weight j : ℂ) • pureDensity (E.coeff j))
            (∑ k, (F.weight k : ℂ) • pureDensity (F.coeff k)) :=
        congrArg₂ tensorState E.barycenter F.barycenter
      _ = _ := by
        ext x y
        simp only [tensorState, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
          Fintype.sum_prod_type, Complex.ofReal_mul]
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring

theorem rclikeComplexCast (r : ℝ) : (RCLike.ofReal r : ℂ) = Complex.ofReal r := by
  with_reducible_and_instances rfl

def unitaryCoeffColumn [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (U : Matrix.unitaryGroup (α × β) ℂ) (i : α × β) : Coeff α β :=
  fun a b => (U : Matrix (α × β) (α × β) ℂ) (a, b) i

theorem unitaryCoeffColumn_normalized [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (U : Matrix.unitaryGroup (α × β) ℂ) (i : α × β) :
    IsNormalizedCoeff (unitaryCoeffColumn U i) := by
  have hu : Matrix.conjTranspose (U : Matrix (α × β) (α × β) ℂ) *
      (U : Matrix (α × β) (α × β) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have h := congrArg (fun M : Matrix (α × β) (α × β) ℂ => (M i i).re) hu
  simpa [IsNormalizedCoeff, hsSq, unitaryCoeffColumn, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.mul_conj, mul_comm, Complex.re_sum,
    Fintype.sum_prod_type] using h

theorem density_spectral_probability [Fintype α] [DecidableEq α]
    (ρ : Matrix α α ℂ) (hρ : ρ.PosSemidef) (htrace : Matrix.trace ρ = 1) :
    (∀ i, 0 ≤ hρ.isHermitian.eigenvalues i) ∧
      (∑ i, hρ.isHermitian.eigenvalues i) = 1 := by
  refine ⟨hρ.eigenvalues_nonneg, ?_⟩
  have ht := congrArg Complex.re hρ.isHermitian.trace_eq_sum_eigenvalues
  rw [htrace] at ht
  simpa only [Complex.one_re, Complex.re_sum, rclikeComplexCast,
    Complex.ofReal_re] using ht.symm

theorem spectral_physical_density_expansion [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (ρ : Matrix (α × β) (α × β) ℂ) (hρ : ρ.IsHermitian) :
    ρ = ∑ i, (hρ.eigenvalues i : ℂ) • pureDensity (unitaryCoeffColumn hρ.eigenvectorUnitary i) := by
  calc
    ρ = (hρ.eigenvectorUnitary : Matrix (α × β) (α × β) ℂ) *
        Matrix.diagonal (fun i => Complex.ofReal (hρ.eigenvalues i)) *
        Matrix.conjTranspose (hρ.eigenvectorUnitary : Matrix (α × β) (α × β) ℂ) := by
      simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def,
        Matrix.star_eq_conjTranspose, rclikeComplexCast] using hρ.spectral_theorem
    _ = _ := by
      ext x y
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul, pureDensity, unitaryCoeffColumn]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem density_has_matrixEnsemble [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (ρ : Matrix (α × β) (α × β) ℂ) (hρ : IsDensity ρ) :
    Nonempty (FinitePureEnsemble ρ) := by
  let e : Fin (Fintype.card (α × β)) ≃ α × β := (Fintype.equivFin (α × β)).symm
  obtain ⟨hp, hs⟩ := density_spectral_probability ρ hρ.1 hρ.2
  refine ⟨{
    count := Fintype.card (α × β)
    weight := fun j => hρ.1.isHermitian.eigenvalues (e j)
    weight_nonneg := fun j => hp (e j)
    weight_sum := ?_
    coeff := fun j => unitaryCoeffColumn hρ.1.isHermitian.eigenvectorUnitary (e j)
    normalized := fun j => unitaryCoeffColumn_normalized _ _
    barycenter := ?_ }⟩
  · rw [e.sum_comp]
    exact hs
  · exact (spectral_physical_density_expansion ρ hρ.1.isHermitian).trans (e.sum_comp _).symm

theorem density_entanglementOfFormationNat_ne_top [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (ρ : Matrix (α × β) (α × β) ℂ) (hρ : IsDensity ρ) :
    entanglementOfFormationNat ρ ≠ ⊤ := by
  obtain ⟨E⟩ := density_has_matrixEnsemble ρ hρ
  exact ne_of_lt (lt_of_le_of_lt (entanglementOfFormationNat_le_ensemble E)
    (EReal.coe_lt_top E.averageEntropy))

end QuantumProver.IsotropicFormation
