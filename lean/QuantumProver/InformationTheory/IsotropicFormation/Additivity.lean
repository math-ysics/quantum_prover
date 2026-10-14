import QuantumProver.InformationTheory.IsotropicFormation.Definitions
import QuantumProver.InformationTheory.IsotropicFormation.TwoFactorBounds
import QuantumProver.InformationTheory.IsotropicFormation.ProductEnsembles
import QuantumProver.InformationTheory.IsotropicFormation.StateIdentities

noncomputable section

namespace QuantumProver.IsotropicFormation

open scoped BigOperators ComplexOrder
open Set

def matrixUnitCoeff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (i : α) (j : β) : Coeff α β := fun a b => if a = i ∧ b = j then 1 else 0

theorem matrixUnitCoeff_normalized {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (i : α) (j : β) :
    IsNormalizedCoeff (matrixUnitCoeff i j) := by
  have hnorm (a : α) (b : β) :
      Complex.normSq (matrixUnitCoeff i j a b) =
        if a = i ∧ b = j then (1 : ℝ) else 0 := by
    by_cases h : a = i ∧ b = j <;> simp [matrixUnitCoeff, h]
  change (∑ a, ∑ b, Complex.normSq (matrixUnitCoeff i j a b)) = 1
  simp_rw [hnorm]
  simp [ite_and]

theorem aliceReduced_matrixUnitCoeff {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (i : α) (j : β) :
    aliceReduced (matrixUnitCoeff i j) = realDiagonal (fun a => if a = i then 1 else 0) := by
  rw [aliceReduced_eq_gram]
  ext a b
  by_cases ha : a = i
  · subst a
    by_cases hb : b = i
    · subst b
      simp [matrixUnitCoeff, Matrix.mul_apply, Matrix.conjTranspose_apply,
        realDiagonal, Matrix.diagonal_apply]
    · have hib : i ≠ b := Ne.symm hb
      simp [matrixUnitCoeff, Matrix.mul_apply, Matrix.conjTranspose_apply,
        realDiagonal, Matrix.diagonal_apply, hb, hib]
  · have hia : i ≠ a := Ne.symm ha
    by_cases hb : b = i
    · subst b
      simp [matrixUnitCoeff, Matrix.mul_apply, Matrix.conjTranspose_apply,
        realDiagonal, Matrix.diagonal_apply, ha, hia]
    · have hib : i ≠ b := Ne.symm hb
      simp [matrixUnitCoeff, Matrix.mul_apply, Matrix.conjTranspose_apply,
        realDiagonal, Matrix.diagonal_apply, ha, hia, hb, hib]

theorem pureEntropyNat_matrixUnitCoeff {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (i : α) (j : β) :
    pureEntropyNat (matrixUnitCoeff i j) = 0 := by
  rw [pureEntropyNat, aliceReduced_matrixUnitCoeff, vonNeumannEntropyNat_realDiagonal]
  unfold classicalEntropy
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a = i <;> simp [ha]

theorem matrixUnitCoeff_trace_of_ne {α : Type*} [Fintype α] [DecidableEq α]
    (i j : α) (hij : i ≠ j) : Matrix.trace (matrixUnitCoeff i j) = 0 := by
  change (∑ a, matrixUnitCoeff i j a a) = 0
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a = i <;> simp [matrixUnitCoeff, ha, hij]

theorem entanglementOfFormationNat_matrixUnitCoeff {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (i : α) (j : β) :
    entanglementOfFormationNat (pureDensity (matrixUnitCoeff i j)) = 0 := by
  apply le_antisymm
  · have h := entanglementOfFormationNat_pure_le
      (matrixUnitCoeff i j) (matrixUnitCoeff_normalized i j)
    simpa only [pureEntropyNat_matrixUnitCoeff, EReal.coe_zero] using h
  · exact entanglementOfFormationNat_nonneg _

def bellPreparationCoeff (α : Type*) [Fintype α] [DecidableEq α] : Coeff α α :=
  Matrix.diagonal (fun _ => ((Real.sqrt (Fintype.card α) : ℝ) : ℂ)⁻¹)

theorem pureDensity_bellPreparationCoeff (α : Type*) [Fintype α] [DecidableEq α] :
    pureDensity (bellPreparationCoeff α) = (bellProjector : Matrix (α × α) (α × α) ℂ) := by
  ext x y
  simp only [pureDensity, bellPreparationCoeff, Matrix.diagonal_apply, bellProjector, bellVector]

theorem bellPreparationCoeff_eq_diagonalSqrtCoeff (α : Type*) [Fintype α] [DecidableEq α] :
    bellPreparationCoeff α = diagonalSqrtCoeff (fun _ : α => (Fintype.card α : ℝ)⁻¹) := by
  simp only [bellPreparationCoeff, diagonalSqrtCoeff, realDiagonal, Real.sqrt_inv, Complex.ofReal_inv]

theorem bellPreparationCoeff_normalized (α : Type*) [Fintype α] [DecidableEq α]
    (hcard : 0 < Fintype.card α) : IsNormalizedCoeff (bellPreparationCoeff α) := by
  have hd : 0 < (Fintype.card α : ℝ) := by exact_mod_cast hcard
  rw [bellPreparationCoeff_eq_diagonalSqrtCoeff]
  apply diagonalSqrtCoeff_normalized _ (fun _ => inv_nonneg.mpr hd.le)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ hd.ne'

theorem pureEntropyNat_bellPreparationCoeff (α : Type*) [Fintype α] [DecidableEq α]
    (hcard : 0 < Fintype.card α) : pureEntropyNat (bellPreparationCoeff α) = Real.log (Fintype.card α) := by
  have hd : 0 < (Fintype.card α : ℝ) := by exact_mod_cast hcard
  rw [bellPreparationCoeff_eq_diagonalSqrtCoeff,
    pureEntropyNat_diagonalSqrtCoeff _ (fun _ => inv_nonneg.mpr hd.le)]
  simp only [classicalEntropy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Real.negMulLog_def, Real.log_inv, neg_mul_neg, ← mul_assoc,
    mul_inv_cancel₀ hd.ne', one_mul]

theorem isotropicState_one (α : Type*) [Fintype α] [DecidableEq α] :
    isotropicState α 1 = (bellProjector : Matrix (α × α) (α × α) ℂ) := by
  simp [isotropicState]

theorem isotropicEOFNat_one_le (α : Type*) [Fintype α] [DecidableEq α]
    (hcard : 0 < Fintype.card α) : isotropicEOFNat α 1 ≤ (Real.log (Fintype.card α) : EReal) := by
  change entanglementOfFormationNat (isotropicState α 1) ≤ _
  rw [isotropicState_one, ← pureDensity_bellPreparationCoeff]
  have h := entanglementOfFormationNat_pure_le (bellPreparationCoeff α) (bellPreparationCoeff_normalized α hcard)
  rwa [pureEntropyNat_bellPreparationCoeff α hcard] at h

def unitaryCoeffConj {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (M : Coeff α α) : Coeff α α :=
  (U : Matrix α α ℂ) * M * Matrix.conjTranspose (U : Matrix α α ℂ)

theorem unitaryCoeffConj_normalized {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (M : Coeff α α) (hM : IsNormalizedCoeff M) :
    IsNormalizedCoeff (unitaryCoeffConj U M) := by
  have hU : Matrix.conjTranspose (U : Matrix α α ℂ) * (U : Matrix α α ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  change hsSq ((U : Matrix α α ℂ) * M * Matrix.conjTranspose (U : Matrix α α ℂ)) = 1
  rw [hsSq_unitary_conj _ M hU]
  exact hM

theorem unitaryCoeffConj_trace {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (M : Coeff α α) :
    Matrix.trace (unitaryCoeffConj U M) = Matrix.trace M := by
  have hU : Matrix.conjTranspose (U : Matrix α α ℂ) * (U : Matrix α α ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  exact trace_unitary_conj _ M hU

theorem pureEntropyNat_unitaryCoeffConj {α : Type*} [Fintype α] [DecidableEq α]
    (U : Matrix.unitaryGroup α ℂ) (M : Coeff α α) :
    pureEntropyNat (unitaryCoeffConj U M) = pureEntropyNat M := by
  have hU : Matrix.conjTranspose (U : Matrix α α ℂ) * (U : Matrix α α ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  simp only [pureEntropyNat, aliceReduced_eq_gram, unitaryCoeffConj]
  rw [gram_unitary_conj _ M hU]
  exact vonNeumannEntropyNat_unitary_conj
    (M * Matrix.conjTranspose M) (Matrix.posSemidef_self_mul_conjTranspose M).isHermitian U

def unitaryOrbitState {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (U : Fin m → Matrix.unitaryGroup α ℂ) (weight : Fin m → ℝ) (M : Coeff α α) :
    Matrix (α × α) (α × α) ℂ :=
  ∑ j, (weight j : ℂ) • pureDensity (unitaryCoeffConj (U j) M)

def unitaryOrbitEnsemble {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (U : Fin m → Matrix.unitaryGroup α ℂ) (weight : Fin m → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hsum : ∑ j, weight j = 1)
    (M : Coeff α α) (hM : IsNormalizedCoeff M) :
    FinitePureEnsemble (unitaryOrbitState U weight M) where
  count := m
  weight := weight
  weight_nonneg := hw
  weight_sum := hsum
  coeff := fun j => unitaryCoeffConj (U j) M
  normalized := fun j => unitaryCoeffConj_normalized (U j) M hM
  barycenter := rfl

theorem unitaryOrbitEnsemble_averageEntropy {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} (U : Fin m → Matrix.unitaryGroup α ℂ) (weight : Fin m → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hsum : ∑ j, weight j = 1)
    (M : Coeff α α) (hM : IsNormalizedCoeff M) :
    (unitaryOrbitEnsemble U weight hw hsum M hM).averageEntropy = pureEntropyNat M := by
  change (∑ j : Fin m, weight j * pureEntropyNat (unitaryCoeffConj (U j) M)) = _
  simp_rw [pureEntropyNat_unitaryCoeffConj, ← Finset.sum_mul]
  rw [hsum, one_mul]

theorem unitaryOrbitState_isDensity {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} (U : Fin m → Matrix.unitaryGroup α ℂ) (weight : Fin m → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hsum : ∑ j, weight j = 1)
    (M : Coeff α α) (hM : IsNormalizedCoeff M) :
    IsDensity (unitaryOrbitState U weight M) :=
  (unitaryOrbitEnsemble U weight hw hsum M hM).isDensity

theorem entanglementOfFormationNat_unitaryOrbit_le {α : Type*}
    [Fintype α] [DecidableEq α] {m : ℕ}
    (U : Fin m → Matrix.unitaryGroup α ℂ) (weight : Fin m → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hsum : ∑ j, weight j = 1)
    (M : Coeff α α) (hM : IsNormalizedCoeff M) :
    entanglementOfFormationNat (unitaryOrbitState U weight M) ≤ (pureEntropyNat M : EReal) := by
  have h := entanglementOfFormationNat_le_ensemble (unitaryOrbitEnsemble U weight hw hsum M hM)
  rwa [unitaryOrbitEnsemble_averageEntropy] at h

def finiteUnitaryOrbitState {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (U : ι → Matrix.unitaryGroup α ℂ) (weight : ι → ℝ) (M : Coeff α α) :
    Matrix (α × α) (α × α) ℂ :=
  ∑ j, (weight j : ℂ) • pureDensity (unitaryCoeffConj (U j) M)

def finiteUnitaryOrbitEnsemble {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι]
    (U : ι → Matrix.unitaryGroup α ℂ) (weight : ι → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hsum : ∑ j, weight j = 1)
    (M : Coeff α α) (hM : IsNormalizedCoeff M) :
    FinitePureEnsemble (finiteUnitaryOrbitState U weight M) where
  count := Fintype.card ι
  weight := fun j => weight ((Fintype.equivFin ι).symm j)
  weight_nonneg := fun _ => hw _
  weight_sum := ((Fintype.equivFin ι).symm.sum_comp weight).trans hsum
  coeff := fun j => unitaryCoeffConj (U ((Fintype.equivFin ι).symm j)) M
  normalized := fun _ => unitaryCoeffConj_normalized _ M hM
  barycenter := ((Fintype.equivFin ι).symm.sum_comp
    (fun j => (weight j : ℂ) • pureDensity (unitaryCoeffConj (U j) M))).symm

theorem finiteUnitaryOrbitEnsemble_averageEntropy {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι]
    (U : ι → Matrix.unitaryGroup α ℂ) (weight : ι → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hsum : ∑ j, weight j = 1)
    (M : Coeff α α) (hM : IsNormalizedCoeff M) :
    (finiteUnitaryOrbitEnsemble U weight hw hsum M hM).averageEntropy =
      pureEntropyNat M := by
  change (∑ j : Fin (Fintype.card ι),
    weight ((Fintype.equivFin ι).symm j) *
      pureEntropyNat (unitaryCoeffConj (U ((Fintype.equivFin ι).symm j)) M)) = _
  simp_rw [pureEntropyNat_unitaryCoeffConj, ← Finset.sum_mul]
  rw [(Fintype.equivFin ι).symm.sum_comp weight, hsum, one_mul]

theorem finiteUnitaryOrbitState_isDensity {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι]
    (U : ι → Matrix.unitaryGroup α ℂ) (weight : ι → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hsum : ∑ j, weight j = 1)
    (M : Coeff α α) (hM : IsNormalizedCoeff M) :
    IsDensity (finiteUnitaryOrbitState U weight M) :=
  (finiteUnitaryOrbitEnsemble U weight hw hsum M hM).isDensity

theorem entanglementOfFormationNat_finiteUnitaryOrbit_le {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι]
    (U : ι → Matrix.unitaryGroup α ℂ) (weight : ι → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hsum : ∑ j, weight j = 1)
    (M : Coeff α α) (hM : IsNormalizedCoeff M) :
    entanglementOfFormationNat (finiteUnitaryOrbitState U weight M) ≤
      (pureEntropyNat M : EReal) := by
  have h := entanglementOfFormationNat_le_ensemble
    (finiteUnitaryOrbitEnsemble U weight hw hsum M hM)
  rwa [finiteUnitaryOrbitEnsemble_averageEntropy] at h

theorem finiteUnitaryOrbitState_uniform_eq {α ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι]
    (U : ι → Matrix.unitaryGroup α ℂ) (M : Coeff α α) :
    finiteUnitaryOrbitState U (fun _ => (Fintype.card ι : ℝ)⁻¹) M =
      (Fintype.card ι : ℂ)⁻¹ • ∑ j, pureDensity (unitaryCoeffConj (U j) M) := by
  simp only [finiteUnitaryOrbitState, Complex.ofReal_inv, Complex.ofReal_natCast,
    ← Finset.smul_sum]

theorem uniformFiniteUnitaryOrbitWeight_sum (ι : Type*) [Fintype ι] [Nonempty ι] :
    (∑ _ : ι, (Fintype.card ι : ℝ)⁻¹) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')

def mixState {α β : Type*}
    (ρ σ : Matrix (α × β) (α × β) ℂ) (t : ℝ) :
    Matrix (α × β) (α × β) ℂ :=
  (t : ℂ) • ρ + ((1 - t : ℝ) : ℂ) • σ

def FinitePureEnsemble.mix {α β : Type*} [Fintype α] [Fintype β]
    {ρ σ : Matrix (α × β) (α × β) ℂ}
    (E : FinitePureEnsemble ρ) (F : FinitePureEnsemble σ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : FinitePureEnsemble (mixState ρ σ t) where
  count := E.count + F.count
  weight := Fin.addCases (fun j => t * E.weight j) (fun k => (1 - t) * F.weight k)
  weight_nonneg := by
    intro k
    induction k using Fin.addCases
    · simpa only [Fin.addCases_left] using mul_nonneg ht0 (E.weight_nonneg _)
    · simpa only [Fin.addCases_right] using
        mul_nonneg (sub_nonneg.mpr ht1) (F.weight_nonneg _)
  weight_sum := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    simp_rw [← Finset.mul_sum]
    rw [E.weight_sum, F.weight_sum]
    ring
  coeff := Fin.addCases E.coeff F.coeff
  normalized := by
    intro k
    induction k using Fin.addCases
    · simpa only [Fin.addCases_left] using E.normalized _
    · simpa only [Fin.addCases_right] using F.normalized _
  barycenter := by
    rw [Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    change (t : ℂ) • ρ + ((1 - t : ℝ) : ℂ) • σ = _
    calc
      (t : ℂ) • ρ + ((1 - t : ℝ) : ℂ) • σ =
          (t : ℂ) • (∑ j, (E.weight j : ℂ) • pureDensity (E.coeff j)) +
            ((1 - t : ℝ) : ℂ) • (∑ k, (F.weight k : ℂ) • pureDensity (F.coeff k)) :=
        congrArg₂ (fun r s => (t : ℂ) • r + ((1 - t : ℝ) : ℂ) • s)
          E.barycenter F.barycenter
      _ = _ := by simp only [Finset.smul_sum, smul_smul, Complex.ofReal_mul]

theorem FinitePureEnsemble.mix_averageEntropy {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α]
    {ρ σ : Matrix (α × β) (α × β) ℂ}
    (E : FinitePureEnsemble ρ) (F : FinitePureEnsemble σ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (E.mix F t ht0 ht1).averageEntropy =
      t * E.averageEntropy + (1 - t) * F.averageEntropy := by
  change (∑ k : Fin (E.count + F.count),
    Fin.addCases (fun j => t * E.weight j) (fun j => (1 - t) * F.weight j) k *
      pureEntropyNat (Fin.addCases E.coeff F.coeff k)) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rfl

theorem mixState_isDensity {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {ρ σ : Matrix (α × β) (α × β) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : IsDensity (mixState ρ σ t) := by
  obtain ⟨E⟩ := density_has_matrixEnsemble ρ hρ
  obtain ⟨F⟩ := density_has_matrixEnsemble σ hσ
  exact (E.mix F t ht0 ht1).isDensity

theorem mixPreparation_roof_upper {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α]
    {ρ σ : Matrix (α × β) (α × β) ℂ}
    (E : FinitePureEnsemble ρ) (F : FinitePureEnsemble σ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    entanglementOfFormationNat (mixState ρ σ t) ≤
      ((t * E.averageEntropy + (1 - t) * F.averageEntropy : ℝ) : EReal) := by
  have h := entanglementOfFormationNat_le_ensemble (E.mix F t ht0 ht1)
  rwa [E.mix_averageEntropy F t ht0 ht1] at h

theorem entanglementOfFormationNat_mix_le_of_finite {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {ρ σ : Matrix (α × β) (α × β) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hρbot : entanglementOfFormationNat ρ ≠ ⊥)
    (hσbot : entanglementOfFormationNat σ ≠ ⊥)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    entanglementOfFormationNat (mixState ρ σ t) ≤
      (t : EReal) * entanglementOfFormationNat ρ +
        ((1 - t : ℝ) : EReal) * entanglementOfFormationNat σ := by
  have hρcoe := EReal.coe_toReal (density_entanglementOfFormationNat_ne_top ρ hρ) hρbot
  have hσcoe := EReal.coe_toReal (density_entanglementOfFormationNat_ne_top σ hσ) hσbot
  by_cases hmixbot : entanglementOfFormationNat (mixState ρ σ t) = ⊥
  · rw [hmixbot]
    exact bot_le
  have hmixcoe := EReal.coe_toReal
    (density_entanglementOfFormationNat_ne_top _ (mixState_isDensity hρ hσ t ht0 ht1))
    hmixbot
  have hreal : (entanglementOfFormationNat (mixState ρ σ t)).toReal ≤
      t * (entanglementOfFormationNat ρ).toReal +
        (1 - t) * (entanglementOfFormationNat σ).toReal := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hεE : entanglementOfFormationNat ρ <
        (((entanglementOfFormationNat ρ).toReal + ε : ℝ) : EReal) := by
      calc
        entanglementOfFormationNat ρ =
            ((entanglementOfFormationNat ρ).toReal : EReal) := hρcoe.symm
        _ < _ := EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right _ hε)
    have hεF : entanglementOfFormationNat σ <
        (((entanglementOfFormationNat σ).toReal + ε : ℝ) : EReal) := by
      calc
        entanglementOfFormationNat σ =
            ((entanglementOfFormationNat σ).toReal : EReal) := hσcoe.symm
        _ < _ := EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right _ hε)
    obtain ⟨E, hE⟩ := iInf_lt_iff.mp
      (show (⨅ E : FinitePureEnsemble ρ, (E.averageEntropy : EReal)) <
        (((entanglementOfFormationNat ρ).toReal + ε : ℝ) : EReal) from hεE)
    obtain ⟨F, hF⟩ := iInf_lt_iff.mp
      (show (⨅ F : FinitePureEnsemble σ, (F.averageEntropy : EReal)) <
        (((entanglementOfFormationNat σ).toReal + ε : ℝ) : EReal) from hεF)
    have hEreal := EReal.coe_lt_coe_iff.mp hE
    have hFreal := EReal.coe_lt_coe_iff.mp hF
    have hcost : (entanglementOfFormationNat (mixState ρ σ t)).toReal ≤
        t * E.averageEntropy + (1 - t) * F.averageEntropy := by
      apply EReal.coe_le_coe_iff.mp
      rw [hmixcoe]
      exact mixPreparation_roof_upper E F t ht0 ht1
    have hEweight := mul_le_mul_of_nonneg_left hEreal.le ht0
    have hFweight := mul_le_mul_of_nonneg_left hFreal.le (sub_nonneg.mpr ht1)
    nlinarith
  calc
    entanglementOfFormationNat (mixState ρ σ t) =
        ((entanglementOfFormationNat (mixState ρ σ t)).toReal : EReal) := hmixcoe.symm
    _ ≤ ((t * (entanglementOfFormationNat ρ).toReal +
          (1 - t) * (entanglementOfFormationNat σ).toReal : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr hreal
    _ = _ := by rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul, hρcoe, hσcoe]

theorem mixState_isotropicState (α : Type*) [Fintype α] [DecidableEq α]
    (F G t : ℝ) :
    mixState (isotropicState α F) (isotropicState α G) t =
      isotropicState α (t * F + (1 - t) * G) := by
  ext x y
  simp only [mixState, isotropicState, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul]
  push_cast
  ring

theorem tensorPreparation_density {α β γ δ : Type*}
    (M : Coeff α β) (N : Coeff γ δ) :
    pureDensity (tensorCoeff M N) = tensorState (pureDensity M) (pureDensity N) :=
  pureDensity_tensorCoeff M N

theorem tensorPreparation_isDensity {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    {ρ : Matrix (α × β) (α × β) ℂ} {σ : Matrix (γ × δ) (γ × δ) ℂ}
    (E : FinitePureEnsemble ρ) (F : FinitePureEnsemble σ) :
    IsDensity (tensorState ρ σ) :=
  (E.tensor F).isDensity

theorem tensorState_isDensity {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    {ρ : Matrix (α × β) (α × β) ℂ} {σ : Matrix (γ × δ) (γ × δ) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) : IsDensity (tensorState ρ σ) := by
  obtain ⟨E⟩ := density_has_matrixEnsemble ρ hρ
  obtain ⟨F⟩ := density_has_matrixEnsemble σ hσ
  exact tensorPreparation_isDensity E F

theorem isotropic_tensor_entanglementOfFormationNat_ne_top
    (d1 d2 : ℕ) (hd1 : 2 ≤ d1) (hd2 : 2 ≤ d2)
    (F1 F2 : ℝ) (hF10 : 0 ≤ F1) (hF11 : F1 ≤ 1) (hF20 : 0 ≤ F2) (hF21 : F2 ≤ 1) :
    entanglementOfFormationNat
      (tensorState (isotropicState (Fin d1) F1) (isotropicState (Fin d2) F2)) ≠ ⊤ := by
  apply density_entanglementOfFormationNat_ne_top
  apply tensorState_isDensity
  · exact isotropicState_isDensity (Fin d1) (by simpa using hd1) F1 hF10 hF11
  · exact isotropicState_isDensity (Fin d2) (by simpa using hd2) F2 hF20 hF21

theorem tensorPreparation_roof_upper {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq γ]
    {ρ : Matrix (α × β) (α × β) ℂ} {σ : Matrix (γ × δ) (γ × δ) ℂ}
    (E : FinitePureEnsemble ρ) (F : FinitePureEnsemble σ) :
    entanglementOfFormationNat (tensorState ρ σ) ≤
      ((E.tensor F).averageEntropy : EReal) :=
  entanglementOfFormationNat_le_ensemble (E.tensor F)

theorem FinitePureEnsemble.tensor_averageEntropy_of_component_equalities
    {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq γ]
    {ρ : Matrix (α × β) (α × β) ℂ} {σ : Matrix (γ × δ) (γ × δ) ℂ}
    (E : FinitePureEnsemble ρ) (F : FinitePureEnsemble σ)
    (hcomponent : ∀ j k,
      pureEntropyNat (tensorCoeff (E.coeff j) (F.coeff k)) =
        pureEntropyNat (E.coeff j) + pureEntropyNat (F.coeff k)) :
    (E.tensor F).averageEntropy = E.averageEntropy + F.averageEntropy := by
  change (∑ l : Fin (E.count * F.count),
    (E.weight (ensembleProductIndex E.count F.count l).1 *
      F.weight (ensembleProductIndex E.count F.count l).2) *
        pureEntropyNat (tensorCoeff
          (E.coeff (ensembleProductIndex E.count F.count l).1)
          (F.coeff (ensembleProductIndex E.count F.count l).2))) = _
  rw [ensembleProductIndex_sum E.count F.count
    (fun jk => (E.weight jk.1 * F.weight jk.2) *
      pureEntropyNat (tensorCoeff (E.coeff jk.1) (F.coeff jk.2)))]
  simp only [Fintype.sum_prod_type]
  simp_rw [hcomponent]
  calc
    (∑ j, ∑ k, (E.weight j * F.weight k) *
        (pureEntropyNat (E.coeff j) + pureEntropyNat (F.coeff k))) =
      (∑ j, ∑ k,
        ((E.weight j * pureEntropyNat (E.coeff j)) * F.weight k +
          E.weight j * (F.weight k * pureEntropyNat (F.coeff k)))) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = E.averageEntropy + F.averageEntropy := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [E.weight_sum, F.weight_sum]
      simp [FinitePureEnsemble.averageEntropy]

theorem entanglementOfFormationNat_tensor_le_of_entropy_additivity
    {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    {ρ : Matrix (α × β) (α × β) ℂ} {σ : Matrix (γ × δ) (γ × δ) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hadd : ∀ (M : Coeff α β) (N : Coeff γ δ),
      IsNormalizedCoeff M → IsNormalizedCoeff N →
        pureEntropyNat (tensorCoeff M N) = pureEntropyNat M + pureEntropyNat N) :
    entanglementOfFormationNat (tensorState ρ σ) ≤
      entanglementOfFormationNat ρ + entanglementOfFormationNat σ := by
  apply EReal.le_add_of_forall_gt
    (.inr (density_entanglementOfFormationNat_ne_top σ hσ))
    (.inl (density_entanglementOfFormationNat_ne_top ρ hρ))
  intro a ha b hb
  obtain ⟨E, hE⟩ := iInf_lt_iff.mp
    (show (⨅ E : FinitePureEnsemble ρ, (E.averageEntropy : EReal)) < a from ha)
  obtain ⟨F, hF⟩ := iInf_lt_iff.mp
    (show (⨅ F : FinitePureEnsemble σ, (F.averageEntropy : EReal)) < b from hb)
  calc
    entanglementOfFormationNat (tensorState ρ σ) ≤
        ((E.tensor F).averageEntropy : EReal) :=
      entanglementOfFormationNat_le_ensemble (E.tensor F)
    _ = (E.averageEntropy : EReal) + (F.averageEntropy : EReal) := by
      rw [E.tensor_averageEntropy_of_component_equalities F
        (fun j k => hadd _ _ (E.normalized j) (F.normalized k)), EReal.coe_add]
    _ ≤ a + b := (EReal.add_lt_add hE hF).le

theorem entanglementOfFormationNat_mix_le {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {ρ σ : Matrix (α × β) (α × β) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    entanglementOfFormationNat (mixState ρ σ t) ≤
      (t : EReal) * entanglementOfFormationNat ρ +
        ((1 - t : ℝ) : EReal) * entanglementOfFormationNat σ :=
  entanglementOfFormationNat_mix_le_of_finite hρ hσ
    (entanglementOfFormationNat_ne_bot ρ) (entanglementOfFormationNat_ne_bot σ)
    t ht0 ht1

theorem isotropicEOFNat_convex (α : Type*) [Fintype α] [DecidableEq α]
    (hcard : 2 ≤ Fintype.card α) (F G : ℝ)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (hG0 : 0 ≤ G) (hG1 : G ≤ 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    isotropicEOFNat α (t * F + (1 - t) * G) ≤
      (t : EReal) * isotropicEOFNat α F +
        ((1 - t : ℝ) : EReal) * isotropicEOFNat α G := by
  have h := entanglementOfFormationNat_mix_le
    (isotropicState_isDensity α hcard F hF0 hF1)
    (isotropicState_isDensity α hcard G hG0 hG1) t ht0 ht1
  simpa only [mixState_isotropicState, isotropicEOFNat] using h

theorem FinitePureEnsemble.tensor_averageEntropy {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    {ρ : Matrix (α × β) (α × β) ℂ} {σ : Matrix (γ × δ) (γ × δ) ℂ}
    (E : FinitePureEnsemble ρ) (F : FinitePureEnsemble σ) :
    (E.tensor F).averageEntropy = E.averageEntropy + F.averageEntropy :=
  E.tensor_averageEntropy_of_component_equalities F
    (fun j k => pureEntropyNat_tensorCoeff (E.coeff j) (F.coeff k)
      (E.normalized j) (F.normalized k))

theorem entanglementOfFormationNat_tensor_le {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    {ρ : Matrix (α × β) (α × β) ℂ} {σ : Matrix (γ × δ) (γ × δ) ℂ}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    entanglementOfFormationNat (tensorState ρ σ) ≤
      entanglementOfFormationNat ρ + entanglementOfFormationNat σ :=
  entanglementOfFormationNat_tensor_le_of_entropy_additivity hρ hσ
    (fun M N hM hN => pureEntropyNat_tensorCoeff M N hM hN)

theorem isotropic_twoFactor_EOF_upper (d1 d2 : ℕ) (hd1 : 2 ≤ d1) (hd2 : 2 ≤ d2)
    (F1 F2 : ℝ) (hF10 : 0 ≤ F1) (hF11 : F1 ≤ 1) (hF20 : 0 ≤ F2) (hF21 : F2 ≤ 1) :
    entanglementOfFormationNat
      (tensorState (isotropicState (Fin d1) F1) (isotropicState (Fin d2) F2)) ≤
      isotropicEOFNat (Fin d1) F1 + isotropicEOFNat (Fin d2) F2 := by
  exact entanglementOfFormationNat_tensor_le
    (isotropicState_isDensity (Fin d1) (by simpa only [Fintype.card_fin] using hd1)
      F1 hF10 hF11)
    (isotropicState_isDensity (Fin d2) (by simpa only [Fintype.card_fin] using hd2)
      F2 hF20 hF21)

def isotropicEOFReal (α : Type*) [Fintype α] [DecidableEq α] (F : ℝ) : ℝ :=
  (isotropicEOFNat α F).toReal

theorem isotropicEOFNat_coe_real (α : Type*) [Fintype α] [DecidableEq α]
    (hcard : 2 ≤ Fintype.card α) (F : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    (isotropicEOFReal α F : EReal) = isotropicEOFNat α F :=
  entanglementOfFormationNat_coe_toReal _ (isotropicState_isDensity α hcard F hF0 hF1)

theorem isotropicEOFReal_nonneg (α : Type*) [Fintype α] [DecidableEq α]
    (hcard : 2 ≤ Fintype.card α) (F : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    0 ≤ isotropicEOFReal α F := by
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_zero, isotropicEOFNat_coe_real α hcard F hF0 hF1]
  exact entanglementOfFormationNat_nonneg _

theorem isotropicEOFReal_convex (α : Type*) [Fintype α] [DecidableEq α]
    (hcard : 2 ≤ Fintype.card α) : ConvexOn ℝ (Icc (0 : ℝ) 1) (isotropicEOFReal α) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro F hF G hG a b ha hb hab
  have ha1 : a ≤ 1 := by linarith
  have hb_eq : b = 1 - a := by linarith
  rw [hb_eq]
  simp only [smul_eq_mul]
  have hmix0 : 0 ≤ a * F + (1 - a) * G :=
    add_nonneg (mul_nonneg ha hF.1) (mul_nonneg (sub_nonneg.mpr ha1) hG.1)
  have hmix1 : a * F + (1 - a) * G ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hF.2 ha
    have h2 := mul_le_mul_of_nonneg_left hG.2 (sub_nonneg.mpr ha1)
    nlinarith
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul,
    isotropicEOFNat_coe_real α hcard _ hmix0 hmix1,
    isotropicEOFNat_coe_real α hcard F hF.1 hF.2,
    isotropicEOFNat_coe_real α hcard G hG.1 hG.2]
  exact isotropicEOFNat_convex α hcard F G hF.1 hF.2 hG.1 hG.2 a ha ha1

theorem convex_nonnegative_zero_affine_support_interior
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Icc (0 : ℝ) 1) f)
    (hf0 : f 0 = 0) (hnonneg : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ f y)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ a b : ℝ, 0 ≤ b ∧ a + b * x = f x ∧
      ∀ y ∈ Icc (0 : ℝ) 1, a + b * y ≤ f y := by
  have hxs : x ∈ interior (Icc (0 : ℝ) 1) := by
    simpa only [interior_Icc, mem_Ioo] using And.intro hx0 hx1
  have hx : x ∈ Icc (0 : ℝ) 1 := ⟨hx0.le, hx1.le⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  let b := derivWithin f (Iio x) x
  let a := f x - b * x
  have hleft0 : slope f 0 x ≤ b :=
    hf.slope_le_leftDeriv_of_mem_interior hzero hxs hx0
  have hb : 0 ≤ b := by
    have hleft0' : f x / x ≤ b := by
      simpa only [slope_def_field, hf0, sub_zero] using hleft0
    exact (div_nonneg (hnonneg x hx) hx0.le).trans hleft0'
  refine ⟨a, b, hb, ?_, ?_⟩
  · dsimp [a]
    ring
  · intro y hy
    rcases lt_trichotomy y x with hyx | rfl | hxy
    · have hleft : slope f y x ≤ b :=
        hf.slope_le_leftDeriv_of_mem_interior hy hxs hyx
      rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hyx)] at hleft
      dsimp [a]
      nlinarith
    · dsimp [a]
      linarith
    · have hright : b ≤ slope f x y :=
        (hf.leftDeriv_le_rightDeriv_of_mem_interior hxs).trans
          (hf.rightDeriv_le_slope_of_mem_interior hxs hy hxy)
      rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at hright
      dsimp [a]
      nlinarith

theorem isotropicEOFReal_affine_support_interior_of_zero
    (α : Type*) [Fintype α] [DecidableEq α] (hcard : 2 ≤ Fintype.card α)
    (hzero : isotropicEOFNat α 0 = 0) (F : ℝ) (hF0 : 0 < F) (hF1 : F < 1) :
    ∃ a b : ℝ, 0 ≤ b ∧ a + b * F = isotropicEOFReal α F ∧
      ∀ G ∈ Icc (0 : ℝ) 1, a + b * G ≤ isotropicEOFReal α G := by
  apply convex_nonnegative_zero_affine_support_interior (isotropicEOFReal α)
    (isotropicEOFReal_convex α hcard) _ _ F hF0 hF1
  · simp only [isotropicEOFReal, hzero, EReal.toReal_zero]
  · intro G hG
    exact isotropicEOFReal_nonneg α hcard G hG.1 hG.2

def isotropicTwirlWeight (α : Type*) [Fintype α] : ℝ :=
  1 / ((Fintype.card α : ℝ) + 1)

theorem isotropicTwirlWeight_bounds (α : Type*) [Fintype α] :
    0 ≤ isotropicTwirlWeight α ∧ isotropicTwirlWeight α ≤ 1 := by
  have hd : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  unfold isotropicTwirlWeight
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < Fintype.card α + 1)).mpr
    nlinarith

theorem one_sub_isotropicTwirlWeight (α : Type*) [Fintype α] :
    1 - isotropicTwirlWeight α = (Fintype.card α : ℝ) / ((Fintype.card α : ℝ) + 1) := by
  have hd : (0 : ℝ) < Fintype.card α + 1 := by positivity
  unfold isotropicTwirlWeight
  field_simp [hd.ne']
  ring

def isotropicBlockExpression (α : Type*) [Fintype α] [DecidableEq α]
    (D : Matrix (α × α) (α × α) ℂ) (F q : ℝ) :
    Matrix (α × α) (α × α) ℂ :=
  (F : ℂ) • bellProjector +
    ((q / ((Fintype.card α : ℝ) - 1) : ℝ) : ℂ) • (D - bellProjector) +
    (((1 - F - q) / ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)) : ℝ) : ℂ) •
      (1 - D)

theorem isotropicBlockExpression_mix (α : Type*) [Fintype α] [DecidableEq α]
    (hcard : 2 ≤ Fintype.card α) (D : Matrix (α × α) (α × α) ℂ) (F q : ℝ) :
    (isotropicTwirlWeight α : ℂ) • isotropicBlockExpression α D F q +
      ((1 - isotropicTwirlWeight α : ℝ) : ℂ) •
        isotropicBlockExpression α D F ((1 - F - q) / (Fintype.card α : ℝ)) =
      isotropicState α F := by
  have hd : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hcard
  have hd0 : (Fintype.card α : ℂ) ≠ 0 := by
    exact_mod_cast (show (Fintype.card α : ℝ) ≠ 0 by linarith)
  have hm1 : (Fintype.card α : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (show (Fintype.card α : ℝ) - 1 ≠ 0 by linarith)
  have hp1 : (Fintype.card α : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show (Fintype.card α : ℝ) + 1 ≠ 0 by linarith)
  have hsq : (Fintype.card α : ℂ) ^ 2 - 1 ≠ 0 := by
    exact_mod_cast (show (Fintype.card α : ℝ) ^ 2 - 1 ≠ 0 by nlinarith)
  ext x y
  simp only [isotropicBlockExpression, isotropicTwirlWeight, isotropicState,
    Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  push_cast
  field_simp [hd0, hm1, hp1, hsq]
  ring

theorem isotropicEOFNat_le_of_two_finiteUnitaryOrbit_blocks
    {α ι κ : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [Fintype κ]
    (hcard : 2 ≤ Fintype.card α)
    (U : ι → Matrix.unitaryGroup α ℂ) (V : κ → Matrix.unitaryGroup α ℂ)
    (weightU : ι → ℝ) (weightV : κ → ℝ)
    (hwU : ∀ j, 0 ≤ weightU j) (hwV : ∀ j, 0 ≤ weightV j)
    (hsumU : ∑ j, weightU j = 1) (hsumV : ∑ j, weightV j = 1)
    (M : Coeff α α) (hM : IsNormalizedCoeff M)
    (D : Matrix (α × α) (α × α) ℂ) (F q : ℝ)
    (hblockU : finiteUnitaryOrbitState U weightU M = isotropicBlockExpression α D F q)
    (hblockV : finiteUnitaryOrbitState V weightV M =
      isotropicBlockExpression α D F ((1 - F - q) / (Fintype.card α : ℝ))) :
    isotropicEOFNat α F ≤ (pureEntropyNat M : EReal) := by
  let EU := finiteUnitaryOrbitEnsemble U weightU hwU hsumU M hM
  let EV := finiteUnitaryOrbitEnsemble V weightV hwV hsumV M hM
  have hweight := isotropicTwirlWeight_bounds α
  let E := EU.mix EV (isotropicTwirlWeight α) hweight.1 hweight.2
  have hcost : E.averageEntropy = pureEntropyNat M := by
    dsimp only [E]
    rw [FinitePureEnsemble.mix_averageEntropy]
    dsimp only [EU, EV]
    rw [finiteUnitaryOrbitEnsemble_averageEntropy,
      finiteUnitaryOrbitEnsemble_averageEntropy]
    ring
  have hstate : mixState (finiteUnitaryOrbitState U weightU M)
      (finiteUnitaryOrbitState V weightV M) (isotropicTwirlWeight α) =
        isotropicState α F := by
    simp only [mixState, hblockU, hblockV]
    exact isotropicBlockExpression_mix α hcard D F q
  have hroof := entanglementOfFormationNat_le_ensemble E
  have hroof' : entanglementOfFormationNat
      (mixState (finiteUnitaryOrbitState U weightU M)
        (finiteUnitaryOrbitState V weightV M) (isotropicTwirlWeight α)) ≤
      (pureEntropyNat M : EReal) := by
    simpa only [hcost] using hroof
  simpa only [hstate, isotropicEOFNat] using hroof'

section MatrixPreparationApplications

open scoped BigOperators ComplexOrder Matrix

variable {α : Type*} [Fintype α] [DecidableEq α]

def diagonalSqrtProbabilityKernel (q : α → ℝ) : α × α → ℂ :=
  fun x => (Real.sqrt (q x.1) : ℂ) * (Real.sqrt (q x.2) : ℂ)

theorem pureDensity_diagonalSqrtCoeff_eq_matrixDiagonalPairEmbedding (q : α → ℝ) :
    pureDensity (diagonalSqrtCoeff q) =
      matrixDiagonalPairEmbedding (diagonalSqrtProbabilityKernel q) := by
  ext x y
  by_cases hx : x.1 = x.2 <;> by_cases hy : y.1 = y.2 <;>
    simp [pureDensity, diagonalSqrtCoeff, realDiagonal, Matrix.diagonal_apply,
      matrixDiagonalPairEmbedding, diagonalSqrtProbabilityKernel, hx, hy]

theorem diagonalSqrtProbabilityKernel_diagonal_sum (q : α → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i = 1) :
    (∑ i, diagonalSqrtProbabilityKernel q (i, i)) = 1 := by
  calc
    _ = ((∑ i, q i : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro i _
      change (Real.sqrt (q i) : ℂ) * (Real.sqrt (q i) : ℂ) = (q i : ℂ)
      rw [← Complex.ofReal_mul]
      congr 1
      nlinarith [Real.sq_sqrt (hq i)]
    _ = 1 := by rw [hsum]; norm_num

theorem diagonalSqrtProbabilityKernel_sum (q : α → ℝ) :
    (∑ x, diagonalSqrtProbabilityKernel q x) =
      ((∑ i, Real.sqrt (q i) : ℝ) : ℂ) ^ 2 := by
  calc
    _ = ∑ i, ∑ j, (Real.sqrt (q i) : ℂ) * (Real.sqrt (q j) : ℂ) := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = (∑ i, (Real.sqrt (q i) : ℂ)) * (∑ j, (Real.sqrt (q j) : ℂ)) := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
    _ = _ := by push_cast <;> ring

theorem diagonalSqrtProbabilityKernel_fidelity (q : α → ℝ) :
    (∑ x, diagonalSqrtProbabilityKernel q x) / (Fintype.card α : ℂ) =
      (classicalBellFidelity q : ℂ) := by
  rw [diagonalSqrtProbabilityKernel_sum, classicalBellFidelity]
  push_cast <;> rfl

theorem matrixPermutationTwirl_diagonalSqrtCoeff (hcard : 2 ≤ Fintype.card α)
    (q : α → ℝ) (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i = 1) :
    matrixPermutationTwirl (pureDensity (diagonalSqrtCoeff q)) =
      isotropicBlockExpression α matrixDiagonalPairProjector
        (classicalBellFidelity q) (1 - classicalBellFidelity q) := by
  rw [pureDensity_diagonalSqrtCoeff_eq_matrixDiagonalPairEmbedding,
    matrixPermutationTwirl_diagonalPairEmbedding_eq _ hcard,
    diagonalSqrtProbabilityKernel_diagonal_sum q hq hsum,
    diagonalSqrtProbabilityKernel_fidelity]
  simp only [isotropicBlockExpression, sub_self, zero_div,
    Complex.ofReal_zero, zero_smul, add_zero]
  push_cast <;> rfl

theorem pureDensity_matrixUnitCoeff_eq_diagonal (i j : α) :
    pureDensity (matrixUnitCoeff i j) =
      Matrix.diagonal (fun x : α × α => if x = (i, j) then 1 else 0) := by
  have hcoeff (x : α × α) : matrixUnitCoeff i j x.1 x.2 =
      if x = (i, j) then 1 else 0 := by
    simp only [matrixUnitCoeff, Prod.ext_iff]
  ext x y
  simp only [pureDensity, hcoeff, Matrix.diagonal_apply]
  by_cases hx : x = (i, j) <;> by_cases hy : y = (i, j)
  · subst x
    subst y
    simp
  · have hxy : x ≠ y := fun h => hy (h.symm.trans hx)
    simp [hx, hy, hxy, Ne.symm hy]
  · have hxy : x ≠ y := fun h => hx (h.trans hy)
    simp [hx, hy, hxy]
  · by_cases hxy : x = y <;>
      simp [hx, hy, hxy]

theorem matrixPermutationTwirl_matrixUnitCoeff (i j : α) (hij : i ≠ j) :
    matrixPermutationTwirl (pureDensity (matrixUnitCoeff i j)) =
      isotropicBlockExpression α matrixDiagonalPairProjector 0 0 := by
  let f : α × α → ℂ := fun x => if x = (i, j) then 1 else 0
  have hf : ∀ a, f (a, a) = 0 := by
    intro a
    have hne : (a, a) ≠ (i, j) := by
      intro h
      have h1 : a = i := congrArg Prod.fst h
      have h2 : a = j := congrArg Prod.snd h
      exact hij (h1.symm.trans h2)
    simp only [f, if_neg hne]
  have hsum : (∑ x, f x) = 1 := by simp [f]
  rw [pureDensity_matrixUnitCoeff_eq_diagonal,
    matrixPermutationTwirl_zeroDiagonalPair f hf, hsum]
  simp only [isotropicBlockExpression, Complex.ofReal_zero, zero_smul,
    zero_div, sub_zero, zero_add]
  push_cast <;> rfl

theorem fourthPhaseTwirl_isotropicBlockExpression_flat
    (hcard : 2 ≤ Fintype.card α) (U : Matrix α α ℂ) (hU : Uᴴ * U = 1)
    (hflat : ∀ i j, Complex.normSq (U i j) = (Fintype.card α : ℝ)⁻¹)
    (F q : ℝ) :
    fourthPhaseTwirl
      (localPairCoeff U * isotropicBlockExpression α matrixDiagonalPairProjector F q *
        (localPairCoeff U)ᴴ) =
      isotropicBlockExpression α matrixDiagonalPairProjector F
        ((1 - F - q) / (Fintype.card α : ℝ)) := by
  have hUrow : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hBell := bellProjector_localPairCoeff U hUrow
  have hlocal := localPairCoeff_unitary_row U hU
  have hD := fourthPhaseTwirl_localPairDiagonal_flat U hflat
    (by omega : 0 < Fintype.card α)
  have hconj :
      localPairCoeff U * isotropicBlockExpression α matrixDiagonalPairProjector F q *
          (localPairCoeff U)ᴴ =
        (F : ℂ) • bellProjector +
          ((q / ((Fintype.card α : ℝ) - 1) : ℝ) : ℂ) •
            (localPairCoeff U * matrixDiagonalPairProjector * (localPairCoeff U)ᴴ -
              bellProjector) +
          (((1 - F - q) /
              ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)) : ℝ) : ℂ) •
            (1 - localPairCoeff U * matrixDiagonalPairProjector * (localPairCoeff U)ᴴ) := by
    simp only [isotropicBlockExpression, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hBell, hlocal]
  rw [hconj]
  simp only [fourthPhaseTwirl_add, fourthPhaseTwirl_sub, fourthPhaseTwirl_smul,
    fourthPhaseTwirl_bellProjector, fourthPhaseTwirl_one, hD]
  have hd : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hcard
  have hd0 : (Fintype.card α : ℂ) ≠ 0 := by
    exact_mod_cast (show (Fintype.card α : ℝ) ≠ 0 by linarith)
  have hm1 : (Fintype.card α : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (show (Fintype.card α : ℝ) - 1 ≠ 0 by linarith)
  ext x y
  simp only [isotropicBlockExpression, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  push_cast
  field_simp [hd0, hm1]
  ring

end MatrixPreparationApplications

section MatrixFiniteTwirlRecovery

open scoped BigOperators ComplexOrder Matrix

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem unitaryCoeffConj_mul (U V : Matrix.unitaryGroup α ℂ) (M : Coeff α α) :
    unitaryCoeffConj (U * V) M = unitaryCoeffConj U (unitaryCoeffConj V M) := by
  simp only [unitaryCoeffConj, Submonoid.coe_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

theorem finiteUnitaryOrbitState_left_conjugate {ι : Type*} [Fintype ι]
    (U : Matrix.unitaryGroup α ℂ) (V : ι → Matrix.unitaryGroup α ℂ)
    (weight : ι → ℝ) (M : Coeff α α) :
    localPairCoeff (U : Matrix α α ℂ) * finiteUnitaryOrbitState V weight M *
        (localPairCoeff (U : Matrix α α ℂ))ᴴ =
      finiteUnitaryOrbitState (fun j => U * V j) weight M := by
  simp only [finiteUnitaryOrbitState, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, pureDensity_localPairCoeff]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change pureDensity (unitaryCoeffConj U (unitaryCoeffConj (V j) M)) =
    pureDensity (unitaryCoeffConj (U * V j) M)
  rw [unitaryCoeffConj_mul]

theorem finiteUnitaryOrbitState_permutation_eq (M : Coeff α α) :
    finiteUnitaryOrbitState (matrixPermutationUnitary (α := α))
        (fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) M =
      matrixPermutationTwirl (pureDensity M) := by
  rw [finiteUnitaryOrbitState_uniform_eq, matrixPermutationTwirl_pureDensity]
  rfl

def phaseFourierPermutationUnitary {N : ℕ} [NeZero N] (e : α ≃ ZMod N)
    (j : (α → ZMod 4) × Equiv.Perm α) : Matrix.unitaryGroup α ℂ :=
  matrixFourthPhaseUnitary j.1 * (matrixFourierOnUnitary e * matrixPermutationUnitary j.2)

theorem finiteUnitaryOrbitState_phaseFourierPermutation_eq
    {N : ℕ} [NeZero N] (e : α ≃ ZMod N) (M : Coeff α α) :
    finiteUnitaryOrbitState (phaseFourierPermutationUnitary e)
        (fun _ => (Fintype.card ((α → ZMod 4) × Equiv.Perm α) : ℝ)⁻¹) M =
      fourthPhaseTwirl
        (localPairCoeff (normalizedFourierOn e) * matrixPermutationTwirl (pureDensity M) *
          (localPairCoeff (normalizedFourierOn e))ᴴ) := by
  have hFourier :
      localPairCoeff (normalizedFourierOn e) * matrixPermutationTwirl (pureDensity M) *
          (localPairCoeff (normalizedFourierOn e))ᴴ =
        finiteUnitaryOrbitState
          (fun σ => matrixFourierOnUnitary e * matrixPermutationUnitary σ)
          (fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) M := by
    rw [← finiteUnitaryOrbitState_permutation_eq M]
    exact finiteUnitaryOrbitState_left_conjugate
      (matrixFourierOnUnitary e) matrixPermutationUnitary _ M
  have hPhase (phase : α → ZMod 4) :
      fourthPhasePairCoeff phase *
          (localPairCoeff (normalizedFourierOn e) * matrixPermutationTwirl (pureDensity M) *
            (localPairCoeff (normalizedFourierOn e))ᴴ) * (fourthPhasePairCoeff phase)ᴴ =
        finiteUnitaryOrbitState
          (fun σ => matrixFourthPhaseUnitary phase *
            (matrixFourierOnUnitary e * matrixPermutationUnitary σ))
          (fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) M := by
    rw [fourthPhasePairCoeff_eq_localPairCoeff, hFourier]
    exact finiteUnitaryOrbitState_left_conjugate
      (matrixFourthPhaseUnitary phase) _ _ M
  calc
    finiteUnitaryOrbitState (phaseFourierPermutationUnitary e)
        (fun _ => (Fintype.card ((α → ZMod 4) × Equiv.Perm α) : ℝ)⁻¹) M =
      (Fintype.card (α → ZMod 4) : ℂ)⁻¹ • ∑ phase : α → ZMod 4,
        finiteUnitaryOrbitState
          (fun σ => matrixFourthPhaseUnitary phase *
            (matrixFourierOnUnitary e * matrixPermutationUnitary σ))
          (fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) M := by
      rw [finiteUnitaryOrbitState_uniform_eq]
      simp only [finiteUnitaryOrbitState_uniform_eq, Fintype.card_prod,
        Nat.cast_mul, mul_inv, Fintype.sum_prod_type, phaseFourierPermutationUnitary]
      rw [← Finset.smul_sum, smul_smul]
    _ = _ := by
      rw [fourthPhaseTwirl]
      congr 1
      exact Finset.sum_congr rfl (fun phase _ => (hPhase phase).symm)

theorem isotropicEOFNat_le_of_matrixPermutation_block
    (hcard : 2 ≤ Fintype.card α) (M : Coeff α α) (hM : IsNormalizedCoeff M)
    (F q : ℝ)
    (hblock : matrixPermutationTwirl (pureDensity M) =
      isotropicBlockExpression α matrixDiagonalPairProjector F q) :
    isotropicEOFNat α F ≤ (pureEntropyNat M : EReal) := by
  letI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  letI : NeZero (Fintype.card α) := ⟨by omega⟩
  let e : α ≃ ZMod (Fintype.card α) :=
    Fintype.equivOfCardEq (by rw [ZMod.card])
  refine isotropicEOFNat_le_of_two_finiteUnitaryOrbit_blocks hcard
    (matrixPermutationUnitary (α := α)) (phaseFourierPermutationUnitary e)
    (fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹)
    (fun _ => (Fintype.card ((α → ZMod 4) × Equiv.Perm α) : ℝ)⁻¹)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (uniformFiniteUnitaryOrbitWeight_sum (Equiv.Perm α))
    (uniformFiniteUnitaryOrbitWeight_sum ((α → ZMod 4) × Equiv.Perm α))
    M hM matrixDiagonalPairProjector F q ?_ ?_
  · rw [finiteUnitaryOrbitState_permutation_eq]
    exact hblock
  · rw [finiteUnitaryOrbitState_phaseFourierPermutation_eq, hblock]
    apply fourthPhaseTwirl_isotropicBlockExpression_flat hcard
      (normalizedFourierOn e) (normalizedFourierOn_unitary_col e)
    intro i j
    exact normalizedFourierOn_normSq e i j

theorem isotropicEOFNat_classicalBellFidelity_le_classicalEntropy
    (hcard : 2 ≤ Fintype.card α) (q : α → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i = 1) :
    isotropicEOFNat α (classicalBellFidelity q) ≤ (classicalEntropy q : EReal) := by
  have h := isotropicEOFNat_le_of_matrixPermutation_block hcard
    (diagonalSqrtCoeff q) (diagonalSqrtCoeff_normalized q hq hsum)
    (classicalBellFidelity q) (1 - classicalBellFidelity q)
    (matrixPermutationTwirl_diagonalSqrtCoeff hcard q hq hsum)
  rwa [pureEntropyNat_diagonalSqrtCoeff q hq] at h

theorem isotropicEOFNat_zero (hcard : 2 ≤ Fintype.card α) :
    isotropicEOFNat α 0 = 0 := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card α)
  apply le_antisymm
  · have h := isotropicEOFNat_le_of_matrixPermutation_block hcard
      (matrixUnitCoeff i j) (matrixUnitCoeff_normalized i j) 0 0
      (matrixPermutationTwirl_matrixUnitCoeff i j hij)
    simpa only [pureEntropyNat_matrixUnitCoeff, EReal.coe_zero] using h
  · exact entanglementOfFormationNat_nonneg _

end MatrixFiniteTwirlRecovery

section MatrixScalarRecoveryIntegration

open scoped BigOperators ComplexOrder
open Set

theorem isotropicEOFReal_approximate_scalar_support_of_matrix_recovery
    (α : Type*) [Fintype α] [DecidableEq α]
    (hcard : 2 ≤ Fintype.card α)
    (hzero : isotropicEOFNat α 0 = 0)
    (hrecovery : ∀ q : α → ℝ, (∀ i, 0 ≤ q i) → (∑ i, q i = 1) →
      isotropicEOFNat α (classicalBellFidelity q) ≤ (classicalEntropy q : EReal))
    (F : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (eps : ℝ) (heps : 0 < eps) :
    ∃ a b : ℝ, 0 ≤ b ∧ isotropicEOFReal α F - eps ≤ a + b * F ∧
      ∀ q : α → ℝ, (∀ i, 0 ≤ q i) → (∑ i, q i = 1) →
        a + b * classicalBellFidelity q ≤ classicalEntropy q := by
  letI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  by_cases hFzero : F = 0
  · subst F
    refine ⟨0, 0, le_rfl, ?_, ?_⟩
    · simp only [isotropicEOFReal, hzero, EReal.toReal_zero, zero_mul, add_zero]
      linarith
    · intro q hq hsum
      simpa only [zero_mul, add_zero] using classicalEntropy_nonneg q hq hsum
  by_cases hFone : F = 1
  · subst F
    obtain ⟨a, b, hb, hpoint, hsupport⟩ :=
      classicalBellFidelity_endpoint_affine_minorant (α := α) eps heps
    have hbell : isotropicEOFReal α 1 ≤ Real.log (Fintype.card α) := by
      apply EReal.coe_le_coe_iff.mp
      rw [isotropicEOFNat_coe_real α hcard 1 (by norm_num) (by norm_num)]
      exact isotropicEOFNat_one_le α (by omega)
    refine ⟨a, b, hb, ?_, hsupport⟩
    simpa only [mul_one] using (sub_le_sub_right hbell eps).trans hpoint
  have hFpos : 0 < F := lt_of_le_of_ne hF0 (Ne.symm hFzero)
  have hFlt : F < 1 := lt_of_le_of_ne hF1 hFone
  obtain ⟨a, b, hb, hpoint, hsupport⟩ :=
    isotropicEOFReal_affine_support_interior_of_zero α hcard hzero F hFpos hFlt
  refine ⟨a, b, hb, ?_, ?_⟩
  · rw [hpoint]
    exact sub_le_self _ heps.le
  · intro q hq hsum
    have hq0 : 0 ≤ classicalBellFidelity q := classicalBellFidelity_nonneg q
    have hq1 : classicalBellFidelity q ≤ 1 := classicalBellFidelity_le_one q hq hsum
    have hrecReal : isotropicEOFReal α (classicalBellFidelity q) ≤
        classicalEntropy q := by
      apply EReal.coe_le_coe_iff.mp
      rw [isotropicEOFNat_coe_real α hcard _ hq0 hq1]
      exact hrecovery q hq hsum
    exact (hsupport _ ⟨hq0, hq1⟩).trans hrecReal

theorem isotropic_twoFactor_EOF_lower_of_matrix_onecopy_recovery
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (hα : 2 ≤ Fintype.card α) (hβ : 2 ≤ Fintype.card β)
    (hzeroα : isotropicEOFNat α 0 = 0) (hzeroβ : isotropicEOFNat β 0 = 0)
    (hrecoveryα : ∀ q : α → ℝ, (∀ i, 0 ≤ q i) → (∑ i, q i = 1) →
      isotropicEOFNat α (classicalBellFidelity q) ≤ (classicalEntropy q : EReal))
    (hrecoveryβ : ∀ q : β → ℝ, (∀ i, 0 ≤ q i) → (∑ i, q i = 1) →
      isotropicEOFNat β (classicalBellFidelity q) ≤ (classicalEntropy q : EReal))
    (F1 F2 : ℝ) (hF10 : 0 ≤ F1) (hF11 : F1 ≤ 1)
    (hF20 : 0 ≤ F2) (hF21 : F2 ≤ 1) :
    isotropicEOFNat α F1 + isotropicEOFNat β F2 ≤
      entanglementOfFormationNat
        (tensorState (isotropicState α F1) (isotropicState β F2)) := by
  letI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  letI : Nonempty β := Fintype.card_pos_iff.mp (by omega)
  let ρ := tensorState (isotropicState α F1) (isotropicState β F2)
  have hρ : IsDensity ρ := tensorState_isDensity
    (isotropicState_isDensity α hα F1 hF10 hF11)
    (isotropicState_isDensity β hβ F2 hF20 hF21)
  let r : ℝ := (entanglementOfFormationNat ρ).toReal
  have hfinite : (r : EReal) = entanglementOfFormationNat ρ :=
    entanglementOfFormationNat_coe_toReal ρ hρ
  have hreal : isotropicEOFReal α F1 + isotropicEOFReal β F2 ≤ r := by
    by_contra hnot
    have hgap : 0 < isotropicEOFReal α F1 + isotropicEOFReal β F2 - r :=
      sub_pos.mpr (lt_of_not_ge hnot)
    let eps := (isotropicEOFReal α F1 + isotropicEOFReal β F2 - r) / 4
    have heps : 0 < eps := by dsimp only [eps]; linarith
    obtain ⟨a1, b1, hb1, hpoint1, hsupport1⟩ :=
      isotropicEOFReal_approximate_scalar_support_of_matrix_recovery
        α hα hzeroα hrecoveryα F1 hF10 hF11 eps heps
    obtain ⟨a2, b2, hb2, hpoint2, hsupport2⟩ :=
      isotropicEOFReal_approximate_scalar_support_of_matrix_recovery
        β hβ hzeroβ hrecoveryβ F2 hF20 hF21 eps heps
    have hlower := twoFactor_affine_lower_le_entanglementOfFormationNat
      ρ a1 b1 a2 b2 hb1 hb2 hsupport1 hsupport2
    dsimp only [ρ] at hlower
    rw [physicalFidelityLeft_tensor_isotropic F1 F2 hα hβ,
      physicalFidelityRight_tensor_isotropic F1 F2 hα hβ] at hlower
    have hscore : a1 + a2 + b1 * F1 + b2 * F2 ≤ r := by
      apply EReal.coe_le_coe_iff.mp
      rw [hfinite]
      exact hlower
    dsimp only [eps] at hpoint1 hpoint2
    linarith
  calc
    isotropicEOFNat α F1 + isotropicEOFNat β F2 =
        ((isotropicEOFReal α F1 + isotropicEOFReal β F2 : ℝ) : EReal) := by
      rw [EReal.coe_add, isotropicEOFNat_coe_real α hα F1 hF10 hF11,
        isotropicEOFNat_coe_real β hβ F2 hF20 hF21]
    _ ≤ (r : EReal) := EReal.coe_le_coe_iff.mpr hreal
    _ = entanglementOfFormationNat ρ := hfinite

theorem isotropic_twoFactor_EOF_eq_of_matrix_onecopy_recovery
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (hα : 2 ≤ Fintype.card α) (hβ : 2 ≤ Fintype.card β)
    (hzeroα : isotropicEOFNat α 0 = 0) (hzeroβ : isotropicEOFNat β 0 = 0)
    (hrecoveryα : ∀ q : α → ℝ, (∀ i, 0 ≤ q i) → (∑ i, q i = 1) →
      isotropicEOFNat α (classicalBellFidelity q) ≤ (classicalEntropy q : EReal))
    (hrecoveryβ : ∀ q : β → ℝ, (∀ i, 0 ≤ q i) → (∑ i, q i = 1) →
      isotropicEOFNat β (classicalBellFidelity q) ≤ (classicalEntropy q : EReal))
    (F1 F2 : ℝ) (hF10 : 0 ≤ F1) (hF11 : F1 ≤ 1)
    (hF20 : 0 ≤ F2) (hF21 : F2 ≤ 1) :
    entanglementOfFormationNat
        (tensorState (isotropicState α F1) (isotropicState β F2)) =
      isotropicEOFNat α F1 + isotropicEOFNat β F2 := by
  exact le_antisymm
    (entanglementOfFormationNat_tensor_le
      (isotropicState_isDensity α hα F1 hF10 hF11)
      (isotropicState_isDensity β hβ F2 hF20 hF21))
    (isotropic_twoFactor_EOF_lower_of_matrix_onecopy_recovery hα hβ
      hzeroα hzeroβ hrecoveryα hrecoveryβ F1 F2 hF10 hF11 hF20 hF21)

end MatrixScalarRecoveryIntegration

section TwoFactorFinalIntegration

open scoped BigOperators ComplexOrder

theorem isotropicEOFReal_approximate_scalar_support
    (α : Type*) [Fintype α] [DecidableEq α] (hcard : 2 ≤ Fintype.card α)
    (F : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (eps : ℝ) (heps : 0 < eps) :
    ∃ a b : ℝ, 0 ≤ b ∧ isotropicEOFReal α F - eps ≤ a + b * F ∧
      ∀ q : α → ℝ, (∀ i, 0 ≤ q i) → (∑ i, q i = 1) →
        a + b * classicalBellFidelity q ≤ classicalEntropy q :=
  isotropicEOFReal_approximate_scalar_support_of_matrix_recovery α hcard
    (isotropicEOFNat_zero hcard)
    (fun q hq hsum => isotropicEOFNat_classicalBellFidelity_le_classicalEntropy
      hcard q hq hsum) F hF0 hF1 eps heps

theorem isotropic_twoFactor_EOF_lower
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (hα : 2 ≤ Fintype.card α) (hβ : 2 ≤ Fintype.card β)
    (F1 F2 : ℝ) (hF10 : 0 ≤ F1) (hF11 : F1 ≤ 1)
    (hF20 : 0 ≤ F2) (hF21 : F2 ≤ 1) :
    isotropicEOFNat α F1 + isotropicEOFNat β F2 ≤
      entanglementOfFormationNat
        (tensorState (isotropicState α F1) (isotropicState β F2)) :=
  isotropic_twoFactor_EOF_lower_of_matrix_onecopy_recovery hα hβ
    (isotropicEOFNat_zero hα) (isotropicEOFNat_zero hβ)
    (fun q hq hsum => isotropicEOFNat_classicalBellFidelity_le_classicalEntropy hα q hq hsum)
    (fun q hq hsum => isotropicEOFNat_classicalBellFidelity_le_classicalEntropy hβ q hq hsum)
    F1 F2 hF10 hF11 hF20 hF21

theorem isotropic_twoFactor_EOF_additive (d1 d2 : ℕ) (hd1 : 2 ≤ d1) (hd2 : 2 ≤ d2)
    (F1 F2 : ℝ) (hF10 : 0 ≤ F1) (hF11 : F1 ≤ 1) (hF20 : 0 ≤ F2) (hF21 : F2 ≤ 1) :
    entanglementOfFormationNat
        (tensorState (isotropicState (Fin d1) F1) (isotropicState (Fin d2) F2)) =
      isotropicEOFNat (Fin d1) F1 + isotropicEOFNat (Fin d2) F2 := by
  have hcard1 : 2 ≤ Fintype.card (Fin d1) := by
    simpa only [Fintype.card_fin] using hd1
  have hcard2 : 2 ≤ Fintype.card (Fin d2) := by
    simpa only [Fintype.card_fin] using hd2
  exact le_antisymm
    (isotropic_twoFactor_EOF_upper d1 d2 hd1 hd2 F1 F2 hF10 hF11 hF20 hF21)
    (isotropic_twoFactor_EOF_lower hcard1 hcard2 F1 F2 hF10 hF11 hF20 hF21)

theorem twoFactorEOFAdditivity : TwoFactorEOFAdditivity := by
  intro d1 d2 hd1 hd2 F1 F2 hF10 hF11 hF20 hF21
  exact isotropic_twoFactor_EOF_additive d1 d2 hd1 hd2 F1 F2 hF10 hF11 hF20 hF21

end TwoFactorFinalIntegration

end QuantumProver.IsotropicFormation
