import QuantumProver.InformationTheory.IsotropicFormation.TwoFactorBounds
import QuantumProver.InformationTheory.IsotropicFormation.ProductEnsembles

noncomputable section

namespace QuantumProver.IsotropicFormation

open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
  ContinuousFunctionalCalculus

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_perm_hermitian_trace_ge (P : Matrix α α ℂ) (hP : P.IsHermitian)
    (h : α → ℝ) :
    ∃ σ : Equiv.Perm α,
      (Matrix.trace (P * realDiagonal h)).re ≤
        ∑ i, h i * hP.eigenvalues (σ i) := by
  let U := hP.eigenvectorUnitary
  have hcol : (U : Matrix α α ℂ)ᴴ * (U : Matrix α α ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hrow : (U : Matrix α α ℂ) * (U : Matrix α α ℂ)ᴴ = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self U
  have hdiag : P = (U : Matrix α α ℂ) *
      Matrix.diagonal (fun i => (hP.eigenvalues i : ℂ)) * (U : Matrix α α ℂ)ᴴ := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, rclikeComplexCast] using hP.spectral_theorem
  obtain ⟨σ, hσ⟩ := exists_perm_conjugated_trace_ge (U : Matrix α α ℂ)
    hcol hrow hP.eigenvalues h
  refine ⟨σ, ?_⟩
  simpa only [← hdiag, realDiagonal] using hσ

theorem pureEntropyNat_rightModulus (M : Coeff α α) :
    pureEntropyNat (rightModulus M) = pureEntropyNat M := by
  calc
    pureEntropyNat (rightModulus M) = vonNeumannEntropyNat (Mᴴ * M) :=
      pureEntropyNat_rightModulus_gram M
    _ = vonNeumannEntropyNat (M * Mᴴ) := vonNeumannEntropyNat_gram M
    _ = pureEntropyNat M := by rw [pureEntropyNat, aliceReduced_eq_gram]

theorem pureEntropyNat_perm_diagonal_spectrum (P : Coeff α α) (hP : P.IsHermitian)
    (σ : Equiv.Perm α) :
    pureEntropyNat (realDiagonal (hP.eigenvalues ∘ σ)) = pureEntropyNat P := by
  calc
    pureEntropyNat (realDiagonal (hP.eigenvalues ∘ σ)) =
        vonNeumannEntropyNat (realDiagonal (hP.eigenvalues ∘ σ) *
          realDiagonal (hP.eigenvalues ∘ σ)) := by
      rw [pureEntropyNat, aliceReduced_eq_gram, (realDiagonal_isHermitian _).eq]
    _ = classicalEntropy (fun i => hP.eigenvalues i ^ 2) :=
      vonNeumannEntropyNat_perm_diagonal_square hP.eigenvalues σ
    _ = vonNeumannEntropyNat (P * P) := (vonNeumannEntropyNat_square_spectral P hP).symm
    _ = pureEntropyNat P := by rw [pureEntropyNat, aliceReduced_eq_gram, hP.eq]

theorem pureEntropyNat_eq_of_hermitian_charpoly_eq (P Q : Coeff α α)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hc : P.charpoly = Q.charpoly) :
    pureEntropyNat P = pureEntropyNat Q := by
  simp only [pureEntropyNat, aliceReduced_eq_gram, hP.eq, hQ.eq]
  exact vonNeumannEntropyNat_square_eq_of_charpoly_eq P Q hP hQ hc

section PositiveDiagonalBridge

variable {β : Type*} [Fintype β] [DecidableEq β]

theorem positive_twoFactor_affine_lower_of_spectral_comparator
    (P : Coeff (α × β) (α × β)) (hP : P.PosSemidef) (hnorm : IsNormalizedCoeff P)
    (a1 b1 a2 b2 : ℝ)
    (h1 : ∀ q : α → ℝ, (∀ x, 0 ≤ q x) → (∑ x, q x = 1) →
      a1 + b1 * classicalBellFidelity q ≤ classicalEntropy q)
    (h2 : ∀ q : β → ℝ, (∀ y, 0 ≤ q y) → (∑ y, q y = 1) →
      a2 + b2 * classicalBellFidelity q ≤ classicalEntropy q)
    (σ : Equiv.Perm (α × β))
    (hscore : b1 * bellFidelityLeft P + b2 * bellFidelityRight P ≤
      b1 * bellFidelityLeft (realDiagonal (hP.isHermitian.eigenvalues ∘ σ)) +
        b2 * bellFidelityRight (realDiagonal (hP.isHermitian.eigenvalues ∘ σ))) :
    a1 + a2 + b1 * bellFidelityLeft P + b2 * bellFidelityRight P ≤ pureEntropyNat P := by
  let lambda := hP.isHermitian.eigenvalues ∘ σ
  let p := fun i => lambda i ^ 2
  have hlambda : ∀ i, 0 ≤ lambda i := fun i => hP.eigenvalues_nonneg (σ i)
  have hp : ∀ i, 0 ≤ p i := fun i => sq_nonneg (lambda i)
  have hsum : ∑ i, p i = 1 := by
    change (∑ i, lambda i ^ 2) = 1
    rw [← hsSq_realDiagonal lambda]
    exact (hsSq_perm_diagonal_spectrum P hP.isHermitian σ).trans hnorm
  have hdiag : diagonalSqrtCoeff p = realDiagonal lambda := diagonalSqrtCoeff_sq lambda hlambda
  have hbound := diagonalSqrtCoeff_twoFactor_affine_lower p hp hsum a1 b1 a2 b2 h1 h2
  rw [hdiag, pureEntropyNat_perm_diagonal_spectrum P hP.isHermitian σ] at hbound
  dsimp only [lambda] at hbound
  linarith

end PositiveDiagonalBridge

section TwoModuliReduction

variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty α] [Nonempty β]

theorem twoFactor_affine_lower_of_positive (a1 b1 a2 b2 : ℝ)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (hpositive : ∀ P : Coeff (α × β) (α × β), P.PosSemidef → IsNormalizedCoeff P →
      a1 + a2 + b1 * bellFidelityLeft P + b2 * bellFidelityRight P ≤ pureEntropyNat P)
    (M : Coeff (α × β) (α × β)) (hM : IsNormalizedCoeff M) :
    a1 + a2 + b1 * bellFidelityLeft M + b2 * bellFidelityRight M ≤ pureEntropyNat M := by
  have hleftNorm : IsNormalizedCoeff (leftModulus M) := by
    rw [IsNormalizedCoeff, hsSq_leftModulus]
    exact hM
  have hrightNorm : IsNormalizedCoeff (rightModulus M) := by
    rw [IsNormalizedCoeff, hsSq_rightModulus]
    exact hM
  have hleft := hpositive (leftModulus M) (leftModulus_posSemidef M) hleftNorm
  have hright := hpositive (rightModulus M) (rightModulus_posSemidef M) hrightNorm
  rw [pureEntropyNat_leftModulus] at hleft
  rw [pureEntropyNat_rightModulus] at hright
  have hf1 := mul_le_mul_of_nonneg_left (two_bellFidelityLeft_le_moduli M) hb1
  have hf2 := mul_le_mul_of_nonneg_left (two_bellFidelityRight_le_moduli M) hb2
  nlinarith

theorem twoFactor_affine_lower_of_spectral_rearrangement (a1 b1 a2 b2 : ℝ)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (h1 : ∀ q : α → ℝ, (∀ x, 0 ≤ q x) → (∑ x, q x = 1) →
      a1 + b1 * classicalBellFidelity q ≤ classicalEntropy q)
    (h2 : ∀ q : β → ℝ, (∀ y, 0 ≤ q y) → (∑ y, q y = 1) →
      a2 + b2 * classicalBellFidelity q ≤ classicalEntropy q)
    (hcomparator : ∀ (P : Coeff (α × β) (α × β)) (hP : P.PosSemidef)
      (w1 w2 : ℝ), 0 ≤ w1 → 0 ≤ w2 → ∃ σ : Equiv.Perm (α × β),
        w1 * hsSq (ptraceLeft P) + w2 * hsSq (ptraceRight P) ≤
          w1 * hsSq (ptraceLeft (realDiagonal (hP.isHermitian.eigenvalues ∘ σ))) +
            w2 * hsSq (ptraceRight (realDiagonal (hP.isHermitian.eigenvalues ∘ σ))))
    (M : Coeff (α × β) (α × β)) (hM : IsNormalizedCoeff M) :
    a1 + a2 + b1 * bellFidelityLeft M + b2 * bellFidelityRight M ≤ pureEntropyNat M := by
  apply twoFactor_affine_lower_of_positive a1 b1 a2 b2 hb1 hb2 _ M hM
  intro P hP hnorm
  obtain ⟨σ, hσ⟩ := hcomparator P hP (b1 / Fintype.card α) (b2 / Fintype.card β)
    (div_nonneg hb1 (Nat.cast_nonneg _)) (div_nonneg hb2 (Nat.cast_nonneg _))
  apply positive_twoFactor_affine_lower_of_spectral_comparator P hP hnorm
    a1 b1 a2 b2 h1 h2 σ
  simpa only [bellFidelityLeft, bellFidelityRight, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hσ

theorem twoFactor_affine_lower (a1 b1 a2 b2 : ℝ)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (h1 : ∀ q : α → ℝ, (∀ x, 0 ≤ q x) → (∑ x, q x = 1) →
      a1 + b1 * classicalBellFidelity q ≤ classicalEntropy q)
    (h2 : ∀ q : β → ℝ, (∀ y, 0 ≤ q y) → (∑ y, q y = 1) →
      a2 + b2 * classicalBellFidelity q ≤ classicalEntropy q)
    (M : Coeff (α × β) (α × β)) (hM : IsNormalizedCoeff M) :
    a1 + a2 + b1 * bellFidelityLeft M + b2 * bellFidelityRight M ≤ pureEntropyNat M := by
  apply twoFactor_affine_lower_of_spectral_rearrangement a1 b1 a2 b2 hb1 hb2 h1 h2
    ?_ M hM
  intro P hP w1 w2 hw1 hw2
  simpa only [realDiagonal, Function.comp_def] using
    exists_perm_twoFactor_quadratic_comparator P hP w1 w2 hw1 hw2

theorem FinitePureEnsemble.twoFactor_affine_lower
    {ρ : Matrix ((α × β) × (α × β)) ((α × β) × (α × β)) ℂ}
    (E : FinitePureEnsemble ρ) (a1 b1 a2 b2 : ℝ)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (h1 : ∀ q : α → ℝ, (∀ x, 0 ≤ q x) → (∑ x, q x = 1) →
      a1 + b1 * classicalBellFidelity q ≤ classicalEntropy q)
    (h2 : ∀ q : β → ℝ, (∀ y, 0 ≤ q y) → (∑ y, q y = 1) →
      a2 + b2 * classicalBellFidelity q ≤ classicalEntropy q) :
    a1 + a2 + b1 * physicalFidelityLeft ρ + b2 * physicalFidelityRight ρ ≤
      E.averageEntropy := by
  have hconst1 : (∑ j, E.weight j * a1) = a1 := by
    rw [← Finset.sum_mul, E.weight_sum, one_mul]
  have hconst2 : (∑ j, E.weight j * a2) = a2 := by
    rw [← Finset.sum_mul, E.weight_sum, one_mul]
  have hleft : (∑ j, E.weight j * (b1 * bellFidelityLeft (E.coeff j))) =
      b1 * physicalFidelityLeft ρ := by
    rw [E.bellMeanLeft, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => mul_left_comm _ _ _)
  have hright : (∑ j, E.weight j * (b2 * bellFidelityRight (E.coeff j))) =
      b2 * physicalFidelityRight ρ := by
    rw [E.bellMeanRight, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => mul_left_comm _ _ _)
  calc
    _ = ∑ j, E.weight j * (a1 + a2 + b1 * bellFidelityLeft (E.coeff j) +
        b2 * bellFidelityRight (E.coeff j)) := by
      simp only [mul_add, Finset.sum_add_distrib, hconst1, hconst2, hleft, hright]
    _ ≤ E.averageEntropy := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left
        (_root_.QuantumProver.IsotropicFormation.twoFactor_affine_lower
          a1 b1 a2 b2 hb1 hb2 h1 h2 (E.coeff j) (E.normalized j))
        (E.weight_nonneg j)

theorem twoFactor_affine_lower_le_entanglementOfFormationNat
    (ρ : Matrix ((α × β) × (α × β)) ((α × β) × (α × β)) ℂ)
    (a1 b1 a2 b2 : ℝ) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (h1 : ∀ q : α → ℝ, (∀ x, 0 ≤ q x) → (∑ x, q x = 1) →
      a1 + b1 * classicalBellFidelity q ≤ classicalEntropy q)
    (h2 : ∀ q : β → ℝ, (∀ y, 0 ≤ q y) → (∑ y, q y = 1) →
      a2 + b2 * classicalBellFidelity q ≤ classicalEntropy q) :
    ((a1 + a2 + b1 * physicalFidelityLeft ρ + b2 * physicalFidelityRight ρ : ℝ) : EReal) ≤
      entanglementOfFormationNat ρ := by
  rw [entanglementOfFormationNat]
  refine le_iInf fun E => ?_
  exact_mod_cast E.twoFactor_affine_lower a1 b1 a2 b2 hb1 hb2 h1 h2

end TwoModuliReduction

section ScalarEndpointSupport

variable [Nonempty α]

omit [DecidableEq α]

omit [Nonempty α] in
theorem classicalBellFidelity_nonneg (q : α → ℝ) : 0 ≤ classicalBellFidelity q :=
  div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

theorem classicalBellFidelity_le_one (q : α → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hsum : ∑ i, q i = 1) : classicalBellFidelity q ≤ 1 := by
  have hd : 0 < (Fintype.card α : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hsq : (∑ i, Real.sqrt (q i) ^ 2) = 1 := by
    calc
      _ = ∑ i, q i := Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hq i))
      _ = 1 := hsum
  apply (div_le_iff₀ hd).2
  simpa only [Finset.card_univ, hsq, mul_one, one_mul] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => Real.sqrt (q i)))

theorem classicalBellFidelity_eq_one_uniform (q : α → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hsum : ∑ i, q i = 1) (hf : classicalBellFidelity q = 1) :
    ∀ i, q i = (Fintype.card α : ℝ)⁻¹ := by
  let d : ℝ := Fintype.card α
  let s : ℝ := ∑ i, Real.sqrt (q i)
  have hd : 0 < d := Nat.cast_pos.mpr Fintype.card_pos
  have hsquares : (∑ i, Real.sqrt (q i) ^ 2) = 1 := by
    calc
      _ = ∑ i, q i := Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hq i))
      _ = 1 := hsum
  have hs : s ^ 2 = d := by
    have h := (div_eq_iff hd.ne').1 hf
    simpa only [classicalBellFidelity, d, s, one_mul] using h
  have hvariance : (∑ i, (Real.sqrt (q i) - s / d) ^ 2) = 0 := by
    calc
      _ = (∑ i, Real.sqrt (q i) ^ 2) -
          (2 * (s / d)) * (∑ i, Real.sqrt (q i)) +
          (Fintype.card α : ℝ) * (s / d) ^ 2 := by
        have hpoint : ∀ i, (Real.sqrt (q i) - s / d) ^ 2 =
            Real.sqrt (q i) ^ 2 - (2 * (s / d)) * Real.sqrt (q i) +
              (s / d) ^ 2 := fun i => by ring
        simp only [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 1 - s ^ 2 / d := by
        rw [hsquares]
        change 1 - 2 * (s / d) * s + d * (s / d) ^ 2 = 1 - s ^ 2 / d
        field_simp [hd.ne']
        ring
      _ = 0 := by rw [hs, div_self hd.ne', sub_self]
  have hzero : ∀ i, (Real.sqrt (q i) - s / d) ^ 2 = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 hvariance
      i (Finset.mem_univ i)
  have hsqrt : ∀ i, Real.sqrt (q i) = s / d := fun i => by
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hzero i))
  intro i
  have hqi : q i = (s / d) ^ 2 := by
    rw [← hsqrt i, Real.sq_sqrt (hq i)]
  rw [hqi]
  change (s / d) ^ 2 = d⁻¹
  rw [div_pow, hs]
  field_simp [hd.ne']

theorem classicalEntropy_uniform :
    classicalEntropy (fun _ : α => (Fintype.card α : ℝ)⁻¹) =
      Real.log (Fintype.card α : ℝ) := by
  have hd : (Fintype.card α : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos)
  simp only [classicalEntropy, Real.negMulLog, Real.log_inv, neg_mul_neg,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]

theorem classicalEntropy_eq_log_card_of_fidelity_one (q : α → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, q i = 1)
    (hf : classicalBellFidelity q = 1) :
    classicalEntropy q = Real.log (Fintype.card α : ℝ) := by
  have heq : q = fun _ => (Fintype.card α : ℝ)⁻¹ :=
    funext (classicalBellFidelity_eq_one_uniform q hq hsum hf)
  rw [heq]
  exact classicalEntropy_uniform

omit [Nonempty α] in
@[fun_prop] theorem continuous_classicalBellFidelity :
    Continuous (classicalBellFidelity (α := α)) := by
  unfold classicalBellFidelity
  fun_prop

omit [Nonempty α] in
@[fun_prop] theorem continuous_classicalEntropy :
    Continuous (classicalEntropy (α := α)) := by
  unfold classicalEntropy
  fun_prop

def classicalProbabilitySimplex (α : Type*) [Fintype α] : Set (α → ℝ) :=
  {q | (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1}

omit [Nonempty α] in
theorem isCompact_classicalProbabilitySimplex :
    IsCompact (classicalProbabilitySimplex α) := by
  have hclosed : IsClosed (classicalProbabilitySimplex α) := by
    have hset : classicalProbabilitySimplex α =
        (⋂ i, {q : α → ℝ | 0 ≤ q i}) ∩ {q | ∑ i, q i = 1} := by
      ext q
      simp only [classicalProbabilitySimplex, Set.mem_ofPred_eq,
        Set.mem_inter_iff, Set.mem_iInter]
    rw [hset]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  have hsub : classicalProbabilitySimplex α ⊆ Set.Icc (0 : α → ℝ) 1 := by
    intro q hq
    refine ⟨hq.1, ?_⟩
    intro i
    have hle : q i ≤ ∑ j, q j :=
      Finset.single_le_sum (fun j _ => hq.1 j) (Finset.mem_univ i)
    simpa only [hq.2, Pi.one_apply] using hle
  exact isCompact_Icc.of_isClosed_subset hclosed hsub

theorem classicalBellFidelity_endpoint_affine_minorant (eps : ℝ) (heps : 0 < eps) :
    ∃ a b : ℝ, 0 ≤ b ∧ Real.log (Fintype.card α : ℝ) - eps ≤ a + b ∧
      ∀ q : α → ℝ, (∀ i, 0 ≤ q i) → (∑ i, q i = 1) →
        a + b * classicalBellFidelity q ≤ classicalEntropy q := by
  let c : ℝ := Real.log (Fintype.card α : ℝ) - eps
  by_cases hc : c ≤ 0
  · refine ⟨c, 0, le_rfl, ?_, ?_⟩
    · simp only [add_zero]
      exact le_rfl
    · intro q hq hsum
      simpa only [zero_mul, add_zero] using
        hc.trans (classicalEntropy_nonneg q hq hsum)
  have hcpos : 0 < c := lt_of_not_ge hc
  let bad : Set (α → ℝ) := classicalProbabilitySimplex α ∩
    {q | classicalEntropy q ≤ c}
  have hcompact : IsCompact bad :=
    isCompact_classicalProbabilitySimplex.inter_right
      (isClosed_le continuous_classicalEntropy continuous_const)
  by_cases hbad : bad.Nonempty
  · obtain ⟨q0, hq0, hmax⟩ := hcompact.exists_isMaxOn hbad
      continuous_classicalBellFidelity.continuousOn
    let m := classicalBellFidelity q0
    have hm : m < 1 := by
      have hle : m ≤ 1 := classicalBellFidelity_le_one q0 hq0.1.1 hq0.1.2
      by_contra hnot
      have heq : classicalBellFidelity q0 = 1 := le_antisymm hle (not_lt.mp hnot)
      have hentropy := classicalEntropy_eq_log_card_of_fidelity_one q0
        hq0.1.1 hq0.1.2 heq
      have hsmall : classicalEntropy q0 ≤ c := hq0.2
      dsimp only [c] at hsmall
      linarith
    let b := c / (1 - m)
    have hb : 0 ≤ b := div_nonneg hcpos.le (sub_pos.mpr hm).le
    have hbden : b * (1 - m) = c := div_mul_cancel₀ c (sub_pos.mpr hm).ne'
    refine ⟨c - b, b, hb, ?_, ?_⟩
    · dsimp only [c]
      linarith
    · intro q hq hsum
      have hnn : 0 ≤ classicalEntropy q := classicalEntropy_nonneg q hq hsum
      by_cases hlow : classicalEntropy q ≤ c
      · have hqm : classicalBellFidelity q ≤ m := hmax ⟨⟨hq, hsum⟩, hlow⟩
        calc
          c - b + b * classicalBellFidelity q ≤ c - b + b * m :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hqm hb)
          _ = 0 := by nlinarith [hbden]
          _ ≤ classicalEntropy q := hnn
      · have hqone := classicalBellFidelity_le_one q hq hsum
        calc
          c - b + b * classicalBellFidelity q ≤ c - b + b * 1 :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hqone hb)
          _ = c := by ring
          _ ≤ classicalEntropy q := (lt_of_not_ge hlow).le
  · refine ⟨c, 0, le_rfl, ?_, ?_⟩
    · simp only [add_zero]
      exact le_rfl
    · intro q hq hsum
      have hgt : c < classicalEntropy q := lt_of_not_ge fun hlow =>
        hbad ⟨q, ⟨⟨hq, hsum⟩, hlow⟩⟩
      simpa only [zero_mul, add_zero] using hgt.le

end ScalarEndpointSupport

end QuantumProver.IsotropicFormation
