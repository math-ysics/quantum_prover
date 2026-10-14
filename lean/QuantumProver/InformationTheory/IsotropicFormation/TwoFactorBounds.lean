import QuantumProver.InformationTheory.IsotropicFormation.Definitions

noncomputable section

namespace QuantumProver.IsotropicFormation

open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Kronecker

variable {α β : Type*} [Fintype α] [Fintype β]

def rightModulus [DecidableEq β] (M : Matrix α β ℂ) : Matrix β β ℂ :=
  CFC.sqrt (Mᴴ * M)

def leftModulus [DecidableEq α] (M : Matrix α β ℂ) : Matrix α α ℂ :=
  CFC.sqrt (M * Mᴴ)

theorem rightModulus_posSemidef [DecidableEq β] (M : Matrix α β ℂ) :
    (rightModulus M).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Mᴴ * M))

theorem leftModulus_posSemidef [DecidableEq α] (M : Matrix α β ℂ) :
    (leftModulus M).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M * Mᴴ))

theorem rightModulus_square [DecidableEq β] (M : Matrix α β ℂ) :
    rightModulus M * rightModulus M = Mᴴ * M := by
  rw [rightModulus, ← pow_two]
  exact CFC.sq_sqrt (Mᴴ * M) (Matrix.posSemidef_conjTranspose_mul_self M).nonneg

theorem leftModulus_square [DecidableEq α] (M : Matrix α β ℂ) :
    leftModulus M * leftModulus M = M * Mᴴ := by
  rw [leftModulus, ← pow_two]
  exact CFC.sq_sqrt (M * Mᴴ) (Matrix.posSemidef_self_mul_conjTranspose M).nonneg

theorem hsSq_rightModulus [DecidableEq β] (M : Matrix α β ℂ) :
    hsSq (rightModulus M) = hsSq M := by
  rw [hsSq_eq_trace_conjTranspose_mul_self,
    (rightModulus_posSemidef M).isHermitian.eq, rightModulus_square]
  exact (hsSq_eq_trace_conjTranspose_mul_self M).symm

theorem hsSq_leftModulus [DecidableEq α] (M : Matrix α β ℂ) :
    hsSq (leftModulus M) = hsSq M := by
  rw [hsSq_eq_trace_conjTranspose_mul_self,
    (leftModulus_posSemidef M).isHermitian.eq, leftModulus_square]
  exact (hsSq_eq_trace_self_mul_conjTranspose M).symm

theorem aliceReduced_eq_gram (M : Matrix α β ℂ) :
    aliceReduced M = M * Mᴴ := by
  ext i j
  simp [aliceReduced, ptraceRight, pureDensity, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

theorem pureEntropyNat_leftModulus [DecidableEq α] (M : Matrix α β ℂ) :
    pureEntropyNat (leftModulus M) = pureEntropyNat M := by
  simp only [pureEntropyNat, aliceReduced_eq_gram,
    (leftModulus_posSemidef M).isHermitian.eq, leftModulus_square]

theorem pureEntropyNat_rightModulus_gram [DecidableEq β] (M : Matrix α β ℂ) :
    pureEntropyNat (rightModulus M) = vonNeumannEntropyNat (Mᴴ * M) := by
  simp only [pureEntropyNat, aliceReduced_eq_gram,
    (rightModulus_posSemidef M).isHermitian.eq, rightModulus_square]

theorem weighted_ptrace_comparator [DecidableEq α] [DecidableEq β]
    (P D : Matrix (α × β) (α × β) ℂ) (w₁ w₂ : ℝ)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hcross : w₁ * hsSq (ptraceLeft P) + w₂ * hsSq (ptraceRight P) ≤
      w₁ * hsInner (ptraceLeft P) (ptraceLeft D) +
      w₂ * hsInner (ptraceRight P) (ptraceRight D)) :
    w₁ * hsSq (ptraceLeft P) + w₂ * hsSq (ptraceRight P) ≤
      w₁ * hsSq (ptraceLeft D) + w₂ * hsSq (ptraceRight D) := by
  have h := weighted_ptrace_square_completion D P w₁ w₂ hw₁ hw₂
  linarith

section GramBlocks

variable {γ : Type*} [Fintype γ]

theorem hsSq_gram_swap (A : Matrix α γ ℂ) :
    hsSq (A * Aᴴ) = hsSq (Aᴴ * A) := by
  rw [hsSq_eq_trace_self_mul_conjTranspose,
    (Matrix.isHermitian_mul_conjTranspose_self A).eq,
    hsSq_eq_trace_self_mul_conjTranspose,
    (Matrix.isHermitian_conjTranspose_mul_self A).eq]
  apply congrArg Complex.re
  calc
    _ = Matrix.trace (A * (Aᴴ * A) * Aᴴ) := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_cycle A (Aᴴ * A) Aᴴ

theorem hsSq_cross_gram (A : Matrix α γ ℂ) (B : Matrix β γ ℂ) :
    hsSq (A * Bᴴ) = hsInner (Aᴴ * A) (Bᴴ * B) := by
  rw [hsSq_eq_trace_self_mul_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose,
    hsInner_hermitian_eq_trace _ _ (Matrix.isHermitian_conjTranspose_mul_self A)]
  apply congrArg Complex.re
  calc
    _ = Matrix.trace (A * (Bᴴ * B) * Aᴴ) := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = _ := Matrix.trace_mul_cycle A (Bᴴ * B) Aᴴ

theorem hsSq_cross_gram_sq_le (A : Matrix α γ ℂ) (B : Matrix β γ ℂ) :
    hsSq (A * Bᴴ) ^ 2 ≤ hsSq (A * Aᴴ) * hsSq (B * Bᴴ) := by
  have h := hsInner_sq_le (Aᴴ * A) (Bᴴ * B)
  rw [← hsSq_cross_gram A B, ← hsSq_gram_swap A, ← hsSq_gram_swap B] at h
  exact h

end GramBlocks

theorem positive_block_hsSq_sq_le [DecidableEq α] [DecidableEq β]
    (Q : Matrix α α ℂ) (P : Matrix β β ℂ) (X : Matrix α β ℂ)
    (hK : (Matrix.fromBlocks Q X Xᴴ P).PosSemidef) :
    hsSq X ^ 2 ≤ hsSq Q * hsSq P := by
  let K := Matrix.fromBlocks Q X Xᴴ P
  let S := CFC.sqrt K
  have hS : Sᴴ = S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K)).isHermitian.eq
  have hSS : S * Sᴴ = K := by
    rw [hS]
    simpa only [pow_two] using CFC.sq_sqrt K hK.nonneg
  let A : Matrix α (α ⊕ β) ℂ := fun i r => S (Sum.inl i) r
  let B : Matrix β (α ⊕ β) ℂ := fun j r => S (Sum.inr j) r
  have hA : A * Aᴴ = Q := by
    ext i j
    have h := congrArg (fun T : Matrix (α ⊕ β) (α ⊕ β) ℂ =>
      T (Sum.inl i) (Sum.inl j)) hSS
    change (∑ r : α ⊕ β, S (Sum.inl i) r * star (S (Sum.inl j) r)) = Q i j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, K] using h
  have hB : B * Bᴴ = P := by
    ext i j
    have h := congrArg (fun T : Matrix (α ⊕ β) (α ⊕ β) ℂ =>
      T (Sum.inr i) (Sum.inr j)) hSS
    change (∑ r : α ⊕ β, S (Sum.inr i) r * star (S (Sum.inr j) r)) = P i j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, K] using h
  have hX : A * Bᴴ = X := by
    ext i j
    have h := congrArg (fun T : Matrix (α ⊕ β) (α ⊕ β) ℂ =>
      T (Sum.inl i) (Sum.inr j)) hSS
    change (∑ r : α ⊕ β, S (Sum.inl i) r * star (S (Sum.inr j) r)) = X i j
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, K] using h
  have h := hsSq_cross_gram_sq_le A B
  rw [hA, hB, hX] at h
  exact h

theorem positive_block_hsSq_arithmetic_mean [DecidableEq α] [DecidableEq β]
    (Q : Matrix α α ℂ) (P : Matrix β β ℂ) (X : Matrix α β ℂ)
    (hK : (Matrix.fromBlocks Q X Xᴴ P).PosSemidef) :
    2 * hsSq X ≤ hsSq Q + hsSq P := by
  have h := positive_block_hsSq_sq_le Q P X hK
  have hQ := hsSq_nonneg Q
  have hP := hsSq_nonneg P
  have hX := hsSq_nonneg X
  by_contra hn
  have hgap : 0 < 2 * hsSq X - (hsSq Q + hsSq P) := by linarith
  have hsum : 0 < 2 * hsSq X + hsSq Q + hsSq P := by linarith
  have hp := mul_pos hgap hsum
  nlinarith [sq_nonneg (hsSq Q - hsSq P)]

section CoefficientBlockTrace

variable [DecidableEq α] [DecidableEq β]

theorem ptraceLeft_positive_block
    (Q P X : Matrix (α × β) (α × β) ℂ)
    (hK : (Matrix.fromBlocks Q X Xᴴ P).PosSemidef) :
    (Matrix.fromBlocks (ptraceLeft Q) (ptraceLeft X)
      (ptraceLeft X)ᴴ (ptraceLeft P)).PosSemidef := by
  let e (i : α) : β ⊕ β → (α × β) ⊕ (α × β) :=
    Sum.map (fun j => (i, j)) (fun j => (i, j))
  have hp := Matrix.posSemidef_sum (Finset.univ : Finset α)
    (fun i _ => hK.submatrix (e i))
  have heq : (∑ i, (Matrix.fromBlocks Q X Xᴴ P).submatrix (e i) (e i)) =
      Matrix.fromBlocks (ptraceLeft Q) (ptraceLeft X)
        (ptraceLeft X)ᴴ (ptraceLeft P) := by
    ext x y
    cases x <;> cases y <;>
      simp [e, Matrix.sum_apply, Matrix.submatrix_apply, ptraceLeft,
        Matrix.conjTranspose_apply, star_sum]
  rw [heq] at hp
  simpa using hp

theorem ptraceLeft_positive_block_arithmetic_mean
    (Q P X : Matrix (α × β) (α × β) ℂ)
    (hK : (Matrix.fromBlocks Q X Xᴴ P).PosSemidef) :
    2 * hsSq (ptraceLeft X) ≤ hsSq (ptraceLeft Q) + hsSq (ptraceLeft P) :=
  positive_block_hsSq_arithmetic_mean _ _ _ (ptraceLeft_positive_block Q P X hK)

theorem ptraceRight_positive_block
    (Q P X : Matrix (α × β) (α × β) ℂ)
    (hK : (Matrix.fromBlocks Q X Xᴴ P).PosSemidef) :
    (Matrix.fromBlocks (ptraceRight Q) (ptraceRight X)
      (ptraceRight X)ᴴ (ptraceRight P)).PosSemidef := by
  let e (j : β) : α ⊕ α → (α × β) ⊕ (α × β) :=
    Sum.map (fun i => (i, j)) (fun i => (i, j))
  have hp := Matrix.posSemidef_sum (Finset.univ : Finset β)
    (fun j _ => hK.submatrix (e j))
  have heq : (∑ j, (Matrix.fromBlocks Q X Xᴴ P).submatrix (e j) (e j)) =
      Matrix.fromBlocks (ptraceRight Q) (ptraceRight X)
        (ptraceRight X)ᴴ (ptraceRight P) := by
    ext x y
    cases x <;> cases y <;>
      simp [e, Matrix.sum_apply, Matrix.submatrix_apply, ptraceRight,
        Matrix.conjTranspose_apply, star_sum]
  rw [heq] at hp
  simpa using hp

theorem ptraceRight_positive_block_arithmetic_mean
    (Q P X : Matrix (α × β) (α × β) ℂ)
    (hK : (Matrix.fromBlocks Q X Xᴴ P).PosSemidef) :
    2 * hsSq (ptraceRight X) ≤ hsSq (ptraceRight Q) + hsSq (ptraceRight P) :=
  positive_block_hsSq_arithmetic_mean _ _ _ (ptraceRight_positive_block Q P X hK)

end CoefficientBlockTrace

theorem fromBlocks_zero_posSemidef [DecidableEq α] [DecidableEq β]
    (Q : Matrix α α ℂ) (P : Matrix β β ℂ)
    (hQ : Q.PosSemidef) (hP : P.PosSemidef) :
    (Matrix.fromBlocks Q 0 0 P).PosSemidef := by
  let V := Matrix.fromBlocks (CFC.sqrt Q) (0 : Matrix α β ℂ)
    (0 : Matrix β α ℂ) (CFC.sqrt P)
  have hQroot : (CFC.sqrt Q)ᴴ = CFC.sqrt Q :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)).isHermitian.eq
  have hProot : (CFC.sqrt P)ᴴ = CFC.sqrt P :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian.eq
  have hV : V * Vᴴ = Matrix.fromBlocks Q 0 0 P := by
    simp [V, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      hQroot, hProot, CFC.sqrt_mul_sqrt_self Q hQ.nonneg,
      CFC.sqrt_mul_sqrt_self P hP.nonneg]
  exact hV ▸ Matrix.posSemidef_self_mul_conjTranspose V

theorem modulus_block_posSemidef [DecidableEq α] [DecidableEq β]
    (M : Matrix α β ℂ) :
    (Matrix.fromBlocks (leftModulus M) M Mᴴ (rightModulus M)).PosSemidef := by
  let H := Matrix.fromBlocks (0 : Matrix α α ℂ) M Mᴴ (0 : Matrix β β ℂ)
  let D := Matrix.fromBlocks (leftModulus M) (0 : Matrix α β ℂ)
    (0 : Matrix β α ℂ) (rightModulus M)
  have hH : H.IsHermitian := by
    change Hᴴ = H
    simp [H, Matrix.fromBlocks_conjTranspose]
  have hD : D.PosSemidef := fromBlocks_zero_posSemidef _ _
    (leftModulus_posSemidef M) (rightModulus_posSemidef M)
  have hDsquare : D * D = Hᴴ * H := by
    simp [D, H, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      leftModulus_square, rightModulus_square]
  have habs : CFC.abs H = D := by
    unfold CFC.abs
    apply (CFC.sqrt_eq_iff _ _
      (Matrix.posSemidef_conjTranspose_mul_self H).nonneg hD.nonneg).2
    exact hDsquare
  have hp : 0 ≤ CFC.abs H + H := by
    rw [CFC.abs_add_self H hH.isSelfAdjoint, two_smul]
    exact add_nonneg (CFC.posPart_nonneg H) (CFC.posPart_nonneg H)
  have heq : CFC.abs H + H =
      Matrix.fromBlocks (leftModulus M) M Mᴴ (rightModulus M) := by
    rw [habs]
    ext i j
    cases i <;> cases j <;> simp [D, H]
  rw [heq] at hp
  exact Matrix.nonneg_iff_posSemidef.mp hp

theorem two_bellFidelityLeft_le_moduli [DecidableEq α] [DecidableEq β]
    [Nonempty α] (M : Matrix (α × β) (α × β) ℂ) :
    2 * bellFidelityLeft M ≤
      bellFidelityLeft (leftModulus M) + bellFidelityLeft (rightModulus M) := by
  have h := ptraceLeft_positive_block_arithmetic_mean _ _ _
    (modulus_block_posSemidef M)
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  unfold bellFidelityLeft
  calc
    _ = (2 * hsSq (ptraceLeft M)) / Fintype.card α := by ring
    _ ≤ (hsSq (ptraceLeft (leftModulus M)) +
        hsSq (ptraceLeft (rightModulus M))) / Fintype.card α :=
      (div_le_div_iff_of_pos_right hc).2 h
    _ = _ := by ring

theorem two_bellFidelityRight_le_moduli [DecidableEq α] [DecidableEq β]
    [Nonempty β] (M : Matrix (α × β) (α × β) ℂ) :
    2 * bellFidelityRight M ≤
      bellFidelityRight (leftModulus M) + bellFidelityRight (rightModulus M) := by
  have h := ptraceRight_positive_block_arithmetic_mean _ _ _
    (modulus_block_posSemidef M)
  have hc : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  unfold bellFidelityRight
  calc
    _ = (2 * hsSq (ptraceRight M)) / Fintype.card β := by ring
    _ ≤ (hsSq (ptraceRight (leftModulus M)) +
        hsSq (ptraceRight (rightModulus M))) / Fintype.card β :=
      (div_le_div_iff_of_pos_right hc).2 h
    _ = _ := by ring

section PhysicalBellBridge

variable [DecidableEq α] [DecidableEq β]

theorem trace_pureDensity_pairBellLeft
    (M : Matrix (α × β) (α × β) ℂ) :
    Matrix.trace (pureDensity M * pairBellProjectorLeft) =
      ((bellFidelityLeft M : ℝ) : ℂ) := by
  let c : ℂ := (((Fintype.card α : ℝ)⁻¹ : ℝ) : ℂ)
  calc
    _ = ∑ i : α, ∑ j : β, ∑ l : β, ∑ k : α,
        M (i, j) (i, l) * star (M (k, j) (k, l)) * c := by
      simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pureDensity,
        pairBellProjectorLeft, bellProjector_apply, Fintype.sum_prod_type,
        Prod.mk.injEq, ite_and, mul_ite, ite_mul, Finset.sum_ite_irrel, c]
    _ = ∑ j : β, ∑ l : β, ∑ i : α, ∑ k : α,
        M (i, j) (i, l) * star (M (k, j) (k, l)) * c := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
    _ = ∑ j : β, ∑ l : β,
        ((Complex.normSq (∑ i : α, M (i, j) (i, l)) : ℝ) : ℂ) * c := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      rw [normSq_sum_complex]
      simp only [Finset.sum_mul]
    _ = _ := by
      simp [bellFidelityLeft, hsSq, ptraceLeft, c, div_eq_mul_inv,
        Finset.sum_mul]

theorem trace_pureDensity_pairBellRight
    (M : Matrix (α × β) (α × β) ℂ) :
    Matrix.trace (pureDensity M * pairBellProjectorRight) =
      ((bellFidelityRight M : ℝ) : ℂ) := by
  let c : ℂ := (((Fintype.card β : ℝ)⁻¹ : ℝ) : ℂ)
  calc
    _ = ∑ i : α, ∑ j : β, ∑ k : α, ∑ l : β,
        M (i, j) (k, j) * star (M (i, l) (k, l)) * c := by
      simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, pureDensity,
        pairBellProjectorRight, bellProjector_apply, Fintype.sum_prod_type,
        Prod.mk.injEq, ite_and, mul_ite, ite_mul, Finset.sum_ite_irrel, c]
    _ = ∑ i : α, ∑ k : α, ∑ j : β, ∑ l : β,
        M (i, j) (k, j) * star (M (i, l) (k, l)) * c := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i : α, ∑ k : α,
        ((Complex.normSq (∑ j : β, M (i, j) (k, j)) : ℝ) : ℂ) * c := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      rw [normSq_sum_complex]
      simp only [Finset.sum_mul]
    _ = _ := by
      simp [bellFidelityRight, hsSq, ptraceRight, c, div_eq_mul_inv,
        Finset.sum_mul]

theorem physicalFidelityLeft_pureDensity
    (M : Matrix (α × β) (α × β) ℂ) :
    physicalFidelityLeft (pureDensity M) = bellFidelityLeft M := by
  unfold physicalFidelityLeft
  rw [trace_pureDensity_pairBellLeft]
  simp

theorem physicalFidelityRight_pureDensity
    (M : Matrix (α × β) (α × β) ℂ) :
    physicalFidelityRight (pureDensity M) = bellFidelityRight M := by
  unfold physicalFidelityRight
  rw [trace_pureDensity_pairBellRight]
  simp

theorem physicalFidelityLeft_sum {ι : Type*} [Fintype ι]
    (ρ : ι → Matrix ((α × β) × (α × β)) ((α × β) × (α × β)) ℂ) :
    physicalFidelityLeft (∑ j, ρ j) = ∑ j, physicalFidelityLeft (ρ j) := by
  simp [physicalFidelityLeft, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]

theorem physicalFidelityRight_sum {ι : Type*} [Fintype ι]
    (ρ : ι → Matrix ((α × β) × (α × β)) ((α × β) × (α × β)) ℂ) :
    physicalFidelityRight (∑ j, ρ j) = ∑ j, physicalFidelityRight (ρ j) := by
  simp [physicalFidelityRight, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]

theorem physicalFidelityLeft_real_smul (w : ℝ)
    (ρ : Matrix ((α × β) × (α × β)) ((α × β) × (α × β)) ℂ) :
    physicalFidelityLeft ((w : ℂ) • ρ) = w * physicalFidelityLeft ρ := by
  simp [physicalFidelityLeft, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re]

theorem physicalFidelityRight_real_smul (w : ℝ)
    (ρ : Matrix ((α × β) × (α × β)) ((α × β) × (α × β)) ℂ) :
    physicalFidelityRight ((w : ℂ) • ρ) = w * physicalFidelityRight ρ := by
  simp [physicalFidelityRight, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re]

theorem FinitePureEnsemble.bellMeanLeft
    {ρ : Matrix ((α × β) × (α × β)) ((α × β) × (α × β)) ℂ}
    (E : FinitePureEnsemble ρ) :
    physicalFidelityLeft ρ = ∑ j, E.weight j * bellFidelityLeft (E.coeff j) := by
  calc
    _ = physicalFidelityLeft (∑ j, (E.weight j : ℂ) • pureDensity (E.coeff j)) :=
      congrArg physicalFidelityLeft E.barycenter
    _ = ∑ j, physicalFidelityLeft ((E.weight j : ℂ) • pureDensity (E.coeff j)) :=
      physicalFidelityLeft_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [physicalFidelityLeft_real_smul, physicalFidelityLeft_pureDensity]

theorem FinitePureEnsemble.bellMeanRight
    {ρ : Matrix ((α × β) × (α × β)) ((α × β) × (α × β)) ℂ}
    (E : FinitePureEnsemble ρ) :
    physicalFidelityRight ρ = ∑ j, E.weight j * bellFidelityRight (E.coeff j) := by
  calc
    _ = physicalFidelityRight (∑ j, (E.weight j : ℂ) • pureDensity (E.coeff j)) :=
      congrArg physicalFidelityRight E.barycenter
    _ = ∑ j, physicalFidelityRight ((E.weight j : ℂ) • pureDensity (E.coeff j)) :=
      physicalFidelityRight_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [physicalFidelityRight_real_smul, physicalFidelityRight_pureDensity]

end PhysicalBellBridge

section MatrixUnitaryCoordinates

variable [DecidableEq α] [DecidableEq β]

theorem tensorCoeff_eq_kronecker (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    tensorCoeff A B = A ⊗ₖ B := rfl

theorem tensorCoeff_unitary_col (U : Matrix α α ℂ) (V : Matrix β β ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    (tensorCoeff U V)ᴴ * tensorCoeff U V = 1 := by
  rw [tensorCoeff_eq_kronecker, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, hU, hV, Matrix.one_kronecker_one]

theorem tensorCoeff_unitary_row (U : Matrix α α ℂ) (V : Matrix β β ℂ)
    (hU : U * Uᴴ = 1) (hV : V * Vᴴ = 1) :
    tensorCoeff U V * (tensorCoeff U V)ᴴ = 1 := by
  rw [tensorCoeff_eq_kronecker, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, hU, hV, Matrix.one_kronecker_one]

theorem gram_unitary_conj (U M : Matrix α α ℂ) (hU : Uᴴ * U = 1) :
    (U * M * Uᴴ) * (U * M * Uᴴ)ᴴ = U * (M * Mᴴ) * Uᴴ := by
  calc
    _ = U * M * (Uᴴ * U) * Mᴴ * Uᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    _ = _ := by rw [hU]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem trace_unitary_conj (U A : Matrix α α ℂ) (hU : Uᴴ * U = 1) :
    Matrix.trace (U * A * Uᴴ) = Matrix.trace A := by
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

theorem hsSq_unitary_conj (U A : Matrix α α ℂ) (hU : Uᴴ * U = 1) :
    hsSq (U * A * Uᴴ) = hsSq A := by
  rw [hsSq_eq_trace_self_mul_conjTranspose, gram_unitary_conj U A hU,
    trace_unitary_conj U _ hU, ← hsSq_eq_trace_self_mul_conjTranspose]

theorem liftLeft_eq_kronecker (B : Matrix β β ℂ) :
    liftLeft B = (1 : Matrix α α ℂ) ⊗ₖ B := by
  ext x y
  by_cases h : x.1 = y.1 <;> simp [liftLeft, Matrix.one_apply, h]

theorem liftRight_eq_kronecker (A : Matrix α α ℂ) :
    liftRight A = A ⊗ₖ (1 : Matrix β β ℂ) := by
  ext x y
  by_cases h : x.2 = y.2 <;> simp [liftRight, Matrix.one_apply, h]

theorem liftLeft_product_unitary_conj (U : Matrix α α ℂ)
    (V B : Matrix β β ℂ) (hU : U * Uᴴ = 1) :
    tensorCoeff U V * liftLeft B * (tensorCoeff U V)ᴴ =
      liftLeft (V * B * Vᴴ) := by
  rw [tensorCoeff_eq_kronecker, liftLeft_eq_kronecker,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, hU, liftLeft_eq_kronecker]

theorem liftRight_product_unitary_conj (U A : Matrix α α ℂ)
    (V : Matrix β β ℂ) (hV : V * Vᴴ = 1) :
    tensorCoeff U V * liftRight A * (tensorCoeff U V)ᴴ =
      liftRight (U * A * Uᴴ) := by
  rw [tensorCoeff_eq_kronecker, liftRight_eq_kronecker,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one, hV, liftRight_eq_kronecker]

end MatrixUnitaryCoordinates

section WeightedSiteField

variable [DecidableEq α] [DecidableEq β]

def weightedSiteField (P : Matrix (α × β) (α × β) ℂ) (w₁ w₂ : ℝ) :
    Matrix (α × β) (α × β) ℂ :=
  (w₁ : ℂ) • liftLeft (ptraceLeft P) +
    (w₂ : ℂ) • liftRight (ptraceRight P)

theorem hsInner_add_right (A B C : Matrix α β ℂ) :
    hsInner A (B + C) = hsInner A B + hsInner A C := by
  simp [hsInner, Matrix.add_apply, mul_add, Complex.add_re,
    Finset.sum_add_distrib]

theorem hsInner_real_smul_right (A B : Matrix α β ℂ) (w : ℝ) :
    hsInner A ((w : ℂ) • B) = w * hsInner A B := by
  simp only [hsInner, Matrix.smul_apply, smul_eq_mul]
  have hentry (i : α) (j : β) :
      (star (A i j) * ((w : ℂ) * B i j)).re =
        w * (star (A i j) * B i j).re := by
    rw [mul_left_comm, Complex.mul_re]
    simp
  simp only [hentry, ← Finset.mul_sum]

theorem hsInner_weightedSiteField
    (D P : Matrix (α × β) (α × β) ℂ) (w₁ w₂ : ℝ) :
    hsInner D (weightedSiteField P w₁ w₂) =
      w₁ * hsInner (ptraceLeft D) (ptraceLeft P) +
        w₂ * hsInner (ptraceRight D) (ptraceRight P) := by
  simp only [weightedSiteField, hsInner_add_right, hsInner_real_smul_right,
    hsInner_liftLeft, hsInner_liftRight]

theorem hsInner_self_weightedSiteField
    (P : Matrix (α × β) (α × β) ℂ) (w₁ w₂ : ℝ) :
    hsInner P (weightedSiteField P w₁ w₂) =
      w₁ * hsSq (ptraceLeft P) + w₂ * hsSq (ptraceRight P) := by
  simp only [hsInner_weightedSiteField, hsInner_self]

theorem weighted_quadratic_ge_of_siteField_trace
    (P D : Matrix (α × β) (α × β) ℂ) (w₁ w₂ : ℝ)
    (hP : P.IsHermitian) (hD : D.IsHermitian)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (htrace : (Matrix.trace (P * weightedSiteField P w₁ w₂)).re ≤
      (Matrix.trace (D * weightedSiteField P w₁ w₂)).re) :
    w₁ * hsSq (ptraceLeft P) + w₂ * hsSq (ptraceRight P) ≤
      w₁ * hsSq (ptraceLeft D) + w₂ * hsSq (ptraceRight D) := by
  apply weighted_ptrace_comparator P D w₁ w₂ hw₁ hw₂
  rw [← hsInner_hermitian_eq_trace _ _ hP,
    ← hsInner_hermitian_eq_trace _ _ hD,
    hsInner_self_weightedSiteField, hsInner_weightedSiteField] at htrace
  simpa only [hsInner_comm] using htrace

end WeightedSiteField

section SpectralAssignment

variable [DecidableEq α]

theorem exists_perm_linear_ge (K : Matrix α α ℝ)
    (hK : K ∈ doublyStochastic ℝ α)
    (ℓ : Matrix α α ℝ →ₗ[ℝ] ℝ) :
    ∃ σ : Equiv.Perm α, ℓ K ≤ ℓ (σ.permMatrix ℝ) := by
  classical
  obtain ⟨w, hw, hsum, hdecomp⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic hK
  obtain ⟨σ, hσmem, hσmax⟩ := Finset.exists_max_image Finset.univ
    (fun σ : Equiv.Perm α => ℓ (σ.permMatrix ℝ)) Finset.univ_nonempty
  refine ⟨σ, ?_⟩
  calc
    ℓ K = ∑ τ : Equiv.Perm α, w τ * ℓ (τ.permMatrix ℝ) := by
      rw [← hdecomp, map_sum]
      simp only [map_smul, smul_eq_mul]
    _ ≤ ∑ τ : Equiv.Perm α, w τ * ℓ (σ.permMatrix ℝ) := by
      exact Finset.sum_le_sum (fun τ hτ =>
        mul_le_mul_of_nonneg_left (hσmax τ hτ) (hw τ))
    _ = ℓ (σ.permMatrix ℝ) := by rw [← Finset.sum_mul, hsum, one_mul]

def matrixPairingLinear (x y : α → ℝ) : Matrix α α ℝ →ₗ[ℝ] ℝ where
  toFun K := ∑ i, ∑ j, K i j * x i * y j
  map_add' A B := by simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r A := by
    simp [Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem exists_perm_pairing_ge (K : Matrix α α ℝ)
    (hK : K ∈ doublyStochastic ℝ α) (x y : α → ℝ) :
    ∃ σ : Equiv.Perm α,
      (∑ i, ∑ j, K i j * x i * y j) ≤ ∑ i, x i * y (σ i) := by
  obtain ⟨σ, hσ⟩ := exists_perm_linear_ge K hK (matrixPairingLinear x y)
  refine ⟨σ, ?_⟩
  simpa [matrixPairingLinear, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, ite_mul] using hσ

def unitarySquaredWeights (U : Matrix α α ℂ) : Matrix α α ℝ :=
  fun i j => Complex.normSq (U i j)

theorem unitarySquaredWeights_doublyStochastic (U : Matrix α α ℂ)
    (hcol : Uᴴ * U = 1) (hrow : U * Uᴴ = 1) :
    unitarySquaredWeights U ∈ doublyStochastic ℝ α := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, ?_, ?_⟩
  · intro i
    have h := congrArg (fun A : Matrix α α ℂ => (A i i).re) hrow
    simpa [unitarySquaredWeights, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Complex.mul_re, Complex.normSq_apply, Complex.re_sum] using h
  · intro j
    have h := congrArg (fun A : Matrix α α ℂ => (A j j).re) hcol
    simpa [unitarySquaredWeights, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Complex.mul_re, Complex.normSq_apply, Complex.re_sum] using h

theorem conjugated_diagonal_entry (U : Matrix α α ℂ) (lambda : α → ℝ) (i : α) :
    (U * Matrix.diagonal (fun j => (lambda j : ℂ)) * Uᴴ) i i =
      ∑ j, (Complex.normSq (U i j) : ℂ) * (lambda j : ℂ) := by
  have hentry (j : α) : U i j * (lambda j : ℂ) * star (U i j) =
      (Complex.normSq (U i j) : ℂ) * (lambda j : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply] <;> ring
  simpa [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    hentry] using (Finset.sum_congr rfl (fun j _ => hentry j))

theorem trace_conjugated_diagonal_score (U : Matrix α α ℂ)
    (lambda h : α → ℝ) :
    (Matrix.trace ((U * Matrix.diagonal (fun j => (lambda j : ℂ)) * Uᴴ) *
      Matrix.diagonal (fun i => (h i : ℂ)))).re =
      ∑ i, ∑ j, unitarySquaredWeights U i j * h i * lambda j := by
  calc
    _ = ∑ i, ((U * Matrix.diagonal (fun j => (lambda j : ℂ)) * Uᴴ) i i *
        (h i : ℂ)).re := by
      simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
        Complex.re_sum]
    _ = _ := by
      simp only [conjugated_diagonal_entry, Finset.sum_mul, Complex.re_sum,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, sub_zero, unitarySquaredWeights]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem exists_perm_conjugated_trace_ge (U : Matrix α α ℂ)
    (hcol : Uᴴ * U = 1) (hrow : U * Uᴴ = 1) (lambda h : α → ℝ) :
    ∃ σ : Equiv.Perm α,
      (Matrix.trace ((U * Matrix.diagonal (fun j => (lambda j : ℂ)) * Uᴴ) *
        Matrix.diagonal (fun i => (h i : ℂ)))).re ≤ ∑ i, h i * lambda (σ i) := by
  rw [trace_conjugated_diagonal_score]
  exact exists_perm_pairing_ge _ (unitarySquaredWeights_doublyStochastic U hcol hrow) h lambda

end SpectralAssignment

section DiagonalTraceComparator

variable [DecidableEq α] [DecidableEq β]

theorem weightedSiteField_diagonal
    (P : Matrix (α × β) (α × β) ℂ) (w₁ w₂ : ℝ)
    (μ : β → ℝ) (ν : α → ℝ)
    (hleft : ptraceLeft P = Matrix.diagonal (fun j => (μ j : ℂ)))
    (hright : ptraceRight P = Matrix.diagonal (fun i => (ν i : ℂ))) :
    weightedSiteField P w₁ w₂ =
      Matrix.diagonal (fun x : α × β => ((w₁ * μ x.2 + w₂ * ν x.1 : ℝ) : ℂ)) := by
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨k, l⟩
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [weightedSiteField, hleft, hright, liftLeft, liftRight,
      Matrix.diagonal_apply, Matrix.add_apply, Matrix.smul_apply,
      hik, hjl, Prod.mk.injEq, smul_eq_mul]

theorem trace_diagonal_real_product (lambda h : α → ℝ) :
    (Matrix.trace (Matrix.diagonal (fun i => (lambda i : ℂ)) *
      Matrix.diagonal (fun i => (h i : ℂ)))).re = ∑ i, lambda i * h i := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Complex.re_sum, Complex.mul_re]

theorem exists_perm_weighted_quadratic_ge_of_diagonal_traces
    (P U : Matrix (α × β) (α × β) ℂ) (lambda : α × β → ℝ)
    (hP : P.IsHermitian)
    (hcol : Uᴴ * U = 1) (hrow : U * Uᴴ = 1)
    (hdecomp : P = U * Matrix.diagonal (fun x => (lambda x : ℂ)) * Uᴴ)
    (μ : β → ℝ) (ν : α → ℝ)
    (hleft : ptraceLeft P = Matrix.diagonal (fun j => (μ j : ℂ)))
    (hright : ptraceRight P = Matrix.diagonal (fun i => (ν i : ℂ)))
    (w₁ w₂ : ℝ) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) :
    ∃ σ : Equiv.Perm (α × β),
      w₁ * hsSq (ptraceLeft P) + w₂ * hsSq (ptraceRight P) ≤
        w₁ * hsSq (ptraceLeft (Matrix.diagonal (fun x => (lambda (σ x) : ℂ)))) +
        w₂ * hsSq (ptraceRight (Matrix.diagonal (fun x => (lambda (σ x) : ℂ)))) := by
  let h : α × β → ℝ := fun x => w₁ * μ x.2 + w₂ * ν x.1
  obtain ⟨σ, hσ⟩ := exists_perm_conjugated_trace_ge U hcol hrow lambda h
  let D : Matrix (α × β) (α × β) ℂ :=
    Matrix.diagonal (fun x => (lambda (σ x) : ℂ))
  have hD : D.IsHermitian := by
    change Dᴴ = D
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    · simp [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hxy, Ne.symm hxy]
  have hfield : weightedSiteField P w₁ w₂ =
      Matrix.diagonal (fun x => (h x : ℂ)) :=
    weightedSiteField_diagonal P w₁ w₂ μ ν hleft hright
  have htrace : (Matrix.trace (P * weightedSiteField P w₁ w₂)).re ≤
      (Matrix.trace (D * weightedSiteField P w₁ w₂)).re := by
    rw [hfield, hdecomp, trace_diagonal_real_product]
    simpa only [mul_comm] using hσ
  exact ⟨σ, weighted_quadratic_ge_of_siteField_trace P D w₁ w₂ hP hD
    hw₁ hw₂ htrace⟩

end DiagonalTraceComparator

section FullProductSpectralTransport

variable [DecidableEq α] [DecidableEq β]

private theorem weighted_lifts_diagonal (μ : β → ℝ) (ν : α → ℝ) (w₁ w₂ : ℝ) :
    (w₁ : ℂ) • liftLeft (Matrix.diagonal (fun j => (μ j : ℂ))) +
      (w₂ : ℂ) • liftRight (Matrix.diagonal (fun i => (ν i : ℂ))) =
        Matrix.diagonal (fun x : α × β => ((w₁ * μ x.2 + w₂ * ν x.1 : ℝ) : ℂ)) := by
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨k, l⟩
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [liftLeft, liftRight, Matrix.diagonal_apply, Matrix.add_apply,
      Matrix.smul_apply, hik, hjl, Prod.mk.injEq, smul_eq_mul]

private theorem weightedSiteField_product_spectral
    (P : Matrix (α × β) (α × β) ℂ)
    (U : Matrix α α ℂ) (V : Matrix β β ℂ) (μ : β → ℝ) (ν : α → ℝ)
    (hU : U * Uᴴ = 1) (hV : V * Vᴴ = 1)
    (hleft : ptraceLeft P = V * Matrix.diagonal (fun j => (μ j : ℂ)) * Vᴴ)
    (hright : ptraceRight P = U * Matrix.diagonal (fun i => (ν i : ℂ)) * Uᴴ)
    (w₁ w₂ : ℝ) :
    weightedSiteField P w₁ w₂ = tensorCoeff U V *
      Matrix.diagonal (fun x : α × β => ((w₁ * μ x.2 + w₂ * ν x.1 : ℝ) : ℂ)) *
        (tensorCoeff U V)ᴴ := by
  rw [weightedSiteField, hleft, hright, ← weighted_lifts_diagonal μ ν w₁ w₂]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    liftLeft_product_unitary_conj U V _ hU,
    liftRight_product_unitary_conj U _ V hV]

private theorem eigenvector_unitary_decomposition_B (A : Matrix α α ℂ)
    (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix α α ℂ) *
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
        (hA.eigenvectorUnitary : Matrix α α ℂ)ᴴ := by
  simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Function.comp_def, rclikeComplexCast] using hA.spectral_theorem

private theorem trace_against_unitary_coordinates (P K B : Matrix α α ℂ) :
    Matrix.trace (P * (K * B * Kᴴ)) = Matrix.trace ((Kᴴ * P * K) * B) := by
  calc
    _ = Matrix.trace ((P * K) * B * Kᴴ) := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Kᴴ * (P * K) * B) := Matrix.trace_mul_cycle (P * K) B Kᴴ
    _ = _ := by congr 1; simp only [Matrix.mul_assoc]

theorem exists_perm_twoFactor_quadratic_comparator
    (P : Matrix (α × β) (α × β) ℂ) (hP : P.PosSemidef)
    (w₁ w₂ : ℝ) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) :
    ∃ σ : Equiv.Perm (α × β),
      w₁ * hsSq (ptraceLeft P) + w₂ * hsSq (ptraceRight P) ≤
        w₁ * hsSq (ptraceLeft (Matrix.diagonal
          (fun x => (hP.isHermitian.eigenvalues (σ x) : ℂ)))) +
        w₂ * hsSq (ptraceRight (Matrix.diagonal
          (fun x => (hP.isHermitian.eigenvalues (σ x) : ℂ)))) := by
  let hA : (ptraceRight P).IsHermitian := (ptraceRight_posSemidef P hP).isHermitian
  let hB : (ptraceLeft P).IsHermitian := (ptraceLeft_posSemidef P hP).isHermitian
  let ν : α → ℝ := hA.eigenvalues
  let μ : β → ℝ := hB.eigenvalues
  let lambda : α × β → ℝ := hP.isHermitian.eigenvalues
  let U : Matrix α α ℂ := hA.eigenvectorUnitary
  let V : Matrix β β ℂ := hB.eigenvectorUnitary
  let W : Matrix (α × β) (α × β) ℂ := hP.isHermitian.eigenvectorUnitary
  have hUcol : Uᴴ * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUrow : U * Uᴴ = 1 := by
    simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hVcol : Vᴴ * V = 1 := by
    simpa only [V, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have hVrow : V * Vᴴ = 1 := by
    simpa only [V, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hB.eigenvectorUnitary
  have hWcol : Wᴴ * W = 1 := by
    simpa only [W, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hP.isHermitian.eigenvectorUnitary
  have hWrow : W * Wᴴ = 1 := by
    simpa only [W, Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hP.isHermitian.eigenvectorUnitary
  have hleft : ptraceLeft P = V * Matrix.diagonal (fun j => (μ j : ℂ)) * Vᴴ := by
    simpa only [V, μ] using eigenvector_unitary_decomposition_B (ptraceLeft P) hB
  have hright : ptraceRight P = U * Matrix.diagonal (fun i => (ν i : ℂ)) * Uᴴ := by
    simpa only [U, ν] using eigenvector_unitary_decomposition_B (ptraceRight P) hA
  have hglobal : P = W * Matrix.diagonal (fun x => (lambda x : ℂ)) * Wᴴ := by
    simpa only [W, lambda] using eigenvector_unitary_decomposition_B P hP.isHermitian
  let K := tensorCoeff U V
  have hKcol : Kᴴ * K = 1 := tensorCoeff_unitary_col U V hUcol hVcol
  have hKrow : K * Kᴴ = 1 := tensorCoeff_unitary_row U V hUrow hVrow
  let T := Kᴴ * W
  have hTcol : Tᴴ * T = 1 := by
    calc
      _ = Wᴴ * (K * Kᴴ) * W := by
        simp only [T, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = 1 := by rw [hKrow, Matrix.mul_one, hWcol]
  have hTrow : T * Tᴴ = 1 := by
    calc
      _ = Kᴴ * (W * Wᴴ) * K := by
        simp only [T, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = 1 := by rw [hWrow, Matrix.mul_one, hKcol]
  let h : α × β → ℝ := fun x => w₁ * μ x.2 + w₂ * ν x.1
  have hfield : weightedSiteField P w₁ w₂ =
      K * Matrix.diagonal (fun x => (h x : ℂ)) * Kᴴ :=
    weightedSiteField_product_spectral P U V μ ν hUrow hVrow hleft hright w₁ w₂
  have hcoord : Kᴴ * P * K = T * Matrix.diagonal (fun x => (lambda x : ℂ)) * Tᴴ := by
    rw [hglobal]
    simp only [T, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  obtain ⟨σ, hσ⟩ := exists_perm_conjugated_trace_ge T hTcol hTrow lambda h
  let D : Matrix (α × β) (α × β) ℂ :=
    Matrix.diagonal (fun x => (lambda (σ x) : ℂ))
  have hD : D.IsHermitian := by
    change Dᴴ = D
    ext x y
    by_cases hxy : x = y
    · subst y; simp [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    · simp [D, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hxy, Ne.symm hxy]
  have htrace : w₁ * hsSq (ptraceLeft P) + w₂ * hsSq (ptraceRight P) ≤
      (Matrix.trace (D * Matrix.diagonal (fun x => (h x : ℂ)))).re := by
    calc
      _ = (Matrix.trace (P * weightedSiteField P w₁ w₂)).re := by
        rw [← hsInner_hermitian_eq_trace _ _ hP.isHermitian,
          hsInner_self_weightedSiteField]
      _ = (Matrix.trace ((T * Matrix.diagonal (fun x => (lambda x : ℂ)) * Tᴴ) *
          Matrix.diagonal (fun x => (h x : ℂ)))).re := by
        rw [hfield, trace_against_unitary_coordinates, hcoord]
      _ ≤ ∑ x, h x * lambda (σ x) := hσ
      _ = _ := by
        rw [trace_diagonal_real_product]
        exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)
  have hcross : w₁ * hsSq (ptraceLeft P) + w₂ * hsSq (ptraceRight P) ≤
      w₁ * hsInner (ptraceLeft D) (Matrix.diagonal (fun j => (μ j : ℂ))) +
        w₂ * hsInner (ptraceRight D) (Matrix.diagonal (fun i => (ν i : ℂ))) := by
    have hdiag : Matrix.diagonal (fun x => (h x : ℂ)) =
        (w₁ : ℂ) • liftLeft (Matrix.diagonal (fun j => (μ j : ℂ))) +
          (w₂ : ℂ) • liftRight (Matrix.diagonal (fun i => (ν i : ℂ))) :=
      (weighted_lifts_diagonal μ ν w₁ w₂).symm
    rw [hdiag, ← hsInner_hermitian_eq_trace _ _ hD,
      hsInner_add_right, hsInner_real_smul_right, hsInner_real_smul_right,
      hsInner_liftLeft, hsInner_liftRight] at htrace
    exact htrace
  have hLnorm : hsSq (ptraceLeft P) = hsSq (Matrix.diagonal (fun j => (μ j : ℂ))) := by
    rw [hleft]
    exact hsSq_unitary_conj V _ hVcol
  have hRnorm : hsSq (ptraceRight P) = hsSq (Matrix.diagonal (fun i => (ν i : ℂ))) := by
    rw [hright]
    exact hsSq_unitary_conj U _ hUcol
  have hsqL := mul_le_mul_of_nonneg_left
    (hsSq_square_completion (ptraceLeft D) (Matrix.diagonal (fun j => (μ j : ℂ)))) hw₁
  have hsqR := mul_le_mul_of_nonneg_left
    (hsSq_square_completion (ptraceRight D) (Matrix.diagonal (fun i => (ν i : ℂ)))) hw₂
  refine ⟨σ, ?_⟩
  change w₁ * hsSq (ptraceLeft P) + w₂ * hsSq (ptraceRight P) ≤
    w₁ * hsSq (ptraceLeft D) + w₂ * hsSq (ptraceRight D)
  rw [hsInner_comm (Matrix.diagonal (fun j => (μ j : ℂ))) (ptraceLeft D), ← hLnorm] at hsqL
  rw [hsInner_comm (Matrix.diagonal (fun i => (ν i : ℂ))) (ptraceRight D), ← hRnorm] at hsqR
  nlinarith

end FullProductSpectralTransport

section MatrixPhysicalTensorFidelities

variable {γ δ : Type*} [Fintype γ] [Fintype δ]

theorem tensorState_eq_kronecker_submatrix
    (ρ : Matrix (α × β) (α × β) ℂ) (σ : Matrix (γ × δ) (γ × δ) ℂ) :
    tensorState ρ σ = (ρ ⊗ₖ σ).submatrix
      (Equiv.prodProdProdComm α γ β δ) (Equiv.prodProdProdComm α γ β δ) := rfl

theorem tensorState_mul
    (ρ A : Matrix (α × β) (α × β) ℂ)
    (σ B : Matrix (γ × δ) (γ × δ) ℂ) :
    tensorState ρ σ * tensorState A B = tensorState (ρ * A) (σ * B) := by
  let e := Equiv.prodProdProdComm α γ β δ
  calc
    _ = ((ρ ⊗ₖ σ) * (A ⊗ₖ B)).submatrix e e := by
      change (ρ ⊗ₖ σ).submatrix e e * (A ⊗ₖ B).submatrix e e = _
      exact Matrix.submatrix_mul_equiv _ _ _ e _
    _ = _ := by rw [← Matrix.mul_kronecker_mul]; rfl

theorem trace_tensorState
    (ρ : Matrix (α × β) (α × β) ℂ) (σ : Matrix (γ × δ) (γ × δ) ℂ) :
    Matrix.trace (tensorState ρ σ) = Matrix.trace ρ * Matrix.trace σ := by
  let e := Equiv.prodProdProdComm α γ β δ
  calc
    _ = Matrix.trace (ρ ⊗ₖ σ) := by
      change (∑ x, (ρ ⊗ₖ σ) (e x) (e x)) = ∑ x, (ρ ⊗ₖ σ) x x
      exact e.sum_comp (fun x => (ρ ⊗ₖ σ) x x)
    _ = _ := Matrix.trace_kronecker ρ σ

end MatrixPhysicalTensorFidelities

section MatrixIsotropicFidelities

variable [DecidableEq α] [DecidableEq β]

theorem pairBellProjectorLeft_eq_tensorState :
    (pairBellProjectorLeft : Matrix ((α × β) × (α × β)) ((α × β) × (α × β)) ℂ) =
      tensorState (bellProjector : Matrix (α × α) (α × α) ℂ)
        (1 : Matrix (β × β) (β × β) ℂ) := by
  ext x y
  simp only [pairBellProjectorLeft, tensorState, Matrix.one_apply]

theorem pairBellProjectorRight_eq_tensorState :
    (pairBellProjectorRight : Matrix ((α × β) × (α × β)) ((α × β) × (α × β)) ℂ) =
      tensorState (1 : Matrix (α × α) (α × α) ℂ)
        (bellProjector : Matrix (β × β) (β × β) ℂ) := by
  ext x y
  simp only [pairBellProjectorRight, tensorState, Matrix.one_apply]

theorem trace_tensorState_pairBellLeft
    (ρ : Matrix (α × α) (α × α) ℂ) (σ : Matrix (β × β) (β × β) ℂ) :
    Matrix.trace (tensorState ρ σ * pairBellProjectorLeft) =
      Matrix.trace (ρ * bellProjector) * Matrix.trace σ := by
  rw [pairBellProjectorLeft_eq_tensorState, tensorState_mul,
    trace_tensorState, Matrix.mul_one]

theorem trace_tensorState_pairBellRight
    (ρ : Matrix (α × α) (α × α) ℂ) (σ : Matrix (β × β) (β × β) ℂ) :
    Matrix.trace (tensorState ρ σ * pairBellProjectorRight) =
      Matrix.trace ρ * Matrix.trace (σ * bellProjector) := by
  rw [pairBellProjectorRight_eq_tensorState, tensorState_mul,
    trace_tensorState, Matrix.mul_one]

theorem isotropicState_mul_bellProjector (F : ℝ) (hα : 0 < Fintype.card α) :
    isotropicState α F * bellProjector =
      (F : ℂ) • (bellProjector : Matrix (α × α) (α × α) ℂ) := by
  simp only [isotropicState, Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul,
    Matrix.one_mul, bellProjector_idempotent hα, sub_self, smul_zero, add_zero]

theorem trace_isotropicState_mul_bellProjector
    (F : ℝ) (hα : 0 < Fintype.card α) :
    Matrix.trace (isotropicState α F * bellProjector) = (F : ℂ) := by
  rw [isotropicState_mul_bellProjector F hα, Matrix.trace_smul, bellProjector_trace hα]
  simp

theorem isotropicState_trace (F : ℝ) (hα : 2 ≤ Fintype.card α) :
    Matrix.trace (isotropicState α F) = 1 := by
  have hpos : 0 < Fintype.card α := lt_of_lt_of_le (by norm_num) hα
  have hd : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hα
  have hden : 0 < (Fintype.card α : ℝ) ^ 2 - 1 := by nlinarith
  have hr : F + ((1 - F) / ((Fintype.card α : ℝ) ^ 2 - 1)) *
      ((Fintype.card α : ℝ) * Fintype.card α - 1) = 1 := by
    rw [← pow_two, div_mul_cancel₀ _ hden.ne']
    ring
  simp only [isotropicState, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_sub, Matrix.trace_one, bellProjector_trace hpos, Fintype.card_prod,
    smul_eq_mul, mul_one]
  exact_mod_cast hr

theorem physicalFidelityLeft_tensor_isotropic
    (F1 F2 : ℝ) (hα : 2 ≤ Fintype.card α) (hβ : 2 ≤ Fintype.card β) :
    physicalFidelityLeft (tensorState (isotropicState α F1) (isotropicState β F2)) =
      F1 := by
  have hpos : 0 < Fintype.card α := lt_of_lt_of_le (by norm_num) hα
  rw [physicalFidelityLeft, trace_tensorState_pairBellLeft,
    trace_isotropicState_mul_bellProjector F1 hpos, isotropicState_trace F2 hβ, mul_one]
  rfl

theorem physicalFidelityRight_tensor_isotropic
    (F1 F2 : ℝ) (hα : 2 ≤ Fintype.card α) (hβ : 2 ≤ Fintype.card β) :
    physicalFidelityRight (tensorState (isotropicState α F1) (isotropicState β F2)) =
      F2 := by
  have hpos : 0 < Fintype.card β := lt_of_lt_of_le (by norm_num) hβ
  rw [physicalFidelityRight, trace_tensorState_pairBellRight,
    trace_isotropicState_mul_bellProjector F2 hpos, isotropicState_trace F1 hα, one_mul]
  rfl

end MatrixIsotropicFidelities

section MatrixFiniteTwirlUnits

def normalizedFourierCoeff (N : ℕ) [NeZero N] : Matrix (ZMod N) (ZMod N) ℂ :=
  fun i j => ((Real.sqrt (N : ℝ) : ℂ)⁻¹) * ZMod.stdAddChar (i * j)

private theorem stdAddChar_normSq (N : ℕ) [NeZero N] (z : ZMod N) :
    Complex.normSq (ZMod.stdAddChar z) = 1 := by
  rw [Complex.normSq_eq_norm_sq, AddChar.norm_apply]
  norm_num

theorem normalizedFourierCoeff_normSq (N : ℕ) [NeZero N] (i j : ZMod N) :
    Complex.normSq (normalizedFourierCoeff N i j) = (N : ℝ)⁻¹ := by
  simp only [normalizedFourierCoeff, Complex.normSq_mul, Complex.normSq_inv,
    Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg N),
    stdAddChar_normSq, mul_one]

private theorem normalizedFourierCoeff_cross (N : ℕ) [NeZero N]
    (i j k : ZMod N) :
    star (normalizedFourierCoeff N k i) * normalizedFourierCoeff N k j =
      (((N : ℝ)⁻¹ : ℝ) : ℂ) * ZMod.stdAddChar (k * (j - i)) := by
  let c : ℂ := (Real.sqrt (N : ℝ) : ℂ)⁻¹
  have hc : star c * c = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj]
    simp only [c, Complex.normSq_inv, Complex.normSq_ofReal,
      Real.mul_self_sqrt (Nat.cast_nonneg N)]
  have hchar : star (ZMod.stdAddChar (k * i)) * ZMod.stdAddChar (k * j) =
      ZMod.stdAddChar (k * (j - i)) := by
    have hneg : star (ZMod.stdAddChar (k * i)) = ZMod.stdAddChar (-(k * i)) := by
      simpa only [Complex.star_def] using
        (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) (k * i)).symm
    rw [hneg, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  change star (c * ZMod.stdAddChar (k * i)) * (c * ZMod.stdAddChar (k * j)) = _
  rw [star_mul]
  calc
    _ = (star c * c) * (star (ZMod.stdAddChar (k * i)) * ZMod.stdAddChar (k * j)) := by ring
    _ = _ := by rw [hc, hchar]

theorem normalizedFourierCoeff_unitary_col (N : ℕ) [NeZero N] :
    (normalizedFourierCoeff N)ᴴ * normalizedFourierCoeff N = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [normalizedFourierCoeff_cross]
  rw [← Finset.mul_sum, AddChar.sum_mulShift (j - i) (ZMod.isPrimitive_stdAddChar N)]
  by_cases hij : i = j
  · subst j
    simp [Matrix.one_apply, ZMod.card, Complex.ofReal_inv, NeZero.ne N]
  · simp [Matrix.one_apply, hij, sub_ne_zero.mpr (Ne.symm hij)]

theorem normalizedFourierCoeff_unitary_row (N : ℕ) [NeZero N] :
    normalizedFourierCoeff N * (normalizedFourierCoeff N)ᴴ = 1 :=
  mul_eq_one_comm.mp (normalizedFourierCoeff_unitary_col N)

def normalizedFourierUnitary (N : ℕ) [NeZero N] :
    unitary (Matrix (ZMod N) (ZMod N) ℂ) :=
  ⟨normalizedFourierCoeff N, Unitary.mem_iff.mpr ⟨
    by simpa only [Matrix.star_eq_conjTranspose] using normalizedFourierCoeff_unitary_col N,
    by simpa only [Matrix.star_eq_conjTranspose] using normalizedFourierCoeff_unitary_row N⟩⟩

variable [DecidableEq α]

def normalizedFourierOn {N : ℕ} [NeZero N] (e : α ≃ ZMod N) : Matrix α α ℂ :=
  (normalizedFourierCoeff N).submatrix e e

theorem normalizedFourierOn_unitary_col {N : ℕ} [NeZero N] (e : α ≃ ZMod N) :
    (normalizedFourierOn e)ᴴ * normalizedFourierOn e = 1 := by
  rw [normalizedFourierOn, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    normalizedFourierCoeff_unitary_col, Matrix.submatrix_one_equiv]

theorem normalizedFourierOn_unitary_row {N : ℕ} [NeZero N] (e : α ≃ ZMod N) :
    normalizedFourierOn e * (normalizedFourierOn e)ᴴ = 1 :=
  mul_eq_one_comm.mp (normalizedFourierOn_unitary_col e)

theorem normalizedFourierOn_normSq {N : ℕ} [NeZero N] (e : α ≃ ZMod N) (i j : α) :
    Complex.normSq (normalizedFourierOn e i j) = (N : ℝ)⁻¹ :=
  normalizedFourierCoeff_normSq N (e i) (e j)

def fourthPhaseCoeff (phase : α → ZMod 4) : Matrix α α ℂ :=
  Matrix.diagonal (fun i => ZMod.stdAddChar (phase i))

theorem fourthPhaseCoeff_unitary_col (phase : α → ZMod 4) :
    (fourthPhaseCoeff phase)ᴴ * fourthPhaseCoeff phase = 1 := by
  have hentry (i : α) : star (ZMod.stdAddChar (phase i)) * ZMod.stdAddChar (phase i) = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, stdAddChar_normSq]
    rfl
  rw [fourthPhaseCoeff, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs
  · exact hentry i
  · rfl

theorem fourthPhaseCoeff_unitary_row (phase : α → ZMod 4) :
    fourthPhaseCoeff phase * (fourthPhaseCoeff phase)ᴴ = 1 :=
  mul_eq_one_comm.mp (fourthPhaseCoeff_unitary_col phase)

end MatrixFiniteTwirlUnits

section MatrixLocalPairMatrix

variable [DecidableEq α]

def localPairCoeff (U : Matrix α α ℂ) : Matrix (α × α) (α × α) ℂ :=
  U ⊗ₖ U.map star

theorem localPairCoeff_unitary_col (U : Matrix α α ℂ) (hU : Uᴴ * U = 1) :
    (localPairCoeff U)ᴴ * localPairCoeff U = 1 := by
  have hbar : (U.map star)ᴴ * U.map star = 1 := by
    have hstar : (U.map star)ᴴ = Uᵀ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    rw [hstar]
    change Uᵀ * (Uᴴ)ᵀ = 1
    rw [← Matrix.transpose_mul, hU, Matrix.transpose_one]
  rw [localPairCoeff, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, hU, hbar, Matrix.one_kronecker_one]

theorem localPairCoeff_unitary_row (U : Matrix α α ℂ) (hU : Uᴴ * U = 1) :
    localPairCoeff U * (localPairCoeff U)ᴴ = 1 :=
  mul_eq_one_comm.mp (localPairCoeff_unitary_col U hU)

theorem localPairCoeff_mulVec (U M : Matrix α α ℂ) :
    localPairCoeff U *ᵥ (fun x : α × α => M x.1 x.2) =
      fun x : α × α => (U * M * Uᴴ) x.1 x.2 := by
  change localPairCoeff U *ᵥ Matrix.vec Mᵀ = Matrix.vec (U * M * Uᴴ)ᵀ
  rw [localPairCoeff, Matrix.kronecker_mulVec_vec]
  congr 1
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rfl

theorem pureDensity_localPairCoeff (U M : Matrix α α ℂ) :
    localPairCoeff U * pureDensity M * (localPairCoeff U)ᴴ =
      pureDensity (U * M * Uᴴ) := by
  let v : α × α → ℂ := fun x => M x.1 x.2
  change localPairCoeff U * Matrix.vecMulVec v (star v) * (localPairCoeff U)ᴴ = _
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
  rw [show localPairCoeff U *ᵥ v = (fun x : α × α => (U * M * Uᴴ) x.1 x.2) from
    localPairCoeff_mulVec U M]
  rfl

def bellCoeff : Matrix α α ℂ :=
  ((Real.sqrt (Fintype.card α : ℝ) : ℂ)⁻¹) • (1 : Matrix α α ℂ)

theorem pureDensity_bellCoeff :
    pureDensity (bellCoeff : Matrix α α ℂ) =
      (bellProjector : Matrix (α × α) (α × α) ℂ) := by
  have hv (x : α × α) : bellCoeff x.1 x.2 = bellVector x := by
    simp [bellCoeff, bellVector, Matrix.one_apply, smul_eq_mul]
  ext x y
  simp only [pureDensity, bellProjector, hv]

theorem bellCoeff_unitary_conjugation (U : Matrix α α ℂ) (hU : U * Uᴴ = 1) :
    U * (bellCoeff : Matrix α α ℂ) * Uᴴ = bellCoeff := by
  simp only [bellCoeff, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]

theorem bellProjector_localPairCoeff (U : Matrix α α ℂ) (hU : U * Uᴴ = 1) :
    localPairCoeff U * (bellProjector : Matrix (α × α) (α × α) ℂ) *
        (localPairCoeff U)ᴴ = bellProjector := by
  simpa only [pureDensity_bellCoeff, bellCoeff_unitary_conjugation U hU] using
    pureDensity_localPairCoeff U (bellCoeff : Matrix α α ℂ)

end MatrixLocalPairMatrix

section MatrixFourthPhaseTwirl

variable [DecidableEq α]

def phaseSignedChar (x y : α × α) : AddChar (α → ZMod 4) ℂ where
  toFun phase := ZMod.stdAddChar (phase x.1 - phase x.2 - phase y.1 + phase y.2)
  map_zero_eq_one' := by simp
  map_add_eq_mul' phase1 phase2 := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [Pi.add_apply]
    ring

theorem phaseSignedChar_eq_one_iff (x y : α × α) :
    phaseSignedChar x y = 1 ↔ ((x.1 = x.2 ∧ y.1 = y.2) ∨ x = y) := by
  constructor
  · intro hchar
    have hzero (phase : α → ZMod 4) :
        phase x.1 - phase x.2 - phase y.1 + phase y.2 = 0 := by
      have hvalue := congrArg (fun χ : AddChar (α → ZMod 4) ℂ => χ phase) hchar
      change ZMod.stdAddChar (phase x.1 - phase x.2 - phase y.1 + phase y.2) = 1 at hvalue
      apply ZMod.injective_stdAddChar
      simpa only [AddChar.map_zero_eq_one] using hvalue
    by_cases hx : x.1 = x.2
    · left
      refine ⟨hx, ?_⟩
      by_contra hy
      have ht := hzero (fun z => if z = y.1 then 1 else 0)
      norm_num [hx, hy, Ne.symm hy] at ht
      exact (by decide : (1 : ZMod 4) ≠ 0) ht
    · right
      have hy1 : y.1 = x.1 := by
        by_contra hy1
        have ht := hzero (fun z => if z = x.1 then 1 else 0)
        by_cases hy2 : y.2 = x.1
        · norm_num [hx, Ne.symm hx, hy1, hy2] at ht
          exact (by decide : (2 : ZMod 4) ≠ 0) ht
        · norm_num [hx, Ne.symm hx, hy1, hy2] at ht
          exact (by decide : (1 : ZMod 4) ≠ 0) ht
      have hy2 : y.2 = x.2 := by
        by_contra hy2
        have ht := hzero (fun z => if z = x.2 then 1 else 0)
        norm_num [hx, Ne.symm hx, hy1, hy2] at ht
        exact (by decide : (1 : ZMod 4) ≠ 0) ht
      exact Prod.ext hy1.symm hy2.symm
  · rintro (⟨hx, hy⟩ | hxy)
    · ext phase
      simp [phaseSignedChar, hx, hy]
    · subst y
      ext phase
      change ZMod.stdAddChar (phase x.1 - phase x.2 - phase x.1 + phase x.2) = 1
      have hzero : phase x.1 - phase x.2 - phase x.1 + phase x.2 = 0 := by ring
      rw [hzero, AddChar.map_zero_eq_one]

theorem phaseSignedChar_mean (x y : α × α) :
    (Fintype.card (α → ZMod 4) : ℂ)⁻¹ * ∑ phase, phaseSignedChar x y phase =
      if ((x.1 = x.2 ∧ y.1 = y.2) ∨ x = y) then 1 else 0 := by
  have hcard : (Fintype.card (α → ZMod 4) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  by_cases hmask : ((x.1 = x.2 ∧ y.1 = y.2) ∨ x = y)
  · have hchar := (phaseSignedChar_eq_one_iff x y).mpr hmask
    rw [hchar]
    simp [hmask, hcard]
  · have hchar : phaseSignedChar x y ≠ 1 := fun h =>
      hmask ((phaseSignedChar_eq_one_iff x y).mp h)
    rw [AddChar.sum_eq_zero_of_ne_one hchar]
    simp [hmask]

def fourthPhasePairCoeff (phase : α → ZMod 4) : Matrix (α × α) (α × α) ℂ :=
  fourthPhaseCoeff (fun x : α × α => phase x.1 - phase x.2)

theorem fourthPhasePairCoeff_eq_localPairCoeff (phase : α → ZMod 4) :
    fourthPhasePairCoeff phase = localPairCoeff (fourthPhaseCoeff phase) := by
  have hdiff (a b : ZMod 4) : ZMod.stdAddChar (a - b) =
      ZMod.stdAddChar a * star (ZMod.stdAddChar b) := by
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
    rfl
  ext x y
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2
  · have hxy : x = y := Prod.ext h1 h2
    subst y
    simpa [fourthPhasePairCoeff, fourthPhaseCoeff, localPairCoeff,
      Matrix.diagonal_apply] using hdiff (phase x.1) (phase x.2)
  · have hxy : x ≠ y := fun h => h2 (congrArg Prod.snd h)
    simp [fourthPhasePairCoeff, fourthPhaseCoeff, localPairCoeff,
      Matrix.diagonal_apply, hxy, h1, h2]
  · have hxy : x ≠ y := fun h => h1 (congrArg Prod.fst h)
    simp [fourthPhasePairCoeff, fourthPhaseCoeff, localPairCoeff,
      Matrix.diagonal_apply, hxy, h1, h2]
  · have hxy : x ≠ y := fun h => h1 (congrArg Prod.fst h)
    simp [fourthPhasePairCoeff, fourthPhaseCoeff, localPairCoeff,
      Matrix.diagonal_apply, hxy, h1, h2]

theorem fourthPhasePairCoeff_unitary_col (phase : α → ZMod 4) :
    (fourthPhasePairCoeff phase)ᴴ * fourthPhasePairCoeff phase = 1 :=
  fourthPhaseCoeff_unitary_col _

theorem fourthPhasePairCoeff_unitary_row (phase : α → ZMod 4) :
    fourthPhasePairCoeff phase * (fourthPhasePairCoeff phase)ᴴ = 1 :=
  fourthPhaseCoeff_unitary_row _

private theorem fourthPhasePairCoeff_entry_product
    (phase : α → ZMod 4) (x y : α × α) :
    ZMod.stdAddChar (phase x.1 - phase x.2) *
        star (ZMod.stdAddChar (phase y.1 - phase y.2)) = phaseSignedChar x y phase := by
  have hneg : star (ZMod.stdAddChar (phase y.1 - phase y.2)) =
      ZMod.stdAddChar (-(phase y.1 - phase y.2)) := by
    simpa only [Complex.star_def] using
      (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := 4)) (phase y.1 - phase y.2)).symm
  rw [hneg, ← AddChar.map_add_eq_mul]
  change ZMod.stdAddChar _ = ZMod.stdAddChar _
  congr 1
  ring

theorem fourthPhasePairCoeff_conjugation_entry
    (phase : α → ZMod 4) (ρ : Matrix (α × α) (α × α) ℂ) (x y : α × α) :
    (fourthPhasePairCoeff phase * ρ * (fourthPhasePairCoeff phase)ᴴ) x y =
      phaseSignedChar x y phase * ρ x y := by
  simp only [fourthPhasePairCoeff, fourthPhaseCoeff, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  calc
    _ = (ZMod.stdAddChar (phase x.1 - phase x.2) *
        star (ZMod.stdAddChar (phase y.1 - phase y.2))) * ρ x y := by ring
    _ = _ := by rw [fourthPhasePairCoeff_entry_product]

def fourthPhaseTwirl (ρ : Matrix (α × α) (α × α) ℂ) :
    Matrix (α × α) (α × α) ℂ :=
  (Fintype.card (α → ZMod 4) : ℂ)⁻¹ •
    ∑ phase : α → ZMod 4, fourthPhasePairCoeff phase * ρ * (fourthPhasePairCoeff phase)ᴴ

theorem fourthPhaseTwirl_apply
    (ρ : Matrix (α × α) (α × α) ℂ) (x y : α × α) :
    fourthPhaseTwirl ρ x y =
      if ((x.1 = x.2 ∧ y.1 = y.2) ∨ x = y) then ρ x y else 0 := by
  simp only [fourthPhaseTwirl, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, fourthPhasePairCoeff_conjugation_entry]
  rw [← Finset.sum_mul, ← mul_assoc, phaseSignedChar_mean]
  split_ifs <;> simp

end MatrixFourthPhaseTwirl

section MatrixFourierProjector

variable [DecidableEq α]

theorem localPairCoeff_mul (U V : Matrix α α ℂ) :
    localPairCoeff (U * V) = localPairCoeff U * localPairCoeff V := by
  change (U * V) ⊗ₖ ((U * V).map (starRingEnd ℂ)) =
    (U ⊗ₖ U.map (starRingEnd ℂ)) * (V ⊗ₖ V.map (starRingEnd ℂ))
  rw [Matrix.map_mul, Matrix.mul_kronecker_mul]

theorem localPairCoeff_conjugation_one (U : Matrix α α ℂ) (hU : Uᴴ * U = 1) :
    localPairCoeff U * (1 : Matrix (α × α) (α × α) ℂ) * (localPairCoeff U)ᴴ = 1 := by
  rw [Matrix.mul_one, localPairCoeff_unitary_row U hU]

def matrixDiagonalPairProjector : Matrix (α × α) (α × α) ℂ :=
  Matrix.diagonal (fun x => if x.1 = x.2 then 1 else 0)

theorem matrixDiagonalPairProjector_idempotent :
    (matrixDiagonalPairProjector : Matrix (α × α) (α × α) ℂ) *
      matrixDiagonalPairProjector = matrixDiagonalPairProjector := by
  simp only [matrixDiagonalPairProjector, Matrix.diagonal_mul_diagonal]
  congr 1
  ext x
  split_ifs <;> simp

theorem matrixDiagonalPairProjector_hermitian :
    (matrixDiagonalPairProjector : Matrix (α × α) (α × α) ℂ).IsHermitian := by
  change (matrixDiagonalPairProjector : Matrix (α × α) (α × α) ℂ)ᴴ =
    matrixDiagonalPairProjector
  simp only [matrixDiagonalPairProjector, Matrix.diagonal_conjTranspose]
  congr 1
  ext x
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem matrixDiagonalPairProjector_trace :
    Matrix.trace (matrixDiagonalPairProjector : Matrix (α × α) (α × α) ℂ) =
      (Fintype.card α : ℂ) := by
  rw [matrixDiagonalPairProjector, Matrix.trace_diagonal, Fintype.sum_prod_type]
  simp

theorem matrixDiagonalPairProjector_mul_bellProjector :
    (matrixDiagonalPairProjector : Matrix (α × α) (α × α) ℂ) * bellProjector =
      bellProjector := by
  ext x y
  rw [matrixDiagonalPairProjector, Matrix.diagonal_mul]
  by_cases hx : x.1 = x.2 <;> simp [bellProjector_apply, hx]

theorem bellProjector_mul_matrixDiagonalPairProjector :
    (bellProjector : Matrix (α × α) (α × α) ℂ) * matrixDiagonalPairProjector =
      bellProjector := by
  ext x y
  rw [matrixDiagonalPairProjector, Matrix.mul_diagonal]
  by_cases hy : y.1 = y.2 <;> simp [bellProjector_apply, hy]

theorem trace_mul_matrixDiagonalPairProjector (ρ : Matrix (α × α) (α × α) ℂ) :
    Matrix.trace (ρ * matrixDiagonalPairProjector) = ∑ i, ρ (i, i) (i, i) := by
  simp [matrixDiagonalPairProjector, Matrix.mul_diagonal, Matrix.trace,
    Matrix.diag, Fintype.sum_prod_type, mul_ite]

private theorem mul_bellProjector_diagonal_entry
    (ρ : Matrix (α × α) (α × α) ℂ) (x : α × α) :
    (ρ * bellProjector : Matrix (α × α) (α × α) ℂ) x x =
      if x.1 = x.2 then (∑ i, ρ x (i, i)) / (Fintype.card α : ℂ) else 0 := by
  by_cases hx : x.1 = x.2
  · simp only [Matrix.mul_apply, Fintype.sum_prod_type, bellProjector_apply,
      hx, and_true, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [← Finset.sum_mul]
    rw [div_eq_mul_inv]
  · simp [Matrix.mul_apply, bellProjector_apply, hx]

theorem trace_mul_bellProjector_exact
    (ρ : Matrix (α × α) (α × α) ℂ) :
    Matrix.trace (ρ * bellProjector) =
      (∑ z : α × α, ρ (z.1, z.1) (z.2, z.2)) / (Fintype.card α : ℂ) := by
  change (∑ x : α × α, (ρ * bellProjector : Matrix (α × α) (α × α) ℂ) x x) = _
  simp only [mul_bellProjector_diagonal_entry, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_div]

theorem matrixHermitianTrace_eq_ofReal {η : Type*} [Fintype η]
    (ρ : Matrix η η ℂ) (hρ : ρ.IsHermitian) :
    Matrix.trace ρ = ((Matrix.trace ρ).re : ℂ) := by
  have hstar : star (Matrix.trace ρ) = Matrix.trace ρ := by
    rw [← Matrix.trace_conjTranspose, hρ.eq]
  exact (Complex.conj_eq_iff_re.mp (by simpa only [Complex.star_def] using hstar)).symm

theorem matrixHermitianTrace_mul_eq_ofReal {η : Type*} [Fintype η]
    (ρ A : Matrix η η ℂ) (hρ : ρ.IsHermitian) (hA : A.IsHermitian) :
    Matrix.trace (ρ * A) = ((Matrix.trace (ρ * A)).re : ℂ) := by
  have hstar : star (Matrix.trace (ρ * A)) = Matrix.trace (ρ * A) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hρ.eq,
      Matrix.trace_mul_comm]
  exact (Complex.conj_eq_iff_re.mp (by simpa only [Complex.star_def] using hstar)).symm

private theorem localPair_diagonalProjector_entry (U : Matrix α α ℂ) (x y : α × α) :
    (localPairCoeff U * matrixDiagonalPairProjector * (localPairCoeff U)ᴴ :
      Matrix (α × α) (α × α) ℂ) x y =
      ∑ a, U x.1 a * star (U x.2 a) * star (U y.1 a) * U y.2 a := by
  rw [Matrix.mul_apply]
  simp only [matrixDiagonalPairProjector, Matrix.mul_diagonal]
  simp only [Matrix.conjTranspose_apply, localPairCoeff, Matrix.kroneckerMap_apply,
    Matrix.map_apply, Fintype.sum_prod_type, star_mul, star_star, mul_ite, ite_mul,
    mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_assoc]
    <;> simp only [mul_comm, mul_left_comm, mul_assoc]

private theorem localPair_diagonalProjector_diagonal_pair_entry
    (U : Matrix α α ℂ) (i k : α) :
    (localPairCoeff U * matrixDiagonalPairProjector * (localPairCoeff U)ᴴ :
      Matrix (α × α) (α × α) ℂ)
        (i, i) (k, k) =
      ∑ a, (Complex.normSq (U i a) : ℂ) * (Complex.normSq (U k a) : ℂ) := by
  rw [localPair_diagonalProjector_entry]
  apply Finset.sum_congr rfl
  intro a _
  have hi : U i a * star (U i a) = (Complex.normSq (U i a) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  have hk : U k a * star (U k a) = (Complex.normSq (U k a) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  calc
    _ = (U i a * star (U i a)) * (U k a * star (U k a)) := by ring
    _ = _ := by rw [hi, hk]

private theorem localPair_diagonalProjector_density_diagonal_entry
    (U : Matrix α α ℂ) (x : α × α) :
    (localPairCoeff U * matrixDiagonalPairProjector * (localPairCoeff U)ᴴ :
      Matrix (α × α) (α × α) ℂ) x x =
      ∑ a, (Complex.normSq (U x.1 a) : ℂ) * (Complex.normSq (U x.2 a) : ℂ) := by
  rw [localPair_diagonalProjector_entry]
  apply Finset.sum_congr rfl
  intro a _
  have hi : U x.1 a * star (U x.1 a) = (Complex.normSq (U x.1 a) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  have hj : U x.2 a * star (U x.2 a) = (Complex.normSq (U x.2 a) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  calc
    _ = (U x.1 a * star (U x.1 a)) * (U x.2 a * star (U x.2 a)) := by ring
    _ = _ := by rw [hi, hj]

private theorem flat_normSq_product_sum (U : Matrix α α ℂ)
    (hflat : ∀ i j, Complex.normSq (U i j) = (Fintype.card α : ℝ)⁻¹)
    (hα : 0 < Fintype.card α) (i k : α) :
    (∑ a, (Complex.normSq (U i a) : ℂ) * (Complex.normSq (U k a) : ℂ)) =
      (Fintype.card α : ℂ)⁻¹ := by
  have hd : (Fintype.card α : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hα)
  simp_rw [hflat]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast]
  rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]

theorem fourthPhaseTwirl_localPairDiagonal_flat (U : Matrix α α ℂ)
    (hflat : ∀ i j, Complex.normSq (U i j) = (Fintype.card α : ℝ)⁻¹)
    (hα : 0 < Fintype.card α) :
    fourthPhaseTwirl
      (localPairCoeff U * matrixDiagonalPairProjector * (localPairCoeff U)ᴴ) =
      bellProjector + (Fintype.card α : ℂ)⁻¹ • (1 - matrixDiagonalPairProjector) := by
  ext x y
  rw [fourthPhaseTwirl_apply]
  by_cases hdiag : x.1 = x.2 ∧ y.1 = y.2
  · have he :
        (localPairCoeff U * matrixDiagonalPairProjector * (localPairCoeff U)ᴴ :
          Matrix (α × α) (α × α) ℂ) x y =
          (Fintype.card α : ℂ)⁻¹ := by
      rcases x with ⟨i, j⟩
      rcases y with ⟨k, l⟩
      rcases hdiag with ⟨hx, hy⟩
      simp only at hx hy
      subst j
      subst l
      rw [localPair_diagonalProjector_diagonal_pair_entry]
      exact flat_normSq_product_sum U hflat hα i k
    rw [if_pos (Or.inl hdiag), he]
    simp [hdiag.1, hdiag.2, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, matrixDiagonalPairProjector, Matrix.diagonal_apply,
      Matrix.one_apply, bellProjector_apply, Complex.ofReal_inv]
  · by_cases hxy : x = y
    · subst y
      have hx : x.1 ≠ x.2 := fun h => hdiag ⟨h, h⟩
      have he :
          (localPairCoeff U * matrixDiagonalPairProjector * (localPairCoeff U)ᴴ :
            Matrix (α × α) (α × α) ℂ) x x =
            (Fintype.card α : ℂ)⁻¹ := by
        rw [localPair_diagonalProjector_density_diagonal_entry]
        exact flat_normSq_product_sum U hflat hα x.1 x.2
      rw [if_pos (Or.inr rfl), he]
      simp [hx, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
        matrixDiagonalPairProjector, Matrix.diagonal_apply, Matrix.one_apply,
        bellProjector_apply]
    · simp [hdiag, hxy, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
        matrixDiagonalPairProjector, Matrix.diagonal_apply, Matrix.one_apply,
        bellProjector_apply]

theorem fourthPhaseTwirl_normalizedFourierDiagonal {N : ℕ} [NeZero N]
    (e : α ≃ ZMod N) :
    fourthPhaseTwirl
      (localPairCoeff (normalizedFourierOn e) * matrixDiagonalPairProjector *
        (localPairCoeff (normalizedFourierOn e))ᴴ) =
      bellProjector + (Fintype.card α : ℂ)⁻¹ • (1 - matrixDiagonalPairProjector) := by
  have hcard : Fintype.card α = N := by
    rw [Fintype.card_congr e, ZMod.card]
  apply fourthPhaseTwirl_localPairDiagonal_flat
  · intro i j
    simpa only [hcard] using normalizedFourierOn_normSq e i j
  · rw [hcard]
    exact Nat.pos_of_ne_zero (NeZero.ne N)

theorem fourthPhaseTwirl_add (ρ σ : Matrix (α × α) (α × α) ℂ) :
    fourthPhaseTwirl (ρ + σ) = fourthPhaseTwirl ρ + fourthPhaseTwirl σ := by
  ext x y
  simp only [fourthPhaseTwirl_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem fourthPhaseTwirl_smul (c : ℂ) (ρ : Matrix (α × α) (α × α) ℂ) :
    fourthPhaseTwirl (c • ρ) = c • fourthPhaseTwirl ρ := by
  ext x y
  simp only [fourthPhaseTwirl_apply, Matrix.smul_apply]
  split_ifs <;> simp

theorem fourthPhaseTwirl_sub (ρ σ : Matrix (α × α) (α × α) ℂ) :
    fourthPhaseTwirl (ρ - σ) = fourthPhaseTwirl ρ - fourthPhaseTwirl σ := by
  ext x y
  simp only [fourthPhaseTwirl_apply, Matrix.sub_apply]
  split_ifs <;> simp

theorem fourthPhaseTwirl_sum {ι : Type*} (s : Finset ι)
    (ρ : ι → Matrix (α × α) (α × α) ℂ) :
    fourthPhaseTwirl (∑ i ∈ s, ρ i) = ∑ i ∈ s, fourthPhaseTwirl (ρ i) := by
  ext x y
  simp only [fourthPhaseTwirl_apply, Matrix.sum_apply]
  split_ifs <;> simp

theorem fourthPhaseTwirl_one :
    fourthPhaseTwirl (1 : Matrix (α × α) (α × α) ℂ) = 1 := by
  ext x y
  rw [fourthPhaseTwirl_apply]
  by_cases hxy : x = y
  · simp [hxy, Matrix.one_apply]
  · simp [hxy, Matrix.one_apply]

theorem fourthPhaseTwirl_bellProjector :
    fourthPhaseTwirl (bellProjector : Matrix (α × α) (α × α) ℂ) = bellProjector := by
  ext x y
  rw [fourthPhaseTwirl_apply, bellProjector_apply]
  by_cases hdiag : x.1 = x.2 ∧ y.1 = y.2
  · simp [hdiag]
  · simp [hdiag]

theorem fourthPhaseTwirl_matrixDiagonalPairProjector :
    fourthPhaseTwirl (matrixDiagonalPairProjector : Matrix (α × α) (α × α) ℂ) =
      matrixDiagonalPairProjector := by
  ext x y
  rw [fourthPhaseTwirl_apply]
  by_cases hxy : x = y
  · simp [hxy, matrixDiagonalPairProjector, Matrix.diagonal_apply]
  · simp [hxy, matrixDiagonalPairProjector, Matrix.diagonal_apply]

def matrixFourthPhaseUnitary (phase : α → ZMod 4) : unitary (Matrix α α ℂ) :=
  ⟨fourthPhaseCoeff phase, Unitary.mem_iff.mpr ⟨
    by simpa only [Matrix.star_eq_conjTranspose] using fourthPhaseCoeff_unitary_col phase,
    by simpa only [Matrix.star_eq_conjTranspose] using fourthPhaseCoeff_unitary_row phase⟩⟩

def matrixFourierOnUnitary {N : ℕ} [NeZero N] (e : α ≃ ZMod N) :
    unitary (Matrix α α ℂ) :=
  ⟨normalizedFourierOn e, Unitary.mem_iff.mpr ⟨
    by simpa only [Matrix.star_eq_conjTranspose] using normalizedFourierOn_unitary_col e,
    by simpa only [Matrix.star_eq_conjTranspose] using normalizedFourierOn_unitary_row e⟩⟩

theorem fourthPhaseTwirl_pureDensity (M : Matrix α α ℂ) :
    fourthPhaseTwirl (pureDensity M) =
      (Fintype.card (α → ZMod 4) : ℂ)⁻¹ • ∑ phase : α → ZMod 4,
        pureDensity (fourthPhaseCoeff phase * M * (fourthPhaseCoeff phase)ᴴ) := by
  simp only [fourthPhaseTwirl, fourthPhasePairCoeff_eq_localPairCoeff,
    pureDensity_localPairCoeff]

end MatrixFourierProjector

section MatrixPermutationMean

variable [DecidableEq α]

def matrixPermutationMean (f : α × α → ℂ) (x : α × α) : ℂ :=
  (Fintype.card (Equiv.Perm α) : ℂ)⁻¹ *
    ∑ σ : Equiv.Perm α, f (σ x.1, σ x.2)

theorem matrixPermutationMean_invariant (f : α × α → ℂ)
    (τ : Equiv.Perm α) (x : α × α) :
    matrixPermutationMean f (τ x.1, τ x.2) = matrixPermutationMean f x := by
  unfold matrixPermutationMean
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ : Equiv.Perm α => f (σ x.1, σ x.2))

theorem matrixPermutationMean_diag_sum (f : α × α → ℂ) :
    (∑ i, matrixPermutationMean f (i, i)) = ∑ i, f (i, i) := by
  have hcard : (Fintype.card (Equiv.Perm α) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum (σ : Equiv.Perm α) : (∑ i, f (σ i, σ i)) = ∑ i, f (i, i) :=
    Equiv.sum_comp σ (fun i => f (i, i))
  simp only [matrixPermutationMean]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem matrixPermutationMean_sum (f : α × α → ℂ) :
    (∑ x, matrixPermutationMean f x) = ∑ x, f x := by
  have hcard : (Fintype.card (Equiv.Perm α) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum (σ : Equiv.Perm α) :
      (∑ x : α × α, f (σ x.1, σ x.2)) = ∑ x, f x :=
    Equiv.sum_comp (Equiv.prodCongr σ σ) f
  simp only [matrixPermutationMean]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem matrixPermutationMean_diag (f : α × α → ℂ) (i : α) :
    matrixPermutationMean f (i, i) = (∑ a, f (a, a)) / (Fintype.card α : ℂ) := by
  have hd : (Fintype.card α : ℂ) ≠ 0 := by
    haveI : Nonempty α := ⟨i⟩
    exact_mod_cast Fintype.card_ne_zero
  have hconst (a : α) :
      matrixPermutationMean f (a, a) = matrixPermutationMean f (i, i) := by
    simpa only [Equiv.swap_apply_left] using
      matrixPermutationMean_invariant f (Equiv.swap i a) (i, i)
  have hsum := matrixPermutationMean_diag_sum f
  simp only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  apply (eq_div_iff hd).mpr
  simpa only [mul_comm] using hsum

private theorem exists_perm_ordered_pair {i j a b : α} (hij : i ≠ j) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm α, σ i = a ∧ σ j = b := by
  have hmove : ∀ {a b c d : α}, a ≠ b → c ≠ d →
      ∃ σ : Equiv.Perm α, σ • a = c ∧ σ • b = d :=
    MulAction.is_two_pretransitive_iff.mp (Equiv.Perm.isMultiplyPretransitive α 2)
  obtain ⟨σ, hσi, hσj⟩ := hmove (a := i) (b := j) (c := a) (d := b) hij hab
  exact ⟨σ, hσi, hσj⟩

theorem matrixPermutationMean_offdiag (f : α × α → ℂ) (i j : α) (hij : i ≠ j) :
    matrixPermutationMean f (i, j) =
      ((∑ x, f x) - ∑ a, f (a, a)) /
        ((Fintype.card α : ℂ) * ((Fintype.card α : ℂ) - 1)) := by
  have htwo : 2 ≤ Fintype.card α :=
    Fintype.one_lt_card_iff.mpr ⟨i, j, hij⟩
  have hd : (Fintype.card α : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card α ≠ 0)
  have hd1 : (Fintype.card α : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (by omega : (Fintype.card α : ℤ) - 1 ≠ 0)
  let v := matrixPermutationMean f (i, i)
  let w := matrixPermutationMean f (i, j)
  have hdiag (a : α) : matrixPermutationMean f (a, a) = v := by
    simpa only [Equiv.swap_apply_left] using
      matrixPermutationMean_invariant f (Equiv.swap i a) (i, i)
  have hoff (a b : α) (hab : a ≠ b) : matrixPermutationMean f (a, b) = w := by
    obtain ⟨σ, hσi, hσj⟩ := exists_perm_ordered_pair hij hab
    simpa only [hσi, hσj] using matrixPermutationMean_invariant f σ (i, j)
  have hentry (a b : α) :
      matrixPermutationMean f (a, b) = w + if a = b then v - w else 0 := by
    by_cases hab : a = b
    · subst b
      rw [hdiag]
      simp
    · rw [hoff a b hab]
      simp [hab]
  have htotal := matrixPermutationMean_sum f
  rw [Fintype.sum_prod_type] at htotal
  simp_rw [hentry] at htotal
  have htotal' :
      (Fintype.card α : ℂ) * ((Fintype.card α : ℂ) * w + (v - w)) = ∑ x, f x := by
    simpa only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] using htotal
  have hdiagSum := matrixPermutationMean_diag_sum f
  simp only [hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hdiagSum
  change w = _
  apply (eq_div_iff (mul_ne_zero hd hd1)).mpr
  calc
    w * ((Fintype.card α : ℂ) * ((Fintype.card α : ℂ) - 1)) =
        (Fintype.card α : ℂ) * ((Fintype.card α : ℂ) * w + (v - w)) -
          (Fintype.card α : ℂ) * v := by ring
    _ = _ := by rw [htotal', hdiagSum]

end MatrixPermutationMean

section MatrixPhysicalPermutationTwirl

variable [DecidableEq α]

theorem permutationCoeff_unitary_col (σ : Equiv.Perm α) :
    (σ.permMatrix ℂ)ᴴ * σ.permMatrix ℂ = 1 := by
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
    mul_inv_cancel, Matrix.permMatrix_one]

theorem localPairCoeff_permutation (σ : Equiv.Perm α) :
    localPairCoeff (σ.permMatrix ℂ) =
      Equiv.Perm.permMatrix ℂ (Equiv.prodCongr σ σ) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  by_cases hik : σ i = k <;> by_cases hjl : σ j = l <;>
    simp [localPairCoeff, Matrix.kronecker_apply, Matrix.map_apply,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Equiv.prodCongr_apply, hik, hjl, eq_comm]
  simp [Ne.symm hik, Ne.symm hjl]

theorem localPairCoeff_permutation_conjugation (σ : Equiv.Perm α)
    (ρ : Matrix (α × α) (α × α) ℂ) :
    localPairCoeff (σ.permMatrix ℂ) * ρ * (localPairCoeff (σ.permMatrix ℂ))ᴴ =
      ρ.submatrix (Equiv.prodCongr σ σ) (Equiv.prodCongr σ σ) := by
  rw [localPairCoeff_permutation, Matrix.conjTranspose_permMatrix]
  change (Equiv.prodCongr σ σ).toPEquiv.toMatrix * ρ *
    (Equiv.prodCongr σ σ).symm.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext x y
  rfl

def matrixPermutationTwirl (ρ : Matrix (α × α) (α × α) ℂ) :
    Matrix (α × α) (α × α) ℂ :=
  (Fintype.card (Equiv.Perm α) : ℂ)⁻¹ • ∑ σ : Equiv.Perm α,
    localPairCoeff (σ.permMatrix ℂ) * ρ * (localPairCoeff (σ.permMatrix ℂ))ᴴ

theorem matrixPermutationTwirl_apply (ρ : Matrix (α × α) (α × α) ℂ)
    (x y : α × α) :
    matrixPermutationTwirl ρ x y = (Fintype.card (Equiv.Perm α) : ℂ)⁻¹ *
      ∑ σ : Equiv.Perm α, ρ (σ x.1, σ x.2) (σ y.1, σ y.2) := by
  simp only [matrixPermutationTwirl, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, localPairCoeff_permutation_conjugation, Matrix.submatrix_apply,
    Equiv.prodCongr_apply]
  rfl

theorem matrixPermutationTwirl_add (ρ σ : Matrix (α × α) (α × α) ℂ) :
    matrixPermutationTwirl (ρ + σ) = matrixPermutationTwirl ρ + matrixPermutationTwirl σ := by
  ext x y
  simp only [matrixPermutationTwirl_apply, Matrix.add_apply]
  rw [Finset.sum_add_distrib, mul_add]

theorem matrixPermutationTwirl_smul (c : ℂ) (ρ : Matrix (α × α) (α × α) ℂ) :
    matrixPermutationTwirl (c • ρ) = c • matrixPermutationTwirl ρ := by
  ext x y
  simp only [matrixPermutationTwirl_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

theorem matrixPermutationTwirl_sub (ρ σ : Matrix (α × α) (α × α) ℂ) :
    matrixPermutationTwirl (ρ - σ) = matrixPermutationTwirl ρ - matrixPermutationTwirl σ := by
  ext x y
  simp only [matrixPermutationTwirl_apply, Matrix.sub_apply]
  rw [Finset.sum_sub_distrib, mul_sub]

def matrixDiagonalPairEmbedding (f : α × α → ℂ) :
    Matrix (α × α) (α × α) ℂ :=
  fun x y => if x.1 = x.2 ∧ y.1 = y.2 then f (x.1, y.1) else 0

theorem matrixPermutationTwirl_diagonalPairEmbedding_apply (f : α × α → ℂ)
    (x y : α × α) :
    matrixPermutationTwirl (matrixDiagonalPairEmbedding f) x y =
      if x.1 = x.2 ∧ y.1 = y.2 then matrixPermutationMean f (x.1, y.1) else 0 := by
  rw [matrixPermutationTwirl_apply]
  have hinj (σ : Equiv.Perm α) :
      (σ x.1 = σ x.2 ∧ σ y.1 = σ y.2) ↔ (x.1 = x.2 ∧ y.1 = y.2) := by
    simp only [σ.injective.eq_iff]
  simp only [matrixDiagonalPairEmbedding, hinj]
  split_ifs
  · rfl
  · simp

theorem matrixPermutationTwirl_diagonal_apply (f : α × α → ℂ) (x y : α × α) :
    matrixPermutationTwirl (Matrix.diagonal f) x y =
      if x = y then matrixPermutationMean f x else 0 := by
  rw [matrixPermutationTwirl_apply]
  have hinj (σ : Equiv.Perm α) :
      (σ x.1, σ x.2) = (σ y.1, σ y.2) ↔ x = y :=
    (Equiv.prodCongr σ σ).injective.eq_iff
  simp only [Matrix.diagonal_apply, hinj]
  split_ifs
  · rfl
  · simp

theorem matrixPermutationTwirl_diagonalPairEmbedding_eq
    (f : α × α → ℂ) (hα : 2 ≤ Fintype.card α) :
    matrixPermutationTwirl (matrixDiagonalPairEmbedding f) =
      ((∑ x, f x) / (Fintype.card α : ℂ)) • bellProjector +
      (((∑ a, f (a, a)) - (∑ x, f x) / (Fintype.card α : ℂ)) /
        ((Fintype.card α : ℂ) - 1)) • (matrixDiagonalPairProjector - bellProjector) := by
  have hd : (Fintype.card α : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card α ≠ 0)
  have hd1 : (Fintype.card α : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (by omega : (Fintype.card α : ℤ) - 1 ≠ 0)
  ext x y
  rw [matrixPermutationTwirl_diagonalPairEmbedding_apply]
  by_cases hdiag : x.1 = x.2 ∧ y.1 = y.2
  · rcases x with ⟨i, j⟩
    rcases y with ⟨k, l⟩
    rcases hdiag with ⟨hx, hy⟩
    simp only at hx hy
    subst j
    subst l
    simp only [Prod.fst, Prod.snd, eq_self_iff_true, true_and, if_true]
    by_cases hik : i = k
    · subst k
      rw [matrixPermutationMean_diag]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.sub_apply, matrixDiagonalPairProjector, Matrix.diagonal_apply,
        bellProjector_apply, Prod.fst, Prod.snd, eq_self_iff_true, true_and,
        if_true, Complex.ofReal_inv, Complex.ofReal_natCast]
      field_simp [hd, hd1]
      ring
    · rw [matrixPermutationMean_offdiag f i k hik]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.sub_apply, matrixDiagonalPairProjector, Matrix.diagonal_apply,
        bellProjector_apply, Prod.fst, Prod.snd, eq_self_iff_true, true_and,
        if_true, Prod.mk.injEq, hik, and_false, if_false,
        Complex.ofReal_inv, Complex.ofReal_natCast]
      field_simp [hd, hd1]
      ring
  · by_cases hxy : x = y
    · subst y
      have hx : x.1 ≠ x.2 := fun h => hdiag ⟨h, h⟩
      simp [hx, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
        matrixDiagonalPairProjector, Matrix.diagonal_apply, bellProjector_apply]
    · simp [hdiag, hxy, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
        matrixDiagonalPairProjector, Matrix.diagonal_apply, bellProjector_apply]

theorem matrixPermutationTwirl_zeroDiagonalPair (f : α × α → ℂ)
    (hf : ∀ i, f (i, i) = 0) :
    matrixPermutationTwirl (Matrix.diagonal f) =
      ((∑ x, f x) / ((Fintype.card α : ℂ) * ((Fintype.card α : ℂ) - 1))) •
        (1 - matrixDiagonalPairProjector) := by
  ext x y
  rw [matrixPermutationTwirl_diagonal_apply]
  by_cases hxy : x = y
  · subst y
    by_cases hx : x.1 = x.2
    · rcases x with ⟨i, j⟩
      simp only at hx
      subst j
      rw [if_pos rfl, matrixPermutationMean_diag]
      simp [hf, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
        matrixDiagonalPairProjector, Matrix.diagonal_apply]
    · rw [if_pos rfl, matrixPermutationMean_offdiag f x.1 x.2 hx]
      simp [hf, hx, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
        matrixDiagonalPairProjector, Matrix.diagonal_apply]
  · simp [hxy, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      matrixDiagonalPairProjector, Matrix.diagonal_apply]

theorem fourthPhaseTwirl_diagonal_decomposition
    (ρ : Matrix (α × α) (α × α) ℂ) :
    fourthPhaseTwirl ρ =
      matrixDiagonalPairEmbedding (fun z => ρ (z.1, z.1) (z.2, z.2)) +
      Matrix.diagonal (fun z => if z.1 = z.2 then 0 else ρ z z) := by
  ext x y
  rw [fourthPhaseTwirl_apply]
  by_cases hdiag : x.1 = x.2 ∧ y.1 = y.2
  · have hx : x = (x.1, x.1) := by
      apply Prod.ext
      · rfl
      · exact hdiag.1.symm
    have hy : y = (y.1, y.1) := by
      apply Prod.ext
      · rfl
      · exact hdiag.2.symm
    have hD : (Matrix.diagonal (fun z : α × α =>
        if z.1 = z.2 then 0 else ρ z z)) x y = 0 := by
      by_cases hxy : x = y
      · subst y
        simp [Matrix.diagonal_apply, hdiag.1]
      · simp [Matrix.diagonal_apply, hxy]
    rw [if_pos (Or.inl hdiag)]
    change ρ x y = (if x.1 = x.2 ∧ y.1 = y.2 then
      ρ (x.1, x.1) (y.1, y.1) else 0) +
      (Matrix.diagonal (fun z : α × α => if z.1 = z.2 then 0 else ρ z z)) x y
    rw [if_pos hdiag, hD, add_zero]
    exact congrArg₂ ρ hx hy
  · by_cases hxy : x = y
    · subst y
      have hx : x.1 ≠ x.2 := fun h => hdiag ⟨h, h⟩
      simp [hx, matrixDiagonalPairEmbedding, Matrix.add_apply, Matrix.diagonal_apply]
    · simp [hdiag, hxy, matrixDiagonalPairEmbedding, Matrix.add_apply,
        Matrix.diagonal_apply]

theorem phaseOutsideDiagonal_sum (ρ : Matrix (α × α) (α × α) ℂ) :
    (∑ x : α × α, if x.1 = x.2 then 0 else ρ x x) =
      Matrix.trace ρ - ∑ i, ρ (i, i) (i, i) := by
  calc
    _ = ∑ x : α × α, (ρ x x - if x.1 = x.2 then ρ x x else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      have hdiag : (∑ x : α × α, if x.1 = x.2 then ρ x x else 0) =
          ∑ i, ρ (i, i) (i, i) := by
        rw [Fintype.sum_prod_type]
        simp
      rw [hdiag]
      rfl

theorem matrixPhasePermutationTwirl_blocks
    (ρ : Matrix (α × α) (α × α) ℂ) (hα : 2 ≤ Fintype.card α) :
    matrixPermutationTwirl (fourthPhaseTwirl ρ) =
      ((∑ z : α × α, ρ (z.1, z.1) (z.2, z.2)) / (Fintype.card α : ℂ)) •
        bellProjector +
      (((∑ i, ρ (i, i) (i, i)) -
        (∑ z : α × α, ρ (z.1, z.1) (z.2, z.2)) / (Fintype.card α : ℂ)) /
        ((Fintype.card α : ℂ) - 1)) • (matrixDiagonalPairProjector - bellProjector) +
      ((Matrix.trace ρ - ∑ i, ρ (i, i) (i, i)) /
        ((Fintype.card α : ℂ) * ((Fintype.card α : ℂ) - 1))) •
        (1 - matrixDiagonalPairProjector) := by
  rw [fourthPhaseTwirl_diagonal_decomposition, matrixPermutationTwirl_add,
    matrixPermutationTwirl_diagonalPairEmbedding_eq _ hα]
  rw [matrixPermutationTwirl_zeroDiagonalPair
    (fun z : α × α => if z.1 = z.2 then 0 else ρ z z) (by intro i; simp),
    phaseOutsideDiagonal_sum]

theorem matrixPhasePermutationTwirl_blocks_normalized
    (ρ : Matrix (α × α) (α × α) ℂ) (hα : 2 ≤ Fintype.card α)
    (htrace : Matrix.trace ρ = 1) :
    matrixPermutationTwirl (fourthPhaseTwirl ρ) =
      ((∑ z : α × α, ρ (z.1, z.1) (z.2, z.2)) / (Fintype.card α : ℂ)) •
        bellProjector +
      (((∑ i, ρ (i, i) (i, i)) -
        (∑ z : α × α, ρ (z.1, z.1) (z.2, z.2)) / (Fintype.card α : ℂ)) /
        ((Fintype.card α : ℂ) - 1)) • (matrixDiagonalPairProjector - bellProjector) +
      ((1 - ∑ i, ρ (i, i) (i, i)) /
        ((Fintype.card α : ℂ) * ((Fintype.card α : ℂ) - 1))) •
        (1 - matrixDiagonalPairProjector) := by
  simpa only [htrace] using matrixPhasePermutationTwirl_blocks ρ hα

theorem matrixPhasePermutationTwirl_trace_blocks
    (ρ : Matrix (α × α) (α × α) ℂ) (hα : 2 ≤ Fintype.card α) :
    matrixPermutationTwirl (fourthPhaseTwirl ρ) =
      Matrix.trace (ρ * bellProjector) • bellProjector +
      ((Matrix.trace (ρ * matrixDiagonalPairProjector) -
        Matrix.trace (ρ * bellProjector)) / ((Fintype.card α : ℂ) - 1)) •
        (matrixDiagonalPairProjector - bellProjector) +
      ((Matrix.trace ρ - Matrix.trace (ρ * matrixDiagonalPairProjector)) /
        ((Fintype.card α : ℂ) * ((Fintype.card α : ℂ) - 1))) •
        (1 - matrixDiagonalPairProjector) := by
  simpa only [trace_mul_bellProjector_exact, trace_mul_matrixDiagonalPairProjector] using
    matrixPhasePermutationTwirl_blocks ρ hα

theorem matrixPhasePermutationTwirl_real_blocks
    (ρ : Matrix (α × α) (α × α) ℂ) (hρ : ρ.IsHermitian)
    (hα : 2 ≤ Fintype.card α) :
    let t : ℝ := (Matrix.trace ρ).re
    let p : ℝ := (Matrix.trace (ρ * bellProjector)).re
    let q : ℝ := (Matrix.trace (ρ * matrixDiagonalPairProjector)).re - p
    matrixPermutationTwirl (fourthPhaseTwirl ρ) =
      (p : ℂ) • bellProjector +
      ((q / ((Fintype.card α : ℝ) - 1) : ℝ) : ℂ) •
        (matrixDiagonalPairProjector - bellProjector) +
      (((t - p - q) / ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)) : ℝ) : ℂ) •
        (1 - matrixDiagonalPairProjector) := by
  dsimp only
  have ht := matrixHermitianTrace_eq_ofReal ρ hρ
  have hp := matrixHermitianTrace_mul_eq_ofReal ρ bellProjector hρ
    bellProjector_posSemidef.isHermitian
  have hr := matrixHermitianTrace_mul_eq_ofReal ρ matrixDiagonalPairProjector hρ
    matrixDiagonalPairProjector_hermitian
  have hq : Matrix.trace (ρ * matrixDiagonalPairProjector) -
      Matrix.trace (ρ * bellProjector) =
      (((Matrix.trace (ρ * matrixDiagonalPairProjector)).re -
        (Matrix.trace (ρ * bellProjector)).re : ℝ) : ℂ) := by
    calc
      _ = ((Matrix.trace (ρ * matrixDiagonalPairProjector)).re : ℂ) -
          ((Matrix.trace (ρ * bellProjector)).re : ℂ) :=
        congrArg₂ (fun a b : ℂ => a - b) hr hp
      _ = _ := (Complex.ofReal_sub _ _).symm
  have hc : Matrix.trace ρ - Matrix.trace (ρ * matrixDiagonalPairProjector) =
      (((Matrix.trace ρ).re - (Matrix.trace (ρ * matrixDiagonalPairProjector)).re : ℝ) : ℂ) := by
    calc
      _ = ((Matrix.trace ρ).re : ℂ) -
          ((Matrix.trace (ρ * matrixDiagonalPairProjector)).re : ℂ) :=
        congrArg₂ (fun a b : ℂ => a - b) ht hr
      _ = _ := (Complex.ofReal_sub _ _).symm
  have hnum : (Matrix.trace ρ).re - (Matrix.trace (ρ * bellProjector)).re -
      ((Matrix.trace (ρ * matrixDiagonalPairProjector)).re -
        (Matrix.trace (ρ * bellProjector)).re) =
      (Matrix.trace ρ).re - (Matrix.trace (ρ * matrixDiagonalPairProjector)).re := by ring
  rw [matrixPhasePermutationTwirl_trace_blocks ρ hα, hq, hc, hp]
  simp only [Complex.ofReal_re]
  rw [hnum]
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_natCast, Complex.ofReal_one]

def matrixPermutationUnitary (σ : Equiv.Perm α) : unitary (Matrix α α ℂ) :=
  ⟨σ.permMatrix ℂ, Unitary.mem_iff.mpr ⟨
    by simpa only [Matrix.star_eq_conjTranspose] using permutationCoeff_unitary_col σ,
    by simpa only [Matrix.star_eq_conjTranspose] using
      mul_eq_one_comm.mp (permutationCoeff_unitary_col σ)⟩⟩

theorem matrixPermutationTwirl_pureDensity (M : Matrix α α ℂ) :
    matrixPermutationTwirl (pureDensity M) =
      (Fintype.card (Equiv.Perm α) : ℂ)⁻¹ • ∑ σ : Equiv.Perm α,
        pureDensity (σ.permMatrix ℂ * M * (σ.permMatrix ℂ)ᴴ) := by
  simp only [matrixPermutationTwirl, pureDensity_localPairCoeff]

end MatrixPhysicalPermutationTwirl

end QuantumProver.IsotropicFormation
