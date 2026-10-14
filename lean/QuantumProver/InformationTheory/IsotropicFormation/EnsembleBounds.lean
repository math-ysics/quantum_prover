import Mathlib

noncomputable section

namespace QuantumProver.IsotropicFormation

open scoped BigOperators

variable {α β ι : Type*} [Fintype α] [Fintype β]

def classicalEntropy (p : α → ℝ) : ℝ := ∑ a, Real.negMulLog (p a)

def marginalLeft (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)

def marginalRight (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)

def conditionalLeft (p : α × β → ℝ) (b : β) (a : α) : ℝ :=
  p (a, b) / marginalRight p b

def conditionalRight (p : α × β → ℝ) (a : α) (b : β) : ℝ :=
  p (a, b) / marginalLeft p a

omit [Fintype α] in
theorem marginalLeft_nonneg (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) (a : α) :
    0 ≤ marginalLeft p a := Finset.sum_nonneg (fun b _ => hp (a, b))

omit [Fintype β] in
theorem marginalRight_nonneg (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) (b : β) :
    0 ≤ marginalRight p b := Finset.sum_nonneg (fun a _ => hp (a, b))

theorem marginalLeft_sum (p : α × β → ℝ) :
    ∑ a, marginalLeft p a = ∑ z, p z := by
  simp only [marginalLeft, Fintype.sum_prod_type]

theorem marginalRight_sum (p : α × β → ℝ) :
    ∑ b, marginalRight p b = ∑ z, p z := by
  simp only [marginalRight, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [Fintype β] in
theorem entry_le_marginalRight (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z)
    (a : α) (b : β) : p (a, b) ≤ marginalRight p b := by
  exact Finset.single_le_sum (fun a _ => hp (a, b)) (Finset.mem_univ a)

omit [Fintype β] in
theorem entry_eq_zero_of_marginalRight_zero (p : α × β → ℝ)
    (hp : ∀ z, 0 ≤ p z) (a : α) (b : β) (hb : marginalRight p b = 0) :
    p (a, b) = 0 :=
  le_antisymm (hb ▸ entry_le_marginalRight p hp a b) (hp (a, b))

omit [Fintype β] in
theorem conditionalLeft_nonneg (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z)
    (b : β) (a : α) : 0 ≤ conditionalLeft p b a :=
  div_nonneg (hp (a, b)) (marginalRight_nonneg p hp b)

omit [Fintype β] in
theorem conditionalLeft_reconstruct (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z)
    (b : β) (a : α) : marginalRight p b * conditionalLeft p b a = p (a, b) := by
  by_cases hb : marginalRight p b = 0
  · simp [conditionalLeft, hb, entry_eq_zero_of_marginalRight_zero p hp a b hb]
  · unfold conditionalLeft
    field_simp [hb]

omit [Fintype β] in
theorem conditionalLeft_sum (p : α × β → ℝ) (b : β)
    (hb : marginalRight p b ≠ 0) : ∑ a, conditionalLeft p b a = 1 := by
  simp only [conditionalLeft, ← Finset.sum_div]
  exact div_self hb

theorem classicalEntropy_mul (w : ℝ) (p : α → ℝ) :
    classicalEntropy (fun a => w * p a) =
      (∑ a, p a) * Real.negMulLog w + w * classicalEntropy p := by
  simp only [classicalEntropy, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]

theorem classicalEntropy_nonneg (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) : 0 ≤ classicalEntropy p := by
  apply Finset.sum_nonneg
  intro a _
  apply Real.negMulLog_nonneg (hp a)
  rw [← hsum]
  exact Finset.single_le_sum (fun a _ => hp a) (Finset.mem_univ a)

theorem classicalEntropy_swap (p : α × β → ℝ) :
    classicalEntropy (fun z : β × α => p (z.2, z.1)) = classicalEntropy p := by
  simp only [classicalEntropy, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem classicalEntropy_concave_mixture [Fintype ι] (w : ι → ℝ)
    (p : ι → α → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hp : ∀ i a, 0 ≤ p i a) :
    (∑ i, w i * classicalEntropy (p i)) ≤
      classicalEntropy (fun a => ∑ i, w i * p i a) := by
  have hreorder : (∑ i, w i * classicalEntropy (p i)) =
      ∑ a, ∑ i, w i * Real.negMulLog (p i a) := by
    simp only [classicalEntropy, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hreorder]
  apply Finset.sum_le_sum
  intro a _
  simpa only [smul_eq_mul] using
    Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := w)
      (p := fun i => p i a) (fun i _ => hw i) hsum (fun i _ => hp i a)

omit [Fintype β] in

theorem conditionalLeft_entropy_column (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z)
    (b : β) :
    marginalRight p b * classicalEntropy (conditionalLeft p b) =
      (∑ a, Real.negMulLog (p (a, b))) - Real.negMulLog (marginalRight p b) := by
  by_cases hb : marginalRight p b = 0
  · have he : ∀ a, p (a, b) = 0 := fun a =>
      entry_eq_zero_of_marginalRight_zero p hp a b hb
    simp [hb, he]
  · have heq : (fun a => marginalRight p b * conditionalLeft p b a) =
        fun a => p (a, b) := funext (conditionalLeft_reconstruct p hp b)
    have h := classicalEntropy_mul (marginalRight p b) (conditionalLeft p b)
    rw [heq, conditionalLeft_sum p b hb, one_mul] at h
    change (∑ a, Real.negMulLog (p (a, b))) =
      Real.negMulLog (marginalRight p b) +
        marginalRight p b * classicalEntropy (conditionalLeft p b) at h
    linarith [h]

theorem weightedConditionalLeft_eq (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) :
    (∑ b, marginalRight p b * classicalEntropy (conditionalLeft p b)) =
      classicalEntropy p - classicalEntropy (marginalRight p) := by
  simp_rw [conditionalLeft_entropy_column p hp]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [classicalEntropy, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem weightedConditionalRight_eq (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) :
    (∑ a, marginalLeft p a * classicalEntropy (conditionalRight p a)) =
      classicalEntropy p - classicalEntropy (marginalLeft p) := by
  have h := weightedConditionalLeft_eq
    (fun z : β × α => p (z.2, z.1)) (fun z => hp (z.2, z.1))
  change (∑ a, marginalLeft p a * classicalEntropy (conditionalRight p a)) =
    classicalEntropy (fun z : β × α => p (z.2, z.1)) -
      classicalEntropy (marginalLeft p) at h
  rw [classicalEntropy_swap] at h
  exact h

theorem weightedConditionalLeft_le_marginal (p : α × β → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    (∑ b, marginalRight p b * classicalEntropy (conditionalLeft p b)) ≤
      classicalEntropy (marginalLeft p) := by
  have hm : (fun a => ∑ b, marginalRight p b * conditionalLeft p b a) =
      marginalLeft p := by
    funext a
    simp_rw [conditionalLeft_reconstruct p hp]
    rfl
  have h := classicalEntropy_concave_mixture (marginalRight p) (conditionalLeft p)
    (marginalRight_nonneg p hp) ((marginalRight_sum p).trans hsum)
    (conditionalLeft_nonneg p hp)
  rw [hm] at h
  exact h

theorem classicalEntropy_pair_le_marginals (p : α × β → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    classicalEntropy p ≤ classicalEntropy (marginalLeft p) +
      classicalEntropy (marginalRight p) := by
  have h := weightedConditionalLeft_le_marginal p hp hsum
  rw [weightedConditionalLeft_eq p hp] at h
  linarith

theorem weightedConditionals_le_entropy (p : α × β → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    (∑ b, marginalRight p b * classicalEntropy (conditionalLeft p b)) +
      (∑ a, marginalLeft p a * classicalEntropy (conditionalRight p a)) ≤
        classicalEntropy p := by
  rw [weightedConditionalLeft_eq p hp, weightedConditionalRight_eq p hp]
  linarith [classicalEntropy_pair_le_marginals p hp hsum]

def classicalBellFidelity (q : α → ℝ) : ℝ :=
  (∑ a, Real.sqrt (q a)) ^ 2 / (Fintype.card α : ℝ)

def diagonalBellFidelityLeft (p : α × β → ℝ) : ℝ :=
  (∑ b, (∑ a, Real.sqrt (p (a, b))) ^ 2) / (Fintype.card α : ℝ)

def diagonalBellFidelityRight (p : α × β → ℝ) : ℝ :=
  diagonalBellFidelityLeft (fun z : β × α => p (z.2, z.1))

theorem weightedConditionalLeft_fidelity (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) :
    (∑ b, marginalRight p b * classicalBellFidelity (conditionalLeft p b)) =
      diagonalBellFidelityLeft p := by
  unfold classicalBellFidelity diagonalBellFidelityLeft
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  have hroot : (∑ a, Real.sqrt (p (a, b))) =
      Real.sqrt (marginalRight p b) * ∑ a, Real.sqrt (conditionalLeft p b a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [← conditionalLeft_reconstruct p hp b a,
      Real.sqrt_mul (marginalRight_nonneg p hp b)]
  have hsq : (∑ a, Real.sqrt (p (a, b))) ^ 2 =
      marginalRight p b * (∑ a, Real.sqrt (conditionalLeft p b a)) ^ 2 := by
    rw [hroot, mul_pow, Real.sq_sqrt (marginalRight_nonneg p hp b)]
  rw [← mul_div_assoc, hsq]

theorem conditionalLeft_affine_lower (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z)
    (hsum : ∑ z, p z = 1) (a b : ℝ)
    (hsupport : ∀ q : α → ℝ, (∀ x, 0 ≤ q x) → (∑ x, q x = 1) →
      a + b * classicalBellFidelity q ≤ classicalEntropy q) :
    a + b * diagonalBellFidelityLeft p ≤
      ∑ y, marginalRight p y * classicalEntropy (conditionalLeft p y) := by
  have hy (y : β) :
      marginalRight p y * (a + b * classicalBellFidelity (conditionalLeft p y)) ≤
        marginalRight p y * classicalEntropy (conditionalLeft p y) := by
    by_cases hzero : marginalRight p y = 0
    · simp [hzero]
    · exact mul_le_mul_of_nonneg_left
        (hsupport (conditionalLeft p y) (conditionalLeft_nonneg p hp y)
          (conditionalLeft_sum p y hzero)) (marginalRight_nonneg p hp y)
  have hcalc :
      (∑ y, marginalRight p y * (a + b * classicalBellFidelity (conditionalLeft p y))) =
        a + b * diagonalBellFidelityLeft p := by
    calc
      _ = (∑ y, marginalRight p y) * a +
          b * ∑ y, marginalRight p y * classicalBellFidelity (conditionalLeft p y) := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = _ := by rw [marginalRight_sum, hsum, one_mul, weightedConditionalLeft_fidelity p hp]
  rw [← hcalc]
  exact Finset.sum_le_sum (fun y _ => hy y)

theorem conditionalRight_affine_lower (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z)
    (hsum : ∑ z, p z = 1) (a b : ℝ)
    (hsupport : ∀ q : β → ℝ, (∀ y, 0 ≤ q y) → (∑ y, q y = 1) →
      a + b * classicalBellFidelity q ≤ classicalEntropy q) :
    a + b * diagonalBellFidelityRight p ≤
      ∑ x, marginalLeft p x * classicalEntropy (conditionalRight p x) := by
  have hswap : (∑ z : β × α, p (z.2, z.1)) = 1 := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using hsum
  exact conditionalLeft_affine_lower (fun z : β × α => p (z.2, z.1))
    (fun z => hp (z.2, z.1)) hswap a b hsupport

theorem diagonal_twoFactor_affine_lower (p : α × β → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) (a1 b1 a2 b2 : ℝ)
    (h1 : ∀ q : α → ℝ, (∀ x, 0 ≤ q x) → (∑ x, q x = 1) →
      a1 + b1 * classicalBellFidelity q ≤ classicalEntropy q)
    (h2 : ∀ q : β → ℝ, (∀ y, 0 ≤ q y) → (∑ y, q y = 1) →
      a2 + b2 * classicalBellFidelity q ≤ classicalEntropy q) :
    a1 + a2 + b1 * diagonalBellFidelityLeft p + b2 * diagonalBellFidelityRight p ≤
      classicalEntropy p := by
  have hleft := conditionalLeft_affine_lower p hp hsum a1 b1 h1
  have hright := conditionalRight_affine_lower p hp hsum a2 b2 h2
  have htotal := weightedConditionals_le_entropy p hp hsum
  linarith

section DiagonalCFC

open scoped ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator ContinuousFunctionalCalculus

variable [DecidableEq α]

local instance : ContinuousFunctionalCalculus ℂ (α → ℂ) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

local instance : ContinuousFunctionalCalculus ℝ (α → ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

def realDiagonal (p : α → ℝ) : Matrix α α ℂ :=
  Matrix.diagonal (fun a => (p a : ℂ))

def diagonalRealStarAlgHom : (α → ℂ) →⋆ₐ[ℝ] Matrix α α ℂ where
  toAlgHom :=
    { toRingHom := Matrix.diagonalRingHom α ℂ
      commutes' r := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [Algebra.algebraMap_eq_smul_one]
        · simp [Algebra.algebraMap_eq_smul_one, hij] }
  map_star' v := by
    change Matrix.diagonal (star v) = (Matrix.diagonal v)ᴴ
    rw [Matrix.diagonal_conjTranspose]

theorem diagonalRealStarAlgHom_continuous :
    Continuous (diagonalRealStarAlgHom (α := α)) :=
  (LinearMap.toContinuousLinearMap
    (diagonalRealStarAlgHom (α := α)).toAlgHom.toLinearMap).continuous

theorem cfc_realDiagonal (p : α → ℝ) :
    cfc Real.negMulLog (realDiagonal p) = realDiagonal (fun a => Real.negMulLog (p a)) := by
  have ha : IsSelfAdjoint (fun a : α => (p a : ℂ)) := by
    change star (fun a : α => (p a : ℂ)) = _
    ext a
    simp
  have hd : IsSelfAdjoint (realDiagonal p) := by
    change (Matrix.diagonal (fun a => (p a : ℂ)))ᴴ = _
    rw [Matrix.diagonal_conjTranspose, ha]
    rfl
  have hpi : cfc Real.negMulLog (fun a : α => (p a : ℂ)) =
      fun a => (Real.negMulLog (p a) : ℂ) := by
    rw [cfc_map_pi (S := ℝ) Real.negMulLog (fun a : α => (p a : ℂ))
      (hf := Real.continuous_negMulLog.continuousOn) (ha := ha)
      (ha' := fun a => by change star (p a : ℂ) = (p a : ℂ); simp)]
    funext a
    change cfc Real.negMulLog (algebraMap ℝ ℂ (p a)) = _
    rw [cfc_algebraMap]
    rfl
  have h := (diagonalRealStarAlgHom (α := α)).map_cfc Real.negMulLog
    (fun a : α => (p a : ℂ)) Real.continuous_negMulLog.continuousOn
    diagonalRealStarAlgHom_continuous ha hd
  rw [hpi] at h
  exact h.symm

theorem trace_cfc_eq_sum (A : Matrix α α ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    Matrix.trace (cfc f A) = ∑ i, (f (hA.eigenvalues i) : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.trace_diagonal]
  rfl

theorem trace_cfc_eq_of_charpoly_eq (A B : Matrix α α ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hc : A.charpoly = B.charpoly)
    (f : ℝ → ℝ) : Matrix.trace (cfc f A) = Matrix.trace (cfc f B) := by
  rw [trace_cfc_eq_sum A hA, trace_cfc_eq_sum B hB,
    (hA.eigenvalues_eq_eigenvalues_iff hB).mpr hc]

end DiagonalCFC

end QuantumProver.IsotropicFormation
