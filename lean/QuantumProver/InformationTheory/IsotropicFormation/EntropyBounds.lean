import Mathlib

noncomputable section

namespace QuantumProver.IsotropicFormation

open scoped BigOperators ComplexOrder MatrixOrder Matrix

variable {α β : Type*}

def hsSq [Fintype α] [Fintype β] (M : Matrix α β ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

def hsInner [Fintype α] [Fintype β] (A B : Matrix α β ℂ) : ℝ :=
  ∑ i, ∑ j, (star (A i j) * B i j).re

def ptraceLeft [Fintype α] (M : Matrix (α × β) (α × β) ℂ) : Matrix β β ℂ :=
  fun j k => ∑ i, M (i, j) (i, k)

def ptraceRight [Fintype β] (M : Matrix (α × β) (α × β) ℂ) : Matrix α α ℂ :=
  fun i k => ∑ j, M (i, j) (k, j)

def bellFidelityLeft [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) : ℝ :=
  hsSq (ptraceLeft M) / Fintype.card α

def bellFidelityRight [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) : ℝ :=
  hsSq (ptraceRight M) / Fintype.card β

theorem hsSq_nonneg [Fintype α] [Fintype β] (M : Matrix α β ℂ) :
    0 ≤ hsSq M := by
  exact Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg (M i j)))

theorem hsSq_zero [Fintype α] [Fintype β] :
    hsSq (0 : Matrix α β ℂ) = 0 := by
  simp [hsSq]

theorem hsInner_self [Fintype α] [Fintype β] (M : Matrix α β ℂ) :
    hsInner M M = hsSq M := by
  simp [hsInner, hsSq, Complex.mul_re, Complex.normSq_apply]

theorem scalar_normSq_sub (z w : ℂ) :
    Complex.normSq (z - w) = Complex.normSq z + Complex.normSq w -
      2 * (star w * z).re := by
  simp [Complex.normSq_apply, Complex.mul_re]
  ring

theorem hsSq_sub [Fintype α] [Fintype β] (A B : Matrix α β ℂ) :
    hsSq (A - B) = hsSq A + hsSq B - 2 * hsInner B A := by
  simp only [hsSq, hsInner, Matrix.sub_apply]
  simp_rw [scalar_normSq_sub]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem hsSq_square_completion [Fintype α] [Fintype β]
    (A B : Matrix α β ℂ) :
    2 * hsInner B A - hsSq B ≤ hsSq A := by
  have h := hsSq_nonneg (A - B)
  rw [hsSq_sub] at h
  linarith

theorem ptraceLeft_trace [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) :
    Matrix.trace (ptraceLeft M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag_apply, ptraceLeft, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem ptraceRight_trace [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) :
    Matrix.trace (ptraceRight M) = Matrix.trace M := by
  simp [Matrix.trace, ptraceRight, Fintype.sum_prod_type]

theorem ptraceLeft_posSemidef [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) (hM : M.PosSemidef) :
    (ptraceLeft M).PosSemidef := by
  have hp := Matrix.posSemidef_sum (Finset.univ : Finset α)
    (fun i _ => hM.submatrix (fun j : β => (i, j)))
  have heq : ptraceLeft M = ∑ i, M.submatrix (fun j : β => (i, j))
      (fun j : β => (i, j)) := by
    ext j k
    simp [ptraceLeft, Matrix.submatrix_apply, Matrix.sum_apply]
  rw [heq]
  simpa using hp

theorem ptraceRight_posSemidef [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) (hM : M.PosSemidef) :
    (ptraceRight M).PosSemidef := by
  have hp := Matrix.posSemidef_sum (Finset.univ : Finset β)
    (fun j _ => hM.submatrix (fun i : α => (i, j)))
  have heq : ptraceRight M = ∑ j, M.submatrix (fun i : α => (i, j))
      (fun i : α => (i, j)) := by
    ext i k
    simp [ptraceRight, Matrix.submatrix_apply, Matrix.sum_apply]
  rw [heq]
  simpa using hp

theorem bellFidelityLeft_nonneg [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) : 0 ≤ bellFidelityLeft M := by
  exact div_nonneg (hsSq_nonneg _) (Nat.cast_nonneg _)

theorem bellFidelityRight_nonneg [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) : 0 ≤ bellFidelityRight M := by
  exact div_nonneg (hsSq_nonneg _) (Nat.cast_nonneg _)

theorem ptraceLeft_add [Fintype α]
    (A B : Matrix (α × β) (α × β) ℂ) :
    ptraceLeft (A + B) = ptraceLeft A + ptraceLeft B := by
  ext j k
  simp [ptraceLeft, Finset.sum_add_distrib]

theorem ptraceRight_add [Fintype β]
    (A B : Matrix (α × β) (α × β) ℂ) :
    ptraceRight (A + B) = ptraceRight A + ptraceRight B := by
  ext i k
  simp [ptraceRight, Finset.sum_add_distrib]

theorem ptraceLeft_sub [Fintype α]
    (A B : Matrix (α × β) (α × β) ℂ) :
    ptraceLeft (A - B) = ptraceLeft A - ptraceLeft B := by
  ext j k
  simp [ptraceLeft, Finset.sum_sub_distrib]

theorem ptraceRight_sub [Fintype β]
    (A B : Matrix (α × β) (α × β) ℂ) :
    ptraceRight (A - B) = ptraceRight A - ptraceRight B := by
  ext i k
  simp [ptraceRight, Finset.sum_sub_distrib]

theorem ptraceLeft_smul [Fintype α] (z : ℂ)
    (M : Matrix (α × β) (α × β) ℂ) :
    ptraceLeft (z • M) = z • ptraceLeft M := by
  ext j k
  simp [ptraceLeft, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem ptraceRight_smul [Fintype β] (z : ℂ)
    (M : Matrix (α × β) (α × β) ℂ) :
    ptraceRight (z • M) = z • ptraceRight M := by
  ext i k
  simp [ptraceRight, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem ptraceLeft_conjTranspose [Fintype α]
    (M : Matrix (α × β) (α × β) ℂ) :
    ptraceLeft Mᴴ = (ptraceLeft M)ᴴ := by
  ext j k
  simp [ptraceLeft, Matrix.conjTranspose_apply, star_sum]

theorem ptraceRight_conjTranspose [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) :
    ptraceRight Mᴴ = (ptraceRight M)ᴴ := by
  ext i k
  simp [ptraceRight, Matrix.conjTranspose_apply, star_sum]

theorem normSq_sum_le_card_mul [Fintype α] (z : α → ℂ) :
    Complex.normSq (∑ i, z i) ≤
      (Fintype.card α : ℝ) * ∑ i, Complex.normSq (z i) := by
  have hre := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun i => (z i).re)
  have him := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun i => (z i).im)
  simpa only [Complex.normSq_apply, Complex.re_sum, Complex.im_sum,
    Finset.card_univ, pow_two, Finset.sum_add_distrib, mul_add] using
      add_le_add hre him

theorem weighted_ptrace_square_completion [Fintype α] [Fintype β]
    (A B : Matrix (α × β) (α × β) ℂ) (w₁ w₂ : ℝ)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) :
    2 * (w₁ * hsInner (ptraceLeft B) (ptraceLeft A) +
      w₂ * hsInner (ptraceRight B) (ptraceRight A)) -
      (w₁ * hsSq (ptraceLeft B) + w₂ * hsSq (ptraceRight B)) ≤
      w₁ * hsSq (ptraceLeft A) + w₂ * hsSq (ptraceRight A) := by
  have h₁ := mul_le_mul_of_nonneg_left
    (hsSq_square_completion (ptraceLeft A) (ptraceLeft B)) hw₁
  have h₂ := mul_le_mul_of_nonneg_left
    (hsSq_square_completion (ptraceRight A) (ptraceRight B)) hw₂
  nlinarith

theorem hsSq_eq_trace_self_mul_conjTranspose [Fintype α] [Fintype β]
    (M : Matrix α β ℂ) : hsSq M = (Matrix.trace (M * Mᴴ)).re := by
  simp [hsSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.mul_conj, Complex.re_sum]

theorem hsSq_eq_trace_conjTranspose_mul_self [Fintype α] [Fintype β]
    (M : Matrix α β ℂ) : hsSq M = (Matrix.trace (Mᴴ * M)).re := by
  rw [Matrix.trace_mul_comm]
  exact hsSq_eq_trace_self_mul_conjTranspose M

theorem bellFidelityLeft_le_hsSq [Fintype α] [Fintype β] [Nonempty α]
    (M : Matrix (α × β) (α × β) ℂ) : bellFidelityLeft M ≤ hsSq M := by
  classical
  have hentry (j k : β) := normSq_sum_le_card_mul
    (fun i : α => M (i, j) (i, k))
  have htrace : hsSq (ptraceLeft M) ≤ (Fintype.card α : ℝ) *
      ∑ j : β, ∑ k : β, ∑ i : α, Complex.normSq (M (i, j) (i, k)) := by
    unfold hsSq ptraceLeft
    calc
      _ ≤ ∑ j : β, ∑ k : β, (Fintype.card α : ℝ) *
          ∑ i : α, Complex.normSq (M (i, j) (i, k)) := by
        exact Finset.sum_le_sum (fun j _ =>
          Finset.sum_le_sum (fun k _ => hentry j k))
      _ = _ := by simp only [Finset.mul_sum]
  have hdiag : (∑ j : β, ∑ k : β, ∑ i : α,
      Complex.normSq (M (i, j) (i, k))) ≤ hsSq M := by
    calc
      _ ≤ ∑ j : β, ∑ k : β, ∑ i : α, ∑ l : α,
          Complex.normSq (M (i, j) (l, k)) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.single_le_sum
          (fun l _ => Complex.normSq_nonneg (M (i, j) (l, k))) (Finset.mem_univ i)
      _ = hsSq M := by
        calc
          _ = ∑ j : β, ∑ i : α, ∑ k : β, ∑ l : α,
              Complex.normSq (M (i, j) (l, k)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.sum_comm]
          _ = ∑ i : α, ∑ j : β, ∑ k : β, ∑ l : α,
              Complex.normSq (M (i, j) (l, k)) := by rw [Finset.sum_comm]
          _ = hsSq M := by
            simp only [hsSq, Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.sum_comm]
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hc).2
  simpa [mul_comm] using htrace.trans (mul_le_mul_of_nonneg_left hdiag hc.le)

def swapCoeff (M : Matrix (α × β) (α × β) ℂ) :
    Matrix (β × α) (β × α) ℂ :=
  fun x y => M (x.2, x.1) (y.2, y.1)

theorem hsSq_swapCoeff [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) : hsSq (swapCoeff M) = hsSq M := by
  simp only [hsSq, swapCoeff, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]

theorem ptraceLeft_swapCoeff [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) :
    ptraceLeft (swapCoeff M) = ptraceRight M := rfl

theorem ptraceRight_swapCoeff [Fintype α]
    (M : Matrix (α × β) (α × β) ℂ) :
    ptraceRight (swapCoeff M) = ptraceLeft M := rfl

theorem bellFidelityLeft_swapCoeff [Fintype α] [Fintype β]
    (M : Matrix (α × β) (α × β) ℂ) :
    bellFidelityLeft (swapCoeff M) = bellFidelityRight M := rfl

theorem bellFidelityRight_le_hsSq [Fintype α] [Fintype β] [Nonempty β]
    (M : Matrix (α × β) (α × β) ℂ) : bellFidelityRight M ≤ hsSq M := by
  rw [← bellFidelityLeft_swapCoeff]
  exact (bellFidelityLeft_le_hsSq (swapCoeff M)).trans_eq (hsSq_swapCoeff M)

def liftLeft [DecidableEq α] (B : Matrix β β ℂ) :
    Matrix (α × β) (α × β) ℂ :=
  fun x y => if x.1 = y.1 then B x.2 y.2 else 0

def liftRight [DecidableEq β] (A : Matrix α α ℂ) :
    Matrix (α × β) (α × β) ℂ :=
  fun x y => if x.2 = y.2 then A x.1 y.1 else 0

theorem hsInner_liftLeft [Fintype α] [Fintype β] [DecidableEq α]
    (M : Matrix (α × β) (α × β) ℂ) (B : Matrix β β ℂ) :
    hsInner M (liftLeft B) = hsInner (ptraceLeft M) B := by
  calc
    _ = ∑ i : α, ∑ j : β, ∑ k : β,
        (star (M (i, j) (i, k)) * B j k).re := by
      simp [hsInner, liftLeft, Fintype.sum_prod_type, apply_ite, Finset.sum_ite_irrel]
    _ = ∑ j : β, ∑ k : β, ∑ i : α,
        (star (M (i, j) (i, k)) * B j k).re := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
    _ = _ := by
      simp [hsInner, ptraceLeft, star_sum, Finset.sum_mul, Complex.re_sum]

theorem hsInner_liftRight [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix (α × β) (α × β) ℂ) (A : Matrix α α ℂ) :
    hsInner M (liftRight A) = hsInner (ptraceRight M) A := by
  calc
    _ = ∑ i : α, ∑ j : β, ∑ k : α,
        (star (M (i, j) (k, j)) * A i k).re := by
      simp [hsInner, liftRight, Fintype.sum_prod_type, apply_ite]
    _ = ∑ i : α, ∑ k : α, ∑ j : β,
        (star (M (i, j) (k, j)) * A i k).re := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = _ := by
      simp [hsInner, ptraceRight, star_sum, Finset.sum_mul, Complex.re_sum]

def hsCoordinates (M : Matrix α β ℂ) (x : (α × β) × Bool) : ℝ :=
  if x.2 then (M x.1.1 x.1.2).re else (M x.1.1 x.1.2).im

theorem sum_hsCoordinates_sq [Fintype α] [Fintype β] (M : Matrix α β ℂ) :
    (∑ x : (α × β) × Bool, hsCoordinates M x ^ 2) = hsSq M := by
  simp [hsCoordinates, hsSq, Fintype.sum_prod_type,
    Complex.normSq_apply, pow_two]

theorem sum_hsCoordinates_mul [Fintype α] [Fintype β] (A B : Matrix α β ℂ) :
    (∑ x : (α × β) × Bool, hsCoordinates A x * hsCoordinates B x) =
      hsInner A B := by
  simp [hsCoordinates, hsInner, Fintype.sum_prod_type, Complex.mul_re]

theorem hsInner_sq_le [Fintype α] [Fintype β] (A B : Matrix α β ℂ) :
    hsInner A B ^ 2 ≤ hsSq A * hsSq B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset ((α × β) × Bool)) (hsCoordinates A) (hsCoordinates B)
  rw [sum_hsCoordinates_mul, sum_hsCoordinates_sq, sum_hsCoordinates_sq] at h
  exact h

theorem hsInner_comm [Fintype α] [Fintype β] (A B : Matrix α β ℂ) :
    hsInner A B = hsInner B A := by
  rw [← sum_hsCoordinates_mul, ← sum_hsCoordinates_mul]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem hsInner_eq_trace_conjTranspose_mul [Fintype α] [Fintype β]
    (A B : Matrix α β ℂ) : hsInner A B = (Matrix.trace (Aᴴ * B)).re := by
  simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  exact Finset.sum_comm

theorem hsInner_hermitian_eq_trace [Fintype α]
    (A B : Matrix α α ℂ) (hA : A.IsHermitian) :
    hsInner A B = (Matrix.trace (A * B)).re := by
  rw [hsInner_eq_trace_conjTranspose_mul, hA.eq]

theorem hsSq_conjTranspose [Fintype α] [Fintype β] (M : Matrix α β ℂ) :
    hsSq Mᴴ = hsSq M := by
  rw [hsSq_eq_trace_self_mul_conjTranspose, Matrix.conjTranspose_conjTranspose]
  exact (hsSq_eq_trace_conjTranspose_mul_self M).symm

theorem normSq_sum_complex [Fintype α] (z : α → ℂ) :
    ((Complex.normSq (∑ i, z i) : ℝ) : ℂ) = ∑ i, ∑ j, z i * star (z j) := by
  rw [← Complex.mul_conj]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.star_def]
  exact Finset.sum_comm

end QuantumProver.IsotropicFormation
