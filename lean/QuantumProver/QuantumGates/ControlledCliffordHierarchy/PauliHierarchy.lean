import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Two
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped Matrix

namespace QuantumProver.ControlledCliffordHierarchy
namespace BinaryUnipotent

variable {R : Type*} [Ring R] [CharP R 2]

theorem one_add_pow_two_pow (N : R) (h : ℕ) :
    (1 + N) ^ (2 ^ h) = 1 + N ^ (2 ^ h) := by
  simpa using add_pow_char_pow_of_commute 2 h (Commute.one_left N)

theorem one_add_pow_two_pow_eq_one_iff (N : R) (h : ℕ) :
    (1 + N) ^ (2 ^ h) = 1 ↔ N ^ (2 ^ h) = 0 := by
  rw [one_add_pow_two_pow]
  constructor
  · intro hpow
    have hcancel : (1 : R) + N ^ (2 ^ h) = 1 + 0 := by simpa using hpow
    exact add_left_cancel hcancel
  · intro hzero
    simp only [hzero, add_zero]

theorem one_add_pow_two_pow_ne_one (N : R) (h : ℕ)
    (hN : N ^ (2 ^ h) ≠ 0) : (1 + N) ^ (2 ^ h) ≠ 1 := by
  exact fun hpow => hN ((one_add_pow_two_pow_eq_one_iff N h).mp hpow)

theorem one_add_pow_two_pow_eq_one_of_nilpotent_bound
    (N : R) (d h : ℕ) (hzero : N ^ d = 0) (hbound : d ≤ 2 ^ h) :
    (1 + N) ^ (2 ^ h) = 1 := by
  apply (one_add_pow_two_pow_eq_one_iff N h).mpr
  exact pow_eq_zero_of_le hbound hzero

omit [CharP R 2] in

theorem pow_ne_zero_of_chain_endpoint
    (N : R) (d k : ℕ) (hendpoint : N ^ (d - 1) ≠ 0) (hk : k < d) :
    N ^ k ≠ 0 := by
  intro hzero
  apply hendpoint
  exact pow_eq_zero_of_le (Nat.le_sub_one_of_lt hk) hzero

theorem orderOf_one_add_of_nilpotency_interval
    (N : R) (d h : ℕ) (hzero : N ^ d = 0)
    (hendpoint : N ^ (d - 1) ≠ 0)
    (hlower : 2 ^ h < d) (hupper : d ≤ 2 ^ (h + 1)) :
    orderOf (1 + N) = 2 ^ (h + 1) := by
  apply orderOf_eq_prime_pow (p := 2) (n := h)
  · exact one_add_pow_two_pow_ne_one N h
      (pow_ne_zero_of_chain_endpoint N d (2 ^ h) hendpoint hlower)
  · exact one_add_pow_two_pow_eq_one_of_nilpotent_bound N d (h + 1) hzero hupper

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem binary_matrix_one_add_pow_two_pow
    (N : Matrix ι ι (ZMod 2)) (h : ℕ) :
    (1 + N) ^ (2 ^ h) = 1 + N ^ (2 ^ h) :=
  one_add_pow_two_pow N h

theorem binary_matrix_orderOf_one_add
    (N : Matrix ι ι (ZMod 2)) (d h : ℕ) (hzero : N ^ d = 0)
    (hendpoint : N ^ (d - 1) ≠ 0)
    (hlower : 2 ^ h < d) (hupper : d ≤ 2 ^ (h + 1)) :
    orderOf (1 + N) = 2 ^ (h + 1) :=
  orderOf_one_add_of_nilpotency_interval N d h hzero hendpoint hlower hupper

end Matrix

end BinaryUnipotent

namespace RegularChain

variable {R : Type*} [Semiring R]

theorem pow_entry_zero_before_diagonal {d : ℕ}
    (N : Matrix (Fin d) (Fin d) R)
    (htri : ∀ i j : Fin d, i.val ≤ j.val → N i j = 0) (k : ℕ) :
    ∀ i j : Fin d, i.val < j.val + k → (N ^ k) i j = 0 := by
  induction k with
  | zero =>
      intro i j hlt
      have hne : i ≠ j := by
        intro heq
        subst j
        omega
      simp [Matrix.one_apply, hne]
  | succ k ih =>
      intro i j hlt
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l hl
      by_cases hlj : l.val ≤ j.val
      · rw [htri l j hlj, mul_zero]
      · rw [ih i l (by omega), zero_mul]

theorem pow_entry_one_on_diagonal {d : ℕ}
    (N : Matrix (Fin d) (Fin d) R)
    (htri : ∀ i j : Fin d, i.val ≤ j.val → N i j = 0)
    (hstep : ∀ i j : Fin d, i.val = j.val + 1 → N i j = 1) (k : ℕ) :
    ∀ i j : Fin d, i.val = j.val + k → (N ^ k) i j = 1 := by
  induction k with
  | zero =>
      intro i j heq
      have hij : i = j := Fin.ext (by omega)
      subst j
      simp
  | succ k ih =>
      intro i j heq
      have hjnext : j.val + 1 < d := by
        have hi := i.isLt
        omega
      let l : Fin d := ⟨j.val + 1, hjnext⟩
      rw [pow_succ, Matrix.mul_apply]
      calc
        (∑ b : Fin d, (N ^ k) i b * N b j) = (N ^ k) i l * N l j := by
          apply Finset.sum_eq_single l
          · intro b hb hbl
            by_cases hbj : b.val ≤ j.val
            · rw [htri b j hbj, mul_zero]
            · have hbnext : b.val ≠ j.val + 1 := by
                intro hval
                apply hbl
                apply Fin.ext
                exact hval
              rw [pow_entry_zero_before_diagonal N htri k i b (by omega), zero_mul]
          · intro hl
            exact (hl (Finset.mem_univ l)).elim
        _ = 1 := by
          rw [ih i l (by dsimp [l]; omega), hstep l j rfl, mul_one]

theorem pow_dimension_eq_zero {d : ℕ}
    (N : Matrix (Fin d) (Fin d) R)
    (htri : ∀ i j : Fin d, i.val ≤ j.val → N i j = 0) : N ^ d = 0 := by
  apply Matrix.ext
  intro i j
  apply pow_entry_zero_before_diagonal N htri d i j
  have hi := i.isLt
  omega

theorem pow_dimension_sub_one_ne_zero [Nontrivial R] {d : ℕ} (hd : 0 < d)
    (N : Matrix (Fin d) (Fin d) R)
    (htri : ∀ i j : Fin d, i.val ≤ j.val → N i j = 0)
    (hstep : ∀ i j : Fin d, i.val = j.val + 1 → N i j = 1) :
    N ^ (d - 1) ≠ 0 := by
  let first : Fin d := ⟨0, hd⟩
  let last : Fin d := ⟨d - 1, by omega⟩
  have hentry := pow_entry_one_on_diagonal N htri hstep (d - 1) last first
    (by simp [first, last])
  intro hzero
  have hentryzero : (N ^ (d - 1)) last first = 0 := by rw [hzero]; rfl
  exact one_ne_zero (hentry.symm.trans hentryzero)

def twoStepMatrix {d : ℕ} (c : Fin d → R) : Matrix (Fin d) (Fin d) R :=
  fun i j => if i.val = j.val + 1 then 1 else if i.val = j.val + 2 then c j else 0

theorem twoStepMatrix_triangular {d : ℕ} (c : Fin d → R) :
    ∀ i j : Fin d, i.val ≤ j.val → twoStepMatrix c i j = 0 := by
  intro i j hle
  simp [twoStepMatrix, show i.val ≠ j.val + 1 by omega,
    show i.val ≠ j.val + 2 by omega]

theorem twoStepMatrix_adjacent {d : ℕ} (c : Fin d → R) :
    ∀ i j : Fin d, i.val = j.val + 1 → twoStepMatrix c i j = 1 := by
  intro i j heq
  simp [twoStepMatrix, heq]

theorem twoStepMatrix_nilpotency [Nontrivial R] {d : ℕ} (hd : 0 < d)
    (c : Fin d → R) :
    twoStepMatrix c ^ d = 0 ∧ twoStepMatrix c ^ (d - 1) ≠ 0 := by
  exact ⟨pow_dimension_eq_zero _ (twoStepMatrix_triangular c),
    pow_dimension_sub_one_ne_zero hd _ (twoStepMatrix_triangular c)
      (twoStepMatrix_adjacent c)⟩

end RegularChain

namespace PhysicalMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def involutionMatrix (f : ι → ι) : Matrix ι ι ℂ :=
  fun row col => if row = f col then 1 else 0

theorem involutionMatrix_adjoint (f : ι → ι) (hf : Function.Involutive f) :
    (involutionMatrix f).conjTranspose = involutionMatrix f := by
  ext row col
  have heq : col = f row ↔ row = f col := by
    constructor
    · intro h
      simpa only [h, hf] using (hf row).symm
    · intro h
      simpa only [h, hf] using (hf col).symm
  simp [involutionMatrix, Matrix.conjTranspose_apply, heq]

theorem involutionMatrix_square (f : ι → ι) (hf : Function.Involutive f) :
    involutionMatrix f * involutionMatrix f = 1 := by
  ext row col
  simp only [Matrix.mul_apply, involutionMatrix, mul_ite, mul_one, mul_zero]
  simp [hf col, Matrix.one_apply]

theorem involutionMatrix_mulVec (f : ι → ι) (hf : Function.Involutive f)
    (ψ : ι → ℂ) : involutionMatrix f *ᵥ ψ = fun row => ψ (f row) := by
  funext row
  have heq (col : ι) : row = f col ↔ col = f row := by
    constructor
    · intro h
      have := congrArg f h
      simpa only [hf col] using this.symm
    · intro h
      have := congrArg f h
      simpa only [hf row] using this.symm
  simp [Matrix.mulVec, dotProduct, involutionMatrix, heq]

theorem involutionMatrix_unitary (f : ι → ι) (hf : Function.Involutive f) :
    (involutionMatrix f).conjTranspose * involutionMatrix f = 1 ∧
      involutionMatrix f * (involutionMatrix f).conjTranspose = 1 := by
  rw [involutionMatrix_adjoint f hf]
  exact ⟨involutionMatrix_square f hf, involutionMatrix_square f hf⟩

theorem diagonal_adjoint (d : ι → ℂ) (hd : ∀ i, star (d i) = d i) :
    (Matrix.diagonal d).conjTranspose = Matrix.diagonal d := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  exact hd i

theorem diagonal_square (d : ι → ℂ) (hd : ∀ i, d i * d i = 1) :
    Matrix.diagonal d * Matrix.diagonal d = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply, hd i, Matrix.one_apply]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

end PhysicalMatrix
end QuantumProver.ControlledCliffordHierarchy
