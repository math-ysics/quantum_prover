import Mathlib

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace QuantumProver.DepolarizingSquashedEntanglement

def c1LogCoth (x : ℝ) : ℝ :=
  if x = 1 then 2 else Real.log x * (x + 1) / (x - 1)

@[simp] theorem c1LogCoth_one : c1LogCoth 1 = 2 := by
  simp [c1LogCoth]

theorem c1LogCoth_eq {x : ℝ} (hx : 1 < x) :
    c1LogCoth x = Real.log x * (x + 1) / (x - 1) := by
  simp [c1LogCoth, ne_of_gt hx]

theorem c1LogCoth_decomposition {x : ℝ} (hx : 1 < x) :
    c1LogCoth x = Real.log x + 2 * Real.log x / (x - 1) := by
  rw [c1LogCoth_eq hx]
  have hne : x - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  field_simp
  ring

theorem c1LogCoth_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ c1LogCoth x := by
  by_cases heq : x = 1
  · simp [heq]
  · have hgt : 1 < x := lt_of_le_of_ne hx (Ne.symm heq)
    rw [c1LogCoth_eq hgt]
    exact div_nonneg (mul_nonneg (Real.log_nonneg hx) (by linarith)) (by linarith)

theorem c1LogCoth_le_log_add_two {x : ℝ} (hx : 1 < x) :
    c1LogCoth x ≤ Real.log x + 2 := by
  rw [c1LogCoth_decomposition hx]
  have hd : 0 < x - 1 := sub_pos.mpr hx
  have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hquot : Real.log x / (x - 1) ≤ 1 := (div_le_one hd).2 hlog
  have hscale : 2 * Real.log x / (x - 1) ≤ 2 := by
    simpa only [mul_div_assoc, mul_one] using
      mul_le_mul_of_nonneg_left hquot (by norm_num : (0:ℝ) ≤ 2)
  linarith

theorem c1_arcosh_half_le_log {m : ℝ} (hm : 2 ≤ m) :
    Real.arcosh (m / 2) ≤ Real.log m := by
  have hhalf : 0 ≤ m / 2 := by linarith
  have hsqrt : Real.sqrt ((m / 2)^2 - 1) ≤ m / 2 :=
    Real.sqrt_le_iff.mpr ⟨hhalf, by nlinarith⟩
  unfold Real.arcosh
  apply Real.log_le_log
  · positivity
  · linarith

def c1HsMass {I J : Type*} [Fintype I] [Fintype J] (Z : Matrix I J ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (Z i j)

theorem c1HsMass_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (Z : Matrix I J ℂ) : 0 ≤ c1HsMass Z := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact Complex.normSq_nonneg _

@[simp] theorem c1_star_mul_re_normSq (z : ℂ) :
    (star z * z).re = Complex.normSq z := by
  simp [Complex.mul_re, Complex.normSq_apply]

theorem c1_trace_gram {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (Z : Matrix I J ℂ) :
    (Matrix.trace (Zᴴ * Z)).re = c1HsMass Z := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [Complex.re_sum, c1_star_mul_re_normSq]
  exact Finset.sum_comm

theorem c1HsMass_conjTranspose {I J : Type*} [Fintype I] [Fintype J]
    (Z : Matrix I J ℂ) : c1HsMass Zᴴ = c1HsMass Z := by
  simp only [c1HsMass, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

theorem c1HsMass_fromBlocks {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (A : Matrix I K ℂ) (B : Matrix I L ℂ)
    (C : Matrix J K ℂ) (D : Matrix J L ℂ) :
    c1HsMass (Matrix.fromBlocks A B C D) =
      c1HsMass A + c1HsMass B + c1HsMass C + c1HsMass D := by
  simp only [c1HsMass, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  simp only [Finset.sum_add_distrib]
  ring

def c1Binary {I J : Type*} (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (Z : Matrix J I ℂ) : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.fromBlocks A Zᴴ Z B

theorem c1Binary_isHermitian {I J : Type*}
    {A : Matrix I I ℂ} {B : Matrix J J ℂ} (Z : Matrix J I ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (c1Binary A B Z).IsHermitian := by
  exact Matrix.IsHermitian.fromBlocks hA (by simp) hB

theorem c1Binary_square_blocks {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) (Z : Matrix J I ℂ) :
    c1Binary A B Z * c1Binary A B Z =
      Matrix.fromBlocks (A*A + Zᴴ*Z) (A*Zᴴ + Zᴴ*B)
        (Z*A + B*Z) (Z*Zᴴ + B*B) := by
  exact Matrix.fromBlocks_multiply _ _ _ _ _ _ _ _

theorem c1Binary_square_posSemidef {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {A : Matrix I I ℂ} {B : Matrix J J ℂ} (Z : Matrix J I ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (c1Binary A B Z * c1Binary A B Z).PosSemidef := by
  have hH := c1Binary_isHermitian Z hA hB
  simpa only [hH.eq] using Matrix.posSemidef_conjTranspose_mul_self (c1Binary A B Z)

theorem c1Binary_hs_mass {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) (Z : Matrix J I ℂ) :
    c1HsMass (c1Binary A B Z) = c1HsMass A + c1HsMass B + 2*c1HsMass Z := by
  unfold c1Binary
  rw [c1HsMass_fromBlocks, c1HsMass_conjTranspose]
  ring

theorem c1_two_noise_le_trace {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {A : Matrix I I ℂ} {B : Matrix J J ℂ} (Z : Matrix J I ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    2*(Matrix.trace (Zᴴ*Z)).re ≤
      (Matrix.trace (c1Binary A B Z * c1Binary A B Z)).re := by
  have hH := c1Binary_isHermitian Z hA hB
  have ht : (Matrix.trace (c1Binary A B Z * c1Binary A B Z)).re =
      c1HsMass (c1Binary A B Z) := by
    simpa only [hH.eq] using c1_trace_gram (c1Binary A B Z)
  rw [c1_trace_gram, ht, c1Binary_hs_mass]
  linarith [c1HsMass_nonneg A, c1HsMass_nonneg B]

theorem c1_oneWay_factor (δ : ℝ) :
    (4*δ/3)^2/(16*Real.log 2) = δ^2/(9*Real.log 2) := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  ring

end QuantumProver.DepolarizingSquashedEntanglement
