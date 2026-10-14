import QuantumProver.InformationTheory.WernerEndpoint.ExteriorSupport

set_option autoImplicit false

noncomputable section

namespace QuantumProver.WernerEndpoint.WernerProductFactorization

open scoped BigOperators
open Matrix ExteriorSupport

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem tensor_normSq (x : X → ℂ) (y : Y → ℂ) :
    vectorNormSq (fun xy : X × Y => x xy.1 * y xy.2) =
      vectorNormSq x * vectorNormSq y := by
  simp only [vectorNormSq, Fintype.sum_prod_type, Complex.normSq_mul]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

private theorem mul_star_eq_normSq (z : ℂ) :
    z * star z = (Complex.normSq z : ℂ) := by
  simpa only [Complex.star_def] using Complex.mul_conj z

theorem pureDensity_purity (x : X → ℂ) :
    purity (pureDensity x) = vectorNormSq x ^ 2 := by
  have hterm (i j : X) :
      (x i * star (x j)) * (x j * star (x i)) =
        (Complex.normSq (x i) : ℂ) * (Complex.normSq (x j) : ℂ) := by
    rw [← mul_star_eq_normSq, ← mul_star_eq_normSq]
    ring
  simp only [purity, pureDensity, crossDensity, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, hterm, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp only [vectorNormSq, pow_two]

theorem partialTraceRight_tensor (x : X → ℂ) (y : Y → ℂ) :
    partialTraceRight (pureDensity (fun xy : X × Y => x xy.1 * y xy.2)) =
      (vectorNormSq x : ℂ) • pureDensity y := by
  ext i j
  change (∑ a, (x a * y i) * star (x a * y j)) =
    (vectorNormSq x : ℂ) * (y i * star (y j))
  simp only [star_mul]
  have hterm (a : X) :
      x a * y i * (star (y j) * star (x a)) =
        (Complex.normSq (x a) : ℂ) * (y i * star (y j)) := by
    rw [← mul_star_eq_normSq]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  simp [vectorNormSq]

theorem partialTraceLeft_tensor (x : X → ℂ) (y : Y → ℂ) :
    partialTraceLeft (pureDensity (fun xy : X × Y => x xy.1 * y xy.2)) =
      (vectorNormSq y : ℂ) • pureDensity x := by
  ext i j
  change (∑ a, (x i * y a) * star (x j * y a)) =
    (vectorNormSq y : ℂ) * (x i * star (x j))
  simp only [star_mul]
  have hterm (a : Y) :
      x i * y a * (star (y a) * star (x j)) =
        (Complex.normSq (y a) : ℂ) * (x i * star (x j)) := by
    rw [← mul_star_eq_normSq]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  simp [vectorNormSq]

private theorem hsNormSq_eq_zero_matrix {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℂ) (hA : hsNormSq A = 0) : A = 0 := by
  classical
  ext i j
  have hrow := Finset.single_le_sum
    (fun a (_ : a ∈ (Finset.univ : Finset I)) =>
      Finset.sum_nonneg (fun b (_ : b ∈ (Finset.univ : Finset J)) =>
        sq_nonneg ‖A a b‖)) (Finset.mem_univ i)
  have hentry := Finset.single_le_sum
    (fun b (_ : b ∈ (Finset.univ : Finset J)) => sq_nonneg ‖A i b‖)
    (Finset.mem_univ j)
  change (∑ b, ‖A i b‖ ^ 2) ≤ hsNormSq A at hrow
  rw [hA] at hrow
  have hn : ‖A i j‖ = 0 := by nlinarith [norm_nonneg (A i j)]
  exact norm_eq_zero.mp hn

theorem marginal_purity_left_eq_right (ψ : X × Y → ℂ) :
    purity (partialTraceLeft (pureDensity ψ)) =
      purity (partialTraceRight (pureDensity ψ)) := by
  have h := congrArg Complex.re
    (cross_square_trace_eq (fun x y => ψ (x, y)) (fun x y => ψ (x, y)))
  exact h

theorem marginal_purity_eq_one_iff_exists_product
    (ψ : X × Y → ℂ) (hψ : vectorNormSq ψ = 1) :
    purity (partialTraceRight (pureDensity ψ)) = 1 ↔
      ∃ x : X → ℂ, ∃ y : Y → ℂ,
        vectorNormSq x = 1 ∧ vectorNormSq y = 1 ∧
          ∀ xy : X × Y, ψ xy = x xy.1 * y xy.2 := by
  classical
  constructor
  · intro hp
    let A : Matrix Y X ℂ := fun y x => ψ (x, y)
    have hA : hsNormSq A = 1 := by
      calc
        hsNormSq A = vectorNormSq ψ := by
          simp only [hsNormSq, A, vectorNormSq, Fintype.sum_prod_type,
            Complex.sq_norm]
          exact Finset.sum_comm
        _ = 1 := hψ
    have hρ : reducedLeft A = partialTraceRight (pureDensity ψ) := rfl
    have hw : hsNormSq (orderedExterior A) = 0 := by
      rw [orderedExterior_hsNormSq_of_normalized A hA, hρ, hp]
      norm_num
    have hzero := hsNormSq_eq_zero_matrix (orderedExterior A) hw
    have hminor (x a : X) (y b : Y) :
        ψ (x, y) * ψ (a, b) = ψ (a, y) * ψ (x, b) := by
      have hz := congrFun (congrFun hzero (y, b)) (x, a)
      change (ψ (x, y) * ψ (a, b) - ψ (a, y) * ψ (x, b)) / 2 = 0 at hz
      have hm := (div_eq_zero_iff).mp hz
      exact sub_eq_zero.mp (hm.resolve_right (by norm_num))
    have hnonzero : ∃ xy : X × Y, ψ xy ≠ 0 := by
      by_contra h
      have hz : ψ = 0 := by
        funext xy
        exact not_not.mp (not_exists.mp h xy)
      have hn : vectorNormSq ψ = 0 := by simp [hz, vectorNormSq]
      linarith
    obtain ⟨⟨x0, y0⟩, hxy⟩ := hnonzero
    let u : X → ℂ := fun x => ψ (x, y0)
    let v : Y → ℂ := fun y => ψ (x0, y) / ψ (x0, y0)
    have hfactor : ∀ xy : X × Y, ψ xy = u xy.1 * v xy.2 := by
      rintro ⟨x, y⟩
      dsimp [u, v]
      rw [← mul_div_assoc]
      exact (eq_div_iff hxy).mpr (by
        rw [hminor x x0 y y0]
        ring)
    have hu0 : vectorNormSq u ≠ 0 := by
      intro hu
      have hz := matrix_vectorNormSq_eq_zero u hu
      exact hxy (congrFun hz x0)
    have hum := matrix_vectorNormSq_nonneg u
    have huPos : 0 < vectorNormSq u := lt_of_le_of_ne hum (Ne.symm hu0)
    have huv : vectorNormSq u * vectorNormSq v = 1 := by
      rw [← tensor_normSq]
      have heq : (fun xy : X × Y => u xy.1 * v xy.2) = ψ :=
        funext (fun xy => (hfactor xy).symm)
      rw [heq, hψ]
    let r : ℝ := Real.sqrt (vectorNormSq u)
    have hr0 : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr huPos)
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
    have hrMass : Complex.normSq (r : ℂ) = vectorNormSq u := by
      simp only [Complex.normSq_ofReal, ← sq]
      exact Real.sq_sqrt hum
    have hiMass : Complex.normSq ((r : ℂ)⁻¹) = (vectorNormSq u)⁻¹ := by
      rw [Complex.normSq_inv, hrMass]
    refine ⟨(r : ℂ)⁻¹ • u, (r : ℂ) • v, ?_, ?_, ?_⟩
    · rw [matrix_vectorNormSq_scalar, hiMass, inv_mul_cancel₀ hu0]
    · rw [matrix_vectorNormSq_scalar, hrMass, huv]
    · intro xy
      rw [hfactor xy]
      simp only [Pi.smul_apply, smul_eq_mul]
      calc
        u xy.1 * v xy.2 = ((r : ℂ)⁻¹ * (r : ℂ)) * (u xy.1 * v xy.2) := by
          rw [inv_mul_cancel₀ hrC, one_mul]
        _ = _ := by ring
  · rintro ⟨x, y, hx, hy, hprod⟩
    have heq : ψ = fun xy : X × Y => x xy.1 * y xy.2 := funext hprod
    rw [heq, partialTraceRight_tensor, hx]
    simp only [Complex.ofReal_one, one_smul]
    rw [pureDensity_purity, hy]
    norm_num

theorem left_marginal_purity_eq_one_iff_exists_product
    (ψ : X × Y → ℂ) (hψ : vectorNormSq ψ = 1) :
    purity (partialTraceLeft (pureDensity ψ)) = 1 ↔
      ∃ x : X → ℂ, ∃ y : Y → ℂ,
        vectorNormSq x = 1 ∧ vectorNormSq y = 1 ∧
          ∀ xy : X × Y, ψ xy = x xy.1 * y xy.2 := by
  rw [marginal_purity_left_eq_right]
  exact marginal_purity_eq_one_iff_exists_product ψ hψ

end QuantumProver.WernerEndpoint.WernerProductFactorization
