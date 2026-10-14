import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace QuantumProver.ElegantJointMeasurement.Concurrence

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix

noncomputable section

variable {s a b c : Type*}

def hsNormSq [Fintype a] [Fintype b] (M : Matrix a b ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

def purity [Fintype b] (ρ : Matrix b b ℂ) : ℝ :=
  (Matrix.trace (ρ * ρ)).re

def IsDensity [Fintype b] (ρ : Matrix b b ℂ) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

def iConcurrence [Fintype b] (ρ : Matrix b b ℂ) : ℝ :=
  Real.sqrt (2 * (1 - purity ρ))

section Scalar

variable [Fintype s]

theorem weighted_variance (w x : s → ℝ) (hsum : ∑ k, w k = 1) :
    ∑ k, w k * (x k - ∑ l, w l * x l) ^ 2 =
      ∑ k, w k * (x k) ^ 2 - (∑ k, w k * x k) ^ 2 := by
  let m := ∑ k, w k * x k
  change ∑ k, w k * (x k - m) ^ 2 = ∑ k, w k * x k ^ 2 - m ^ 2
  calc
    ∑ k, w k * (x k - m) ^ 2 =
        ∑ k, (w k * x k ^ 2 - (2 * m) * (w k * x k) + m ^ 2 * w k) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (∑ k, w k * x k ^ 2) - (2 * m) * (∑ k, w k * x k) +
        m ^ 2 * (∑ k, w k) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by rw [hsum]; change _ - 2 * m * m + m ^ 2 * 1 = _; ring

theorem weighted_square_le (w x : s → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hsum : ∑ k, w k = 1) :
    (∑ k, w k * x k) ^ 2 ≤ ∑ k, w k * (x k) ^ 2 := by
  have hvar : 0 ≤ ∑ k, w k * (x k - ∑ l, w l * x l) ^ 2 :=
    Finset.sum_nonneg (fun k hk => mul_nonneg (hw k) (sq_nonneg _))
  rw [weighted_variance w x hsum] at hvar
  linarith

theorem weighted_sqrt_le (w x : s → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hsum : ∑ k, w k = 1) (hx : ∀ k, 0 ≤ x k) :
    ∑ k, w k * Real.sqrt (x k) ≤ Real.sqrt (∑ k, w k * x k) := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := Finset.univ) (r := fun k => w k * Real.sqrt (x k))
    (f := w) (g := fun k => w k * x k)
    (fun k hk => hw k) (fun k hk => mul_nonneg (hw k) (hx k))
    (fun k hk => by rw [mul_pow, Real.sq_sqrt (hx k)]; nlinarith)
  rw [hsum, one_mul] at hcs
  exact Real.le_sqrt_of_sq_le hcs

end Scalar

section Matrices

variable [Fintype s] [Fintype b] [DecidableEq b]

theorem purity_eq_hsNormSq (ρ : Matrix b b ℂ) (hρ : ρ.IsHermitian) :
    purity ρ = hsNormSq ρ := by
  unfold purity hsNormSq
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← hρ.apply j i]
  simp [Complex.star_def, Complex.mul_re, Complex.normSq_apply]

theorem purity_transpose (ρ : Matrix b b ℂ) : purity ρᵀ = purity ρ := by
  unfold purity
  exact congrArg Complex.re (Matrix.trace_transpose_mul ρ ρ)

theorem iConcurrence_transpose (ρ : Matrix b b ℂ) :
    iConcurrence ρᵀ = iConcurrence ρ := by
  unfold iConcurrence
  rw [purity_transpose]

theorem hsNormSq_mixture_le (w : s → ℝ) (ρ : s → Matrix b b ℂ)
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1) :
    hsNormSq (∑ k, w k • ρ k) ≤ ∑ k, w k * hsNormSq (ρ k) := by
  have hentry (i j : b) :
      Complex.normSq ((∑ k, w k • ρ k) i j) ≤
        ∑ k, w k * Complex.normSq (ρ k i j) := by
    have hre := weighted_square_le w (fun k => (ρ k i j).re) hw hsum
    have him := weighted_square_le w (fun k => (ρ k i j).im) hw hsum
    simpa only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul,
      Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add,
      Complex.normSq_apply, pow_two, Finset.sum_add_distrib, mul_add,
      Finset.sum_const_zero, add_zero, mul_zero] using
      add_le_add hre him
  unfold hsNormSq
  calc
    ∑ i, ∑ j, Complex.normSq ((∑ k, w k • ρ k) i j) ≤
        ∑ i, ∑ j, ∑ k, w k * Complex.normSq (ρ k i j) := by
      exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hentry i j))
    _ = ∑ k, w k * ∑ i, ∑ j, Complex.normSq (ρ k i j) := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ i, ∑ k, ∑ j, w k * Complex.normSq (ρ k i j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]

theorem posSemidef_mixture (w : s → ℝ) (ρ : s → Matrix b b ℂ)
    (hw : ∀ k, 0 ≤ w k) (hρ : ∀ k, (ρ k).PosSemidef) :
    (∑ k, w k • ρ k).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact Finset.sum_nonneg (fun k hk => Matrix.nonneg_iff_posSemidef.mpr ((hρ k).smul (hw k)))

theorem density_mixture (w : s → ℝ) (ρ : s → Matrix b b ℂ)
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1)
    (hρ : ∀ k, IsDensity (ρ k)) : IsDensity (∑ k, w k • ρ k) := by
  constructor
  · exact posSemidef_mixture w ρ hw (fun k => (hρ k).1)
  · simp only [Matrix.trace_sum, Matrix.trace_smul, (hρ _).2,
      Complex.real_smul, mul_one]
    exact_mod_cast hsum

theorem purity_mixture_le_of_posSemidef (w : s → ℝ) (ρ : s → Matrix b b ℂ)
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1)
    (hρ : ∀ k, (ρ k).PosSemidef) :
    purity (∑ k, w k • ρ k) ≤ ∑ k, w k * purity (ρ k) := by
  rw [purity_eq_hsNormSq _ (posSemidef_mixture w ρ hw hρ).isHermitian]
  simp_rw [purity_eq_hsNormSq _ (hρ _).isHermitian]
  exact hsNormSq_mixture_le w ρ hw hsum

theorem purity_mixture_le (w : s → ℝ) (ρ : s → Matrix b b ℂ)
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1)
    (hρ : ∀ k, IsDensity (ρ k)) :
    purity (∑ k, w k • ρ k) ≤ ∑ k, w k * purity (ρ k) :=
  purity_mixture_le_of_posSemidef w ρ hw hsum (fun k => (hρ k).1)

theorem purity_eq_sum_eigenvalues_sq (ρ : Matrix b b ℂ) (hρ : ρ.IsHermitian) :
    purity ρ = ∑ i, hρ.eigenvalues i ^ 2 := by
  unfold purity
  conv_lhs => rw [hρ.spectral_theorem, ← map_mul]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  simp [Function.comp_apply, pow_two]

theorem density_purity_le_one (ρ : Matrix b b ℂ) (hρ : IsDensity ρ) :
    purity ρ ≤ 1 := by
  have hsum : ∑ i, hρ.1.isHermitian.eigenvalues i = 1 := by
    simpa using
      congrArg Complex.re (hρ.1.isHermitian.trace_eq_sum_eigenvalues.symm.trans hρ.2)
  rw [purity_eq_sum_eigenvalues_sq ρ hρ.1.isHermitian]
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := hρ.1.isHermitian.eigenvalues) (fun i hi => hρ.1.eigenvalues_nonneg i)
  simpa [hsum] using h

theorem iConcurrence_mixture_ge_of_posSemidef (w : s → ℝ) (ρ : s → Matrix b b ℂ)
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1)
    (hρ : ∀ k, (ρ k).PosSemidef) (hp : ∀ k, purity (ρ k) ≤ 1) :
    ∑ k, w k * iConcurrence (ρ k) ≤ iConcurrence (∑ k, w k • ρ k) := by
  unfold iConcurrence
  calc
    ∑ k, w k * Real.sqrt (2 * (1 - purity (ρ k))) ≤
        Real.sqrt (∑ k, w k * (2 * (1 - purity (ρ k)))) :=
      weighted_sqrt_le w _ hw hsum
        (fun k => mul_nonneg (by norm_num) (sub_nonneg.mpr (hp k)))
    _ ≤ Real.sqrt (2 * (1 - purity (∑ k, w k • ρ k))) := by
      apply Real.sqrt_le_sqrt
      have hmix := purity_mixture_le_of_posSemidef w ρ hw hsum hρ
      have heq : ∑ k, w k * (2 * (1 - purity (ρ k))) =
          2 * (1 - ∑ k, w k * purity (ρ k)) := by
        calc
          _ = ∑ k, (2 * w k - 2 * (w k * purity (ρ k))) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = 2 * (∑ k, w k) - 2 * (∑ k, w k * purity (ρ k)) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          _ = _ := by rw [hsum]; ring
      rw [heq]
      linarith

theorem iConcurrence_mixture_ge (w : s → ℝ) (ρ : s → Matrix b b ℂ)
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1)
    (hρ : ∀ k, IsDensity (ρ k)) :
    ∑ k, w k * iConcurrence (ρ k) ≤ iConcurrence (∑ k, w k • ρ k) :=
  iConcurrence_mixture_ge_of_posSemidef w ρ hw hsum
    (fun k => (hρ k).1) (fun k => density_purity_le_one _ (hρ k))

end Matrices

section Normalization

variable [Fintype b] [DecidableEq b]

theorem purity_real_smul (t : ℝ) (ρ : Matrix b b ℂ) :
    purity (t • ρ) = t ^ 2 * purity ρ := by
  simp only [purity, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

def probability (ρ : Matrix b b ℂ) : ℝ := (Matrix.trace ρ).re

def normalize (ρ : Matrix b b ℂ) : Matrix b b ℂ := (probability ρ)⁻¹ • ρ

theorem probability_nonneg (ρ : Matrix b b ℂ) (hρ : ρ.PosSemidef) :
    0 ≤ probability ρ := (Complex.nonneg_iff.mp hρ.trace_nonneg).1

theorem trace_eq_probability (ρ : Matrix b b ℂ) (hρ : ρ.PosSemidef) :
    Matrix.trace ρ = (probability ρ : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using (Complex.nonneg_iff.mp hρ.trace_nonneg).2.symm

theorem eq_zero_of_probability_zero (ρ : Matrix b b ℂ) (hρ : ρ.PosSemidef)
    (hp : probability ρ = 0) : ρ = 0 := by
  apply hρ.trace_eq_zero_iff.mp
  rw [trace_eq_probability ρ hρ, hp]
  norm_num

theorem normalize_posSemidef (ρ : Matrix b b ℂ) (hρ : ρ.PosSemidef) :
    (normalize ρ).PosSemidef := hρ.smul (inv_nonneg.mpr (probability_nonneg ρ hρ))

theorem normalize_density (ρ : Matrix b b ℂ) (hρ : ρ.PosSemidef)
    (hp : 0 < probability ρ) : IsDensity (normalize ρ) := by
  refine ⟨normalize_posSemidef ρ hρ, ?_⟩
  rw [normalize, Matrix.trace_smul, trace_eq_probability ρ hρ,
    Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hp.ne']
  norm_num

theorem normalize_eq_zero (ρ : Matrix b b ℂ) (hp : probability ρ = 0) :
    normalize ρ = 0 := by simp [normalize, hp]

theorem probability_smul_normalize (ρ : Matrix b b ℂ) (hρ : ρ.PosSemidef) :
    probability ρ • normalize ρ = ρ := by
  by_cases hp : probability ρ = 0
  · rw [hp, zero_smul, eq_zero_of_probability_zero ρ hρ hp]
  · rw [normalize, smul_smul, mul_inv_cancel₀ hp, one_smul]

theorem normalize_purity_le_one (ρ : Matrix b b ℂ) (hρ : ρ.PosSemidef) :
    purity (normalize ρ) ≤ 1 := by
  by_cases hp : probability ρ = 0
  · simp [normalize_eq_zero ρ hp, purity]
  · exact density_purity_le_one _ (normalize_density ρ hρ
      (lt_of_le_of_ne (probability_nonneg ρ hρ) (Ne.symm hp)))

theorem zero_probability_contribution (ρ : Matrix b b ℂ) (hp : probability ρ = 0) :
    probability ρ * iConcurrence (normalize ρ) = 0 := by rw [hp, zero_mul]

end Normalization

section Kraus

variable [Fintype s] [Fintype a] [Fintype b] [Fintype c]
variable [DecidableEq a] [DecidableEq b]

theorem purity_gram_swap (Ψ : Matrix a b ℂ) :
    purity (Ψᴴ * Ψ) = purity (Ψ * Ψᴴ) := by
  unfold purity
  apply congrArg Complex.re
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (Ψᴴ * Ψ * Ψᴴ) Ψ

theorem iConcurrence_gram_swap (Ψ : Matrix a b ℂ) :
    iConcurrence (Ψᴴ * Ψ) = iConcurrence (Ψ * Ψᴴ) := by
  unfold iConcurrence
  rw [purity_gram_swap Ψ]

theorem gram_transpose (Ψ : Matrix a b ℂ) :
    (Ψᵀ)ᴴ * Ψᵀ = (Ψ * Ψᴴ)ᵀ := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose]

theorem iConcurrence_gram_transpose (Ψ : Matrix a b ℂ) :
    iConcurrence ((Ψᵀ)ᴴ * Ψᵀ) = iConcurrence (Ψᴴ * Ψ) := by
  rw [gram_transpose, iConcurrence_transpose, ← iConcurrence_gram_swap Ψ]

theorem probability_gram_transpose (Ψ : Matrix a b ℂ) :
    probability ((Ψᵀ)ᴴ * Ψᵀ) = probability (Ψᴴ * Ψ) := by
  unfold probability
  rw [gram_transpose, Matrix.trace_transpose, Matrix.trace_mul_comm Ψ Ψᴴ]

theorem probability_gram_eq_hsNormSq (Ψ : Matrix a b ℂ) :
    probability (Ψᴴ * Ψ) = hsNormSq Ψ := by
  unfold probability hsNormSq
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  calc
    _ = ∑ i, ∑ j, Complex.normSq (Ψ j i) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp [Complex.star_def, Complex.mul_re, Complex.normSq_apply]
    _ = _ := by rw [Finset.sum_comm]

def branchReduction (Ψ : Matrix a b ℂ) (A : Matrix c a ℂ) : Matrix b b ℂ :=
  Ψᴴ * Aᴴ * A * Ψ

theorem branchReduction_eq_gram (Ψ : Matrix a b ℂ) (A : Matrix c a ℂ) :
    branchReduction Ψ A = (A * Ψ)ᴴ * (A * Ψ) := by
  simp [branchReduction, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem branchReduction_posSemidef (Ψ : Matrix a b ℂ) (A : Matrix c a ℂ) :
    (branchReduction Ψ A).PosSemidef := by
  rw [branchReduction_eq_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self (A * Ψ)

def normalizedCoefficient (Ψ : Matrix a b ℂ) (A : Matrix c a ℂ) : Matrix c b ℂ :=
  Real.sqrt ((probability (branchReduction Ψ A))⁻¹) • (A * Ψ)

theorem normalizedCoefficient_gram (Ψ : Matrix a b ℂ) (A : Matrix c a ℂ) :
    (normalizedCoefficient Ψ A)ᴴ * normalizedCoefficient Ψ A =
      normalize (branchReduction Ψ A) := by
  let q := Real.sqrt ((probability (branchReduction Ψ A))⁻¹)
  have hq : q * q = (probability (branchReduction Ψ A))⁻¹ := by
    simpa only [q, pow_two] using
      Real.sq_sqrt (inv_nonneg.mpr (probability_nonneg _ (branchReduction_posSemidef Ψ A)))
  change (q • (A * Ψ))ᴴ * (q • (A * Ψ)) =
    (probability (branchReduction Ψ A))⁻¹ • branchReduction Ψ A
  simp only [Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hq, ← branchReduction_eq_gram]

theorem normalizedCoefficient_trace_one (Ψ : Matrix a b ℂ) (A : Matrix c a ℂ)
    (hp : 0 < probability (branchReduction Ψ A)) :
    Matrix.trace ((normalizedCoefficient Ψ A)ᴴ * normalizedCoefficient Ψ A) = 1 := by
  rw [normalizedCoefficient_gram]
  exact (normalize_density _ (branchReduction_posSemidef Ψ A) hp).2

theorem normalizedCoefficient_zero (Ψ : Matrix a b ℂ) (A : Matrix c a ℂ)
    (hp : probability (branchReduction Ψ A) = 0) : normalizedCoefficient Ψ A = 0 := by
  simp [normalizedCoefficient, hp]

theorem complete_kraus_reduction_sum (Ψ : Matrix a b ℂ) (A : s → Matrix c a ℂ)
    (hcomplete : ∑ k, (A k)ᴴ * A k = 1) :
    ∑ k, branchReduction Ψ (A k) = Ψᴴ * Ψ := by
  calc
    ∑ k, branchReduction Ψ (A k) = Ψᴴ * (∑ k, (A k)ᴴ * A k) * Ψ := by
      simp [branchReduction, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
    _ = Ψᴴ * Ψ := by rw [hcomplete]; simp

theorem complete_kraus_probability_sum (Ψ : Matrix a b ℂ) (A : s → Matrix c a ℂ)
    (hnorm : Matrix.trace (Ψᴴ * Ψ) = 1)
    (hcomplete : ∑ k, (A k)ᴴ * A k = 1) :
    ∑ k, probability (branchReduction Ψ (A k)) = 1 := by
  simp only [probability, ← Complex.re_sum, ← Matrix.trace_sum,
    complete_kraus_reduction_sum Ψ A hcomplete, hnorm, Complex.one_re]

theorem complete_kraus_normalized_average (Ψ : Matrix a b ℂ) (A : s → Matrix c a ℂ)
    (hcomplete : ∑ k, (A k)ᴴ * A k = 1) :
    ∑ k, probability (branchReduction Ψ (A k)) • normalize (branchReduction Ψ (A k)) =
      Ψᴴ * Ψ := by
  simp_rw [probability_smul_normalize _ (branchReduction_posSemidef Ψ (A _))]
  exact complete_kraus_reduction_sum Ψ A hcomplete

theorem local_kraus_iConcurrence_monotone (Ψ : Matrix a b ℂ) (A : s → Matrix c a ℂ)
    (hnorm : Matrix.trace (Ψᴴ * Ψ) = 1)
    (hcomplete : ∑ k, (A k)ᴴ * A k = 1) :
    ∑ k, probability (branchReduction Ψ (A k)) *
      iConcurrence (normalize (branchReduction Ψ (A k))) ≤ iConcurrence (Ψᴴ * Ψ) := by
  have h := iConcurrence_mixture_ge_of_posSemidef
    (fun k => probability (branchReduction Ψ (A k)))
    (fun k => normalize (branchReduction Ψ (A k)))
    (fun k => probability_nonneg _ (branchReduction_posSemidef Ψ (A k)))
    (complete_kraus_probability_sum Ψ A hnorm hcomplete)
    (fun k => normalize_posSemidef _ (branchReduction_posSemidef Ψ (A k)))
    (fun k => normalize_purity_le_one _ (branchReduction_posSemidef Ψ (A k)))
  rwa [complete_kraus_normalized_average Ψ A hcomplete] at h

theorem local_kraus_pure_iConcurrence_monotone (Ψ : Matrix a b ℂ) (A : s → Matrix c a ℂ)
    (hnorm : Matrix.trace (Ψᴴ * Ψ) = 1)
    (hcomplete : ∑ k, (A k)ᴴ * A k = 1) :
    ∑ k, probability (branchReduction Ψ (A k)) *
      iConcurrence ((normalizedCoefficient Ψ (A k))ᴴ * normalizedCoefficient Ψ (A k)) ≤
        iConcurrence (Ψᴴ * Ψ) := by
  simp_rw [normalizedCoefficient_gram]
  exact local_kraus_iConcurrence_monotone Ψ A hnorm hcomplete

theorem right_normalizedCoefficient (Ψ : Matrix a b ℂ) (B : Matrix c b ℂ) :
    (normalizedCoefficient Ψᵀ B)ᵀ =
      Real.sqrt ((probability (branchReduction Ψᵀ B))⁻¹) • (Ψ * Bᵀ) := by
  simp [normalizedCoefficient, Matrix.transpose_mul]

theorem right_branch_probability (Ψ : Matrix a b ℂ) (B : Matrix c b ℂ) :
    probability (branchReduction Ψᵀ B) =
      probability ((Ψ * Bᵀ)ᴴ * (Ψ * Bᵀ)) := by
  classical
  rw [branchReduction_eq_gram]
  have hcoef : B * Ψᵀ = (Ψ * Bᵀ)ᵀ := by simp [Matrix.transpose_mul]
  rw [hcoef, probability_gram_transpose]

theorem right_local_kraus_pure_iConcurrence_monotone
    (Ψ : Matrix a b ℂ) (B : s → Matrix c b ℂ)
    (hnorm : Matrix.trace (Ψᴴ * Ψ) = 1)
    (hcomplete : ∑ k, (B k)ᴴ * B k = 1) :
    ∑ k, probability (branchReduction Ψᵀ (B k)) *
      iConcurrence (((normalizedCoefficient Ψᵀ (B k))ᵀ)ᴴ *
        (normalizedCoefficient Ψᵀ (B k))ᵀ) ≤ iConcurrence (Ψᴴ * Ψ) := by
  classical
  have hnorm' : Matrix.trace ((Ψᵀ)ᴴ * Ψᵀ) = 1 := by
    rw [trace_eq_probability _ (Matrix.posSemidef_conjTranspose_mul_self Ψᵀ),
      probability_gram_transpose]
    simp [probability, hnorm]
  have h := local_kraus_pure_iConcurrence_monotone Ψᵀ B hnorm' hcomplete
  simp_rw [iConcurrence_gram_transpose]
  rwa [iConcurrence_gram_transpose] at h

end Kraus

section Homogeneous

variable [Fintype s] [Fintype a] [Fintype b] [Fintype c]
variable [DecidableEq a] [DecidableEq b]

def densityBudget (ρ : Matrix b b ℂ) : ℝ :=
  probability ρ * iConcurrence (normalize ρ)

def homogeneousBudget (Ψ : Matrix a b ℂ) : ℝ := densityBudget (Ψᴴ * Ψ)

theorem probability_sum (ρ : s → Matrix b b ℂ) :
    probability (∑ k, ρ k) = ∑ k, probability (ρ k) := by
  simp [probability, Matrix.trace_sum, Complex.re_sum]

theorem densityBudget_zero : densityBudget (0 : Matrix b b ℂ) = 0 := by
  simp [densityBudget, probability]

theorem homogeneousBudget_zero : homogeneousBudget (0 : Matrix a b ℂ) = 0 := by
  simp [homogeneousBudget, densityBudget_zero]

theorem homogeneousBudget_nonneg (Ψ : Matrix a b ℂ) : 0 ≤ homogeneousBudget Ψ :=
  mul_nonneg (probability_nonneg _ (Matrix.posSemidef_conjTranspose_mul_self Ψ))
    (Real.sqrt_nonneg _)

theorem homogeneousBudget_of_normalized (Ψ : Matrix a b ℂ)
    (hnorm : Matrix.trace (Ψᴴ * Ψ) = 1) :
    homogeneousBudget Ψ = iConcurrence (Ψᴴ * Ψ) := by
  simp [homogeneousBudget, densityBudget, normalize, probability, hnorm]

theorem probability_real_smul (t : ℝ) (ρ : Matrix b b ℂ) :
    probability (t • ρ) = t * probability ρ := by
  simp only [probability, Matrix.trace_smul, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem densityBudget_sq (ρ : Matrix b b ℂ) (hρ : ρ.PosSemidef) :
    densityBudget ρ ^ 2 = 2 * (probability ρ ^ 2 - purity ρ) := by
  by_cases hp : probability ρ = 0
  · rw [eq_zero_of_probability_zero ρ hρ hp]
    simp [densityBudget, probability, purity]
  · have hc : iConcurrence (normalize ρ) ^ 2 = 2 * (1 - purity (normalize ρ)) :=
      Real.sq_sqrt (mul_nonneg (by norm_num) (sub_nonneg.mpr (normalize_purity_le_one ρ hρ)))
    rw [densityBudget, mul_pow, hc, normalize, purity_real_smul]
    field_simp [hp]
    <;> ring

theorem densityBudget_eq_sqrt (ρ : Matrix b b ℂ) (hρ : ρ.PosSemidef) :
    densityBudget ρ = Real.sqrt (2 * (probability ρ ^ 2 - purity ρ)) := by
  have hn : 0 ≤ densityBudget ρ :=
    mul_nonneg (probability_nonneg ρ hρ) (Real.sqrt_nonneg _)
  rw [← densityBudget_sq ρ hρ, Real.sqrt_sq hn]

theorem homogeneousBudget_eq_sqrt (Ψ : Matrix a b ℂ) :
    homogeneousBudget Ψ = Real.sqrt (2 * (probability (Ψᴴ * Ψ) ^ 2 - purity (Ψᴴ * Ψ))) :=
  densityBudget_eq_sqrt _ (Matrix.posSemidef_conjTranspose_mul_self Ψ)

theorem gram_real_smul (t : ℝ) (Ψ : Matrix a b ℂ) :
    (t • Ψ)ᴴ * (t • Ψ) = t ^ 2 • (Ψᴴ * Ψ) := by
  simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, pow_two]

theorem homogeneousBudget_real_smul (t : ℝ) (Ψ : Matrix a b ℂ) :
    homogeneousBudget (t • Ψ) = t ^ 2 * homogeneousBudget Ψ := by
  have hsq : homogeneousBudget (t • Ψ) ^ 2 = (t ^ 2 * homogeneousBudget Ψ) ^ 2 := by
    change densityBudget ((t • Ψ)ᴴ * (t • Ψ)) ^ 2 = _
    rw [densityBudget_sq _ (Matrix.posSemidef_conjTranspose_mul_self _), gram_real_smul,
      probability_real_smul, purity_real_smul]
    simp only [mul_pow]
    change _ = (t ^ 2) ^ 2 * densityBudget (Ψᴴ * Ψ) ^ 2
    rw [densityBudget_sq _ (Matrix.posSemidef_conjTranspose_mul_self Ψ)]
    ring
  exact (sq_eq_sq₀ (homogeneousBudget_nonneg _) (mul_nonneg (sq_nonneg t)
    (homogeneousBudget_nonneg Ψ))).mp hsq

theorem probability_gram_swap (Ψ : Matrix a b ℂ) :
    probability (Ψ * Ψᴴ) = probability (Ψᴴ * Ψ) := by
  unfold probability
  exact congrArg Complex.re (Matrix.trace_mul_comm Ψ Ψᴴ)

theorem homogeneousBudget_conjTranspose (Ψ : Matrix a b ℂ) :
    homogeneousBudget Ψᴴ = homogeneousBudget Ψ := by
  rw [homogeneousBudget_eq_sqrt, homogeneousBudget_eq_sqrt, Matrix.conjTranspose_conjTranspose,
    probability_gram_swap, ← purity_gram_swap Ψ]

theorem densityBudget_sum_le (ρ : s → Matrix b b ℂ)
    (hρ : ∀ k, (ρ k).PosSemidef) :
    ∑ k, densityBudget (ρ k) ≤ densityBudget (∑ k, ρ k) := by
  have htotal : (∑ k, ρ k).PosSemidef := by
    simpa using posSemidef_mixture (fun _ : s => (1 : ℝ)) ρ (fun _ => by norm_num) hρ
  let p := probability (∑ k, ρ k)
  have hp0 : 0 ≤ p := probability_nonneg _ htotal
  have hpsum : ∑ k, probability (ρ k) = p := (probability_sum ρ).symm
  change ∑ k, probability (ρ k) * iConcurrence (normalize (ρ k)) ≤
    p * iConcurrence (normalize (∑ k, ρ k))
  by_cases hp : p = 0
  · have hs0 : ∑ k, probability (ρ k) = 0 := hpsum.trans hp
    have hk0 (k : s) : probability (ρ k) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => probability_nonneg _ (hρ j))).mp hs0 k (Finset.mem_univ k)
    simp [hk0, hp]
  · let w : s → ℝ := fun k => probability (ρ k) / p
    have hw (k : s) : 0 ≤ w k := div_nonneg (probability_nonneg _ (hρ k)) hp0
    have hwsum : ∑ k, w k = 1 := by
      simp only [w, ← Finset.sum_div]
      rw [hpsum, div_self hp]
    have havg : ∑ k, w k • normalize (ρ k) = normalize (∑ k, ρ k) := by
      change ∑ k, w k • normalize (ρ k) = p⁻¹ • ∑ k, ρ k
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      calc
        w k • normalize (ρ k) = (p⁻¹ * probability (ρ k)) • normalize (ρ k) := by
          congr 1
          dsimp [w]
          rw [div_eq_mul_inv, mul_comm]
        _ = p⁻¹ • (probability (ρ k) • normalize (ρ k)) := (smul_smul _ _ _).symm
        _ = p⁻¹ • ρ k := by rw [probability_smul_normalize _ (hρ k)]
    have hc := iConcurrence_mixture_ge_of_posSemidef w (fun k => normalize (ρ k)) hw hwsum
      (fun k => normalize_posSemidef _ (hρ k)) (fun k => normalize_purity_le_one _ (hρ k))
    rw [havg] at hc
    calc
      ∑ k, probability (ρ k) * iConcurrence (normalize (ρ k)) =
          p * (∑ k, w k * iConcurrence (normalize (ρ k))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [w]
        field_simp [hp]
        <;> ring
      _ ≤ p * iConcurrence (normalize (∑ k, ρ k)) := mul_le_mul_of_nonneg_left hc hp0

theorem homogeneousBudget_transpose (Ψ : Matrix a b ℂ) :
    homogeneousBudget Ψᵀ = homogeneousBudget Ψ := by
  unfold homogeneousBudget densityBudget iConcurrence normalize
  simp_rw [probability_gram_transpose, purity_real_smul]
  rw [gram_transpose, purity_transpose, ← purity_gram_swap Ψ]

theorem homogeneousBudget_conjugate (Ψ : Matrix a b ℂ) :
    homogeneousBudget (Ψ.map conj) = homogeneousBudget Ψ := by
  have hmap : (Ψᴴ)ᵀ = Ψ.map conj := by
    rfl
  rw [← hmap, homogeneousBudget_transpose, homogeneousBudget_conjTranspose]

theorem left_kraus_homogeneousBudget_le (Ψ : Matrix a b ℂ) (A : s → Matrix c a ℂ)
    (hcomplete : ∑ k, (A k)ᴴ * A k = 1) :
    ∑ k, homogeneousBudget (A k * Ψ) ≤ homogeneousBudget Ψ := by
  classical
  have h := densityBudget_sum_le (fun k => branchReduction Ψ (A k))
    (fun k => branchReduction_posSemidef Ψ (A k))
  rw [complete_kraus_reduction_sum Ψ A hcomplete] at h
  simpa only [homogeneousBudget, branchReduction_eq_gram] using h

theorem right_kraus_homogeneousBudget_le (Ψ : Matrix a b ℂ) (B : s → Matrix c b ℂ)
    (hcomplete : ∑ k, (B k)ᴴ * B k = 1) :
    ∑ k, homogeneousBudget (Ψ * (B k)ᵀ) ≤ homogeneousBudget Ψ := by
  classical
  have h := left_kraus_homogeneousBudget_le Ψᵀ B hcomplete
  have hcoef (k : s) : B k * Ψᵀ = (Ψ * (B k)ᵀ)ᵀ := by simp [Matrix.transpose_mul]
  simp_rw [hcoef, homogeneousBudget_transpose] at h
  exact h

theorem left_kraus_probability_sum (Ψ : Matrix a b ℂ) (A : s → Matrix c a ℂ)
    (hcomplete : ∑ k, (A k)ᴴ * A k = 1) :
    ∑ k, probability ((A k * Ψ)ᴴ * (A k * Ψ)) = probability (Ψᴴ * Ψ) := by
  have h := congrArg probability (complete_kraus_reduction_sum Ψ A hcomplete)
  rw [probability_sum] at h
  simpa only [branchReduction_eq_gram] using h

theorem right_kraus_probability_sum (Ψ : Matrix a b ℂ) (B : s → Matrix c b ℂ)
    (hcomplete : ∑ k, (B k)ᴴ * B k = 1) :
    ∑ k, probability ((Ψ * (B k)ᵀ)ᴴ * (Ψ * (B k)ᵀ)) = probability (Ψᴴ * Ψ) := by
  classical
  have h := left_kraus_probability_sum Ψᵀ B hcomplete
  have hcoef (k : s) : B k * Ψᵀ = (Ψ * (B k)ᵀ)ᵀ := by simp [Matrix.transpose_mul]
  simp_rw [hcoef, probability_gram_transpose] at h
  exact h

end Homogeneous

structure RawPureBranch where
  aliceDim : ℕ
  bobDim : ℕ
  coefficient : Matrix (Fin aliceDim) (Fin bobDim) ℂ

namespace RawPureBranch

def mass (q : RawPureBranch) : ℝ := probability (q.coefficientᴴ * q.coefficient)
def budget (q : RawPureBranch) : ℝ := homogeneousBudget q.coefficient

theorem mass_nonneg (q : RawPureBranch) : 0 ≤ q.mass :=
  probability_nonneg _ (Matrix.posSemidef_conjTranspose_mul_self q.coefficient)

theorem budget_nonneg (q : RawPureBranch) : 0 ≤ q.budget :=
  homogeneousBudget_nonneg q.coefficient

end RawPureBranch

inductive FiniteLocalKrausTree : ℕ → ℕ → Type where
  | leaf (m n : ℕ) : FiniteLocalKrausTree m n
  | alice (m n out outcomes : ℕ)
      (A : Fin outcomes → Matrix (Fin out) (Fin m) ℂ)
      (complete : ∑ k, (A k)ᴴ * A k = 1)
      (next : Fin outcomes → FiniteLocalKrausTree out n) : FiniteLocalKrausTree m n
  | bob (m n out outcomes : ℕ)
      (B : Fin outcomes → Matrix (Fin out) (Fin n) ℂ)
      (complete : ∑ k, (B k)ᴴ * B k = 1)
      (next : Fin outcomes → FiniteLocalKrausTree m out) : FiniteLocalKrausTree m n

namespace FiniteLocalKrausTree

def terminalBranches : {m n : ℕ} → FiniteLocalKrausTree m n →
    Matrix (Fin m) (Fin n) ℂ → List RawPureBranch
  | _, _, .leaf m n, Ψ => [⟨m, n, Ψ⟩]
  | _, _, .alice m n out outcomes A complete next, Ψ =>
      (List.ofFn fun k : Fin outcomes => terminalBranches (next k) (A k * Ψ)).flatten
  | _, _, .bob m n out outcomes B complete next, Ψ =>
      (List.ofFn fun k : Fin outcomes => terminalBranches (next k) (Ψ * (B k)ᵀ)).flatten

def terminalBudget {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (Ψ : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ((T.terminalBranches Ψ).map RawPureBranch.budget).sum

def terminalMass {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (Ψ : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ((T.terminalBranches Ψ).map RawPureBranch.mass).sum

@[simp] theorem terminalBudget_leaf (m n : ℕ) (Ψ : Matrix (Fin m) (Fin n) ℂ) :
    terminalBudget (.leaf m n) Ψ = homogeneousBudget Ψ := by
  simp [terminalBudget, terminalBranches, RawPureBranch.budget]

@[simp] theorem terminalMass_leaf (m n : ℕ) (Ψ : Matrix (Fin m) (Fin n) ℂ) :
    terminalMass (.leaf m n) Ψ = probability (Ψᴴ * Ψ) := by
  simp [terminalMass, terminalBranches, RawPureBranch.mass]

theorem terminalBudget_alice (m n out outcomes : ℕ)
    (A : Fin outcomes → Matrix (Fin out) (Fin m) ℂ)
    (complete : ∑ k, (A k)ᴴ * A k = 1)
    (next : Fin outcomes → FiniteLocalKrausTree out n)
    (Ψ : Matrix (Fin m) (Fin n) ℂ) :
    terminalBudget (.alice m n out outcomes A complete next) Ψ =
      ∑ k, terminalBudget (next k) (A k * Ψ) := by
  simp [terminalBudget, terminalBranches, List.map_flatten, List.sum_flatten,
    List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem terminalBudget_bob (m n out outcomes : ℕ)
    (B : Fin outcomes → Matrix (Fin out) (Fin n) ℂ)
    (complete : ∑ k, (B k)ᴴ * B k = 1)
    (next : Fin outcomes → FiniteLocalKrausTree m out)
    (Ψ : Matrix (Fin m) (Fin n) ℂ) :
    terminalBudget (.bob m n out outcomes B complete next) Ψ =
      ∑ k, terminalBudget (next k) (Ψ * (B k)ᵀ) := by
  simp [terminalBudget, terminalBranches, List.map_flatten, List.sum_flatten,
    List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem terminalMass_alice (m n out outcomes : ℕ)
    (A : Fin outcomes → Matrix (Fin out) (Fin m) ℂ)
    (complete : ∑ k, (A k)ᴴ * A k = 1)
    (next : Fin outcomes → FiniteLocalKrausTree out n)
    (Ψ : Matrix (Fin m) (Fin n) ℂ) :
    terminalMass (.alice m n out outcomes A complete next) Ψ =
      ∑ k, terminalMass (next k) (A k * Ψ) := by
  simp [terminalMass, terminalBranches, List.map_flatten, List.sum_flatten,
    List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem terminalMass_bob (m n out outcomes : ℕ)
    (B : Fin outcomes → Matrix (Fin out) (Fin n) ℂ)
    (complete : ∑ k, (B k)ᴴ * B k = 1)
    (next : Fin outcomes → FiniteLocalKrausTree m out)
    (Ψ : Matrix (Fin m) (Fin n) ℂ) :
    terminalMass (.bob m n out outcomes B complete next) Ψ =
      ∑ k, terminalMass (next k) (Ψ * (B k)ᵀ) := by
  simp [terminalMass, terminalBranches, List.map_flatten, List.sum_flatten,
    List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem terminalBudget_le {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (Ψ : Matrix (Fin m) (Fin n) ℂ) : T.terminalBudget Ψ ≤ homogeneousBudget Ψ := by
  induction T with
  | leaf m n => simp
  | alice m n out outcomes A complete next ih =>
    rw [terminalBudget_alice]
    calc
      ∑ k, terminalBudget (next k) (A k * Ψ) ≤ ∑ k, homogeneousBudget (A k * Ψ) := by
        exact Finset.sum_le_sum (fun k hk => ih k (A k * Ψ))
      _ ≤ homogeneousBudget Ψ := left_kraus_homogeneousBudget_le Ψ A complete
  | bob m n out outcomes B complete next ih =>
    rw [terminalBudget_bob]
    calc
      ∑ k, terminalBudget (next k) (Ψ * (B k)ᵀ) ≤ ∑ k, homogeneousBudget (Ψ * (B k)ᵀ) := by
        exact Finset.sum_le_sum (fun k hk => ih k (Ψ * (B k)ᵀ))
      _ ≤ homogeneousBudget Ψ := right_kraus_homogeneousBudget_le Ψ B complete

theorem terminalMass_eq {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (Ψ : Matrix (Fin m) (Fin n) ℂ) : T.terminalMass Ψ = probability (Ψᴴ * Ψ) := by
  induction T with
  | leaf m n => simp
  | alice m n out outcomes A complete next ih =>
    rw [terminalMass_alice]
    simp_rw [ih]
    exact left_kraus_probability_sum Ψ A complete
  | bob m n out outcomes B complete next ih =>
    rw [terminalMass_bob]
    simp_rw [ih]
    exact right_kraus_probability_sum Ψ B complete

theorem terminalMass_eq_one {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (Ψ : Matrix (Fin m) (Fin n) ℂ) (hnorm : Matrix.trace (Ψᴴ * Ψ) = 1) :
    T.terminalMass Ψ = 1 := by rw [terminalMass_eq]; simp [probability, hnorm]

theorem terminal_average_iConcurrence_le {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (Ψ : Matrix (Fin m) (Fin n) ℂ) (hnorm : Matrix.trace (Ψᴴ * Ψ) = 1) :
    ((T.terminalBranches Ψ).map fun q => q.mass *
      iConcurrence (normalize (q.coefficientᴴ * q.coefficient))).sum ≤
        iConcurrence (Ψᴴ * Ψ) := by
  change T.terminalBudget Ψ ≤ iConcurrence (Ψᴴ * Ψ)
  rw [← homogeneousBudget_of_normalized Ψ hnorm]
  exact T.terminalBudget_le Ψ

end FiniteLocalKrausTree

section TwoQubits

theorem trace_square_fin_two {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) :
    Matrix.trace (M * M) = (Matrix.trace M) ^ 2 - 2 * Matrix.det M := by
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.det_fin_two]
  ring

theorem purity_gram_fin_two (M : Matrix (Fin 2) (Fin 2) ℂ) :
    purity (Mᴴ * M) = probability (Mᴴ * M) ^ 2 - 2 * ‖Matrix.det M‖ ^ 2 := by
  have hM := Matrix.posSemidef_conjTranspose_mul_self M
  have hdet : Matrix.det (Mᴴ * M) = ((‖Matrix.det M‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  unfold purity
  rw [trace_square_fin_two, trace_eq_probability _ hM, hdet]
  simp [pow_two, Complex.mul_re]

theorem probability_mul_iConcurrence_eq_two_det (M : Matrix (Fin 2) (Fin 2) ℂ) :
    probability (Mᴴ * M) * iConcurrence (normalize (Mᴴ * M)) = 2 * ‖Matrix.det M‖ := by
  let p := probability (Mᴴ * M)
  have hM := Matrix.posSemidef_conjTranspose_mul_self M
  have hp0 : 0 ≤ p := probability_nonneg _ hM
  change p * iConcurrence (normalize (Mᴴ * M)) = 2 * ‖Matrix.det M‖
  by_cases hp : p = 0
  · have htrace : Matrix.trace (Mᴴ * M) = 0 := by
      rw [trace_eq_probability _ hM]
      change (p : ℂ) = 0
      rw [hp]
      norm_num
    have hzero : M = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htrace
    simp [hp, hzero]
  · have hc : iConcurrence (normalize (Mᴴ * M)) ^ 2 =
        2 * (1 - purity (normalize (Mᴴ * M))) :=
      Real.sq_sqrt (mul_nonneg (by norm_num)
        (sub_nonneg.mpr (normalize_purity_le_one _ hM)))
    have hsq : (p * iConcurrence (normalize (Mᴴ * M))) ^ 2 =
        (2 * ‖Matrix.det M‖) ^ 2 := by
      rw [mul_pow, hc]
      change p ^ 2 * (2 * (1 - purity (p⁻¹ • (Mᴴ * M)))) = _
      rw [purity_real_smul, purity_gram_fin_two]
      change p ^ 2 * (2 * (1 - p⁻¹ ^ 2 * (p ^ 2 - 2 * ‖Matrix.det M‖ ^ 2))) = _
      field_simp [hp]
      <;> ring
    exact (sq_eq_sq₀
      (mul_nonneg hp0 (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num) (norm_nonneg _))).mp hsq

theorem homogeneousBudget_fin_two (M : Matrix (Fin 2) (Fin 2) ℂ) :
    homogeneousBudget M = 2 * ‖Matrix.det M‖ := probability_mul_iConcurrence_eq_two_det M

theorem reference_tail_budget (T : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) (ht : 0 < t) :
    homogeneousBudget ((2 * Real.sqrt t)⁻¹ • T.map conj) = ‖Matrix.det T‖ / (2 * t) := by
  rw [homogeneousBudget_real_smul, homogeneousBudget_conjugate, homogeneousBudget_fin_two,
    inv_pow, mul_pow, Real.sq_sqrt ht.le]
  norm_num
  field_simp [ht.ne']
  <;> ring

end TwoQubits

section Transport

variable {a' b' c' : Type*}
variable [Fintype a] [Fintype b] [Fintype c] [Fintype a'] [Fintype b'] [Fintype c']
variable [DecidableEq a] [DecidableEq b] [DecidableEq a'] [DecidableEq b']

theorem reindex_mul_equiv (ea : a ≃ a') (eb : b ≃ b') (ec : c ≃ c')
    (M : Matrix a b ℂ) (N : Matrix b c ℂ) :
    Matrix.reindex ea eb M * Matrix.reindex eb ec N = Matrix.reindex ea ec (M * N) :=
  Matrix.submatrix_mul_equiv M N ea.symm eb.symm ec.symm

theorem trace_reindex_equiv (eb : b ≃ b') (ρ : Matrix b b ℂ) :
    Matrix.trace (Matrix.reindex eb eb ρ) = Matrix.trace ρ := by
  simpa [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply] using
    eb.symm.sum_comp (fun i => ρ i i)

theorem probability_reindex_equiv (eb : b ≃ b') (ρ : Matrix b b ℂ) :
    probability (Matrix.reindex eb eb ρ) = probability ρ := by
  unfold probability
  rw [trace_reindex_equiv]

theorem purity_reindex_equiv (eb : b ≃ b') (ρ : Matrix b b ℂ) :
    purity (Matrix.reindex eb eb ρ) = purity ρ := by
  unfold purity
  rw [reindex_mul_equiv, trace_reindex_equiv]

theorem homogeneousBudget_reindex_equiv (ea : a ≃ a') (eb : b ≃ b')
    (Ψ : Matrix a b ℂ) : homogeneousBudget (Matrix.reindex ea eb Ψ) = homogeneousBudget Ψ := by
  rw [homogeneousBudget_eq_sqrt, homogeneousBudget_eq_sqrt, Matrix.conjTranspose_reindex,
    reindex_mul_equiv, probability_reindex_equiv, purity_reindex_equiv]

theorem terminalBudget_le_at_finite_indices
    (T : FiniteLocalKrausTree (Fintype.card a) (Fintype.card b)) (Ψ : Matrix a b ℂ) :
    T.terminalBudget (Matrix.reindex (Fintype.equivFin a) (Fintype.equivFin b) Ψ) ≤
      homogeneousBudget Ψ := by
  simpa only [homogeneousBudget_reindex_equiv] using
    T.terminalBudget_le (Matrix.reindex (Fintype.equivFin a) (Fintype.equivFin b) Ψ)

end Transport

section LocalReference

open scoped Kronecker

variable {κ p q : Type*} [Fintype κ] [DecidableEq κ]
variable [Fintype a] [Fintype b] [Fintype p] [Fintype q]
variable [DecidableEq a] [DecidableEq b] [DecidableEq p] [DecidableEq q]

theorem homogeneousBudget_local_pure_ancillas (Ψ : Matrix a b ℂ) (u : p → ℂ) (v : q → ℂ)
    (hu : star u ⬝ᵥ u = 1) (hv : star v ⬝ᵥ v = 1) :
    homogeneousBudget (Ψ ⊗ₖ Matrix.vecMulVec u v) = homogeneousBudget Ψ := by
  let R := Matrix.vecMulVec (star v) v
  have hg : (Matrix.vecMulVec u v)ᴴ * Matrix.vecMulVec u v = R := by
    rw [Matrix.conjTranspose_vecMulVec, Matrix.vecMulVec_mul_vecMulVec, hu]
    simp [R]
  have htr : Matrix.trace R = 1 := by simpa [R] using hv
  have hr : R * R = R := by
    dsimp [R]
    rw [Matrix.vecMulVec_mul_vecMulVec, dotProduct_comm v (star v), hv]
    simp
  have hgram : (Ψ ⊗ₖ Matrix.vecMulVec u v)ᴴ * (Ψ ⊗ₖ Matrix.vecMulVec u v) =
      (Ψᴴ * Ψ) ⊗ₖ R := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hg]
  have ht : Matrix.trace ((Ψ ⊗ₖ Matrix.vecMulVec u v)ᴴ *
      (Ψ ⊗ₖ Matrix.vecMulVec u v)) = Matrix.trace (Ψᴴ * Ψ) := by
    rw [hgram, Matrix.trace_kronecker, htr, mul_one]
  have htsq : Matrix.trace (((Ψ ⊗ₖ Matrix.vecMulVec u v)ᴴ *
      (Ψ ⊗ₖ Matrix.vecMulVec u v)) * ((Ψ ⊗ₖ Matrix.vecMulVec u v)ᴴ *
      (Ψ ⊗ₖ Matrix.vecMulVec u v))) = Matrix.trace ((Ψᴴ * Ψ) * (Ψᴴ * Ψ)) := by
    rw [hgram, ← Matrix.mul_kronecker_mul, hr, Matrix.trace_kronecker, htr, mul_one]
  simp only [homogeneousBudget_eq_sqrt, probability, purity, ht, htsq]

def bellAmplitude : ℝ := Real.sqrt (1 / 2)

theorem bellAmplitude_sq : bellAmplitude ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)

def localBellKet : Fin 2 × Fin 2 → ℂ := fun z =>
  if z.1 = z.2 then (bellAmplitude : ℂ) else 0

theorem localBellKet_normalized : star localBellKet ⬝ᵥ localBellKet = 1 := by
  have hh : (bellAmplitude : ℂ) * (bellAmplitude : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ← pow_two, bellAmplitude_sq]
    norm_num
  norm_num [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, localBellKet,
    Complex.star_def, hh]

def referenceInput (c : κ → ℝ) :
    Matrix (κ × (Fin 2 × Fin 2)) (κ × (Fin 2 × Fin 2)) ℂ :=
  Matrix.diagonal (fun k => (c k : ℂ)) ⊗ₖ Matrix.vecMulVec localBellKet localBellKet

theorem referenceInput_budget (c : κ → ℝ) :
    homogeneousBudget (referenceInput c) =
      homogeneousBudget (Matrix.diagonal (fun k => (c k : ℂ))) :=
  homogeneousBudget_local_pure_ancillas _ _ _ localBellKet_normalized localBellKet_normalized

def referenceBra (A : Matrix (Fin 2) κ ℂ) : Matrix (Fin 2) (κ × (Fin 2 × Fin 2)) ℂ :=
  fun h z => if h = z.2.2 then conj (A z.2.1 z.1) else 0

theorem reference_product_bra_coefficient (c : κ → ℝ)
    (A B : Matrix (Fin 2) κ ℂ) :
    referenceBra A * referenceInput c * (referenceBra B)ᵀ =
      (1 / 2 : ℝ) • (A * Matrix.diagonal (fun k => (c k : ℂ)) * Bᵀ).map conj := by
  have hh : (bellAmplitude : ℂ) * (bellAmplitude : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ← pow_two, bellAmplitude_sq]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [referenceBra, referenceInput, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.kronecker_apply, Matrix.diagonal_apply,
      localBellKet, Matrix.vecMulVec_apply, Complex.star_def, hh,
      Finset.sum_ite_irrel, mul_ite, ite_mul, Finset.mul_sum, Finset.sum_mul,
      mul_comm, mul_left_comm, mul_assoc]

def referenceIndexEquiv : (κ × (Fin 2 × Fin 2)) ≃ ((Fin 2 × κ) × Fin 2) where
  toFun z := ((z.2.1, z.1), z.2.2)
  invFun z := (z.1.2, (z.1.1, z.2))
  left_inv _ := rfl
  right_inv _ := rfl

def physicalReferenceInput (c : κ → ℝ) :
    Matrix ((Fin 2 × κ) × Fin 2) ((Fin 2 × κ) × Fin 2) ℂ :=
  Matrix.reindex referenceIndexEquiv referenceIndexEquiv (referenceInput c)

def physicalReferenceBra (A : Matrix (Fin 2) κ ℂ) :
    Matrix (Fin 2) ((Fin 2 × κ) × Fin 2) ℂ :=
  Matrix.reindex (Equiv.refl _) referenceIndexEquiv (referenceBra A)

theorem physicalReferenceBra_apply (A : Matrix (Fin 2) κ ℂ) (h a r : Fin 2) (k : κ) :
    physicalReferenceBra A h ((a, k), r) = if h = r then conj (A a k) else 0 := rfl

theorem physicalReferenceInput_apply (c : κ → ℝ) (a r b s : Fin 2) (k l : κ) :
    physicalReferenceInput c ((a, k), r) ((b, l), s) =
      if a = r ∧ b = s ∧ k = l then ((c k / 2 : ℝ) : ℂ) else 0 := by
  have hh : (bellAmplitude : ℂ) * (bellAmplitude : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ← pow_two, bellAmplitude_sq]
    norm_num
  by_cases har : a = r <;> by_cases hbs : b = s <;> by_cases hkl : k = l <;>
    simp [physicalReferenceInput, Matrix.reindex_apply, Matrix.submatrix_apply,
      referenceIndexEquiv, referenceInput, Matrix.kronecker_apply, Matrix.diagonal_apply,
      Matrix.vecMulVec_apply, localBellKet, har, hbs, hkl, hh, mul_assoc, div_eq_mul_inv]

theorem physical_reference_product_bra_coefficient (c : κ → ℝ)
    (A B : Matrix (Fin 2) κ ℂ) :
    physicalReferenceBra A * physicalReferenceInput c * (physicalReferenceBra B)ᵀ =
      (1 / 2 : ℝ) • (A * Matrix.diagonal (fun k => (c k : ℂ)) * Bᵀ).map conj := by
  have ht : (physicalReferenceBra B)ᵀ =
      Matrix.reindex referenceIndexEquiv (Equiv.refl _) (referenceBra B)ᵀ := rfl
  rw [ht]
  unfold physicalReferenceBra physicalReferenceInput
  rw [reindex_mul_equiv, reindex_mul_equiv, Matrix.reindex_refl_refl]
  exact reference_product_bra_coefficient c A B

theorem physical_reference_scaled_input_apply (c : κ → ℝ) (t : ℝ)
    (a r b s : Fin 2) (k l : κ) :
    ((Real.sqrt t)⁻¹ • physicalReferenceInput c) ((a, k), r) ((b, l), s) =
      if a = r ∧ b = s ∧ k = l then ((c k / (2 * Real.sqrt t) : ℝ) : ℂ) else 0 := by
  rw [Matrix.smul_apply, physicalReferenceInput_apply]
  split_ifs <;> simp [Complex.real_smul, div_eq_mul_inv, mul_inv_rev, mul_comm,
    mul_left_comm, mul_assoc]

theorem physical_reference_scaled_branch_coefficient (c : κ → ℝ)
    (A B : Matrix (Fin 2) κ ℂ) (t : ℝ) :
    physicalReferenceBra A * ((Real.sqrt t)⁻¹ • physicalReferenceInput c) *
      (physicalReferenceBra B)ᵀ =
        (2 * Real.sqrt t)⁻¹ • (A * Matrix.diagonal (fun k => (c k : ℂ)) * Bᵀ).map conj := by
  rw [Matrix.mul_smul, Matrix.smul_mul, physical_reference_product_bra_coefficient, smul_smul]
  have hscale : (Real.sqrt t)⁻¹ * (1 / 2 : ℝ) = (2 * Real.sqrt t)⁻¹ := by
    rw [mul_inv_rev]
    norm_num
  rw [hscale]

theorem physical_reference_normalized_branch (c : κ → ℝ)
    (A B : Matrix (Fin 2) κ ℂ) (t : ℝ) (ht : 0 < t) :
    homogeneousBudget (physicalReferenceBra A *
      ((Real.sqrt t)⁻¹ • physicalReferenceInput c) * (physicalReferenceBra B)ᵀ) =
        ‖Matrix.det (A * Matrix.diagonal (fun k => (c k : ℂ)) * Bᵀ)‖ / (2 * t) := by
  rw [physical_reference_scaled_branch_coefficient]
  exact reference_tail_budget _ t ht

theorem diagonal_contraction_eq_column_sum (c : κ → ℝ)
    (A B : Matrix (Fin 2) κ ℂ) :
    A * Matrix.diagonal (fun k => (c k : ℂ)) * Bᵀ =
      ∑ k, (c k : ℂ) • Matrix.vecMulVec (fun i => A i k) (fun j => B j k) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

def omittedCoefficient (β : κ → ℝ) (k : κ) : κ → ℝ := fun z => if z = k then 0 else β z

theorem omitted_diagonal_contraction_eq_tail_sum (β : κ → ℝ)
    (A B : Matrix (Fin 2) κ ℂ) (k : κ) :
    A * Matrix.diagonal (fun z => (omittedCoefficient β k z : ℂ)) * Bᵀ =
      ∑ z ∈ Finset.univ.erase k,
        (β z : ℂ) • Matrix.vecMulVec (fun i => A i z) (fun j => B j z) := by
  rw [diagonal_contraction_eq_column_sum]
  have hz : (omittedCoefficient β k k : ℂ) •
      Matrix.vecMulVec (fun i => A i k) (fun j => B j k) = 0 := by simp [omittedCoefficient]
  rw [← Finset.sum_erase Finset.univ
    (f := fun z => (omittedCoefficient β k z : ℂ) •
      Matrix.vecMulVec (fun i => A i z) (fun j => B j z)) hz]
  apply Finset.sum_congr rfl
  intro z hz
  simp [omittedCoefficient, Finset.ne_of_mem_erase hz]

theorem physical_reference_tail_branch_budget (β : κ → ℝ)
    (A B : Matrix (Fin 2) κ ℂ) (k : κ) (t : ℝ) (ht : 0 < t) :
    homogeneousBudget (physicalReferenceBra A *
      ((Real.sqrt t)⁻¹ • physicalReferenceInput (omittedCoefficient β k)) *
        (physicalReferenceBra B)ᵀ) =
      ‖Matrix.det (∑ z ∈ Finset.univ.erase k,
        (β z : ℂ) • Matrix.vecMulVec (fun i => A i z) (fun j => B j z))‖ / (2 * t) := by
  rw [physical_reference_normalized_branch _ _ _ _ ht,
    omitted_diagonal_contraction_eq_tail_sum]

end LocalReference

section ProtectedReference

open scoped Kronecker

variable [Fintype s] [Fintype a] [Fintype b] [Fintype c]
variable [DecidableEq a] [DecidableEq b] [DecidableEq c]

def withReference (K : Matrix c a ℂ) : Matrix (c × Fin 2) (a × Fin 2) ℂ :=
  K ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem withReference_apply (K : Matrix c a ℂ) (i : c) (j : a) (r h : Fin 2) :
    withReference K (i, r) (j, h) = if r = h then K i j else 0 := by
  simp [withReference, Matrix.kronecker_apply, Matrix.one_apply, mul_ite]

theorem withReference_sum (K : s → Matrix c a ℂ) :
    withReference (∑ k, K k) = ∑ k, withReference (K k) := by
  ext ⟨i, r⟩ ⟨j, h⟩
  simp [withReference, Matrix.kronecker_apply, Matrix.sum_apply, Finset.sum_mul]

theorem withReference_complete (K : s → Matrix c a ℂ)
    (hcomplete : ∑ k, (K k)ᴴ * K k = 1) :
    ∑ k, (withReference (K k))ᴴ * withReference (K k) = 1 := by
  simp only [withReference, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  change ∑ k, withReference ((K k)ᴴ * K k) = _
  rw [← withReference_sum, hcomplete]
  exact Matrix.one_kronecker_one

theorem withReference_mul (K : Matrix c a ℂ) (L : Matrix a b ℂ) :
    withReference K * withReference L = withReference (K * L) := by
  simp only [withReference, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem withReference_left_branch_apply (K : Matrix c a ℂ)
    (Ψ : Matrix (a × Fin 2) (b × Fin 2) ℂ) (i : c) (j : b) (r h : Fin 2) :
    (withReference K * Ψ) (i, r) (j, h) = ∑ k, K i k * Ψ (k, r) (j, h) := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, withReference_apply,
    ite_mul, Finset.sum_ite_irrel]

theorem withReference_right_branch_apply (K : Matrix c b ℂ)
    (Ψ : Matrix (a × Fin 2) (b × Fin 2) ℂ) (i : a) (j : c) (r h : Fin 2) :
    (Ψ * (withReference K)ᵀ) (i, r) (j, h) = ∑ k, Ψ (i, r) (k, h) * K j k := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, withReference_apply,
    mul_ite, Finset.sum_ite_irrel]

def rowReferenceBra (u : a → ℂ) : Matrix (Fin 2) (a × Fin 2) ℂ :=
  fun r z => if r = z.2 then u z.1 else 0

theorem rowReferenceBra_vecMul (u : c → ℂ) (K : Matrix c a ℂ) :
    rowReferenceBra (u ᵥ* K) = rowReferenceBra u * withReference K := by
  ext r ⟨i, h⟩
  by_cases hrh : r = h
  · subst h
    simp [rowReferenceBra, Matrix.mul_apply, Fintype.sum_prod_type, withReference_apply,
      Matrix.vecMul, dotProduct, mul_ite, ite_mul, Finset.sum_ite_irrel]
  · simp [rowReferenceBra, Matrix.mul_apply, Fintype.sum_prod_type, withReference_apply,
      hrh, Matrix.vecMul, dotProduct, mul_ite, ite_mul, Finset.sum_ite_irrel]

def outputReferenceBra (i : a) : Matrix (Fin 2) (a × Fin 2) ℂ :=
  rowReferenceBra (fun j => if j = i then 1 else 0)

theorem outputReferenceBra_complete :
    ∑ i : a, (outputReferenceBra i)ᴴ * outputReferenceBra i = 1 := by
  ext ⟨i, r⟩ ⟨j, h⟩
  by_cases hij : i = j <;> by_cases hrh : r = h <;>
    simp [outputReferenceBra, rowReferenceBra, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, hij, hrh, mul_ite, ite_mul, Finset.sum_ite_irrel] <;> aesop

theorem outputReferenceBra_branch (Ψ : Matrix (a × Fin 2) (b × Fin 2) ℂ) (i : a) (j : b) :
    outputReferenceBra i * Ψ * (outputReferenceBra j)ᵀ =
      fun r h => Ψ (i, r) (j, h) := by
  ext r h
  simp [outputReferenceBra, rowReferenceBra, Matrix.mul_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, Finset.sum_ite_irrel]

theorem outputReference_budget_le (Ψ : Matrix (a × Fin 2) (b × Fin 2) ℂ) :
    ∑ i : a, ∑ j : b,
      homogeneousBudget (outputReferenceBra i * Ψ * (outputReferenceBra j)ᵀ) ≤
        homogeneousBudget Ψ := by
  calc
    _ ≤ ∑ i : a, homogeneousBudget (outputReferenceBra i * Ψ) := by
      exact Finset.sum_le_sum (fun i hi => right_kraus_homogeneousBudget_le
        (outputReferenceBra i * Ψ) (fun j : b => outputReferenceBra j) outputReferenceBra_complete)
    _ ≤ homogeneousBudget Ψ := left_kraus_homogeneousBudget_le Ψ
      (fun i : a => outputReferenceBra i) outputReferenceBra_complete

theorem outputReference_probability_sum (Ψ : Matrix (a × Fin 2) (b × Fin 2) ℂ) :
    ∑ i : a, ∑ j : b,
      probability ((outputReferenceBra i * Ψ * (outputReferenceBra j)ᵀ)ᴴ *
        (outputReferenceBra i * Ψ * (outputReferenceBra j)ᵀ)) = probability (Ψᴴ * Ψ) := by
  simp_rw [right_kraus_probability_sum _ (fun j : b => outputReferenceBra j)
    outputReferenceBra_complete]
  exact left_kraus_probability_sum Ψ (fun i : a => outputReferenceBra i) outputReferenceBra_complete

end ProtectedReference

structure SystemBraPair (m n : ℕ) where
  left : Fin m → ℂ
  right : Fin n → ℂ

namespace SystemBraPair

def precomposeLeft {m n out : ℕ} (q : SystemBraPair out n)
    (K : Matrix (Fin out) (Fin m) ℂ) : SystemBraPair m n :=
  ⟨q.left ᵥ* K, q.right⟩

def precomposeRight {m n out : ℕ} (q : SystemBraPair m out)
    (K : Matrix (Fin out) (Fin n) ℂ) : SystemBraPair m n :=
  ⟨q.left, q.right ᵥ* K⟩

def referenceCoefficient {m n : ℕ} (q : SystemBraPair m n)
    (Ψ : Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rowReferenceBra q.left * Ψ * (rowReferenceBra q.right)ᵀ

theorem referenceCoefficient_precomposeLeft {m n out : ℕ} (q : SystemBraPair out n)
    (K : Matrix (Fin out) (Fin m) ℂ)
    (Ψ : Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ) :
    (q.precomposeLeft K).referenceCoefficient Ψ =
      q.referenceCoefficient (withReference K * Ψ) := by
  simp only [referenceCoefficient, precomposeLeft, rowReferenceBra_vecMul, Matrix.mul_assoc]

theorem referenceCoefficient_precomposeRight {m n out : ℕ} (q : SystemBraPair m out)
    (K : Matrix (Fin out) (Fin n) ℂ)
    (Ψ : Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ) :
    (q.precomposeRight K).referenceCoefficient Ψ =
      q.referenceCoefficient (Ψ * (withReference K)ᵀ) := by
  simp only [referenceCoefficient, precomposeRight, rowReferenceBra_vecMul,
    Matrix.transpose_mul, Matrix.mul_assoc]

end SystemBraPair

namespace FiniteLocalKrausTree

def terminalBraPairs : {m n : ℕ} → FiniteLocalKrausTree m n → List (SystemBraPair m n)
  | _, _, .leaf m n =>
      (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n =>
        (⟨fun a => if a = i then 1 else 0, fun b => if b = j then 1 else 0⟩ : SystemBraPair m n)).flatten
  | _, _, .alice m n out outcomes A complete next =>
      (List.ofFn fun k : Fin outcomes =>
        (terminalBraPairs (next k)).map (fun q => q.precomposeLeft (A k))).flatten
  | _, _, .bob m n out outcomes B complete next =>
      (List.ofFn fun k : Fin outcomes =>
        (terminalBraPairs (next k)).map (fun q => q.precomposeRight (B k))).flatten

def referenceTerminalBranches : {m n : ℕ} → FiniteLocalKrausTree m n →
    Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ → List (Matrix (Fin 2) (Fin 2) ℂ)
  | _, _, .leaf m n, Ψ =>
      (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n =>
        outputReferenceBra i * Ψ * (outputReferenceBra j)ᵀ).flatten
  | _, _, .alice m n out outcomes A complete next, Ψ =>
      (List.ofFn fun k : Fin outcomes => referenceTerminalBranches (next k) (withReference (A k) * Ψ)).flatten
  | _, _, .bob m n out outcomes B complete next, Ψ =>
      (List.ofFn fun k : Fin outcomes => referenceTerminalBranches (next k) (Ψ * (withReference (B k))ᵀ)).flatten

def referenceTerminalBudget {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (Ψ : Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ) : ℝ :=
  ((T.referenceTerminalBranches Ψ).map homogeneousBudget).sum

def referenceTerminalMass {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (Ψ : Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ) : ℝ :=
  ((T.referenceTerminalBranches Ψ).map fun M => probability (Mᴴ * M)).sum

theorem referenceTerminalBudget_leaf (m n : ℕ)
    (Ψ : Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ) :
    referenceTerminalBudget (.leaf m n) Ψ =
      ∑ i : Fin m, ∑ j : Fin n,
        homogeneousBudget (outputReferenceBra i * Ψ * (outputReferenceBra j)ᵀ) := by
  simp [referenceTerminalBudget, referenceTerminalBranches, List.map_flatten,
    List.sum_flatten, List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem referenceTerminalBudget_alice (m n out outcomes : ℕ)
    (A : Fin outcomes → Matrix (Fin out) (Fin m) ℂ)
    (complete : ∑ k, (A k)ᴴ * A k = 1)
    (next : Fin outcomes → FiniteLocalKrausTree out n)
    (Ψ : Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ) :
    referenceTerminalBudget (.alice m n out outcomes A complete next) Ψ =
      ∑ k, referenceTerminalBudget (next k) (withReference (A k) * Ψ) := by
  simp [referenceTerminalBudget, referenceTerminalBranches, List.map_flatten,
    List.sum_flatten, List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem referenceTerminalBudget_bob (m n out outcomes : ℕ)
    (B : Fin outcomes → Matrix (Fin out) (Fin n) ℂ)
    (complete : ∑ k, (B k)ᴴ * B k = 1)
    (next : Fin outcomes → FiniteLocalKrausTree m out)
    (Ψ : Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ) :
    referenceTerminalBudget (.bob m n out outcomes B complete next) Ψ =
      ∑ k, referenceTerminalBudget (next k) (Ψ * (withReference (B k))ᵀ) := by
  simp [referenceTerminalBudget, referenceTerminalBranches, List.map_flatten,
    List.sum_flatten, List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def]

theorem referenceTerminalBudget_le {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (Ψ : Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ) :
    T.referenceTerminalBudget Ψ ≤ homogeneousBudget Ψ := by
  induction T with
  | leaf m n => rw [referenceTerminalBudget_leaf]; exact outputReference_budget_le Ψ
  | alice m n out outcomes A complete next ih =>
    rw [referenceTerminalBudget_alice]
    calc
      _ ≤ ∑ k, homogeneousBudget (withReference (A k) * Ψ) :=
        Finset.sum_le_sum (fun k hk => ih k _)
      _ ≤ homogeneousBudget Ψ := left_kraus_homogeneousBudget_le Ψ
        (fun k => withReference (A k)) (withReference_complete A complete)
  | bob m n out outcomes B complete next ih =>
    rw [referenceTerminalBudget_bob]
    calc
      _ ≤ ∑ k, homogeneousBudget (Ψ * (withReference (B k))ᵀ) :=
        Finset.sum_le_sum (fun k hk => ih k _)
      _ ≤ homogeneousBudget Ψ := right_kraus_homogeneousBudget_le Ψ
        (fun k => withReference (B k)) (withReference_complete B complete)

theorem referenceTerminalMass_eq {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (Ψ : Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ) :
    T.referenceTerminalMass Ψ = probability (Ψᴴ * Ψ) := by
  induction T with
  | leaf m n =>
    simp only [referenceTerminalMass, referenceTerminalBranches, List.map_flatten,
      List.sum_flatten, List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    exact outputReference_probability_sum Ψ
  | alice m n out outcomes A complete next ih =>
    change ((List.ofFn fun k : Fin outcomes =>
      referenceTerminalBranches (next k) (withReference (A k) * Ψ)).flatten.map
        (fun M => probability (Mᴴ * M))).sum = _
    simp only [List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn,
      List.sum_ofFn, Function.comp_def]
    change ∑ k, referenceTerminalMass (next k) (withReference (A k) * Ψ) = _
    simp_rw [ih]
    exact left_kraus_probability_sum Ψ (fun k => withReference (A k))
      (withReference_complete A complete)
  | bob m n out outcomes B complete next ih =>
    change ((List.ofFn fun k : Fin outcomes =>
      referenceTerminalBranches (next k) (Ψ * (withReference (B k))ᵀ)).flatten.map
        (fun M => probability (Mᴴ * M))).sum = _
    simp only [List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn,
      List.sum_ofFn, Function.comp_def]
    change ∑ k, referenceTerminalMass (next k) (Ψ * (withReference (B k))ᵀ) = _
    simp_rw [ih]
    exact right_kraus_probability_sum Ψ (fun k => withReference (B k))
      (withReference_complete B complete)

theorem referenceTerminalBranches_eq_braPairs {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (Ψ : Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ) :
    T.referenceTerminalBranches Ψ =
      (T.terminalBraPairs).map (fun q => q.referenceCoefficient Ψ) := by
  induction T with
  | leaf m n =>
    simp [referenceTerminalBranches, terminalBraPairs, SystemBraPair.referenceCoefficient,
      outputReferenceBra, List.map_flatten, List.map_ofFn, List.map_map, Function.comp_def]
  | alice m n out outcomes A complete next ih =>
    simp only [referenceTerminalBranches, terminalBraPairs, List.map_flatten,
      List.map_ofFn, List.map_map, Function.comp_def]
    simp_rw [SystemBraPair.referenceCoefficient_precomposeLeft, ih]
  | bob m n out outcomes B complete next ih =>
    simp only [referenceTerminalBranches, terminalBraPairs, List.map_flatten,
      List.map_ofFn, List.map_map, Function.comp_def]
    simp_rw [SystemBraPair.referenceCoefficient_precomposeRight, ih]

theorem terminalBra_referenceBudget_le {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (Ψ : Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ) :
    ((T.terminalBraPairs).map fun q => homogeneousBudget (q.referenceCoefficient Ψ)).sum ≤
      homogeneousBudget Ψ := by
  simpa only [referenceTerminalBudget, referenceTerminalBranches_eq_braPairs,
    List.map_map, Function.comp_def] using T.referenceTerminalBudget_le Ψ

end FiniteLocalKrausTree

section BraTransport

variable [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem referenceCoefficient_reindex {m n : ℕ} (q : SystemBraPair m n)
    (ea : a ≃ Fin m) (eb : b ≃ Fin n)
    (Ψ : Matrix (a × Fin 2) (b × Fin 2) ℂ) :
    q.referenceCoefficient (Matrix.reindex (ea.prodCongr (Equiv.refl _))
      (eb.prodCongr (Equiv.refl _)) Ψ) =
        rowReferenceBra (fun i => q.left (ea i)) * Ψ *
          (rowReferenceBra (fun j => q.right (eb j)))ᵀ := by
  have hl : rowReferenceBra q.left =
      Matrix.reindex (Equiv.refl _) (ea.prodCongr (Equiv.refl _))
        (rowReferenceBra (fun i => q.left (ea i))) := by
    ext r ⟨i, h⟩
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, rowReferenceBra]
  have hr : rowReferenceBra q.right =
      Matrix.reindex (Equiv.refl _) (eb.prodCongr (Equiv.refl _))
        (rowReferenceBra (fun j => q.right (eb j))) := by
    ext r ⟨j, h⟩
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, rowReferenceBra]
  unfold SystemBraPair.referenceCoefficient
  rw [hl, hr]
  have ht : (Matrix.reindex (Equiv.refl (Fin 2)) (eb.prodCongr (Equiv.refl (Fin 2)))
      (rowReferenceBra (fun j => q.right (eb j))))ᵀ =
      Matrix.reindex (eb.prodCongr (Equiv.refl (Fin 2))) (Equiv.refl (Fin 2))
        (rowReferenceBra (fun j => q.right (eb j)))ᵀ := rfl
  rw [ht, reindex_mul_equiv, reindex_mul_equiv, Matrix.reindex_refl_refl]

end BraTransport

namespace SystemBraPair

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def leftKetMatrix {m n : ℕ} (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) : Matrix (Fin 2) κ ℂ :=
  fun i k => conj (q.left (ea (i, k)))

def rightKetMatrix {m n : ℕ} (q : SystemBraPair m n)
    (eb : (Fin 2 × κ) ≃ Fin n) : Matrix (Fin 2) κ ℂ :=
  fun j k => conj (q.right (eb (j, k)))

theorem physicalReferenceBra_leftKet {m n : ℕ} (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) :
    physicalReferenceBra (q.leftKetMatrix ea) = rowReferenceBra (fun z => q.left (ea z)) := by
  ext r ⟨⟨i, k⟩, h⟩
  simp [physicalReferenceBra_apply, leftKetMatrix, rowReferenceBra]

theorem physicalReferenceBra_rightKet {m n : ℕ} (q : SystemBraPair m n)
    (eb : (Fin 2 × κ) ≃ Fin n) :
    physicalReferenceBra (q.rightKetMatrix eb) = rowReferenceBra (fun z => q.right (eb z)) := by
  ext r ⟨⟨j, k⟩, h⟩
  simp [physicalReferenceBra_apply, rightKetMatrix, rowReferenceBra]

def tailCost {m n : ℕ} (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) : ℝ :=
  ‖Matrix.det (∑ z ∈ Finset.univ.erase k,
    (β z : ℂ) • Matrix.vecMulVec (fun i => q.leftKetMatrix ea i z)
      (fun j => q.rightKetMatrix eb j z))‖

theorem referenceCoefficient_tail_budget {m n : ℕ} (q : SystemBraPair m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) (t : ℝ) (ht : 0 < t) :
    homogeneousBudget (q.referenceCoefficient
      (Matrix.reindex (ea.prodCongr (Equiv.refl _)) (eb.prodCongr (Equiv.refl _))
        ((Real.sqrt t)⁻¹ • physicalReferenceInput (omittedCoefficient β k)))) =
      q.tailCost ea eb β k / (2 * t) := by
  rw [referenceCoefficient_reindex, ← physicalReferenceBra_leftKet q ea,
    ← physicalReferenceBra_rightKet q eb]
  exact physical_reference_tail_branch_budget β (q.leftKetMatrix ea)
    (q.rightKetMatrix eb) k t ht

end SystemBraPair

namespace FiniteLocalKrausTree

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem terminal_tail_cost_le {m n : ℕ} (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) (t : ℝ) (ht : 0 < t) :
    ((T.terminalBraPairs).map fun q => q.tailCost ea eb β k).sum ≤
      (2 * t) * homogeneousBudget
        ((Real.sqrt t)⁻¹ • physicalReferenceInput (omittedCoefficient β k)) := by
  have h := T.terminalBra_referenceBudget_le
    (Matrix.reindex (ea.prodCongr (Equiv.refl _)) (eb.prodCongr (Equiv.refl _))
      ((Real.sqrt t)⁻¹ • physicalReferenceInput (omittedCoefficient β k)))
  rw [homogeneousBudget_reindex_equiv] at h
  simp_rw [SystemBraPair.referenceCoefficient_tail_budget _ ea eb β k t ht] at h
  simp only [div_eq_mul_inv, List.sum_map_mul_right] at h
  change ((T.terminalBraPairs).map fun q => q.tailCost ea eb β k).sum / (2 * t) ≤ _ at h
  have hpos : 0 < 2 * t := mul_pos (by norm_num) ht
  simpa only [mul_comm] using (div_le_iff₀ hpos).mp h

end FiniteLocalKrausTree

section ProductEffects

open scoped Kronecker

variable {d p : Type*} [Fintype s] [Fintype a] [Fintype b] [Fintype c]
variable [Fintype d] [Fintype p] [DecidableEq a] [DecidableEq p]

theorem kronecker_sum_left (K : s → Matrix a b ℂ) (R : Matrix c d ℂ) :
    (∑ k, K k) ⊗ₖ R = ∑ k, K k ⊗ₖ R := by
  ext ⟨i, r⟩ ⟨j, h⟩
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul]

theorem kronecker_sum_right (R : Matrix a b ℂ) (K : s → Matrix c d ℂ) :
    R ⊗ₖ (∑ k, K k) = ∑ k, R ⊗ₖ K k := by
  ext ⟨i, r⟩ ⟨j, h⟩
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.mul_sum]

theorem kronecker_left_complete (K : s → Matrix c a ℂ)
    (hcomplete : ∑ k, (K k)ᴴ * K k = 1) :
    ∑ k, (K k ⊗ₖ (1 : Matrix p p ℂ))ᴴ * (K k ⊗ₖ (1 : Matrix p p ℂ)) = 1 := by
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [← kronecker_sum_left, hcomplete]
  exact Matrix.one_kronecker_one

theorem kronecker_right_complete (K : s → Matrix c a ℂ)
    (hcomplete : ∑ k, (K k)ᴴ * K k = 1) :
    ∑ k, ((1 : Matrix p p ℂ) ⊗ₖ K k)ᴴ * ((1 : Matrix p p ℂ) ⊗ₖ K k) = 1 := by
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [← kronecker_sum_right, hcomplete]
  exact Matrix.one_kronecker_one

def rowEffect (u : a → ℂ) : Matrix a a ℂ :=
  (Matrix.replicateRow Unit u)ᴴ * Matrix.replicateRow Unit u

theorem rowEffect_apply (u : a → ℂ) (i j : a) :
    rowEffect u i j = conj (u i) * u j := by
  simp [rowEffect, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.replicateRow, Complex.star_def]

theorem rowEffect_vecMul (u : c → ℂ) (K : Matrix c a ℂ) :
    rowEffect (u ᵥ* K) = Kᴴ * rowEffect u * K := by
  simp only [rowEffect, Matrix.replicateRow_vecMul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem rowEffect_basis_sum :
    ∑ i : a, rowEffect (fun j => if j = i then 1 else 0) = 1 := by
  ext i j
  by_cases hij : i = j <;>
    simp [Matrix.sum_apply, rowEffect_apply, Matrix.one_apply, hij,
      mul_ite, ite_mul, Finset.sum_ite_irrel] <;> aesop

theorem list_sum_map_sandwich {u : Type*} (l : List u) (f : u → Matrix a a ℂ)
    (K : Matrix a b ℂ) :
    (l.map fun z => Kᴴ * f z * K).sum = Kᴴ * (l.map f).sum * K := by
  induction l with
  | nil => simp
  | cons z l ih => simp [List.map_cons, List.sum_cons, Matrix.mul_add, Matrix.add_mul, ih]

end ProductEffects

namespace SystemBraPair

open scoped Kronecker

def productEffect {m n : ℕ} (q : SystemBraPair m n) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ := rowEffect q.left ⊗ₖ rowEffect q.right

theorem productEffect_precomposeLeft {m n out : ℕ} (q : SystemBraPair out n)
    (K : Matrix (Fin out) (Fin m) ℂ) :
    (q.precomposeLeft K).productEffect =
      (K ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ * q.productEffect *
        (K ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  simp only [productEffect, precomposeLeft, rowEffect_vecMul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

theorem productEffect_precomposeRight {m n out : ℕ} (q : SystemBraPair m out)
    (K : Matrix (Fin out) (Fin n) ℂ) :
    (q.precomposeRight K).productEffect =
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K)ᴴ * q.productEffect *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) := by
  simp only [productEffect, precomposeRight, rowEffect_vecMul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

theorem productEffect_apply {m n : ℕ} (q : SystemBraPair m n)
    (i k : Fin m) (j l : Fin n) :
    q.productEffect (i, j) (k, l) = conj (q.left i * q.right j) * (q.left k * q.right l) := by
  simp only [productEffect, Matrix.kronecker_apply, rowEffect_apply, map_mul]
  ring

theorem productEffect_eq_outer {m n : ℕ} (q : SystemBraPair m n) :
    q.productEffect = Matrix.vecMulVec (fun z => conj (q.left z.1 * q.right z.2))
      (fun z => q.left z.1 * q.right z.2) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  exact productEffect_apply q i k j l

theorem productEffect_posSemidef {m n : ℕ} (q : SystemBraPair m n) :
    q.productEffect.PosSemidef := by
  rw [productEffect_eq_outer]
  have hstar : star (fun z : Fin m × Fin n => q.left z.1 * q.right z.2) =
      fun z => conj (q.left z.1 * q.right z.2) := by
    funext z
    rfl
  rw [← hstar]
  exact Matrix.posSemidef_vecMulVec_star_self (fun z : Fin m × Fin n => q.left z.1 * q.right z.2)

end SystemBraPair

namespace FiniteLocalKrausTree

open scoped Kronecker

def terminalProductEffect {m n : ℕ} (T : FiniteLocalKrausTree m n) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  ((T.terminalBraPairs).map SystemBraPair.productEffect).sum

theorem terminalProductEffect_leaf (m n : ℕ) : terminalProductEffect (.leaf m n) = 1 := by
  simp only [terminalProductEffect, terminalBraPairs, List.map_flatten, List.sum_flatten,
    List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def, SystemBraPair.productEffect]
  simp_rw [← kronecker_sum_right]
  rw [← kronecker_sum_left, rowEffect_basis_sum, rowEffect_basis_sum]
  exact Matrix.one_kronecker_one

theorem terminalProductEffect_alice (m n out outcomes : ℕ)
    (A : Fin outcomes → Matrix (Fin out) (Fin m) ℂ)
    (complete : ∑ k, (A k)ᴴ * A k = 1) (next : Fin outcomes → FiniteLocalKrausTree out n) :
    terminalProductEffect (.alice m n out outcomes A complete next) =
      ∑ k, (A k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ * (next k).terminalProductEffect *
        (A k ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  simp only [terminalProductEffect, terminalBraPairs, List.map_flatten, List.sum_flatten,
    List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    SystemBraPair.productEffect_precomposeLeft, list_sum_map_sandwich]

theorem terminalProductEffect_bob (m n out outcomes : ℕ)
    (B : Fin outcomes → Matrix (Fin out) (Fin n) ℂ)
    (complete : ∑ k, (B k)ᴴ * B k = 1) (next : Fin outcomes → FiniteLocalKrausTree m out) :
    terminalProductEffect (.bob m n out outcomes B complete next) =
      ∑ k, ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ B k)ᴴ * (next k).terminalProductEffect *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ B k) := by
  simp only [terminalProductEffect, terminalBraPairs, List.map_flatten, List.sum_flatten,
    List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    SystemBraPair.productEffect_precomposeRight, list_sum_map_sandwich]

theorem terminalProductEffect_eq_one {m n : ℕ} (T : FiniteLocalKrausTree m n) :
    T.terminalProductEffect = 1 := by
  induction T with
  | leaf m n => exact terminalProductEffect_leaf m n
  | alice m n out outcomes A complete next ih =>
    rw [terminalProductEffect_alice]
    simp_rw [ih, Matrix.mul_one]
    exact kronecker_left_complete A complete
  | bob m n out outcomes B complete next ih =>
    rw [terminalProductEffect_bob]
    simp_rw [ih, Matrix.mul_one]
    exact kronecker_right_complete B complete

end FiniteLocalKrausTree

section EuclideanEffects

variable [Fintype a] [DecidableEq a]

theorem toEuclideanCLM_outer (u : a → ℂ) :
    Matrix.toEuclideanCLM (n := a) (𝕜 := ℂ) (Matrix.vecMulVec u (fun j => conj (u j))) =
      InnerProductSpace.rankOne ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 u) := by
  ext x i
  change (Matrix.vecMulVec u (fun j => conj (u j)) *ᵥ (fun j => x j)) i =
    (inner ℂ (WithLp.toLp 2 u) x • WithLp.toLp 2 u) i
  simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, PiLp.inner_apply,
    RCLike.inner_apply, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]

end EuclideanEffects

namespace SystemBraPair

def productKet {m n : ℕ} (q : SystemBraPair m n) : EuclideanSpace ℂ (Fin m × Fin n) :=
  WithLp.toLp 2 (fun z => conj (q.left z.1 * q.right z.2))

theorem productEffect_toEuclideanCLM {m n : ℕ} (q : SystemBraPair m n) :
    Matrix.toEuclideanCLM (n := Fin m × Fin n) (𝕜 := ℂ) q.productEffect =
      InnerProductSpace.rankOne ℂ q.productKet q.productKet := by
  have houter : q.productEffect = Matrix.vecMulVec
      (fun z : Fin m × Fin n => conj (q.left z.1 * q.right z.2))
      (fun z => conj (conj (q.left z.1 * q.right z.2))) := by
    rw [productEffect_eq_outer]
    simp
  rw [houter]
  exact toEuclideanCLM_outer _

end SystemBraPair

namespace FiniteLocalKrausTree

theorem terminal_rankOne_sum_eq_one {m n : ℕ} (T : FiniteLocalKrausTree m n) :
    ((T.terminalBraPairs).map fun q =>
      InnerProductSpace.rankOne ℂ q.productKet q.productKet).sum = 1 := by
  have hsum (l : List (SystemBraPair m n)) :
      (l.map fun q => Matrix.toEuclideanCLM (n := Fin m × Fin n) (𝕜 := ℂ) q.productEffect).sum =
        Matrix.toEuclideanCLM (n := Fin m × Fin n) (𝕜 := ℂ) ((l.map SystemBraPair.productEffect).sum) := by
    induction l with
    | nil => simp
    | cons q l ih => simp [List.map_cons, List.sum_cons, ih]
  simp_rw [← SystemBraPair.productEffect_toEuclideanCLM]
  rw [hsum]
  change Matrix.toEuclideanCLM (n := Fin m × Fin n) (𝕜 := ℂ) T.terminalProductEffect = 1
  rw [terminalProductEffect_eq_one]
  exact map_one _

end FiniteLocalKrausTree

end

end QuantumProver.ElegantJointMeasurement.Concurrence

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

noncomputable section

variable {I O R : Type*} [Fintype I] [Fintype O]
  [DecidableEq I] [DecidableEq O]

def amplification (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (k : ℕ)
    (M : Matrix (Fin k × I) (Fin k × I) ℂ) :
    Matrix (Fin k × O) (Fin k × O) ℂ :=
  fun i j => Φ (fun a b => M (i.1, a) (j.1, b)) i.2 j.2

def CompletelyPositive (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Prop :=
  ∀ k (M : Matrix (Fin k × I) (Fin k × I) ℂ),
    M.PosSemidef → (amplification Φ k M).PosSemidef

def choi (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    Matrix (I × O) (I × O) ℂ :=
  fun i j => Φ (Matrix.single i.1 j.1 1) i.2 j.2

def entangledVector (I : Type*) [Fintype I] : Fin (Fintype.card I) × I → ℂ :=
  fun i => if i.1 = Fintype.equivFin I i.2 then 1 else 0

def entangledInput (I : Type*) [Fintype I] :
    Matrix (Fin (Fintype.card I) × I) (Fin (Fintype.card I) × I) ℂ :=
  Matrix.vecMulVec (entangledVector I) (star (entangledVector I))

theorem entangledInput_posSemidef : (entangledInput I).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (entangledVector I)

theorem entangledInput_block (i j : I) :
    (fun a b => entangledInput I (Fintype.equivFin I i, a)
      (Fintype.equivFin I j, b)) = Matrix.single i j 1 := by
  ext a b
  by_cases hia : i = a <;> by_cases hjb : j = b <;>
    simp [entangledInput, entangledVector, Matrix.vecMulVec_apply,
      Matrix.single_apply, (Fintype.equivFin I).injective.eq_iff, hia, hjb]

theorem amplification_entangledInput_submatrix
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    (amplification Φ (Fintype.card I) (entangledInput I)).submatrix
      (fun i : I × O => (Fintype.equivFin I i.1, i.2))
      (fun i : I × O => (Fintype.equivFin I i.1, i.2)) = choi Φ := by
  ext i j
  simp only [Matrix.submatrix_apply, amplification, choi, entangledInput_block]

theorem choi_posSemidef (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hΦ : CompletelyPositive Φ) : (choi Φ).PosSemidef := by
  have h := (hΦ (Fintype.card I) (entangledInput I) entangledInput_posSemidef).submatrix
    (fun i : I × O => (Fintype.equivFin I i.1, i.2))
  rwa [amplification_entangledInput_submatrix] at h

def choiFactor (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    Matrix (I × O) (I × O) ℂ := CFC.sqrt (choi Φ)

theorem choiFactor_mul_conjTranspose
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ) :
    choiFactor Φ * (choiFactor Φ)ᴴ = choi Φ := by
  have hs : (choiFactor Φ)ᴴ = choiFactor Φ :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (choi Φ))).isHermitian
  rw [hs, ← pow_two]
  exact CFC.sq_sqrt (choi Φ) (choi_posSemidef Φ hΦ).nonneg

def krausOperator (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (q : I × O) :
    Matrix O I ℂ := fun b i => choiFactor Φ (i, b) q

def krausMap [Fintype R] (K : R → Matrix O I ℂ) :
    Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ where
  toFun M := ∑ q, K q * M * (K q)ᴴ
  map_add' M N := by
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' z M := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply]

theorem kraus_matrix_unit (K : Matrix O I ℂ) (i j : I) (b c : O) :
    (K * Matrix.single i j (1 : ℂ) * Kᴴ) b c = K b i * conj (K c j) := by
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

theorem krausMap_matrix_unit
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ) (i j : I) :
    krausMap (krausOperator Φ) (Matrix.single i j 1) = Φ (Matrix.single i j 1) := by
  ext b c
  change (∑ q, krausOperator Φ q * Matrix.single i j (1 : ℂ) *
    (krausOperator Φ q)ᴴ) b c = _
  simp only [Matrix.sum_apply, kraus_matrix_unit, krausOperator]
  change (choiFactor Φ * (choiFactor Φ)ᴴ) (i, b) (j, c) = choi Φ (i, b) (j, c)
  rw [choiFactor_mul_conjTranspose Φ hΦ]

theorem linearMap_eq_of_matrix_units
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (h : ∀ i j, Φ (Matrix.single i j 1) = Ψ (Matrix.single i j 1)) : Φ = Ψ := by
  apply Matrix.ext_linearMap
  intro i j
  apply LinearMap.ext
  intro z
  change Φ (Matrix.single i j z) = Ψ (Matrix.single i j z)
  have hsingle : Matrix.single i j z = z • Matrix.single i j (1 : ℂ) := by
    simp [Matrix.smul_single]
  rw [hsingle, map_smul, map_smul, h i j]

theorem completelyPositive_eq_krausMap
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ) :
    Φ = krausMap (krausOperator Φ) :=
  linearMap_eq_of_matrix_units Φ _ (fun i j => (krausMap_matrix_unit Φ hΦ i j).symm)

theorem completelyPositive_apply_eq_sum
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (M : Matrix I I ℂ) :
    Φ M = ∑ q : I × O, krausOperator Φ q * M * (krausOperator Φ q)ᴴ := by
  exact congrArg (fun Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ => Ψ M)
    (completelyPositive_eq_krausMap Φ hΦ)

theorem krausMap_trace [Fintype R] (K : R → Matrix O I ℂ) (M : Matrix I I ℂ) :
    (krausMap K M).trace = ((∑ q, (K q)ᴴ * K q) * M).trace := by
  change (∑ q, K q * M * (K q)ᴴ).trace = _
  simp only [Matrix.trace_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  exact Matrix.trace_mul_cycle (K q) M (K q)ᴴ

theorem krausMap_trace_preserving_iff [Fintype R] (K : R → Matrix O I ℂ) :
    (∀ M : Matrix I I ℂ, (krausMap K M).trace = M.trace) ↔
      ∑ q, (K q)ᴴ * K q = 1 := by
  constructor
  · intro h
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro M
    rw [← krausMap_trace, Matrix.one_mul]
    exact h M
  · intro h M
    rw [krausMap_trace, h, Matrix.one_mul]

variable {S : Type*} [Fintype S]

def instrumentKraus (Φ : S → Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (q : S × (I × O)) : Matrix O I ℂ := krausOperator (Φ q.1) q.2

theorem instrument_refinement_apply
    (Φ : S → Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (M : Matrix I I ℂ) :
    krausMap (instrumentKraus Φ) M = ∑ s, Φ s M := by
  change (∑ q : S × (I × O), instrumentKraus Φ q * M *
    (instrumentKraus Φ q)ᴴ) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  exact (completelyPositive_apply_eq_sum (Φ s) (hΦ s) M).symm

theorem instrumentKraus_complete
    (Φ : S → Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ M : Matrix I I ℂ, (∑ s, Φ s M).trace = M.trace) :
    ∑ q : S × (I × O), (instrumentKraus Φ q)ᴴ * instrumentKraus Φ q = 1 := by
  apply (krausMap_trace_preserving_iff (instrumentKraus Φ)).mp
  intro M
  rw [instrument_refinement_apply Φ hΦ]
  exact htrace M

theorem instrument_reported_outcome
    (Φ : S → Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (s : S) (M : Matrix I I ℂ) :
    Φ s M = ∑ q : I × O, instrumentKraus Φ (s, q) * M *
      (instrumentKraus Φ (s, q))ᴴ :=
  completelyPositive_apply_eq_sum (Φ s) (hΦ s) M

def ancillaryKraus (k : ℕ) (K : Matrix O I ℂ) :
    Matrix (Fin k × O) (Fin k × I) ℂ := (1 : Matrix (Fin k) (Fin k) ℂ) ⊗ₖ K

theorem ancillaryKraus_block (k : ℕ) (K : Matrix O I ℂ)
    (M : Matrix (Fin k × I) (Fin k × I) ℂ) (r s : Fin k) (b c : O) :
    (ancillaryKraus k K * M * (ancillaryKraus k K)ᴴ) (r, b) (s, c) =
      (K * Matrix.of (fun i j => M (r, i) (s, j)) * Kᴴ) b c := by
  simp [ancillaryKraus, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type,
    apply_ite, mul_ite, ite_mul]

theorem amplification_krausMap [Fintype R] (K : R → Matrix O I ℂ) (k : ℕ)
    (M : Matrix (Fin k × I) (Fin k × I) ℂ) :
    amplification (krausMap K) k M =
      ∑ q, ancillaryKraus k (K q) * M * (ancillaryKraus k (K q))ᴴ := by
  ext i j
  rcases i with ⟨r, b⟩
  rcases j with ⟨s, c⟩
  change (∑ q, K q * Matrix.of (fun i j => M (r, i) (s, j)) * (K q)ᴴ) b c = _
  simp only [Matrix.sum_apply, ancillaryKraus_block]

theorem completelyPositive_amplification_eq_sum
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : CompletelyPositive Φ)
    (k : ℕ) (M : Matrix (Fin k × I) (Fin k × I) ℂ) :
    amplification Φ k M = ∑ q : I × O,
      ancillaryKraus k (krausOperator Φ q) * M *
        (ancillaryKraus k (krausOperator Φ q))ᴴ := by
  calc
    amplification Φ k M = amplification (krausMap (krausOperator Φ)) k M :=
      congrArg (fun Ψ => amplification Ψ k M) (completelyPositive_eq_krausMap Φ hΦ)
    _ = _ := amplification_krausMap _ _ _

theorem krausMap_completelyPositive [Fintype R] (K : R → Matrix O I ℂ) :
    CompletelyPositive (krausMap K) := by
  intro k M hM
  rw [amplification_krausMap]
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg
    (fun q _ => (hM.mul_mul_conjTranspose_same (ancillaryKraus k (K q))).nonneg)

theorem instrument_reported_amplification
    (Φ : S → Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (s : S) (k : ℕ)
    (M : Matrix (Fin k × I) (Fin k × I) ℂ) :
    amplification (Φ s) k M = ∑ q : I × O,
      ancillaryKraus k (instrumentKraus Φ (s, q)) * M *
        (ancillaryKraus k (instrumentKraus Φ (s, q)))ᴴ :=
  completelyPositive_amplification_eq_sum (Φ s) (hΦ s) k M

section FinNodes

variable {m n out : ℕ}

def finInstrumentKraus
    (Φ : S → Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin out) (Fin out) ℂ) :
    Fin (Fintype.card (S × (Fin m × Fin out))) → Matrix (Fin out) (Fin m) ℂ :=
  fun r => instrumentKraus Φ ((Fintype.equivFin (S × (Fin m × Fin out))).symm r)

def finInstrumentReport (r : Fin (Fintype.card (S × (Fin m × Fin out)))) : S :=
  ((Fintype.equivFin (S × (Fin m × Fin out))).symm r).1

theorem finInstrumentKraus_complete
    (Φ : S → Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin out) (Fin out) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ M : Matrix (Fin m) (Fin m) ℂ, (∑ s, Φ s M).trace = M.trace) :
    ∑ r, (finInstrumentKraus Φ r)ᴴ * finInstrumentKraus Φ r = 1 := by
  calc
    _ = ∑ q : S × (Fin m × Fin out),
        (instrumentKraus Φ q)ᴴ * instrumentKraus Φ q :=
      (Fintype.equivFin (S × (Fin m × Fin out))).symm.sum_comp
        (fun q => (instrumentKraus Φ q)ᴴ * instrumentKraus Φ q)
    _ = 1 := instrumentKraus_complete Φ hΦ htrace

theorem finInstrumentKraus_reported_outcome [DecidableEq S]
    (Φ : S → Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin out) (Fin out) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (s : S)
    (M : Matrix (Fin m) (Fin m) ℂ) :
    Φ s M = ∑ r, if finInstrumentReport (m := m) (out := out) r = s then
      finInstrumentKraus Φ r * M * (finInstrumentKraus Φ r)ᴴ else 0 := by
  unfold finInstrumentKraus finInstrumentReport
  rw [(Fintype.equivFin (S × (Fin m × Fin out))).symm.sum_comp
    (fun q : S × (Fin m × Fin out) => if q.1 = s then
      instrumentKraus Φ q * M * (instrumentKraus Φ q)ᴴ else 0)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simpa using instrument_reported_outcome Φ hΦ s M

def cpAliceNode
    (Φ : S → Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin out) (Fin out) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ M : Matrix (Fin m) (Fin m) ℂ, (∑ s, Φ s M).trace = M.trace)
    (next : S → QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree out n) :
    QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree m n :=
  .alice m n out (Fintype.card (S × (Fin m × Fin out)))
    (finInstrumentKraus Φ) (finInstrumentKraus_complete Φ hΦ htrace)
    (fun r => next (finInstrumentReport r))

def cpBobNode
    (Φ : S → Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin out) (Fin out) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ M : Matrix (Fin n) (Fin n) ℂ, (∑ s, Φ s M).trace = M.trace)
    (next : S → QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree m out) :
    QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree m n :=
  .bob m n out (Fintype.card (S × (Fin n × Fin out)))
    (finInstrumentKraus Φ) (finInstrumentKraus_complete Φ hΦ htrace)
    (fun r => next (finInstrumentReport r))

end FinNodes

inductive FiniteLocalCPInstrumentTree : ℕ → ℕ → Type where
  | leaf (m n : ℕ) : FiniteLocalCPInstrumentTree m n
  | alice (m n out outcomes : ℕ)
      (Φ : Fin outcomes → Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ]
        Matrix (Fin out) (Fin out) ℂ)
      (positive : ∀ s, CompletelyPositive (Φ s))
      (trace : ∀ M : Matrix (Fin m) (Fin m) ℂ, (∑ s, Φ s M).trace = M.trace)
      (next : Fin outcomes → FiniteLocalCPInstrumentTree out n) :
      FiniteLocalCPInstrumentTree m n
  | bob (m n out outcomes : ℕ)
      (Φ : Fin outcomes → Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
        Matrix (Fin out) (Fin out) ℂ)
      (positive : ∀ s, CompletelyPositive (Φ s))
      (trace : ∀ M : Matrix (Fin n) (Fin n) ℂ, (∑ s, Φ s M).trace = M.trace)
      (next : Fin outcomes → FiniteLocalCPInstrumentTree m out) :
      FiniteLocalCPInstrumentTree m n

namespace FiniteLocalCPInstrumentTree

def krausRefinement : {m n : ℕ} → FiniteLocalCPInstrumentTree m n →
    QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree m n
  | _, _, .leaf m n => .leaf m n
  | _, _, .alice _ _ _ _ Φ positive trace next =>
      cpAliceNode Φ positive trace (fun s => krausRefinement (next s))
  | _, _, .bob _ _ _ _ Φ positive trace next =>
      cpBobNode Φ positive trace (fun s => krausRefinement (next s))

theorem refined_terminalBudget_le {m n : ℕ} (T : FiniteLocalCPInstrumentTree m n)
    (Ψ : Matrix (Fin m) (Fin n) ℂ) :
    T.krausRefinement.terminalBudget Ψ ≤ QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget Ψ :=
  T.krausRefinement.terminalBudget_le Ψ

theorem refined_referenceTerminalBudget_le {m n : ℕ}
    (T : FiniteLocalCPInstrumentTree m n)
    (Ψ : Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ) :
    ((T.krausRefinement.referenceTerminalBranches Ψ).map
      QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget).sum ≤ QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget Ψ :=
  T.krausRefinement.referenceTerminalBudget_le Ψ

theorem refined_referenceTerminalMass_eq {m n : ℕ}
    (T : FiniteLocalCPInstrumentTree m n)
    (Ψ : Matrix (Fin m × Fin 2) (Fin n × Fin 2) ℂ) :
    ((T.krausRefinement.referenceTerminalBranches Ψ).map
      (fun M => QuantumProver.ElegantJointMeasurement.Concurrence.probability (Mᴴ * M))).sum =
      QuantumProver.ElegantJointMeasurement.Concurrence.probability (Ψᴴ * Ψ) :=
  T.krausRefinement.referenceTerminalMass_eq Ψ

theorem refined_terminalProductEffect_eq_one {m n : ℕ}
    (T : FiniteLocalCPInstrumentTree m n) :
    (T.krausRefinement.terminalBraPairs.map
      QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair.productEffect).sum = 1 :=
  T.krausRefinement.terminalProductEffect_eq_one

theorem refined_terminal_tail_cost_le {m n : ℕ} {κ : Type*}
    [Fintype κ] [DecidableEq κ] (T : FiniteLocalCPInstrumentTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) (t : ℝ) (ht : 0 < t) :
    (T.krausRefinement.terminalBraPairs.map
      (fun q => q.tailCost ea eb β k)).sum ≤ (2 * t) *
      QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget ((Real.sqrt t)⁻¹ •
        QuantumProver.ElegantJointMeasurement.Concurrence.physicalReferenceInput (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k)) :=
  T.krausRefinement.terminal_tail_cost_le ea eb β k t ht

end FiniteLocalCPInstrumentTree

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

noncomputable section

variable {m n out : ℕ}

def leftApplication
    (Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin out) (Fin out) ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin out × Fin n) (Fin out × Fin n) ℂ where
  toFun X := fun i j => Φ (Matrix.of (fun a b => X (a, i.2) (b, j.2))) i.1 j.1
  map_add' X Y := by
    ext i j
    change Φ (Matrix.of (fun a b => X (a, i.2) (b, j.2)) +
      Matrix.of (fun a b => Y (a, i.2) (b, j.2))) i.1 j.1 = _
    rw [map_add]
    rfl
  map_smul' z X := by
    ext i j
    change Φ (z • Matrix.of (fun a b => X (a, i.2) (b, j.2))) i.1 j.1 = _
    rw [map_smul]
    rfl

def rightApplication
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin out) (Fin out) ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin out) (Fin m × Fin out) ℂ where
  toFun X := fun i j => Φ (Matrix.of (fun a b => X (i.1, a) (j.1, b))) i.2 j.2
  map_add' X Y := by
    ext i j
    change Φ (Matrix.of (fun a b => X (i.1, a) (j.1, b)) +
      Matrix.of (fun a b => Y (i.1, a) (j.1, b))) i.2 j.2 = _
    rw [map_add]
    rfl
  map_smul' z X := by
    ext i j
    change Φ (z • Matrix.of (fun a b => X (i.1, a) (j.1, b))) i.2 j.2 = _
    rw [map_smul]
    rfl

def leftKrausApplication (K : Matrix (Fin out) (Fin m) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    Matrix (Fin out × Fin n) (Fin out × Fin n) ℂ :=
  (K ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) * X *
    (K ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ

def rightKrausApplication (K : Matrix (Fin out) (Fin n) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    Matrix (Fin m × Fin out) (Fin m × Fin out) ℂ :=
  ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) * X *
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K)ᴴ

theorem leftKrausApplication_block (K : Matrix (Fin out) (Fin m) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (i j : Fin out) (r s : Fin n) :
    leftKrausApplication K X (i, r) (j, s) =
      (K * Matrix.of (fun a b => X (a, r) (b, s)) * Kᴴ) i j := by
  simp [leftKrausApplication, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fintype.sum_prod_type, apply_ite, mul_ite, ite_mul]

theorem rightKrausApplication_block (K : Matrix (Fin out) (Fin n) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (r s : Fin m) (i j : Fin out) :
    rightKrausApplication K X (r, i) (s, j) =
      (K * Matrix.of (fun a b => X (r, a) (s, b)) * Kᴴ) i j :=
  ancillaryKraus_block m K X r s i j

theorem leftApplication_eq_kraus
    (Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin out) (Fin out) ℂ)
    (hΦ : CompletelyPositive Φ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    leftApplication Φ X = ∑ q : Fin m × Fin out,
      leftKrausApplication (krausOperator Φ q) X := by
  ext ⟨i, r⟩ ⟨j, s⟩
  change Φ (Matrix.of (fun a b => X (a, r) (b, s))) i j = _
  rw [completelyPositive_apply_eq_sum Φ hΦ]
  simp only [Matrix.sum_apply, leftKrausApplication_block]

theorem rightApplication_eq_kraus
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin out) (Fin out) ℂ)
    (hΦ : CompletelyPositive Φ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    rightApplication Φ X = ∑ q : Fin n × Fin out,
      rightKrausApplication (krausOperator Φ q) X := by
  ext ⟨r, i⟩ ⟨s, j⟩
  change Φ (Matrix.of (fun a b => X (r, a) (s, b))) i j = _
  rw [completelyPositive_apply_eq_sum Φ hΦ]
  simp only [Matrix.sum_apply, rightKrausApplication_block]

section HiddenLabels

variable {S : Type*} [Fintype S]

theorem sum_left_reported_evaluation
    (Φ : S → Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin out) (Fin out) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (f : S → Matrix (Fin out × Fin n) (Fin out × Fin n) ℂ →ₗ[ℂ] ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (∑ s, f s (leftApplication (Φ s) X)) =
      ∑ r, f (finInstrumentReport r) (leftKrausApplication (finInstrumentKraus Φ r) X) := by
  calc
    _ = ∑ s, ∑ q : Fin m × Fin out,
        f s (leftKrausApplication (krausOperator (Φ s) q) X) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [leftApplication_eq_kraus (Φ s) (hΦ s), map_sum]
    _ = ∑ q : S × (Fin m × Fin out),
        f q.1 (leftKrausApplication (instrumentKraus Φ q) X) := by
      simp only [Fintype.sum_prod_type, instrumentKraus]
    _ = _ := by
      simpa only [finInstrumentKraus, finInstrumentReport] using
        ((Fintype.equivFin (S × (Fin m × Fin out))).symm.sum_comp
          (fun q => f q.1 (leftKrausApplication (instrumentKraus Φ q) X))).symm

theorem sum_right_reported_evaluation
    (Φ : S → Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin out) (Fin out) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (f : S → Matrix (Fin m × Fin out) (Fin m × Fin out) ℂ →ₗ[ℂ] ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (∑ s, f s (rightApplication (Φ s) X)) =
      ∑ r, f (finInstrumentReport r) (rightKrausApplication (finInstrumentKraus Φ r) X) := by
  calc
    _ = ∑ s, ∑ q : Fin n × Fin out,
        f s (rightKrausApplication (krausOperator (Φ s) q) X) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [rightApplication_eq_kraus (Φ s) (hΦ s), map_sum]
    _ = ∑ q : S × (Fin n × Fin out),
        f q.1 (rightKrausApplication (instrumentKraus Φ q) X) := by
      simp only [Fintype.sum_prod_type, instrumentKraus]
    _ = _ := by
      simpa only [finInstrumentKraus, finInstrumentReport] using
        ((Fintype.equivFin (S × (Fin n × Fin out))).symm.sum_comp
          (fun q => f q.1 (rightKrausApplication (instrumentKraus Φ q) X))).symm

end HiddenLabels

theorem productEffect_trace_precomposeLeft
    (q : QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair out n) (K : Matrix (Fin out) (Fin m) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    ((q.precomposeLeft K).productEffect * X).trace =
      (q.productEffect * leftKrausApplication K X).trace := by
  rw [q.productEffect_precomposeLeft]
  unfold leftKrausApplication
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem productEffect_trace_precomposeRight
    (q : QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair m out) (K : Matrix (Fin out) (Fin n) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    ((q.precomposeRight K).productEffect * X).trace =
      (q.productEffect * rightKrausApplication K X).trace := by
  rw [q.productEffect_precomposeRight]
  unfold rightKrausApplication
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

namespace FiniteLocalCPInstrumentTree

universe u

@[reducible] def LeafLabels : {m n : ℕ} → FiniteLocalCPInstrumentTree m n → Type u → Type u
  | _, _, .leaf _ _, L => L
  | _, _, .alice _ _ _ _ _ _ _ next, L => ∀ s, LeafLabels (next s) L
  | _, _, .bob _ _ _ _ _ _ _ next, L => ∀ s, LeafLabels (next s) L

variable {L : Type u}

def matrixReportedEvaluation [DecidableEq L] : {m n : ℕ} → (T : FiniteLocalCPInstrumentTree m n) →
    LeafLabels T L → L → (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℂ] ℂ)
  | _, _, .leaf m n, labels, ell =>
      if labels = ell then Matrix.traceLinearMap (Fin m × Fin n) ℂ ℂ else 0
  | _, _, .alice _ _ _ _ Φ _ _ next, labels, ell =>
      ∑ s, (matrixReportedEvaluation (next s) (labels s) ell).comp (leftApplication (Φ s))
  | _, _, .bob _ _ _ _ Φ _ _ next, labels, ell =>
      ∑ s, (matrixReportedEvaluation (next s) (labels s) ell).comp (rightApplication (Φ s))

def reportedTerminalBraPairs : {m n : ℕ} → (T : FiniteLocalCPInstrumentTree m n) →
    LeafLabels T L → List (QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair m n × L)
  | _, _, .leaf m n, labels =>
      ((QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree.leaf m n).terminalBraPairs).map (fun q => (q, labels))
  | _, _, .alice _ _ _ _ Φ _ _ next, labels =>
      (List.ofFn fun r =>
        (reportedTerminalBraPairs (next (finInstrumentReport r))
          (labels (finInstrumentReport r))).map
          (fun p => (p.1.precomposeLeft (finInstrumentKraus Φ r), p.2))).flatten
  | _, _, .bob _ _ _ _ Φ _ _ next, labels =>
      (List.ofFn fun r =>
        (reportedTerminalBraPairs (next (finInstrumentReport r))
          (labels (finInstrumentReport r))).map
          (fun p => (p.1.precomposeRight (finInstrumentKraus Φ r), p.2))).flatten

variable [DecidableEq L]

def labelledEffectEvaluation (l : List (QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair m n × L))
    (ell : L) (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : ℂ :=
  (l.map (fun p => if p.2 = ell then (p.1.productEffect * X).trace else 0)).sum

theorem map_fst_precomposeLeft
    (l : List (QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair out n × L))
    (K : Matrix (Fin out) (Fin m) ℂ) :
    (l.map (fun p => (p.1.precomposeLeft K, p.2))).map Prod.fst =
      (l.map Prod.fst).map (fun q => q.precomposeLeft K) := by
  simp only [List.map_map, Function.comp_def]

theorem map_fst_precomposeRight
    (l : List (QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair m out × L))
    (K : Matrix (Fin out) (Fin n) ℂ) :
    (l.map (fun p => (p.1.precomposeRight K, p.2))).map Prod.fst =
      (l.map Prod.fst).map (fun q => q.precomposeRight K) := by
  simp only [List.map_map, Function.comp_def]

theorem reportedTerminalBraPairs_fst (T : FiniteLocalCPInstrumentTree m n) :
    ∀ labels : LeafLabels T L,
      (T.reportedTerminalBraPairs labels).map Prod.fst = T.krausRefinement.terminalBraPairs := by
  induction T with
  | leaf m n =>
    intro labels
    simp [reportedTerminalBraPairs, krausRefinement, List.map_map, Function.comp_def]
  | alice m n out outcomes Φ positive trace next ih =>
    intro labels
    simp only [reportedTerminalBraPairs, krausRefinement, cpAliceNode,
      QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree.terminalBraPairs, List.map_flatten, List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext r
    simp only [Function.comp_def]
    rw [map_fst_precomposeLeft, ih (finInstrumentReport r) (labels (finInstrumentReport r))]
  | bob m n out outcomes Φ positive trace next ih =>
    intro labels
    simp only [reportedTerminalBraPairs, krausRefinement, cpBobNode,
      QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree.terminalBraPairs, List.map_flatten, List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext r
    simp only [Function.comp_def]
    rw [map_fst_precomposeRight, ih (finInstrumentReport r) (labels (finInstrumentReport r))]

theorem list_trace_product_sum
    (l : List (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ))
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (l.map (fun E => (E * X).trace)).sum = (l.sum * X).trace := by
  induction l with
  | nil => simp
  | cons E l ih => simp [List.map_cons, List.sum_cons, Matrix.add_mul, ih]

theorem list_bra_trace_sum (l : List (QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair m n))
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (l.map (fun q => (q.productEffect * X).trace)).sum =
      ((l.map QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair.productEffect).sum * X).trace := by
  simpa only [List.map_map, Function.comp_def] using
    list_trace_product_sum (l.map QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair.productEffect) X

theorem matrixReportedEvaluation_eq_labelledEffects (T : FiniteLocalCPInstrumentTree m n) :
    ∀ (labels : LeafLabels T L) (ell : L)
      (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
      T.matrixReportedEvaluation labels ell X =
        labelledEffectEvaluation (T.reportedTerminalBraPairs labels) ell X := by
  induction T with
  | leaf m n =>
    intro labels ell X
    by_cases h : labels = ell
    · simp only [matrixReportedEvaluation, if_pos h, Matrix.traceLinearMap_apply,
        labelledEffectEvaluation, reportedTerminalBraPairs, List.map_map,
        Function.comp_def, if_pos h]
      rw [list_bra_trace_sum]
      change X.trace =
        ((QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree.leaf m n).terminalProductEffect * X).trace
      rw [QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree.terminalProductEffect_eq_one, Matrix.one_mul]
    · simp [matrixReportedEvaluation, labelledEffectEvaluation, reportedTerminalBraPairs,
        h, Function.comp_def]
  | alice m n out outcomes Φ positive trace next ih =>
    intro labels ell X
    simp only [matrixReportedEvaluation, LinearMap.sum_apply, LinearMap.comp_apply]
    rw [sum_left_reported_evaluation Φ positive
      (fun s => (next s).matrixReportedEvaluation (labels s) ell) X]
    simp only [labelledEffectEvaluation, reportedTerminalBraPairs,
      List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn,
      List.sum_ofFn, Function.comp_def]
    apply Finset.sum_congr rfl
    intro r _
    rw [ih (finInstrumentReport r) (labels (finInstrumentReport r)) ell]
    simp only [labelledEffectEvaluation, productEffect_trace_precomposeLeft]
  | bob m n out outcomes Φ positive trace next ih =>
    intro labels ell X
    simp only [matrixReportedEvaluation, LinearMap.sum_apply, LinearMap.comp_apply]
    rw [sum_right_reported_evaluation Φ positive
      (fun s => (next s).matrixReportedEvaluation (labels s) ell) X]
    simp only [labelledEffectEvaluation, reportedTerminalBraPairs,
      List.map_flatten, List.sum_flatten, List.map_map, List.map_ofFn,
      List.sum_ofFn, Function.comp_def]
    apply Finset.sum_congr rfl
    intro r _
    rw [ih (finInstrumentReport r) (labels (finInstrumentReport r)) ell]
    simp only [labelledEffectEvaluation, productEffect_trace_precomposeRight]

theorem reportedTerminalBraPairs_length (T : FiniteLocalCPInstrumentTree m n)
    (labels : LeafLabels T L) :
    (T.reportedTerminalBraPairs labels).length = T.krausRefinement.terminalBraPairs.length := by
  simpa using congrArg List.length (T.reportedTerminalBraPairs_fst labels)

def terminalOccurrence (T : FiniteLocalCPInstrumentTree m n) (labels : LeafLabels T L)
    (i : Fin T.krausRefinement.terminalBraPairs.length) :
    Fin (T.reportedTerminalBraPairs labels).length :=
  (finCongr (T.reportedTerminalBraPairs_length labels)).symm i

def terminalReport (T : FiniteLocalCPInstrumentTree m n) (labels : LeafLabels T L)
    (i : Fin T.krausRefinement.terminalBraPairs.length) : L :=
  ((T.reportedTerminalBraPairs labels).get (T.terminalOccurrence labels i)).2

theorem terminalOccurrence_val (T : FiniteLocalCPInstrumentTree m n)
    (labels : LeafLabels T L) (i : Fin T.krausRefinement.terminalBraPairs.length) :
    (T.terminalOccurrence labels i).val = i.val := by
  simp [terminalOccurrence]

theorem reportedTerminalBraPairs_get_fst (T : FiniteLocalCPInstrumentTree m n)
    (labels : LeafLabels T L) (i : Fin T.krausRefinement.terminalBraPairs.length) :
    ((T.reportedTerminalBraPairs labels).get (T.terminalOccurrence labels i)).1 =
      T.krausRefinement.terminalBraPairs.get i := by
  have hi : i.val < (T.reportedTerminalBraPairs labels).length := by
    rw [T.reportedTerminalBraPairs_length labels]
    exact i.isLt
  have h := congrArg (fun l : List (QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair m n) => l[i.val]?)
    (T.reportedTerminalBraPairs_fst labels)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem i.isLt, Option.map_some, Option.some.injEq] at h
  simpa only [List.get_eq_getElem, terminalOccurrence_val] using h

theorem sum_get_map {α M : Type*} [AddCommMonoid M] (l : List α) (g : α → M) :
    (∑ i : Fin l.length, g (l.get i)) = (l.map g).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn (g ∘ l.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]

theorem matrixReportedEvaluation_eq_terminalEffects
    (T : FiniteLocalCPInstrumentTree m n) (labels : LeafLabels T L) (ell : L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    T.matrixReportedEvaluation labels ell X =
      ∑ i : Fin T.krausRefinement.terminalBraPairs.length,
        if T.terminalReport labels i = ell then
          ((T.krausRefinement.terminalBraPairs.get i).productEffect * X).trace else 0 := by
  calc
    _ = ∑ i : Fin (T.reportedTerminalBraPairs labels).length,
        if ((T.reportedTerminalBraPairs labels).get i).2 = ell then
          (((T.reportedTerminalBraPairs labels).get i).1.productEffect * X).trace else 0 := by
      rw [T.matrixReportedEvaluation_eq_labelledEffects labels ell X]
      exact (sum_get_map _ _).symm
    _ = ∑ i : Fin T.krausRefinement.terminalBraPairs.length,
        if ((T.reportedTerminalBraPairs labels).get (T.terminalOccurrence labels i)).2 = ell then
          (((T.reportedTerminalBraPairs labels).get (T.terminalOccurrence labels i)).1.productEffect * X).trace
        else 0 :=
      ((finCongr (T.reportedTerminalBraPairs_length labels)).symm.sum_comp
        (fun i => if ((T.reportedTerminalBraPairs labels).get i).2 = ell then
          (((T.reportedTerminalBraPairs labels).get i).1.productEffect * X).trace else 0)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [T.reportedTerminalBraPairs_get_fst labels i]
      rfl

def matrixReportedEffect (T : FiniteLocalCPInstrumentTree m n)
    (labels : LeafLabels T L) (ell : L) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  ∑ i : Fin T.krausRefinement.terminalBraPairs.length,
    if T.terminalReport labels i = ell then
      (T.krausRefinement.terminalBraPairs.get i).productEffect else 0

theorem matrixReportedEvaluation_eq_trace_effect
    (T : FiniteLocalCPInstrumentTree m n) (labels : LeafLabels T L) (ell : L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    T.matrixReportedEvaluation labels ell X = (T.matrixReportedEffect labels ell * X).trace := by
  rw [T.matrixReportedEvaluation_eq_terminalEffects labels ell X]
  simp only [matrixReportedEffect, Matrix.sum_mul, Matrix.trace_sum,
    ite_mul, Matrix.zero_mul, apply_ite, Matrix.trace_zero]

def matrixBornProbability (T : FiniteLocalCPInstrumentTree m n)
    (labels : LeafLabels T L) (ell : L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : ℝ :=
  (T.matrixReportedEvaluation labels ell X).re

theorem matrixBornProbability_eq_terminalEffects
    (T : FiniteLocalCPInstrumentTree m n) (labels : LeafLabels T L) (ell : L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    T.matrixBornProbability labels ell X =
      ∑ i : Fin T.krausRefinement.terminalBraPairs.length,
        if T.terminalReport labels i = ell then
          ((T.krausRefinement.terminalBraPairs.get i).productEffect * X).trace.re else 0 := by
  simpa only [matrixBornProbability, Complex.re_sum, apply_ite, Complex.zero_re] using
    congrArg Complex.re (T.matrixReportedEvaluation_eq_terminalEffects labels ell X)

theorem matrixReportedEffect_posSemidef (T : FiniteLocalCPInstrumentTree m n)
    (labels : LeafLabels T L) (ell : L) : (T.matrixReportedEffect labels ell).PosSemidef := by
  unfold matrixReportedEffect
  apply Matrix.nonneg_iff_posSemidef.mp
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact (T.krausRefinement.terminalBraPairs.get i).productEffect_posSemidef.nonneg
  · exact le_rfl

theorem sum_matrixReportedEffect [Fintype L] (T : FiniteLocalCPInstrumentTree m n)
    (labels : LeafLabels T L) : ∑ ell, T.matrixReportedEffect labels ell = 1 := by
  calc
    _ = ∑ i : Fin T.krausRefinement.terminalBraPairs.length,
        (T.krausRefinement.terminalBraPairs.get i).productEffect := by
      unfold matrixReportedEffect
      rw [Finset.sum_comm]
      simp [eq_comm]
    _ = (T.krausRefinement.terminalBraPairs.map
        QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair.productEffect).sum := sum_get_map _ _
    _ = 1 := T.krausRefinement.terminalProductEffect_eq_one

theorem matrixReportedEffect_unique (T : FiniteLocalCPInstrumentTree m n)
    (labels : LeafLabels T L) (ell : L)
    (F : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hF : ∀ X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      (F * X).trace = T.matrixReportedEvaluation labels ell X) :
    F = T.matrixReportedEffect labels ell := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [← T.matrixReportedEvaluation_eq_trace_effect labels ell X]
  exact hF X

open scoped Matrix.Norms.L2Operator

theorem trace_product_posSemidef_nonneg
    (E X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hE : E.PosSemidef) (hX : X.PosSemidef) : 0 ≤ (E * X).trace := by
  let S := CFC.sqrt X
  have hs : Sᴴ = S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X)).isHermitian
  have hsq : S * S = X := by
    simpa only [S, pow_two] using CFC.sq_sqrt X hX.nonneg
  have h := (hE.mul_mul_conjTranspose_same S).trace_nonneg
  rw [hs] at h
  rw [← hsq, ← Matrix.mul_assoc, Matrix.trace_mul_cycle E S S]
  exact h

theorem matrixBornProbability_nonneg (T : FiniteLocalCPInstrumentTree m n)
    (labels : LeafLabels T L) (ell : L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hX : X.PosSemidef) :
    0 ≤ T.matrixBornProbability labels ell X := by
  unfold matrixBornProbability
  rw [T.matrixReportedEvaluation_eq_trace_effect labels ell X]
  exact (Complex.nonneg_iff.mp
    (trace_product_posSemidef_nonneg _ X (T.matrixReportedEffect_posSemidef labels ell) hX)).1

theorem matrixReportedEvaluation_im_eq_zero (T : FiniteLocalCPInstrumentTree m n)
    (labels : LeafLabels T L) (ell : L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hX : X.PosSemidef) :
    (T.matrixReportedEvaluation labels ell X).im = 0 := by
  rw [T.matrixReportedEvaluation_eq_trace_effect labels ell X]
  exact (Complex.nonneg_iff.mp
    (trace_product_posSemidef_nonneg _ X (T.matrixReportedEffect_posSemidef labels ell) hX)).2.symm

theorem sum_matrixBornProbability [Fintype L] (T : FiniteLocalCPInstrumentTree m n)
    (labels : LeafLabels T L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (∑ ell, T.matrixBornProbability labels ell X) = X.trace.re := by
  unfold matrixBornProbability
  simp_rw [T.matrixReportedEvaluation_eq_trace_effect labels]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul,
    T.sum_matrixReportedEffect labels, Matrix.one_mul]

theorem sum_matrixBornProbability_density [Fintype L]
    (T : FiniteLocalCPInstrumentTree m n) (labels : LeafLabels T L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (htrace : X.trace = 1) :
    (∑ ell, T.matrixBornProbability labels ell X) = 1 := by
  rw [T.sum_matrixBornProbability labels X, htrace]
  rfl

end FiniteLocalCPInstrumentTree

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

noncomputable section

section Composition

variable {I O P : Type*} [Fintype I] [Fintype O] [Fintype P]
  [DecidableEq I] [DecidableEq O] [DecidableEq P]

theorem amplification_comp (Ψ : Matrix O O ℂ →ₗ[ℂ] Matrix P P ℂ)
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (k : ℕ)
    (X : Matrix (Fin k × I) (Fin k × I) ℂ) :
    amplification (Ψ.comp Φ) k X = amplification Ψ k (amplification Φ k X) := rfl

theorem CompletelyPositive.comp
    {Ψ : Matrix O O ℂ →ₗ[ℂ] Matrix P P ℂ}
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΨ : CompletelyPositive Ψ) (hΦ : CompletelyPositive Φ) :
    CompletelyPositive (Ψ.comp Φ) := by
  intro k X hX
  rw [amplification_comp]
  exact hΨ k _ (hΦ k X hX)

def sandwichMap (K : Matrix O I ℂ) : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ :=
  krausMap (fun _ : Unit => K)

theorem sandwichMap_apply (K : Matrix O I ℂ) (X : Matrix I I ℂ) :
    sandwichMap K X = K * X * Kᴴ := by
  change (∑ _ : Unit, K * X * Kᴴ) = _
  simp

theorem sandwichMap_completelyPositive (K : Matrix O I ℂ) :
    CompletelyPositive (sandwichMap K) := krausMap_completelyPositive _

theorem kraus_sandwich_comp (K : Matrix P O ℂ) (E : Matrix O I ℂ)
    (X : Matrix I I ℂ) :
    K * (E * X * Eᴴ) * Kᴴ = (K * E) * X * (K * E)ᴴ := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end Composition

variable {d D m : ℕ}

def inclusionMatrix (h : d ≤ D) : Matrix (Fin D) (Fin d) ℂ :=
  fun i j => if i = Fin.castLE h j then 1 else 0

theorem inclusionMatrix_isometry (h : d ≤ D) :
    (inclusionMatrix h)ᴴ * inclusionMatrix h = 1 := by
  have hinj : Function.Injective (Fin.castLE h) := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun z : Fin D => z.val) hij
  ext i j
  simp [Matrix.mul_apply, inclusionMatrix, Matrix.conjTranspose_apply,
    Matrix.one_apply, hinj.eq_iff, apply_ite, mul_ite, ite_mul, ite_and, eq_comm]

theorem inclusionMatrix_projection_apply (h : d ≤ D) (i j : Fin D) :
    (inclusionMatrix h * (inclusionMatrix h)ᴴ) i j =
      if i = j ∧ i.val < d then 1 else 0 := by
  by_cases hi : i.val < d
  · let a : Fin d := ⟨i.val, hi⟩
    have hea : Fin.castLE h a = i := Fin.ext rfl
    have hieq (b : Fin d) : i = Fin.castLE h b ↔ a = b := by
      constructor
      · intro he
        apply Fin.ext
        exact congrArg (fun z : Fin D => z.val) he
      · intro he
        simpa [← he] using hea.symm
    have hterm (b : Fin d) :
        inclusionMatrix h i b * conj (inclusionMatrix h j b) =
          if b = a then (if i = j then 1 else 0) else 0 := by
      by_cases hb : b = a
      · subst b
        simp [inclusionMatrix, hea, eq_comm]
      · have hn : i ≠ Fin.castLE h b := by
          intro he
          exact hb ((hieq b).mp he).symm
        simp [inclusionMatrix, hn, hb]
    change (∑ b, inclusionMatrix h i b * conj (inclusionMatrix h j b)) = _
    simp_rw [hterm]
    simp [hi]
  · have hne (b : Fin d) : i ≠ Fin.castLE h b := by
      intro he
      apply hi
      simpa only [he, Fin.val_castLE] using b.isLt
    simp [Matrix.mul_apply, inclusionMatrix, Matrix.conjTranspose_apply,
      hne, hi, apply_ite]

def padMap (h : d ≤ D)
    (Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  (sandwichMap (inclusionMatrix h)).comp Φ

theorem padMap_apply (h : d ≤ D)
    (Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    padMap h Φ X = inclusionMatrix h * Φ X * (inclusionMatrix h)ᴴ :=
  sandwichMap_apply _ _

theorem padMap_completelyPositive (h : d ≤ D)
    (Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hΦ : CompletelyPositive Φ) : CompletelyPositive (padMap h Φ) :=
  (sandwichMap_completelyPositive _).comp hΦ

theorem padMap_trace (h : d ≤ D)
    (Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) : (padMap h Φ X).trace = (Φ X).trace := by
  rw [padMap_apply, Matrix.trace_mul_cycle, inclusionMatrix_isometry, Matrix.one_mul]

def unpadFallback (hd : 0 < d) (j : Fin D) : Matrix (Fin d) (Fin D) ℂ :=
  if j.val < d then 0 else Matrix.single (⟨0, hd⟩ : Fin d) j 1

def unpadKraus (hd : 0 < d) (h : d ≤ D) : Unit ⊕ Fin D → Matrix (Fin d) (Fin D) ℂ
  | .inl _ => (inclusionMatrix h)ᴴ
  | .inr j => unpadFallback hd j

theorem unpadFallback_gram (hd : 0 < d) (j : Fin D) :
    (unpadFallback hd j)ᴴ * unpadFallback hd j =
      if j.val < d then 0 else Matrix.single j j (1 : ℂ) := by
  by_cases hj : j.val < d
  · simp [unpadFallback, hj]
  · simp only [unpadFallback, if_neg hj, Matrix.conjTranspose_single, star_one,
      Matrix.single_mul_single_same, one_mul]

theorem unpadFallback_mul_inclusion (hd : 0 < d) (h : d ≤ D) (j : Fin D) :
    unpadFallback hd j * inclusionMatrix h = 0 := by
  by_cases hj : j.val < d
  · simp [unpadFallback, hj]
  · have hrow (b : Fin d) : inclusionMatrix h j b = 0 := by
      have hne : j ≠ Fin.castLE h b := by
        intro he
        apply hj
        simpa only [he, Fin.val_castLE] using b.isLt
      simp [inclusionMatrix, hne]
    ext a b
    simp [unpadFallback, hj, Matrix.mul_apply, Matrix.single_apply,
      ite_and, mul_ite, ite_mul, hrow]

theorem unpadKraus_complete (hd : 0 < d) (h : d ≤ D) :
    ∑ q : Unit ⊕ Fin D, (unpadKraus hd h q)ᴴ * unpadKraus hd h q = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [unpadKraus, Fintype.sum_unique, Matrix.conjTranspose_conjTranspose,
    unpadFallback_gram]
  ext i j
  have hf : (∑ k : Fin D, if k.val < d then (0 : Matrix (Fin D) (Fin D) ℂ)
      else Matrix.single k k 1) i j =
      if i.val < d then 0 else (if i = j then 1 else 0) := by
    rw [Matrix.sum_apply]
    calc
      (∑ k : Fin D, (if k.val < d then (0 : Matrix (Fin D) (Fin D) ℂ)
          else Matrix.single k k 1) i j) =
          (if i.val < d then (0 : Matrix (Fin D) (Fin D) ℂ)
          else Matrix.single i i 1) i j := by
        apply Finset.sum_eq_single i
        · intro k _ hki
          by_cases hk : k.val < d
          · simp only [if_pos hk, Matrix.zero_apply]
          · simp only [if_neg hk, Matrix.single_apply, hki, false_and, if_false]
        · simp
      _ = _ := by
        by_cases hi : i.val < d
        · simp only [if_pos hi, Matrix.zero_apply]
        · simp only [if_neg hi, Matrix.single_apply, true_and]
  rw [Matrix.add_apply, inclusionMatrix_projection_apply, hf]
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val < d <;> simp [Matrix.one_apply, hi]
  · simp [Matrix.one_apply, hij]

def unpadMap (hd : 0 < d) (h : d ≤ D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  krausMap (unpadKraus hd h)

theorem unpadMap_completelyPositive (hd : 0 < d) (h : d ≤ D) :
    CompletelyPositive (unpadMap hd h) := krausMap_completelyPositive _

theorem unpadMap_trace_preserving (hd : 0 < d) (h : d ≤ D)
    (X : Matrix (Fin D) (Fin D) ℂ) : (unpadMap hd h X).trace = X.trace :=
  (krausMap_trace_preserving_iff (unpadKraus hd h)).mpr (unpadKraus_complete hd h) X

theorem unpadMap_recover (hd : 0 < d) (h : d ≤ D)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    unpadMap hd h (inclusionMatrix h * X * (inclusionMatrix h)ᴴ) = X := by
  change (∑ q : Unit ⊕ Fin D,
    unpadKraus hd h q * (inclusionMatrix h * X * (inclusionMatrix h)ᴴ) *
      (unpadKraus hd h q)ᴴ) = X
  simp_rw [kraus_sandwich_comp]
  rw [Fintype.sum_sum_type]
  simp only [unpadKraus, Fintype.sum_unique, inclusionMatrix_isometry,
    unpadFallback_mul_inclusion, Matrix.one_mul, Matrix.conjTranspose_one,
    Matrix.mul_one, Matrix.zero_mul, Matrix.conjTranspose_zero, Matrix.mul_zero,
    Finset.sum_const_zero, add_zero]

theorem unpadMap_padMap (hd : 0 < d) (h : d ≤ D)
    (Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) : unpadMap hd h (padMap h Φ X) = Φ X := by
  rw [padMap_apply, unpadMap_recover]

theorem padMap_zero_output (h : 0 ≤ D)
    (Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin 0) (Fin 0) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) : padMap h Φ X = 0 := by
  rw [padMap_apply]
  ext i j
  simp [Matrix.mul_apply]

theorem no_tracePreserving_map_to_zero (hD : 0 < D)
    (Φ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin 0) (Fin 0) ℂ) :
    ¬ (∀ X : Matrix (Fin D) (Fin D) ℂ, (Φ X).trace = X.trace) := by
  intro h
  have hs := h (Matrix.single (⟨0, hD⟩ : Fin D) ⟨0, hD⟩ 1)
  simpa using hs

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix

noncomputable section

variable {S : Type*} [Fintype S] {m n d D p : ℕ}

def commonOutputDimension (dims : S → ℕ) : ℕ := 1 + ∑ s, dims s

theorem le_commonOutputDimension (dims : S → ℕ) (s : S) :
    dims s ≤ commonOutputDimension dims := by
  have h : dims s ≤ ∑ t, dims t :=
    Finset.single_le_sum (fun t _ => Nat.zero_le (dims t)) (Finset.mem_univ s)
  unfold commonOutputDimension
  omega

def paddedInstrument (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ) :
    S → Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ]
      Matrix (Fin (commonOutputDimension dims)) (Fin (commonOutputDimension dims)) ℂ :=
  fun s => padMap (le_commonOutputDimension dims s) (Φ s)

theorem paddedInstrument_completelyPositive (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (s : S) :
    CompletelyPositive (paddedInstrument dims Φ s) :=
  padMap_completelyPositive _ _ (hΦ s)

theorem paddedInstrument_trace_preserving (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, (∑ s, (Φ s X).trace) = X.trace)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    (∑ s, paddedInstrument dims Φ s X).trace = X.trace := by
  rw [Matrix.trace_sum]
  simp only [paddedInstrument, padMap_trace]
  exact htrace X

theorem leftApplication_comp
    (Ψ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    leftApplication (Ψ.comp Φ) X = leftApplication Ψ (leftApplication Φ X) := rfl

theorem rightApplication_comp
    (Ψ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    rightApplication (Ψ.comp Φ) X = rightApplication Ψ (rightApplication Φ X) := rfl

theorem left_unpad_padded_application (hd : 0 < d) (h : d ≤ D)
    (Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    leftApplication (unpadMap hd h) (leftApplication (padMap h Φ) X) = leftApplication Φ X := by
  have heq : (unpadMap hd h).comp (padMap h Φ) = Φ := by
    apply LinearMap.ext
    intro M
    exact unpadMap_padMap hd h Φ M
  rw [← leftApplication_comp, heq]

theorem right_unpad_padded_application (hd : 0 < d) (h : d ≤ D)
    (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    rightApplication (unpadMap hd h) (rightApplication (padMap h Φ) X) = rightApplication Φ X := by
  have heq : (unpadMap hd h).comp (padMap h Φ) = Φ := by
    apply LinearMap.ext
    intro M
    exact unpadMap_padMap hd h Φ M
  rw [← rightApplication_comp, heq]

abbrev unpadAliceNode (hd : 0 < d) (h : d ≤ D)
    (next : FiniteLocalCPInstrumentTree d n) : FiniteLocalCPInstrumentTree D n :=
  .alice D n d 1 (fun _ => unpadMap hd h) (fun _ => unpadMap_completelyPositive hd h)
    (by intro X; simpa using unpadMap_trace_preserving hd h X) (fun _ => next)

abbrev unpadBobNode (hd : 0 < d) (h : d ≤ D)
    (next : FiniteLocalCPInstrumentTree m d) : FiniteLocalCPInstrumentTree m D :=
  .bob m D d 1 (fun _ => unpadMap hd h) (fun _ => unpadMap_completelyPositive hd h)
    (by intro X; simpa using unpadMap_trace_preserving hd h X) (fun _ => next)

inductive DependentOutputCPInstrumentTree : ℕ → ℕ → Type where
  | leaf (m n : ℕ) : DependentOutputCPInstrumentTree m n
  | alice (m n outcomes : ℕ) (dims : Fin outcomes → ℕ)
      (positiveDims : ∀ s, 0 < dims s)
      (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
      (positive : ∀ s, CompletelyPositive (Φ s))
      (trace : ∀ X : Matrix (Fin m) (Fin m) ℂ, (∑ s, (Φ s X).trace) = X.trace)
      (next : ∀ s, DependentOutputCPInstrumentTree (dims s) n) :
      DependentOutputCPInstrumentTree m n
  | bob (m n outcomes : ℕ) (dims : Fin outcomes → ℕ)
      (positiveDims : ∀ s, 0 < dims s)
      (Φ : ∀ s, Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
      (positive : ∀ s, CompletelyPositive (Φ s))
      (trace : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∑ s, (Φ s X).trace) = X.trace)
      (next : ∀ s, DependentOutputCPInstrumentTree m (dims s)) :
      DependentOutputCPInstrumentTree m n

namespace DependentOutputCPInstrumentTree

universe u

@[reducible] def LeafLabels : {m n : ℕ} → DependentOutputCPInstrumentTree m n → Type u → Type u
  | _, _, .leaf _ _, L => L
  | _, _, .alice _ _ _ _ _ _ _ _ next, L => ∀ s, LeafLabels (next s) L
  | _, _, .bob _ _ _ _ _ _ _ _ next, L => ∀ s, LeafLabels (next s) L

variable {L : Type u}

def matrixReportedEvaluation [DecidableEq L] : {m n : ℕ} →
    (T : DependentOutputCPInstrumentTree m n) → LeafLabels T L → L →
      (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ →ₗ[ℂ] ℂ)
  | _, _, .leaf m n, labels, ell =>
      if labels = ell then Matrix.traceLinearMap (Fin m × Fin n) ℂ ℂ else 0
  | _, _, .alice _ _ _ _ _ Φ _ _ next, labels, ell =>
      ∑ s, (matrixReportedEvaluation (next s) (labels s) ell).comp (leftApplication (Φ s))
  | _, _, .bob _ _ _ _ _ Φ _ _ next, labels, ell =>
      ∑ s, (matrixReportedEvaluation (next s) (labels s) ell).comp (rightApplication (Φ s))

def commonTree : {m n : ℕ} → DependentOutputCPInstrumentTree m n → FiniteLocalCPInstrumentTree m n
  | _, _, .leaf m n => .leaf m n
  | _, _, .alice m n outcomes dims hd Φ positive trace next =>
      .alice m n (commonOutputDimension dims) outcomes (paddedInstrument dims Φ)
        (paddedInstrument_completelyPositive dims Φ positive)
        (paddedInstrument_trace_preserving dims Φ trace)
        (fun s => unpadAliceNode (hd s) (le_commonOutputDimension dims s) (commonTree (next s)))
  | _, _, .bob m n outcomes dims hd Φ positive trace next =>
      .bob m n (commonOutputDimension dims) outcomes (paddedInstrument dims Φ)
        (paddedInstrument_completelyPositive dims Φ positive)
        (paddedInstrument_trace_preserving dims Φ trace)
        (fun s => unpadBobNode (hd s) (le_commonOutputDimension dims s) (commonTree (next s)))

def commonLabels : {m n : ℕ} → (T : DependentOutputCPInstrumentTree m n) →
    LeafLabels T L → FiniteLocalCPInstrumentTree.LeafLabels T.commonTree L
  | _, _, .leaf _ _, labels => labels
  | _, _, .alice _ _ _ _ _ _ _ _ next, labels => fun s _ => commonLabels (next s) (labels s)
  | _, _, .bob _ _ _ _ _ _ _ _ next, labels => fun s _ => commonLabels (next s) (labels s)

variable [DecidableEq L]

theorem matrixReportedEvaluation_eq_commonTree (T : DependentOutputCPInstrumentTree m n) :
    ∀ (labels : LeafLabels T L) (ell : L)
      (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
      T.matrixReportedEvaluation labels ell X =
        T.commonTree.matrixReportedEvaluation (T.commonLabels labels) ell X := by
  induction T with
  | leaf m n => intro labels ell X; rfl
  | alice m n outcomes dims hd Φ positive trace next ih =>
    intro labels ell X
    simp only [matrixReportedEvaluation, commonTree, commonLabels,
      FiniteLocalCPInstrumentTree.matrixReportedEvaluation,
      LinearMap.sum_apply, LinearMap.comp_apply, Fin.sum_univ_one]
    simp_rw [paddedInstrument, left_unpad_padded_application]
    apply Finset.sum_congr rfl
    intro s _
    exact ih s (labels s) ell (leftApplication (Φ s) X)
  | bob m n outcomes dims hd Φ positive trace next ih =>
    intro labels ell X
    simp only [matrixReportedEvaluation, commonTree, commonLabels,
      FiniteLocalCPInstrumentTree.matrixReportedEvaluation,
      LinearMap.sum_apply, LinearMap.comp_apply, Fin.sum_univ_one]
    simp_rw [paddedInstrument, right_unpad_padded_application]
    apply Finset.sum_congr rfl
    intro s _
    exact ih s (labels s) ell (rightApplication (Φ s) X)

def terminalReport (T : DependentOutputCPInstrumentTree m n) (labels : LeafLabels T L) :
    Fin T.commonTree.krausRefinement.terminalBraPairs.length → L :=
  T.commonTree.terminalReport (T.commonLabels labels)

theorem matrixReportedEvaluation_eq_terminalEffects
    (T : DependentOutputCPInstrumentTree m n) (labels : LeafLabels T L) (ell : L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    T.matrixReportedEvaluation labels ell X =
      ∑ i : Fin T.commonTree.krausRefinement.terminalBraPairs.length,
        if T.terminalReport labels i = ell then
          ((T.commonTree.krausRefinement.terminalBraPairs.get i).productEffect * X).trace else 0 := by
  rw [T.matrixReportedEvaluation_eq_commonTree labels ell X]
  exact T.commonTree.matrixReportedEvaluation_eq_terminalEffects (T.commonLabels labels) ell X

theorem terminal_tail_cost_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (T : DependentOutputCPInstrumentTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (β : κ → ℝ) (k : κ) (t : ℝ) (ht : 0 < t) :
    (T.commonTree.krausRefinement.terminalBraPairs.map (fun q => q.tailCost ea eb β k)).sum ≤
      (2 * t) * QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget ((Real.sqrt t)⁻¹ •
        QuantumProver.ElegantJointMeasurement.Concurrence.physicalReferenceInput (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k)) :=
  T.commonTree.refined_terminal_tail_cost_le ea eb β k t ht

end DependentOutputCPInstrumentTree

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

noncomputable section

section SpectralAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {G : Matrix ι ι ℂ}

theorem spectralReal_mul (hG : G.IsHermitian) (f g : ℝ → ℝ) :
    hG.cfc f * hG.cfc g = hG.cfc (fun x => f x * g x) := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  apply congrArg Matrix.diagonal
  funext i
  simp [Function.comp_apply]

theorem spectralReal_hermitian (hG : G.IsHermitian) (f : ℝ → ℝ) :
    (hG.cfc f).IsHermitian := by
  change star (hG.cfc f) = hG.cfc f
  unfold Matrix.IsHermitian.cfc
  rw [← map_star]
  congr 1
  change (Matrix.diagonal (fun i => (f (hG.eigenvalues i) : ℂ)))ᴴ = _
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  · simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply, hij, Ne.symm hij]

theorem spectralReal_eq (hG : G.IsHermitian) (f g : ℝ → ℝ)
    (hfg : ∀ i, f (hG.eigenvalues i) = g (hG.eigenvalues i)) : hG.cfc f = hG.cfc g := by
  unfold Matrix.IsHermitian.cfc
  congr 1
  apply congrArg Matrix.diagonal
  funext i
  exact congrArg (fun x : ℝ => (x : ℂ)) (hfg i)

end SpectralAlgebra

variable {m p : ℕ}

def positiveInputKraus (K : Matrix (Fin p) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  CFC.sqrt (Kᴴ * K)

def rootPseudoInverse (K : Matrix (Fin p) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (Matrix.isHermitian_conjTranspose_mul_self K).cfc (fun x => (Real.sqrt x)⁻¹)

def supportGram (K : Matrix (Fin p) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (Matrix.isHermitian_conjTranspose_mul_self K).cfc
    (fun x => if Real.sqrt x = 0 then 0 else 1)

def complementGram (K : Matrix (Fin p) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 - supportGram K

theorem positiveInputKraus_posSemidef (K : Matrix (Fin p) (Fin m) ℂ) :
    (positiveInputKraus K).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Kᴴ * K))

theorem positiveInputKraus_square (K : Matrix (Fin p) (Fin m) ℂ) :
    positiveInputKraus K * positiveInputKraus K = Kᴴ * K := by
  rw [← pow_two]
  exact CFC.sq_sqrt (Kᴴ * K) (Matrix.posSemidef_conjTranspose_mul_self K).nonneg

theorem positiveInputKraus_spectral (K : Matrix (Fin p) (Fin m) ℂ) :
    positiveInputKraus K =
      (Matrix.isHermitian_conjTranspose_mul_self K).cfc Real.sqrt := by
  unfold positiveInputKraus
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ _
    (Matrix.posSemidef_conjTranspose_mul_self K).nonneg,
    (Matrix.isHermitian_conjTranspose_mul_self K).cfc_eq]
  apply spectralReal_eq
  intro i
  simp [Real.coe_sqrt, Real.coe_toNNReal',
    max_eq_left (Matrix.eigenvalues_conjTranspose_mul_self_nonneg K i)]

theorem rootPseudoInverse_hermitian (K : Matrix (Fin p) (Fin m) ℂ) :
    (rootPseudoInverse K).IsHermitian := spectralReal_hermitian _ _

theorem supportGram_hermitian (K : Matrix (Fin p) (Fin m) ℂ) :
    (supportGram K).IsHermitian := spectralReal_hermitian _ _

theorem supportGram_square (K : Matrix (Fin p) (Fin m) ℂ) :
    supportGram K * supportGram K = supportGram K := by
  unfold supportGram
  rw [spectralReal_mul]
  apply spectralReal_eq
  intro i
  by_cases h : Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self K).eigenvalues i) = 0 <;>
    simp [h]

theorem rootPseudoInverse_mul_positiveInput (K : Matrix (Fin p) (Fin m) ℂ) :
    rootPseudoInverse K * positiveInputKraus K = supportGram K := by
  rw [positiveInputKraus_spectral]
  unfold rootPseudoInverse supportGram
  rw [spectralReal_mul]
  apply spectralReal_eq
  intro i
  by_cases h : Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self K).eigenvalues i) = 0 <;>
    simp [h]

theorem supportGram_mul_positiveInput (K : Matrix (Fin p) (Fin m) ℂ) :
    supportGram K * positiveInputKraus K = positiveInputKraus K := by
  rw [positiveInputKraus_spectral]
  unfold supportGram
  rw [spectralReal_mul]
  apply spectralReal_eq
  intro i
  by_cases h : Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self K).eigenvalues i) = 0 <;>
    simp [h]

theorem rootPseudoInverse_gram_rootPseudoInverse (K : Matrix (Fin p) (Fin m) ℂ) :
    rootPseudoInverse K * (Kᴴ * K) * rootPseudoInverse K = supportGram K := by
  conv_lhs => rw [(Matrix.isHermitian_conjTranspose_mul_self K).spectral_theorem]
  change rootPseudoInverse K *
    (Matrix.isHermitian_conjTranspose_mul_self K).cfc (fun x => x) * rootPseudoInverse K = _
  unfold rootPseudoInverse supportGram
  rw [spectralReal_mul, spectralReal_mul]
  apply spectralReal_eq
  intro i
  have hn := Matrix.eigenvalues_conjTranspose_mul_self_nonneg K i
  by_cases h : Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self K).eigenvalues i) = 0
  · have hz : (Matrix.isHermitian_conjTranspose_mul_self K).eigenvalues i = 0 := by
      nlinarith [Real.mul_self_sqrt hn]
    simp [hz]
  · simp only [if_neg h]
    calc
      (Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self K).eigenvalues i))⁻¹ *
          (Matrix.isHermitian_conjTranspose_mul_self K).eigenvalues i *
          (Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self K).eigenvalues i))⁻¹ =
        (Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self K).eigenvalues i))⁻¹ *
          (Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self K).eigenvalues i) *
            Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self K).eigenvalues i)) *
          (Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self K).eigenvalues i))⁻¹ := by
        rw [Real.mul_self_sqrt hn]
      _ = 1 := by field_simp

theorem complementGram_hermitian (K : Matrix (Fin p) (Fin m) ℂ) :
    (complementGram K).IsHermitian := by
  unfold complementGram
  exact Matrix.isHermitian_one.sub (supportGram_hermitian K)

theorem complementGram_square (K : Matrix (Fin p) (Fin m) ℂ) :
    complementGram K * complementGram K = complementGram K := by
  unfold complementGram
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, supportGram_square]
  abel

theorem complementGram_mul_positiveInput (K : Matrix (Fin p) (Fin m) ℂ) :
    complementGram K * positiveInputKraus K = 0 := by
  rw [complementGram, Matrix.sub_mul, Matrix.one_mul, supportGram_mul_positiveInput, sub_self]

theorem positiveInput_mul_complementGram (K : Matrix (Fin p) (Fin m) ℂ) :
    positiveInputKraus K * complementGram K = 0 := by
  have h := congrArg Matrix.conjTranspose (complementGram_mul_positiveInput K)
  simpa only [Matrix.conjTranspose_mul, (positiveInputKraus_posSemidef K).isHermitian.eq,
    (complementGram_hermitian K).eq, Matrix.conjTranspose_zero] using h

theorem kraus_mul_complementGram (K : Matrix (Fin p) (Fin m) ℂ) :
    K * complementGram K = 0 := by
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  have hgram : (K * complementGram K)ᴴ * (K * complementGram K) =
      complementGram K * (Kᴴ * K) * complementGram K := by
    simp only [Matrix.conjTranspose_mul, (complementGram_hermitian K).eq, Matrix.mul_assoc]
  rw [hgram, ← positiveInputKraus_square, Matrix.mul_assoc, Matrix.mul_assoc,
    positiveInput_mul_complementGram, Matrix.mul_zero, Matrix.mul_zero, Matrix.trace_zero]

theorem kraus_mul_supportGram (K : Matrix (Fin p) (Fin m) ℂ) :
    K * supportGram K = K := by
  have h := kraus_mul_complementGram K
  rw [complementGram, Matrix.mul_sub, Matrix.mul_one] at h
  exact (sub_eq_zero.mp h).symm

def polarPartialIsometry (K : Matrix (Fin p) (Fin m) ℂ) : Matrix (Fin p) (Fin m) ℂ :=
  K * rootPseudoInverse K

theorem polarPartialIsometry_mul_positiveInput (K : Matrix (Fin p) (Fin m) ℂ) :
    polarPartialIsometry K * positiveInputKraus K = K := by
  rw [polarPartialIsometry, Matrix.mul_assoc, rootPseudoInverse_mul_positiveInput,
    kraus_mul_supportGram]

theorem polarPartialIsometry_gram (K : Matrix (Fin p) (Fin m) ℂ) :
    (polarPartialIsometry K)ᴴ * polarPartialIsometry K = supportGram K := by
  unfold polarPartialIsometry
  simp only [Matrix.conjTranspose_mul, (rootPseudoInverse_hermitian K).eq, Matrix.mul_assoc]
  simpa only [Matrix.mul_assoc] using rootPseudoInverse_gram_rootPseudoInverse K

def resetRow (hp : 0 < p) (j : Fin m) : Matrix (Fin p) (Fin m) ℂ :=
  Matrix.single (⟨0, hp⟩ : Fin p) j 1

theorem resetRow_gram (hp : 0 < p) (j : Fin m) :
    (resetRow hp j)ᴴ * resetRow hp j = Matrix.single j j (1 : ℂ) := by
  simp only [resetRow, Matrix.conjTranspose_single, star_one,
    Matrix.single_mul_single_same, one_mul]

theorem resetRow_complete (hp : 0 < p) :
    ∑ j : Fin m, (resetRow hp j)ᴴ * resetRow hp j = 1 := by
  simp_rw [resetRow_gram]
  ext a b
  rw [Matrix.sum_apply]
  calc
    (∑ j : Fin m, Matrix.single j j (1 : ℂ) a b) = Matrix.single a a (1 : ℂ) a b := by
      apply Finset.sum_eq_single a
      · intro j _ hja
        simp only [Matrix.single_apply, hja, false_and, if_false]
      · simp
    _ = _ := by simp [Matrix.single_apply, Matrix.one_apply]

theorem rightFactor_gram {o : ℕ} (A : Matrix (Fin o) (Fin m) ℂ)
    (Q : Matrix (Fin m) (Fin m) ℂ) :
    (A * Q)ᴴ * (A * Q) = Qᴴ * (Aᴴ * A) * Q := by
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

def rectangularRecoveryKraus (hp : 0 < p) (K : Matrix (Fin p) (Fin m) ℂ) :
    Unit ⊕ Fin m → Matrix (Fin p) (Fin m) ℂ
  | .inl _ => polarPartialIsometry K
  | .inr j => resetRow hp j * complementGram K

theorem rectangularRecoveryKraus_complete (hp : 0 < p) (K : Matrix (Fin p) (Fin m) ℂ) :
    ∑ q : Unit ⊕ Fin m, (rectangularRecoveryKraus hp K q)ᴴ *
      rectangularRecoveryKraus hp K q = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [rectangularRecoveryKraus, Fintype.sum_unique, polarPartialIsometry_gram]
  have hsum : (∑ j : Fin m, (resetRow hp j * complementGram K)ᴴ *
      (resetRow hp j * complementGram K)) = complementGram K := by
    simp_rw [rightFactor_gram]
    calc
      (∑ j : Fin m, (complementGram K)ᴴ * ((resetRow hp j)ᴴ * resetRow hp j) *
          complementGram K) =
        (complementGram K)ᴴ * (∑ j : Fin m, (resetRow hp j)ᴴ * resetRow hp j) *
          complementGram K := by rw [Finset.mul_sum, Finset.sum_mul]
      _ = complementGram K := by
        rw [resetRow_complete, complementGram_hermitian K, Matrix.mul_one, complementGram_square]
  rw [hsum, complementGram]
  abel

def rectangularRecovery (hp : 0 < p) (K : Matrix (Fin p) (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ :=
  krausMap (rectangularRecoveryKraus hp K)

theorem rectangularRecovery_completelyPositive (hp : 0 < p) (K : Matrix (Fin p) (Fin m) ℂ) :
    CompletelyPositive (rectangularRecovery hp K) := krausMap_completelyPositive _

theorem rectangularRecovery_trace_preserving (hp : 0 < p) (K : Matrix (Fin p) (Fin m) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) : (rectangularRecovery hp K X).trace = X.trace :=
  (krausMap_trace_preserving_iff _).mpr (rectangularRecoveryKraus_complete hp K) X

theorem rectangularRecovery_apply (hp : 0 < p) (K : Matrix (Fin p) (Fin m) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    rectangularRecovery hp K
      (positiveInputKraus K * X * (positiveInputKraus K)ᴴ) = K * X * Kᴴ := by
  change (∑ q : Unit ⊕ Fin m, rectangularRecoveryKraus hp K q *
    (positiveInputKraus K * X * (positiveInputKraus K)ᴴ) *
      (rectangularRecoveryKraus hp K q)ᴴ) = _
  simp_rw [kraus_sandwich_comp]
  rw [Fintype.sum_sum_type]
  simp only [rectangularRecoveryKraus, Fintype.sum_unique,
    polarPartialIsometry_mul_positiveInput, Matrix.mul_assoc,
    complementGram_mul_positiveInput, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.conjTranspose_zero, Finset.sum_const_zero, add_zero]

theorem positiveInputKraus_gram (K : Matrix (Fin p) (Fin m) ℂ) :
    (positiveInputKraus K)ᴴ * positiveInputKraus K = Kᴴ * K := by
  rw [(positiveInputKraus_posSemidef K).isHermitian, positiveInputKraus_square]

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

noncomputable section

variable {m p n : ℕ}

theorem rectangularRecovery_comp_sandwichMap (hp : 0 < p) (K : Matrix (Fin p) (Fin m) ℂ) :
    (rectangularRecovery hp K).comp (sandwichMap (positiveInputKraus K)) = sandwichMap K := by
  apply LinearMap.ext
  intro X
  simpa only [LinearMap.comp_apply, sandwichMap_apply] using rectangularRecovery_apply hp K X

theorem leftApplication_sandwichMap (K : Matrix (Fin p) (Fin m) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    leftApplication (sandwichMap K) X = leftKrausApplication K X := by
  ext a b
  rcases a with ⟨i, r⟩
  rcases b with ⟨j, s⟩
  change (sandwichMap K (Matrix.of (fun a b => X (a, r) (b, s)))) i j = _
  rw [sandwichMap_apply, leftKrausApplication_block]

theorem rightApplication_sandwichMap (K : Matrix (Fin p) (Fin n) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    rightApplication (sandwichMap K) X = rightKrausApplication K X := by
  ext a b
  rcases a with ⟨r, i⟩
  rcases b with ⟨s, j⟩
  change (sandwichMap K (Matrix.of (fun a b => X (r, a) (s, b)))) i j = _
  rw [sandwichMap_apply, rightKrausApplication_block]

theorem left_rectangularRecovery_branch (hp : 0 < p) (K : Matrix (Fin p) (Fin m) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    leftApplication (rectangularRecovery hp K) (leftKrausApplication (positiveInputKraus K) X) =
      leftKrausApplication K X := by
  simp_rw [← leftApplication_sandwichMap]
  rw [← leftApplication_comp, rectangularRecovery_comp_sandwichMap]

theorem right_rectangularRecovery_branch (hp : 0 < p) (K : Matrix (Fin p) (Fin n) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    rightApplication (rectangularRecovery hp K) (rightKrausApplication (positiveInputKraus K) X) =
      rightKrausApplication K X := by
  simp_rw [← rightApplication_sandwichMap]
  rw [← rightApplication_comp, rectangularRecovery_comp_sandwichMap]

theorem positiveInputKraus_branch_trace (K : Matrix (Fin p) (Fin m) ℂ)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    (positiveInputKraus K * X * (positiveInputKraus K)ᴴ).trace = (K * X * Kᴴ).trace := by
  calc
    _ = ((Kᴴ * K) * X).trace := by rw [Matrix.trace_mul_cycle, positiveInputKraus_gram]
    _ = _ := (Matrix.trace_mul_cycle K X Kᴴ).symm

section InstrumentAbsorption

variable {S : Type*}

def absorbedRecoveryInstrument (hp : 0 < p) (K : Matrix (Fin p) (Fin m) ℂ) (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ) :
    ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ :=
  fun s => (Φ s).comp (rectangularRecovery hp K)

theorem absorbedRecoveryInstrument_completelyPositive
    (hp : 0 < p) (K : Matrix (Fin p) (Fin m) ℂ) (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (s : S) :
    CompletelyPositive (absorbedRecoveryInstrument hp K dims Φ s) :=
  (hΦ s).comp (rectangularRecovery_completelyPositive hp K)

theorem absorbedRecoveryInstrument_trace_preserving [Fintype S]
    (hp : 0 < p) (K : Matrix (Fin p) (Fin m) ℂ) (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (htrace : ∀ X : Matrix (Fin p) (Fin p) ℂ, (∑ s, (Φ s X).trace) = X.trace)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    (∑ s, (absorbedRecoveryInstrument hp K dims Φ s X).trace) = X.trace := by
  change (∑ s, (Φ s (rectangularRecovery hp K X)).trace) = X.trace
  rw [htrace, rectangularRecovery_trace_preserving]

theorem absorbedRecoveryInstrument_branch
    (hp : 0 < p) (K : Matrix (Fin p) (Fin m) ℂ) (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (s : S) (X : Matrix (Fin m) (Fin m) ℂ) :
    absorbedRecoveryInstrument hp K dims Φ s
      (positiveInputKraus K * X * (positiveInputKraus K)ᴴ) = Φ s (K * X * Kᴴ) := by
  change Φ s (rectangularRecovery hp K _) = _
  rw [rectangularRecovery_apply]

theorem positiveInputKraus_complete [Fintype S] (dims : S → ℕ)
    (K : ∀ s, Matrix (Fin (dims s)) (Fin m) ℂ)
    (hK : ∑ s, (K s)ᴴ * K s = 1) :
    ∑ s, (positiveInputKraus (K s))ᴴ * positiveInputKraus (K s) = 1 := by
  simpa only [positiveInputKraus_gram] using hK

theorem positiveInputKraus_hasSum (dims : S → ℕ)
    (K : ∀ s, Matrix (Fin (dims s)) (Fin m) ℂ)
    (hK : HasSum (fun s => (K s)ᴴ * K s) 1) :
    HasSum (fun s => (positiveInputKraus (K s))ᴴ * positiveInputKraus (K s)) 1 := by
  simpa only [positiveInputKraus_gram] using hK

end InstrumentAbsorption

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

noncomputable section

theorem absorbedRecoveryInstrument_trace_hasSum {S : Type*} {m p : ℕ}
    (hp : 0 < p) (K : Matrix (Fin p) (Fin m) ℂ) (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (htrace : ∀ X : Matrix (Fin p) (Fin p) ℂ, HasSum (fun s => (Φ s X).trace) X.trace)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    HasSum (fun s => (absorbedRecoveryInstrument hp K dims Φ s X).trace) X.trace := by
  change HasSum (fun s => (Φ s (rectangularRecovery hp K X)).trace) X.trace
  simpa only [rectangularRecovery_trace_preserving] using htrace (rectangularRecovery hp K X)

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

noncomputable section

variable {a b m n : ℕ}

theorem left_right_kraus_commute
    (A : Matrix (Fin m) (Fin a) ℂ) (B : Matrix (Fin n) (Fin b) ℂ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    leftKrausApplication A (rightKrausApplication B X) =
      rightKrausApplication B (leftKrausApplication A X) := by
  unfold leftKrausApplication rightKrausApplication
  simp_rw [kraus_sandwich_comp]
  simp only [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem left_right_application_commute
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (Ψ : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hΦ : CompletelyPositive Φ) (hΨ : CompletelyPositive Ψ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    leftApplication Φ (rightApplication Ψ X) =
      rightApplication Ψ (leftApplication Φ X) := by
  calc
    _ = ∑ r : Fin b × Fin n,
        leftApplication Φ (rightKrausApplication (krausOperator Ψ r) X) := by
      rw [rightApplication_eq_kraus Ψ hΨ, map_sum]
    _ = ∑ r : Fin b × Fin n, ∑ q : Fin a × Fin m,
        leftKrausApplication (krausOperator Φ q)
          (rightKrausApplication (krausOperator Ψ r) X) := by
      simp_rw [leftApplication_eq_kraus Φ hΦ]
    _ = ∑ q : Fin a × Fin m, ∑ r : Fin b × Fin n,
        rightKrausApplication (krausOperator Ψ r)
          (leftKrausApplication (krausOperator Φ q) X) := by
      simp_rw [left_right_kraus_commute]
      rw [Finset.sum_comm]
    _ = _ := by
      rw [leftApplication_eq_kraus Φ hΦ, map_sum]
      simp_rw [rightApplication_eq_kraus Ψ hΨ]

theorem leftApplication_trace_preserving
    (Φ : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (htrace : ∀ X, (Φ X).trace = X.trace)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (leftApplication Φ X).trace = X.trace := by
  rw [Matrix.trace, Fintype.sum_prod_type, Finset.sum_comm]
  change (∑ r : Fin b, (Φ (Matrix.of (fun i j => X (i, r) (j, r)))).trace) = X.trace
  simp_rw [htrace]
  rw [Matrix.trace, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

theorem rightApplication_trace_preserving
    (Ψ : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (htrace : ∀ X, (Ψ X).trace = X.trace)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (rightApplication Ψ X).trace = X.trace := by
  rw [Matrix.trace, Fintype.sum_prod_type]
  change (∑ r : Fin a, (Ψ (Matrix.of (fun i j => X (r, i) (r, j)))).trace) = X.trace
  simp_rw [htrace]
  simp [Matrix.trace, Fintype.sum_prod_type]

structure LocalRecovery (input output : ℕ) where
  map : Matrix (Fin input) (Fin input) ℂ →ₗ[ℂ] Matrix (Fin output) (Fin output) ℂ
  completelyPositive : CompletelyPositive map
  trace_preserving : ∀ X, (map X).trace = X.trace

def LocalRecovery.identity (a : ℕ) : LocalRecovery a a where
  map := sandwichMap (1 : Matrix (Fin a) (Fin a) ℂ)
  completelyPositive := sandwichMap_completelyPositive _
  trace_preserving X := by simp [sandwichMap_apply]

theorem LocalRecovery.identity_apply (X : Matrix (Fin a) (Fin a) ℂ) :
    (LocalRecovery.identity a).map X = X := by simp [LocalRecovery.identity, sandwichMap_apply]

def pendingApplication (RA : LocalRecovery a m) (RB : LocalRecovery b n) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ →ₗ[ℂ] Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  (rightApplication RB.map).comp (leftApplication RA.map)

theorem pendingApplication_trace (RA : LocalRecovery a m) (RB : LocalRecovery b n)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (pendingApplication RA RB X).trace = X.trace := by
  change (rightApplication RB.map (leftApplication RA.map X)).trace = X.trace
  rw [rightApplication_trace_preserving RB.map RB.trace_preserving,
    leftApplication_trace_preserving RA.map RA.trace_preserving]

theorem pendingApplication_identity (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    pendingApplication (LocalRecovery.identity a) (LocalRecovery.identity b) X = X := by
  change rightApplication (sandwichMap 1) (leftApplication (sandwichMap 1) X) = X
  rw [leftApplication_sandwichMap, rightApplication_sandwichMap]
  simp [leftKrausApplication, rightKrausApplication, Matrix.one_kronecker_one]

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

noncomputable section

variable {a b m n d D : ℕ}

def LocalRecovery.comp (R2 : LocalRecovery m n) (R1 : LocalRecovery a m) : LocalRecovery a n where
  map := R2.map.comp R1.map
  completelyPositive := R2.completelyPositive.comp R1.completelyPositive
  trace_preserving X := by
    change (R2.map (R1.map X)).trace = X.trace
    rw [R2.trace_preserving, R1.trace_preserving]

def LocalRecovery.unpad (hd : 0 < d) (h : d ≤ D) : LocalRecovery D d where
  map := unpadMap hd h
  completelyPositive := unpadMap_completelyPositive hd h
  trace_preserving := unpadMap_trace_preserving hd h

def LocalRecovery.rectangular (hp : 0 < m) (K : Matrix (Fin m) (Fin a) ℂ) : LocalRecovery a m where
  map := rectangularRecovery hp K
  completelyPositive := rectangularRecovery_completelyPositive hp K
  trace_preserving := rectangularRecovery_trace_preserving hp K

section PendingInstruments

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem commonOutputDimension_pos (dims : S → ℕ) : 0 < commonOutputDimension dims := by
  unfold commonOutputDimension
  omega

abbrev pendingCount (dims : S → ℕ) (a : ℕ) :=
  Fintype.card (S × (Fin a × Fin (commonOutputDimension dims)))

def pendingReport (dims : S → ℕ) {a : ℕ} (r : Fin (pendingCount dims a)) : S :=
  finInstrumentReport (m := a) (out := commonOutputDimension dims) r

def pendingInstrument (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (RA : LocalRecovery a m) :
    S → Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ]
      Matrix (Fin (commonOutputDimension dims)) (Fin (commonOutputDimension dims)) ℂ :=
  paddedInstrument dims (fun s => (Φ s).comp RA.map)

def pendingKraus (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (RA : LocalRecovery a m) :
    Fin (pendingCount dims a) → Matrix (Fin (commonOutputDimension dims)) (Fin a) ℂ :=
  finInstrumentKraus (pendingInstrument dims Φ RA)

theorem pendingInstrument_completelyPositive (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (RA : LocalRecovery a m) (s : S) :
    CompletelyPositive (pendingInstrument dims Φ RA s) :=
  paddedInstrument_completelyPositive dims _ (fun s => (hΦ s).comp RA.completelyPositive) s

theorem pendingInstrument_trace_preserving (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, (∑ s, (Φ s X).trace) = X.trace)
    (RA : LocalRecovery a m) (X : Matrix (Fin a) (Fin a) ℂ) :
    (∑ s, pendingInstrument dims Φ RA s X).trace = X.trace := by
  apply paddedInstrument_trace_preserving dims (fun s => (Φ s).comp RA.map)
  intro Y
  change (∑ s, (Φ s (RA.map Y)).trace) = Y.trace
  rw [htrace, RA.trace_preserving]

theorem pendingKraus_complete (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, (∑ s, (Φ s X).trace) = X.trace)
    (RA : LocalRecovery a m) : ∑ r, (pendingKraus dims Φ RA r)ᴴ * pendingKraus dims Φ RA r = 1 :=
  finInstrumentKraus_complete (pendingInstrument dims Φ RA)
    (pendingInstrument_completelyPositive dims Φ hΦ RA)
    (pendingInstrument_trace_preserving dims Φ htrace RA)

theorem pendingPositiveKraus_complete (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, (∑ s, (Φ s X).trace) = X.trace)
    (RA : LocalRecovery a m) :
    ∑ r, (positiveInputKraus (pendingKraus dims Φ RA r))ᴴ *
      positiveInputKraus (pendingKraus dims Φ RA r) = 1 := by
  simp_rw [positiveInputKraus_gram]
  exact pendingKraus_complete dims Φ hΦ htrace RA

def pendingLocalRecovery (dims : S → ℕ) (hd : ∀ s, 0 < dims s)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (RA : LocalRecovery a m) (r : Fin (pendingCount dims a)) :
    LocalRecovery a (dims (pendingReport dims r)) :=
  (LocalRecovery.unpad (hd (pendingReport dims r)) (le_commonOutputDimension dims _)).comp
    (LocalRecovery.rectangular (commonOutputDimension_pos dims) (pendingKraus dims Φ RA r))

theorem sum_pending_left_evaluation (dims : S → ℕ) (hd : ∀ s, 0 < dims s)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (f : ∀ s, Matrix (Fin (dims s) × Fin n) (Fin (dims s) × Fin n) ℂ →ₗ[ℂ] ℂ)
    (RA : LocalRecovery a m) (RB : LocalRecovery b n)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (∑ s, f s (leftApplication (Φ s) (pendingApplication RA RB X))) =
      ∑ r : Fin (pendingCount dims a), f (pendingReport dims r)
        (pendingApplication (pendingLocalRecovery dims hd Φ RA r) RB
          (leftKrausApplication (positiveInputKraus (pendingKraus dims Φ RA r)) X)) := by
  let f' : S → Matrix (Fin (commonOutputDimension dims) × Fin b)
      (Fin (commonOutputDimension dims) × Fin b) ℂ →ₗ[ℂ] ℂ := fun s =>
    (f s).comp ((rightApplication RB.map).comp
      (leftApplication (unpadMap (hd s) (le_commonOutputDimension dims s))))
  calc
    _ = ∑ s, f' s (leftApplication (pendingInstrument dims Φ RA s) X) := by
      apply Finset.sum_congr rfl
      intro s _
      have heq : (unpadMap (hd s) (le_commonOutputDimension dims s)).comp
          (pendingInstrument dims Φ RA s) = (Φ s).comp RA.map := by
        apply LinearMap.ext
        intro Y
        exact unpadMap_padMap (hd s) (le_commonOutputDimension dims s) ((Φ s).comp RA.map) Y
      have he : leftApplication (unpadMap (hd s) (le_commonOutputDimension dims s))
          (leftApplication (pendingInstrument dims Φ RA s) X) =
          leftApplication (Φ s) (leftApplication RA.map X) := by
        rw [← leftApplication_comp, heq, leftApplication_comp]
      change f s (leftApplication (Φ s) (rightApplication RB.map (leftApplication RA.map X))) =
        f s (rightApplication RB.map (leftApplication (unpadMap (hd s)
          (le_commonOutputDimension dims s)) (leftApplication (pendingInstrument dims Φ RA s) X)))
      rw [left_right_application_commute (Φ s) RB.map (hΦ s) RB.completelyPositive]
      exact congrArg (fun Y => f s (rightApplication RB.map Y)) he.symm
    _ = ∑ r : Fin (pendingCount dims a), f' (pendingReport dims r)
        (leftKrausApplication (pendingKraus dims Φ RA r) X) :=
      sum_left_reported_evaluation (pendingInstrument dims Φ RA)
        (pendingInstrument_completelyPositive dims Φ hΦ RA) f' X
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      change f (pendingReport dims r) (rightApplication RB.map
        (leftApplication (unpadMap (hd (pendingReport dims r)) (le_commonOutputDimension dims _))
          (leftKrausApplication (pendingKraus dims Φ RA r) X))) =
        f (pendingReport dims r) (rightApplication RB.map
          (leftApplication ((unpadMap (hd (pendingReport dims r)) (le_commonOutputDimension dims _)).comp
            (rectangularRecovery (commonOutputDimension_pos dims) (pendingKraus dims Φ RA r)))
            (leftKrausApplication (positiveInputKraus (pendingKraus dims Φ RA r)) X)))
      rw [leftApplication_comp, left_rectangularRecovery_branch]

theorem sum_pending_right_evaluation (dims : S → ℕ) (hd : ∀ s, 0 < dims s)
    (Φ : ∀ s, Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (f : ∀ s, Matrix (Fin m × Fin (dims s)) (Fin m × Fin (dims s)) ℂ →ₗ[ℂ] ℂ)
    (RA : LocalRecovery a m) (RB : LocalRecovery b n)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (∑ s, f s (rightApplication (Φ s) (pendingApplication RA RB X))) =
      ∑ r : Fin (pendingCount dims b), f (pendingReport dims r)
        (pendingApplication RA (pendingLocalRecovery dims hd Φ RB r)
          (rightKrausApplication (positiveInputKraus (pendingKraus dims Φ RB r)) X)) := by
  let f' : S → Matrix (Fin a × Fin (commonOutputDimension dims))
      (Fin a × Fin (commonOutputDimension dims)) ℂ →ₗ[ℂ] ℂ := fun s =>
    (f s).comp ((rightApplication (unpadMap (hd s) (le_commonOutputDimension dims s))).comp
      (leftApplication RA.map))
  calc
    _ = ∑ s, f' s (rightApplication (pendingInstrument dims Φ RB s) X) := by
      apply Finset.sum_congr rfl
      intro s _
      have heq : (unpadMap (hd s) (le_commonOutputDimension dims s)).comp
          (pendingInstrument dims Φ RB s) = (Φ s).comp RB.map := by
        apply LinearMap.ext
        intro Y
        exact unpadMap_padMap (hd s) (le_commonOutputDimension dims s) ((Φ s).comp RB.map) Y
      have he : rightApplication (unpadMap (hd s) (le_commonOutputDimension dims s))
          (rightApplication (pendingInstrument dims Φ RB s) (leftApplication RA.map X)) =
          rightApplication (Φ s) (rightApplication RB.map (leftApplication RA.map X)) := by
        rw [← rightApplication_comp, heq, rightApplication_comp]
      change f s (rightApplication (Φ s) (rightApplication RB.map (leftApplication RA.map X))) =
        f s (rightApplication (unpadMap (hd s) (le_commonOutputDimension dims s))
          (leftApplication RA.map (rightApplication (pendingInstrument dims Φ RB s) X)))
      rw [left_right_application_commute RA.map (pendingInstrument dims Φ RB s)
        RA.completelyPositive (pendingInstrument_completelyPositive dims Φ hΦ RB s)]
      exact congrArg (f s) he.symm
    _ = ∑ r : Fin (pendingCount dims b), f' (pendingReport dims r)
        (rightKrausApplication (pendingKraus dims Φ RB r) X) :=
      sum_right_reported_evaluation (pendingInstrument dims Φ RB)
        (pendingInstrument_completelyPositive dims Φ hΦ RB) f' X
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      change f (pendingReport dims r) (rightApplication
          (unpadMap (hd (pendingReport dims r)) (le_commonOutputDimension dims _))
          (leftApplication RA.map (rightKrausApplication (pendingKraus dims Φ RB r) X))) =
        f (pendingReport dims r) (rightApplication
          (unpadMap (hd (pendingReport dims r)) (le_commonOutputDimension dims _))
          (rightApplication (rectangularRecovery (commonOutputDimension_pos dims) (pendingKraus dims Φ RB r))
            (leftApplication RA.map
              (rightKrausApplication (positiveInputKraus (pendingKraus dims Φ RB r)) X))))
      rw [← left_right_application_commute RA.map
        (rectangularRecovery (commonOutputDimension_pos dims) (pendingKraus dims Φ RB r))
        RA.completelyPositive (rectangularRecovery_completelyPositive _ _),
        right_rectangularRecovery_branch]

end PendingInstruments

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

noncomputable section

universe u

inductive FiniteFixedPositiveKrausTree (a b : ℕ) (L : Type u) : Type u where
  | leaf (report : L)
  | alice (outcomes : ℕ) (A : Fin outcomes → Matrix (Fin a) (Fin a) ℂ)
      (positive : ∀ r, (A r).PosSemidef) (complete : ∑ r, (A r)ᴴ * A r = 1)
      (next : Fin outcomes → FiniteFixedPositiveKrausTree a b L)
  | bob (outcomes : ℕ) (B : Fin outcomes → Matrix (Fin b) (Fin b) ℂ)
      (positive : ∀ r, (B r).PosSemidef) (complete : ∑ r, (B r)ᴴ * B r = 1)
      (next : Fin outcomes → FiniteFixedPositiveKrausTree a b L)

theorem sandwichInstrument_trace_preserving {d outcomes : ℕ}
    (K : Fin outcomes → Matrix (Fin d) (Fin d) ℂ) (hK : ∑ r, (K r)ᴴ * K r = 1)
    (X : Matrix (Fin d) (Fin d) ℂ) : (∑ r, sandwichMap (K r) X).trace = X.trace := by
  simp_rw [sandwichMap_apply]
  exact (krausMap_trace_preserving_iff K).mpr hK X

namespace FiniteFixedPositiveKrausTree

variable {a b : ℕ} {L : Type u}

def matrixReportedEvaluation [DecidableEq L] : FiniteFixedPositiveKrausTree a b L → L →
    (Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ →ₗ[ℂ] ℂ)
  | .leaf report, ell =>
      if report = ell then Matrix.traceLinearMap (Fin a × Fin b) ℂ ℂ else 0
  | .alice _ A _ _ next, ell =>
      ∑ r, (matrixReportedEvaluation (next r) ell).comp (leftApplication (sandwichMap (A r)))
  | .bob _ B _ _ next, ell =>
      ∑ r, (matrixReportedEvaluation (next r) ell).comp (rightApplication (sandwichMap (B r)))

def toCPInstrumentTree : FiniteFixedPositiveKrausTree a b L → FiniteLocalCPInstrumentTree a b
  | .leaf _ => .leaf a b
  | .alice outcomes A _ complete next =>
      .alice a b a outcomes (fun r => sandwichMap (A r))
        (fun r => sandwichMap_completelyPositive (A r))
        (sandwichInstrument_trace_preserving A complete)
        (fun r => toCPInstrumentTree (next r))
  | .bob outcomes B _ complete next =>
      .bob a b b outcomes (fun r => sandwichMap (B r))
        (fun r => sandwichMap_completelyPositive (B r))
        (sandwichInstrument_trace_preserving B complete)
        (fun r => toCPInstrumentTree (next r))

def cpLeafLabels : (T : FiniteFixedPositiveKrausTree a b L) →
    FiniteLocalCPInstrumentTree.LeafLabels T.toCPInstrumentTree L
  | .leaf report => report
  | .alice _ _ _ _ next => fun r => cpLeafLabels (next r)
  | .bob _ _ _ _ next => fun r => cpLeafLabels (next r)

variable [DecidableEq L]

theorem matrixReportedEvaluation_eq_toCPInstrumentTree
    (T : FiniteFixedPositiveKrausTree a b L) :
    ∀ (ell : L) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ),
      T.matrixReportedEvaluation ell X = T.toCPInstrumentTree.matrixReportedEvaluation T.cpLeafLabels ell X := by
  induction T with
  | leaf report => intro ell X; rfl
  | alice outcomes A positive complete next ih =>
    intro ell X
    simp only [matrixReportedEvaluation, toCPInstrumentTree, cpLeafLabels,
      FiniteLocalCPInstrumentTree.matrixReportedEvaluation, LinearMap.sum_apply, LinearMap.comp_apply]
    apply Finset.sum_congr rfl
    intro r _
    exact ih r ell (leftApplication (sandwichMap (A r)) X)
  | bob outcomes B positive complete next ih =>
    intro ell X
    simp only [matrixReportedEvaluation, toCPInstrumentTree, cpLeafLabels,
      FiniteLocalCPInstrumentTree.matrixReportedEvaluation, LinearMap.sum_apply, LinearMap.comp_apply]
    apply Finset.sum_congr rfl
    intro r _
    exact ih r ell (rightApplication (sandwichMap (B r)) X)

end FiniteFixedPositiveKrausTree

namespace DependentOutputCPInstrumentTree

variable {a b m n : ℕ} {L : Type u}

def compileFixed : {m n : ℕ} → (T : DependentOutputCPInstrumentTree m n) → LeafLabels T L →
    LocalRecovery a m → LocalRecovery b n → FiniteFixedPositiveKrausTree a b L
  | _, _, .leaf _ _, labels, _, _ => .leaf labels
  | _, _, .alice _ _ _ dims hd Φ positive trace next, labels, RA, RB =>
      .alice (pendingCount dims a) (fun r => positiveInputKraus (pendingKraus dims Φ RA r))
        (fun r => positiveInputKraus_posSemidef (pendingKraus dims Φ RA r))
        (pendingPositiveKraus_complete dims Φ positive trace RA)
        (fun r => compileFixed (next (pendingReport dims r)) (labels (pendingReport dims r))
          (pendingLocalRecovery dims hd Φ RA r) RB)
  | _, _, .bob _ _ _ dims hd Φ positive trace next, labels, RA, RB =>
      .bob (pendingCount dims b) (fun r => positiveInputKraus (pendingKraus dims Φ RB r))
        (fun r => positiveInputKraus_posSemidef (pendingKraus dims Φ RB r))
        (pendingPositiveKraus_complete dims Φ positive trace RB)
        (fun r => compileFixed (next (pendingReport dims r)) (labels (pendingReport dims r))
          RA (pendingLocalRecovery dims hd Φ RB r))

variable [DecidableEq L]

theorem matrixReportedEvaluation_eq_compileFixed (T : DependentOutputCPInstrumentTree m n) :
    ∀ (labels : LeafLabels T L) (RA : LocalRecovery a m) (RB : LocalRecovery b n)
      (ell : L) (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ),
      T.matrixReportedEvaluation labels ell (pendingApplication RA RB X) =
        (T.compileFixed labels RA RB).matrixReportedEvaluation ell X := by
  induction T with
  | leaf m n =>
    intro labels RA RB ell X
    by_cases h : labels = ell <;>
      simp [matrixReportedEvaluation, compileFixed,
        FiniteFixedPositiveKrausTree.matrixReportedEvaluation, h, pendingApplication_trace]
  | alice m n outcomes dims hd Φ positive trace next ih =>
    intro labels RA RB ell X
    simp only [matrixReportedEvaluation, compileFixed,
      FiniteFixedPositiveKrausTree.matrixReportedEvaluation, LinearMap.sum_apply, LinearMap.comp_apply]
    rw [sum_pending_left_evaluation dims hd Φ positive
      (fun s => (next s).matrixReportedEvaluation (labels s) ell) RA RB X]
    simp_rw [leftApplication_sandwichMap]
    apply Finset.sum_congr rfl
    intro r _
    exact ih (pendingReport dims r) (labels (pendingReport dims r))
      (pendingLocalRecovery dims hd Φ RA r) RB ell
      (leftKrausApplication (positiveInputKraus (pendingKraus dims Φ RA r)) X)
  | bob m n outcomes dims hd Φ positive trace next ih =>
    intro labels RA RB ell X
    simp only [matrixReportedEvaluation, compileFixed,
      FiniteFixedPositiveKrausTree.matrixReportedEvaluation, LinearMap.sum_apply, LinearMap.comp_apply]
    rw [sum_pending_right_evaluation dims hd Φ positive
      (fun s => (next s).matrixReportedEvaluation (labels s) ell) RA RB X]
    simp_rw [rightApplication_sandwichMap]
    apply Finset.sum_congr rfl
    intro r _
    exact ih (pendingReport dims r) (labels (pendingReport dims r))
      RA (pendingLocalRecovery dims hd Φ RB r) ell
      (rightKrausApplication (positiveInputKraus (pendingKraus dims Φ RB r)) X)

def fixedInitialPositiveTree (T : DependentOutputCPInstrumentTree a b) (labels : LeafLabels T L) :
    FiniteFixedPositiveKrausTree a b L :=
  T.compileFixed labels (LocalRecovery.identity a) (LocalRecovery.identity b)

theorem matrixReportedEvaluation_eq_fixedInitialPositiveTree
    (T : DependentOutputCPInstrumentTree a b) (labels : LeafLabels T L) (ell : L)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    T.matrixReportedEvaluation labels ell X = (T.fixedInitialPositiveTree labels).matrixReportedEvaluation ell X := by
  simpa only [fixedInitialPositiveTree, pendingApplication_identity] using
    T.matrixReportedEvaluation_eq_compileFixed labels (LocalRecovery.identity a) (LocalRecovery.identity b) ell X

def fixedInitialKrausTree (T : DependentOutputCPInstrumentTree a b) (labels : LeafLabels T L) :
    QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree a b :=
  (T.fixedInitialPositiveTree labels).toCPInstrumentTree.krausRefinement

def fixedInitialTerminalReport (T : DependentOutputCPInstrumentTree a b) (labels : LeafLabels T L) :
    Fin (T.fixedInitialKrausTree labels).terminalBraPairs.length → L :=
  (T.fixedInitialPositiveTree labels).toCPInstrumentTree.terminalReport
    (T.fixedInitialPositiveTree labels).cpLeafLabels

theorem matrixReportedEvaluation_eq_fixedInitial_terminalEffects
    (T : DependentOutputCPInstrumentTree a b) (labels : LeafLabels T L) (ell : L)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    T.matrixReportedEvaluation labels ell X =
      ∑ i : Fin (T.fixedInitialKrausTree labels).terminalBraPairs.length,
        if T.fixedInitialTerminalReport labels i = ell then
          (((T.fixedInitialKrausTree labels).terminalBraPairs.get i).productEffect * X).trace else 0 := by
  rw [matrixReportedEvaluation_eq_fixedInitialPositiveTree,
    FiniteFixedPositiveKrausTree.matrixReportedEvaluation_eq_toCPInstrumentTree]
  exact (T.fixedInitialPositiveTree labels).toCPInstrumentTree.matrixReportedEvaluation_eq_terminalEffects
    (T.fixedInitialPositiveTree labels).cpLeafLabels ell X

end DependentOutputCPInstrumentTree

def usesFixedLocalDimensions (a b : ℕ) : {m n : ℕ} → QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree m n → Prop
  | _, _, .leaf m n => m = a ∧ n = b
  | _, _, .alice m n out _ _ _ next =>
      m = a ∧ n = b ∧ out = a ∧ ∀ r, usesFixedLocalDimensions a b (next r)
  | _, _, .bob m n out _ _ _ next =>
      m = a ∧ n = b ∧ out = b ∧ ∀ r, usesFixedLocalDimensions a b (next r)

namespace FiniteFixedPositiveKrausTree

variable {a b : ℕ} {L : Type u}

theorem toCPInstrumentTree_refinement_usesFixedLocalDimensions
    (T : FiniteFixedPositiveKrausTree a b L) :
    usesFixedLocalDimensions a b T.toCPInstrumentTree.krausRefinement := by
  induction T with
  | leaf report => simp [toCPInstrumentTree, FiniteLocalCPInstrumentTree.krausRefinement, usesFixedLocalDimensions]
  | alice outcomes A positive complete next ih =>
    simp only [toCPInstrumentTree, FiniteLocalCPInstrumentTree.krausRefinement, cpAliceNode,
      usesFixedLocalDimensions]
    refine ⟨True.intro, True.intro, True.intro, ?_⟩
    intro r
    exact ih (finInstrumentReport r)
  | bob outcomes B positive complete next ih =>
    simp only [toCPInstrumentTree, FiniteLocalCPInstrumentTree.krausRefinement, cpBobNode,
      usesFixedLocalDimensions]
    refine ⟨True.intro, True.intro, True.intro, ?_⟩
    intro r
    exact ih (finInstrumentReport r)

end FiniteFixedPositiveKrausTree

namespace DependentOutputCPInstrumentTree

variable {a b : ℕ} {L : Type u} [DecidableEq L]

theorem fixedInitialKrausTree_usesFixedLocalDimensions
    (T : DependentOutputCPInstrumentTree a b) (labels : LeafLabels T L) :
    usesFixedLocalDimensions a b (T.fixedInitialKrausTree labels) :=
  (T.fixedInitialPositiveTree labels).toCPInstrumentTree_refinement_usesFixedLocalDimensions

theorem fixedInitial_terminal_tail_cost_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (T : DependentOutputCPInstrumentTree a b) (labels : LeafLabels T L)
    (ea : (Fin 2 × κ) ≃ Fin a) (eb : (Fin 2 × κ) ≃ Fin b)
    (β : κ → ℝ) (k : κ) (t : ℝ) (ht : 0 < t) :
    ((T.fixedInitialKrausTree labels).terminalBraPairs.map (fun q => q.tailCost ea eb β k)).sum ≤
      (2 * t) * QuantumProver.ElegantJointMeasurement.Concurrence.homogeneousBudget ((Real.sqrt t)⁻¹ •
        QuantumProver.ElegantJointMeasurement.Concurrence.physicalReferenceInput (QuantumProver.ElegantJointMeasurement.Concurrence.omittedCoefficient β k)) :=
  (T.fixedInitialKrausTree labels).terminal_tail_cost_le ea eb β k t ht

end DependentOutputCPInstrumentTree

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

noncomputable section

theorem posSemidef_norm_le_trace {a : Type*} [Fintype a] [DecidableEq a]
    (R : Matrix a a ℂ) (hR : R.PosSemidef) : ‖R‖ ≤ R.trace.re := by
  have hnorm : ‖R‖ = ‖fun i => (hR.isHermitian.eigenvalues i : ℂ)‖ := by
    conv_lhs => rw [hR.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
    rfl
  have ht : R.trace.re = ∑ i, hR.isHermitian.eigenvalues i := by
    rw [hR.isHermitian.trace_eq_sum_eigenvalues]
    simp
  rw [hnorm, ht]
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => hR.eigenvalues_nonneg i))).mpr
  intro i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hR.eigenvalues_nonneg i)]
  exact Finset.single_le_sum (fun k _ => hR.eigenvalues_nonneg k) (Finset.mem_univ i)

namespace HeterogeneousCPInstrument

variable {S : Type*} {m : ℕ}

abbrev Hidden (m : ℕ) (dims : S → ℕ) := Σ s : S, Fin (m * dims s)

def kraus (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (q : Hidden m dims) : Matrix (Fin (dims q.1)) (Fin m) ℂ :=
  krausOperator (Φ q.1)
    ((finProdFinEquiv : Fin m × Fin (dims q.1) ≃ Fin (m * dims q.1)).symm q.2)

theorem apply_eq_sum (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (s : S)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    Φ s X = ∑ q : Fin (m * dims s), kraus dims Φ ⟨s, q⟩ * X * (kraus dims Φ ⟨s, q⟩)ᴴ := by
  rw [completelyPositive_apply_eq_sum (Φ s) (hΦ s)]
  exact ((finProdFinEquiv : Fin m × Fin (dims s) ≃ Fin (m * dims s)).symm.sum_comp
    (fun q => krausOperator (Φ s) q * X * (krausOperator (Φ s) q)ᴴ)).symm

theorem reported_gram_trace (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (s : S)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    ((∑ q : Fin (m * dims s), (kraus dims Φ ⟨s, q⟩)ᴴ * kraus dims Φ ⟨s, q⟩) * X).trace =
      (Φ s X).trace := by
  rw [apply_eq_sum dims Φ hΦ s X, Matrix.trace_sum, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact (Matrix.trace_mul_cycle (kraus dims Φ ⟨s, q⟩) X (kraus dims Φ ⟨s, q⟩)ᴴ).symm

theorem reported_gram_hasSum (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, HasSum (fun s => (Φ s X).trace) X.trace) :
    HasSum (fun s => ∑ q : Fin (m * dims s),
      (kraus dims Φ ⟨s, q⟩)ᴴ * kraus dims Φ ⟨s, q⟩) 1 := by
  apply Pi.hasSum.mpr
  intro i
  apply Pi.hasSum.mpr
  intro j
  have h := htrace (Matrix.single j i 1)
  have heq (s : S) : (Φ s (Matrix.single j i 1)).trace =
      (∑ q : Fin (m * dims s), (kraus dims Φ ⟨s, q⟩)ᴴ * kraus dims Φ ⟨s, q⟩) i j := by
    rw [← reported_gram_trace dims Φ hΦ s]
    simp [Matrix.trace_mul_single]
  simp_rw [heq] at h
  by_cases hij : i = j
  · subst j
    simpa [Matrix.trace_single_eq_same, Matrix.one_apply] using h
  · simpa [Matrix.trace_single_eq_of_ne j i (1 : ℂ) (Ne.symm hij), Matrix.one_apply, hij] using h

theorem gram_summable (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, HasSum (fun s => (Φ s X).trace) X.trace) :
    Summable (fun q : Hidden m dims => (kraus dims Φ q)ᴴ * kraus dims Φ q) := by
  let G := fun q : Hidden m dims => (kraus dims Φ q)ᴴ * kraus dims Φ q
  let g := fun q : Hidden m dims => (G q).trace.re
  have hg0 (q : Hidden m dims) : 0 ≤ g q :=
    (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (kraus dims Φ q)).trace_nonneg).1
  have heq (s : S) : (∑ q : Fin (m * dims s), g ⟨s, q⟩) = (Φ s 1).trace.re := by
    rw [← reported_gram_trace dims Φ hΦ s]
    simp [g, G, Matrix.trace_sum]
  let reHom : ℂ →+ ℝ :=
    { toFun := Complex.re
      map_zero' := rfl
      map_add' := Complex.add_re }
  have hre : HasSum (fun s => (Φ s 1).trace.re) ((1 : Matrix (Fin m) (Fin m) ℂ).trace.re) :=
    (htrace 1).map reHom Complex.continuous_re
  have hg : Summable g := (summable_sigma_of_nonneg hg0).mpr
    ⟨fun s => (hasSum_fintype _).summable, by
      simpa only [tsum_fintype, heq] using hre.summable⟩
  exact hg.of_norm_bounded (fun q => posSemidef_norm_le_trace _
    (Matrix.posSemidef_conjTranspose_mul_self (kraus dims Φ q)))

theorem gram_hasSum (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, HasSum (fun s => (Φ s X).trace) X.trace) :
    HasSum (fun q : Hidden m dims => (kraus dims Φ q)ᴴ * kraus dims Φ q) 1 := by
  have hs := gram_summable dims Φ hΦ htrace
  have heq : (∑' q : Hidden m dims, (kraus dims Φ q)ᴴ * kraus dims Φ q) = 1 := by
    rw [hs.tsum_sigma]
    simp only [tsum_fintype]
    exact (reported_gram_hasSum dims Φ hΦ htrace).tsum_eq
  simpa only [heq] using hs.hasSum

theorem zero_output_apply (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (s : S) (hzero : dims s = 0) (X : Matrix (Fin m) (Fin m) ℂ) : Φ s X = 0 := by
  ext i j
  have hi := i.isLt
  simp [hzero] at hi

theorem hidden_output_pos (dims : S → ℕ) (q : Hidden m dims) : 0 < dims q.1 := by
  by_contra h
  have hz : dims q.1 = 0 := Nat.eq_zero_of_not_pos h
  have hq := q.2.isLt
  simp [hz] at hq

def positiveKraus (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (q : Hidden m dims) : Matrix (Fin m) (Fin m) ℂ :=
  positiveInputKraus (kraus dims Φ q)

theorem positive_gram_hasSum (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, HasSum (fun s => (Φ s X).trace) X.trace) :
    HasSum (fun q : Hidden m dims => (positiveKraus dims Φ q)ᴴ * positiveKraus dims Φ q) 1 := by
  simpa only [positiveKraus, positiveInputKraus_gram] using gram_hasSum dims Φ hΦ htrace

def recovery (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (q : Hidden m dims) : LocalRecovery m (dims q.1) :=
  LocalRecovery.rectangular (hidden_output_pos dims q) (kraus dims Φ q)

theorem recovery_apply (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (q : Hidden m dims) (X : Matrix (Fin m) (Fin m) ℂ) :
    (recovery dims Φ q).map (positiveKraus dims Φ q * X * (positiveKraus dims Φ q)ᴴ) =
      kraus dims Φ q * X * (kraus dims Φ q)ᴴ :=
  rectangularRecovery_apply (hidden_output_pos dims q) (kraus dims Φ q) X

theorem apply_eq_sum_recovery (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (s : S) (X : Matrix (Fin m) (Fin m) ℂ) :
    Φ s X = ∑ q : Fin (m * dims s), (recovery dims Φ ⟨s, q⟩).map
      (positiveKraus dims Φ ⟨s, q⟩ * X * (positiveKraus dims Φ ⟨s, q⟩)ᴴ) := by
  simp only [recovery_apply]
  exact apply_eq_sum dims Φ hΦ s X

theorem reported_recovery_trace_hasSum (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, HasSum (fun s => (Φ s X).trace) X.trace)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    HasSum (fun s => ∑ q : Fin (m * dims s), ((recovery dims Φ ⟨s, q⟩).map
      (positiveKraus dims Φ ⟨s, q⟩ * X * (positiveKraus dims Φ ⟨s, q⟩)ᴴ)).trace) X.trace := by
  have heq (s : S) : (∑ q : Fin (m * dims s), ((recovery dims Φ ⟨s, q⟩).map
      (positiveKraus dims Φ ⟨s, q⟩ * X * (positiveKraus dims Φ ⟨s, q⟩)ᴴ)).trace) =
      (Φ s X).trace := by
    simpa only [Matrix.trace_sum] using
      (congrArg Matrix.trace (apply_eq_sum_recovery dims Φ hΦ s X)).symm
  simp_rw [heq]
  exact htrace X

end HeterogeneousCPInstrument

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP.HeterogeneousCPInstrument

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

noncomputable section

variable {S : Type*} {a b m n : ℕ}

theorem left_apply_eq_sum_recovery (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (s : S)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    leftApplication (Φ s) X = ∑ q : Fin (m * dims s),
      leftApplication (recovery dims Φ ⟨s, q⟩).map (leftKrausApplication (positiveKraus dims Φ ⟨s, q⟩) X) := by
  have heq (q : Fin (m * dims s)) :
      leftApplication (recovery dims Φ ⟨s, q⟩).map (leftKrausApplication (positiveKraus dims Φ ⟨s, q⟩) X) =
        leftKrausApplication (kraus dims Φ ⟨s, q⟩) X :=
    left_rectangularRecovery_branch (hidden_output_pos dims ⟨s, q⟩) (kraus dims Φ ⟨s, q⟩) X
  simp_rw [heq]
  rw [leftApplication_eq_kraus (Φ s) (hΦ s)]
  exact ((finProdFinEquiv : Fin m × Fin (dims s) ≃ Fin (m * dims s)).symm.sum_comp
    (fun q => leftKrausApplication (krausOperator (Φ s) q) X)).symm

theorem right_apply_eq_sum_recovery (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (s : S)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    rightApplication (Φ s) X = ∑ q : Fin (n * dims s),
      rightApplication (recovery dims Φ ⟨s, q⟩).map (rightKrausApplication (positiveKraus dims Φ ⟨s, q⟩) X) := by
  have heq (q : Fin (n * dims s)) :
      rightApplication (recovery dims Φ ⟨s, q⟩).map (rightKrausApplication (positiveKraus dims Φ ⟨s, q⟩) X) =
        rightKrausApplication (kraus dims Φ ⟨s, q⟩) X :=
    right_rectangularRecovery_branch (hidden_output_pos dims ⟨s, q⟩) (kraus dims Φ ⟨s, q⟩) X
  simp_rw [heq]
  rw [rightApplication_eq_kraus (Φ s) (hΦ s)]
  exact ((finProdFinEquiv : Fin n × Fin (dims s) ≃ Fin (n * dims s)).symm.sum_comp
    (fun q => rightKrausApplication (krausOperator (Φ s) q) X)).symm

def absorbed (RA : LocalRecovery a m) (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ) :
    ∀ s, Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ :=
  fun s => (Φ s).comp RA.map

theorem absorbed_completelyPositive (RA : LocalRecovery a m) (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (s : S) :
    CompletelyPositive (absorbed RA dims Φ s) := (hΦ s).comp RA.completelyPositive

theorem absorbed_trace_hasSum (RA : LocalRecovery a m) (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, HasSum (fun s => (Φ s X).trace) X.trace)
    (X : Matrix (Fin a) (Fin a) ℂ) :
    HasSum (fun s => (absorbed RA dims Φ s X).trace) X.trace := by
  change HasSum (fun s => (Φ s (RA.map X)).trace) X.trace
  simpa only [RA.trace_preserving] using htrace (RA.map X)

theorem absorbed_positive_gram_hasSum (RA : LocalRecovery a m) (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, HasSum (fun s => (Φ s X).trace) X.trace) :
    HasSum (fun q : Hidden a dims => (positiveKraus dims (absorbed RA dims Φ) q)ᴴ *
      positiveKraus dims (absorbed RA dims Φ) q) 1 :=
  positive_gram_hasSum dims (absorbed RA dims Φ) (absorbed_completelyPositive RA dims Φ hΦ)
    (absorbed_trace_hasSum RA dims Φ htrace)

theorem left_pending_report_action (RA : LocalRecovery a m) (RB : LocalRecovery b n)
    (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (s : S)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    leftApplication (Φ s) (pendingApplication RA RB X) = ∑ q : Fin (a * dims s),
      pendingApplication (recovery dims (absorbed RA dims Φ) ⟨s, q⟩) RB
        (leftKrausApplication (positiveKraus dims (absorbed RA dims Φ) ⟨s, q⟩) X) := by
  change leftApplication (Φ s) (rightApplication RB.map (leftApplication RA.map X)) = _
  rw [left_right_application_commute (Φ s) RB.map (hΦ s) RB.completelyPositive,
    ← leftApplication_comp]
  change rightApplication RB.map (leftApplication (absorbed RA dims Φ s) X) = _
  rw [left_apply_eq_sum_recovery dims (absorbed RA dims Φ)
    (absorbed_completelyPositive RA dims Φ hΦ) s X, map_sum]
  rfl

theorem right_pending_report_action (RA : LocalRecovery a m) (RB : LocalRecovery b n)
    (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s)) (s : S)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    rightApplication (Φ s) (pendingApplication RA RB X) = ∑ q : Fin (b * dims s),
      pendingApplication RA (recovery dims (absorbed RB dims Φ) ⟨s, q⟩)
        (rightKrausApplication (positiveKraus dims (absorbed RB dims Φ) ⟨s, q⟩) X) := by
  change rightApplication (Φ s) (rightApplication RB.map (leftApplication RA.map X)) = _
  rw [← rightApplication_comp]
  change rightApplication (absorbed RB dims Φ s) (leftApplication RA.map X) = _
  rw [← left_right_application_commute RA.map (absorbed RB dims Φ s) RA.completelyPositive
    (absorbed_completelyPositive RB dims Φ hΦ s)]
  rw [right_apply_eq_sum_recovery dims (absorbed RB dims Φ)
    (absorbed_completelyPositive RB dims Φ hΦ) s X, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact left_right_application_commute RA.map (recovery dims (absorbed RB dims Φ) ⟨s, q⟩).map
    RA.completelyPositive (recovery dims (absorbed RB dims Φ) ⟨s, q⟩).completelyPositive _

end

end QuantumProver.ElegantJointMeasurement.CP.HeterogeneousCPInstrument

namespace QuantumProver.ElegantJointMeasurement.CP.HeterogeneousCPInstrument

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

noncomputable section

variable {S : Type*} {m : ℕ}

theorem hidden_trace_hasSum (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, HasSum (fun s => (Φ s X).trace) X.trace)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    HasSum (fun q : Hidden m dims => (kraus dims Φ q * X * (kraus dims Φ q)ᴴ).trace) X.trace := by
  let f : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun G => (G * X).trace
      map_add' := by intro A B; rw [Matrix.add_mul, Matrix.trace_add]
      map_smul' := by intro z G; simp [Matrix.smul_mul, Matrix.trace_smul] }
  have h := (gram_hasSum dims Φ hΦ htrace).map f.toAddMonoidHom f.continuous_of_finiteDimensional
  change HasSum (fun q : Hidden m dims => f ((kraus dims Φ q)ᴴ * kraus dims Φ q)) (f 1) at h
  have heq (q : Hidden m dims) : f ((kraus dims Φ q)ᴴ * kraus dims Φ q) =
      (kraus dims Φ q * X * (kraus dims Φ q)ᴴ).trace :=
    (Matrix.trace_mul_cycle (kraus dims Φ q) X (kraus dims Φ q)ᴴ).symm
  have ht : f 1 = X.trace := by simp [f]
  simpa only [heq, ht] using h

theorem hidden_positive_trace_hasSum (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, HasSum (fun s => (Φ s X).trace) X.trace)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    HasSum (fun q : Hidden m dims =>
      (positiveKraus dims Φ q * X * (positiveKraus dims Φ q)ᴴ).trace) X.trace := by
  simp_rw [positiveKraus, positiveInputKraus_branch_trace]
  exact hidden_trace_hasSum dims Φ hΦ htrace X

theorem hidden_recovery_trace_hasSum (dims : S → ℕ)
    (Φ : ∀ s, Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (dims s)) (Fin (dims s)) ℂ)
    (hΦ : ∀ s, CompletelyPositive (Φ s))
    (htrace : ∀ X : Matrix (Fin m) (Fin m) ℂ, HasSum (fun s => (Φ s X).trace) X.trace)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    HasSum (fun q : Hidden m dims => ((recovery dims Φ q).map
      (positiveKraus dims Φ q * X * (positiveKraus dims Φ q)ᴴ)).trace) X.trace := by
  simp_rw [recovery_apply]
  exact hidden_trace_hasSum dims Φ hΦ htrace X

end

end QuantumProver.ElegantJointMeasurement.CP.HeterogeneousCPInstrument

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator
open Filter Topology Set

noncomputable section

set_option maxHeartbeats 800000

variable {m p : ℕ}

def polarEpsilon (N : ℕ) : ℝ := 1 / ((N : ℝ) + 1)

theorem polarEpsilon_pos (N : ℕ) : 0 < polarEpsilon N := by
  unfold polarEpsilon
  positivity

theorem polarEpsilon_tendsto : Tendsto polarEpsilon atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem continuous_gram : Continuous (fun K : Matrix (Fin p) (Fin m) ℂ => Kᴴ * K) :=
  continuous_id.matrix_conjTranspose.matrix_mul continuous_id

theorem continuous_positiveInputKraus : Continuous (positiveInputKraus (p := p) (m := m)) :=
  CFC.continuousOn_sqrt.comp_continuous continuous_gram
    (fun K => (Matrix.posSemidef_conjTranspose_mul_self K).nonneg)

theorem measurable_positiveInputKraus : Measurable (positiveInputKraus (p := p) (m := m)) :=
  continuous_positiveInputKraus.measurable

private theorem continuous_gram_cfc (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (fun K : Matrix (Fin p) (Fin m) ℂ => cfc f (Kᴴ * K)) := by
  exact Continuous.cfc_of_mem_nhdsSet f (s := Set.univ) (by simp) continuous_gram
    (fun K => Matrix.isHermitian_conjTranspose_mul_self K) hf.continuousOn

def regularizedGramInverse (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  cfc (fun x : ℝ => (max x 0 + polarEpsilon N)⁻¹) (Kᴴ * K)

def regularizedRootInverse (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  cfc (fun x : ℝ => (Real.sqrt (max x 0 + polarEpsilon N))⁻¹) (Kᴴ * K)

def regularizedPolar (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) : Matrix (Fin p) (Fin m) ℂ :=
  K * regularizedRootInverse K N

def regularizedSupport (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  cfc (fun x : ℝ => max x 0 / (max x 0 + polarEpsilon N)) (Kᴴ * K)

theorem continuous_regularizedGramInverse (N : ℕ) :
    Continuous (fun K : Matrix (Fin p) (Fin m) ℂ => regularizedGramInverse K N) := by
  apply continuous_gram_cfc
  apply Continuous.inv₀
  · fun_prop
  · intro x
    exact ne_of_gt (add_pos_of_nonneg_of_pos (le_max_right x 0) (polarEpsilon_pos N))

theorem continuous_regularizedRootInverse (N : ℕ) :
    Continuous (fun K : Matrix (Fin p) (Fin m) ℂ => regularizedRootInverse K N) := by
  apply continuous_gram_cfc
  apply Continuous.inv₀
  · fun_prop
  · intro x
    exact ne_of_gt (Real.sqrt_pos.mpr
      (add_pos_of_nonneg_of_pos (le_max_right x 0) (polarEpsilon_pos N)))

theorem continuous_regularizedPolar (N : ℕ) :
    Continuous (fun K : Matrix (Fin p) (Fin m) ℂ => regularizedPolar K N) :=
  continuous_id.matrix_mul (continuous_regularizedRootInverse N)

theorem continuous_regularizedSupport (N : ℕ) :
    Continuous (fun K : Matrix (Fin p) (Fin m) ℂ => regularizedSupport K N) := by
  apply continuous_gram_cfc
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact ne_of_gt (add_pos_of_nonneg_of_pos (le_max_right x 0) (polarEpsilon_pos N))

theorem spectralReal_tendsto {a : Type*} [Fintype a] [DecidableEq a]
    {G : Matrix a a ℂ} (hG : G.IsHermitian) (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (h : ∀ i, Tendsto (fun N => F N (hG.eigenvalues i)) atTop (𝓝 (f (hG.eigenvalues i)))) :
    Tendsto (fun N => hG.cfc (F N)) atTop (𝓝 (hG.cfc f)) := by
  have hd : Tendsto (fun N => Matrix.diagonal (fun i => (F N (hG.eigenvalues i) : ℂ))) atTop
      (𝓝 (Matrix.diagonal (fun i => (f (hG.eigenvalues i) : ℂ)))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.diagonal_apply, Function.comp_def] using
        (Complex.continuous_ofReal.tendsto (f (hG.eigenvalues i))).comp (h i)
    · simpa [Matrix.diagonal_apply, hij] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  simpa only [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Function.comp_def] using!
    (tendsto_const_nhds.mul hd).mul tendsto_const_nhds

private theorem scalar_support_tendsto (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun N => max x 0 / (max x 0 + polarEpsilon N)) atTop
      (𝓝 (if Real.sqrt x = 0 then 0 else 1)) := by
  by_cases hz : x = 0
  · subst x
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne hx (Ne.symm hz)))
    simpa [max_eq_left hx, hs, hz] using!
      (tendsto_const_nhds.div (tendsto_const_nhds.add polarEpsilon_tendsto) (by simpa using hz) :
        Tendsto (fun N => x / (x + polarEpsilon N)) atTop (𝓝 (x / (x + 0))))

theorem tendsto_regularizedSupport (K : Matrix (Fin p) (Fin m) ℂ) :
    Tendsto (regularizedSupport K) atTop (𝓝 (supportGram K)) := by
  unfold regularizedSupport supportGram
  simp_rw [(Matrix.isHermitian_conjTranspose_mul_self K).cfc_eq]
  exact spectralReal_tendsto _ _ _ (fun i => scalar_support_tendsto _
    (Matrix.eigenvalues_conjTranspose_mul_self_nonneg K i))

private theorem scalar_polar_tendsto (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun N => (if Real.sqrt x = 0 then 0 else 1) *
      (Real.sqrt (max x 0 + polarEpsilon N))⁻¹) atTop (𝓝 (Real.sqrt x)⁻¹) := by
  by_cases hs : Real.sqrt x = 0
  · simpa [hs] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have hAdd : Tendsto (fun N => x + polarEpsilon N) atTop (𝓝 x) := by
      simpa using (tendsto_const_nhds.add polarEpsilon_tendsto)
    have h := (Real.continuous_sqrt.tendsto x).comp hAdd
    simpa [max_eq_left hx, hs, Function.comp_def] using h.inv₀ hs

theorem tendsto_regularizedPolar (K : Matrix (Fin p) (Fin m) ℂ) :
    Tendsto (regularizedPolar K) atTop (𝓝 (polarPartialIsometry K)) := by
  have heq (N : ℕ) : regularizedPolar K N = K *
      (Matrix.isHermitian_conjTranspose_mul_self K).cfc (fun x =>
        (if Real.sqrt x = 0 then 0 else 1) * (Real.sqrt (max x 0 + polarEpsilon N))⁻¹) := by
    calc
      _ = (K * supportGram K) * regularizedRootInverse K N := by
        rw [kraus_mul_supportGram]
        rfl
      _ = K * (supportGram K * regularizedRootInverse K N) := Matrix.mul_assoc _ _ _
      _ = _ := by
        rw [regularizedRootInverse, (Matrix.isHermitian_conjTranspose_mul_self K).cfc_eq,
          supportGram, spectralReal_mul]
  change Tendsto (fun N => regularizedPolar K N) atTop _
  simp_rw [heq]
  have hlim : Tendsto (fun N => (Matrix.isHermitian_conjTranspose_mul_self K).cfc (fun x =>
      (if Real.sqrt x = 0 then 0 else 1) * (Real.sqrt (max x 0 + polarEpsilon N))⁻¹)) atTop
      (𝓝 (rootPseudoInverse K)) :=
    spectralReal_tendsto _ _ _ (fun i => scalar_polar_tendsto _
      (Matrix.eigenvalues_conjTranspose_mul_self_nonneg K i))
  simpa only [Function.comp_def, polarPartialIsometry] using
    ((continuous_const.matrix_mul continuous_id :
      Continuous (fun M : Matrix (Fin m) (Fin m) ℂ => K * M)).tendsto (rootPseudoInverse K)).comp hlim

theorem measurable_supportGram : Measurable (supportGram (p := p) (m := m)) :=
  measurable_of_tendsto_metrizable (fun N => (continuous_regularizedSupport N).measurable)
    (tendsto_pi_nhds.mpr tendsto_regularizedSupport)

theorem measurable_polarPartialIsometry : Measurable (polarPartialIsometry (p := p) (m := m)) :=
  measurable_of_tendsto_metrizable (fun N => (continuous_regularizedPolar N).measurable)
    (tendsto_pi_nhds.mpr tendsto_regularizedPolar)

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

noncomputable section

variable {m p : ℕ}

open MeasureTheory

set_option maxHeartbeats 800000

theorem measurable_complementGram : Measurable (complementGram (p := p) (m := m)) :=
  measurable_const.sub measurable_supportGram

theorem measurable_rectangularRecoveryKraus (hp : 0 < p) (q : Unit ⊕ Fin m) :
    Measurable (fun K : Matrix (Fin p) (Fin m) ℂ => rectangularRecoveryKraus hp K q) := by
  cases q with
  | inl u => exact measurable_polarPartialIsometry
  | inr j =>
    exact (continuous_const.matrix_mul continuous_id :
      Continuous (fun Q : Matrix (Fin m) (Fin m) ℂ => resetRow hp j * Q)).measurable.comp
      measurable_complementGram

theorem stronglyMeasurable_rectangularRecoveryKraus (hp : 0 < p) (q : Unit ⊕ Fin m) :
    StronglyMeasurable (fun K : Matrix (Fin p) (Fin m) ℂ => rectangularRecoveryKraus hp K q) :=
  (measurable_rectangularRecoveryKraus hp q).stronglyMeasurable

private theorem measurable_rectangular_mul {Ω a b c : Type*} [MeasurableSpace Ω]
    [Fintype a] [Fintype b] [Fintype c]
    (A : Ω → Matrix a b ℂ) (B : Ω → Matrix b c ℂ) (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun z => A z * B z) := by
  have hAe (i : a) (j : b) : Measurable (fun z => A z i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)
  have hBe (i : b) (j : c) : Measurable (fun z => B z i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hB)
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ (fun k _ => (hAe i k).mul (hBe k j))

private theorem measurable_rectangular_adjoint {Ω a b : Type*} [MeasurableSpace Ω] [Fintype a] [Fintype b]
    (A : Ω → Matrix a b ℂ) (hA : Measurable A) : Measurable (fun z => (A z)ᴴ) :=
  (continuous_id.matrix_conjTranspose : Continuous (fun A : Matrix a b ℂ => Aᴴ)).measurable.comp hA

theorem measurable_rectangularRecovery_application (hp : 0 < p) :
    Measurable (fun z : Matrix (Fin p) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ =>
      rectangularRecovery hp z.1 z.2) := by
  change Measurable (fun z : Matrix (Fin p) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ =>
    ∑ q : Unit ⊕ Fin m, rectangularRecoveryKraus hp z.1 q * z.2 * (rectangularRecoveryKraus hp z.1 q)ᴴ)
  apply Finset.measurable_sum
  intro q _
  have hq : Measurable (fun z : Matrix (Fin p) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ =>
      rectangularRecoveryKraus hp z.1 q) := (measurable_rectangularRecoveryKraus hp q).comp measurable_fst
  exact measurable_rectangular_mul _ _ (measurable_rectangular_mul _ _ hq measurable_snd)
    (measurable_rectangular_adjoint _ hq)

theorem stronglyMeasurable_rectangularRecovery_application (hp : 0 < p) :
    StronglyMeasurable (fun z : Matrix (Fin p) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ =>
      rectangularRecovery hp z.1 z.2) :=
  (measurable_rectangularRecovery_application hp).stronglyMeasurable

theorem measurable_rectangularRecovery_of_measurable {Ω : Type*} [MeasurableSpace Ω]
    (hp : 0 < p) (K : Ω → Matrix (Fin p) (Fin m) ℂ) (X : Ω → Matrix (Fin m) (Fin m) ℂ)
    (hK : Measurable K) (hX : Measurable X) :
    Measurable (fun z => rectangularRecovery hp (K z) (X z)) := by
  simpa only [Function.comp_def] using!
    (measurable_rectangularRecovery_application (m := m) (p := p) hp).comp (hK.prodMk hX)

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator
open Filter Topology

noncomputable section

set_option maxHeartbeats 800000

variable {m p : ℕ}

def regularizedRoot (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  cfc (fun x : ℝ => Real.sqrt (max x 0 + polarEpsilon N)) (Kᴴ * K)

theorem regularized_shift_spectral (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) :
    Kᴴ * K + polarEpsilon N • (1 : Matrix (Fin m) (Fin m) ℂ) =
      (Matrix.isHermitian_conjTranspose_mul_self K).cfc (fun x => x + polarEpsilon N) := by
  have hid : cfc (fun x : ℝ => x) (Kᴴ * K) = Kᴴ * K := by
    simpa using! (cfc_id' ℝ (Kᴴ * K) (Matrix.isHermitian_conjTranspose_mul_self K))
  have hc : cfc (fun _ : ℝ => polarEpsilon N) (Kᴴ * K) =
      polarEpsilon N • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using!
      (cfc_const (polarEpsilon N) (Kᴴ * K) (Matrix.isHermitian_conjTranspose_mul_self K))
  rw [← (Matrix.isHermitian_conjTranspose_mul_self K).cfc_eq,
    cfc_add (Kᴴ * K) (fun x : ℝ => x) (fun _ : ℝ => polarEpsilon N), hid, hc]

theorem regularizedRoot_square (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) :
    regularizedRoot K N * regularizedRoot K N =
      Kᴴ * K + polarEpsilon N • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  simp only [regularizedRoot, (Matrix.isHermitian_conjTranspose_mul_self K).cfc_eq]
  rw [spectralReal_mul, regularized_shift_spectral]
  apply spectralReal_eq
  intro i
  have hn := Matrix.eigenvalues_conjTranspose_mul_self_nonneg K i
  rw [max_eq_left hn, Real.mul_self_sqrt (add_nonneg hn (le_of_lt (polarEpsilon_pos N)))]

theorem regularizedRoot_nonneg (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) :
    0 ≤ regularizedRoot K N :=
  cfc_nonneg (fun _ _ => Real.sqrt_nonneg _)

theorem regularizedRoot_eq_sqrt (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) :
    CFC.sqrt (Kᴴ * K + polarEpsilon N • (1 : Matrix (Fin m) (Fin m) ℂ)) =
      regularizedRoot K N :=
  CFC.sqrt_unique (regularizedRoot_square K N) (regularizedRoot_nonneg K N)

theorem regularizedGramInverse_mul_shift (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) :
    regularizedGramInverse K N *
      (Kᴴ * K + polarEpsilon N • (1 : Matrix (Fin m) (Fin m) ℂ)) = 1 := by
  rw [regularizedGramInverse, (Matrix.isHermitian_conjTranspose_mul_self K).cfc_eq,
    regularized_shift_spectral, spectralReal_mul]
  calc
    _ = (Matrix.isHermitian_conjTranspose_mul_self K).cfc (fun _ => 1) := by
      apply spectralReal_eq
      intro i
      have hn := Matrix.eigenvalues_conjTranspose_mul_self_nonneg K i
      rw [max_eq_left hn]
      exact inv_mul_cancel₀ (ne_of_gt (add_pos_of_nonneg_of_pos hn (polarEpsilon_pos N)))
    _ = 1 := by
      rw [← (Matrix.isHermitian_conjTranspose_mul_self K).cfc_eq]
      simpa using! (cfc_const_one ℝ (Kᴴ * K) (Matrix.isHermitian_conjTranspose_mul_self K))

theorem regularizedGramInverse_eq_inverse (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) :
    regularizedGramInverse K N =
      (Kᴴ * K + polarEpsilon N • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ :=
  (Matrix.inv_eq_left_inv (regularizedGramInverse_mul_shift K N)).symm

theorem regularizedRootInverse_mul_root (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) :
    regularizedRootInverse K N * regularizedRoot K N = 1 := by
  rw [regularizedRootInverse, regularizedRoot,
    (Matrix.isHermitian_conjTranspose_mul_self K).cfc_eq,
    (Matrix.isHermitian_conjTranspose_mul_self K).cfc_eq, spectralReal_mul]
  calc
    _ = (Matrix.isHermitian_conjTranspose_mul_self K).cfc (fun _ => 1) := by
      apply spectralReal_eq
      intro i
      exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr
        (add_pos_of_nonneg_of_pos (le_max_right _ 0) (polarEpsilon_pos N))))
    _ = 1 := by
      rw [← (Matrix.isHermitian_conjTranspose_mul_self K).cfc_eq]
      simpa using! (cfc_const_one ℝ (Kᴴ * K) (Matrix.isHermitian_conjTranspose_mul_self K))

theorem regularizedRootInverse_eq_inverse_sqrt (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) :
    regularizedRootInverse K N =
      (CFC.sqrt (Kᴴ * K + polarEpsilon N • (1 : Matrix (Fin m) (Fin m) ℂ)))⁻¹ := by
  rw [regularizedRoot_eq_sqrt]
  exact (Matrix.inv_eq_left_inv (regularizedRootInverse_mul_root K N)).symm

theorem regularizedPolar_eq_inverse_sqrt (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) :
    regularizedPolar K N =
      K * (CFC.sqrt (Kᴴ * K + polarEpsilon N • (1 : Matrix (Fin m) (Fin m) ℂ)))⁻¹ := by
  rw [regularizedPolar, regularizedRootInverse_eq_inverse_sqrt]

theorem regularizedSupport_eq_gram_inverse (K : Matrix (Fin p) (Fin m) ℂ) (N : ℕ) :
    regularizedSupport K N = (Kᴴ * K) *
      (Kᴴ * K + polarEpsilon N • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ := by
  have hid : (Matrix.isHermitian_conjTranspose_mul_self K).cfc (fun x => x) = Kᴴ * K := by
    rw [← (Matrix.isHermitian_conjTranspose_mul_self K).cfc_eq]
    simpa using! (cfc_id' ℝ (Kᴴ * K) (Matrix.isHermitian_conjTranspose_mul_self K))
  calc
    _ = (Matrix.isHermitian_conjTranspose_mul_self K).cfc (fun x => x) *
        (Matrix.isHermitian_conjTranspose_mul_self K).cfc
          (fun x => (max x 0 + polarEpsilon N)⁻¹) := by
      rw [regularizedSupport, (Matrix.isHermitian_conjTranspose_mul_self K).cfc_eq, spectralReal_mul]
      apply spectralReal_eq
      intro i
      simp [max_eq_left (Matrix.eigenvalues_conjTranspose_mul_self_nonneg K i), div_eq_mul_inv]
    _ = (Kᴴ * K) * regularizedGramInverse K N := by
      rw [hid, ← (Matrix.isHermitian_conjTranspose_mul_self K).cfc_eq]
      rfl
    _ = _ := by rw [regularizedGramInverse_eq_inverse]

theorem tendsto_polar_inverse_sqrt (K : Matrix (Fin p) (Fin m) ℂ) :
    Tendsto (fun N => K *
      (CFC.sqrt (Kᴴ * K + polarEpsilon N • (1 : Matrix (Fin m) (Fin m) ℂ)))⁻¹)
      atTop (𝓝 (polarPartialIsometry K)) := by
  have h := tendsto_regularizedPolar K
  change Tendsto (fun N => regularizedPolar K N) atTop _ at h
  simpa only [regularizedPolar_eq_inverse_sqrt] using h

theorem tendsto_support_gram_inverse (K : Matrix (Fin p) (Fin m) ℂ) :
    Tendsto (fun N => (Kᴴ * K) *
      (Kᴴ * K + polarEpsilon N • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹)
      atTop (𝓝 (supportGram K)) := by
  have h := tendsto_regularizedSupport K
  change Tendsto (fun N => regularizedSupport K N) atTop _ at h
  simpa only [regularizedSupport_eq_gram_inverse] using h

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

set_option maxHeartbeats 800000

def MatrixUnitMeasurable {Z I O : Type*} [MeasurableSpace Z] [DecidableEq I]
    (Φ : Z → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) : Prop :=
  ∀ i j b c, Measurable (fun z => Φ z (Matrix.single i j 1) b c)

theorem matrixMap_apply_eq_sum_matrix_units {I O : Type*} [Fintype I] [DecidableEq I]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (X : Matrix I I ℂ) :
    Φ X = ∑ i : I, ∑ j : I, X i j • Φ (Matrix.single i j 1) := by
  have hX : X = ∑ i : I, ∑ j : I, X i j • Matrix.single i j (1 : ℂ) := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single X
  conv_lhs => rw [hX]
  simp only [map_sum, map_smul]

theorem measurable_matrixMap_apply {Z I O : Type*} [MeasurableSpace Z]
    [Fintype I] [DecidableEq I]
    (Φ : Z → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) (hΦ : MatrixUnitMeasurable Φ)
    (X : Z → Matrix I I ℂ) (hX : Measurable X) :
    Measurable (fun z => Φ z (X z)) := by
  have hXe (i j : I) : Measurable (fun z => X z i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hX)
  refine Measurable.of_eval fun b => Measurable.of_eval fun c => ?_
  have heq : (fun z => Φ z (X z) b c) =
      (fun z => ∑ i : I, ∑ j : I, X z i j * Φ z (Matrix.single i j 1) b c) := by
    funext z
    rw [matrixMap_apply_eq_sum_matrix_units (Φ z) (X z)]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
    (fun j _ => (hXe i j).mul (hΦ i j b c)))

theorem stronglyMeasurable_matrixMap_apply {Z I O : Type*} [MeasurableSpace Z]
    [Fintype I] [DecidableEq I] [Fintype O]
    (Φ : Z → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)) (hΦ : MatrixUnitMeasurable Φ)
    (X : Z → Matrix I I ℂ) (hX : Measurable X) :
    StronglyMeasurable (fun z => Φ z (X z)) := by
  classical
  exact (measurable_matrixMap_apply Φ hΦ X hX).stronglyMeasurable

section JointRecoveryAbsorption

variable {H Ω O : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable {m p : ℕ}

def pendingRecoveryField (hp : 0 < p) (K : H → Matrix (Fin p) (Fin m) ℂ) :
    H → LocalRecovery m p := fun h => LocalRecovery.rectangular hp (K h)

def recoveryAbsorbedField (hp : 0 < p) (K : H → Matrix (Fin p) (Fin m) ℂ)
    (Φ : H × Ω → (Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix O O ℂ)) :
    H × Ω → (Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix O O ℂ) :=
  fun z => (Φ z).comp (pendingRecoveryField hp K z.1).map

theorem measurable_pendingRecoveryField_apply (hp : 0 < p)
    (K : H → Matrix (Fin p) (Fin m) ℂ) (hK : Measurable K)
    (X : H × Ω → Matrix (Fin m) (Fin m) ℂ) (hX : Measurable X) :
    Measurable (fun z => (pendingRecoveryField hp K z.1).map (X z)) :=
  measurable_rectangularRecovery_of_measurable hp (fun z : H × Ω => K z.1) X
    (hK.comp measurable_fst) hX

theorem recoveryAbsorbedField_matrixUnitMeasurable (hp : 0 < p)
    (K : H → Matrix (Fin p) (Fin m) ℂ) (hK : Measurable K)
    (Φ : H × Ω → (Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : MatrixUnitMeasurable Φ) : MatrixUnitMeasurable (recoveryAbsorbedField hp K Φ) := by
  intro i j b c
  have hR : Measurable (fun z : H × Ω =>
      (pendingRecoveryField hp K z.1).map (Matrix.single i j 1)) :=
    measurable_pendingRecoveryField_apply hp K hK _ measurable_const
  have h := measurable_matrixMap_apply Φ hΦ _ hR
  exact (measurable_pi_apply c).comp ((measurable_pi_apply b).comp h)

theorem measurable_recoveryAbsorbedField_apply (hp : 0 < p)
    (K : H → Matrix (Fin p) (Fin m) ℂ) (hK : Measurable K)
    (Φ : H × Ω → (Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : MatrixUnitMeasurable Φ) (X : H × Ω → Matrix (Fin m) (Fin m) ℂ)
    (hX : Measurable X) : Measurable (fun z => recoveryAbsorbedField hp K Φ z (X z)) :=
  measurable_matrixMap_apply _ (recoveryAbsorbedField_matrixUnitMeasurable hp K hK Φ hΦ) X hX

theorem stronglyMeasurable_recoveryAbsorbedField_apply [Fintype O] (hp : 0 < p)
    (K : H → Matrix (Fin p) (Fin m) ℂ) (hK : Measurable K)
    (Φ : H × Ω → (Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : MatrixUnitMeasurable Φ) (X : H × Ω → Matrix (Fin m) (Fin m) ℂ)
    (hX : Measurable X) : StronglyMeasurable (fun z => recoveryAbsorbedField hp K Φ z (X z)) := by
  classical
  exact (measurable_recoveryAbsorbedField_apply hp K hK Φ hΦ X hX).stronglyMeasurable

theorem recoveryAbsorbedField_completelyPositive [Fintype O] [DecidableEq O]
    (hp : 0 < p) (K : H → Matrix (Fin p) (Fin m) ℂ)
    (Φ : H × Ω → (Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : ∀ z, CompletelyPositive (Φ z)) (z : H × Ω) :
    CompletelyPositive (recoveryAbsorbedField hp K Φ z) :=
  (hΦ z).comp (pendingRecoveryField hp K z.1).completelyPositive

theorem recoveryAbsorbedField_matrixTraceComplete [Fintype O]
    (hp : 0 < p) (K : H → Matrix (Fin p) (Fin m) ℂ)
    (Φ : H × Ω → (Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix O O ℂ)) (μ : H → Measure Ω)
    (htrace : ∀ h (Y : Matrix (Fin p) (Fin p) ℂ),
      (∫ ω, (Φ (h, ω) Y).trace ∂μ h) = Y.trace)
    (h : H) (X : Matrix (Fin m) (Fin m) ℂ) :
    (∫ ω, (recoveryAbsorbedField hp K Φ (h, ω) X).trace ∂μ h) = X.trace := by
  change (∫ ω, (Φ (h, ω) ((pendingRecoveryField hp K h).map X)).trace ∂μ h) = X.trace
  rw [htrace, (pendingRecoveryField hp K h).trace_preserving]

theorem recoveryAbsorbedField_eq_absorbedRecoveryInstrument {out : ℕ}
    (hp : 0 < p) (K : H → Matrix (Fin p) (Fin m) ℂ)
    (Φ : H × Ω → (Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix (Fin out) (Fin out) ℂ))
    (z : H × Ω) :
    recoveryAbsorbedField hp K Φ z =
      absorbedRecoveryInstrument hp (K z.1) (fun _ : Ω => out) (fun ω => Φ (z.1, ω)) z.2 := rfl

end JointRecoveryAbsorption

section SetwiseRecoveryAbsorption

variable {H Ω O : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable {m p : ℕ}

def setwiseRecoveryAbsorbedField (hp : 0 < p) (K : H → Matrix (Fin p) (Fin m) ℂ)
    (Φ : H → Set Ω → (Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix O O ℂ))
    (h : H) (B : Set Ω) : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix O O ℂ :=
  (Φ h B).comp (pendingRecoveryField hp K h).map

theorem setwiseRecoveryAbsorbedField_matrixUnitMeasurable (hp : 0 < p)
    (K : H → Matrix (Fin p) (Fin m) ℂ) (hK : Measurable K)
    (Φ : H → Set Ω → (Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : ∀ B, MeasurableSet B → MatrixUnitMeasurable (fun h => Φ h B))
    (B : Set Ω) (hB : MeasurableSet B) :
    MatrixUnitMeasurable (fun h => setwiseRecoveryAbsorbedField hp K Φ h B) := by
  intro i j b c
  have hR : Measurable (fun h => (pendingRecoveryField hp K h).map (Matrix.single i j 1)) :=
    measurable_rectangularRecovery_of_measurable hp K _ hK measurable_const
  have h := measurable_matrixMap_apply (fun h => Φ h B) (hΦ B hB) _ hR
  exact (measurable_pi_apply c).comp ((measurable_pi_apply b).comp h)

theorem measurable_setwiseRecoveryAbsorbedField_apply (hp : 0 < p)
    (K : H → Matrix (Fin p) (Fin m) ℂ) (hK : Measurable K)
    (Φ : H → Set Ω → (Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : ∀ B, MeasurableSet B → MatrixUnitMeasurable (fun h => Φ h B))
    (B : Set Ω) (hB : MeasurableSet B) (X : H → Matrix (Fin m) (Fin m) ℂ) (hX : Measurable X) :
    Measurable (fun h => setwiseRecoveryAbsorbedField hp K Φ h B (X h)) :=
  measurable_matrixMap_apply _ (setwiseRecoveryAbsorbedField_matrixUnitMeasurable hp K hK Φ hΦ B hB) X hX

theorem setwiseRecoveryAbsorbedField_completelyPositive [Fintype O] [DecidableEq O]
    (hp : 0 < p) (K : H → Matrix (Fin p) (Fin m) ℂ)
    (Φ : H → Set Ω → (Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : ∀ h B, MeasurableSet B → CompletelyPositive (Φ h B))
    (h : H) (B : Set Ω) (hB : MeasurableSet B) :
    CompletelyPositive (setwiseRecoveryAbsorbedField hp K Φ h B) :=
  (hΦ h B hB).comp (pendingRecoveryField hp K h).completelyPositive

theorem setwiseRecoveryAbsorbedField_matrixTraceComplete [Fintype O]
    (hp : 0 < p) (K : H → Matrix (Fin p) (Fin m) ℂ)
    (Φ : H → Set Ω → (Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix O O ℂ))
    (htrace : ∀ h (Y : Matrix (Fin p) (Fin p) ℂ), (Φ h Set.univ Y).trace = Y.trace)
    (h : H) (X : Matrix (Fin m) (Fin m) ℂ) :
    (setwiseRecoveryAbsorbedField hp K Φ h Set.univ X).trace = X.trace := by
  change (Φ h Set.univ ((pendingRecoveryField hp K h).map X)).trace = X.trace
  rw [htrace, (pendingRecoveryField hp K h).trace_preserving]

end SetwiseRecoveryAbsorption

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

set_option maxHeartbeats 800000

theorem stronglyMeasurable_setwiseRecoveryAbsorbedField_apply
    {H Ω O : Type*} [MeasurableSpace H] [MeasurableSpace Ω] [Fintype O] {m p : ℕ}
    (hp : 0 < p) (K : H → Matrix (Fin p) (Fin m) ℂ) (hK : Measurable K)
    (Φ : H → Set Ω → (Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : ∀ B, MeasurableSet B → MatrixUnitMeasurable (fun h => Φ h B))
    (B : Set Ω) (hB : MeasurableSet B) (X : H → Matrix (Fin m) (Fin m) ℂ) (hX : Measurable X) :
    StronglyMeasurable (fun h => setwiseRecoveryAbsorbedField hp K Φ h B (X h)) := by
  classical
  exact (measurable_setwiseRecoveryAbsorbedField_apply hp K hK Φ hΦ B hB X hX).stronglyMeasurable

theorem absorbedRecoveryInstrument_matrixUnitMeasurable
    {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω] {m p out : ℕ}
    (hp : 0 < p) (K : H → Matrix (Fin p) (Fin m) ℂ) (hK : Measurable K)
    (Φ : H × Ω → (Matrix (Fin p) (Fin p) ℂ →ₗ[ℂ] Matrix (Fin out) (Fin out) ℂ))
    (hΦ : MatrixUnitMeasurable Φ) :
    MatrixUnitMeasurable (fun z : H × Ω => absorbedRecoveryInstrument hp (K z.1)
      (fun _ : Ω => out) (fun ω => Φ (z.1, ω)) z.2) := by
  simpa only [← recoveryAbsorbedField_eq_absorbedRecoveryInstrument] using
    recoveryAbsorbedField_matrixUnitMeasurable hp K hK Φ hΦ

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

set_option maxHeartbeats 800000

theorem MatrixUnitMeasurable.comp {Z I P O : Type*} [MeasurableSpace Z]
    [Fintype I] [DecidableEq I] [Fintype P] [DecidableEq P]
    (Φ : Z → (Matrix P P ℂ →ₗ[ℂ] Matrix O O ℂ)) (hΦ : MatrixUnitMeasurable Φ)
    (Ψ : Z → (Matrix I I ℂ →ₗ[ℂ] Matrix P P ℂ)) (hΨ : MatrixUnitMeasurable Ψ) :
    MatrixUnitMeasurable (fun z => (Φ z).comp (Ψ z)) := by
  intro i j b c
  have hX : Measurable (fun z => Ψ z (Matrix.single i j 1)) :=
    Measurable.of_eval fun a => Measurable.of_eval fun d => hΨ i j a d
  have h := measurable_matrixMap_apply Φ hΦ _ hX
  exact (measurable_pi_apply c).comp ((measurable_pi_apply b).comp h)

theorem pendingRecoveryField_matrixUnitMeasurable
    {H : Type*} [MeasurableSpace H] {m p : ℕ} (hp : 0 < p)
    (K : H → Matrix (Fin p) (Fin m) ℂ) (hK : Measurable K) :
    MatrixUnitMeasurable (fun h => (pendingRecoveryField hp K h).map) := by
  intro i j b c
  have h := measurable_rectangularRecovery_of_measurable hp K
    (fun _ => Matrix.single i j 1) hK measurable_const
  exact (measurable_pi_apply c).comp ((measurable_pi_apply b).comp h)

theorem matrixUnitMeasurable_const {Z I O : Type*} [MeasurableSpace Z] [DecidableEq I]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : MatrixUnitMeasurable (fun _ : Z => Φ) :=
  fun _ _ _ _ => measurable_const

theorem localRecovery_comp_matrixUnitMeasurable
    {H : Type*} [MeasurableSpace H] {m p q : ℕ}
    (R : H → LocalRecovery m p) (S : H → LocalRecovery p q)
    (hR : MatrixUnitMeasurable (fun h => (R h).map))
    (hS : MatrixUnitMeasurable (fun h => (S h).map)) :
    MatrixUnitMeasurable (fun h => ((S h).comp (R h)).map) :=
  MatrixUnitMeasurable.comp _ hS _ hR

end

end QuantumProver.ElegantJointMeasurement.CP

namespace QuantumProver.ElegantJointMeasurement.CP

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

theorem canonicalRecovery_comp_const_matrixUnitMeasurable
    {H : Type*} [MeasurableSpace H] {m p q : ℕ} (hp : 0 < p)
    (K : H → Matrix (Fin p) (Fin m) ℂ) (hK : Measurable K) (S : LocalRecovery p q) :
    MatrixUnitMeasurable (fun h => (S.comp (LocalRecovery.rectangular hp (K h))).map) :=
  localRecovery_comp_matrixUnitMeasurable (fun h => LocalRecovery.rectangular hp (K h)) (fun _ => S)
    (pendingRecoveryField_matrixUnitMeasurable hp K hK) (matrixUnitMeasurable_const S.map)

theorem canonicalRecovery_unpad_matrixUnitMeasurable
    {H : Type*} [MeasurableSpace H] {m p q : ℕ} (hq : 0 < q) (hqp : q ≤ p)
    (K : H → Matrix (Fin p) (Fin m) ℂ) (hK : Measurable K) :
    MatrixUnitMeasurable (fun h => ((LocalRecovery.unpad hq hqp).comp
      (LocalRecovery.rectangular (Nat.lt_of_lt_of_le hq hqp) (K h))).map) :=
  canonicalRecovery_comp_const_matrixUnitMeasurable _ K hK (LocalRecovery.unpad hq hqp)

end

end QuantumProver.ElegantJointMeasurement.CP
