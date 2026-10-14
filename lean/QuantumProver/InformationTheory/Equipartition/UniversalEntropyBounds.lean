import Mathlib
import QuantumProver.InformationTheory.Equipartition.Definitions

noncomputable section

open scoped BigOperators
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace QuantumProver.Equipartition.FiniteModel

structure FiniteLaw (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  sum_weight : ∑ i, weight i = 1

namespace FiniteLaw

variable {ι : Type*} [Fintype ι] (L : FiniteLaw ι)

def expect (f : ι → ℝ) : ℝ := ∑ i, L.weight i * f i

def mass (S : Finset ι) : ℝ := ∑ i ∈ S, L.weight i

def mean (Z : ι → ℝ) : ℝ := L.expect Z

def secondMoment (Z : ι → ℝ) (c : ℝ) : ℝ :=
  L.expect (fun i => (Z i - c) ^ 2)

def variance (Z : ι → ℝ) : ℝ := L.secondMoment Z (L.mean Z)

def weightedSecondMoment (Z : ι → ℝ) (c t : ℝ) : ℝ :=
  L.expect (fun i => (Z i - c) ^ 2 * Real.exp (t * |Z i - c|))

theorem expect_nonneg {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ L.expect f := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (L.nonneg i) (hf i)

theorem exists_weight_pos : ∃ i, 0 < L.weight i := by
  by_contra h
  push_neg at h
  have hz : ∑ i, L.weight i = 0 :=
    Finset.sum_eq_zero fun i _ => le_antisymm (h i) (L.nonneg i)
  rw [L.sum_weight] at hz
  norm_num at hz

theorem expect_pos {f : ι → ℝ} (hf : ∀ i, 0 < f i) : 0 < L.expect f := by
  obtain ⟨i, hi⟩ := L.exists_weight_pos
  apply lt_of_lt_of_le (mul_pos hi (hf i))
  exact Finset.single_le_sum
    (fun j _ => mul_nonneg (L.nonneg j) (hf j).le) (Finset.mem_univ i)

theorem expect_mono {f g : ι → ℝ} (hfg : ∀ i, f i ≤ g i) :
    L.expect f ≤ L.expect g := by
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (hfg i) (L.nonneg i)

@[simp] theorem expect_const (c : ℝ) : L.expect (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, L.sum_weight, one_mul]

theorem expect_add (f g : ι → ℝ) :
    L.expect (fun i => f i + g i) = L.expect f + L.expect g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (f g : ι → ℝ) :
    L.expect (fun i => f i - g i) = L.expect f - L.expect g := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_smul (a : ℝ) (f : ι → ℝ) :
    L.expect (fun i => a * f i) = a * L.expect f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem expect_centered (Z : ι → ℝ) :
    L.expect (fun i => Z i - L.mean Z) = 0 := by
  rw [L.expect_sub, L.expect_const]
  simp [mean]

theorem mass_nonneg (S : Finset ι) : 0 ≤ L.mass S := by
  exact Finset.sum_nonneg fun i _ => L.nonneg i

theorem mass_le_one (S : Finset ι) : L.mass S ≤ 1 := by
  classical
  rw [← L.sum_weight]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun i _ _ => L.nonneg i)

theorem secondMoment_nonneg (Z : ι → ℝ) (c : ℝ) :
    0 ≤ L.secondMoment Z c := by
  exact L.expect_nonneg fun i => sq_nonneg (Z i - c)

theorem variance_nonneg (Z : ι → ℝ) : 0 ≤ L.variance Z :=
  L.secondMoment_nonneg Z (L.mean Z)

theorem secondMoment_decomposition (Z : ι → ℝ) (c : ℝ) :
    L.secondMoment Z c = L.variance Z + (L.mean Z - c) ^ 2 := by
  calc
    L.secondMoment Z c =
        L.expect (fun i =>
          (Z i - L.mean Z) ^ 2 +
            (2 * (L.mean Z - c)) * (Z i - L.mean Z) +
              (L.mean Z - c) ^ 2) := by
      unfold secondMoment
      congr 1
      funext i
      ring
    _ = L.variance Z + (L.mean Z - c) ^ 2 := by
      rw [L.expect_add, L.expect_add, L.expect_smul,
        L.expect_centered, L.expect_const]
      simp only [variance, secondMoment, mul_zero, add_zero]

theorem variance_le_secondMoment (Z : ι → ℝ) (c : ℝ) :
    L.variance Z ≤ L.secondMoment Z c := by
  rw [L.secondMoment_decomposition]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem secondMoment_le_weightedSecondMoment (Z : ι → ℝ) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    L.secondMoment Z c ≤ L.weightedSecondMoment Z c t := by
  apply L.expect_mono
  intro i
  have he : 1 ≤ Real.exp (t * |Z i - c|) :=
    Real.one_le_exp_iff.mpr (mul_nonneg ht (abs_nonneg _))
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left he (sq_nonneg (Z i - c))

theorem variance_le_weightedSecondMoment (Z : ι → ℝ) (c : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    L.variance Z ≤ L.weightedSecondMoment Z c t :=
  (L.variance_le_secondMoment Z c).trans
    (L.secondMoment_le_weightedSecondMoment Z c ht)

theorem mass_le_expect_div (S : Finset ι) {f : ι → ℝ} {a : ℝ}
    (hf : ∀ i, 0 ≤ f i) (ha : 0 < a) (hS : ∀ i ∈ S, a ≤ f i) :
    L.mass S ≤ L.expect f / a := by
  classical
  apply (le_div_iff₀ ha).mpr
  calc
    L.mass S * a = ∑ i ∈ S, L.weight i * a := by
      unfold mass
      rw [Finset.sum_mul]
    _ ≤ ∑ i ∈ S, L.weight i * f i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hS i hi) (L.nonneg i)
    _ ≤ L.expect f := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun i _ _ => mul_nonneg (L.nonneg i) (hf i))

theorem mass_le_secondMoment_div_sq (S : Finset ι) (Z : ι → ℝ)
    (c : ℝ) {a : ℝ} (ha : 0 < a)
    (hS : ∀ i ∈ S, a ≤ |Z i - c|) :
    L.mass S ≤ L.secondMoment Z c / a ^ 2 := by
  apply L.mass_le_expect_div S (fun i => sq_nonneg _) (sq_pos_of_pos ha)
  intro i hi
  have hp : 0 ≤ (|Z i - c| - a) * (|Z i - c| + a) :=
    mul_nonneg (sub_nonneg.mpr (hS i hi))
      (add_nonneg (abs_nonneg _) ha.le)
  nlinarith [sq_abs (Z i - c)]

theorem mass_le_of_secondMoment (S : Finset ι) (Z : ι → ℝ)
    (c : ℝ) {a ε : ℝ} (ha : 0 < a)
    (hS : ∀ i ∈ S, a ≤ |Z i - c|)
    (hbudget : L.secondMoment Z c ≤ ε * a ^ 2) :
    L.mass S ≤ ε := by
  apply (L.mass_le_secondMoment_div_sq S Z c ha hS).trans
  exact (div_le_iff₀ (sq_pos_of_pos ha)).mpr hbudget

def lowerTail [DecidableEq ι] (Z : ι → ℝ) (c a : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => Z i < c - a)

def upperTail [DecidableEq ι] (Z : ι → ℝ) (c a : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => c + a < Z i)

theorem lowerTail_mass_le [DecidableEq ι] (Z : ι → ℝ) (c : ℝ)
    {a : ℝ} (ha : 0 < a) :
    L.mass (lowerTail Z c a) ≤ L.secondMoment Z c / a ^ 2 := by
  apply L.mass_le_secondMoment_div_sq _ Z c ha
  intro i hi
  have h : Z i < c - a := (Finset.mem_filter.mp hi).2
  linarith [neg_le_abs (Z i - c)]

theorem upperTail_mass_le [DecidableEq ι] (Z : ι → ℝ) (c : ℝ)
    {a : ℝ} (ha : 0 < a) :
    L.mass (upperTail Z c a) ≤ L.secondMoment Z c / a ^ 2 := by
  apply L.mass_le_secondMoment_div_sq _ Z c ha
  intro i hi
  have h : c + a < Z i := (Finset.mem_filter.mp hi).2
  linarith [le_abs_self (Z i - c)]

theorem lowerTail_mass_le_laplace [DecidableEq ι] (Z : ι → ℝ)
    (c a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    L.mass (lowerTail Z c a) ≤
      Real.exp (-t * a) * L.expect (fun i => Real.exp (-t * (Z i - c))) := by
  have hm := L.mass_le_expect_div (lowerTail Z c a)
    (f := fun i => Real.exp (-t * (Z i - c)))
    (a := Real.exp (t * a)) (fun i => (Real.exp_pos _).le)
    (Real.exp_pos _) (by
      intro i hi
      apply Real.exp_le_exp.mpr
      have h : Z i < c - a := (Finset.mem_filter.mp hi).2
      have hp : 0 ≤ t * (-(Z i - c) - a) :=
        mul_nonneg ht (by linarith)
      nlinarith)
  calc
    L.mass (lowerTail Z c a) ≤
        L.expect (fun i => Real.exp (-t * (Z i - c))) / Real.exp (t * a) := hm
    _ = Real.exp (-t * a) *
        L.expect (fun i => Real.exp (-t * (Z i - c))) := by
      have he : Real.exp (-t * a) = (Real.exp (t * a))⁻¹ := by
        rw [neg_mul, Real.exp_neg]
      rw [div_eq_mul_inv, ← he]
      ring

end FiniteLaw

namespace Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def overlapWeight (U : Matrix.unitaryGroup ι ℂ) (i j : ι) : ℝ :=
  Complex.normSq ((U : CMat ι) i j)

theorem overlapWeight_nonneg (U : Matrix.unitaryGroup ι ℂ) (i j : ι) :
    0 ≤ overlapWeight U i j := Complex.normSq_nonneg _

theorem overlapWeight_sum_row (U : Matrix.unitaryGroup ι ℂ) (i : ι) :
    ∑ j, overlapWeight U i j = 1 := by
  have hu : (U : CMat ι) * (U : CMat ι)ᴴ = 1 := Unitary.coe_mul_star_self U
  have hi := congrArg (fun M : CMat ι => (M i i).re) hu
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj,
    Complex.re_sum, overlapWeight] using hi

theorem overlapWeight_sum_col (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    ∑ i, overlapWeight U i j = 1 := by
  have hu : (U : CMat ι)ᴴ * (U : CMat ι) = 1 := Unitary.coe_star_mul_self U
  have hj := congrArg (fun M : CMat ι => (M j j).re) hu
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_sum, overlapWeight] using hj

theorem trace_unitary_conjugate (U : Matrix.unitaryGroup ι ℂ) (X : CMat ι) :
    (Unitary.conjStarAlgAut ℝ (CMat ι) U X).trace = X.trace := by
  change ((U : CMat ι) * X * (U : CMat ι)ᴴ).trace = X.trace
  have hu : (U : CMat ι)ᴴ * (U : CMat ι) = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self U
  rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul]

theorem cfc_eq_conjugate (f : ℝ → ℝ) {A : CMat ι} (hA : A.IsHermitian) :
    cfc f A = Unitary.conjStarAlgAut ℝ (CMat ι) hA.eigenvectorUnitary
      (Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ))) := by
  exact hA.cfc_eq f

theorem trace_cfc_eq_sum (f : ℝ → ℝ) {A : CMat ι} (hA : A.IsHermitian) :
    (cfc f A).trace.re = ∑ i, f (hA.eigenvalues i) := by
  rw [cfc_eq_conjugate f hA, trace_unitary_conjugate, Matrix.trace_diagonal]
  simp [Complex.re_sum]

theorem trace_eq_sum_eigenvalues_re {A : CMat ι} (hA : A.IsHermitian) :
    A.trace.re = ∑ i, hA.eigenvalues i := by
  rw [hA.trace_eq_sum_eigenvalues]
  simp [Complex.re_sum]

theorem trace_diagonal_overlap (U : Matrix.unitaryGroup ι ℂ) (a b : ι → ℝ) :
    (Matrix.diagonal (fun i => (a i : ℂ)) *
      Unitary.conjStarAlgAut ℝ (CMat ι) U
        (Matrix.diagonal (fun j => (b j : ℂ)))).trace.re =
      ∑ i, ∑ j, a i * b j * overlapWeight U i j := by
  change (Matrix.diagonal (fun i => (a i : ℂ)) *
    ((U : CMat ι) * Matrix.diagonal (fun j => (b j : ℂ)) *
      (U : CMat ι)ᴴ)).trace.re = _
  have hentry (i : ι) : (Matrix.diagonal (fun i => (a i : ℂ)) *
      ((U : CMat ι) * Matrix.diagonal (fun j => (b j : ℂ)) *
        (U : CMat ι)ᴴ)) i i =
      ∑ j, (a i : ℂ) * (((U : CMat ι) i j * (b j : ℂ)) *
        starRingEnd ℂ ((U : CMat ι) i j)) := by
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Finset.mul_sum,
      Complex.star_def]
  simp only [Matrix.trace, Matrix.diag, hentry, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have h : (a i : ℂ) * (((U : CMat ι) i j * (b j : ℂ)) *
      starRingEnd ℂ ((U : CMat ι) i j)) =
      ((a i * b j : ℝ) : ℂ) *
        ((U : CMat ι) i j * starRingEnd ℂ ((U : CMat ι) i j)) := by
    push_cast
    ring
  rw [h, Complex.mul_conj, Complex.re_ofReal_mul]
  rfl

def overlapUnitary {A B : CMat ι} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Matrix.unitaryGroup ι ℂ := star hA.eigenvectorUnitary * hB.eigenvectorUnitary

theorem trace_cfc_mul_cfc_eq_overlap (f g : ℝ → ℝ) {A B : CMat ι}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (cfc f A * cfc g B).trace.re =
      ∑ i, ∑ j, f (hA.eigenvalues i) * g (hB.eigenvalues j) *
        overlapWeight (overlapUnitary hA hB) i j := by
  have ha := cfc_eq_conjugate f hA
  have hu : hA.eigenvectorUnitary * overlapUnitary hA hB = hB.eigenvectorUnitary := by
    simp [overlapUnitary, ← mul_assoc]
  have hp : cfc f A * cfc g B =
      Unitary.conjStarAlgAut ℝ (CMat ι) hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *
          Unitary.conjStarAlgAut ℝ (CMat ι) (overlapUnitary hA hB)
            (Matrix.diagonal (fun j => (g (hB.eigenvalues j) : ℂ)))) := by
    rw [map_mul, ← Unitary.conjStarAlgAut_mul_apply, hu,
      ← ha, ← cfc_eq_conjugate g hB]
  rw [hp, trace_unitary_conjugate, trace_diagonal_overlap]

theorem trace_mul_cfc_eq_overlap (f : ℝ → ℝ) {A B : CMat ι}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * cfc f B).trace.re =
      ∑ i, ∑ j, hA.eigenvalues i * f (hB.eigenvalues j) *
        overlapWeight (overlapUnitary hA hB) i j := by
  have ha : A = Unitary.conjStarAlgAut ℝ (CMat ι) hA.eigenvectorUnitary
      (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) := hA.spectral_theorem
  have hu : hA.eigenvectorUnitary * overlapUnitary hA hB = hB.eigenvectorUnitary := by
    simp [overlapUnitary, ← mul_assoc]
  have hp : A * cfc f B =
      Unitary.conjStarAlgAut ℝ (CMat ι) hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
          Unitary.conjStarAlgAut ℝ (CMat ι) (overlapUnitary hA hB)
            (Matrix.diagonal (fun j => (f (hB.eigenvalues j) : ℂ)))) := by
    rw [map_mul, ← Unitary.conjStarAlgAut_mul_apply, hu,
      ← ha, ← cfc_eq_conjugate f hB]
  rw [hp, trace_unitary_conjugate, trace_diagonal_overlap]

theorem trace_mul_cfc_self_eq_sum (f : ℝ → ℝ) {A : CMat ι}
    (hA : A.IsHermitian) :
    (A * cfc f A).trace.re = ∑ i, hA.eigenvalues i * f (hA.eigenvalues i) := by
  rw [trace_mul_cfc_eq_overlap f hA hA]
  have hu : overlapUnitary hA hA = 1 := by simp [overlapUnitary]
  rw [hu]
  simp [overlapWeight, Matrix.one_apply]

end Spectral

section MatrixNS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nsWeight_eq_overlap {ρ σ : CMat ι}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (i j : ι) :
    nsWeight ρ σ (i, j) = hρ.eigenvalues i *
      Spectral.overlapWeight (Spectral.overlapUnitary hρ hσ) i j := by
  simp only [nsWeight, spectrumValue_of_isHermitian hρ,
    spectrumUnitary_of_isHermitian hρ, spectrumUnitary_of_isHermitian hσ]
  rfl

theorem nsWeight_nonneg {ρ σ : CMat ι} (hρ : ρ.PosSemidef) (z : ι × ι) :
    0 ≤ nsWeight ρ σ z := by
  rw [nsWeight, spectrumValue_of_isHermitian hρ.1]
  exact mul_nonneg (hρ.eigenvalues_nonneg _) (Complex.normSq_nonneg _)

theorem nsWeight_sum {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.IsHermitian) :
    ∑ z, nsWeight ρ σ z = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [nsWeight_eq_overlap hρ.1.1 hσ, ← Finset.mul_sum,
    Spectral.overlapWeight_sum_row, mul_one]
  rw [← Spectral.trace_eq_sum_eigenvalues_re hρ.1.1]
  exact hρ.trace_real

def nsLaw (ρ σ : CMat ι) (hρ : IsState ρ) (hσ : σ.PosSemidef) :
    FiniteLaw (ι × ι) where
  weight := nsWeight ρ σ
  nonneg := nsWeight_nonneg hρ.1
  sum_weight := nsWeight_sum hρ hσ.1

theorem nsLaw_expect (ρ σ : CMat ι) (hρ : IsState ρ) (hσ : σ.PosSemidef)
    (f : ι × ι → ℝ) :
    (nsLaw ρ σ hρ hσ).expect f = nsExpectation ρ σ f := rfl

theorem nsLaw_weightedSecondMoment (ρ σ : CMat ι)
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (c t : ℝ) :
    (nsLaw ρ σ hρ hσ).weightedSecondMoment (nsLikelihood ρ σ) c t =
      nsWeightedMoment ρ σ c t := rfl

theorem nsLaw_variance_le_weightedMoment (ρ σ : CMat ι)
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (nsLaw ρ σ hρ hσ).variance (nsLikelihood ρ σ) ≤ nsWeightedMoment ρ σ c t :=
  (nsLaw ρ σ hρ hσ).variance_le_weightedSecondMoment (nsLikelihood ρ σ) c ht

theorem nsExpectation_null_spectral (f : ℝ → ℝ) {ρ σ : CMat ι}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    nsExpectation ρ σ (fun z => f (spectrumValue ρ z.1)) =
      ∑ i, hρ.eigenvalues i * f (hρ.eigenvalues i) := by
  unfold nsExpectation
  rw [Fintype.sum_prod_type]
  simp_rw [nsWeight_eq_overlap hρ hσ, spectrumValue_of_isHermitian hρ]
  calc
    (∑ i, ∑ j, hρ.eigenvalues i *
        Spectral.overlapWeight (Spectral.overlapUnitary hρ hσ) i j *
          f (hρ.eigenvalues i)) =
        ∑ i, hρ.eigenvalues i * f (hρ.eigenvalues i) *
          (∑ j, Spectral.overlapWeight (Spectral.overlapUnitary hρ hσ) i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by simp_rw [Spectral.overlapWeight_sum_row, mul_one]

theorem nsExpectation_alternative_spectral (f : ℝ → ℝ) {ρ σ : CMat ι}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    nsExpectation ρ σ (fun z => f (spectrumValue σ z.2)) =
      (ρ * cfc f σ).trace.re := by
  unfold nsExpectation
  rw [Fintype.sum_prod_type, Spectral.trace_mul_cfc_eq_overlap f hρ hσ]
  simp_rw [nsWeight_eq_overlap hρ hσ, spectrumValue_of_isHermitian hσ]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem nsExpectation_likelihood_eq_umegakiReal {ρ σ : CMat ι}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    nsExpectation ρ σ (nsLikelihood ρ σ) = umegakiReal ρ σ := by
  have hid : nsExpectation ρ σ (nsLikelihood ρ σ) =
      (nsExpectation ρ σ (fun z => Real.log (spectrumValue ρ z.1)) -
        nsExpectation ρ σ (fun z => Real.log (spectrumValue σ z.2))) / Real.log 2 := by
    unfold nsExpectation nsLikelihood logTwo
    calc
      _ = (∑ z, (nsWeight ρ σ z * Real.log (spectrumValue ρ z.1) -
          nsWeight ρ σ z * Real.log (spectrumValue σ z.2)) / Real.log 2) := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _ = _ := by rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [hid, nsExpectation_null_spectral Real.log hρ hσ,
    nsExpectation_alternative_spectral Real.log hρ hσ,
    ← Spectral.trace_mul_cfc_self_eq_sum Real.log hρ]
  simp only [umegakiReal, tracePair, matrixLog, Matrix.mul_sub,
    Matrix.trace_sub, Complex.sub_re]

theorem nsLaw_mean_eq_umegakiReal (ρ σ : CMat ι)
    (hρ : IsState ρ) (hσ : σ.PosSemidef) :
    (nsLaw ρ σ hρ hσ).mean (nsLikelihood ρ σ) = umegakiReal ρ σ :=
  nsExpectation_likelihood_eq_umegakiReal hρ.1.1 hσ.1

theorem nsLaw_mean_eq_umegaki (ρ σ : CMat ι)
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    ((nsLaw ρ σ hρ hσ).mean (nsLikelihood ρ σ) : EReal) = umegaki ρ σ := by
  rw [nsLaw_mean_eq_umegakiReal]
  simp only [umegaki, hs, if_true]

theorem overlapWeight_zero_of_alternative_kernel {ρ σ : CMat ι}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hs : SupportLE ρ σ)
    (i j : ι) (hr : hρ.eigenvalues i ≠ 0) (hq : hσ.eigenvalues j = 0) :
    Spectral.overlapWeight (Spectral.overlapUnitary hρ hσ) i j = 0 := by
  have hv : σ *ᵥ ⇑(hσ.eigenvectorBasis j) = 0 := by
    simpa [hq] using hσ.mulVec_eigenvectorBasis j
  have hρv := hs ⇑(hσ.eigenvectorBasis j) hv
  have hentry (k : ι) : (ρ * (hσ.eigenvectorUnitary : CMat ι)) k j = 0 := by
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hρv k
  have hdiag : (hρ.eigenvectorUnitary : CMat ι)ᴴ * ρ *
      (hρ.eigenvectorUnitary : CMat ι) =
      Matrix.diagonal (fun k => (hρ.eigenvalues k : ℂ)) :=
    by simpa only [Unitary.conjStarAlgAut_star_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using
      hρ.conjStarAlgAut_star_eigenvectorUnitary
  have hunit : (hρ.eigenvectorUnitary : CMat ι) *
      (hρ.eigenvectorUnitary : CMat ι)ᴴ = 1 :=
    Unitary.coe_mul_star_self hρ.eigenvectorUnitary
  have hmatrix : Matrix.diagonal (fun k => (hρ.eigenvalues k : ℂ)) *
      (Spectral.overlapUnitary hρ hσ : CMat ι) =
      (hρ.eigenvectorUnitary : CMat ι)ᴴ * ρ *
        (hσ.eigenvectorUnitary : CMat ι) := by
    rw [← hdiag]
    change (((hρ.eigenvectorUnitary : CMat ι)ᴴ * ρ *
        (hρ.eigenvectorUnitary : CMat ι)) *
          ((hρ.eigenvectorUnitary : CMat ι)ᴴ *
            (hσ.eigenvectorUnitary : CMat ι))) = _
    calc
      _ = (hρ.eigenvectorUnitary : CMat ι)ᴴ * ρ *
          (((hρ.eigenvectorUnitary : CMat ι) *
            (hρ.eigenvectorUnitary : CMat ι)ᴴ) *
              (hσ.eigenvectorUnitary : CMat ι)) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hunit, Matrix.one_mul]
  have hzero : ((hρ.eigenvectorUnitary : CMat ι)ᴴ * ρ *
      (hσ.eigenvectorUnitary : CMat ι)) i j = 0 := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp_rw [hentry, mul_zero]
    simp
  rw [← hmatrix, Matrix.diagonal_mul] at hzero
  have hrC : (hρ.eigenvalues i : ℂ) ≠ 0 := by exact_mod_cast hr
  have hz : (Spectral.overlapUnitary hρ hσ : CMat ι) i j = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hrC
  simp [Spectral.overlapWeight, hz]

theorem scalar_likelihood_exp (p q α : ℝ) (hp : 0 < p) (hq : 0 < q) :
    p * Real.exp ((α - 1) * Real.log 2 * (logTwo p - logTwo q)) =
      Real.rpow p α * Real.rpow q (1 - α) := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  calc
    p * Real.exp ((α - 1) * Real.log 2 * (logTwo p - logTwo q)) =
        Real.exp (Real.log p) *
          Real.exp ((α - 1) * Real.log 2 * (logTwo p - logTwo q)) := by
      rw [Real.exp_log hp]
    _ = Real.exp (Real.log p +
        (α - 1) * Real.log 2 * (logTwo p - logTwo q)) :=
      (Real.exp_add _ _).symm
    _ = Real.exp (Real.log p * α + Real.log q * (1 - α)) := by
      congr 1
      unfold logTwo
      field_simp [hlog]
      <;> ring
    _ = Real.rpow p α * Real.rpow q (1 - α) := by
      rw [Real.exp_add]
      congr 1
      · exact (Real.rpow_def_of_pos hp α).symm
      · exact (Real.rpow_def_of_pos hq (1 - α)).symm

theorem nsExpectation_exp_eq_petzTrace {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 0 < α) :
    nsExpectation ρ σ (fun z =>
      Real.exp ((α - 1) * Real.log 2 * nsLikelihood ρ σ z)) =
      petzTrace ρ σ α := by
  unfold nsExpectation petzTrace tracePair matrixRpow
  rw [Fintype.sum_prod_type,
    Spectral.trace_cfc_mul_cfc_eq_overlap _ _ hρ.1.1 hσ.1]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [nsWeight_eq_overlap hρ.1.1 hσ.1]
  simp only [nsLikelihood, spectrumValue_of_isHermitian hρ.1.1,
    spectrumValue_of_isHermitian hσ.1]
  by_cases hr : hρ.1.1.eigenvalues i = 0
  · simp [hr, Real.zero_rpow hα.ne']
  have hrpos : 0 < hρ.1.1.eigenvalues i :=
    lt_of_le_of_ne (hρ.1.eigenvalues_nonneg i) (Ne.symm hr)
  by_cases hq : hσ.1.eigenvalues j = 0
  · have hw := overlapWeight_zero_of_alternative_kernel hρ.1.1 hσ.1 hs i j hr hq
    simp [hw]
  have hqpos : 0 < hσ.1.eigenvalues j :=
    lt_of_le_of_ne (hσ.eigenvalues_nonneg j) (Ne.symm hq)
  rw [mul_right_comm]
  rw [scalar_likelihood_exp _ _ α hrpos hqpos]

theorem nsLaw_exp_eq_petzTrace (ρ σ : CMat ι)
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 0 < α) :
    (nsLaw ρ σ hρ hσ).expect (fun z =>
      Real.exp ((α - 1) * Real.log 2 * nsLikelihood ρ σ z)) =
      petzTrace ρ σ α :=
  nsExpectation_exp_eq_petzTrace hρ hσ hs hα

theorem petzTrace_pos_of_support (ρ σ : CMat ι)
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 0 < α) : 0 < petzTrace ρ σ α := by
  have hp := (nsLaw ρ σ hρ hσ).expect_pos
    (fun z => Real.exp_pos ((α - 1) * Real.log 2 * nsLikelihood ρ σ z))
  rw [nsLaw_exp_eq_petzTrace ρ σ hρ hσ hs hα] at hp
  exact hp

theorem petzDivergence_of_support (ρ σ : CMat ι)
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) :
    petzDivergence ρ σ α =
      (logTwo (petzTrace ρ σ α) / (α - 1) : EReal) := by
  have hp := petzTrace_pos_of_support ρ σ hρ hσ hs hα
  simp [petzDivergence, hα1, hs, ne_of_gt hp]

theorem nsLaw_laplace_centered (ρ σ : CMat ι)
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    (c t : ℝ) (hα : 0 < 1 - t / Real.log 2) :
    (nsLaw ρ σ hρ hσ).expect (fun z =>
      Real.exp (-t * (nsLikelihood ρ σ z - c))) =
      Real.exp (t * c) * petzTrace ρ σ (1 - t / Real.log 2) := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have he : (fun z => Real.exp (-t * (nsLikelihood ρ σ z - c))) =
      (fun z => Real.exp (t * c) * Real.exp (-t * nsLikelihood ρ σ z)) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, FiniteLaw.expect_smul]
  congr 1
  rw [← nsLaw_exp_eq_petzTrace ρ σ hρ hσ hs hα]
  apply congrArg (nsLaw ρ σ hρ hσ).expect
  funext z
  congr 1
  field_simp [hlog]
  <;> ring

end MatrixNS

namespace ScalarRate

open Filter Set
open scoped Topology

def rateSet (u : ℕ → ℝ) : Set ℝ :=
  {r | ∃ n : ℕ, 0 < n ∧ r = u n / (n : ℝ)}

def infRate (u : ℕ → ℝ) : ℝ := sInf (rateSet u)

def supRate (u : ℕ → ℝ) : ℝ := sSup (rateSet u)

def zeroExtension (u : ℕ → ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else u n

theorem rateSet_nonempty (u : ℕ → ℝ) : (rateSet u).Nonempty :=
  ⟨u 1 / (1 : ℝ), 1, by norm_num, by norm_num⟩

theorem zeroExtension_subadditive (u : ℕ → ℝ)
    (h : ∀ m n : ℕ, 0 < m → 0 < n → u (m + n) ≤ u m + u n) :
    Subadditive (zeroExtension u) := by
  intro m n
  by_cases hm : m = 0
  · simp [zeroExtension, hm]
  by_cases hn : n = 0
  · simp [zeroExtension, hn]
  have hmn : m + n ≠ 0 := by omega
  simpa [zeroExtension, hm, hn, hmn] using
    h m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

theorem zeroExtension_normalized_lower (u : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 0 < n → -C * (n : ℝ) ≤ u n) (n : ℕ) :
    -C ≤ zeroExtension u n / (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn, hC]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  apply (le_div_iff₀ hnR).mpr
  simpa [zeroExtension, hn] using h n (Nat.pos_of_ne_zero hn)

theorem zeroExtension_rates_bddBelow (u : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n : ℕ, 0 < n → -C * (n : ℝ) ≤ u n) :
    BddBelow (range fun n => zeroExtension u n / (n : ℝ)) := by
  refine ⟨-C, ?_⟩
  rintro x ⟨n, rfl⟩
  exact zeroExtension_normalized_lower u hC h n

theorem zeroExtension_rate_eq (u : ℕ → ℝ) (h : Subadditive (zeroExtension u)) :
    h.lim = infRate u := by
  rw [Subadditive.lim]
  unfold infRate
  congr 1
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    exact ⟨n, hnpos, by simp [zeroExtension, Nat.ne_of_gt hnpos]⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, Nat.succ_le_of_lt hn, by simp [zeroExtension, Nat.ne_of_gt hn]⟩

theorem subadditive_full_limit (u : ℕ → ℝ)
    (hsub : ∀ m n : ℕ, 0 < m → 0 < n → u (m + n) ≤ u m + u n)
    {C : ℝ} (hC : 0 ≤ C) (hlower : ∀ n : ℕ, 0 < n → -C * (n : ℝ) ≤ u n) :
    Tendsto (fun n => u n / (n : ℝ)) atTop (𝓝 (infRate u)) := by
  have hsub0 := zeroExtension_subadditive u hsub
  have ht := hsub0.tendsto_lim (zeroExtension_rates_bddBelow u hC hlower)
  rw [zeroExtension_rate_eq u hsub0] at ht
  apply ht.congr
  intro n
  by_cases hn : n = 0 <;> simp [zeroExtension, hn]

theorem infRate_mul_le (u : ℕ → ℝ)
    (hsub : ∀ m n : ℕ, 0 < m → 0 < n → u (m + n) ≤ u m + u n)
    {C : ℝ} (hC : 0 ≤ C) (hlower : ∀ n : ℕ, 0 < n → -C * (n : ℝ) ≤ u n)
    {n : ℕ} (hn : 0 < n) : (n : ℝ) * infRate u ≤ u n := by
  have hsub0 := zeroExtension_subadditive u hsub
  have hb := hsub0.lim_le_div (zeroExtension_rates_bddBelow u hC hlower) hn.ne'
  rw [zeroExtension_rate_eq u hsub0] at hb
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hb' : infRate u ≤ u n / (n : ℝ) := by
    simpa [zeroExtension, Nat.ne_of_gt hn] using hb
  simpa [mul_comm] using (le_div_iff₀ hnR).mp hb'

theorem positive_superadditive_mul (u : ℕ → ℝ)
    (hsuper : ∀ m n : ℕ, 0 < m → 0 < n → u m + u n ≤ u (m + n))
    {m : ℕ} (hm : 0 < m) : ∀ k : ℕ, 0 < k → (k : ℝ) * u m ≤ u (k * m) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · simp [hk0]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    calc
      ((k + 1 : ℕ) : ℝ) * u m = (k : ℝ) * u m + u m := by push_cast; ring
      _ ≤ u (k * m) + u m := by linarith [ih hkpos]
      _ ≤ u (k * m + m) := hsuper _ _ (Nat.mul_pos hkpos hm) hm
      _ = u ((k + 1) * m) := by rw [Nat.succ_mul]

theorem superadditive_repetition_bound (u : ℕ → ℝ)
    (hsuper : ∀ m n : ℕ, 0 < m → 0 < n → u m + u n ≤ u (m + n))
    {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hrepeat : ∀ k : ℕ, 0 < k → u (k * n) ≤ (k : ℝ) * p) :
    (n : ℝ) * supRate u ≤ p := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrate : ∀ m : ℕ, 0 < m → u m / (m : ℝ) ≤ p / (n : ℝ) := by
    intro m hm
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hlo := positive_superadditive_mul u hsuper hm n hn
    have hhi := hrepeat m hm
    have hbound : (n : ℝ) * u m ≤ (m : ℝ) * p :=
      hlo.trans (by simpa [Nat.mul_comm] using hhi)
    apply (div_le_div_iff₀ hmR hnR).mpr
    simpa [mul_comm] using hbound
  have hsup : supRate u ≤ p / (n : ℝ) := by
    unfold supRate
    apply csSup_le (rateSet_nonempty u)
    rintro x ⟨m, hm, rfl⟩
    exact hrate m hm
  simpa [mul_comm] using (le_div_iff₀ hnR).mp hsup

end ScalarRate

end QuantumProver.Equipartition.FiniteModel
