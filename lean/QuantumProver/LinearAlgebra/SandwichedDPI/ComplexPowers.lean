import Mathlib

set_option autoImplicit false
noncomputable section

open Matrix Complex Filter Set
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix
  Matrix.Norms.L2Operator Topology

namespace QuantumProver.SandwichedDPI

def scalarComplexPower (x : ℝ) (z : ℂ) : ℂ :=
  if x = 0 then 0 else Complex.exp (z * (Real.log x : ℂ))

theorem scalarComplexPower_add (x : ℝ) (z w : ℂ) :
    scalarComplexPower x (z + w) = scalarComplexPower x z * scalarComplexPower x w := by
  by_cases hx : x = 0
  · simp [scalarComplexPower, hx]
  · simp only [scalarComplexPower, ite_eq_right hx]
    rw [← Complex.exp_add]
    congr 1
    ring

theorem scalarComplexPower_conj (x : ℝ) (z : ℂ) :
    conj (scalarComplexPower x z) = scalarComplexPower x (conj z) := by
  by_cases hx : x = 0
  · simp [scalarComplexPower, hx]
  · simp only [scalarComplexPower, ite_eq_right hx]
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal]

theorem differentiable_scalarComplexPower (x : ℝ) :
    Differentiable ℂ (scalarComplexPower x) := by
  change Differentiable ℂ (fun z : ℂ =>
    if x = 0 then 0 else Complex.exp (z * (Real.log x : ℂ)))
  by_cases hx : x = 0
  · simp only [ite_eq_left hx]
    exact differentiable_const (0 : ℂ)
  · simp only [ite_eq_right hx]
    exact (Complex.differentiable_exp : Differentiable ℂ Complex.exp).comp
      (differentiable_id.mul_const (Real.log x : ℂ))

theorem scalarComplexPower_ofReal_of_pos {x : ℝ} (hx : 0 < x) (r : ℝ) :
    scalarComplexPower x (r : ℂ) = (x ^ r : ℝ) := by
  rw [scalarComplexPower, ite_eq_right (ne_of_gt hx), Real.rpow_def_of_pos hx,
    Complex.ofReal_exp, Complex.ofReal_mul]
  congr 1
  ring

theorem scalarComplexPower_ofReal {x r : ℝ} (hx : 0 ≤ x) (hr : r ≠ 0) :
    scalarComplexPower x (r : ℂ) = (x ^ r : ℝ) := by
  by_cases hx0 : x = 0
  · simp [scalarComplexPower, hx0, Real.zero_rpow hr]
  · exact scalarComplexPower_ofReal_of_pos (lt_of_le_of_ne hx (Ne.symm hx0)) r

theorem norm_scalarComplexPower_of_ne_zero {x : ℝ} (hx : x ≠ 0) (z : ℂ) :
    ‖scalarComplexPower x z‖ = Real.exp (z.re * Real.log x) := by
  simp [scalarComplexPower, hx, Complex.norm_exp, Complex.mul_re]

theorem norm_scalarComplexPower_imaginary_le_one (x t : ℝ) :
    ‖scalarComplexPower x (Complex.I * (t : ℂ))‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [scalarComplexPower, hx]
  · rw [norm_scalarComplexPower_of_ne_zero hx]
    simp

theorem norm_scalarComplexPower_le {x R : ℝ} {z : ℂ} (hz : |z.re| ≤ R) :
    ‖scalarComplexPower x z‖ ≤ Real.exp (R * |Real.log x|) := by
  by_cases hx : x = 0
  · simp only [scalarComplexPower, ite_eq_left hx, norm_zero]
    exact (Real.exp_pos _).le
  · rw [norm_scalarComplexPower_of_ne_zero hx]
    apply Real.exp_le_exp.mpr
    calc
      z.re * Real.log x ≤ |z.re * Real.log x| := le_abs_self _
      _ = |z.re| * |Real.log x| := abs_mul _ _
      _ ≤ R * |Real.log x| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : Matrix I I ℂ}

def complexPower (hA : A.PosSemidef) (z : ℂ) : Matrix I I ℂ :=
  Unitary.conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
    (Matrix.diagonal (fun i => scalarComplexPower (hA.1.eigenvalues i) z))

theorem complexPower_spectral (hA : A.PosSemidef) (z : ℂ) :
    complexPower hA z = (hA.1.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (fun i => scalarComplexPower (hA.1.eigenvalues i) z) *
      (hA.1.eigenvectorUnitary : Matrix I I ℂ)ᴴ := by
  simp only [complexPower, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]

theorem complexPower_apply (hA : A.PosSemidef) (z : ℂ) (i j : I) :
    complexPower hA z i j = ∑ k,
      hA.1.eigenvectorUnitary i k * scalarComplexPower (hA.1.eigenvalues k) z *
        star (hA.1.eigenvectorUnitary j k) := by
  rw [complexPower_spectral]
  change (∑ k, ((hA.1.eigenvectorUnitary : Matrix I I ℂ) *
    Matrix.diagonal (fun l => scalarComplexPower (hA.1.eigenvalues l) z)) i k *
      star (hA.1.eigenvectorUnitary j k)) = _
  simp only [Matrix.mul_diagonal]

theorem complexPower_add (hA : A.PosSemidef) (z w : ℂ) :
    complexPower hA (z + w) = complexPower hA z * complexPower hA w := by
  unfold complexPower
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  congr 1
  funext i
  exact scalarComplexPower_add _ z w

theorem complexPower_conjTranspose (hA : A.PosSemidef) (z : ℂ) :
    (complexPower hA z)ᴴ = complexPower hA (conj z) := by
  change star (complexPower hA z) = complexPower hA (conj z)
  unfold complexPower
  rw [← map_star, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  congr 1
  funext i
  exact scalarComplexPower_conj _ z

theorem complexPower_mul_comm (hA : A.PosSemidef) (z w : ℂ) :
    complexPower hA z * complexPower hA w = complexPower hA w * complexPower hA z := by
  rw [← complexPower_add, ← complexPower_add, add_comm]

theorem complexPower_real (hA : A.PosSemidef) {r : ℝ} (hr : r ≠ 0) :
    complexPower hA (r : ℂ) = CFC.rpow A r := by
  have hp : CFC.rpow A r = cfc (fun x : ℝ => x ^ r) A :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := A) (y := r) hA.nonneg
  rw [hp, hA.1.cfc_eq]
  unfold complexPower Matrix.IsHermitian.cfc
  congr 1
  congr 1
  funext i
  exact scalarComplexPower_ofReal (hA.eigenvalues_nonneg i) hr

theorem complexPower_real_of_posDef (hA : A.PosSemidef) (hpos : A.PosDef) (r : ℝ) :
    complexPower hA (r : ℂ) = CFC.rpow A r := by
  have hp : CFC.rpow A r = cfc (fun x : ℝ => x ^ r) A :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := A) (y := r) hA.nonneg
  rw [hp, hA.1.cfc_eq]
  unfold complexPower Matrix.IsHermitian.cfc
  congr 1
  congr 1
  funext i
  exact scalarComplexPower_ofReal_of_pos (hpos.eigenvalues_pos i) r

@[simp] theorem complexPower_one (hA : A.PosSemidef) : complexPower hA 1 = A := by
  calc
    complexPower hA 1 = CFC.rpow A 1 := complexPower_real hA one_ne_zero
    _ = A := CFC.rpow_one (A := Matrix I I ℂ) A hA.nonneg

theorem complexPower_zero_eq_support (hA : A.PosSemidef) :
    complexPower hA 0 = cfc (fun x : ℝ => if x = 0 then 0 else 1) A := by
  rw [hA.1.cfc_eq]
  unfold complexPower Matrix.IsHermitian.cfc
  congr 1
  congr 1
  funext i
  by_cases hx : hA.1.eigenvalues i = 0 <;> simp [scalarComplexPower, hx]

theorem complexPower_zero_idempotent (hA : A.PosSemidef) :
    complexPower hA 0 * complexPower hA 0 = complexPower hA 0 := by
  simpa using (complexPower_add hA 0 0).symm

theorem complexPower_zero_mul (hA : A.PosSemidef) (z : ℂ) :
    complexPower hA 0 * complexPower hA z = complexPower hA z := by
  simpa using (complexPower_add hA 0 z).symm

@[simp] theorem complexPower_zero_of_posDef (hA : A.PosSemidef) (hpos : A.PosDef) :
    complexPower hA 0 = 1 := by
  calc
    complexPower hA 0 = CFC.rpow A 0 := complexPower_real_of_posDef hA hpos 0
    _ = 1 := CFC.rpow_zero (A := Matrix I I ℂ) A hA.nonneg

theorem differentiable_complexPower (hA : A.PosSemidef) :
    Differentiable ℂ (complexPower hA) := by
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  simp_rw [complexPower_apply]
  apply Differentiable.fun_sum
  intro k hk
  exact ((differentiable_const (hA.1.eigenvectorUnitary i k)).mul
    (differentiable_scalarComplexPower (hA.1.eigenvalues k))).mul_const
      (star (hA.1.eigenvectorUnitary j k))

theorem analyticAt_complexPower (hA : A.PosSemidef) (z : ℂ) :
    AnalyticAt ℂ (complexPower hA) z := (differentiable_complexPower hA).analyticAt z

theorem continuous_complexPower (hA : A.PosSemidef) : Continuous (complexPower hA) :=
  (differentiable_complexPower hA).continuous

theorem norm_complexPower_eq_pi_norm (hA : A.PosSemidef) (z : ℂ) :
    ‖complexPower hA z‖ = ‖fun i => scalarComplexPower (hA.1.eigenvalues i) z‖ := by
  simp only [complexPower, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]

theorem norm_complexPower_imaginary_le_one (hA : A.PosSemidef) (t : ℝ) :
    ‖complexPower hA (Complex.I * (t : ℂ))‖ ≤ 1 := by
  rw [norm_complexPower_eq_pi_norm]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i =>
    norm_scalarComplexPower_imaginary_le_one _ t

theorem complexPower_imaginary_mem_unitary (hA : A.PosSemidef)
    (hpos : A.PosDef) (t : ℝ) :
    complexPower hA (Complex.I * (t : ℂ)) ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    complexPower_conjTranspose, ← complexPower_add]
  have hzero : Complex.I * (t : ℂ) + conj (Complex.I * (t : ℂ)) = 0 := by simp
  rw [hzero, complexPower_zero_of_posDef hA hpos]

theorem abs_complexPower_of_re_pos (hA : A.PosSemidef) {z : ℂ} (hz : 0 < z.re) :
    CFC.abs (complexPower hA z) = CFC.rpow A z.re := by
  have hreal : complexPower hA (z.re : ℂ) = CFC.rpow A z.re :=
    complexPower_real hA (ne_of_gt hz)
  have hsum : (z.re : ℂ) + (z.re : ℂ) = conj z + z := by
    apply Complex.ext <;> simp
  have hprod : CFC.rpow A z.re * CFC.rpow A z.re =
      (complexPower hA z)ᴴ * complexPower hA z := by
    rw [← hreal, ← complexPower_add, hsum, complexPower_add,
      ← complexPower_conjTranspose]
  change CFC.sqrt ((complexPower hA z)ᴴ * complexPower hA z) = CFC.rpow A z.re
  exact CFC.sqrt_unique hprod (CFC.rpow_nonneg : 0 ≤ CFC.rpow A z.re)

def complexPowerStripBound (hA : A.PosSemidef) (R : ℝ) : ℝ :=
  ∑ i, Real.exp (R * |Real.log (hA.1.eigenvalues i)|)

theorem complexPowerStripBound_nonnegative (hA : A.PosSemidef) (R : ℝ) :
    0 ≤ complexPowerStripBound hA R := by
  exact Finset.sum_nonneg fun i _ => (Real.exp_pos _).le

theorem norm_complexPower_le_stripBound (hA : A.PosSemidef) {R : ℝ} {z : ℂ}
    (hz : |z.re| ≤ R) : ‖complexPower hA z‖ ≤ complexPowerStripBound hA R := by
  rw [norm_complexPower_eq_pi_norm]
  apply (pi_norm_le_iff_of_nonneg (complexPowerStripBound_nonnegative hA R)).mpr
  intro i
  change ‖scalarComplexPower (hA.1.eigenvalues i) z‖ ≤
    ∑ j, Real.exp (R * |Real.log (hA.1.eigenvalues j)|)
  apply (norm_scalarComplexPower_le (x := hA.1.eigenvalues i) hz).trans
  exact Finset.single_le_sum
    (f := fun j : I => Real.exp (R * |Real.log (hA.1.eigenvalues j)|))
    (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

theorem complexPower_bounded_on_verticalStrip (hA : A.PosSemidef) (a b : ℝ) :
    ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ‖complexPower hA z‖ ≤ C := by
  refine ⟨complexPowerStripBound hA (max |a| |b|), fun z hz => ?_⟩
  apply norm_complexPower_le_stripBound hA
  apply abs_le.mpr
  constructor
  · have hleft : -max |a| |b| ≤ a :=
      (neg_le_neg (le_max_left |a| |b|)).trans (neg_abs_le a)
    exact hleft.trans hz.1
  · exact hz.2.trans ((le_abs_self b).trans (le_max_right |a| |b|))

end QuantumProver.SandwichedDPI
