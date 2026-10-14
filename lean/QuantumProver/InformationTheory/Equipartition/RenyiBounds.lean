import Mathlib

noncomputable section

open MeasureTheory
open scoped Matrix

namespace QuantumProver.Equipartition.FiniteModel

def expRemainder (y : ℝ) : ℝ := Real.exp (-y) - 1 + y

theorem expRemainder_nonneg (y : ℝ) : 0 ≤ expRemainder y := by
  have h := Real.add_one_le_exp (-y)
  unfold expRemainder
  linarith

theorem expRemainder_integral (y : ℝ) :
    expRemainder y = ∫ v : ℝ in 0..1, y ^ 2 * (1 - v) * Real.exp (-y * v) := by
  have hd (v : ℝ) : HasDerivAt
      (fun v : ℝ => (1 - y + y * v) * Real.exp (-y * v))
      (y ^ 2 * (1 - v) * Real.exp (-y * v)) v := by
    convert (((hasDerivAt_const v (1 - y)).add
      ((hasDerivAt_id v).const_mul y)).mul
      (((hasDerivAt_id v).const_mul (-y)).exp)) using 1 <;>
      (try funext x) <;> (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply,
        Pi.pow_apply, id_eq]) <;> ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hd v)
    (show IntervalIntegrable
      (fun v : ℝ => y ^ 2 * (1 - v) * Real.exp (-y * v)) volume 0 1 from
      (by fun_prop : Continuous (fun v : ℝ =>
        y ^ 2 * (1 - v) * Real.exp (-y * v))).intervalIntegrable 0 1)
  rw [h]
  simp only [mul_one, mul_zero, add_zero, Real.exp_zero]
  unfold expRemainder
  ring

theorem expRemainder_tangent_integral (y : ℝ) :
    (∫ v : ℝ in 0..1,
      y ^ 2 * (1 - v) *
        (Real.exp (-y / 3) * (1 + y / 3 - y * v))) =
      y ^ 2 / 2 * Real.exp (-y / 3) := by
  have hp (v : ℝ) : HasDerivAt
      (fun v : ℝ => v - v ^ 2 / 2 +
        y * (v / 3 - 2 * v ^ 2 / 3 + v ^ 3 / 3))
      ((1 - v) * (1 + y / 3 - y * v)) v := by
    convert (((hasDerivAt_id v).sub (((hasDerivAt_id v).pow 2).div_const 2)).add
      (((((hasDerivAt_id v).div_const 3).sub
        ((((hasDerivAt_id v).pow 2).const_mul 2).div_const 3)).add
        (((hasDerivAt_id v).pow 3).div_const 3)).const_mul y)) using 1 <;>
      (try funext x) <;> (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply,
        Pi.pow_apply, id_eq]) <;> ring
  have hd (v : ℝ) : HasDerivAt
      (fun v : ℝ => (Real.exp (-y / 3) * y ^ 2) *
        (v - v ^ 2 / 2 + y * (v / 3 - 2 * v ^ 2 / 3 + v ^ 3 / 3)))
      (y ^ 2 * (1 - v) *
        (Real.exp (-y / 3) * (1 + y / 3 - y * v))) v := by
    convert (hp v).const_mul (Real.exp (-y / 3) * y ^ 2) using 1 <;>
      (try funext x) <;> (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply,
        Pi.pow_apply, id_eq]) <;> ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hd v)
    (show IntervalIntegrable
      (fun v : ℝ => y ^ 2 * (1 - v) *
        (Real.exp (-y / 3) * (1 + y / 3 - y * v))) volume 0 1 from
      (by fun_prop : Continuous (fun v : ℝ => y ^ 2 * (1 - v) *
        (Real.exp (-y / 3) * (1 + y / 3 - y * v)))).intervalIntegrable 0 1)
  rw [h]
  ring

theorem expRemainder_sharp_lower (y : ℝ) :
    y ^ 2 / 2 * Real.exp (-y / 3) ≤ expRemainder y := by
  rw [expRemainder_integral, ← expRemainder_tangent_integral]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((by fun_prop : Continuous (fun v : ℝ => y ^ 2 * (1 - v) *
      (Real.exp (-y / 3) * (1 + y / 3 - y * v)))).intervalIntegrable 0 1)
    ((by fun_prop : Continuous (fun v : ℝ =>
      y ^ 2 * (1 - v) * Real.exp (-y * v))).intervalIntegrable 0 1)
  intro v hv
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg y) (by linarith [hv.2]))
  have ht := mul_le_mul_of_nonneg_left
    (Real.add_one_le_exp (y / 3 - y * v)) (Real.exp_pos (-y / 3)).le
  rw [← Real.exp_add] at ht
  convert ht using 1 <;> congr 1 <;> ring

theorem expRemainder_majorant_integral (y : ℝ) :
    (∫ v : ℝ in 0..1, y ^ 2 * (1 - v) * Real.exp |y|) =
      y ^ 2 / 2 * Real.exp |y| := by
  have hd (v : ℝ) : HasDerivAt
      (fun v : ℝ => (y ^ 2 * Real.exp |y|) * (v - v ^ 2 / 2))
      (y ^ 2 * (1 - v) * Real.exp |y|) v := by
    convert ((hasDerivAt_id v).sub
      (((hasDerivAt_id v).pow 2).div_const 2)).const_mul
      (y ^ 2 * Real.exp |y|) using 1 <;>
      (try funext x) <;> (try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply,
        Pi.pow_apply, id_eq]) <;> ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hd v)
    (show IntervalIntegrable
      (fun v : ℝ => y ^ 2 * (1 - v) * Real.exp |y|) volume 0 1 from
      (by fun_prop : Continuous
        (fun v : ℝ => y ^ 2 * (1 - v) * Real.exp |y|)).intervalIntegrable 0 1)
  rw [h]
  ring

theorem expRemainder_upper (y : ℝ) :
    expRemainder y ≤ y ^ 2 / 2 * Real.exp |y| := by
  rw [expRemainder_integral, ← expRemainder_majorant_integral]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((by fun_prop : Continuous (fun v : ℝ =>
      y ^ 2 * (1 - v) * Real.exp (-y * v))).intervalIntegrable 0 1)
    ((by fun_prop : Continuous (fun v : ℝ =>
      y ^ 2 * (1 - v) * Real.exp |y|)).intervalIntegrable 0 1)
  intro v hv
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg y) (by linarith [hv.2]))
  apply Real.exp_le_exp.mpr
  calc
    -y * v ≤ |y| * v := mul_le_mul_of_nonneg_right (neg_le_abs y) hv.1
    _ ≤ |y| := by nlinarith [abs_nonneg y, hv.2]

theorem exp_taylor_upper (y : ℝ) :
    Real.exp y ≤ 1 + y + y ^ 2 / 2 * Real.exp |y| := by
  have h := expRemainder_upper (-y)
  simp only [expRemainder, neg_neg, neg_sq, abs_neg] at h
  linarith

theorem exp_sub_one_small {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.exp a - 1 ≤ a * (1 + 2 * a) := by
  have h := exp_taylor_upper a
  rw [abs_of_nonneg ha] at h
  have he : Real.exp a ≤ 3 :=
    (Real.exp_le_exp.mpr ha1).trans Real.exp_one_lt_three.le
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg a)
  nlinarith

section MatrixOperator

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem operator_trace_mul_nonneg {A B : Matrix κ κ ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  have hs : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).1
  have hpos : (CFC.sqrt A * B * CFC.sqrt A).PosSemidef := by
    simpa only [hs] using hB.mul_mul_conjTranspose_same (CFC.sqrt A)
  have htrace : (CFC.sqrt A * B * CFC.sqrt A).trace = (A * B).trace := by
    rw [Matrix.trace_mul_cycle, ← pow_two, CFC.sq_sqrt A hA.nonneg]
  exact (Complex.nonneg_iff.mp (htrace ▸ hpos.trace_nonneg)).1

theorem inverse_half_power_antitone {A B : Matrix κ κ ℂ}
    (hA : A.PosDef) (hAB : (B - A).PosSemidef) :
    (cfc (fun x : ℝ => Real.rpow x (-1 / 2 : ℝ)) A -
      cfc (fun x : ℝ => Real.rpow x (-1 / 2 : ℝ)) B).PosSemidef := by
  have hab : A ≤ B := sub_nonneg.mp hAB.nonneg
  have ha := hA.isStrictlyPositive
  have hb := ha.of_le hab
  have hi : CFC.rpow B (-1 : ℝ) ≤ CFC.rpow A (-1 : ℝ) :=
    CStarAlgebra.rpow_neg_one_le_rpow_neg_one hab ha
  have hh := CFC.rpow_le_rpow
    (show (1 / 2 : ℝ) ∈ Set.Icc 0 1 by norm_num) hi
  simp only [CFC.rpow_eq_pow] at hh
  rw [CFC.rpow_rpow B (-1) (1 / 2) (by norm_num) hb,
    CFC.rpow_rpow A (-1) (1 / 2) (by norm_num) ha] at hh
  norm_num only [neg_mul, one_mul] at hh
  rw [CFC.rpow_eq_cfc_real ha.nonneg, CFC.rpow_eq_cfc_real hb.nonneg] at hh
  rw [show -(1 / 2 : ℝ) = (-1 / 2 : ℝ) by norm_num] at hh
  exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hh)

theorem operator_log_order {A B : Matrix κ κ ℂ}
    (hA : A.PosDef) (hAB : (B - A).PosSemidef) :
    (cfc Real.log B - cfc Real.log A).PosSemidef := by
  have hab : A ≤ B := sub_nonneg.mp hAB.nonneg
  have h := CFC.log_le_log hab hA.isStrictlyPositive
  simpa only [CFC.log] using Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)

theorem trace_entropy_upper_of_faithful_domination {ρ σ : Matrix κ κ ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (htrace : Matrix.trace ρ = 1)
    {a : ℝ} (ha : 0 < a) (hdom : (a • σ - ρ).PosSemidef) :
    (Matrix.trace (ρ * (cfc Real.log ρ - cfc Real.log σ))).re ≤ Real.log a := by
  have hlog : cfc Real.log (a • σ) =
      Real.log a • (1 : Matrix κ κ ℂ) + cfc Real.log σ := by
    simpa only [CFC.log, Algebra.algebraMap_eq_smul_one] using
      CFC.log_smul' σ ha hσ.isStrictlyPositive
  have hp := operator_trace_mul_nonneg hρ.posSemidef
    (operator_log_order hρ hdom)
  rw [hlog] at hp
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, Complex.sub_re,
    Complex.add_re, Complex.smul_re, htrace, Complex.one_re, smul_eq_mul, mul_one] at hp
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith

theorem operator_negative_rpow_antitone {A B : Matrix κ κ ℂ}
    (hA : A.PosDef) (hAB : (B - A).PosSemidef) {p : ℝ}
    (hp₁ : -1 ≤ p) (hp₀ : p ≤ 0) :
    (CFC.rpow A p - CFC.rpow B p).PosSemidef := by
  have hab : A ≤ B := sub_nonneg.mp hAB.nonneg
  have ha := hA.isStrictlyPositive
  have hb := ha.of_le hab
  have hi : CFC.rpow B (-1 : ℝ) ≤ CFC.rpow A (-1 : ℝ) :=
    CStarAlgebra.rpow_neg_one_le_rpow_neg_one hab ha
  have hh := CFC.rpow_le_rpow
    (show -p ∈ Set.Icc (0 : ℝ) 1 by constructor <;> linarith) hi
  simp only [CFC.rpow_eq_pow] at hh
  rw [CFC.rpow_rpow B (-1) (-p) (by norm_num) hb,
    CFC.rpow_rpow A (-1) (-p) (by norm_num) ha] at hh
  simp only [neg_mul, one_mul, neg_neg] at hh
  exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hh)

theorem matrix_mul_rpow_predecessor {A : Matrix κ κ ℂ}
    (hA : A.PosDef) (α : ℝ) :
    A * CFC.rpow A (α - 1) = CFC.rpow A α := by
  have ha := hA.isStrictlyPositive
  calc
    A * CFC.rpow A (α - 1) =
        CFC.rpow A (1 : ℝ) * CFC.rpow A (α - 1) := by
      simp only [CFC.rpow_eq_pow, CFC.rpow_one A ha.nonneg]
    _ = CFC.rpow A (1 + (α - 1)) := by
      simpa only [CFC.rpow_eq_pow] using
        (CFC.rpow_add (x := (1 : ℝ)) (y := α - 1) ha.isUnit).symm
    _ = CFC.rpow A α := by congr 1; ring

theorem trace_rpow_subadd_faithful {A B : Matrix κ κ ℂ}
    (hA : A.PosDef) (hB : B.PosDef) {α : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) :
    (CFC.rpow (A + B) α).trace.re ≤
      (CFC.rpow A α).trace.re + (CFC.rpow B α).trace.re := by
  have hT : (A + B).PosDef := hA.add hB
  have hAT : (A + B - A).PosSemidef := by
    simpa only [add_sub_cancel_left] using hB.posSemidef
  have hBT : (A + B - B).PosSemidef := by
    simpa only [add_sub_cancel_right] using hA.posSemidef
  have hp₁ : -1 ≤ α - 1 := by linarith
  have hp₀ : α - 1 ≤ 0 := by linarith
  have hpa := operator_trace_mul_nonneg hA.posSemidef
    (operator_negative_rpow_antitone hA hAT hp₁ hp₀)
  have hpb := operator_trace_mul_nonneg hB.posSemidef
    (operator_negative_rpow_antitone hB hBT hp₁ hp₀)
  rw [Matrix.mul_sub, matrix_mul_rpow_predecessor hA,
    Matrix.trace_sub, Complex.sub_re] at hpa
  rw [Matrix.mul_sub, matrix_mul_rpow_predecessor hB,
    Matrix.trace_sub, Complex.sub_re] at hpb
  have ht : (CFC.rpow (A + B) α).trace.re =
      (A * CFC.rpow (A + B) (α - 1)).trace.re +
        (B * CFC.rpow (A + B) (α - 1)).trace.re := by
    rw [← matrix_mul_rpow_predecessor hT α, Matrix.add_mul,
      Matrix.trace_add, Complex.add_re]
  linarith

end MatrixOperator

section MatrixFourierPinching

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem orthogonal_projection_phase_unitary {κ : Type*} [Fintype κ]
    [DecidableEq κ] (P : κ → Matrix ι ι ℂ) (c : κ → ℂ)
    (hP : ∀ i, (P i)ᴴ = P i)
    (hmul : ∀ i j, P i * P j = if i = j then P i else 0)
    (hsum : ∑ i, P i = 1) (hc : ∀ i, c i * star (c i) = 1) :
    (∑ i, c i • P i) ∈ Matrix.unitaryGroup ι ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose]
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hP]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hmul, smul_ite, smul_zero]
  have hc' (i : κ) : star (c i) * c i = 1 := (mul_comm _ _).trans (hc i)
  simpa only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, hc', hc, one_smul] using hsum

variable {N : ℕ} [NeZero N]

theorem fourier_character_star (x : ZMod N) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply, ← Circle.coe_inv]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle x)).symm

theorem fourier_character_mul_star (x : ZMod N) :
    ZMod.stdAddChar x * star (ZMod.stdAddChar x) = 1 := by
  rw [fourier_character_star, ← AddChar.map_add_eq_mul,
    add_neg_cancel, AddChar.map_zero_eq_one]

theorem fourier_character_sum (i j : ZMod N) :
    (∑ k : ZMod N, ZMod.stdAddChar (k * (i - j))) =
      if i = j then (N : ℂ) else 0 := by
  simpa [ZMod.card, sub_eq_zero] using
    (AddChar.sum_mulShift (i - j) (ZMod.isPrimitive_stdAddChar N))

def fourierProjectionMatrix (P : ZMod N → Matrix ι ι ℂ) (k : ZMod N) :
    Matrix ι ι ℂ := ∑ i, ZMod.stdAddChar (k * i) • P i

def fourierProjectionUnitary (P : ZMod N → Matrix ι ι ℂ)
    (hP : ∀ i, (P i)ᴴ = P i)
    (hmul : ∀ i j, P i * P j = if i = j then P i else 0)
    (hsum : ∑ i, P i = 1) (k : ZMod N) : Matrix.unitaryGroup ι ℂ :=
  ⟨fourierProjectionMatrix P k,
    orthogonal_projection_phase_unitary P
      (fun i => ZMod.stdAddChar (k * i)) hP hmul hsum
      (fun i => fourier_character_mul_star (k * i))⟩

theorem fourierProjectionMatrix_conjugate (P : ZMod N → Matrix ι ι ℂ)
    (hP : ∀ i, (P i)ᴴ = P i) (A : Matrix ι ι ℂ) (k : ZMod N) :
    fourierProjectionMatrix P k * A * (fourierProjectionMatrix P k)ᴴ =
      ∑ i, ∑ j, ZMod.stdAddChar (k * (i - j)) • (P i * A * P j) := by
  unfold fourierProjectionMatrix
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hP,
    fourier_character_star]
  rw [Finset.sum_mul, Finset.sum_mul]
  simp only [Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← AddChar.map_add_eq_mul]
  congr 2
  ring

theorem fourierProjectionMatrix_sum (P : ZMod N → Matrix ι ι ℂ)
    (hP : ∀ i, (P i)ᴴ = P i) (A : Matrix ι ι ℂ) :
    (∑ k : ZMod N,
      fourierProjectionMatrix P k * A * (fourierProjectionMatrix P k)ᴴ) =
      (N : ℂ) • ∑ i, P i * A * P i := by
  simp_rw [fourierProjectionMatrix_conjugate P hP A]
  calc
    (∑ k : ZMod N, ∑ i, ∑ j,
      ZMod.stdAddChar (k * (i - j)) • (P i * A * P j)) =
        ∑ i, ∑ j, (∑ k : ZMod N, ZMod.stdAddChar (k * (i - j))) •
          (P i * A * P j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_smul.symm
    _ = _ := by
      simp only [fourier_character_sum, ite_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.smul_sum]

theorem fourier_pinching_average (P : ZMod N → Matrix ι ι ℂ)
    (hP : ∀ i, (P i)ᴴ = P i)
    (hmul : ∀ i j, P i * P j = if i = j then P i else 0)
    (hsum : ∑ i, P i = 1) (A : Matrix ι ι ℂ) :
    (∑ i, P i * A * P i) = (N : ℝ)⁻¹ •
      ∑ k : ZMod N, Unitary.conjStarAlgAut ℝ (Matrix ι ι ℂ)
        (fourierProjectionUnitary P hP hmul hsum k) A := by
  have hs := fourierProjectionMatrix_sum P hP A
  change (∑ i, P i * A * P i) = (N : ℝ)⁻¹ •
    ∑ k : ZMod N,
      fourierProjectionMatrix P k * A * (fourierProjectionMatrix P k)ᴴ
  rw [hs]
  have hreal (B : Matrix ι ι ℂ) : (N : ℂ) • B = (N : ℝ) • B := by
    ext i j
    simp
  rw [hreal, smul_smul, inv_mul_cancel₀ (by exact_mod_cast NeZero.ne N), one_smul]

end MatrixFourierPinching

section FiniteFourierPinching

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finite_pinching_unitary_average {κ : Type*} [Fintype κ] [Nonempty κ]
    [DecidableEq κ] (P : κ → Matrix ι ι ℂ)
    (hP : ∀ i, (P i)ᴴ = P i)
    (hmul : ∀ i j, P i * P j = if i = j then P i else 0)
    (hsum : ∑ i, P i = 1) (A : Matrix ι ι ℂ) :
    ∃ U : κ → Matrix.unitaryGroup ι ℂ,
      (∑ i, P i * A * P i) = (Fintype.card κ : ℝ)⁻¹ •
        ∑ k, Unitary.conjStarAlgAut ℝ (Matrix ι ι ℂ) (U k) A := by
  classical
  let v := Fintype.card κ
  letI : NeZero v := ⟨Fintype.card_ne_zero⟩
  let e : κ ≃ ZMod v := Fintype.equivOfCardEq (by simp [v, ZMod.card])
  let Q : ZMod v → Matrix ι ι ℂ := fun i => P (e.symm i)
  have hQ (i : ZMod v) : (Q i)ᴴ = Q i := hP (e.symm i)
  have hQmul (i j : ZMod v) : Q i * Q j = if i = j then Q i else 0 := by
    simpa only [Q, e.symm.injective.eq_iff] using hmul (e.symm i) (e.symm j)
  have hQsum : ∑ i, Q i = 1 := (e.symm.sum_comp P).trans hsum
  let V : ZMod v → Matrix.unitaryGroup ι ℂ :=
    fourierProjectionUnitary Q hQ hQmul hQsum
  refine ⟨fun k => V (e k), ?_⟩
  have hp : (∑ i : ZMod v, Q i * A * Q i) = ∑ i : κ, P i * A * P i :=
    e.symm.sum_comp (fun i => P i * A * P i)
  have hu : (∑ k : κ, Unitary.conjStarAlgAut ℝ (Matrix ι ι ℂ) (V (e k)) A) =
      ∑ k : ZMod v, Unitary.conjStarAlgAut ℝ (Matrix ι ι ℂ) (V k) A :=
    e.sum_comp (fun k => Unitary.conjStarAlgAut ℝ (Matrix ι ι ℂ) (V k) A)
  exact hp.symm.trans ((fourier_pinching_average Q hQ hQmul hQsum A).trans
    (congrArg (fun X : Matrix ι ι ℂ => (v : ℝ)⁻¹ • X) hu.symm))

end FiniteFourierPinching

end QuantumProver.Equipartition.FiniteModel
