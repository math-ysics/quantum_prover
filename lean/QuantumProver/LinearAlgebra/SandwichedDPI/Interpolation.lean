import Mathlib
import QuantumProver.LinearAlgebra.SandwichedDPI.OperatorNorm
import QuantumProver.LinearAlgebra.SandwichedDPI.Support
import QuantumProver.LinearAlgebra.SandwichedDPI.ComplexPowers
import QuantumProver.LinearAlgebra.SandwichedDPI.TraceNorm
import QuantumProver.LinearAlgebra.SandwichedDPI.EndpointBounds
import QuantumProver.LinearAlgebra.SandwichedDPI.RpowSupport
import QuantumProver.LinearAlgebra.SandwichedDPI.QBridge

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QuantumProver.SandwichedDPI

open QuantumProver.SuperchannelDiscrimination
open KrausCompletion

variable {I : Type*} [Fintype I] [DecidableEq I]

def schattenPower (p : ℝ) (X : Matrix I I ℂ) : ℝ :=
  (CFC.rpow (CFC.abs X) p).trace.re

def schattenNorm (p : ℝ) (X : Matrix I I ℂ) : ℝ :=
  schattenPower p X ^ (1 / p : ℝ)

theorem schattenPower_nonneg (p : ℝ) (X : Matrix I I ℂ) :
    0 ≤ schattenPower p X :=
  (Complex.nonneg_iff.mp
    (CFC.rpow_nonneg : 0 ≤ CFC.rpow (CFC.abs X) p).posSemidef.trace_nonneg).1

theorem schattenNorm_nonneg (p : ℝ) (X : Matrix I I ℂ) :
    0 ≤ schattenNorm p X := Real.rpow_nonneg (schattenPower_nonneg p X) _

theorem schattenPower_eq_gram_trace (p : ℝ) (hp : 0 ≤ p) (X : Matrix I I ℂ) :
    schattenPower p X = (CFC.rpow (Xᴴ * X) (p / 2)).trace.re := by
  unfold schattenPower CFC.abs
  rw [Matrix.star_eq_conjTranspose]
  have hsqrt : CFC.sqrt (Xᴴ * X) = CFC.rpow (Xᴴ * X) (1 / 2 : ℝ) :=
    CFC.sqrt_eq_rpow
  rw [hsqrt]
  have hpow : CFC.rpow (CFC.rpow (Xᴴ * X) (1 / 2 : ℝ)) p =
      CFC.rpow (Xᴴ * X) ((1 / 2 : ℝ) * p) :=
    CFC.rpow_rpow_of_exponent_nonneg (Xᴴ * X) (1 / 2 : ℝ) p
      (by norm_num) hp (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
  have he : (1 / 2 : ℝ) * p = p / 2 := by ring
  rw [hpow, he]

theorem schattenNorm_rpow (p : ℝ) (hp : p ≠ 0) (X : Matrix I I ℂ) :
    schattenNorm p X ^ p = schattenPower p X := by
  unfold schattenNorm
  rw [one_div]
  exact Real.rpow_inv_rpow (schattenPower_nonneg p X) hp

theorem schattenPower_of_posSemidef (p : ℝ) {A : Matrix I I ℂ}
    (hA : A.PosSemidef) : schattenPower p A = (CFC.rpow A p).trace.re := by
  unfold schattenPower
  rw [CFC.abs_of_nonneg A hA.nonneg]

theorem schattenPower_one (X : Matrix I I ℂ) :
    schattenPower 1 X = (CFC.abs X).trace.re := by
  unfold schattenPower
  have h : CFC.rpow (CFC.abs X) (1 : ℝ) = CFC.abs X :=
    CFC.rpow_one (CFC.abs X) (CFC.abs_nonneg X)
  rw [h]

theorem schattenNorm_one (X : Matrix I I ℂ) :
    schattenNorm 1 X = (CFC.abs X).trace.re := by
  simp only [schattenNorm, one_div_one, Real.rpow_one, schattenPower_one]

theorem trace_rpow_re_eq_zero_iff {A : Matrix I I ℂ} (hA : A.PosSemidef)
    {p : ℝ} (hp : 0 < p) : (CFC.rpow A p).trace.re = 0 ↔ A = 0 := by
  have hreal : CFC.rpow A p = cfc (fun x : ℝ => x ^ p) A :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := A) (y := p) hA.nonneg
  rw [hreal, Klein.trace_cfc_eq_sum _ hA.1]
  constructor
  · intro h
    apply hA.1.eigenvalues_eq_zero_iff.mp
    ext i
    have hi : hA.1.eigenvalues i ^ p = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => Real.rpow_nonneg (hA.eigenvalues_nonneg j) p)).mp h i
        (Finset.mem_univ i)
    exact (Real.rpow_eq_zero_iff_of_nonneg (hA.eigenvalues_nonneg i)).mp hi |>.1
  · intro h
    have he : hA.1.eigenvalues = 0 := hA.1.eigenvalues_eq_zero_iff.mpr h
    simp only [he, Pi.zero_apply, Real.zero_rpow hp.ne', Finset.sum_const_zero]

theorem schattenPower_eq_zero_iff {p : ℝ} (hp : 0 < p) (X : Matrix I I ℂ) :
    schattenPower p X = 0 ↔ X = 0 := by
  rw [schattenPower, trace_rpow_re_eq_zero_iff (CFC.abs_nonneg X).posSemidef hp,
    CFC.abs_eq_zero_iff]

theorem schattenNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (X : Matrix I I ℂ) :
    schattenNorm p X = 0 ↔ X = 0 := by
  rw [schattenNorm, Real.rpow_eq_zero_iff_of_nonneg (schattenPower_nonneg p X)]
  have hinv : (1 / p : ℝ) ≠ 0 := one_div_ne_zero hp.ne'
  rw [schattenPower_eq_zero_iff hp]
  exact and_iff_left hinv

theorem schattenPower_pos_iff {p : ℝ} (hp : 0 < p) (X : Matrix I I ℂ) :
    0 < schattenPower p X ↔ X ≠ 0 := by
  constructor
  · intro h hz
    have hzero : schattenPower p X = 0 := (schattenPower_eq_zero_iff hp X).mpr hz
    linarith
  · intro h
    have hneq : schattenPower p X ≠ 0 :=
      fun hz => h ((schattenPower_eq_zero_iff hp X).mp hz)
    exact lt_of_le_of_ne (schattenPower_nonneg p X) hneq.symm

private theorem rpow_mul_rpow_pos_exponents {A : Matrix I I ℂ}
    (hA : A.PosSemidef) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    CFC.rpow A x * CFC.rpow A y = CFC.rpow A (x + y) := by
  have hxC : CFC.rpow A x = cfc (fun t : ℝ => t ^ x) A :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := A) (y := x) hA.nonneg
  have hyC : CFC.rpow A y = cfc (fun t : ℝ => t ^ y) A :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := A) (y := y) hA.nonneg
  have hxyC : CFC.rpow A (x + y) = cfc (fun t : ℝ => t ^ (x + y)) A :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := A) (y := x + y) hA.nonneg
  rw [hxC, hyC, hxyC, ← cfc_mul (p := IsSelfAdjoint) _ _ A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro t ht
  have ht0 : 0 ≤ t := by
    obtain ⟨i, rfl⟩ := hA.1.spectrum_real_eq_range_eigenvalues ▸ ht
    exact hA.eigenvalues_nonneg i
  by_cases hz : t = 0
  · simp [hz, Real.zero_rpow hx.ne', Real.zero_rpow hy.ne',
      Real.zero_rpow (add_pos hx hy).ne']
  · exact (Real.rpow_add (lt_of_le_of_ne ht0 (Ne.symm hz)) x y).symm

theorem rpow_sub_one_mul_self {A : Matrix I I ℂ} (hA : A.PosSemidef)
    {p : ℝ} (hp : 1 < p) : CFC.rpow A (p - 1) * A = CFC.rpow A p := by
  have h := rpow_mul_rpow_pos_exponents hA (sub_pos.mpr hp) (by norm_num : (0 : ℝ) < 1)
  have hone : CFC.rpow A (1 : ℝ) = A := CFC.rpow_one A hA.nonneg
  simpa only [hone, sub_add_cancel] using h

theorem rpow_sub_one_conjugate {A : Matrix I I ℂ} (hA : A.PosSemidef)
    {p : ℝ} (hp : 1 < p) :
    CFC.rpow (CFC.rpow A (p - 1)) (p / (p - 1)) = CFC.rpow A p := by
  have hm : (p - 1) * (p / (p - 1)) = p := by
    field_simp [(sub_pos.mpr hp).ne']
  have h : CFC.rpow (CFC.rpow A (p - 1)) (p / (p - 1)) =
      CFC.rpow A ((p - 1) * (p / (p - 1))) :=
    CFC.rpow_rpow_of_exponent_nonneg A (p - 1) (p / (p - 1))
      (sub_pos.mpr hp).le (div_pos (lt_trans zero_lt_one hp) (sub_pos.mpr hp)).le hA.nonneg
  simpa only [hm] using h

theorem norm_trace_rpow_sub_one_mul_self {A : Matrix I I ℂ} (hA : A.PosSemidef)
    {p : ℝ} (hp : 1 < p) :
    ‖(CFC.rpow A (p - 1) * A).trace‖ = schattenPower p A := by
  rw [rpow_sub_one_mul_self hA hp, schattenPower_of_posSemidef p hA]
  exact (Complex.re_eq_norm.mpr
    (CFC.rpow_nonneg : 0 ≤ CFC.rpow A p).posSemidef.trace_nonneg).symm

theorem trace_rpow_sub_one_conjugate {A : Matrix I I ℂ} (hA : A.PosSemidef)
    {p : ℝ} (hp : 1 < p) :
    (CFC.rpow (CFC.rpow A (p - 1)) (p / (p - 1))).trace.re =
      schattenPower p A := by
  rw [rpow_sub_one_conjugate hA hp, schattenPower_of_posSemidef p hA]

section AnalyticMaps

variable {O Z : Type*} [Fintype O] [DecidableEq O] [Fintype Z]

theorem differentiable_krausAction_comp (K : Z → Matrix O I ℂ)
    {f : ℂ → Matrix I I ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z => krausAction K (f z)) :=
  (krausMap K).toContinuousLinearMap.differentiable.comp hf

theorem norm_krausAction_le_opNorm (K : Z → Matrix O I ℂ) (X : Matrix I I ℂ) :
    ‖krausAction K X‖ ≤ ‖(krausMap K).toContinuousLinearMap‖ * ‖X‖ :=
  (krausMap K).toContinuousLinearMap.le_opNorm X

end AnalyticMaps

theorem differentiable_matrixTrace_comp {f : ℂ → Matrix I I ℂ}
    (hf : Differentiable ℂ f) : Differentiable ℂ (fun z => (f z).trace) :=
  (Matrix.traceLinearMap I ℂ ℂ).toContinuousLinearMap.differentiable.comp hf

theorem norm_matrixTrace_le_opNorm (X : Matrix I I ℂ) :
    ‖X.trace‖ ≤ ‖(Matrix.traceLinearMap I ℂ ℂ).toContinuousLinearMap‖ * ‖X‖ :=
  (Matrix.traceLinearMap I ℂ ℂ).toContinuousLinearMap.le_opNorm X

private theorem norm_mul_le_bounds {S : Type*} [Fintype S] [DecidableEq S]
    (X Y : Matrix S S ℂ) {a b : ℝ} (hX : ‖X‖ ≤ a) (hY : ‖Y‖ ≤ b) :
    ‖X * Y‖ ≤ a * b :=
  (norm_mul_le X Y).trans
    (mul_le_mul hX hY (norm_nonneg Y) ((norm_nonneg X).trans hX))

section MatrixWitness

open Complex.HadamardThreeLines

variable {O Z : Type*} [Fintype O] [DecidableEq O] [Fintype Z]

theorem differentiable_tiltedKrausAction_comp (K : Z → Matrix O I ℂ)
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) {f : ℂ → Matrix I I ℂ}
    (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z => tiltedKrausAction K hσ z (f z)) := by
  have hD : Differentiable ℂ (fun z : ℂ =>
      complexPower (krausAction_posSemidef K hσ) ((z - 1) / 2)) :=
    (differentiable_complexPower (krausAction_posSemidef K hσ)).comp
      ((differentiable_id.sub_const (1 : ℂ)).div_const (2 : ℂ))
  have hE : Differentiable ℂ (fun z : ℂ => complexPower hσ ((1 - z) / 2)) :=
    (differentiable_complexPower hσ).comp
      (((differentiable_const (1 : ℂ)).sub differentiable_id).div_const (2 : ℂ))
  exact (hD.mul (differentiable_krausAction_comp K ((hE.mul hf).mul hE))).mul hD

theorem differentiable_analyticTraceWitness (K : Z → Matrix O I ℂ)
    {σ A : Matrix I I ℂ} {B : Matrix O O ℂ}
    (hσ : σ.PosSemidef) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (U : Matrix I I ℂ) (V : Matrix O O ℂ) (p q : ℝ) :
    Differentiable ℂ (analyticTraceWitness K hσ hA hB U V p q) := by
  have hAcp : Differentiable ℂ (fun z : ℂ => complexPower hA ((p : ℂ) * z)) :=
    (differentiable_complexPower hA).comp
      ((differentiable_const (p : ℂ)).mul differentiable_id)
  have hBcp : Differentiable ℂ (fun z : ℂ =>
      complexPower hB ((q : ℂ) * (1 - z))) :=
    (differentiable_complexPower hB).comp
      ((differentiable_const (q : ℂ)).mul
        ((differentiable_const (1 : ℂ)).sub differentiable_id))
  exact differentiable_matrixTrace_comp
    ((hBcp.mul_const V).mul
      (differentiable_tiltedKrausAction_comp K hσ
        ((differentiable_const U).mul hAcp)))

theorem norm_tiltedKrausAction_le_stripBound (K : Z → Matrix O I ℂ)
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) (X : Matrix I I ℂ) :
    ‖tiltedKrausAction K hσ z X‖ ≤
      complexPowerStripBound (krausAction_posSemidef K hσ) 1 *
        (complexPowerStripBound hσ 1 * ‖X‖ * complexPowerStripBound hσ 1) *
      complexPowerStripBound (krausAction_posSemidef K hσ) 1 := by
  have hz01 : 0 ≤ z.re ∧ z.re ≤ 1 := hz
  have hzhalf : (z / 2).re = z.re / 2 := by simp
  have hnegzhalf : (-z / 2).re = -z.re / 2 := by simp
  have hD : ‖complexPower (krausAction_posSemidef K hσ) (z / 2)‖ ≤
      complexPowerStripBound (krausAction_posSemidef K hσ) 1 :=
    norm_complexPower_le_stripBound _ (by
      rw [hzhalf]
      exact abs_le.mpr ⟨by linarith [hz01.1], by linarith [hz01.2]⟩)
  have hE : ‖complexPower hσ (-z / 2)‖ ≤ complexPowerStripBound hσ 1 :=
    norm_complexPower_le_stripBound _ (by
      rw [hnegzhalf]
      exact abs_le.mpr ⟨by linarith [hz01.2], by linarith [hz01.1]⟩)
  have hinside : ‖complexPower hσ (-z / 2) * X * complexPower hσ (-z / 2)‖ ≤
      complexPowerStripBound hσ 1 * ‖X‖ * complexPowerStripBound hσ 1 :=
    norm_mul_le_bounds _ _ (norm_mul_le_bounds _ _ hE le_rfl) hE
  have hmap := (norm_normalizedKraus_action_le K hσ _).trans hinside
  rw [tiltedKrausAction_eq_normalized]
  exact norm_mul_le_bounds _ _ (norm_mul_le_bounds _ _ hD hmap) hD

theorem analyticTraceWitness_bddAbove (K : Z → Matrix O I ℂ)
    {σ A : Matrix I I ℂ} {B : Matrix O O ℂ}
    (hσ : σ.PosSemidef) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (U : Matrix I I ℂ) (V : Matrix O O ℂ) (p q : ℝ) :
    BddAbove ((norm ∘ analyticTraceWitness K hσ hA hB U V p q) ''
      verticalClosedStrip 0 1) := by
  let a := complexPowerStripBound hA |p|
  let b := complexPowerStripBound hB |q|
  let s := complexPowerStripBound hσ 1
  let t := complexPowerStripBound (krausAction_posSemidef K hσ) 1
  let c := ‖(Matrix.traceLinearMap O ℂ ℂ).toContinuousLinearMap‖
  refine ⟨c * (b * ‖V‖ * (t * (s * (‖U‖ * a) * s) * t)), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz01 : 0 ≤ z.re ∧ z.re ≤ 1 := hz
  have hzabs : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith [hz01.1], hz01.2⟩
  have honeabs : |1 - z.re| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hz01.2], by linarith [hz01.1]⟩
  have hAp : ‖complexPower hA ((p : ℂ) * z)‖ ≤ a :=
    norm_complexPower_le_stripBound hA (by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, abs_mul, mul_one] using
        mul_le_mul_of_nonneg_left hzabs (abs_nonneg p))
  have hBq : ‖complexPower hB ((q : ℂ) * (1 - z))‖ ≤ b :=
    norm_complexPower_le_stripBound hB (by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.sub_re, Complex.one_re, abs_mul, mul_one] using
        mul_le_mul_of_nonneg_left honeabs (abs_nonneg q))
  have hX : ‖U * complexPower hA ((p : ℂ) * z)‖ ≤ ‖U‖ * a :=
    norm_mul_le_bounds _ _ le_rfl hAp
  have htilt : ‖tiltedKrausAction K hσ z (U * complexPower hA ((p : ℂ) * z))‖ ≤
      t * (s * (‖U‖ * a) * s) * t := by
    apply (norm_tiltedKrausAction_le_stripBound K hσ hz _).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hX (complexPowerStripBound_nonnegative hσ 1))
          (complexPowerStripBound_nonnegative hσ 1))
        (complexPowerStripBound_nonnegative _ 1))
      (complexPowerStripBound_nonnegative _ 1)
  apply (norm_matrixTrace_le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact norm_mul_le_bounds _ _ (norm_mul_le_bounds _ _ hBq le_rfl) htilt

theorem norm_analyticTraceWitness_le_interior (K : Z → Matrix O I ℂ)
    (hK : krausGram K = 1) {σ A : Matrix I I ℂ} {B : Matrix O O ℂ}
    (hσ : σ.PosSemidef) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (U : Matrix I I ℂ) (V : Matrix O O ℂ) (p q : ℝ)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (hp : 0 < p) (hq : 0 < q)
    {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    ‖analyticTraceWitness K hσ hA hB U V p q z‖ ≤
      ((CFC.rpow B q).trace.re) ^ (1 - z.re) *
        ((CFC.rpow A p).trace.re) ^ z.re := by
  apply norm_le_interp_of_mem_verticalClosedStrip₀₁' _ hz
    (differentiable_analyticTraceWitness K hσ hA hB U V p q).diffContOnCl
    (analyticTraceWitness_bddAbove K hσ hA hB U V p q)
  · intro w hw
    exact norm_analyticTraceWitness_zero_le K hσ hA hB U V p q hU hV hp hq
      (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hw)
  · intro w hw
    exact norm_analyticTraceWitness_one_le K hK hσ hA hB U V p q hU hV hp hq
      (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hw)

theorem analyticTraceWitness_at_reciprocal (K : Z → Matrix O I ℂ)
    {σ A : Matrix I I ℂ} {B : Matrix O O ℂ}
    (hσ : σ.PosSemidef) (hA : A.PosSemidef) (hB : B.PosSemidef)
    {p : ℝ} (hp : 1 < p) :
    analyticTraceWitness K hσ hA hB 1 1 p (p / (p - 1)) ((1 / p : ℝ) : ℂ) =
      (B * tiltedKrausAction K hσ ((1 / p : ℝ) : ℂ) A).trace := by
  have hp0 : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hp1 : p - 1 ≠ 0 := (sub_pos.mpr hp).ne'
  have hpr : p * (1 / p : ℝ) = 1 := by field_simp [hp0]
  have hqr : p / (p - 1) * (1 - 1 / p : ℝ) = 1 := by
    field_simp [hp0, hp1]
  have hpC : (p : ℂ) * ((1 / p : ℝ) : ℂ) = 1 := by exact_mod_cast hpr
  have hqC : ((p / (p - 1) : ℝ) : ℂ) * (1 - ((1 / p : ℝ) : ℂ)) = 1 := by
    exact_mod_cast hqr
  unfold analyticTraceWitness
  rw [hpC, hqC, complexPower_one, complexPower_one, Matrix.mul_one, Matrix.one_mul]

end MatrixWitness

theorem le_of_le_rpow_product {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hθ : 0 < θ) (h : a ≤ a ^ (1 - θ) * b ^ θ) : a ≤ b := by
  by_cases hz : a = 0
  · simpa only [hz] using hb
  · have ha0 : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    have hsplit : a = a ^ (1 - θ) * a ^ θ := by
      rw [← Real.rpow_add ha0]
      simp
    have hmul : a ^ (1 - θ) * a ^ θ ≤ a ^ (1 - θ) * b ^ θ := by
      calc
        a ^ (1 - θ) * a ^ θ = a := hsplit.symm
        _ ≤ a ^ (1 - θ) * b ^ θ := h
    have hcancel : a ^ θ ≤ b ^ θ :=
      le_of_mul_le_mul_left hmul (Real.rpow_pos_of_pos ha0 (1 - θ))
    exact (Real.rpow_le_rpow_iff ha hb hθ).mp hcancel

private theorem matrix_norm_one_le {S : Type*} [Fintype S] [DecidableEq S] :
    ‖(1 : Matrix S S ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by norm_num

theorem schattenPower_tiltedKrausAction_le_of_posSemidef
    {O Z : Type*} [Fintype O] [DecidableEq O] [Fintype Z]
    (K : Z → Matrix O I ℂ) (hK : krausGram K = 1)
    {σ A : Matrix I I ℂ} (hσ : σ.PosSemidef) (hA : A.PosSemidef)
    {p : ℝ} (hp : 1 < p)
    (hY : (tiltedKrausAction K hσ ((1 / p : ℝ) : ℂ) A).PosSemidef) :
    schattenPower p (tiltedKrausAction K hσ ((1 / p : ℝ) : ℂ) A) ≤
      schattenPower p A := by
  let Y := tiltedKrausAction K hσ ((1 / p : ℝ) : ℂ) A
  let B := CFC.rpow Y (p - 1)
  have hB : B.PosSemidef := (CFC.rpow_nonneg : 0 ≤ B).posSemidef
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < p / (p - 1) := div_pos hp0 (sub_pos.mpr hp)
  have hθ0 : 0 < (1 / p : ℝ) := one_div_pos.mpr hp0
  have hθ1 : (1 / p : ℝ) < 1 := (div_lt_one hp0).mpr hp
  have hθ : ((1 / p : ℝ) : ℂ) ∈
      Complex.HadamardThreeLines.verticalClosedStrip 0 1 := ⟨hθ0.le, hθ1.le⟩
  have hbound := norm_analyticTraceWitness_le_interior K hK hσ hA hB
    1 1 p (p / (p - 1)) matrix_norm_one_le matrix_norm_one_le hp0 hq0 hθ
  have hnorm :
      ‖analyticTraceWitness K hσ hA hB 1 1 p (p / (p - 1)) ((1 / p : ℝ) : ℂ)‖ =
        schattenPower p Y := by
    rw [analyticTraceWitness_at_reciprocal K hσ hA hB hp]
    exact norm_trace_rpow_sub_one_mul_self hY hp
  have hdual : (CFC.rpow B (p / (p - 1))).trace.re = schattenPower p Y :=
    trace_rpow_sub_one_conjugate hY hp
  have hinput : (CFC.rpow A p).trace.re = schattenPower p A :=
    (schattenPower_of_posSemidef p hA).symm
  rw [hnorm, hdual, hinput, Complex.ofReal_re] at hbound
  exact le_of_le_rpow_product (schattenPower_nonneg p Y)
    (schattenPower_nonneg p A) hθ0 hbound

section NumericDPI

open QuantumProver.AmplitudeDamping.FiniteModel

variable {O Z : Type*} [Fintype O] [DecidableEq O] [Fintype Z]

theorem schattenPower_tiltedKrausAction_le (K : Z → Matrix O I ℂ)
    (hK : krausGram K = 1) {σ A : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (hA : A.PosSemidef) {p : ℝ} (hp : 1 < p) :
    schattenPower p (tiltedKrausAction K hσ ((1 / p : ℝ) : ℂ) A) ≤
      schattenPower p A := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  exact schattenPower_tiltedKrausAction_le_of_posSemidef K hK hσ hA hp
    (tiltedKrausAction_ofReal_posSemidef K hσ (one_div_pos.mpr hp0)
      ((div_lt_one hp0).mpr hp) hA)

theorem schattenNorm_tiltedKrausAction_le (K : Z → Matrix O I ℂ)
    (hK : krausGram K = 1) {σ A : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (hA : A.PosSemidef) {p : ℝ} (hp : 1 < p) :
    schattenNorm p (tiltedKrausAction K hσ ((1 / p : ℝ) : ℂ) A) ≤
      schattenNorm p A := by
  exact Real.rpow_le_rpow (schattenPower_nonneg p _)
    (schattenPower_tiltedKrausAction_le K hK hσ hA hp)
    (one_div_pos.mpr (lt_trans zero_lt_one hp)).le

theorem sandwichedTrace_krausAction_le (K : Z → Matrix O I ℂ)
    (hK : krausGram K = 1) {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {p : ℝ} (hp : 1 < p) :
    sandwichedTrace p (krausAction K ρ) (krausAction K σ) ≤
      sandwichedTrace p ρ σ := by
  let W := CFC.rpow σ ((1 - p) / (2 * p))
  let A := W * ρ * W
  have hW : W.IsHermitian := (CFC.rpow_nonneg : 0 ≤ W).posSemidef.1
  have hA : A.PosSemidef := by
    simpa only [hW.eq] using hρ.conjTranspose_mul_mul_same W
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hY : (tiltedKrausAction K hσ ((1 / p : ℝ) : ℂ) A).PosSemidef :=
    tiltedKrausAction_ofReal_posSemidef K hσ (one_div_pos.mpr hp0)
      ((div_lt_one hp0).mpr hp) hA
  have hbound := schattenPower_tiltedKrausAction_le K hK hσ hA hp
  rw [schattenPower_of_posSemidef p hY, schattenPower_of_posSemidef p hA] at hbound
  rw [sandwichedTrace_krausAction_eq_tilted K hρ hσ hs hp]
  exact hbound

theorem sandwichedTrace_zero_input {p : ℝ} (hp : 0 < p) (σ : Matrix I I ℂ) :
    sandwichedTrace p 0 σ = 0 := by
  simp only [sandwichedTrace, Matrix.mul_zero, Matrix.zero_mul,
    CFC.zero_rpow hp.ne', Matrix.trace_zero, Complex.zero_re]

theorem sandwichedDivergence_krausAction_le (K : Z → Matrix O I ℂ)
    (hK : krausGram K = 1) {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {p : ℝ} (hp : 1 < p) :
    sandwichedDivergence p (krausAction K ρ) (krausAction K σ) ≤
      sandwichedDivergence p ρ σ := by
  by_cases hs : SupportLE ρ σ
  · have houts := supportLE_krausAction K hρ hσ hs
    simp only [sandwichedDivergence, ite_eq_left hs, ite_eq_left houts,
      EReal.coe_le_coe_iff]
    have hp0 : 0 < p := lt_trans zero_lt_one hp
    by_cases hzero : ρ = 0
    · subst ρ
      have hk0 : krausAction K (0 : Matrix I I ℂ) = 0 := by
        simp only [krausAction, Matrix.mul_zero, Matrix.zero_mul, Finset.sum_const_zero]
      rw [hk0, sandwichedTrace_zero_input hp0, sandwichedTrace_zero_input hp0]
    · have houtzero : krausAction K ρ ≠ 0 := by
        intro hz
        have htrace := krausAction_tracePreserving K hK ρ
        rw [hz, Matrix.trace_zero] at htrace
        exact hzero (hρ.trace_eq_zero_iff.mp htrace.symm)
      have houtpos := sandwichedTrace_pos_of_supportLE
        (krausAction_posSemidef K hρ) (krausAction_posSemidef K hσ) houts houtzero hp
      have hQ := sandwichedTrace_krausAction_le K hK hρ hσ hs hp
      have hden : 0 < (p - 1) * Real.log 2 :=
        mul_pos (sub_pos.mpr hp) (Real.log_pos (by norm_num))
      exact div_le_div_of_nonneg_right (Real.log_le_log houtpos hQ) hden.le
  · simp only [sandwichedDivergence, ite_eq_right hs, le_top]

end NumericDPI

end QuantumProver.SandwichedDPI
