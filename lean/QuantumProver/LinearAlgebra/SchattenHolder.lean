import QuantumProver.LinearAlgebra.SandwichedDPI.Interpolation

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
open Matrix Complex Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Topology

namespace QuantumProver.SandwichedDPI

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem holder_norm_one_le : ‖(1 : Matrix I I ℂ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ => by norm_num

private theorem holder_norm_mul_bound (X Y : Matrix I I ℂ) {a b : ℝ}
    (hX : ‖X‖ ≤ a) (hY : ‖Y‖ ≤ b) : ‖X * Y‖ ≤ a * b :=
  (norm_mul_le X Y).trans
    (mul_le_mul hX hY (norm_nonneg Y) ((norm_nonneg X).trans hX))

private theorem holder_norm_mul_contraction (X Y : Matrix I I ℂ)
    (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) : ‖X * Y‖ ≤ 1 := by
  simpa only [one_mul] using holder_norm_mul_bound X Y hX hY

private theorem holder_norm_trace_le (X : Matrix I I ℂ) : ‖X.trace‖ ≤ traceNorm X := by
  simpa only [Matrix.one_mul] using norm_trace_mul_le_traceNorm 1 X holder_norm_one_le

def holderTraceWitness {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (U V D : Matrix I I ℂ) (x y : ℝ) (z : ℂ) : ℂ :=
  (complexPower hA ((x : ℂ) * (1 - z)) * U *
    complexPower hB ((y : ℂ) * z) * V * D).trace

theorem differentiable_holderTraceWitness {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (U V D : Matrix I I ℂ) (x y : ℝ) :
    Differentiable ℂ (holderTraceWitness hA hB U V D x y) := by
  have hX : Differentiable ℂ (fun z : ℂ => complexPower hA ((x : ℂ) * (1 - z))) :=
    (differentiable_complexPower hA).comp
      ((differentiable_const (x : ℂ)).mul
        ((differentiable_const (1 : ℂ)).sub differentiable_id))
  have hY : Differentiable ℂ (fun z : ℂ => complexPower hB ((y : ℂ) * z)) :=
    (differentiable_complexPower hB).comp
      ((differentiable_const (y : ℂ)).mul differentiable_id)
  exact differentiable_matrixTrace_comp ((((hX.mul_const U).mul hY).mul_const V).mul_const D)

theorem holderTraceWitness_bddAbove {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (U V D : Matrix I I ℂ) (x y : ℝ) :
    BddAbove ((norm ∘ holderTraceWitness hA hB U V D x y) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  let a := complexPowerStripBound hA |x|
  let b := complexPowerStripBound hB |y|
  let c := ‖(Matrix.traceLinearMap I ℂ ℂ).toContinuousLinearMap‖
  refine ⟨c * (a * ‖U‖ * b * ‖V‖ * ‖D‖), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz01 : 0 ≤ z.re ∧ z.re ≤ 1 := hz
  have hzabs : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith [hz01.1], hz01.2⟩
  have honeabs : |1 - z.re| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hz01.2], by linarith [hz01.1]⟩
  have hX : ‖complexPower hA ((x : ℂ) * (1 - z))‖ ≤ a :=
    norm_complexPower_le_stripBound hA (by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.sub_re, Complex.one_re, abs_mul, mul_one] using
        mul_le_mul_of_nonneg_left honeabs (abs_nonneg x))
  have hY : ‖complexPower hB ((y : ℂ) * z)‖ ≤ b :=
    norm_complexPower_le_stripBound hB (by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, abs_mul, mul_one] using
        mul_le_mul_of_nonneg_left hzabs (abs_nonneg y))
  apply (norm_matrixTrace_le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact holder_norm_mul_bound _ _
    (holder_norm_mul_bound _ _
      (holder_norm_mul_bound _ _ (holder_norm_mul_bound _ _ hX le_rfl) hY) le_rfl) le_rfl

theorem holderTraceWitness_zero_le {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (U V : Matrix I I ℂ)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) {r s : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : z.re = 0) :
    ‖holderTraceWitness hA hB U V 1 r s z‖ ≤ (CFC.rpow A r).trace.re := by
  have hXre : ((r : ℂ) * (1 - z)).re = r := by simp [hz]
  have hYre : ((s : ℂ) * z).re = 0 := by simp [hz]
  have hY := norm_complexPower_of_re_eq_zero hB hYre
  unfold holderTraceWitness
  rw [Matrix.mul_one]
  apply (holder_norm_trace_le _).trans
  calc
    traceNorm (complexPower hA ((r : ℂ) * (1 - z)) * U *
        complexPower hB ((s : ℂ) * z) * V) ≤
        traceNorm (complexPower hA ((r : ℂ) * (1 - z))) :=
      (traceNorm_mul_right_le _ V hV).trans
        ((traceNorm_mul_right_le _ _ hY).trans (traceNorm_mul_right_le _ U hU))
    _ = _ := by rw [traceNorm_complexPower_of_re_pos hA (by rwa [hXre]), hXre]

theorem holderTraceWitness_one_le {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (U V : Matrix I I ℂ)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) {r s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : z.re = 1) :
    ‖holderTraceWitness hA hB U V 1 r s z‖ ≤ (CFC.rpow B s).trace.re := by
  have hXre : ((r : ℂ) * (1 - z)).re = 0 := by simp [hz]
  have hYre : ((s : ℂ) * z).re = s := by simp [hz]
  have hX := norm_complexPower_of_re_eq_zero hA hXre
  have hXU := holder_norm_mul_contraction _ U hX hU
  unfold holderTraceWitness
  rw [Matrix.mul_one]
  apply (holder_norm_trace_le _).trans
  calc
    traceNorm (complexPower hA ((r : ℂ) * (1 - z)) * U *
        complexPower hB ((s : ℂ) * z) * V) ≤
        traceNorm (complexPower hB ((s : ℂ) * z)) :=
      (traceNorm_mul_right_le _ V hV).trans (traceNorm_mul_left_le _ _ hXU)
    _ = _ := by rw [traceNorm_complexPower_of_re_pos hB (by rwa [hYre]), hYre]

theorem norm_trace_twoFactors_le (r s : ℝ) (A B U V : Matrix I I ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hr : 1 < r) (hs : 1 < s) (hexp : 1 / r + 1 / s = 1) :
    ‖(A * U * B * V).trace‖ ≤
      ((CFC.rpow A r).trace.re) ^ (1 / r : ℝ) *
        ((CFC.rpow B s).trace.re) ^ (1 / s : ℝ) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hθ0 : 0 < (1 / s : ℝ) := div_pos zero_lt_one hs0
  have hθ1 : (1 / s : ℝ) < 1 := (div_lt_one hs0).mpr hs
  have hrrec : 1 - 1 / s = (1 / r : ℝ) := by linarith
  have hxr : r * (1 - 1 / s : ℝ) = 1 := by rw [hrrec]; field_simp [hr0.ne']
  have hys : s * (1 / s : ℝ) = 1 := by field_simp [hs0.ne']
  have hxrC : (r : ℂ) * (1 - ((1 / s : ℝ) : ℂ)) = 1 := by exact_mod_cast hxr
  have hysC : (s : ℂ) * ((1 / s : ℝ) : ℂ) = 1 := by exact_mod_cast hys
  have hAt : holderTraceWitness hA hB U V 1 r s ((1 / s : ℝ) : ℂ) =
      (A * U * B * V).trace := by
    unfold holderTraceWitness
    rw [hxrC, hysC, complexPower_one, complexPower_one, Matrix.mul_one]
  have hz : ((1 / s : ℝ) : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    exact ⟨by simpa using hθ0.le, by simpa using hθ1.le⟩
  have hBound : ‖holderTraceWitness hA hB U V 1 r s ((1 / s : ℝ) : ℂ)‖ ≤
      ((CFC.rpow A r).trace.re) ^ (1 - 1 / s : ℝ) *
        ((CFC.rpow B s).trace.re) ^ (1 / s : ℝ) := by
    apply Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
      _ hz (differentiable_holderTraceWitness hA hB U V 1 r s).diffContOnCl
      (holderTraceWitness_bddAbove hA hB U V 1 r s)
    · intro z hz0
      exact holderTraceWitness_zero_le hA hB U V hU hV hr0
        (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz0)
    · intro z hz1
      exact holderTraceWitness_one_le hA hB U V hU hV hs0
        (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz1)
  rwa [hAt, hrrec] at hBound

end QuantumProver.SandwichedDPI

namespace QuantumProver.SandwichedDPI

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem holder_complexPower_real_imaginary {A : Matrix I I ℂ}
    (hA : A.PosSemidef) {z : ℂ} (hz : 0 < z.re) :
    complexPower hA z = CFC.rpow A z.re * complexPower hA (Complex.I * (z.im : ℂ)) := by
  have he : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
    apply Complex.ext <;> simp
  calc
    complexPower hA z = complexPower hA ((z.re : ℂ) + Complex.I * (z.im : ℂ)) :=
      congrArg (complexPower hA) he
    _ = complexPower hA (z.re : ℂ) * complexPower hA (Complex.I * (z.im : ℂ)) :=
      complexPower_add hA _ _
    _ = _ := by rw [complexPower_real hA hz.ne']

theorem holderTraceWitness_zero_twoFactor_le (C A B U V : Matrix I I ℂ)
    (hC : C.PosSemidef) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (x y r s : ℝ)
    (hx : 0 < x) (hr : 1 < r) (hs : 1 < s) (hexp : 1 / r + 1 / s = 1)
    {z : ℂ} (hz : z.re = 0) :
    ‖holderTraceWitness hC hA U V B x y z‖ ≤
      ((CFC.rpow C (x * r)).trace.re) ^ (1 / r : ℝ) *
        ((CFC.rpow B s).trace.re) ^ (1 / s : ℝ) := by
  have hXre : ((x : ℂ) * (1 - z)).re = x := by simp [hz]
  have hYre : ((y : ℂ) * z).re = 0 := by simp [hz]
  have hDec := holder_complexPower_real_imaginary hC
    (z := (x : ℂ) * (1 - z)) (by rwa [hXre])
  rw [hXre] at hDec
  let P := complexPower hC (Complex.I * (((x : ℂ) * (1 - z)).im : ℂ))
  let Q := complexPower hA ((y : ℂ) * z)
  let W := P * U * Q * V
  have hP : ‖P‖ ≤ 1 := norm_complexPower_imaginary_le_one hC _
  have hQ : ‖Q‖ ≤ 1 := norm_complexPower_of_re_eq_zero hA hYre
  have hW : ‖W‖ ≤ 1 :=
    holder_norm_mul_contraction _ V
      (holder_norm_mul_contraction _ Q (holder_norm_mul_contraction P U hP hU) hQ) hV
  have hAt : holderTraceWitness hC hA U V B x y z =
      (CFC.rpow C x * W * B * (1 : Matrix I I ℂ)).trace := by
    dsimp only [holderTraceWitness, W, P, Q]
    rw [hDec]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hBound := norm_trace_twoFactors_le r s (CFC.rpow C x) B W 1
    (CFC.rpow_nonneg : 0 ≤ CFC.rpow C x).posSemidef hB hW holder_norm_one_le hr hs hexp
  have hPow : CFC.rpow (CFC.rpow C x) r = CFC.rpow C (x * r) :=
    CFC.rpow_rpow_of_exponent_nonneg C x r hx.le
      (lt_trans zero_lt_one hr).le hC.nonneg
  rw [hPow] at hBound
  rwa [hAt]

theorem holderTraceWitness_one_twoFactor_le (C A B U V : Matrix I I ℂ)
    (hC : C.PosSemidef) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (x y r s : ℝ)
    (hy : 0 < y) (hr : 1 < r) (hs : 1 < s) (hexp : 1 / r + 1 / s = 1)
    {z : ℂ} (hz : z.re = 1) :
    ‖holderTraceWitness hC hA U V B x y z‖ ≤
      ((CFC.rpow A (y * r)).trace.re) ^ (1 / r : ℝ) *
        ((CFC.rpow B s).trace.re) ^ (1 / s : ℝ) := by
  have hXre : ((x : ℂ) * (1 - z)).re = 0 := by simp [hz]
  have hYre : ((y : ℂ) * z).re = y := by simp [hz]
  have hDec := holder_complexPower_real_imaginary hA
    (z := (y : ℂ) * z) (by rwa [hYre])
  rw [hYre] at hDec
  let P := complexPower hA (Complex.I * (((y : ℂ) * z).im : ℂ))
  let Q := complexPower hC ((x : ℂ) * (1 - z))
  let W := P * V
  let Z := Q * U
  have hP : ‖P‖ ≤ 1 := norm_complexPower_imaginary_le_one hA _
  have hQ : ‖Q‖ ≤ 1 := norm_complexPower_of_re_eq_zero hC hXre
  have hW : ‖W‖ ≤ 1 := holder_norm_mul_contraction P V hP hV
  have hZ : ‖Z‖ ≤ 1 := holder_norm_mul_contraction Q U hQ hU
  have hAt : holderTraceWitness hC hA U V B x y z =
      (CFC.rpow A y * W * B * Z).trace := by
    calc
      _ = ((Q * U) * (CFC.rpow A y * W * B)).trace := by
        dsimp only [holderTraceWitness, Q, W, P]
        rw [hDec]
        simp only [Matrix.mul_assoc]
      _ = _ := Matrix.trace_mul_comm _ _
  have hBound := norm_trace_twoFactors_le r s (CFC.rpow A y) B W Z
    (CFC.rpow_nonneg : 0 ≤ CFC.rpow A y).posSemidef hB hW hZ hr hs hexp
  have hPow : CFC.rpow (CFC.rpow A y) r = CFC.rpow A (y * r) :=
    CFC.rpow_rpow_of_exponent_nonneg A y r hy.le
      (lt_trans zero_lt_one hr).le hA.nonneg
  rw [hPow] at hBound
  rwa [hAt]

private theorem holder_interpolation_product (a b c r s t q θ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hr : 0 < r) (hs : 0 < s)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hCexp : (1 / r : ℝ) * (1 - θ) = 1 / t)
    (hAexp : (1 / r : ℝ) * θ = 1 / q) :
    (c ^ (1 / r : ℝ) * b ^ (1 / s : ℝ)) ^ (1 - θ) *
        (a ^ (1 / r : ℝ) * b ^ (1 / s : ℝ)) ^ θ =
      c ^ (1 / t : ℝ) * a ^ (1 / q : ℝ) * b ^ (1 / s : ℝ) := by
  have hb0 : 0 ≤ (1 / s : ℝ) * (1 - θ) :=
    mul_nonneg (div_nonneg zero_le_one hs.le) (sub_nonneg.mpr hθ1)
  have hb1 : 0 ≤ (1 / s : ℝ) * θ :=
    mul_nonneg (div_nonneg zero_le_one hs.le) hθ0
  calc
    _ = (c ^ ((1 / r : ℝ) * (1 - θ)) * a ^ ((1 / r : ℝ) * θ)) *
        (b ^ ((1 / s : ℝ) * (1 - θ)) * b ^ ((1 / s : ℝ) * θ)) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hc _) (Real.rpow_nonneg hb _),
        Real.mul_rpow (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _),
        ← Real.rpow_mul hc, ← Real.rpow_mul hb, ← Real.rpow_mul ha, ← Real.rpow_mul hb]
      ring
    _ = _ := by
      rw [hCexp, hAexp, ← Real.rpow_add_of_nonneg hb hb0 hb1]
      congr 1
      congr 1
      ring

theorem norm_trace_threeFactors_le (p q s : ℝ) (C A B U V : Matrix I I ℂ)
    (hC : C.PosSemidef) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hp : 1 < p) (hq : 1 < q) (hs : 1 < s) (hexp : 1 / p = 1 / q + 1 / s) :
    ‖(C * U * A * V * B).trace‖ ≤
      ((CFC.rpow C (p / (p - 1))).trace.re) ^ (1 / (p / (p - 1)) : ℝ) *
        ((CFC.rpow A q).trace.re) ^ (1 / q : ℝ) *
        ((CFC.rpow B s).trace.re) ^ (1 / s : ℝ) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  let r := s / (s - 1)
  let t := p / (p - 1)
  have hr : 1 < r := (one_lt_div (sub_pos.mpr hs)).mpr (by linarith)
  have ht : 1 < t := (one_lt_div (sub_pos.mpr hp)).mpr (by linarith)
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hrrec : (1 / r : ℝ) = 1 - 1 / s := by
    dsimp only [r]
    field_simp [hs0.ne', (sub_pos.mpr hs).ne'] <;> ring
  have htrec : (1 / t : ℝ) = 1 - 1 / p := by
    dsimp only [t]
    field_simp [hp0.ne', (sub_pos.mpr hp).ne'] <;> ring
  have hrs : 1 / r + 1 / s = (1 : ℝ) := by rw [hrrec]; ring
  have hqRec : (1 / q : ℝ) < 1 / r := by
    rw [hrrec]
    have hpRec : (1 / p : ℝ) < 1 := (div_lt_one hp0).mpr hp
    linarith
  have hrq : r < q := by
    simpa only [one_mul] using (div_lt_div_iff₀ hq0 hr0).mp hqRec
  let θ := r / q
  let x := t / r
  let y := q / r
  have hθ0 : 0 < θ := div_pos hr0 hq0
  have hθ1 : θ < 1 := (div_lt_one hq0).mpr hrq
  have hx : 0 < x := div_pos ht0 hr0
  have hy : 0 < y := div_pos hq0 hr0
  have hxr : x * r = t := by dsimp only [x]; field_simp [hr0.ne']
  have hyr : y * r = q := by dsimp only [y]; field_simp [hr0.ne']
  have hCexp : (1 / r : ℝ) * (1 - θ) = 1 / t := by
    calc
      _ = 1 / r - 1 / q := by dsimp only [θ]; field_simp [hr0.ne', hq0.ne'] <;> ring
      _ = 1 - 1 / p := by rw [hrrec]; linarith
      _ = 1 / t := htrec.symm
  have hAexp : (1 / r : ℝ) * θ = 1 / q := by
    dsimp only [θ]
    field_simp [hr0.ne', hq0.ne']
  have hxAt : x * (1 - θ) = 1 := by
    calc
      _ = t * ((1 / r : ℝ) * (1 - θ)) := by dsimp only [x]; ring
      _ = 1 := by rw [hCexp]; field_simp [ht0.ne']
  have hyAt : y * θ = 1 := by
    dsimp only [y, θ]
    field_simp [hr0.ne', hq0.ne']
  have hxAtC : (x : ℂ) * (1 - (θ : ℂ)) = 1 := by exact_mod_cast hxAt
  have hyAtC : (y : ℂ) * (θ : ℂ) = 1 := by exact_mod_cast hyAt
  have hAt : holderTraceWitness hC hA U V B x y (θ : ℂ) =
      (C * U * A * V * B).trace := by
    unfold holderTraceWitness
    rw [hxAtC, hyAtC, complexPower_one, complexPower_one]
  let c := (CFC.rpow C t).trace.re
  let a := (CFC.rpow A q).trace.re
  let b := (CFC.rpow B s).trace.re
  have hc : 0 ≤ c := (Complex.nonneg_iff.mp
    (CFC.rpow_nonneg : 0 ≤ CFC.rpow C t).posSemidef.trace_nonneg).1
  have ha : 0 ≤ a := (Complex.nonneg_iff.mp
    (CFC.rpow_nonneg : 0 ≤ CFC.rpow A q).posSemidef.trace_nonneg).1
  have hb : 0 ≤ b := (Complex.nonneg_iff.mp
    (CFC.rpow_nonneg : 0 ≤ CFC.rpow B s).posSemidef.trace_nonneg).1
  have hz : (θ : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 :=
    ⟨by simpa using hθ0.le, by simpa using hθ1.le⟩
  have hBound : ‖holderTraceWitness hC hA U V B x y (θ : ℂ)‖ ≤
      (c ^ (1 / r : ℝ) * b ^ (1 / s : ℝ)) ^ (1 - θ) *
        (a ^ (1 / r : ℝ) * b ^ (1 / s : ℝ)) ^ θ := by
    apply Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
      _ hz (differentiable_holderTraceWitness hC hA U V B x y).diffContOnCl
      (holderTraceWitness_bddAbove hC hA U V B x y)
    · intro z hz0
      have h := holderTraceWitness_zero_twoFactor_le C A B U V hC hA hB hU hV
        x y r s hx hr hs hrs (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz0)
      simpa only [hxr] using h
    · intro z hz1
      have h := holderTraceWitness_one_twoFactor_le C A B U V hC hA hB hU hV
        x y r s hy hr hs hrs (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz1)
      simpa only [hyr] using h
  rw [hAt, holder_interpolation_product a b c r s t q θ ha hb hc hr0 hs0
    hθ0.le hθ1.le hCexp hAexp] at hBound
  exact hBound

end QuantumProver.SandwichedDPI

namespace QuantumProver.SandwichedDPI

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem holder_norm_unitary_le (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) : ‖U‖ ≤ 1 := by
  have hGram : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hSquare := CStarRing.norm_star_mul_self (x := U)
  rw [Matrix.star_eq_conjTranspose, hGram] at hSquare
  have hOne : ‖(1 : Matrix I I ℂ)‖ ≤ 1 := holder_norm_one_le
  nlinarith [norm_nonneg U]

private theorem holder_norm_unitary_adjoint_le (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) : ‖Uᴴ‖ ≤ 1 := by
  rw [← Matrix.star_eq_conjTranspose, norm_star]
  exact holder_norm_unitary_le U hU

private theorem holder_polar_reconstruct (A U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (hUA : U * A = CFC.abs A) :
    A = Uᴴ * CFC.abs A := by
  have hGram : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  calc
    A = (Uᴴ * U) * A := by rw [hGram, Matrix.one_mul]
    _ = Uᴴ * (U * A) := Matrix.mul_assoc _ _ _
    _ = _ := by rw [hUA]

theorem schattenNorm_mul_le (p q s : ℝ) (A B : Matrix I I ℂ)
    (hp : 1 ≤ p) (hq : 1 < q) (hs : 1 < s) (hexp : 1 / p = 1 / q + 1 / s) :
    schattenNorm p (A * B) ≤ schattenNorm q A * schattenNorm s B := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  by_cases hZero : A * B = 0
  · have hLeft : schattenNorm p (A * B) = 0 :=
      (schattenNorm_eq_zero_iff hp0 (A * B)).mpr hZero
    rw [hLeft]
    exact mul_nonneg (schattenNorm_nonneg q A) (schattenNorm_nonneg s B)
  obtain ⟨UA, hUA, hUAA⟩ := exists_unitary_polar A
  obtain ⟨UB, hUB, hUBB⟩ := exists_unitary_polar B
  have hArec := holder_polar_reconstruct A UA hUA hUAA
  have hBrec := holder_polar_reconstruct B UB hUB hUBB
  have hAB : A * B = (UAᴴ * CFC.abs A) * (UBᴴ * CFC.abs B) :=
    congrArg₂ (fun X Y : Matrix I I ℂ => X * Y) hArec hBrec
  have hAbsA : (CFC.abs A).PosSemidef := (CFC.abs_nonneg A).posSemidef
  have hAbsB : (CFC.abs B).PosSemidef := (CFC.abs_nonneg B).posSemidef
  have hUAnorm : ‖UAᴴ‖ ≤ 1 := holder_norm_unitary_adjoint_le UA hUA
  have hUBnorm : ‖UBᴴ‖ ≤ 1 := holder_norm_unitary_adjoint_le UB hUB
  by_cases hpOne : p = 1
  · subst p
    obtain ⟨UX, hUX, hTrace⟩ := exists_unitary_traceNorm_attainer (A * B)
    have hUXnorm : ‖UX‖ ≤ 1 := holder_norm_unitary_le UX hUX
    have hProductNorm : ‖UX * UAᴴ‖ ≤ 1 :=
      holder_norm_mul_contraction UX UAᴴ hUXnorm hUAnorm
    have hConj : 1 / q + 1 / s = (1 : ℝ) := by simpa only [one_div_one] using hexp.symm
    have hCycle : (UX * (A * B)).trace =
        (CFC.abs A * UBᴴ * CFC.abs B * (UX * UAᴴ)).trace := by
      calc
        _ = ((UX * UAᴴ) * (CFC.abs A * UBᴴ * CFC.abs B)).trace := by
          simpa only [Matrix.mul_assoc] using
            congrArg (fun Y : Matrix I I ℂ => (UX * Y).trace) hAB
        _ = _ := Matrix.trace_mul_comm _ _
    calc
      schattenNorm 1 (A * B) = traceNorm (A * B) := schattenNorm_one _
      _ = (UX * (A * B)).trace.re := hTrace.symm
      _ ≤ ‖(UX * (A * B)).trace‖ := Complex.re_le_norm _
      _ = ‖(CFC.abs A * UBᴴ * CFC.abs B * (UX * UAᴴ)).trace‖ := congrArg norm hCycle
      _ ≤ ((CFC.rpow (CFC.abs A) q).trace.re) ^ (1 / q : ℝ) *
          ((CFC.rpow (CFC.abs B) s).trace.re) ^ (1 / s : ℝ) :=
        norm_trace_twoFactors_le q s (CFC.abs A) (CFC.abs B) UBᴴ (UX * UAᴴ)
          hAbsA hAbsB hUBnorm hProductNorm hq hs hConj
      _ = _ := rfl
  · have hpStrict : 1 < p := lt_of_le_of_ne hp (Ne.symm hpOne)
    let X := A * B
    obtain ⟨UX, hUX, hUXX⟩ := exists_unitary_polar X
    have hUXnorm : ‖UX‖ ≤ 1 := holder_norm_unitary_le UX hUX
    have hProductNorm : ‖UX * UAᴴ‖ ≤ 1 :=
      holder_norm_mul_contraction UX UAᴴ hUXnorm hUAnorm
    have hAbsX : (CFC.abs X).PosSemidef := (CFC.abs_nonneg X).posSemidef
    let C := CFC.rpow (CFC.abs X) (p - 1)
    have hC : C.PosSemidef := (CFC.rpow_nonneg : 0 ≤ CFC.rpow (CFC.abs X) (p - 1)).posSemidef
    have hCpower : (CFC.rpow C (p / (p - 1))).trace.re = schattenPower p X := by
      dsimp only [C]
      rw [rpow_sub_one_conjugate hAbsX hpStrict]
      rfl
    have hDual : ‖(C * UX * X).trace‖ = schattenPower p X := by
      rw [Matrix.mul_assoc, hUXX]
      dsimp only [C]
      rw [rpow_sub_one_mul_self hAbsX hpStrict]
      exact (Complex.re_eq_norm.mpr
        (CFC.rpow_nonneg : 0 ≤ CFC.rpow (CFC.abs X) p).posSemidef.trace_nonneg).symm
    have hProduct : C * UX * X = C * (UX * UAᴴ) * CFC.abs A * UBᴴ * CFC.abs B := by
      simpa only [X, Matrix.mul_assoc] using
        congrArg (fun Y : Matrix I I ℂ => C * UX * Y) hAB
    have hBound := norm_trace_threeFactors_le p q s C (CFC.abs A) (CFC.abs B)
      (UX * UAᴴ) UBᴴ hC hAbsA hAbsB hProductNorm hUBnorm hpStrict hq hs hexp
    rw [← hProduct, hDual, hCpower] at hBound
    let t := p / (p - 1)
    have hConj : (1 / t : ℝ) + 1 / p = 1 := by
      dsimp only [t]
      field_simp [hp0.ne', (sub_pos.mpr hpStrict).ne'] <;> ring
    have hPowerPos : 0 < schattenPower p X := (schattenPower_pos_iff hp0 X).mpr hZero
    have hSplit : schattenPower p X =
        (schattenPower p X) ^ (1 / t : ℝ) * (schattenPower p X) ^ (1 / p : ℝ) := by
      rw [← Real.rpow_add hPowerPos, hConj, Real.rpow_one]
    have hMul : (schattenPower p X) ^ (1 / t : ℝ) * (schattenPower p X) ^ (1 / p : ℝ) ≤
        (schattenPower p X) ^ (1 / t : ℝ) * (schattenNorm q A * schattenNorm s B) := by
      rw [← hSplit]
      simpa only [schattenNorm, schattenPower, mul_assoc] using hBound
    exact le_of_mul_le_mul_left hMul (Real.rpow_pos_of_pos hPowerPos _)

end QuantumProver.SandwichedDPI
