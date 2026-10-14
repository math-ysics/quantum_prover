import QuantumProver.LinearAlgebra.SandwichedDPI.Interpolation

set_option autoImplicit false
noncomputable section

open Matrix Complex Set
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix
  Matrix.Norms.L2Operator

namespace QuantumProver.ArakiLiebThirringTrace

open QuantumProver.SandwichedDPI

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem norm_trace_mul_le_sqrt_gram (A B : Matrix I I ℂ) :
    ‖(A * B).trace‖ ≤
      Real.sqrt (A * Aᴴ).trace.re * Real.sqrt (Bᴴ * B).trace.re := by
  letI : SeminormedAddCommGroup (Matrix I I ℂ) :=
    Matrix.toMatrixSeminormedAddCommGroup 1 Matrix.PosSemidef.one
  letI : InnerProductSpace ℂ (Matrix I I ℂ) :=
    Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one
  have h := norm_inner_le_norm (𝕜 := ℂ) Aᴴ B
  change ‖(B * 1 * Aᴴᴴ).trace‖ ≤
    Real.sqrt (Aᴴ * 1 * Aᴴᴴ).trace.re * Real.sqrt (B * 1 * Bᴴ).trace.re at h
  simp only [Matrix.mul_one, Matrix.conjTranspose_conjTranspose] at h
  rw [Matrix.trace_mul_comm B A, Matrix.trace_mul_comm Aᴴ A,
    Matrix.trace_mul_comm B Bᴴ] at h
  exact h

private theorem add_conj_eq_twice_re (z : ℂ) :
    z + conj z = ((2 * z.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp <;> ring

def powerFamily {X Y : Matrix I I ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (r : ℝ) (z : ℂ) : Matrix I I ℂ :=
  complexPower hX ((r : ℂ) * z / 2) * complexPower hY ((r : ℂ) * z)

def traceWitness {X Y H : Matrix I I ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hH : H.PosSemidef)
    (U : Matrix I I ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  (complexPower hH (((2 * r : ℝ) : ℂ) - (r : ℂ) * z) * U *
    powerFamily hX hY r z).trace

theorem differentiable_powerFamily {X Y : Matrix I I ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (r : ℝ) :
    Differentiable ℂ (powerFamily hX hY r) := by
  have hXc : Differentiable ℂ (fun z : ℂ =>
      complexPower hX ((r : ℂ) * z / 2)) :=
    (differentiable_complexPower hX).comp
      (((differentiable_const (r : ℂ)).mul differentiable_id).div_const 2)
  have hYc : Differentiable ℂ (fun z : ℂ => complexPower hY ((r : ℂ) * z)) :=
    (differentiable_complexPower hY).comp
      ((differentiable_const (r : ℂ)).mul differentiable_id)
  exact hXc.mul hYc

theorem differentiable_traceWitness {X Y H : Matrix I I ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hH : H.PosSemidef)
    (U : Matrix I I ℂ) (r : ℝ) :
    Differentiable ℂ (traceWitness hX hY hH U r) := by
  have hHc : Differentiable ℂ (fun z : ℂ =>
      complexPower hH (((2 * r : ℝ) : ℂ) - (r : ℂ) * z)) :=
    (differentiable_complexPower hH).comp
      ((differentiable_const ((2 * r : ℝ) : ℂ)).sub
        ((differentiable_const (r : ℂ)).mul differentiable_id))
  exact differentiable_matrixTrace_comp
    ((hHc.mul_const U).mul (differentiable_powerFamily hX hY r))

private theorem norm_mul_le_bounds (A B : Matrix I I ℂ)
    {a b : ℝ} (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) : ‖A * B‖ ≤ a * b :=
  (norm_mul_le A B).trans
    (mul_le_mul hA hB (norm_nonneg B) ((norm_nonneg A).trans hA))

theorem traceWitness_bddAbove {X Y H : Matrix I I ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hH : H.PosSemidef)
    (U : Matrix I I ℂ) (r : ℝ) :
    BddAbove ((norm ∘ traceWitness hX hY hH U r) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  let a := complexPowerStripBound hX |r|
  let b := complexPowerStripBound hY |r|
  let c := complexPowerStripBound hH (3 * |r|)
  let t := ‖(Matrix.traceLinearMap I ℂ ℂ).toContinuousLinearMap‖
  refine ⟨t * (c * ‖U‖ * (a * b)), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz01 : 0 ≤ z.re ∧ z.re ≤ 1 := hz
  have hzabs : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith [hz01.1], hz01.2⟩
  have hrz : |r * z.re| ≤ |r| := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hzabs (abs_nonneg r)
  have hXbound : ‖complexPower hX ((r : ℂ) * z / 2)‖ ≤ a := by
    apply norm_complexPower_le_stripBound hX
    have hre : ((r : ℂ) * z / 2).re = r * z.re / 2 := by simp [Complex.mul_re]
    rw [hre, abs_div]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [abs_nonneg r]
  have hYbound : ‖complexPower hY ((r : ℂ) * z)‖ ≤ b := by
    apply norm_complexPower_le_stripBound hY
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hrz
  have hHbound :
      ‖complexPower hH (((2 * r : ℝ) : ℂ) - (r : ℂ) * z)‖ ≤ c := by
    apply norm_complexPower_le_stripBound hH
    have hre : (((2 * r : ℝ) : ℂ) - (r : ℂ) * z).re = 2 * r - r * z.re := by
      simp [Complex.mul_re]
    rw [hre]
    calc
      |2 * r - r * z.re| ≤ |2 * r| + |r * z.re| := abs_sub _ _
      _ ≤ 3 * |r| := by
        rw [abs_mul (2 : ℝ) r, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith only [hrz]
  apply (norm_matrixTrace_le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact norm_mul_le_bounds _ _
    (norm_mul_le_bounds _ _ hHbound le_rfl)
    (norm_mul_le_bounds _ _ hXbound hYbound)

theorem norm_powerFamily_zero_le {X Y : Matrix I I ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (r : ℝ)
    {z : ℂ} (hz : z.re = 0) : ‖powerFamily hX hY r z‖ ≤ 1 := by
  have hXc : ‖complexPower hX ((r : ℂ) * z / 2)‖ ≤ 1 :=
    norm_complexPower_of_re_eq_zero hX (by simp [Complex.mul_re, hz])
  have hYc : ‖complexPower hY ((r : ℂ) * z)‖ ≤ 1 :=
    norm_complexPower_of_re_eq_zero hY (by simp [Complex.mul_re, hz])
  simpa only [powerFamily, one_mul] using norm_mul_le_bounds _ _ hXc hYc

theorem powerFamily_gram_trace_one {X Y : Matrix I I ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) {r : ℝ} (hr : 0 < r)
    {z : ℂ} (hz : z.re = 1) :
    ((powerFamily hX hY r z)ᴴ * powerFamily hX hY r z).trace =
      (CFC.rpow X r * CFC.rpow Y (2 * r)).trace := by
  let α : ℂ := (r : ℂ) * z / 2
  let β : ℂ := (r : ℂ) * z
  have hα : conj α + α = (r : ℂ) := by
    rw [add_comm, add_conj_eq_twice_re]
    apply Complex.ext <;> simp [α, Complex.mul_re, hz] <;> ring
  have hβ : β + conj β = ((2 * r : ℝ) : ℂ) := by
    rw [add_conj_eq_twice_re]
    apply Complex.ext <;> simp [β, Complex.mul_re, hz] <;> ring
  change ((complexPower hX α * complexPower hY β)ᴴ *
    (complexPower hX α * complexPower hY β)).trace = _
  rw [Matrix.conjTranspose_mul, complexPower_conjTranspose, complexPower_conjTranspose]
  calc
    _ = (complexPower hY (conj β) * complexPower hX (conj α + α) *
        complexPower hY β).trace := by
      rw [complexPower_add]
      simp only [Matrix.mul_assoc]
    _ = (complexPower hY (conj β) * complexPower hX (r : ℂ) *
        complexPower hY β).trace := by rw [hα]
    _ = (complexPower hX (r : ℂ) *
        (complexPower hY β * complexPower hY (conj β))).trace := by
      rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
    _ = (complexPower hX (r : ℂ) * complexPower hY (β + conj β)).trace := by
      rw [complexPower_add]
    _ = _ := by
      rw [hβ, complexPower_real hX hr.ne',
        complexPower_real hY (by linarith : 2 * r ≠ 0)]

theorem trace_product_rpow_nonneg {X Y : Matrix I I ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) {r : ℝ} (hr : 0 < r) :
    0 ≤ (CFC.rpow X r * CFC.rpow Y (2 * r)).trace.re := by
  rw [← powerFamily_gram_trace_one hX hY hr (z := 1) (by simp)]
  exact (Complex.nonneg_iff.mp
    (Matrix.posSemidef_conjTranspose_mul_self (powerFamily hX hY r 1)).trace_nonneg).1

theorem norm_traceWitness_zero_le {X Y H : Matrix I I ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hH : H.PosSemidef)
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z.re = 0) :
    ‖traceWitness hX hY hH U r z‖ ≤ (CFC.rpow H (2 * r)).trace.re := by
  let D := complexPower hH (((2 * r : ℝ) : ℂ) - (r : ℂ) * z)
  have hUF : ‖U * powerFamily hX hY r z‖ ≤ 1 := by
    rw [CStarRing.norm_mem_unitary_mul _ hU]
    exact norm_powerFamily_zero_le hX hY r hz
  have he : (((2 * r : ℝ) : ℂ) - (r : ℂ) * z).re = 2 * r := by
    simp [Complex.mul_re, hz]
  change ‖(D * U * powerFamily hX hY r z).trace‖ ≤ _
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm D]
  calc
    _ ≤ traceNorm D := norm_trace_mul_le_traceNorm _ D hUF
    _ = _ := by
      dsimp only [D]
      rw [traceNorm_complexPower_of_re_pos hH (by rw [he]; linarith), he]

theorem norm_traceWitness_one_le {X Y H : Matrix I I ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hH : H.PosSemidef)
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z.re = 1) :
    ‖traceWitness hX hY hH U r z‖ ≤
      Real.sqrt (CFC.rpow H (2 * r)).trace.re *
        Real.sqrt (CFC.rpow X r * CFC.rpow Y (2 * r)).trace.re := by
  let e : ℂ := ((2 * r : ℝ) : ℂ) - (r : ℂ) * z
  let D := complexPower hH e * U
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have he : e + conj e = ((2 * r : ℝ) : ℂ) := by
    rw [add_conj_eq_twice_re]
    apply Complex.ext <;> simp [e, Complex.mul_re, hz] <;> ring
  have hD : D * Dᴴ = CFC.rpow H (2 * r) := by
    dsimp only [D]
    rw [Matrix.conjTranspose_mul, complexPower_conjTranspose]
    calc
      _ = complexPower hH e * (U * Uᴴ) * complexPower hH (conj e) := by
        simp only [Matrix.mul_assoc]
      _ = complexPower hH (e + conj e) := by
        rw [hU2, Matrix.mul_one, complexPower_add]
      _ = _ := by rw [he, complexPower_real hH (by linarith : 2 * r ≠ 0)]
  have h := norm_trace_mul_le_sqrt_gram D (powerFamily hX hY r z)
  rw [hD, powerFamily_gram_trace_one hX hY hr hz] at h
  exact h

theorem powerFamily_at_reciprocal {X Y : Matrix I I ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) {r : ℝ} (hr : r ≠ 0) :
    powerFamily hX hY r ((1 / r : ℝ) : ℂ) = CFC.sqrt X * Y := by
  have he : (r : ℂ) * ((1 / r : ℝ) : ℂ) = 1 := by
    exact_mod_cast (mul_one_div_cancel hr)
  unfold powerFamily
  rw [he, complexPower_one]
  have hh : (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hsqrt : CFC.sqrt X = CFC.rpow X (1 / 2 : ℝ) := CFC.sqrt_eq_rpow
  rw [hh, complexPower_real hX (by norm_num : (1 / 2 : ℝ) ≠ 0), ← hsqrt]

theorem traceWitness_at_reciprocal {X Y H : Matrix I I ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hH : H.PosSemidef)
    (U : Matrix I I ℂ) {r : ℝ} (hr : 0 < r)
    (hPolar : U * (CFC.sqrt X * Y) = H) :
    traceWitness hX hY hH U r ((1 / r : ℝ) : ℂ) =
      (CFC.rpow H (2 * r)).trace := by
  have he : (r : ℂ) * ((1 / r : ℝ) : ℂ) = 1 := by
    exact_mod_cast (mul_one_div_cancel hr.ne')
  unfold traceWitness
  rw [powerFamily_at_reciprocal hX hY hr.ne', Matrix.mul_assoc, hPolar, he]
  have hsum : ((2 * r : ℝ) : ℂ) - 1 + 1 = ((2 * r : ℝ) : ℂ) := by ring
  calc
    _ = (complexPower hH (((2 * r : ℝ) : ℂ) - 1) * complexPower hH 1).trace := by
      rw [complexPower_one]
    _ = (complexPower hH (((2 * r : ℝ) : ℂ) - 1 + 1)).trace := by
      rw [complexPower_add]
    _ = _ := by rw [hsum, complexPower_real hH (by linarith : 2 * r ≠ 0)]

theorem le_of_two_boundary_interpolation {a b θ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ : 0 < θ)
    (h : a ≤ a ^ (1 - θ) * (Real.sqrt a * Real.sqrt b) ^ θ) : a ≤ b := by
  by_cases haz : a = 0
  · simpa only [haz] using hb
  · have ha0 : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    have hexp : a ^ (1 - θ) * (Real.sqrt a * Real.sqrt b) ^ θ =
        a ^ (1 - θ / 2) * b ^ (θ / 2) := by
      rw [Real.mul_rpow (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),
        Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        ← Real.rpow_mul ha, ← Real.rpow_mul hb, ← mul_assoc,
        ← Real.rpow_add ha0]
      congr 1 <;> congr 1 <;> ring
    rw [hexp] at h
    exact le_of_le_rpow_product ha hb (by linarith : 0 < θ / 2) h

theorem trace_rpow_sandwich_le {X Y : Matrix I I ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) {r : ℝ} (hr : 1 < r) :
    (CFC.rpow (Y * X * Y) r).trace.re ≤
      (CFC.rpow X r * CFC.rpow Y (2 * r)).trace.re := by
  let M := CFC.sqrt X * Y
  let H := CFC.abs M
  have hH : H.PosSemidef := (CFC.abs_nonneg M).posSemidef
  obtain ⟨U, hU, hPolar⟩ := exists_unitary_polar M
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hθ0 : 0 < (1 / r : ℝ) := one_div_pos.mpr hr0
  have hθ1 : (1 / r : ℝ) < 1 := (div_lt_one hr0).mpr hr
  have hθ : ((1 / r : ℝ) : ℂ) ∈
      Complex.HadamardThreeLines.verticalClosedStrip 0 1 := ⟨hθ0.le, hθ1.le⟩
  have ha : 0 ≤ (CFC.rpow H (2 * r)).trace.re :=
    (Complex.nonneg_iff.mp
      (CFC.rpow_nonneg : 0 ≤ CFC.rpow H (2 * r)).posSemidef.trace_nonneg).1
  have hb : 0 ≤ (CFC.rpow X r * CFC.rpow Y (2 * r)).trace.re :=
    trace_product_rpow_nonneg hX hY hr0
  have hbound := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    (traceWitness hX hY hH U r) hθ
    (differentiable_traceWitness hX hY hH U r).diffContOnCl
    (traceWitness_bddAbove hX hY hH U r)
    (fun z hz => norm_traceWitness_zero_le hX hY hH U hU hr0
      (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz))
    (fun z hz => norm_traceWitness_one_le hX hY hH U hU hr0
      (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz))
  have hvalue : ‖traceWitness hX hY hH U r ((1 / r : ℝ) : ℂ)‖ =
      (CFC.rpow H (2 * r)).trace.re := by
    rw [traceWitness_at_reciprocal hX hY hH U hr0 hPolar]
    exact (Complex.re_eq_norm.mpr
      (CFC.rpow_nonneg : 0 ≤ CFC.rpow H (2 * r)).posSemidef.trace_nonneg).symm
  rw [hvalue, Complex.ofReal_re] at hbound
  have hALT := le_of_two_boundary_interpolation ha hb hθ0 hbound
  have hRoot : (CFC.sqrt X)ᴴ = CFC.sqrt X :=
    (CFC.sqrt_nonneg X).posSemidef.1.eq
  have hGram : Mᴴ * M = Y * X * Y := by
    dsimp only [M]
    rw [Matrix.conjTranspose_mul, hY.1.eq, hRoot]
    calc
      _ = Y * (CFC.sqrt X * CFC.sqrt X) * Y := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self X hX.nonneg]
  have hleft : (CFC.rpow H (2 * r)).trace.re =
      (CFC.rpow (Y * X * Y) r).trace.re := by
    change schattenPower (2 * r) M = _
    rw [schattenPower_eq_gram_trace (2 * r) (by linarith) M, hGram]
    congr 2
    ring
  rwa [hleft] at hALT

theorem trace_cfc_rpow_sandwich_le {X Y : Matrix I I ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) {r : ℝ} (hr : 1 < r) :
    (cfc (fun x : ℝ => x ^ r) (Y * X * Y)).trace.re ≤
      (cfc (fun x : ℝ => x ^ r) X * cfc (fun x : ℝ => x ^ (2 * r)) Y).trace.re := by
  have hSandwich : (Y * X * Y).PosSemidef := by
    simpa only [hY.1.eq] using hX.conjTranspose_mul_mul_same Y
  have hs : CFC.rpow (Y * X * Y) r = cfc (fun x : ℝ => x ^ r) (Y * X * Y) :=
    CFC.rpow_eq_cfc_real (a := Y * X * Y) (y := r) hSandwich.nonneg
  have hx : CFC.rpow X r = cfc (fun x : ℝ => x ^ r) X :=
    CFC.rpow_eq_cfc_real (a := X) (y := r) hX.nonneg
  have hy : CFC.rpow Y (2 * r) = cfc (fun x : ℝ => x ^ (2 * r)) Y :=
    CFC.rpow_eq_cfc_real (a := Y) (y := 2 * r) hY.nonneg
  rw [← hs, ← hx, ← hy]
  exact trace_rpow_sandwich_le hX hY hr

end QuantumProver.ArakiLiebThirringTrace
