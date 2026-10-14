import QuantumProver.LinearAlgebra.SandwichedDPI.ComplexPowers
import QuantumProver.LinearAlgebra.SandwichedDPI.TraceNorm

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QuantumProver.SandwichedDPI

open QuantumProver.SuperchannelDiscrimination
open KrausCompletion

variable {I O Z : Type*} [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O] [Fintype Z]

def tiltedKrausAction (K : Z → Matrix O I ℂ) {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) (z : ℂ) (X : Matrix I I ℂ) : Matrix O O ℂ :=
  complexPower (krausAction_posSemidef K hσ) ((z - 1) / 2) *
    krausAction K (complexPower hσ ((1 - z) / 2) * X *
      complexPower hσ ((1 - z) / 2)) *
    complexPower (krausAction_posSemidef K hσ) ((z - 1) / 2)

def analyticTraceWitness (K : Z → Matrix O I ℂ) {σ A : Matrix I I ℂ}
    {B : Matrix O O ℂ} (hσ : σ.PosSemidef) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (U : Matrix I I ℂ) (V : Matrix O O ℂ)
    (p q : ℝ) (z : ℂ) : ℂ :=
  (complexPower hB ((q : ℂ) * (1 - z)) * V *
    tiltedKrausAction K hσ z (U * complexPower hA ((p : ℂ) * z))).trace

theorem norm_complexPower_of_re_eq_zero {S : Type*} [Fintype S] [DecidableEq S]
    {A : Matrix S S ℂ} (hA : A.PosSemidef) {z : ℂ} (hz : z.re = 0) :
    ‖complexPower hA z‖ ≤ 1 := by
  have he : z = Complex.I * (z.im : ℂ) := by
    apply Complex.ext <;> simp [hz]
  rw [he]
  exact norm_complexPower_imaginary_le_one hA z.im

theorem traceNorm_complexPower_of_re_pos {S : Type*} [Fintype S] [DecidableEq S]
    {A : Matrix S S ℂ} (hA : A.PosSemidef) {z : ℂ} (hz : 0 < z.re) :
    traceNorm (complexPower hA z) = (CFC.rpow A z.re).trace.re := by
  unfold traceNorm
  rw [abs_complexPower_of_re_pos hA hz]

private theorem norm_mul_left_contraction {S : Type*} [Fintype S] [DecidableEq S]
    (D X : Matrix S S ℂ) (hD : ‖D‖ ≤ 1) : ‖D * X‖ ≤ ‖X‖ := by
  calc
    ‖D * X‖ ≤ ‖D‖ * ‖X‖ := norm_mul_le _ _
    _ ≤ 1 * ‖X‖ := mul_le_mul_of_nonneg_right hD (norm_nonneg _)
    _ = ‖X‖ := one_mul _

private theorem norm_mul_right_contraction {S : Type*} [Fintype S] [DecidableEq S]
    (X D : Matrix S S ℂ) (hD : ‖D‖ ≤ 1) : ‖X * D‖ ≤ ‖X‖ := by
  calc
    ‖X * D‖ ≤ ‖X‖ * ‖D‖ := norm_mul_le _ _
    _ ≤ ‖X‖ * 1 := mul_le_mul_of_nonneg_left hD (norm_nonneg _)
    _ = ‖X‖ := mul_one _

private theorem norm_sandwich_contraction {S : Type*} [Fintype S] [DecidableEq S]
    (D X : Matrix S S ℂ) (hD : ‖D‖ ≤ 1) : ‖D * X * D‖ ≤ ‖X‖ :=
  (norm_mul_right_contraction (D * X) D hD).trans
    (norm_mul_left_contraction D X hD)

private theorem complexPower_sub_one_half {S : Type*} [Fintype S] [DecidableEq S]
    {A : Matrix S S ℂ} (hA : A.PosSemidef) (z : ℂ) :
    complexPower hA ((z - 1) / 2) =
      complexPower hA (z / 2) * CFC.rpow A (-1 / 2 : ℝ) := by
  calc
    complexPower hA ((z - 1) / 2) =
        complexPower hA (z / 2 + ((-1 / 2 : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    _ = complexPower hA (z / 2) * complexPower hA ((-1 / 2 : ℝ) : ℂ) :=
      complexPower_add hA _ _
    _ = _ := by rw [complexPower_real hA (by norm_num : (-1 / 2 : ℝ) ≠ 0)]

private theorem complexPower_sub_one_half_right {S : Type*}
    [Fintype S] [DecidableEq S] {A : Matrix S S ℂ} (hA : A.PosSemidef) (z : ℂ) :
    complexPower hA ((z - 1) / 2) =
      CFC.rpow A (-1 / 2 : ℝ) * complexPower hA (z / 2) := by
  rw [complexPower_sub_one_half hA z,
    ← complexPower_real hA (by norm_num : (-1 / 2 : ℝ) ≠ 0)]
  exact complexPower_mul_comm hA _ _

private theorem complexPower_one_sub_half {S : Type*} [Fintype S] [DecidableEq S]
    {A : Matrix S S ℂ} (hA : A.PosSemidef) (z : ℂ) :
    complexPower hA ((1 - z) / 2) = CFC.sqrt A * complexPower hA (-z / 2) := by
  calc
    complexPower hA ((1 - z) / 2) =
        complexPower hA (((1 / 2 : ℝ) : ℂ) + -z / 2) := by
      congr 1
      push_cast
      ring
    _ = complexPower hA ((1 / 2 : ℝ) : ℂ) * complexPower hA (-z / 2) :=
      complexPower_add hA _ _
    _ = _ := by
      have hroot : CFC.sqrt A = CFC.rpow A (1 / 2 : ℝ) := CFC.sqrt_eq_rpow
      rw [complexPower_real hA (by norm_num : (1 / 2 : ℝ) ≠ 0), hroot]

private theorem complexPower_one_sub_half_right {S : Type*}
    [Fintype S] [DecidableEq S] {A : Matrix S S ℂ} (hA : A.PosSemidef) (z : ℂ) :
    complexPower hA ((1 - z) / 2) = complexPower hA (-z / 2) * CFC.sqrt A := by
  have hroot : CFC.sqrt A = CFC.rpow A (1 / 2 : ℝ) := CFC.sqrt_eq_rpow
  rw [complexPower_one_sub_half hA z, hroot,
    ← complexPower_real hA (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  exact complexPower_mul_comm hA _ _

theorem tiltedKrausAction_eq_normalized (K : Z → Matrix O I ℂ)
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) (z : ℂ) (X : Matrix I I ℂ) :
    tiltedKrausAction K hσ z X =
      complexPower (krausAction_posSemidef K hσ) (z / 2) *
        krausAction (normalizedKraus K σ)
          (complexPower hσ (-z / 2) * X * complexPower hσ (-z / 2)) *
        complexPower (krausAction_posSemidef K hσ) (z / 2) := by
  rw [tiltedKrausAction, normalizedKraus_action]
  nth_rewrite 1 [complexPower_sub_one_half (krausAction_posSemidef K hσ) z]
  nth_rewrite 1 [complexPower_sub_one_half_right (krausAction_posSemidef K hσ) z]
  nth_rewrite 1 [complexPower_one_sub_half hσ z]
  nth_rewrite 1 [complexPower_one_sub_half_right hσ z]
  simp only [Matrix.mul_assoc]

theorem norm_tiltedKrausAction_zero_le (K : Z → Matrix O I ℂ)
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) {z : ℂ} (hz : z.re = 0)
    (X : Matrix I I ℂ) : ‖tiltedKrausAction K hσ z X‖ ≤ ‖X‖ := by
  have hout : ‖complexPower (krausAction_posSemidef K hσ) (z / 2)‖ ≤ 1 :=
    norm_complexPower_of_re_eq_zero _ (by simp [hz])
  have hin : ‖complexPower hσ (-z / 2)‖ ≤ 1 :=
    norm_complexPower_of_re_eq_zero _ (by simp [hz])
  rw [tiltedKrausAction_eq_normalized]
  exact (norm_sandwich_contraction _ _ hout).trans
    ((norm_normalizedKraus_action_le K hσ _).trans
      (norm_sandwich_contraction _ X hin))

theorem traceNorm_tiltedKrausAction_one_le (K : Z → Matrix O I ℂ)
    (hK : krausGram K = 1) {σ : Matrix I I ℂ} (hσ : σ.PosSemidef)
    {z : ℂ} (hz : z.re = 1) (X : Matrix I I ℂ) :
    traceNorm (tiltedKrausAction K hσ z X) ≤ traceNorm X := by
  let D := complexPower (krausAction_posSemidef K hσ) ((z - 1) / 2)
  let E := complexPower hσ ((1 - z) / 2)
  have hD : ‖D‖ ≤ 1 :=
    norm_complexPower_of_re_eq_zero _ (by simp [hz])
  have hE : ‖E‖ ≤ 1 :=
    norm_complexPower_of_re_eq_zero _ (by simp [hz])
  change traceNorm (D * krausAction K (E * X * E) * D) ≤ traceNorm X
  calc
    traceNorm (D * krausAction K (E * X * E) * D) ≤
        traceNorm (D * krausAction K (E * X * E)) := traceNorm_mul_right_le _ D hD
    _ ≤ traceNorm (krausAction K (E * X * E)) := traceNorm_mul_left_le D _ hD
    _ ≤ traceNorm (E * X * E) := traceNorm_krausAction_le K hK _
    _ ≤ traceNorm (E * X) := traceNorm_mul_right_le _ E hE
    _ ≤ traceNorm X := traceNorm_mul_left_le E X hE

theorem norm_analyticTraceWitness_zero_le (K : Z → Matrix O I ℂ)
    {σ A : Matrix I I ℂ} {B : Matrix O O ℂ}
    (hσ : σ.PosSemidef) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (U : Matrix I I ℂ) (V : Matrix O O ℂ) (p q : ℝ)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (_hp : 0 < p) (hq : 0 < q)
    {z : ℂ} (hz : z.re = 0) :
    ‖analyticTraceWitness K hσ hA hB U V p q z‖ ≤ (CFC.rpow B q).trace.re := by
  let D := complexPower hB ((q : ℂ) * (1 - z))
  let X := U * complexPower hA ((p : ℂ) * z)
  let T := tiltedKrausAction K hσ z X
  have hAp : ‖complexPower hA ((p : ℂ) * z)‖ ≤ 1 :=
    norm_complexPower_of_re_eq_zero _ (by simp [Complex.mul_re, hz])
  have hX : ‖X‖ ≤ 1 := (norm_mul_left_contraction U _ hU).trans hAp
  have hT : ‖T‖ ≤ 1 := (norm_tiltedKrausAction_zero_le K hσ hz X).trans hX
  have hVT : ‖V * T‖ ≤ 1 := (norm_mul_left_contraction V T hV).trans hT
  have hqz : ((q : ℂ) * (1 - z)).re = q := by simp [Complex.mul_re, hz]
  change ‖(D * V * T).trace‖ ≤ _
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm D (V * T)]
  calc
    ‖(V * T * D).trace‖ ≤ traceNorm D := norm_trace_mul_le_traceNorm _ D hVT
    _ = (CFC.rpow B q).trace.re := by
      dsimp only [D]
      rw [traceNorm_complexPower_of_re_pos hB (by rw [hqz]; exact hq), hqz]

theorem norm_analyticTraceWitness_one_le (K : Z → Matrix O I ℂ)
    (hK : krausGram K = 1) {σ A : Matrix I I ℂ} {B : Matrix O O ℂ}
    (hσ : σ.PosSemidef) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (U : Matrix I I ℂ) (V : Matrix O O ℂ) (p q : ℝ)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (hp : 0 < p) (_hq : 0 < q)
    {z : ℂ} (hz : z.re = 1) :
    ‖analyticTraceWitness K hσ hA hB U V p q z‖ ≤ (CFC.rpow A p).trace.re := by
  let D := complexPower hB ((q : ℂ) * (1 - z))
  let X := U * complexPower hA ((p : ℂ) * z)
  let T := tiltedKrausAction K hσ z X
  have hD : ‖D‖ ≤ 1 :=
    norm_complexPower_of_re_eq_zero _ (by simp [Complex.mul_re, hz])
  have hDV : ‖D * V‖ ≤ 1 := (norm_mul_left_contraction D V hD).trans hV
  have hpz : ((p : ℂ) * z).re = p := by simp [Complex.mul_re, hz]
  change ‖(D * V * T).trace‖ ≤ _
  calc
    ‖(D * V * T).trace‖ ≤ traceNorm T := norm_trace_mul_le_traceNorm _ T hDV
    _ ≤ traceNorm X := traceNorm_tiltedKrausAction_one_le K hK hσ hz X
    _ ≤ traceNorm (complexPower hA ((p : ℂ) * z)) := traceNorm_mul_left_le U _ hU
    _ = (CFC.rpow A p).trace.re := by
      rw [traceNorm_complexPower_of_re_pos hA (by rw [hpz]; exact hp), hpz]

end QuantumProver.SandwichedDPI
