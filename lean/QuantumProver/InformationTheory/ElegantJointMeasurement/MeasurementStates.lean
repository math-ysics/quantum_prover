import Mathlib

open scoped BigOperators ComplexConjugate

namespace QuantumProver.ElegantJointMeasurement.States

noncomputable section

def amplitudeScale : ℝ := 1 / (2 * Real.sqrt 2)

def ejmNumerator (u v w : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(u : ℂ) + Complex.I * (v : ℂ), 1 + (w : ℂ);
     -1 + (w : ℂ), (u : ℂ) + Complex.I * (v : ℂ)]

def ejmCoefficient (u v w : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (amplitudeScale : ℂ) • ejmNumerator u v w

def coefficientInner (E F : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2, conj (E i j) * F i j

def frobeniusNormSq (E : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, Complex.normSq (E i j)

theorem amplitudeScale_sq : amplitudeScale ^ 2 = (1 / 8 : ℝ) := by
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  unfold amplitudeScale
  field_simp [hne]
  nlinarith [hsq]

theorem det_ejmNumerator (u v w : ℝ) :
    Matrix.det (ejmNumerator u v w) =
      1 - (u : ℂ) ^ 2 - (v : ℂ) ^ 2 - (w : ℂ) ^ 2 := by
  calc
    Matrix.det (ejmNumerator u v w) =
        1 - (u : ℂ) ^ 2 + Complex.I ^ 2 * (v : ℂ) ^ 2 - (w : ℂ) ^ 2 := by
      rw [ejmNumerator, Matrix.det_fin_two_of]
      ring
    _ = 1 - (u : ℂ) ^ 2 - (v : ℂ) ^ 2 - (w : ℂ) ^ 2 := by
      rw [Complex.I_sq]
      ring

theorem det_ejmCoefficient (u v w : ℝ) (hsphere : u ^ 2 + v ^ 2 + w ^ 2 = 3) :
    Matrix.det (ejmCoefficient u v w) = (-1 / 4 : ℂ) := by
  have hn : Matrix.det (ejmNumerator u v w) = (-2 : ℂ) := by
    rw [det_ejmNumerator]
    calc
      1 - (u : ℂ) ^ 2 - (v : ℂ) ^ 2 - (w : ℂ) ^ 2 =
          (1 : ℂ) - ((u ^ 2 + v ^ 2 + w ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
      _ = -2 := by rw [hsphere]; norm_num
  rw [ejmCoefficient, Matrix.det_smul, Fintype.card_fin, hn,
    ← Complex.ofReal_pow, amplitudeScale_sq]
  norm_num

theorem norm_det_ejmCoefficient (u v w : ℝ) (hsphere : u ^ 2 + v ^ 2 + w ^ 2 = 3) :
    ‖Matrix.det (ejmCoefficient u v w)‖ = (1 / 4 : ℝ) := by
  rw [det_ejmCoefficient u v w hsphere]
  norm_num [norm_div]

theorem ejmNumerator_inner (u v w u' v' w' : ℝ) :
    coefficientInner (ejmNumerator u v w) (ejmNumerator u' v' w') =
      ((2 * (1 + u * u' + v * v' + w * w') : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [coefficientInner, ejmNumerator, Fin.sum_univ_two]
    ring
  · simp [coefficientInner, ejmNumerator, Fin.sum_univ_two]
    ring

theorem coefficientInner_smul (E F : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) :
    coefficientInner (a • E) (b • F) = conj a * b * coefficientInner E F := by
  simp only [coefficientInner, Matrix.smul_apply, smul_eq_mul, map_mul]
  calc
    ∑ i : Fin 2, ∑ j : Fin 2, conj a * conj (E i j) * (b * F i j) =
        ∑ i : Fin 2, ∑ j : Fin 2, (conj a * b) * (conj (E i j) * F i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = conj a * b * (∑ i : Fin 2, ∑ j : Fin 2, conj (E i j) * F i j) := by
      simp only [Finset.mul_sum]

theorem ejmCoefficient_inner (u v w u' v' w' : ℝ) :
    coefficientInner (ejmCoefficient u v w) (ejmCoefficient u' v' w') =
      (((1 + u * u' + v * v' + w * w') / 4 : ℝ) : ℂ) := by
  have hconj : conj (amplitudeScale : ℂ) = (amplitudeScale : ℂ) := by simp
  have hscale : conj (amplitudeScale : ℂ) * (amplitudeScale : ℂ) =
      ((1 / 8 : ℝ) : ℂ) := by
    rw [hconj, ← sq, ← Complex.ofReal_pow, amplitudeScale_sq]
  rw [ejmCoefficient, ejmCoefficient, coefficientInner_smul,
    ejmNumerator_inner, hscale]
  push_cast
  ring

theorem coefficientInner_self (E : Matrix (Fin 2) (Fin 2) ℂ) :
    coefficientInner E E = (frobeniusNormSq E : ℂ) := by
  simp only [coefficientInner, frobeniusNormSq, Complex.conj_mul',
    Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  push_cast
  rfl

theorem frobeniusNormSq_ejmCoefficient (u v w : ℝ)
    (hsphere : u ^ 2 + v ^ 2 + w ^ 2 = 3) :
    frobeniusNormSq (ejmCoefficient u v w) = 1 := by
  have hfour : 1 + u * u + v * v + w * w = 4 := by nlinarith [hsphere]
  have hinner : coefficientInner (ejmCoefficient u v w) (ejmCoefficient u v w) = 1 := by
    rw [ejmCoefficient_inner, hfour]
    norm_num
  apply Complex.ofReal_injective
  rw [← coefficientInner_self]
  simpa only [Complex.ofReal_one] using hinner

def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def singletCoefficient : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • !![0, 1; -1, 0]

def ejmFromPauli (u v w : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    ((u / 2 : ℝ) : ℂ) • pauliX + ((v / 2 : ℝ) : ℂ) • pauliY +
    ((w / 2 : ℝ) : ℂ) • pauliZ) * singletCoefficient

theorem ejmFromPauli_eq (u v w : ℝ) : ejmFromPauli u v w = ejmCoefficient u v w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ejmFromPauli, ejmCoefficient, ejmNumerator, amplitudeScale,
      pauliX, pauliY, pauliZ, singletCoefficient, Matrix.mul_apply,
      Fin.sum_univ_two, div_eq_mul_inv, mul_inv_rev] <;> ring

end

end QuantumProver.ElegantJointMeasurement.States
