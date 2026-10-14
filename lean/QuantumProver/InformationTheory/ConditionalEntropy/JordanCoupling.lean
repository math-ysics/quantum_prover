import QuantumProver.InformationTheory.SuperchannelDiscrimination.QuantumTestingPowerBound

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open QuantumProver.SuperchannelDiscrimination

namespace QuantumProver.ConditionalEntropy.JordanCoupling

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev halfDistance (ρ σ : Matrix I I ℂ) : ℝ :=
  EffectPerturbation.traceNorm (ρ - σ) / 2

theorem halfDistance_nonneg (ρ σ : Matrix I I ℂ) : 0 ≤ halfDistance ρ σ :=
  div_nonneg (EffectPerturbation.traceNorm_nonneg _) (by norm_num)

theorem posSemidef_trace_eq_real {X : Matrix I I ℂ} (hX : X.PosSemidef)
    {t : ℝ} (hTrace : X.trace.re = t) : X.trace = (t : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using hTrace
  · simpa only [Complex.ofReal_im] using
      (Complex.nonneg_iff.mp hX.trace_nonneg).2.symm

theorem density_jordan_trace_re {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ) :
    (ρ - σ)⁺.trace.re = halfDistance ρ σ ∧
      (ρ - σ)⁻.trace.re = halfDistance ρ σ := by
  have hH := hρ.1.isHermitian.sub hσ.1.isHermitian
  have hSum := EffectPerturbation.traceNorm_eq_jordan hH
  have hDiff := EffectPerturbation.trace_eq_jordan hH
  have hZero : (ρ - σ).trace.re = 0 := by
    simp only [Matrix.trace_sub, hρ.2, hσ.2, sub_self, Complex.zero_re]
  dsimp only [halfDistance]
  constructor <;> linarith

theorem density_jordan_traces {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ) :
    (ρ - σ)⁺.trace = (halfDistance ρ σ : ℂ) ∧
      (ρ - σ)⁻.trace = (halfDistance ρ σ : ℂ) := by
  have hMass := density_jordan_trace_re hρ hσ
  exact ⟨posSemidef_trace_eq_real (CFC.posPart_nonneg _).posSemidef hMass.1,
    posSemidef_trace_eq_real (CFC.negPart_nonneg _).posSemidef hMass.2⟩

theorem density_halfDistance_le_one {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ) :
    halfDistance ρ σ ≤ 1 := by
  have h := EffectPerturbation.traceNorm_sub_le_traces hρ.1 hσ.1
  simp only [hρ.2, hσ.2, Complex.one_re] at h
  dsimp only [halfDistance]
  linarith

theorem density_halfDistance_eq_zero_iff {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ) :
    halfDistance ρ σ = 0 ↔ ρ = σ := by
  constructor
  · intro hZero
    have hMass := density_jordan_traces hρ hσ
    have hPos : (ρ - σ)⁺ = 0 :=
      (CFC.posPart_nonneg (ρ - σ)).posSemidef.trace_eq_zero_iff.mp
        (by simpa only [hZero, Complex.ofReal_zero] using hMass.1)
    have hNeg : (ρ - σ)⁻ = 0 :=
      (CFC.negPart_nonneg (ρ - σ)).posSemidef.trace_eq_zero_iff.mp
        (by simpa only [hZero, Complex.ofReal_zero] using hMass.2)
    have hJordan := CFC.posPart_sub_negPart (ρ - σ)
      (hρ.1.isHermitian.sub hσ.1.isHermitian).isSelfAdjoint
    have hDifference : ρ - σ = 0 := by
      simpa only [hPos, hNeg, sub_zero] using hJordan.symm
    exact sub_eq_zero.mp hDifference
  · rintro rfl
    simp [halfDistance, EffectPerturbation.traceNorm]

theorem commonUpper_eq_left_add_negPart {ρ σ : Matrix I I ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    QuantumTestingPowerBound.commonUpper ρ σ = ρ + (ρ - σ)⁻ := by
  unfold QuantumTestingPowerBound.commonUpper
  calc
    σ + (ρ - σ)⁺ = ((ρ - σ)⁺ - (ρ - σ)⁻) + σ + (ρ - σ)⁻ := by abel
    _ = ρ + (ρ - σ)⁻ := by
      rw [CFC.posPart_sub_negPart (ρ - σ) (hρ.sub hσ).isSelfAdjoint]
      abel

def paddedCommon (ρ σ : Matrix I I ℂ) (ε : ℝ) : Matrix I I ℂ :=
  QuantumTestingPowerBound.commonUpper ρ σ + (ε - halfDistance ρ σ) • σ

def plusRemainder (ρ σ : Matrix I I ℂ) (ε : ℝ) : Matrix I I ℂ :=
  (ρ - σ)⁺ + (ε - halfDistance ρ σ) • σ

def minusRemainder (ρ σ : Matrix I I ℂ) (ε : ℝ) : Matrix I I ℂ :=
  (ρ - σ)⁻ + (ε - halfDistance ρ σ) • σ

theorem paddedCommon_eq_sigma_add_plus (ρ σ : Matrix I I ℂ) (ε : ℝ) :
    paddedCommon ρ σ ε = σ + plusRemainder ρ σ ε := by
  simp only [paddedCommon, plusRemainder, QuantumTestingPowerBound.commonUpper,
    add_assoc]

theorem paddedCommon_eq_rho_add_minus {ρ σ : Matrix I I ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (ε : ℝ) :
    paddedCommon ρ σ ε = ρ + minusRemainder ρ σ ε := by
  simp only [paddedCommon, minusRemainder, commonUpper_eq_left_add_negPart hρ hσ,
    add_assoc]

theorem paddedCommon_posSemidef {ρ σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) {ε : ℝ} (hε : halfDistance ρ σ ≤ ε) :
    (paddedCommon ρ σ ε).PosSemidef :=
  (QuantumTestingPowerBound.commonUpper_posSemidef hσ).add
    (hσ.smul (sub_nonneg.mpr hε))

theorem remainder_posSemidef {ρ σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) {ε : ℝ} (hε : halfDistance ρ σ ≤ ε) :
    (plusRemainder ρ σ ε).PosSemidef ∧ (minusRemainder ρ σ ε).PosSemidef :=
  ⟨(CFC.posPart_nonneg _).posSemidef.add (hσ.smul (sub_nonneg.mpr hε)),
    (CFC.negPart_nonneg _).posSemidef.add (hσ.smul (sub_nonneg.mpr hε))⟩

theorem remainder_trace_re {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ) (ε : ℝ) :
    (plusRemainder ρ σ ε).trace.re = ε ∧
      (minusRemainder ρ σ ε).trace.re = ε := by
  have hMass := density_jordan_trace_re hρ hσ
  constructor
  · simp only [plusRemainder, Matrix.trace_add, Complex.add_re, Matrix.trace_smul,
      Complex.smul_re, smul_eq_mul, hσ.2, Complex.one_re, mul_one, hMass.1]
    ring
  · simp only [minusRemainder, Matrix.trace_add, Complex.add_re, Matrix.trace_smul,
      Complex.smul_re, smul_eq_mul, hσ.2, Complex.one_re, mul_one, hMass.2]
    ring

theorem paddedCommon_trace_re {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ) (ε : ℝ) :
    (paddedCommon ρ σ ε).trace.re = 1 + ε := by
  rw [paddedCommon_eq_sigma_add_plus, Matrix.trace_add, Complex.add_re,
    hσ.2, Complex.one_re, (remainder_trace_re hρ hσ ε).1]

def normalizedRemainder (fallback X : Matrix I I ℂ) (ε : ℝ) : Matrix I I ℂ :=
  if ε = 0 then fallback else ε⁻¹ • X

theorem normalizedRemainder_isDensity {fallback X : Matrix I I ℂ}
    (hFallback : FlaggedStates.IsDensity fallback) (hX : X.PosSemidef)
    {ε : ℝ} (hε : 0 ≤ ε) (hTrace : X.trace.re = ε) :
    FlaggedStates.IsDensity (normalizedRemainder fallback X ε) := by
  by_cases hZero : ε = 0
  · simpa only [normalizedRemainder, if_pos hZero] using hFallback
  · have hPSD : (ε⁻¹ • X).PosSemidef := hX.smul (inv_nonneg.mpr hε)
    have hMass : (ε⁻¹ • X).trace.re = 1 := by
      simp only [Matrix.trace_smul, Complex.smul_re, smul_eq_mul, hTrace,
        inv_mul_cancel₀ hZero]
    simpa only [normalizedRemainder, if_neg hZero, Complex.ofReal_one] using
      (show FlaggedStates.IsDensity (ε⁻¹ • X) from
        ⟨hPSD, posSemidef_trace_eq_real hPSD hMass⟩)

theorem normalizedRemainder_scaled {fallback X : Matrix I I ℂ}
    (hX : X.PosSemidef) {ε : ℝ} (hTrace : X.trace.re = ε) :
    ε • normalizedRemainder fallback X ε = X := by
  by_cases hZero : ε = 0
  · have hXZero : X = 0 := hX.trace_eq_zero_iff.mp
      (by simpa only [hZero, Complex.ofReal_zero] using posSemidef_trace_eq_real hX hTrace)
    simp only [hZero, zero_smul, hXZero]
  · simp only [normalizedRemainder, if_neg hZero, smul_smul,
      mul_inv_cancel₀ hZero, one_smul]

theorem coupling_weights {ε : ℝ} (hε : 0 ≤ ε) :
    0 < 1 / (1 + ε) ∧ 1 / (1 + ε) ≤ 1 ∧
      0 ≤ ε / (1 + ε) ∧ ε / (1 + ε) < 1 ∧
      1 / (1 + ε) + ε / (1 + ε) = 1 ∧
      1 - ε / (1 + ε) = 1 / (1 + ε) := by
  have hDen : 0 < 1 + ε := by linarith
  have hBase : 0 < 1 / (1 + ε) := div_pos (by norm_num) hDen
  have hNoise : 0 ≤ ε / (1 + ε) := div_nonneg hε hDen.le
  have hSum : 1 / (1 + ε) + ε / (1 + ε) = 1 := by
    rw [← add_div, div_self (ne_of_gt hDen)]
  exact ⟨hBase, by linarith, hNoise, by linarith, hSum, by linarith⟩

theorem coupling_noise_le_half {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε / (1 + ε) ≤ 1 / 2 := by
  apply (div_le_iff₀ (show 0 < 1 + ε by linarith)).mpr
  linarith

theorem exists_common_density_coupling {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    {ε : ℝ} (hε : halfDistance ρ σ ≤ ε) :
    ∃ ω τPlus τMinus : Matrix I I ℂ,
      FlaggedStates.IsDensity ω ∧ FlaggedStates.IsDensity τPlus ∧
      FlaggedStates.IsDensity τMinus ∧
      ω = (1 / (1 + ε)) • σ + (ε / (1 + ε)) • τPlus ∧
      ω = (1 / (1 + ε)) • ρ + (ε / (1 + ε)) • τMinus := by
  have hε0 : 0 ≤ ε := (halfDistance_nonneg ρ σ).trans hε
  have hDen : 0 < 1 + ε := by linarith
  let C := paddedCommon ρ σ ε
  let τPlus := normalizedRemainder σ (plusRemainder ρ σ ε) ε
  let τMinus := normalizedRemainder σ (minusRemainder ρ σ ε) ε
  let ω := (1 / (1 + ε)) • C
  have hRemainder := remainder_posSemidef hσ.1 hε
  have hMass := remainder_trace_re hρ hσ ε
  have hPlus : FlaggedStates.IsDensity τPlus :=
    normalizedRemainder_isDensity hσ hRemainder.1 hε0 hMass.1
  have hMinus : FlaggedStates.IsDensity τMinus :=
    normalizedRemainder_isDensity hσ hRemainder.2 hε0 hMass.2
  have hC : C.PosSemidef := paddedCommon_posSemidef hσ.1 hε
  have hω : ω.PosSemidef := hC.smul (div_nonneg (by norm_num) hDen.le)
  have hωMass : ω.trace.re = 1 := by
    dsimp only [ω, C]
    simp only [Matrix.trace_smul, Complex.smul_re, smul_eq_mul,
      paddedCommon_trace_re hρ hσ ε, one_div, inv_mul_cancel₀ (ne_of_gt hDen)]
  have hPlusScaled : ε • τPlus = plusRemainder ρ σ ε :=
    normalizedRemainder_scaled hRemainder.1 hMass.1
  have hMinusScaled : ε • τMinus = minusRemainder ρ σ ε :=
    normalizedRemainder_scaled hRemainder.2 hMass.2
  have hCoeff : (1 / (1 + ε)) * ε = ε / (1 + ε) := by ring
  refine ⟨ω, τPlus, τMinus, ⟨hω, posSemidef_trace_eq_real hω hωMass⟩,
    hPlus, hMinus, ?_, ?_⟩
  · calc
      ω = (1 / (1 + ε)) • (σ + plusRemainder ρ σ ε) :=
        congrArg (fun X : Matrix I I ℂ => (1 / (1 + ε)) • X)
          (paddedCommon_eq_sigma_add_plus ρ σ ε)
      _ = (1 / (1 + ε)) • σ + (ε / (1 + ε)) • τPlus := by
        rw [smul_add, ← hPlusScaled, smul_smul, hCoeff]
  · calc
      ω = (1 / (1 + ε)) • (ρ + minusRemainder ρ σ ε) :=
        congrArg (fun X : Matrix I I ℂ => (1 / (1 + ε)) • X)
          (paddedCommon_eq_rho_add_minus hρ.1.isHermitian hσ.1.isHermitian ε)
      _ = (1 / (1 + ε)) • ρ + (ε / (1 + ε)) • τMinus := by
        rw [smul_add, ← hMinusScaled, smul_smul, hCoeff]

end QuantumProver.ConditionalEntropy.JordanCoupling
