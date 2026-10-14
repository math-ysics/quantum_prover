import QuantumProver.LinearAlgebra.SandwichedDPI.EndpointBounds
import QuantumProver.LinearAlgebra.SandwichedDPI.RpowSupport

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QuantumProver.SandwichedDPI

open QuantumProver.AmplitudeDamping.FiniteModel
open QuantumProver.SuperchannelDiscrimination
open KrausCompletion

variable {I O Z : Type*} [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O] [Fintype Z]

theorem tiltedKrausAction_ofReal (K : Z → Matrix O I ℂ)
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) {θ : ℝ}
    (_hθ0 : 0 < θ) (hθ1 : θ < 1) (X : Matrix I I ℂ) :
    tiltedKrausAction K hσ (θ : ℂ) X =
      CFC.rpow (krausAction K σ) ((θ - 1) / 2) *
        krausAction K (CFC.rpow σ ((1 - θ) / 2) * X *
          CFC.rpow σ ((1 - θ) / 2)) *
        CFC.rpow (krausAction K σ) ((θ - 1) / 2) := by
  have hinput : complexPower hσ ((1 - (θ : ℂ)) / 2) =
      CFC.rpow σ ((1 - θ) / 2) := by
    have he : (1 - (θ : ℂ)) / 2 = (((1 - θ) / 2 : ℝ) : ℂ) := by
      push_cast <;> rfl
    rw [he, complexPower_real hσ
      (ne_of_gt (div_pos (sub_pos.mpr hθ1) (by norm_num)))]
  have houtput : complexPower (krausAction_posSemidef K hσ) (((θ : ℂ) - 1) / 2) =
      CFC.rpow (krausAction K σ) ((θ - 1) / 2) := by
    have he : ((θ : ℂ) - 1) / 2 = (((θ - 1) / 2 : ℝ) : ℂ) := by
      push_cast <;> rfl
    rw [he, complexPower_real (krausAction_posSemidef K hσ)
      (ne_of_lt (div_neg_of_neg_of_pos (sub_neg.mpr hθ1) (by norm_num)))]
  unfold tiltedKrausAction
  rw [hinput, houtput]

theorem tiltedKrausAction_ofReal_posSemidef (K : Z → Matrix O I ℂ)
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) {X : Matrix I I ℂ} (hX : X.PosSemidef) :
    (tiltedKrausAction K hσ (θ : ℂ) X).PosSemidef := by
  rw [tiltedKrausAction_ofReal K hσ hθ0 hθ1 X]
  have hE : (CFC.rpow σ ((1 - θ) / 2)).IsHermitian :=
    (CFC.rpow_nonneg : 0 ≤ CFC.rpow σ ((1 - θ) / 2)).posSemidef.1
  have hinput : (CFC.rpow σ ((1 - θ) / 2) * X *
      CFC.rpow σ ((1 - θ) / 2)).PosSemidef := by
    simpa only [hE.eq] using hX.conjTranspose_mul_mul_same (CFC.rpow σ ((1 - θ) / 2))
  have hD : (CFC.rpow (krausAction K σ) ((θ - 1) / 2)).IsHermitian :=
    (CFC.rpow_nonneg : 0 ≤ CFC.rpow (krausAction K σ) ((θ - 1) / 2)).posSemidef.1
  simpa only [hD.eq] using
    (krausAction_posSemidef K hinput).conjTranspose_mul_mul_same
      (CFC.rpow (krausAction K σ) ((θ - 1) / 2))

theorem tiltedKrausAction_sandwichedInput (K : Z → Matrix O I ℂ)
    {ρ σ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : SupportLE ρ σ) {p : ℝ} (hp : 1 < p) :
    tiltedKrausAction K hσ ((1 / p : ℝ) : ℂ)
        (CFC.rpow σ ((1 - p) / (2 * p)) * ρ * CFC.rpow σ ((1 - p) / (2 * p))) =
      CFC.rpow (krausAction K σ) ((1 - p) / (2 * p)) *
        krausAction K ρ * CFC.rpow (krausAction K σ) ((1 - p) / (2 * p)) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpne : p ≠ 0 := hp0.ne'
  have hθ0 : 0 < (1 / p : ℝ) := one_div_pos.mpr hp0
  have hθ1 : (1 / p : ℝ) < 1 :=
    (div_lt_iff₀ hp0).mpr (by simpa only [one_mul] using hp)
  have houtput : ((1 / p - 1) / 2 : ℝ) = (1 - p) / (2 * p) := by
    field_simp [hpne] <;> ring
  have hinput : ((1 - 1 / p) / 2 : ℝ) = -((1 - p) / (2 * p)) := by
    field_simp [hpne] <;> ring
  have hr : (1 - p) / (2 * p) ≠ 0 :=
    ne_of_lt (div_neg_of_neg_of_pos (sub_neg.mpr hp) (mul_pos (by norm_num) hp0))
  rw [tiltedKrausAction_ofReal K hσ hθ0 hθ1, houtput, hinput,
    rpow_inverse_supported_sandwich hρ hσ hs hr]

theorem sandwichedTrace_krausAction_eq_tilted (K : Z → Matrix O I ℂ)
    {ρ σ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : SupportLE ρ σ) {p : ℝ} (hp : 1 < p) :
    sandwichedTrace p (krausAction K ρ) (krausAction K σ) =
      (CFC.rpow (tiltedKrausAction K hσ ((1 / p : ℝ) : ℂ)
        (CFC.rpow σ ((1 - p) / (2 * p)) * ρ * CFC.rpow σ ((1 - p) / (2 * p)))) p).trace.re := by
  rw [tiltedKrausAction_sandwichedInput K hρ hσ hs hp]
  rfl

end QuantumProver.SandwichedDPI
