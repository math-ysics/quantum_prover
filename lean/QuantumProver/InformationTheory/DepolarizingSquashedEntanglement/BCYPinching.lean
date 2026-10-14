import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYRelativeEntropy
import QuantumProver.InformationTheory.Equipartition.PinchingUmegaki
import QuantumProver.InformationTheory.SuperchannelDiscrimination.Pinching

set_option autoImplicit false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYPinching

open BCYRelativeEntropy
open QuantumProver.Equipartition.FiniteModel
open QuantumProver.Equipartition.FiniteModel.Testing
open QuantumProver.Equipartition.FiniteModel.PinchingUmegaki
open QuantumProver.SuperchannelDiscrimination

variable {I : Type*} [Fintype I] [DecidableEq I]

def finiteRelativeEntropyNats (R S : QMatrix I) : ℝ :=
  (R * (cfc Real.log R - cfc Real.log S)).trace.re

theorem umegakiReal_mul_log_two (R S : QMatrix I) :
    umegakiReal R S * Real.log 2 = finiteRelativeEntropyNats R S := by
  simp only [umegakiReal, tracePair, matrixLog, finiteRelativeEntropyNats,
    div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (show (1 : ℝ) < 2 by norm_num)))]

theorem spectralBlockCount_eq_spectrum_ncard {S : QMatrix I}
    (hS : S.IsHermitian) :
    spectralBlockCount hS = (spectrum ℝ S).ncard := by
  classical
  have he : (distinctEigenvalues hS : Set ℝ) = spectrum ℝ S := by
    rw [hS.spectrum_real_eq_range_eigenvalues]
    ext x
    simp [distinctEigenvalues]
  calc
    spectralBlockCount hS = (distinctEigenvalues hS).card := spectralBlockCount_eq hS
    _ = (distinctEigenvalues hS : Set ℝ).ncard := (Set.ncard_coe_finset _).symm
    _ = (spectrum ℝ S).ncard := congrArg Set.ncard he

theorem spectralProjectionFamily {S : QMatrix I} (hS : S.IsHermitian) :
    Pinching.IsProjectionFamily (spectralPinchingProjection hS) := by
  classical
  exact {
    selfAdjoint := fun k => (spectralPinchingProjection_posSemidef hS k).1
    idempotent := spectralPinchingProjection_idempotent hS
    orthogonal := fun _ _ hkl => spectralPinchingProjection_orthogonal hS hkl
    complete := sum_spectralPinchingProjection hS }

def spectralPinchingMap {S : QMatrix I} (hS : S.IsHermitian) :
    QMatrix I →ₗ[ℂ] QMatrix I :=
  Pinching.pinchingMap (spectralPinchingProjection hS)

theorem spectralPinchingMap_apply {S : QMatrix I} (hS : S.IsHermitian)
    (R : QMatrix I) : spectralPinchingMap hS R = spectralPinching hS R := by
  classical
  rw [spectralPinchingMap, Pinching.pinchingMap_apply _
    (spectralProjectionFamily hS).selfAdjoint]
  rfl

theorem spectralPinchingMap_completelyPositive {S : QMatrix I}
    (hS : S.IsHermitian) :
    DiamondControl.CompletelyPositive (spectralPinchingMap hS) :=
  Pinching.pinchingMap_completelyPositive _

theorem spectralPinchingMap_tracePreserving {S : QMatrix I}
    (hS : S.IsHermitian) (R : QMatrix I) :
    (spectralPinchingMap hS R).trace = R.trace :=
  Pinching.pinchingMap_tracePreserving (spectralProjectionFamily hS) R

theorem spectralPinching_fixes_reference {S : QMatrix I}
    (hS : S.IsHermitian) : spectralPinching hS S = S :=
  spectralPinching_fixed hS

theorem spectralPinching_commutes_reference {S : QMatrix I}
    (hS : S.IsHermitian) (R : QMatrix I) :
    Commute (spectralPinching hS R) S :=
  (show Commute S (spectralPinching hS R) from spectralPinching_commutes hS R).symm

def pinchedDensity (ρ : Density I) {S : QMatrix I} (hS : S.IsHermitian) :
    Density I where
  matrix := spectralPinching hS ρ.matrix
  positive := spectralPinching_posSemidef hS ρ.positive
  trace_one := (trace_spectralPinching hS ρ.matrix).trans ρ.trace_one

theorem pinchedDensity_matrix (ρ : Density I) {S : QMatrix I}
    (hS : S.IsHermitian) :
    (pinchedDensity ρ hS).matrix = spectralPinching hS ρ.matrix := rfl

theorem hasSupportIn_pinched (ρ : Density I) {S : QMatrix I}
    (hS : S.IsHermitian) :
    FlaggedStates.HasSupportIn ρ.matrix (pinchedDensity ρ hS).matrix :=
  supportLE_of_psd_domination ρ.positive (spectralPinching_domination hS ρ.positive)

theorem finiteRelativeEntropyNats_sub_pinching_eq {R S : QMatrix I}
    (hS : S.IsHermitian) :
    finiteRelativeEntropyNats R S - finiteRelativeEntropyNats (spectralPinching hS R) S =
      finiteRelativeEntropyNats R (spectralPinching hS R) := by
  have h := congrArg (fun x : ℝ => x * Real.log 2) (umegakiReal_sub_pinching_eq (ρ := R) hS)
  simpa only [sub_mul, umegakiReal_mul_log_two] using h

theorem finiteRelativeEntropyNats_sub_pinching_nonneg (ρ : Density I)
    {S : QMatrix I} (hS : S.IsHermitian) :
    0 ≤ finiteRelativeEntropyNats ρ.matrix S -
      finiteRelativeEntropyNats (pinchedDensity ρ hS).matrix S := by
  rw [pinchedDensity_matrix, finiteRelativeEntropyNats_sub_pinching_eq hS]
  have h := MatrixLog.klein_trace_direct_of_support ρ.positive
    (pinchedDensity ρ hS).positive (hasSupportIn_pinched ρ hS)
  rw [ρ.trace_one, (pinchedDensity ρ hS).trace_one] at h
  simpa only [Complex.one_re, sub_self, finiteRelativeEntropyNats, pinchedDensity_matrix] using h

theorem finiteRelativeEntropyNats_sub_pinching_eq_entropy (ρ : Density I)
    {S : QMatrix I} (hS : S.IsHermitian) :
    finiteRelativeEntropyNats ρ.matrix S -
        finiteRelativeEntropyNats (pinchedDensity ρ hS).matrix S =
      QuantumProver.QuantumEntropy.entropyNats (pinchedDensity ρ hS).matrix -
        QuantumProver.QuantumEntropy.entropyNats ρ.matrix := by
  rw [pinchedDensity_matrix, finiteRelativeEntropyNats_sub_pinching_eq hS]
  have ht := tracePair_spectralPinching_matrixLog_self (ρ := ρ.matrix) hS
  change (spectralPinching hS ρ.matrix * cfc Real.log (spectralPinching hS ρ.matrix)).trace.re =
    (ρ.matrix * cfc Real.log (spectralPinching hS ρ.matrix)).trace.re at ht
  simp only [finiteRelativeEntropyNats, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [← ht]
  simp only [QuantumProver.QuantumEntropy.entropyNats,
    MatrixLog.cfc_mulLog_eq_mul_log ρ.positive.1,
    MatrixLog.cfc_mulLog_eq_mul_log (spectralPinching_posSemidef hS ρ.positive).1]
  ring

theorem finiteRelativeEntropyNats_sub_pinching_le_log_spectrum (ρ : Density I)
    {S : QMatrix I} (hS : S.IsHermitian) :
    finiteRelativeEntropyNats ρ.matrix S -
      finiteRelativeEntropyNats (pinchedDensity ρ hS).matrix S ≤
        Real.log ((spectrum ℝ S).ncard : ℝ) := by
  have hb := umegakiReal_sub_pinching_le_log
    (ρ := ρ.matrix) (σ := S) (show IsState ρ.matrix from ⟨ρ.positive, ρ.trace_one⟩) hS
  have hm := mul_le_mul_of_nonneg_right hb
    (Real.log_pos (show (1 : ℝ) < 2 by norm_num)).le
  rw [sub_mul, umegakiReal_mul_log_two, umegakiReal_mul_log_two] at hm
  simpa only [pinchedDensity_matrix, logTwo,
    div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (show (1 : ℝ) < 2 by norm_num))),
    spectralBlockCount_eq_spectrum_ncard] using hm

theorem entropyNats_pinching_cost (ρ : Density I) {S : QMatrix I}
    (hS : S.IsHermitian) :
    0 ≤ QuantumProver.QuantumEntropy.entropyNats (pinchedDensity ρ hS).matrix -
      QuantumProver.QuantumEntropy.entropyNats ρ.matrix ∧
    QuantumProver.QuantumEntropy.entropyNats (pinchedDensity ρ hS).matrix -
      QuantumProver.QuantumEntropy.entropyNats ρ.matrix ≤ Real.log ((spectrum ℝ S).ncard : ℝ) := by
  rw [← finiteRelativeEntropyNats_sub_pinching_eq_entropy ρ hS]
  exact ⟨finiteRelativeEntropyNats_sub_pinching_nonneg ρ hS,
    finiteRelativeEntropyNats_sub_pinching_le_log_spectrum ρ hS⟩

theorem umegakiNats_of_posDef (R : QMatrix I) {S : QMatrix I} (hS : S.PosDef) :
    umegakiNats R S = (finiteRelativeEntropyNats R S : EReal) :=
  umegakiNats_of_support R S (FlaggedStates.hasSupportIn_of_posDef R hS)

theorem umegakiNats_pinching_cost (ρ : Density I) {S : QMatrix I}
    (hS : S.PosDef) :
    umegakiNats ρ.matrix S - (Real.log ((spectrum ℝ S).ncard : ℝ) : EReal) ≤
      umegakiNats (pinchedDensity ρ hS.1).matrix S := by
  rw [umegakiNats_of_posDef _ hS, umegakiNats_of_posDef _ hS,
    ← EReal.coe_sub, EReal.coe_le_coe_iff]
  linarith [finiteRelativeEntropyNats_sub_pinching_le_log_spectrum ρ hS.1]

theorem umegakiNats_pinching_cost_of_count (ρ : Density I) {S : QMatrix I}
    (hS : S.PosDef) (N : ℕ) (hcount : (spectrum ℝ S).ncard ≤ N + 1) :
    umegakiNats ρ.matrix S - (Real.log ((N : ℝ) + 1) : EReal) ≤
      umegakiNats (pinchedDensity ρ hS.1).matrix S := by
  letI := isState_nonempty_index (show IsState ρ.matrix from ⟨ρ.positive, ρ.trace_one⟩)
  have hp : 0 < ((spectrum ℝ S).ncard : ℝ) := by
    rw [← spectralBlockCount_eq_spectrum_ncard hS.1]
    exact_mod_cast spectralBlockCount_pos hS.1
  have hc : ((spectrum ℝ S).ncard : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hcount
  rw [umegakiNats_of_posDef _ hS, umegakiNats_of_posDef _ hS,
    ← EReal.coe_sub, EReal.coe_le_coe_iff]
  have hb := finiteRelativeEntropyNats_sub_pinching_le_log_spectrum ρ hS.1
  have hl := Real.log_le_log hp hc
  linarith

end QuantumProver.DepolarizingSquashedEntanglement.BCYPinching
