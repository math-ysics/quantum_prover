import QuantumProver.InformationTheory.WernerEndpoint.OperationalEndpointCost
import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.ExtensionIdentities

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace QuantumProver.WernerEndpoint.FidelityError

open Matrix AntisymmetricEnsembleCost
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev rootFidelity (rho sigma : Matrix I I ℂ) : ℝ :=
  QuantumProver.BellDiagonalSquashedEntanglement.rootFidelity rho sigma

def halfTraceDistance (rho sigma : Matrix I I ℂ) : ℝ :=
  SchattenSupport.schattenOne (rho - sigma) / 2

def buresDistance (rho sigma : Matrix I I ℂ) : ℝ :=
  2 * Real.sqrt (1 - rootFidelity rho sigma)

theorem rootFidelity_eq_hht_sandwich (rho sigma : Matrix I I ℂ)
    (hRho : rho.PosSemidef) (hSigma : sigma.PosSemidef) :
    rootFidelity rho sigma = (CFC.sqrt (CFC.sqrt rho * sigma * CFC.sqrt rho)).trace.re :=
  QuantumProver.BellDiagonalSquashedEntanglement.Geometry.sqrt_product_absolute_trace_sandwich rho sigma hRho hSigma

theorem buresDistance_eq_hht_formula (rho sigma : Matrix I I ℂ)
    (hRho : rho.PosSemidef) (hSigma : sigma.PosSemidef) :
    buresDistance rho sigma =
      2 * Real.sqrt (1 - (CFC.sqrt (CFC.sqrt rho * sigma * CFC.sqrt rho)).trace.re) := by
  rw [buresDistance, rootFidelity_eq_hht_sandwich rho sigma hRho hSigma]

theorem halfTraceDistance_nonneg (rho sigma : Matrix I I ℂ) :
    0 ≤ halfTraceDistance rho sigma :=
  div_nonneg (SchattenSupport.schattenOne_nonneg _) (by norm_num)

theorem buresDistance_nonneg (rho sigma : Matrix I I ℂ) :
    0 ≤ buresDistance rho sigma :=
  mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

theorem bellTraceNorm_eq_schattenOne (M : Matrix I I ℂ) :
    QuantumProver.BellDiagonalSquashedEntanglement.traceNorm M = SchattenSupport.schattenOne M := by
  have h : QuantumProver.BellDiagonalSquashedEntanglement.traceNorm M =
      QuantumProver.SuperchannelDiscrimination.EffectPerturbation.traceNorm M := by
    simp only [QuantumProver.BellDiagonalSquashedEntanglement.traceNorm,
      QuantumProver.SuperchannelDiscrimination.EffectPerturbation.traceNorm, CFC.abs,
      Matrix.star_eq_conjTranspose]
  exact h.trans (OperationalEndpointCost.traceNorm_eq_schattenOne M)

theorem pureDensity_schatten_distance_sq_le (v w : I → ℂ)
    (hv : vectorNormSq v = 1) (hw : vectorNormSq w = 1) :
    SchattenSupport.schattenOne (pureDensity v - pureDensity w) ^ 2 ≤
      4 * (1 - Complex.normSq (dotProduct (star v) w)) := by
  let D := pureDensity v - pureDensity w
  have hr : (Matrix.rank D : ℝ) ≤ 2 := by
    exact_mod_cast pureDensity_difference_rank_le_two v w
  have hn : 0 ≤ hsNormSq D := Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => sq_nonneg ‖D i j‖))
  calc
    _ ≤ (Matrix.rank D : ℝ) * hsNormSq D :=
      SchattenSupport.schattenOne_sq_le_rank_hsNormSq D
    _ ≤ 2 * hsNormSq D := mul_le_mul_of_nonneg_right hr hn
    _ = _ := by
      dsimp only [D]
      rw [pureDensity_difference_hsNormSq v w hv hw]
      ring

theorem halfTraceDistance_le_sqrt_one_sub_fidelity_sq
    (rho sigma : Matrix I I ℂ)
    (hRho : rho.PosSemidef ∧ rho.trace = 1)
    (hSigma : sigma.PosSemidef ∧ sigma.trace = 1) :
    halfTraceDistance rho sigma ≤ Real.sqrt (1 - rootFidelity rho sigma ^ 2) := by
  let A : QuantumProver.BellDiagonalSquashedEntanglement.Density I := ⟨rho, hRho⟩
  let B : QuantumProver.BellDiagonalSquashedEntanglement.Density I := ⟨sigma, hSigma⟩
  obtain ⟨v, w, hv, hw, hmRho, hmSigma, hf⟩ :=
    QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.UhlmannGeometry.density_has_fidelity_attaining_purifications A B
  have hvTrace : (pureDensity v).trace = 1 := hv.2
  have hwTrace : (pureDensity w).trace = 1 := hw.2
  rw [pureDensity_trace] at hvTrace hwTrace
  have hvNorm : vectorNormSq v = 1 := by
    simpa only [Complex.ofReal_re, Complex.one_re] using congrArg Complex.re hvTrace
  have hwNorm : vectorNormSq w = 1 := by
    simpa only [Complex.ofReal_re, Complex.one_re] using congrArg Complex.re hwTrace
  have hinner : inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 w) =
      dotProduct (star v) w := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rw [hinner] at hf
  have hOverlap : Complex.normSq (dotProduct (star v) w) =
      rootFidelity rho sigma ^ 2 := by
    rw [← Complex.sq_norm, hf]
  have hmRho' : partialTraceLeft (pureDensity v) = rho := hmRho
  have hmSigma' : partialTraceLeft (pureDensity w) = sigma := hmSigma
  have hContract := OperationalEndpointCost.partialTraceLeft_schatten_distance_le
    (pureDensity v) (pureDensity w)
    (pureDensity_posSemidef v).isHermitian (pureDensity_posSemidef w).isHermitian
  rw [hmRho', hmSigma'] at hContract
  have hPure := pureDensity_schatten_distance_sq_le v w hvNorm hwNorm
  rw [hOverlap] at hPure
  have hF0 : 0 ≤ rootFidelity rho sigma :=
    QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.UhlmannGeometry.rootFidelity_nonneg A B
  have hF1 : rootFidelity rho sigma ≤ 1 :=
    QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.UhlmannGeometry.rootFidelity_le_one A B
  have hBudget : 0 ≤ 1 - rootFidelity rho sigma ^ 2 := by nlinarith
  have hPureBound : SchattenSupport.schattenOne (pureDensity v - pureDensity w) ≤
      2 * Real.sqrt (1 - rootFidelity rho sigma ^ 2) := by
    nlinarith [SchattenSupport.schattenOne_nonneg (pureDensity v - pureDensity w),
      Real.sqrt_nonneg (1 - rootFidelity rho sigma ^ 2), Real.sq_sqrt hBudget]
  dsimp only [halfTraceDistance]
  linarith

theorem halfTraceDistance_le_buresDistance
    (rho sigma : Matrix I I ℂ)
    (hRho : rho.PosSemidef ∧ rho.trace = 1)
    (hSigma : sigma.PosSemidef ∧ sigma.trace = 1) :
    halfTraceDistance rho sigma ≤ buresDistance rho sigma := by
  have h := halfTraceDistance_le_sqrt_one_sub_fidelity_sq rho sigma hRho hSigma
  let A : QuantumProver.BellDiagonalSquashedEntanglement.Density I := ⟨rho, hRho⟩
  let B : QuantumProver.BellDiagonalSquashedEntanglement.Density I := ⟨sigma, hSigma⟩
  have hF0 : 0 ≤ rootFidelity rho sigma :=
    QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.UhlmannGeometry.rootFidelity_nonneg A B
  have hF1 : rootFidelity rho sigma ≤ 1 :=
    QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.UhlmannGeometry.rootFidelity_le_one A B
  have hb : 0 ≤ 1 - rootFidelity rho sigma := by linarith
  have hb2 : 0 ≤ 1 - rootFidelity rho sigma ^ 2 := by nlinarith
  have hs : Real.sqrt (1 - rootFidelity rho sigma ^ 2) ≤
      2 * Real.sqrt (1 - rootFidelity rho sigma) := by
    nlinarith [Real.sqrt_nonneg (1 - rootFidelity rho sigma ^ 2),
      Real.sqrt_nonneg (1 - rootFidelity rho sigma),
      Real.sq_sqrt hb, Real.sq_sqrt hb2]
  exact h.trans hs

theorem halfTraceDistance_le_of_buresDistance_le
    (rho sigma : Matrix I I ℂ)
    (hRho : rho.PosSemidef ∧ rho.trace = 1)
    (hSigma : sigma.PosSemidef ∧ sigma.trace = 1)
    (epsilon : ℝ) (hError : buresDistance rho sigma ≤ epsilon) :
    halfTraceDistance rho sigma ≤ epsilon :=
  (halfTraceDistance_le_buresDistance rho sigma hRho hSigma).trans hError

theorem rootFidelity_self (rho : Matrix I I ℂ)
    (hRho : rho.PosSemidef ∧ rho.trace = 1) : rootFidelity rho rho = 1 := by
  change QuantumProver.BellDiagonalSquashedEntanglement.traceNorm (CFC.sqrt rho * CFC.sqrt rho) = 1
  rw [CFC.sqrt_mul_sqrt_self rho hRho.1.nonneg]
  rw [bellTraceNorm_eq_schattenOne,
    ← OperationalEndpointCost.traceNorm_eq_schattenOne,
    QuantumProver.SuperchannelDiscrimination.EffectPerturbation.traceNorm_of_posSemidef hRho.1,
    hRho.2]
  rfl

theorem buresDistance_self (rho : Matrix I I ℂ)
    (hRho : rho.PosSemidef ∧ rho.trace = 1) : buresDistance rho rho = 0 := by
  simp [buresDistance, rootFidelity_self rho hRho]

theorem halfTraceDistance_tendsto_zero_of_bures
    {J : Type*} (l : Filter J) (X : J → Type*)
    [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (rho sigma : ∀ j, Matrix (X j) (X j) ℂ)
    (hRho : ∀ j, (rho j).PosSemidef ∧ (rho j).trace = 1)
    (hSigma : ∀ j, (sigma j).PosSemidef ∧ (sigma j).trace = 1)
    (hError : Filter.Tendsto (fun j => buresDistance (rho j) (sigma j)) l (nhds 0)) :
    Filter.Tendsto (fun j => halfTraceDistance (rho j) (sigma j)) l (nhds 0) := by
  exact squeeze_zero (fun j => halfTraceDistance_nonneg (rho j) (sigma j))
    (fun j => halfTraceDistance_le_buresDistance (rho j) (sigma j) (hRho j) (hSigma j))
    hError

end QuantumProver.WernerEndpoint.FidelityError
