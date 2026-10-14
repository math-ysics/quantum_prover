import QuantumProver.InformationTheory.ConditionalEntropy.Main

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace QuantumProver.ConditionalEntropy.WeightedContinuity

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def blockDiagonalHom : (J → Matrix I I ℂ) →⋆ₐ[ℝ] Matrix (I × J) (I × J) ℂ where
  toFun := Matrix.blockDiagonal
  map_zero' := Matrix.blockDiagonal_zero
  map_one' := Matrix.blockDiagonal_one
  map_add' := Matrix.blockDiagonal_add
  map_mul' := Matrix.blockDiagonal_mul
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.blockDiagonal_smul,
      Matrix.blockDiagonal_one]
  map_star' R := by
    change Matrix.blockDiagonal (fun j => (R j)ᴴ) = (Matrix.blockDiagonal R)ᴴ
    exact (Matrix.blockDiagonal_conjTranspose R).symm

theorem blockDiagonalHom_continuous :
    Continuous (blockDiagonalHom (I := I) (J := J)) := by
  change Continuous (fun R : J → Matrix I I ℂ => Matrix.blockDiagonal R)
  exact continuous_id.matrix_blockDiagonal

theorem cfc_blockDiagonal (f : ℝ → ℝ) (hf : Continuous f)
    (R : J → Matrix I I ℂ) (hR : ∀ j, (R j).IsHermitian) :
    cfc f (Matrix.blockDiagonal R) = Matrix.blockDiagonal (fun j => cfc f (R j)) := by
  letI : IsometricContinuousFunctionalCalculus ℝ (J → Matrix I I ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  have hPi : IsSelfAdjoint R := by
    funext j
    exact hR j
  have hOut : (Matrix.blockDiagonal R).IsHermitian :=
    Matrix.isHermitian_blockDiagonal_iff.mpr hR
  have hMap := (blockDiagonalHom (I := I) (J := J)).map_cfc f R
    hf.continuousOn blockDiagonalHom_continuous hPi hOut
  rw [cfc_map_pi (S := ℝ) f R hf.continuousOn hPi hR] at hMap
  exact hMap.symm

theorem blockDiagonal_posSemidef (R : J → Matrix I I ℂ)
    (hR : ∀ j, (R j).PosSemidef) : (Matrix.blockDiagonal R).PosSemidef := by
  let Q : J → Matrix I I ℂ := fun j => CFC.sqrt (R j)
  have hFactor : Matrix.blockDiagonal R =
      Matrix.blockDiagonal Q * (Matrix.blockDiagonal Q)ᴴ := by
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    congr 1
    funext j
    exact (ConditionalRange.sqrt_grams (hR j)).1.symm
  rw [hFactor]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem entropyBits_blockDiagonal (R : J → Matrix I I ℂ)
    (hR : ∀ j, (R j).IsHermitian) :
    entropyBits (Matrix.blockDiagonal R) = ∑ j, entropyBits (R j) := by
  change -(cfc (fun x : ℝ => x * Real.log x) (Matrix.blockDiagonal R)).trace.re /
      Real.log 2 = ∑ j, -(cfc (fun x : ℝ => x * Real.log x) (R j)).trace.re / Real.log 2
  rw [cfc_blockDiagonal _ Real.continuous_mul_log R hR, Matrix.trace_blockDiagonal]
  simp only [Complex.re_sum]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

theorem traceNorm_blockDiagonal (R : J → Matrix I I ℂ)
    (hR : ∀ j, (R j).IsHermitian) :
    traceNorm (Matrix.blockDiagonal R) = ∑ j, traceNorm (R j) := by
  have hOut := Matrix.isHermitian_blockDiagonal_iff.mpr hR
  have hAbs : CFC.abs (Matrix.blockDiagonal R) =
      Matrix.blockDiagonal (fun j => CFC.abs (R j)) := by
    rw [CFC.abs_eq_cfc_norm _ hOut.isSelfAdjoint,
      cfc_blockDiagonal _ continuous_norm R hR]
    congr 1
    funext j
    exact (CFC.abs_eq_cfc_norm (R j) (hR j).isSelfAdjoint).symm
  change (CFC.abs (Matrix.blockDiagonal R)).trace.re = ∑ j, (CFC.abs (R j)).trace.re
  rw [hAbs, Matrix.trace_blockDiagonal, Complex.re_sum]

theorem traceNorm_smul (w : ℝ) (hw : 0 ≤ w) (R : Matrix I I ℂ)
    (hR : R.IsHermitian) : traceNorm (w • R) = w * traceNorm R := by
  have hScaled : (w • R).IsHermitian := hR.smul (by rfl)
  have hAbs : CFC.abs (w • R) = w • CFC.abs R := by
    rw [CFC.abs_eq_cfc_norm _ hScaled.isSelfAdjoint,
      CFC.abs_eq_cfc_norm R hR.isSelfAdjoint,
      ← cfc_comp_const_mul (p := IsSelfAdjoint) w (fun x : ℝ => ‖x‖) R
        continuous_norm.continuousOn hR]
    have hFun : (fun x : ℝ => ‖w * x‖) = fun x => w * ‖x‖ := by
      funext x
      rw [norm_mul, Real.norm_of_nonneg hw]
    rw [hFun, cfc_const_mul w _ R continuous_norm.continuousOn]
  change (CFC.abs (w • R)).trace.re = w * (CFC.abs R).trace.re
  rw [hAbs, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

def qcFlag (w : J → ℝ) (R : J → Matrix I I ℂ) : Matrix (I × J) (I × J) ℂ :=
  Matrix.blockDiagonal (fun j => w j • R j)

theorem qcFlag_posSemidef (w : J → ℝ) (R : J → Matrix I I ℂ)
    (hw : ∀ j, 0 ≤ w j) (hR : ∀ j, (R j).PosSemidef) :
    (qcFlag w R).PosSemidef :=
  blockDiagonal_posSemidef _ (fun j => (hR j).smul (hw j))

theorem qcFlag_isDensity (w : J → ℝ) (R : J → Matrix I I ℂ)
    (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1) (hR : ∀ j, IsDensity (R j)) :
    IsDensity (qcFlag w R) := by
  refine ⟨qcFlag_posSemidef w R hw (fun j => (hR j).1), ?_⟩
  rw [qcFlag, Matrix.trace_blockDiagonal]
  calc
    (∑ j, (w j • R j).trace) = ∑ j, (w j : ℂ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.trace_smul, (hR j).2]
      simp
    _ = 1 := by exact_mod_cast hs

theorem qcFlag_flagMarginal (w : J → ℝ) (R : J → Matrix I I ℂ)
    (hR : ∀ j, (R j).trace = 1) :
    QuantumProver.QuantumEntropy.partialTrace_left (qcFlag w R) =
      Matrix.diagonal (fun j => (w j : ℂ)) := by
  ext j j'
  by_cases h : j = j'
  · subst j'
    simp only [QuantumProver.QuantumEntropy.partialTrace_left, qcFlag,
      Matrix.blockDiagonal_apply_eq, Matrix.diagonal_apply_eq]
    change ((w j) • R j).trace = (w j : ℂ)
    rw [Matrix.trace_smul, hR j]
    simp
  · simp [QuantumProver.QuantumEntropy.partialTrace_left, qcFlag,
      Matrix.blockDiagonal_apply, Matrix.diagonal_apply, h]

theorem entropyBits_classicalFlag (w : J → ℝ) :
    entropyBits (Matrix.diagonal (fun j => (w j : ℂ))) =
      -(∑ j, w j * Real.log (w j)) / Real.log 2 := by
  change -(cfc (fun x : ℝ => x * Real.log x)
      (Matrix.diagonal (fun j => (w j : ℂ)))).trace.re / Real.log 2 = _
  rw [QuantumProver.SuperchannelDiscrimination.TensorEntropy.cfc_diagonal_real,
    Matrix.trace_diagonal, Complex.re_sum]
  simp only [Complex.ofReal_re]

theorem conditionalEntropy_qcFlag (w : J → ℝ) (R : J → Matrix I I ℂ)
    (hw : ∀ j, 0 ≤ w j) (hR : ∀ j, IsDensity (R j)) :
    conditionalEntropyBits (qcFlag w R) = ∑ j, w j * entropyBits (R j) := by
  rw [conditionalEntropyBits, qcFlag_flagMarginal w R (fun j => (hR j).2),
    entropyBits_classicalFlag]
  have hBlocks : entropyBits (qcFlag w R) = ∑ j, entropyBits (w j • R j) :=
    entropyBits_blockDiagonal _ (fun j => ((hR j).1.smul (hw j)).1)
  rw [hBlocks]
  have hTerm (j : J) : entropyBits (w j • R j) = w j * entropyBits (R j) -
      w j * Real.log (w j) / Real.log 2 := by
    change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits (w j • R j) = _
    rw [QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits_smul (w j) (hR j).1,
      (hR j).2, Complex.one_re, mul_one]
  simp only [hTerm, Finset.sum_sub_distrib]
  rw [← Finset.sum_div]
  ring

theorem traceDistance_qcFlag (w : J → ℝ) (R S : J → Matrix I I ℂ)
    (hw : ∀ j, 0 ≤ w j) (hR : ∀ j, IsDensity (R j)) (hS : ∀ j, IsDensity (S j)) :
    traceDistance (qcFlag w R) (qcFlag w S) = ∑ j, w j * traceDistance (R j) (S j) := by
  have hDiff : qcFlag w R - qcFlag w S =
      Matrix.blockDiagonal (fun j => w j • (R j - S j)) := by
    rw [qcFlag, qcFlag, ← Matrix.blockDiagonal_sub]
    congr 1
    funext j
    exact (smul_sub (w j) (R j) (S j)).symm
  rw [traceDistance, hDiff, traceNorm_blockDiagonal _
    (fun j => ((hR j).1.1.sub (hS j).1.1).smul (by rfl))]
  simp only [traceNorm_smul _ (hw _) _ ((hR _).1.1.sub (hS _).1.1), traceDistance,
    Finset.sum_div, mul_div_assoc]

theorem weighted_entropyBits_continuity (w : J → ℝ) (R S : J → Matrix I I ℂ)
    (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1)
    (hR : ∀ j, IsDensity (R j)) (hS : ∀ j, IsDensity (S j)) {delta : ℝ}
    (hDistance : ∑ j, w j * traceDistance (R j) (S j) ≤ delta) (hDelta : delta ≤ 1) :
    |(∑ j, w j * entropyBits (R j)) - (∑ j, w j * entropyBits (S j))| ≤
      winterBound I delta := by
  have hFlagDistance : traceDistance (qcFlag w R) (qcFlag w S) ≤ delta := by
    rw [traceDistance_qcFlag w R S hw hR hS]
    exact hDistance
  have hBound := conditionalEntropy_continuity
    (qcFlag_isDensity w R hw hs hR) (qcFlag_isDensity w S hw hs hS) hFlagDistance hDelta
  simpa only [conditionalEntropy_qcFlag w R hw hR,
    conditionalEntropy_qcFlag w S hw hS] using hBound

theorem logDim_fin_power (d n : ℕ) :
    logDimA (Fin (d ^ n)) = (n : ℝ) * (Real.log (d : ℝ) / Real.log 2) := by
  simp only [logDimA, Fintype.card_fin, Nat.cast_pow, Real.log_pow]
  ring

theorem perCopy_winterBound_tendsto_zero (d : ℕ) (delta : ℕ → ℝ)
    (hDelta : Filter.Tendsto delta Filter.atTop (𝓝 (0 : ℝ))) :
    Filter.Tendsto (fun n => winterBound (Fin (d ^ n)) (delta n) / (n : ℝ))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  let L := Real.log (d : ℝ) / Real.log 2
  let noise : ℕ → ℝ := fun n =>
    (1 + delta n) * binaryEntropy (delta n / (1 + delta n))
  have hNoise : Filter.Tendsto noise Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [Function.comp_def, winterBound, logDimA, noise] using
      (winterBound_tendsto_zero Unit).comp hDelta
  have hLinear : Filter.Tendsto (fun n => 2 * delta n * L)
      Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hDelta).mul
        (tendsto_const_nhds (x := L))
  have hSmall : Filter.Tendsto (fun n => noise n / (n : ℝ))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, zero_mul] using
      hNoise.mul (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hTotal : Filter.Tendsto (fun n => 2 * delta n * L + noise n / (n : ℝ))
      Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_add] using hLinear.add hSmall
  apply hTotal.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [winterBound, logDim_fin_power]
  dsimp only [L, noise]
  field_simp [hnR, ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  <;> ring

theorem perCopy_winterBound_sqrt_tendsto_zero (d : ℕ) (epsilon : ℕ → ℝ)
    (hEpsilon : Filter.Tendsto epsilon Filter.atTop (𝓝 (0 : ℝ))) :
    Filter.Tendsto
      (fun n => winterBound (Fin (d ^ n)) (Real.sqrt (epsilon n)) / (n : ℝ))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  apply perCopy_winterBound_tendsto_zero
  simpa only [Function.comp_def, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hEpsilon

end QuantumProver.ConditionalEntropy.WeightedContinuity
