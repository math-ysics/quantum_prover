import QuantumProver.InformationTheory.Equipartition.Definitions
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems
import QuantumProver.InformationTheory.PetzModularPower

set_option autoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
open QuantumProver.Equipartition.FiniteModel
open QuantumProver.SuperchannelDiscrimination

namespace QuantumProver.PetzMeasurementDPI

variable {I : Type*} [Fintype I] [DecidableEq I] {L : ℕ}

theorem umegaki_eq_relativeEntropyBits (rho sigma : CMat I) :
    umegaki rho sigma = FlaggedStates.relativeEntropyBits rho sigma := rfl

def outcomeRow (b : Fin L) (S : CMat I) (i : I) : Matrix (Fin L) I ℂ :=
  fun a j => if a = b then S i j else 0

omit [DecidableEq I] in
theorem outcomeRow_gram (b : Fin L) (S : CMat I) :
    (∑ i : I, (outcomeRow b S i)ᴴ * outcomeRow b S i) = Sᴴ * S := by
  ext j k
  simp [outcomeRow, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    mul_ite]

omit [DecidableEq I] in
theorem outcomeRow_born (b : Fin L) (S X : CMat I) :
    (∑ i : I, outcomeRow b S i * X * (outcomeRow b S i)ᴴ) =
      (S * X * Sᴴ).trace • Matrix.single b b (1 : ℂ) := by
  ext a c
  by_cases ha : a = b <;> by_cases hc : c = b
  · subst a
    subst c
    simp [outcomeRow, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.trace, Matrix.diag, Finset.sum_mul, Matrix.smul_apply]
  · simp [outcomeRow, ha, hc, Ne.symm hc, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.smul_apply]
  · simp [outcomeRow, ha, hc, Ne.symm ha, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.smul_apply]
  · simp [outcomeRow, ha, hc, Ne.symm ha, Ne.symm hc, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.smul_apply]

def measurementKraus (M : FinitePOVM I L) (z : Fin L × I) : Matrix (Fin L) I ℂ :=
  outcomeRow z.1 (CFC.sqrt (M.outcome z.1)) z.2

theorem sqrt_outcome_gram (M : FinitePOVM I L) (b : Fin L) :
    (CFC.sqrt (M.outcome b))ᴴ * CFC.sqrt (M.outcome b) = M.outcome b := by
  have hs : (CFC.sqrt (M.outcome b))ᴴ = CFC.sqrt (M.outcome b) :=
    (CFC.sqrt_nonneg _).posSemidef.1
  rw [hs, CFC.sqrt_mul_sqrt_self _ (M.positive b).nonneg]

theorem sqrt_outcome_trace (M : FinitePOVM I L) (b : Fin L) (X : CMat I) :
    (CFC.sqrt (M.outcome b) * X * (CFC.sqrt (M.outcome b))ᴴ).trace =
      (X * M.outcome b).trace := by
  rw [Matrix.trace_mul_cycle, sqrt_outcome_gram, Matrix.trace_mul_comm]

theorem measurementKraus_complete (M : FinitePOVM I L) :
    KrausCompletion.krausGram (measurementKraus M) = 1 := by
  simp only [KrausCompletion.krausGram, Fintype.sum_prod_type, measurementKraus,
    outcomeRow_gram, sqrt_outcome_gram, M.sum_outcome]

theorem measurementKraus_action (M : FinitePOVM I L) (X : CMat I) :
    KrausCompletion.krausAction (measurementKraus M) X =
      diagonal (fun b => (X * M.outcome b).trace) := by
  rw [KrausCompletion.krausAction, Fintype.sum_prod_type]
  simp only [measurementKraus, outcomeRow_born, sqrt_outcome_trace]
  ext a c
  by_cases hac : a = c
  · subst c
    simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.single, Matrix.diagonal]
  · simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.single, Matrix.diagonal, hac]
    apply Finset.sum_eq_zero
    intro i _
    have hi : ¬ (i = a ∧ i = c) := by
      rintro ⟨rfl, hi⟩
      exact hac hi
    simp [hi]

omit [DecidableEq I] in
theorem trace_mul_eq_real {A B : CMat I} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((A * B).trace.re : ℂ) = (A * B).trace := by
  have hs : star (A * B).trace = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq,
      Matrix.trace_mul_comm]
  apply Complex.ext
  · rfl
  · have hi := congrArg Complex.im hs
    simp only [Complex.star_def, Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

theorem measurementKraus_action_psd (M : FinitePOVM I L) {X : CMat I}
    (hX : X.PosSemidef) :
    KrausCompletion.krausAction (measurementKraus M) X =
      diagonal (fun b => (measurementMass M X b : ℂ)) := by
  rw [measurementKraus_action]
  congr 1
  funext b
  exact (trace_mul_eq_real hX.1 (M.positive b).1).symm

theorem cfc_real_diagonal (p : Fin L → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (p i : ℂ))) = diagonal (fun i => (f (p i) : ℂ)) := by
  exact TensorEntropy.cfc_diagonal_real f p

theorem diagonal_support_iff (p q : Fin L → ℝ) :
    FlaggedStates.HasSupportIn (diagonal (fun i => (p i : ℂ)))
      (diagonal (fun i => (q i : ℂ))) ↔ classicalSupportLE p q := by
  constructor
  · intro hs i hqi
    have hv : diagonal (fun j => (q j : ℂ)) *ᵥ Pi.single i 1 = 0 := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [Matrix.mulVec_diagonal, hqi]
      · simp [Matrix.mulVec_diagonal, Pi.single_apply, hji]
    have hh := congrFun (hs (Pi.single i 1) hv) i
    exact_mod_cast (by simpa [Matrix.mulVec_diagonal] using hh : (p i : ℂ) = 0)
  · intro hs v hv
    ext i
    have hh := congrFun hv i
    simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at hh ⊢
    by_cases hqi : q i = 0
    · rw [hs i hqi]
      simp
    · have hqiC : (q i : ℂ) ≠ 0 := by exact_mod_cast hqi
      rw [(mul_eq_zero.mp hh).resolve_left hqiC]
      simp

theorem relativeEntropyBits_diagonal_eq_classical (p q : Fin L → ℝ) :
    FlaggedStates.relativeEntropyBits (diagonal (fun i => (p i : ℂ)))
      (diagonal (fun i => (q i : ℂ))) = classicalUmegaki p q := by
  classical
  by_cases hs : classicalSupportLE p q
  · rw [FlaggedStates.relativeEntropyBits, ite_eq_left ((diagonal_support_iff p q).mpr hs),
      classicalUmegaki, ite_eq_left hs]
    congr 1
    simp [FlaggedStates.finiteRelativeEntropyBits, cfc_real_diagonal,
      Matrix.mul_sub, Matrix.trace_sub, Complex.re_sum, logTwo,
      Finset.sum_div, Finset.sum_sub_distrib, mul_sub, mul_div_assoc, sub_div]
  · simp [FlaggedStates.relativeEntropyBits, diagonal_support_iff, classicalUmegaki, hs]

theorem classicalUmegaki_measurement_le (M : FinitePOVM I L) {rho sigma : CMat I}
    (hRho : rho.PosSemidef) (hSigma : sigma.PosSemidef) :
    classicalUmegaki (measurementMass M rho) (measurementMass M sigma) ≤
      umegaki rho sigma := by
  have h := InputSupport.relativeEntropyBits_kraus_dpi (measurementKraus M)
    (measurementKraus_complete M) hRho hSigma
  rw [measurementKraus_action_psd M hRho, measurementKraus_action_psd M hSigma,
    relativeEntropyBits_diagonal_eq_classical, ← umegaki_eq_relativeEntropyBits] at h
  exact h

theorem measuredDivergence_one_le_umegaki {rho sigma : CMat I}
    (hRho : rho.PosSemidef) (hSigma : sigma.PosSemidef) :
    measuredDivergence rho sigma 1 ≤ umegaki rho sigma := by
  apply sSup_le
  rintro z ⟨L, M, rfl⟩
  simpa [classicalRenyiDivergence] using
    classicalUmegaki_measurement_le M hRho hSigma

theorem measuredDivergence_one_le_petzDivergence {rho sigma : CMat I}
    (hRho : rho.PosSemidef) (hSigma : sigma.PosSemidef) :
    measuredDivergence rho sigma 1 ≤ petzDivergence rho sigma 1 := by
  simpa [petzDivergence] using
    measuredDivergence_one_le_umegaki hRho hSigma

theorem petzTrace_diagonal_eq_classicalRenyiTrace (p q : Fin L → ℝ) (alpha : ℝ) :
    petzTrace (diagonal (fun i => (p i : ℂ))) (diagonal (fun i => (q i : ℂ))) alpha =
      classicalRenyiTrace p q alpha := by
  simp only [petzTrace, tracePair, matrixRpow, cfc_real_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    classicalRenyiTrace]

theorem petzTrace_nonneg {rho sigma : CMat I} (hRho : rho.PosSemidef)
    (hSigma : sigma.PosSemidef) (alpha : ℝ) : 0 ≤ petzTrace rho sigma alpha := by
  unfold petzTrace tracePair
  apply FlaggedStates.trace_mul_re_nonneg
  · rw [matrixRpow_eq_cfc_rpow hRho]
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := rho) (y := alpha))
  · rw [matrixRpow_eq_cfc_rpow hSigma]
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := sigma) (y := 1 - alpha))

theorem petzTrace_le_classicalRenyiTrace (M : FinitePOVM I L)
    {rho sigma : CMat I} (hRho : rho.PosSemidef) (hSigma : sigma.PosSemidef)
    {alpha : ℝ} (hAlpha0 : 0 < alpha) (hAlpha1 : alpha < 1) :
    petzTrace rho sigma alpha ≤
      classicalRenyiTrace (measurementMass M rho) (measurementMass M sigma) alpha := by
  have h := PetzModularPower.petzTrace_le_kraus (measurementKraus M)
    (measurementKraus_complete M) hRho hSigma hAlpha0 hAlpha1
  rw [measurementKraus_action_psd M hRho, measurementKraus_action_psd M hSigma,
    petzTrace_diagonal_eq_classicalRenyiTrace] at h
  exact h

theorem classicalRenyiDivergence_measurement_le (M : FinitePOVM I L)
    {rho sigma : CMat I} (hRho : rho.PosSemidef) (hSigma : sigma.PosSemidef)
    {alpha : ℝ} (hAlpha0 : 0 < alpha) (hAlpha1 : alpha < 1) :
    classicalRenyiDivergence (measurementMass M rho) (measurementMass M sigma) alpha ≤
      petzDivergence rho sigma alpha := by
  classical
  have hNotOne : alpha ≠ 1 := ne_of_lt hAlpha1
  have hNotAbove : ¬ 1 < alpha := not_lt_of_ge hAlpha1.le
  by_cases hPetz0 : petzTrace rho sigma alpha = 0
  · simp [petzDivergence, hNotOne, hNotAbove, hPetz0]
  have hPetzPos : 0 < petzTrace rho sigma alpha :=
    lt_of_le_of_ne (petzTrace_nonneg hRho hSigma alpha) (Ne.symm hPetz0)
  have hMoment := petzTrace_le_classicalRenyiTrace M hRho hSigma hAlpha0 hAlpha1
  have hClassicalPos : 0 < classicalRenyiTrace (measurementMass M rho)
      (measurementMass M sigma) alpha := hPetzPos.trans_le hMoment
  simp only [classicalRenyiDivergence, petzDivergence, hNotOne, hNotAbove,
    false_and, ite_false, hPetz0, hClassicalPos.ne']
  apply EReal.coe_le_coe
  have hLog : logTwo (petzTrace rho sigma alpha) ≤
      logTwo (classicalRenyiTrace (measurementMass M rho) (measurementMass M sigma) alpha) :=
    div_le_div_of_nonneg_right (Real.log_le_log hPetzPos hMoment)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  exact (div_le_div_right_of_neg (sub_neg.mpr hAlpha1)).mpr hLog

theorem measuredDivergence_le_petzDivergence {rho sigma : CMat I}
    (hRho : rho.PosSemidef) (hSigma : sigma.PosSemidef)
    {alpha : ℝ} (hAlpha0 : 0 < alpha) (hAlpha1 : alpha < 1) :
    measuredDivergence rho sigma alpha ≤ petzDivergence rho sigma alpha := by
  apply sSup_le
  rintro z ⟨L, M, rfl⟩
  exact classicalRenyiDivergence_measurement_le M hRho hSigma hAlpha0 hAlpha1

end QuantumProver.PetzMeasurementDPI
