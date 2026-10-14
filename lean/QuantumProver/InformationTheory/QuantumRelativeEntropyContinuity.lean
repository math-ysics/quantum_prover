import QuantumProver.InformationTheory.QuantumEntropy.MatrixLogSupport
import QuantumProver.InformationTheory.QuantumEntropy.Definitions

set_option autoImplicit false

noncomputable section

open Filter Set Topology Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
open QuantumProver.SuperchannelDiscrimination
open QuantumProver.SuperchannelDiscrimination.FlaggedStates
open QuantumProver.SuperchannelDiscrimination.TensorEntropy
open QuantumProver.SuperchannelDiscrimination.EntropyContinuity
open QuantumProver.SuperchannelDiscrimination.LogCompression

namespace QuantumProver.QuantumRelativeEntropyContinuity

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Mat (I : Type*) := Matrix I I ℂ

def spectralWeight (A : Mat I) {B : Mat I} (hB : B.IsHermitian) (i : I) : ℝ :=
  (((hB.eigenvectorUnitary : Mat I)ᴴ * A * (hB.eigenvectorUnitary : Mat I)) i i).re

theorem spectralWeight_nonneg {A B : Mat I} (hA : A.PosSemidef)
    (hB : B.IsHermitian) (i : I) : 0 ≤ spectralWeight A hB i :=
  QuantumProver.QuantumEntropy.MatrixLogSupport.eigenbasis_weight_nonneg hA hB i

theorem trace_mul_cfc_re_eq_sum (A : Mat I) {B : Mat I}
    (hB : B.IsHermitian) (f : ℝ → ℝ) :
    (A * cfc f B).trace.re = ∑ i, spectralWeight A hB i * f (hB.eigenvalues i) := by
  rw [cfc_spectral f hB]
  change (A * ((hB.eigenvectorUnitary : Mat I) *
    Matrix.diagonal (fun i => (f (hB.eigenvalues i) : ℂ)) *
      (hB.eigenvectorUnitary : Mat I)ᴴ)).trace.re = _
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle]
  simp only [← Matrix.mul_assoc, Matrix.trace, Matrix.diag, Matrix.mul_diagonal,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, spectralWeight]

theorem hasSupportIn_iff_zero_spectralWeight {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.IsHermitian) :
    HasSupportIn A B ↔ ∀ i, hB.eigenvalues i = 0 → spectralWeight A hB i = 0 := by
  let U := hB.eigenvectorUnitary
  let T := Unitary.conjStarAlgAut ℝ (Mat I) (star U)
  let R : Mat I := (U : Mat I)ᴴ * A * (U : Mat I)
  have hP : T (supportProjection B) =
      Matrix.diagonal (fun i => (nonzeroWeight (hB.eigenvalues i) : ℂ)) := by
    rw [supportProjection, cfc_spectral nonzeroWeight hB]
    change Unitary.conjStarAlgAut ℝ (Mat I) (star U)
      (Unitary.conjStarAlgAut ℝ (Mat I) U _) = _
    rw [← Unitary.conjStarAlgAut_mul_apply]
    simp
  have hTA : T A = R := by
    simp [T, R, Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose]
  constructor
  · intro hs i hi
    have h := congrArg T ((hasSupportIn_iff_mul_supportProjection hB).mp hs)
    rw [map_mul, hP, hTA] at h
    have hd := congrArg (fun X : Mat I => (X i i).re) h
    simpa [Matrix.mul_diagonal, nonzeroWeight, hi, spectralWeight, R, U] using hd.symm
  · intro hs
    have hR : R.PosSemidef := hA.conjTranspose_mul_mul_same (U : Mat I)
    have hcol (i : I) (hi : hB.eigenvalues i = 0) : ∀ j, R j i = 0 := by
      have hd : R i i = 0 := by
        have hr : (R i i).re = 0 := hs i hi
        have him : (R i i).im = 0 := (Complex.nonneg_iff.mp (hR.diag_nonneg (i := i))).2.symm
        exact Complex.ext hr him
      have hq : star (Pi.single i (1 : ℂ)) ⬝ᵥ R *ᵥ Pi.single i (1 : ℂ) = 0 := by
        simp [Matrix.mulVec_single, hd]
      have hv := (hR.dotProduct_mulVec_zero_iff).mp hq
      intro j
      simpa [Matrix.mulVec_single] using congrFun hv j
    apply (hasSupportIn_iff_mul_supportProjection hB).mpr
    apply T.injective
    rw [map_mul]
    change T A * T (supportProjection B) = T A
    rw [hP, hTA]
    ext i j
    by_cases hj : hB.eigenvalues j = 0
    · simp [Matrix.mul_diagonal, nonzeroWeight, hj, hcol j hj i]
    · simp [Matrix.mul_diagonal, nonzeroWeight, hj]

def regularizedObjectiveBits (A B : Mat I) (eps : ℝ) : ℝ :=
  (entropyTrace A - (A * cfc Real.log (B + eps • (1 : Mat I))).trace.re) / Real.log 2

theorem regularizedObjectiveBits_spectral (A : Mat I) {B : Mat I}
    (hB : B.IsHermitian) (eps : ℝ) :
    regularizedObjectiveBits A B eps =
      (entropyTrace A - ∑ i, spectralWeight A hB i * Real.log (hB.eigenvalues i + eps)) /
        Real.log 2 := by
  rw [regularizedObjectiveBits, shifted_log_cfc hB eps, trace_mul_cfc_re_eq_sum]

theorem regularizedObjectiveBits_le_relativeEntropyBits {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) {eps : ℝ} (heps : 0 < eps) :
    (regularizedObjectiveBits A B eps : EReal) ≤ relativeEntropyBits A B := by
  by_cases hs : HasSupportIn A B
  · simp only [relativeEntropyBits, hs, ite_true]
    apply EReal.coe_le_coe_iff.mpr
    rw [finiteRelativeEntropyBits_eq_spectral hA.1,
      regularizedObjectiveBits_spectral A hB.1 eps, trace_mul_cfc_re_eq_sum A hB.1]
    apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hsum : ∑ i, spectralWeight A hB.1 i * Real.log (hB.1.eigenvalues i) ≤
        ∑ i, spectralWeight A hB.1 i * Real.log (hB.1.eigenvalues i + eps) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : hB.1.eigenvalues i = 0
      · rw [(hasSupportIn_iff_zero_spectralWeight hA hB.1).mp hs i hi]
        simp
      · apply mul_le_mul_of_nonneg_left _ (spectralWeight_nonneg hA hB.1 i)
        apply Real.log_le_log
        · exact lt_of_le_of_ne (hB.eigenvalues_nonneg i) (Ne.symm hi)
        · exact le_add_of_nonneg_right heps.le
    change entropyTrace A - _ ≤ entropyTrace A - _
    linarith
  · simp [relativeEntropyBits, hs]

theorem regularizedObjectiveBits_tendsto_of_support {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hs : HasSupportIn A B) :
    Tendsto (regularizedObjectiveBits A B) (𝓝 (0 : ℝ)) (𝓝 (finiteRelativeEntropyBits A B)) := by
  have ht (i : I) : Tendsto
      (fun eps : ℝ => spectralWeight A hB.1 i * Real.log (hB.1.eigenvalues i + eps))
      (𝓝 0) (𝓝 (spectralWeight A hB.1 i * Real.log (hB.1.eigenvalues i))) := by
    by_cases hi : hB.1.eigenvalues i = 0
    · rw [(hasSupportIn_iff_zero_spectralWeight hA hB.1).mp hs i hi]
      simp
    · have hl : ContinuousAt (fun eps : ℝ => Real.log (hB.1.eigenvalues i + eps)) 0 := by
        apply ContinuousAt.log
        · fun_prop
        · simpa using hi
      simpa using tendsto_const_nhds.mul hl.tendsto
  have hsum := tendsto_finset_sum Finset.univ (fun i _ => ht i)
  have hc : Tendsto (fun _ : ℝ => entropyTrace A) (𝓝 (0 : ℝ)) (𝓝 (entropyTrace A)) :=
    tendsto_const_nhds
  have h := (hc.sub hsum).div_const (Real.log 2)
  change Tendsto (fun eps : ℝ => regularizedObjectiveBits A B eps) _ _
  simpa only [regularizedObjectiveBits_spectral A hB.1,
    finiteRelativeEntropyBits_eq_spectral hA.1, trace_mul_cfc_re_eq_sum A hB.1, entropyTrace] using h

def regularizedValues (A B : Mat I) : Set EReal :=
  {z | ∃ eps : ℝ, 0 < eps ∧ z = (regularizedObjectiveBits A B eps : EReal)}

theorem sSup_regularizedValues_eq_top_of_support_failure {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hs : ¬ HasSupportIn A B) :
    sSup (regularizedValues A B) = ⊤ := by
  classical
  have hz : ¬ ∀ i, hB.1.eigenvalues i = 0 → spectralWeight A hB.1 i = 0 :=
    fun h => hs ((hasSupportIn_iff_zero_spectralWeight hA hB.1).mpr h)
  push_neg at hz
  obtain ⟨k, hbk, hwk⟩ := hz
  have hw : 0 < spectralWeight A hB.1 k :=
    lt_of_le_of_ne (spectralWeight_nonneg hA hB.1 k) (Ne.symm hwk)
  let C := ∑ i, spectralWeight A hB.1 i * Real.log (hB.1.eigenvalues i + 1)
  have hbound (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
      ∑ i, spectralWeight A hB.1 i * Real.log (hB.1.eigenvalues i + eps) ≤
        C + spectralWeight A hB.1 k * Real.log eps := by
    have hh : ∑ i, spectralWeight A hB.1 i * Real.log (hB.1.eigenvalues i + eps) ≤
        ∑ i, (spectralWeight A hB.1 i * Real.log (hB.1.eigenvalues i + 1) +
          if i = k then spectralWeight A hB.1 k * Real.log eps else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i = k
      · simp [hi, hbk]
      · simp only [if_neg hi, add_zero]
        apply mul_le_mul_of_nonneg_left _ (spectralWeight_nonneg hA hB.1 i)
        exact Real.log_le_log (add_pos_of_nonneg_of_pos (hB.eigenvalues_nonneg i) heps)
          (by linarith)
    simpa [Finset.sum_add_distrib, C] using hh
  apply le_antisymm le_top
  by_contra hn
  obtain ⟨b, hb, _⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  let y := b * Real.log 2 - entropyTrace A + C
  let t := |y / spectralWeight A hB.1 k| + 1
  let eps := Real.exp (-t)
  have ht : 0 < t := by dsimp [t]; positivity
  have heps : 0 < eps := Real.exp_pos _
  have heps1 : eps ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)
  have hy : y ≤ spectralWeight A hB.1 k * |y / spectralWeight A hB.1 k| := by
    have h := mul_le_mul_of_nonneg_left (le_abs_self (y / spectralWeight A hB.1 k)) hw.le
    have heq : spectralWeight A hB.1 k * (y / spectralWeight A hB.1 k) = y := by
      field_simp
    rwa [heq] at h
  have hyt : y < spectralWeight A hB.1 k * t := by dsimp [t]; nlinarith
  have hlarge : b < (entropyTrace A - C + spectralWeight A hB.1 k * t) / Real.log 2 := by
    apply (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    dsimp [y] at hyt
    linarith
  have hobj : (entropyTrace A - C + spectralWeight A hB.1 k * t) / Real.log 2 ≤
      regularizedObjectiveBits A B eps := by
    rw [regularizedObjectiveBits_spectral A hB.1 eps]
    apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hh := hbound eps heps heps1
    have hlog : Real.log eps = -t := Real.log_exp _
    rw [hlog] at hh
    linarith
  have hm : (regularizedObjectiveBits A B eps : EReal) ≤ sSup (regularizedValues A B) :=
    le_sSup ⟨eps, heps, rfl⟩
  exact not_lt_of_ge hm (hb.trans (EReal.coe_lt_coe_iff.mpr (hlarge.trans_le hobj)))

theorem relativeEntropyBits_eq_sSup_regularized {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    relativeEntropyBits A B = sSup (regularizedValues A B) := by
  have hupper : sSup (regularizedValues A B) ≤ relativeEntropyBits A B := by
    apply sSup_le
    rintro z ⟨eps, heps, rfl⟩
    exact regularizedObjectiveBits_le_relativeEntropyBits hA hB heps
  apply le_antisymm _ hupper
  by_cases hs : HasSupportIn A B
  · simp only [relativeEntropyBits, hs, ite_true]
    have ht : Tendsto (fun eps : ℝ => (regularizedObjectiveBits A B eps : EReal))
        (𝓝[>] (0 : ℝ)) (𝓝 (finiteRelativeEntropyBits A B : EReal)) :=
      (continuous_coe_real_ereal.continuousAt.tendsto.comp
      (regularizedObjectiveBits_tendsto_of_support hA hB hs)).mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with eps heps
    exact le_sSup ⟨eps, heps, rfl⟩
  · rw [sSup_regularizedValues_eq_top_of_support_failure hA hB hs]
    exact le_top

theorem regularizedReference_posDef {B : Mat I} (hB : B.PosSemidef)
    {eps : ℝ} (heps : 0 < eps) : (B + eps • (1 : Mat I)).PosDef :=
  Matrix.PosDef.posSemidef_add hB (Matrix.PosDef.one.smul heps)

theorem tendsto_shiftedLogCFC {α : Type*} {l : Filter α}
    {X : α → Mat I} {B : Mat I} (hX : Tendsto X l (𝓝 B))
    (hPSD : ∀ᶠ a in l, (X a).PosSemidef) (hB : B.PosSemidef)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun a => cfc Real.log (X a + eps • (1 : Mat I))) l
      (𝓝 (cfc Real.log (B + eps • (1 : Mat I)))) := by
  let r : ℝ := (‖B‖ + 1) * ‖(1 : Mat I)‖
  have hn : ∀ᶠ a in l, ‖X a‖ < ‖B‖ + 1 :=
    hX.norm.eventually (Iio_mem_nhds (lt_add_one ‖B‖))
  have hspectrum : ∀ᶠ a in l, spectrum ℝ (X a) ⊆ Icc 0 r := by
    filter_upwards [hn, hPSD] with a ha hPa
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hPa.nonneg hx
    have hb := (spectrum.subset_closedBall_norm_mul (X a) hx)
    have hxR : x ≤ ‖X a‖ * ‖(1 : Mat I)‖ := by
      simpa [Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg hx0] using hb
    exact ⟨hx0, hxR.trans (mul_le_mul_of_nonneg_right ha.le (norm_nonneg _))⟩
  have hspectrumB : spectrum ℝ B ⊆ Icc 0 r := by
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hB.nonneg hx
    have hb := spectrum.subset_closedBall_norm_mul B hx
    have hxR : x ≤ ‖B‖ * ‖(1 : Mat I)‖ := by
      simpa [Metric.mem_closedBall, Real.dist_eq, abs_of_nonneg hx0] using hb
    exact ⟨hx0, hxR.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))⟩
  have hf : ContinuousOn (fun x : ℝ => Real.log (x + eps)) (Icc 0 r) := by
    apply ContinuousOn.log (continuousOn_id.add continuousOn_const)
    intro x hx
    exact (add_pos_of_nonneg_of_pos hx.1 heps).ne'
  have ht := hX.cfc isCompact_Icc (fun x : ℝ => Real.log (x + eps)) hspectrum
    (hPSD.mono (fun _ h => h.1.isSelfAdjoint)) hspectrumB hB.1.isSelfAdjoint hf
  rw [← shifted_log_cfc hB.1 eps] at ht
  apply ht.congr'
  filter_upwards [hPSD] with a ha
  exact (shifted_log_cfc ha.1 eps).symm

theorem tendsto_regularizedObjectiveBits {α : Type*} {l : Filter α}
    {rho sigma : Mat I} {rhoSeq sigmaSeq : α → Mat I}
    (hRhoLim : Tendsto rhoSeq l (𝓝 rho)) (hSigmaLim : Tendsto sigmaSeq l (𝓝 sigma))
    (hRhoHerm : ∀ᶠ a in l, (rhoSeq a).IsHermitian) (hRho : rho.IsHermitian)
    (hSigmaPSD : ∀ᶠ a in l, (sigmaSeq a).PosSemidef) (hSigma : sigma.PosSemidef)
    {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun a => regularizedObjectiveBits (rhoSeq a) (sigmaSeq a) eps) l
      (𝓝 (regularizedObjectiveBits rho sigma eps)) := by
  have hent := tendsto_entropyTrace hRhoLim hRhoHerm hRho
  have hlog := tendsto_shiftedLogCFC hSigmaLim hSigmaPSD hSigma heps
  have ht : Continuous (fun M : Mat I => M.trace.re) := by fun_prop
  have hp := ht.continuousAt.tendsto.comp (hRhoLim.mul hlog)
  exact (hent.sub hp).div_const (Real.log 2)

theorem continuousOn_regularizedObjectiveBits {eps : ℝ} (heps : 0 < eps) :
    ContinuousOn (fun p : Mat I × Mat I => regularizedObjectiveBits p.1 p.2 eps)
      {p | p.1.PosSemidef ∧ p.2.PosSemidef} := by
  intro p hp
  apply tendsto_regularizedObjectiveBits
  · exact continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · exact continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact hq.1.1
  · exact hp.1.1
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact hq.2
  · exact hp.2
  · exact heps

theorem relativeEntropyBits_eq_iSup_regularized {A B : Mat I}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    relativeEntropyBits A B =
      ⨆ eps : {t : ℝ // 0 < t}, (regularizedObjectiveBits A B eps.val : EReal) := by
  have heq : regularizedValues A B = Set.range
      (fun eps : {t : ℝ // 0 < t} => (regularizedObjectiveBits A B eps.val : EReal)) := by
    ext z
    constructor
    · rintro ⟨eps, heps, hz⟩
      exact ⟨⟨eps, heps⟩, hz.symm⟩
    · rintro ⟨eps, hz⟩
      exact ⟨eps.val, eps.prop, hz.symm⟩
  rw [relativeEntropyBits_eq_sSup_regularized hA hB, heq, sSup_range]

theorem lowerSemicontinuousOn_relativeEntropyBits :
    LowerSemicontinuousOn (fun p : Mat I × Mat I => relativeEntropyBits p.1 p.2)
      {p | p.1.PosSemidef ∧ p.2.PosSemidef} := by
  have hsup : LowerSemicontinuousOn
      (fun p : Mat I × Mat I =>
        ⨆ eps : {t : ℝ // 0 < t}, (regularizedObjectiveBits p.1 p.2 eps.val : EReal))
      {p | p.1.PosSemidef ∧ p.2.PosSemidef} :=
    lowerSemicontinuousOn_iSup (fun eps =>
      (continuous_coe_real_ereal.comp_continuousOn
        (continuousOn_regularizedObjectiveBits eps.prop)).lowerSemicontinuousOn)
  intro p hp z hz
  have hpEq := relativeEntropyBits_eq_iSup_regularized hp.1 hp.2
  have hz' : z < ⨆ eps : {t : ℝ // 0 < t},
      (regularizedObjectiveBits p.1 p.2 eps.val : EReal) := hpEq ▸ hz
  filter_upwards [hsup p hp z hz', self_mem_nhdsWithin] with q hq hqS
  exact (relativeEntropyBits_eq_iSup_regularized hqS.1 hqS.2).symm ▸ hq

theorem lowerSemicontinuousOn_relativeEntropyBits_density :
    LowerSemicontinuousOn (fun p : Mat I × Mat I => relativeEntropyBits p.1 p.2)
      {p | IsDensity p.1 ∧ p.2.PosSemidef} :=
  (lowerSemicontinuousOn_relativeEntropyBits (I := I)).mono (fun _ hp => ⟨hp.1.1, hp.2⟩)

theorem relativeEntropyBits_le_liminf
    {α : Type*} {l : Filter α} [NeBot l]
    {rho sigma : Mat I} {rhoSeq sigmaSeq : α → Mat I}
    (hRho : rho.PosSemidef) (hSigma : sigma.PosSemidef)
    (hRhoSeq : ∀ a, (rhoSeq a).PosSemidef)
    (hSigmaSeq : ∀ a, (sigmaSeq a).PosSemidef)
    (hRhoLim : Tendsto rhoSeq l (𝓝 rho))
    (hSigmaLim : Tendsto sigmaSeq l (𝓝 sigma)) :
    relativeEntropyBits rho sigma ≤
      Filter.liminf (fun a => relativeEntropyBits (rhoSeq a) (sigmaSeq a)) l := by
  let S : Set (Mat I × Mat I) := {p | p.1.PosSemidef ∧ p.2.PosSemidef}
  let f : Mat I × Mat I → EReal := fun p => relativeEntropyBits p.1 p.2
  let v : α → Mat I × Mat I := fun a => (rhoSeq a, sigmaSeq a)
  have hv : Tendsto v l (𝓝[S] (rho, sigma)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hRhoLim.prodMk_nhds hSigmaLim,
      Filter.Eventually.of_forall (fun a => ⟨hRhoSeq a, hSigmaSeq a⟩)⟩
  have hsc : LowerSemicontinuousWithinAt f S (rho, sigma) :=
    lowerSemicontinuousOn_relativeEntropyBits (I := I) (rho, sigma) ⟨hRho, hSigma⟩
  have hf : f (rho, sigma) ≤ Filter.liminf f (𝓝[S] (rho, sigma)) :=
    LowerSemicontinuousWithinAt.le_liminf hsc
  exact hf.trans hv.liminf_le_liminf_comp

theorem relativeEntropyBits_le_liminf_atTop
    {rho sigma : Mat I} {rhoSeq sigmaSeq : ℕ → Mat I}
    (hRho : rho.PosSemidef) (hSigma : sigma.PosSemidef)
    (hRhoSeq : ∀ n, (rhoSeq n).PosSemidef)
    (hSigmaSeq : ∀ n, (sigmaSeq n).PosSemidef)
    (hRhoLim : Tendsto rhoSeq atTop (𝓝 rho))
    (hSigmaLim : Tendsto sigmaSeq atTop (𝓝 sigma)) :
    relativeEntropyBits rho sigma ≤
      Filter.liminf (fun n => relativeEntropyBits (rhoSeq n) (sigmaSeq n)) atTop :=
  relativeEntropyBits_le_liminf hRho hSigma hRhoSeq hSigmaSeq hRhoLim hSigmaLim

theorem exists_minimizing_pair
    {A B : Set (Mat I)} (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAc : IsCompact A) (hBc : IsCompact B)
    (hA : ∀ rho ∈ A, rho.PosSemidef) (hB : ∀ sigma ∈ B, sigma.PosSemidef) :
    ∃ rho ∈ A, ∃ sigma ∈ B, relativeEntropyBits rho sigma =
      sInf {z | ∃ rho ∈ A, ∃ sigma ∈ B, z = relativeEntropyBits rho sigma} := by
  have hsc : LowerSemicontinuousOn
      (fun p : Mat I × Mat I => relativeEntropyBits p.1 p.2) (A ×ˢ B) :=
    (lowerSemicontinuousOn_relativeEntropyBits (I := I)).mono
      (fun p hp => ⟨hA p.1 hp.1, hB p.2 hp.2⟩)
  obtain ⟨p, hp, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn (hAne.prod hBne) (hAc.prod hBc) hsc
  refine ⟨p.1, hp.1, p.2, hp.2, le_antisymm ?_ ?_⟩
  · apply le_sInf
    rintro z ⟨rho, hrho, sigma, hsigma, rfl⟩
    exact (isMinOn_iff.mp hmin) (rho, sigma) ⟨hrho, hsigma⟩
  · exact sInf_le ⟨p.1, hp.1, p.2, hp.2, rfl⟩

theorem exists_minimizing_pair_density
    {A B : Set (Mat I)} (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hAc : IsCompact A) (hBc : IsCompact B)
    (hA : ∀ rho ∈ A, IsDensity rho) (hB : ∀ sigma ∈ B, sigma.PosSemidef) :
    ∃ rho ∈ A, ∃ sigma ∈ B, relativeEntropyBits rho sigma =
      sInf {z | ∃ rho ∈ A, ∃ sigma ∈ B, z = relativeEntropyBits rho sigma} :=
  exists_minimizing_pair hAne hBne hAc hBc (fun rho hrho => (hA rho hrho).1) hB

end QuantumProver.QuantumRelativeEntropyContinuity
