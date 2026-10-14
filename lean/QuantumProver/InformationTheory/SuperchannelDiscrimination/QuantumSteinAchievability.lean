import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.Definitions
import QuantumProver.InformationTheory.SuperchannelDiscrimination.PetzTensorTail
import QuantumProver.InformationTheory.SuperchannelDiscrimination.QuantumTestingPowerBound

set_option autoImplicit false

noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

namespace QuantumProver.SuperchannelDiscrimination.QuantumSteinAchievability

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
theorem effect_complement {E : Matrix I I ℂ} (hE : FlaggedStates.IsEffect E) :
    FlaggedStates.IsEffect (1 - E) :=
  ⟨hE.2, by simpa using hE.1⟩

theorem acceptanceProbability_complement {ρ E : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) :
    FlaggedStates.acceptanceProbability ρ (1 - E) =
      1 - FlaggedStates.acceptanceProbability ρ E := by
  simp [FlaggedStates.acceptanceProbability, Matrix.mul_sub, hρ.2]

def binaryTestOfEffect (ρ σ : Matrix I I ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    (E : Matrix I I ℂ) (hE : FlaggedStates.IsEffect E) : BinaryTest where
  alpha := FlaggedStates.acceptanceProbability ρ (1 - E)
  beta := FlaggedStates.acceptanceProbability σ E
  alpha_nonneg := (FlaggedStates.acceptanceProbability_bounds hρ (effect_complement hE)).1
  alpha_le_one := (FlaggedStates.acceptanceProbability_bounds hρ (effect_complement hE)).2
  beta_nonneg := (FlaggedStates.acceptanceProbability_bounds hσ hE).1
  beta_le_one := (FlaggedStates.acceptanceProbability_bounds hσ hE).2

@[simp] theorem binaryTestOfEffect_alpha (ρ σ : Matrix I I ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    (E : Matrix I I ℂ) (hE : FlaggedStates.IsEffect E) :
    (binaryTestOfEffect ρ σ hρ hσ E hE).alpha =
      FlaggedStates.acceptanceProbability ρ (1 - E) := rfl

@[simp] theorem binaryTestOfEffect_beta (ρ σ : Matrix I I ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    (E : Matrix I I ℂ) (hE : FlaggedStates.IsEffect E) :
    (binaryTestOfEffect ρ σ hρ hσ E hE).beta =
      FlaggedStates.acceptanceProbability σ E := rfl

theorem positiveSpectralTest_product_posSemidef {H : Matrix I I ℂ}
    (hH : H.IsHermitian) :
    (H * PetzTensorTail.positiveSpectralTest H).PosSemidef := by
  have hprod : H * PetzTensorTail.positiveSpectralTest H =
      cfc (fun x : ℝ => x * PetzTensorTail.positiveIndicator x) H := by
    calc
      H * PetzTensorTail.positiveSpectralTest H =
          cfc (fun x : ℝ => x) H * cfc PetzTensorTail.positiveIndicator H := by
        rw [cfc_id' (p := IsSelfAdjoint) ℝ H hH]
        rfl
      _ = cfc (fun x : ℝ => x * PetzTensorTail.positiveIndicator x) H :=
        (cfc_mul (p := IsSelfAdjoint) (fun x : ℝ => x)
          PetzTensorTail.positiveIndicator H
          (H.finite_real_spectrum.continuousOn _)
          (H.finite_real_spectrum.continuousOn _)).symm
  rw [hprod]
  apply (show (0 : Matrix I I ℂ) ≤ cfc
    (fun x : ℝ => x * PetzTensorTail.positiveIndicator x) H from ?_).posSemidef
  apply cfc_nonneg (p := IsSelfAdjoint)
  intro x hx
  unfold PetzTensorTail.positiveIndicator
  split_ifs with hpos
  · simpa using hpos.le
  · simp

theorem neymanPearson_isEffect {ρ σ : Matrix I I ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (t : ℝ) :
    FlaggedStates.IsEffect (PetzTensorTail.spectralUpperTail ρ σ t) :=
  PetzTensorTail.positiveSpectralTest_isEffect (hρ.sub (hσ.smul (IsSelfAdjoint.all t)))

theorem neymanPearson_weighted_beta_le {ρ σ : Matrix I I ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (t : ℝ) :
    t * FlaggedStates.acceptanceProbability σ (PetzTensorTail.spectralUpperTail ρ σ t) ≤
      FlaggedStates.acceptanceProbability ρ (PetzTensorTail.spectralUpperTail ρ σ t) := by
  have hp := positiveSpectralTest_product_posSemidef
    (hρ.sub (hσ.smul (IsSelfAdjoint.all t)))
  have htrace := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  change 0 ≤ ((ρ - t • σ) * PetzTensorTail.spectralUpperTail ρ σ t).trace.re at htrace
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.smul_re, smul_eq_mul] at htrace
  dsimp [FlaggedStates.acceptanceProbability]
  linarith

theorem neymanPearson_beta_le_inv {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.IsHermitian) {t : ℝ} (ht : 0 < t) :
    FlaggedStates.acceptanceProbability σ (PetzTensorTail.spectralUpperTail ρ σ t) ≤ 1 / t := by
  apply (le_div_iff₀ ht).mpr
  rw [mul_comm]
  exact (neymanPearson_weighted_beta_le hρ.1.1 hσ t).trans
    (FlaggedStates.acceptanceProbability_bounds hρ (neymanPearson_isEffect hρ.1.1 hσ t)).2

def iidStrategyFamily (ρ σ : Matrix I I ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ) : StrategyFamily :=
  fun n => Set.range fun E : {E : Matrix (TensorPinching.RecursiveRows I n)
      (TensorPinching.RecursiveRows I n) ℂ // FlaggedStates.IsEffect E} =>
    binaryTestOfEffect (TensorPinching.recursiveTensorPower ρ n)
      (TensorPinching.recursiveTensorPower σ n)
      (PetzTensorTail.recursiveTensorPower_density hρ n)
      (PetzTensorTail.recursiveTensorPower_density hσ n) E.val E.property

theorem iidStrategyFamily_hasAcceptAll (ρ σ : Matrix I I ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ) :
    HasAcceptAll (iidStrategyFamily ρ σ hρ hσ) := by
  intro n
  refine ⟨⟨1, Matrix.PosSemidef.one, by rw [sub_self]; exact Matrix.PosSemidef.zero⟩, ?_⟩
  unfold binaryTestOfEffect acceptAll
  simp [FlaggedStates.acceptanceProbability,
    (PetzTensorTail.recursiveTensorPower_density hσ n).2]

def iidNeymanPearsonEffect (ρ σ : Matrix I I ℂ) (R : ℝ) (n : ℕ) :
    Matrix (TensorPinching.RecursiveRows I n) (TensorPinching.RecursiveRows I n) ℂ :=
  PetzTensorTail.spectralUpperTail (TensorPinching.recursiveTensorPower ρ n)
    (TensorPinching.recursiveTensorPower σ n) (Real.exp ((n : ℝ) * R))

theorem iidNeymanPearsonEffect_isEffect {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ) (R : ℝ) (n : ℕ) :
    FlaggedStates.IsEffect (iidNeymanPearsonEffect ρ σ R n) :=
  neymanPearson_isEffect (PetzTensorTail.recursiveTensorPower_density hρ n).1.1
    (PetzTensorTail.recursiveTensorPower_density hσ n).1.1 _

def iidNeymanPearsonTest (ρ σ : Matrix I I ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ) (R : ℝ) (n : ℕ) :
    BinaryTest :=
  binaryTestOfEffect (TensorPinching.recursiveTensorPower ρ n)
    (TensorPinching.recursiveTensorPower σ n)
    (PetzTensorTail.recursiveTensorPower_density hρ n)
    (PetzTensorTail.recursiveTensorPower_density hσ n)
    (iidNeymanPearsonEffect ρ σ R n) (iidNeymanPearsonEffect_isEffect hρ hσ R n)

theorem iidNeymanPearsonTest_mem (ρ σ : Matrix I I ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ) (R : ℝ) (n : ℕ) :
    iidNeymanPearsonTest ρ σ hρ hσ R n ∈ iidStrategyFamily ρ σ hρ hσ n :=
  ⟨⟨_, iidNeymanPearsonEffect_isEffect hρ hσ R n⟩, rfl⟩

theorem iidNeymanPearsonTest_beta_le (ρ σ : Matrix I I ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ) (R : ℝ) (n : ℕ) :
    (iidNeymanPearsonTest ρ σ hρ hσ R n).beta ≤ Real.exp (-(n : ℝ) * R) := by
  have hb := neymanPearson_beta_le_inv (PetzTensorTail.recursiveTensorPower_density hρ n)
    (PetzTensorTail.recursiveTensorPower_density hσ n).1.1
    (Real.exp_pos ((n : ℝ) * R))
  simpa [iidNeymanPearsonTest, binaryTestOfEffect, iidNeymanPearsonEffect,
    one_div, ← Real.exp_neg, neg_mul] using hb

theorem negLogTwo_exp_nats (c : ℝ) :
    negLogTwo (ENNReal.ofReal (Real.exp (-c))) = ((c / Real.log 2 : ℝ) : EReal) := by
  rw [negLogTwo_ofReal (Real.exp_pos _), Real.log_exp, neg_neg]

theorem testPositiveBlockRate_ge_of_beta_exp {T : BinaryTest} {R : ℝ} (k : ℕ)
    (hbeta : T.beta ≤ Real.exp (-((k + 1 : ℕ) : ℝ) * R)) :
    ((R / Real.log 2 : ℝ) : EReal) ≤ testPositiveBlockRate T k := by
  have hn : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hs := negLogTwo_antitone (ENNReal.ofReal_le_ofReal hbeta)
  rw [show -((k + 1 : ℕ) : ℝ) * R = -(((k + 1 : ℕ) : ℝ) * R) by ring,
    negLogTwo_exp_nats] at hs
  have hmul := mul_le_mul_of_nonneg_right hs
    (show (0 : EReal) ≤ ((1 / ((k + 1 : ℕ) : ℝ) : ℝ) : EReal) from
      EReal.coe_nonneg.mpr (by positivity))
  have heq : (((((k + 1 : ℕ) : ℝ) * R / Real.log 2 : ℝ) : EReal) *
      ((1 / ((k + 1 : ℕ) : ℝ) : ℝ) : EReal)) = ((R / Real.log 2 : ℝ) : EReal) := by
    rw [← EReal.coe_mul]
    congr 1
    field_simp
  rw [heq] at hmul
  exact hmul

theorem le_orderedSteinExponent_of_testSequence {S : StrategyFamily}
    (T : ℕ → BinaryTest) (hmem : ∀ n, T n ∈ S n)
    (halpha : Tendsto (fun n => (T n).alpha) atTop (𝓝 0)) {R : ℝ}
    (hbeta : ∀ n, (T n).beta ≤ Real.exp (-(n : ℝ) * R)) :
    ((R / Real.log 2 : ℝ) : EReal) ≤ orderedSteinExponent S := by
  apply le_orderedSteinExponent_of_eventual_tests
  intro epsilon hepsilon
  have ha : ∀ᶠ n in atTop, (T n).alpha < epsilon :=
    halpha.eventually (eventually_lt_nhds hepsilon.1)
  rcases Filter.eventually_atTop.mp ha with ⟨N, hN⟩
  filter_upwards [Filter.eventually_ge_atTop N] with k hk
  refine ⟨T (k + 1), ⟨hmem _, (hN _ (by omega)).le⟩, ?_⟩
  exact testPositiveBlockRate_ge_of_beta_exp k (hbeta (k + 1))

theorem exists_negative_moment_gap {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) {R : ℝ}
    (hR : R < PetzMoments.relativeEntropyNats ρ σ) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ 0 < PetzMoments.petzMoment ρ σ (-s) ∧
      s * R + Real.log (PetzMoments.petzMoment ρ σ (-s)) < 0 := by
  have hlim := (PetzMoments.log_petzMoment_div_tendsto hρ hσ).mono_left
    (nhdsLT_le_nhdsNE (0 : ℝ))
  have hquot := hlim.eventually (eventually_gt_nhds hR)
  have hpos := (PetzMoments.petzMoment_eventually_pos hρ hσ).filter_mono
    (nhdsWithin_le_nhds : 𝓝[<] (0 : ℝ) ≤ 𝓝 0)
  have hlo : ∀ᶠ u : ℝ in 𝓝[<] 0, -1 < u :=
    (eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)).filter_mono nhdsWithin_le_nhds
  have hneg : ∀ᶠ u : ℝ in 𝓝[<] 0, u < 0 := self_mem_nhdsWithin
  rcases (hquot.and (hpos.and (hlo.and hneg))).exists with ⟨u, huq, hup, hul, hun⟩
  refine ⟨-u, by linarith, by linarith, by simpa using hup, ?_⟩
  have hlog := (lt_div_iff_of_neg hun).mp huq
  simp only [neg_neg]
  nlinarith

theorem exp_moment_bound_eq_geometric {m : ℝ} (hm : 0 < m)
    (R s : ℝ) (n : ℕ) :
    Real.exp ((n : ℝ) * R) ^ s * m ^ n =
      Real.exp (s * R + Real.log m) ^ n := by
  rw [← Real.exp_mul]
  have hexp : Real.exp (((n : ℝ) * R) * s) = Real.exp (s * R) ^ n := by
    rw [show ((n : ℝ) * R) * s = (n : ℝ) * (s * R) by ring,
      Real.exp_nat_mul]
  rw [hexp, ← mul_pow, Real.exp_add, Real.exp_log hm]

theorem negative_moment_bound_tendsto {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) {R : ℝ}
    (hR : R < PetzMoments.relativeEntropyNats ρ σ) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * R) ^ s *
        (PetzMoments.petzMoment ρ σ (-s)) ^ n) atTop (𝓝 0) := by
  rcases exists_negative_moment_gap hρ hσ hR with ⟨s, hs0, hs1, hm, hgap⟩
  refine ⟨s, hs0, hs1, ?_⟩
  have hq := tendsto_pow_atTop_nhds_zero_of_lt_one
    (Real.exp_pos (s * R + Real.log (PetzMoments.petzMoment ρ σ (-s)))).le
    (Real.exp_lt_one_iff.mpr hgap)
  convert hq using 1
  funext n
  exact exp_moment_bound_eq_geometric hm R s n

theorem le_of_all_strict_nats_rates {D : ℝ} {z : EReal}
    (h : ∀ R : ℝ, R < D → ((R / Real.log 2 : ℝ) : EReal) ≤ z) :
    ((D / Real.log 2 : ℝ) : EReal) ≤ z := by
  by_contra hz
  rcases EReal.exists_between_coe_real (lt_of_not_ge hz) with ⟨r, hzr, hrD⟩
  have hr : r < D / Real.log 2 := EReal.coe_lt_coe_iff.mp hrD
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hR : r * Real.log 2 < D := (lt_div_iff₀ hlog).mp hr
  have hbound := h (r * Real.log 2) hR
  rw [mul_div_cancel_right₀ r (ne_of_gt hlog)] at hbound
  exact (not_le_of_gt hzr hbound).elim

theorem iidNeymanPearsonTest_alpha_le (ρ σ : Matrix I I ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    (R s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ) :
    (iidNeymanPearsonTest ρ σ hρ hσ R n).alpha ≤
      Real.exp ((n : ℝ) * R) ^ s * (PetzMoments.petzMoment ρ σ (-s)) ^ n := by
  have h := QuantumTestingPowerBound.np_typeI_le_petzMoment
    (PetzTensorTail.recursiveTensorPower_density hρ n).1
    (PetzTensorTail.recursiveTensorPower_density hσ n).1
    (Real.exp ((n : ℝ) * R)) s (Real.exp_pos _) hs0 hs1
  rw [PetzTensorTail.recursiveTensorMoment_power hρ.1 hσ.1 n (-s)] at h
  exact h

theorem iidNeymanPearsonTest_exponential_errors (ρ σ : Matrix I I ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    (hσPD : σ.PosDef) {R : ℝ} (hR : R < PetzMoments.relativeEntropyNats ρ σ) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      (∀ n, (iidNeymanPearsonTest ρ σ hρ hσ R n).alpha ≤ q ^ n) ∧
      (∀ n, (iidNeymanPearsonTest ρ σ hρ hσ R n).beta ≤ Real.exp (-(n : ℝ) * R)) := by
  rcases exists_negative_moment_gap hρ hσPD hR with ⟨s, hs0, hs1, hm, hgap⟩
  refine ⟨Real.exp (s * R + Real.log (PetzMoments.petzMoment ρ σ (-s))),
    Real.exp_pos _, Real.exp_lt_one_iff.mpr hgap, ?_,
    iidNeymanPearsonTest_beta_le ρ σ hρ hσ R⟩
  intro n
  exact (iidNeymanPearsonTest_alpha_le ρ σ hρ hσ R s hs0 hs1 n).trans_eq
    (exp_moment_bound_eq_geometric hm R s n)

theorem iidNeymanPearsonTest_alpha_tendsto (ρ σ : Matrix I I ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    (hσPD : σ.PosDef) {R : ℝ} (hR : R < PetzMoments.relativeEntropyNats ρ σ) :
    Tendsto (fun n => (iidNeymanPearsonTest ρ σ hρ hσ R n).alpha) atTop (𝓝 0) := by
  rcases iidNeymanPearsonTest_exponential_errors ρ σ hρ hσ hσPD hR with
    ⟨q, hq0, hq1, ha, _⟩
  exact squeeze_zero (fun n => (iidNeymanPearsonTest ρ σ hρ hσ R n).alpha_nonneg) ha
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1)

theorem iid_strict_rate_le_orderedSteinExponent (ρ σ : Matrix I I ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    (hσPD : σ.PosDef) {R : ℝ} (hR : R < PetzMoments.relativeEntropyNats ρ σ) :
    ((R / Real.log 2 : ℝ) : EReal) ≤ orderedSteinExponent (iidStrategyFamily ρ σ hρ hσ) :=
  le_orderedSteinExponent_of_testSequence (iidNeymanPearsonTest ρ σ hρ hσ R)
    (iidNeymanPearsonTest_mem ρ σ hρ hσ R)
    (iidNeymanPearsonTest_alpha_tendsto ρ σ hρ hσ hσPD hR)
    (iidNeymanPearsonTest_beta_le ρ σ hρ hσ R)

theorem relativeEntropyBits_le_iid_orderedSteinExponent (ρ σ : Matrix I I ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    (hσPD : σ.PosDef) :
    FlaggedStates.relativeEntropyBits ρ σ ≤ orderedSteinExponent (iidStrategyFamily ρ σ hρ hσ) := by
  rw [PetzMoments.relativeEntropyBits_eq_nats_of_posDef hσPD]
  apply le_of_all_strict_nats_rates
  intro R hR
  exact iid_strict_rate_le_orderedSteinExponent ρ σ hρ hσ hσPD hR

theorem iid_bits_rate_achievability (ρ σ : Matrix I I ℂ)
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    (hσPD : σ.PosDef) {r : ℝ} (hr : (r : EReal) < FlaggedStates.relativeEntropyBits ρ σ) :
    Tendsto (fun n => (iidNeymanPearsonTest ρ σ hρ hσ (r * Real.log 2) n).alpha)
      atTop (𝓝 0) ∧
    (∀ n, iidNeymanPearsonTest ρ σ hρ hσ (r * Real.log 2) n ∈
      iidStrategyFamily ρ σ hρ hσ n) ∧
    (∀ n, (iidNeymanPearsonTest ρ σ hρ hσ (r * Real.log 2) n).beta ≤
      (2 : ℝ) ^ (-(n : ℝ) * r)) := by
  rw [PetzMoments.relativeEntropyBits_eq_nats_of_posDef hσPD] at hr
  have hR : r * Real.log 2 < PetzMoments.relativeEntropyNats ρ σ :=
    (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
      (EReal.coe_lt_coe_iff.mp hr)
  refine ⟨iidNeymanPearsonTest_alpha_tendsto ρ σ hρ hσ hσPD hR,
    iidNeymanPearsonTest_mem ρ σ hρ hσ (r * Real.log 2), ?_⟩
  intro n
  have heq : (2 : ℝ) ^ (-(n : ℝ) * r) =
      Real.exp (-(n : ℝ) * (r * Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [heq]
  exact iidNeymanPearsonTest_beta_le ρ σ hρ hσ (r * Real.log 2) n

end QuantumProver.SuperchannelDiscrimination.QuantumSteinAchievability
