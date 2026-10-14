import QuantumProver.InformationTheory.Equipartition.MeasuredRenyiTensorization
import QuantumProver.InformationTheory.MeasuredRelativeEntropyVariational

set_option autoImplicit false

noncomputable section

open Filter Set Topology Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
open QuantumProver.Equipartition.FiniteModel
open QuantumProver.Equipartition.FiniteModel.Testing
open QuantumProver.Equipartition.FiniteModel.PolarTensor

namespace QuantumProver.MeasuredRenyiVariational

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]

def renyiExponent (alpha : ℝ) : ℝ := (alpha - 1) / alpha

def scalarObjective (alpha p q t : ℝ) : ℝ :=
  alpha * p * t ^ (renyiExponent alpha) + (1 - alpha) * q * t

def scalarTrace (alpha p q : ℝ) : ℝ :=
  p ^ alpha * q ^ (1 - alpha)

theorem scalarTrace_le_objective {alpha p q t : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) (hp : 0 ≤ p) (hq : 0 ≤ q) (ht : 0 < t) :
    scalarTrace alpha p q ≤ scalarObjective alpha p q t := by
  have he : renyiExponent alpha * alpha + (1 - alpha) = 0 := by
    unfold renyiExponent
    field_simp [ha.ne']
    ring
  have hprod :
      (p * t ^ (renyiExponent alpha)) ^ alpha * (q * t) ^ (1 - alpha) =
        scalarTrace alpha p q := by
    rw [Real.mul_rpow hp (Real.rpow_nonneg ht.le _), Real.mul_rpow hq ht.le,
      ← Real.rpow_mul ht.le]
    calc
      _ = (p ^ alpha * q ^ (1 - alpha)) *
          (t ^ (renyiExponent alpha * alpha) * t ^ (1 - alpha)) := by ring
      _ = scalarTrace alpha p q := by
        rw [← Real.rpow_add ht, he, Real.rpow_zero, mul_one]
        rfl
  have h := Real.geom_mean_le_arith_mean2_weighted ha.le (by linarith : 0 ≤ 1 - alpha)
    (mul_nonneg hp (Real.rpow_nonneg ht.le (renyiExponent alpha))) (mul_nonneg hq ht.le)
    (by ring : alpha + (1 - alpha) = 1)
  rw [hprod] at h
  simpa only [scalarObjective, mul_assoc] using h

theorem scalarObjective_optimum {alpha p q : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) (hp : 0 < p) (hq : 0 < q) :
    scalarObjective alpha p q ((p / q) ^ alpha) = scalarTrace alpha p q := by
  have he : alpha * renyiExponent alpha = alpha - 1 := by
    unfold renyiExponent
    field_simp [ha.ne']
  have hpow : ((p / q) ^ alpha) ^ (renyiExponent alpha) =
      (p / q) ^ (alpha - 1) := by
    rw [← Real.rpow_mul (div_pos hp hq).le, he]
  have hqpow : q ^ alpha ≠ 0 := (Real.rpow_pos_of_pos hq alpha).ne'
  have hp1 : p * (p / q) ^ (alpha - 1) = scalarTrace alpha p q := by
    rw [Real.div_rpow hp.le hq.le, Real.rpow_sub hp, Real.rpow_sub hq,
      scalarTrace, Real.rpow_sub hq, Real.rpow_one, Real.rpow_one]
    field_simp [hp.ne', hq.ne', hqpow] <;> ring
  have hp2 : q * (p / q) ^ alpha = scalarTrace alpha p q := by
    rw [Real.div_rpow hp.le hq.le, scalarTrace, Real.rpow_sub hq, Real.rpow_one]
    field_simp [hq.ne', hqpow] <;> ring
  unfold scalarObjective
  rw [hpow]
  calc
    _ = alpha * (p * (p / q) ^ (alpha - 1)) + (1 - alpha) * (q * (p / q) ^ alpha) := by ring
    _ = scalarTrace alpha p q := by rw [hp1, hp2]; ring

def epsilonTest (alpha p q eps : ℝ) : ℝ := ((p + eps) / (q + eps)) ^ alpha

theorem epsilonTest_pos {alpha p q eps : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (heps : 0 < eps) :
    0 < epsilonTest alpha p q eps :=
  Real.rpow_pos_of_pos (div_pos (add_pos_of_nonneg_of_pos hp heps)
    (add_pos_of_nonneg_of_pos hq heps)) _

theorem epsilonTest_objective_bounds {alpha p q eps : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) (hp : 0 ≤ p) (hq : 0 ≤ q) (heps : 0 < eps) :
    scalarTrace alpha p q ≤ scalarObjective alpha p q (epsilonTest alpha p q eps) ∧
      scalarObjective alpha p q (epsilonTest alpha p q eps) ≤
        scalarTrace alpha (p + eps) (q + eps) := by
  refine ⟨scalarTrace_le_objective ha ha1 hp hq (epsilonTest_pos hp hq heps), ?_⟩
  rw [← scalarObjective_optimum ha ha1
    (add_pos_of_nonneg_of_pos hp heps) (add_pos_of_nonneg_of_pos hq heps)]
  change scalarObjective alpha p q _ ≤ scalarObjective alpha (p + eps) (q + eps) _
  have ht := (epsilonTest_pos (alpha := alpha) hp hq heps).le
  have htp := Real.rpow_nonneg ht (renyiExponent alpha)
  dsimp only [scalarObjective, epsilonTest] at *
  nlinarith [mul_nonneg (mul_nonneg ha.le heps.le) htp,
    mul_nonneg (mul_nonneg (by linarith : 0 ≤ 1 - alpha) heps.le) ht]

theorem epsilonTest_objective_tendsto {alpha p q : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Tendsto (fun eps : ℝ => scalarObjective alpha p q (epsilonTest alpha p q eps))
      (𝓝[>] (0 : ℝ)) (𝓝 (scalarTrace alpha p q)) := by
  have hupper : Tendsto (fun eps : ℝ => scalarTrace alpha (p + eps) (q + eps))
      (𝓝[>] (0 : ℝ)) (𝓝 (scalarTrace alpha p q)) := by
    have hc : Continuous (fun eps : ℝ => scalarTrace alpha (p + eps) (q + eps)) := by
      unfold scalarTrace
      exact ((Real.continuous_rpow_const ha.le).comp (continuous_const.add continuous_id)).mul
        ((Real.continuous_rpow_const (by linarith : 0 ≤ 1 - alpha)).comp
          (continuous_const.add continuous_id))
    simpa only [add_zero] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [self_mem_nhdsWithin] with eps heps
    exact (epsilonTest_objective_bounds ha ha1 hp hq heps).1
  · filter_upwards [self_mem_nhdsWithin] with eps heps
    exact (epsilonTest_objective_bounds ha ha1 hp hq heps).2

def vectorObjective (alpha : ℝ) (p q r : K → ℝ) : ℝ :=
  ∑ i, scalarObjective alpha (p i) (q i) (r i)

def vectorTrace (alpha : ℝ) (p q : K → ℝ) : ℝ :=
  ∑ i, scalarTrace alpha (p i) (q i)

def vectorValues (alpha : ℝ) (p q : K → ℝ) : Set EReal :=
  {z | ∃ r : K → ℝ, (∀ i, 0 < r i) ∧ z = (vectorObjective alpha p q r : EReal)}

theorem vectorTrace_variational {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (p q : K → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    (vectorTrace alpha p q : EReal) = sInf (vectorValues alpha p q) := by
  apply le_antisymm
  · apply le_sInf
    rintro z ⟨r, hr, rfl⟩
    apply EReal.coe_le_coe_iff.mpr
    exact Finset.sum_le_sum (fun i _ => scalarTrace_le_objective ha ha1 (hp i) (hq i) (hr i))
  · have ht := tendsto_finsetSum Finset.univ
      (fun i _ => epsilonTest_objective_tendsto ha ha1 (hp i) (hq i))
    have hte : Tendsto
        (fun eps : ℝ => (vectorObjective alpha p q (fun i => epsilonTest alpha (p i) (q i) eps) : EReal))
        (𝓝[>] (0 : ℝ)) (𝓝 (vectorTrace alpha p q : EReal)) :=
      continuous_coe_real_ereal.continuousAt.tendsto.comp ht
    apply ge_of_tendsto hte
    filter_upwards [self_mem_nhdsWithin] with eps heps
    exact sInf_le ⟨(fun i => epsilonTest alpha (p i) (q i) eps),
      (fun i => epsilonTest_pos (hp i) (hq i) heps), rfl⟩

def matrixObjective (alpha : ℝ) (rho sigma W : CMat ι) : ℝ :=
  alpha * tracePair rho (matrixRpow W (renyiExponent alpha)) +
    (1 - alpha) * tracePair sigma W

def matrixValues (alpha : ℝ) (rho sigma : CMat ι) : Set EReal :=
  {z | ∃ W : CMat ι, W.PosDef ∧ z = (matrixObjective alpha rho sigma W : EReal)}

def variationalRenyiTrace (alpha : ℝ) (rho sigma : CMat ι) : EReal :=
  sInf (matrixValues alpha rho sigma)

def measuredRenyiTraceValues (alpha : ℝ) (rho sigma : CMat ι) : Set EReal :=
  {z | ∃ L : ℕ, ∃ M : FinitePOVM ι L,
    z = (classicalRenyiTrace (measurementMass M rho) (measurementMass M sigma) alpha : EReal)}

def measuredRenyiTrace (alpha : ℝ) (rho sigma : CMat ι) : EReal :=
  sInf (measuredRenyiTraceValues alpha rho sigma)

theorem tracePair_weightedObservable {L : ℕ} (M : FinitePOVM ι L)
    (A : CMat ι) (r : Fin L → ℝ) :
    tracePair A (povmWeightedObservable M r) = ∑ i, measurementMass M A i * r i := by
  simp only [povmWeightedObservable, tracePair, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    measurementMass, tracePair]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem vectorObjective_eq_weightedTraces {L : ℕ} (M : FinitePOVM ι L)
    (rho sigma : CMat ι) (alpha : ℝ) (r : Fin L → ℝ) :
    vectorObjective alpha (measurementMass M rho) (measurementMass M sigma) r =
      alpha * tracePair rho (povmWeightedObservable M (fun i => Real.rpow (r i) (renyiExponent alpha))) +
        (1 - alpha) * tracePair sigma (povmWeightedObservable M r) := by
  rw [tracePair_weightedObservable, tracePair_weightedObservable]
  simp only [vectorObjective, scalarObjective, Real.rpow_eq_pow,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem matrixObjective_le_vectorObjective {L : ℕ} (M : FinitePOVM ι L)
    {rho sigma : CMat ι} (hRho : rho.PosSemidef) {alpha : ℝ}
    (ha : (1 / 2 : ℝ) ≤ alpha) (ha1 : alpha < 1)
    (r : Fin L → ℝ) (hr : ∀ i, 0 < r i) :
    matrixObjective alpha rho sigma (povmWeightedObservable M r) ≤
      vectorObjective alpha (measurementMass M rho) (measurementMass M sigma) r := by
  have he := renyiExponent_mem ha ha1
  have hj := matrixRpow_povmWeightedObservable_le M r hr he.1 he.2
  have ht := tracePair_loewner_mono hj hRho
  rw [tracePair_comm (matrixRpow _ _) rho, tracePair_comm (povmWeightedObservable _ _) rho] at ht
  rw [vectorObjective_eq_weightedTraces]
  unfold matrixObjective
  dsimp only [renyiExponent] at *
  linarith [mul_le_mul_of_nonneg_left ht (by linarith : 0 ≤ alpha)]

def unitaryFinitePOVM (U : Matrix.unitaryGroup ι ℂ) : FinitePOVM ι (Fintype.card ι) where
  outcome j := (QuantumProver.MeasuredRelativeEntropyVariational.unitaryPOVM U).effect
    ((Fintype.equivFin ι).symm j)
  positive j := (QuantumProver.MeasuredRelativeEntropyVariational.unitaryPOVM U).positive _
  sum_outcome := ((Fintype.equivFin ι).symm.sum_comp
    (QuantumProver.MeasuredRelativeEntropyVariational.unitaryPOVM U).effect).trans
      (QuantumProver.MeasuredRelativeEntropyVariational.unitaryPOVM U).normalized

theorem unitaryFinitePOVM_trace_weighted (U : Matrix.unitaryGroup ι ℂ)
    (A : CMat ι) (r : ι → ℝ) :
    ∑ j, measurementMass (unitaryFinitePOVM U) A j * r ((Fintype.equivFin ι).symm j) =
      (A * ((U : CMat ι) *
        QuantumProver.MeasuredRelativeEntropyVariational.positiveDiagonal r * (U : CMat ι)ᴴ)).trace.re := by
  let M := QuantumProver.MeasuredRelativeEntropyVariational.unitaryPOVM U
  have hs := (Fintype.equivFin ι).symm.sum_comp (fun i : ι =>
    QuantumProver.MeasuredRelativeEntropyVariational.measurementProbability M A i * r i)
  have ht := QuantumProver.MeasuredRelativeEntropyVariational.trace_weighted_effects M A r
  rw [QuantumProver.MeasuredRelativeEntropyVariational.unitaryPOVM_weighted] at ht
  exact hs.trans ht.symm

theorem matrixObjective_eq_spectral {alpha : ℝ} {rho sigma W : CMat ι} (hW : W.PosDef) :
    matrixObjective alpha rho sigma W =
      vectorObjective alpha (measurementMass (unitaryFinitePOVM hW.1.eigenvectorUnitary) rho)
        (measurementMass (unitaryFinitePOVM hW.1.eigenvectorUnitary) sigma)
        (fun j => hW.1.eigenvalues ((Fintype.equivFin ι).symm j)) := by
  have hp : tracePair rho (matrixRpow W (renyiExponent alpha)) =
      ∑ j, measurementMass (unitaryFinitePOVM hW.1.eigenvectorUnitary) rho j *
        (hW.1.eigenvalues ((Fintype.equivFin ι).symm j)) ^ (renyiExponent alpha) := by
    rw [unitaryFinitePOVM_trace_weighted hW.1.eigenvectorUnitary rho
      (fun i : ι => hW.1.eigenvalues i ^ renyiExponent alpha)]
    unfold matrixRpow tracePair
    rw [QuantumProver.SuperchannelDiscrimination.TensorEntropy.cfc_spectral _ hW.1]
    rfl
  have hs : tracePair sigma W =
      ∑ j, measurementMass (unitaryFinitePOVM hW.1.eigenvectorUnitary) sigma j *
        hW.1.eigenvalues ((Fintype.equivFin ι).symm j) := by
    rw [unitaryFinitePOVM_trace_weighted]
    unfold tracePair
    have hrec : (hW.1.eigenvectorUnitary : CMat ι) *
        QuantumProver.MeasuredRelativeEntropyVariational.positiveDiagonal hW.1.eigenvalues *
        (hW.1.eigenvectorUnitary : CMat ι)ᴴ = W := hW.1.spectral_theorem.symm
    rw [hrec]
  rw [matrixObjective, hp, hs]
  simp only [vectorObjective, scalarObjective, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem vectorTrace_eq_classicalRenyiTrace {L : ℕ} (alpha : ℝ) (p q : Fin L → ℝ) :
    vectorTrace alpha p q = classicalRenyiTrace p q alpha := by
  simp only [vectorTrace, scalarTrace, classicalRenyiTrace, Real.rpow_eq_pow]

theorem measuredRenyiTrace_variational {rho sigma : CMat ι}
    (hRho : rho.PosSemidef) (hSigma : sigma.PosSemidef) {alpha : ℝ}
    (ha : (1 / 2 : ℝ) ≤ alpha) (ha1 : alpha < 1) :
    measuredRenyiTrace alpha rho sigma = variationalRenyiTrace alpha rho sigma := by
  have ha0 : 0 < alpha := by linarith
  apply le_antisymm
  · apply le_sInf
    rintro z ⟨W, hW, rfl⟩
    let M := unitaryFinitePOVM hW.1.eigenvectorUnitary
    let r : Fin (Fintype.card ι) → ℝ := fun j => hW.1.eigenvalues ((Fintype.equivFin ι).symm j)
    have hr : ∀ j, 0 < r j := fun j => hW.eigenvalues_pos _
    calc
      measuredRenyiTrace alpha rho sigma ≤
          (classicalRenyiTrace (measurementMass M rho) (measurementMass M sigma) alpha : EReal) :=
        sInf_le ⟨Fintype.card ι, M, rfl⟩
      _ = (vectorTrace alpha (measurementMass M rho) (measurementMass M sigma) : EReal) :=
        congrArg (fun x : ℝ => (x : EReal)) (vectorTrace_eq_classicalRenyiTrace alpha _ _).symm
      _ ≤ (vectorObjective alpha (measurementMass M rho) (measurementMass M sigma) r : EReal) := by
        apply EReal.coe_le_coe_iff.mpr
        exact Finset.sum_le_sum (fun j _ => scalarTrace_le_objective ha0 ha1
          (measurementMass_nonneg M hRho j) (measurementMass_nonneg M hSigma j) (hr j))
      _ = (matrixObjective alpha rho sigma W : EReal) :=
        congrArg (fun x : ℝ => (x : EReal)) (matrixObjective_eq_spectral hW).symm
  · apply le_sInf
    rintro z ⟨L, M, rfl⟩
    rw [← vectorTrace_eq_classicalRenyiTrace alpha,
      vectorTrace_variational ha0 ha1 _ _ (measurementMass_nonneg M hRho)
        (measurementMass_nonneg M hSigma)]
    apply le_sInf
    rintro z ⟨r, hr, rfl⟩
    calc
      variationalRenyiTrace alpha rho sigma ≤
          (matrixObjective alpha rho sigma (povmWeightedObservable M r) : EReal) :=
        sInf_le ⟨povmWeightedObservable M r, povmWeightedObservable_posDef M r hr, rfl⟩
      _ ≤ (vectorObjective alpha (measurementMass M rho) (measurementMass M sigma) r : EReal) :=
        EReal.coe_le_coe_iff.mpr (matrixObjective_le_vectorObjective M hRho ha ha1 r hr)

def logRenyiBits (alpha x : ℝ) : EReal :=
  if x = 0 then ⊤ else ((logTwo x / (alpha - 1) : ℝ) : EReal)

theorem logRenyiBits_antitone {alpha x y : ℝ} (ha1 : alpha < 1)
    (hx : 0 ≤ x) (hxy : x ≤ y) : logRenyiBits alpha y ≤ logRenyiBits alpha x := by
  by_cases hx0 : x = 0
  · simp [logRenyiBits, hx0]
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hyp : 0 < y := hxp.trans_le hxy
  simp only [logRenyiBits, hx0, hyp.ne', ite_false]
  apply EReal.coe_le_coe_iff.mpr
  have hlog : logTwo x ≤ logTwo y :=
    div_le_div_of_nonneg_right (Real.log_le_log hxp hxy)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonpos_right hlog
    (inv_nonpos.mpr (sub_nonpos.mpr ha1.le))

theorem scalarObjective_nonneg {alpha p q t : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) (hp : 0 ≤ p) (hq : 0 ≤ q) (ht : 0 < t) :
    0 ≤ scalarObjective alpha p q t := by
  unfold scalarObjective
  exact add_nonneg (mul_nonneg (mul_nonneg ha.le hp) (Real.rpow_nonneg ht.le _))
    (mul_nonneg (mul_nonneg (by linarith : 0 ≤ 1 - alpha) hq) ht.le)

theorem vectorObjective_pos {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (p q r : K → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hr : ∀ i, 0 < r i) (hsum : ∑ i, p i = 1) : 0 < vectorObjective alpha p q r := by
  have hsp : 0 < ∑ i, p i := by rw [hsum]; norm_num
  obtain ⟨k, _, hpk⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hp i)).mp hsp
  apply Finset.sum_pos' (fun i _ => scalarObjective_nonneg ha ha1 (hp i) (hq i) (hr i))
  refine ⟨k, Finset.mem_univ _, ?_⟩
  unfold scalarObjective
  exact add_pos_of_pos_of_nonneg
    (mul_pos (mul_pos ha hpk) (Real.rpow_pos_of_pos (hr k) _))
    (mul_nonneg (mul_nonneg (by linarith : 0 ≤ 1 - alpha) (hq k)) (hr k).le)

theorem vectorTrace_nonneg (alpha : ℝ) (p q : K → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) : 0 ≤ vectorTrace alpha p q := by
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (Real.rpow_nonneg (hp i) _) (Real.rpow_nonneg (hq i) _))

theorem vectorTrace_le_objective {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (p q r : K → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 < r i) :
    vectorTrace alpha p q ≤ vectorObjective alpha p q r :=
  Finset.sum_le_sum (fun i _ => scalarTrace_le_objective ha ha1 (hp i) (hq i) (hr i))

theorem vectorEpsilon_objective_tendsto {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (p q : K → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    Tendsto (fun eps : ℝ => vectorObjective alpha p q
      (fun i => epsilonTest alpha (p i) (q i) eps))
      (𝓝[>] (0 : ℝ)) (𝓝 (vectorTrace alpha p q)) :=
  tendsto_finsetSum Finset.univ (fun i _ => epsilonTest_objective_tendsto ha ha1 (hp i) (hq i))

def vectorLogValues (alpha : ℝ) (p q : K → ℝ) : Set EReal :=
  {z | ∃ r : K → ℝ, (∀ i, 0 < r i) ∧ z = logRenyiBits alpha (vectorObjective alpha p q r)}

theorem vectorLog_variational {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (p q : K → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, p i = 1) :
    logRenyiBits alpha (vectorTrace alpha p q) = sSup (vectorLogValues alpha p q) := by
  have hupper : sSup (vectorLogValues alpha p q) ≤ logRenyiBits alpha (vectorTrace alpha p q) := by
    apply sSup_le
    rintro z ⟨r, hr, rfl⟩
    exact logRenyiBits_antitone ha1 (vectorTrace_nonneg alpha p q hp hq)
      (vectorTrace_le_objective ha ha1 p q r hp hq hr)
  apply le_antisymm _ hupper
  have ht := vectorEpsilon_objective_tendsto ha ha1 p q hp hq
  by_cases hzero : vectorTrace alpha p q = 0
  · simp only [logRenyiBits, hzero, ite_true]
    by_contra hn
    obtain ⟨b, hb, _⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
    let threshold := Real.exp ((b + 1) * (alpha - 1) * Real.log 2)
    have he : ∀ᶠ eps : ℝ in 𝓝[>] 0,
        vectorObjective alpha p q (fun i => epsilonTest alpha (p i) (q i) eps) < threshold := by
      have hh : vectorTrace alpha p q < threshold := by rw [hzero]; exact Real.exp_pos _
      exact ht.eventually (Iio_mem_nhds hh)
    have hepsPos : ∀ᶠ eps : ℝ in 𝓝[>] 0, 0 < eps := self_mem_nhdsWithin
    obtain ⟨eps, heps, hsmall⟩ := (hepsPos.and he).exists
    let r : K → ℝ := fun i => epsilonTest alpha (p i) (q i) eps
    have hr : ∀ i, 0 < r i := fun i => epsilonTest_pos (hp i) (hq i) heps
    have hpos : 0 < vectorObjective alpha p q r := vectorObjective_pos ha ha1 p q r hp hq hr hsum
    have hlog : Real.log (vectorObjective alpha p q r) <
        (b + 1) * (alpha - 1) * Real.log 2 := by
      have hh := Real.log_lt_log hpos hsmall
      simpa [threshold] using hh
    have hlarge : b + 1 < logTwo (vectorObjective alpha p q r) / (alpha - 1) := by
      apply (lt_div_iff_of_neg (sub_neg.mpr ha1)).mpr
      exact (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog
    have hm : logRenyiBits alpha (vectorObjective alpha p q r) ≤ sSup (vectorLogValues alpha p q) :=
      le_sSup ⟨r, hr, rfl⟩
    simp only [logRenyiBits, hpos.ne', ite_false] at hm
    exact not_lt_of_ge hm (hb.trans (EReal.coe_lt_coe_iff.mpr (by linarith)))
  · simp only [logRenyiBits, hzero, ite_false]
    have hc : ContinuousAt (fun x : ℝ => logTwo x / (alpha - 1)) (vectorTrace alpha p q) := by
      exact (continuousAt_id.log hzero).div_const (Real.log 2) |>.div_const (alpha - 1)
    have hte := continuous_coe_real_ereal.continuousAt.tendsto.comp (hc.tendsto.comp ht)
    apply le_of_tendsto hte
    filter_upwards [self_mem_nhdsWithin] with eps heps
    let r : K → ℝ := fun i => epsilonTest alpha (p i) (q i) eps
    have hr : ∀ i, 0 < r i := fun i => epsilonTest_pos (hp i) (hq i) heps
    have hm := le_sSup (s := vectorLogValues alpha p q) ⟨r, hr, rfl⟩
    change ((logTwo (vectorObjective alpha p q r) / (alpha - 1) : ℝ) : EReal) ≤
      sSup (vectorLogValues alpha p q)
    simpa only [logRenyiBits, (vectorObjective_pos ha ha1 p q r hp hq hr hsum).ne', ite_false] using hm

theorem classicalRenyiDivergence_eq_log {L : ℕ} {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (p q : Fin L → ℝ) :
    classicalRenyiDivergence p q alpha = logRenyiBits alpha (vectorTrace alpha p q) := by
  rw [vectorTrace_eq_classicalRenyiTrace]
  simp only [classicalRenyiDivergence, logRenyiBits,
    ne_of_lt ha1, ite_false, not_lt_of_ge ha1.le, false_and,
    EReal.coe_div, EReal.coe_sub, EReal.coe_one]

theorem classicalRenyiDivergence_variational {L : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) (p q : Fin L → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, p i = 1) :
    classicalRenyiDivergence p q alpha = sSup (vectorLogValues alpha p q) := by
  rw [classicalRenyiDivergence_eq_log ha ha1]
  exact vectorLog_variational ha ha1 p q hp hq hsum

theorem matrixObjective_pos {rho sigma W : CMat ι} (hRho : IsState rho)
    (hSigma : sigma.PosSemidef) (hW : W.PosDef) {alpha : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) : 0 < matrixObjective alpha rho sigma W := by
  rw [matrixObjective_eq_spectral hW]
  exact vectorObjective_pos ha ha1 _ _ _
    (measurementMass_nonneg _ hRho.1) (measurementMass_nonneg _ hSigma)
    (fun j => hW.eigenvalues_pos _) (measurementMass_sum _ hRho)

def matrixLogValues (alpha : ℝ) (rho sigma : CMat ι) : Set EReal :=
  {z | ∃ W : CMat ι, W.PosDef ∧ z = logRenyiBits alpha (matrixObjective alpha rho sigma W)}

def variationalMeasuredDivergence (alpha : ℝ) (rho sigma : CMat ι) : EReal :=
  sSup (matrixLogValues alpha rho sigma)

theorem measuredDivergence_variational {rho sigma : CMat ι} (hRho : IsState rho)
    (hSigma : sigma.PosSemidef) {alpha : ℝ}
    (ha : (1 / 2 : ℝ) ≤ alpha) (ha1 : alpha < 1) :
    measuredDivergence rho sigma alpha = variationalMeasuredDivergence alpha rho sigma := by
  have ha0 : 0 < alpha := by linarith
  apply le_antisymm
  · apply sSup_le
    rintro z ⟨L, M, rfl⟩
    rw [classicalRenyiDivergence_variational ha0 ha1 _ _
      (measurementMass_nonneg M hRho.1) (measurementMass_nonneg M hSigma)
      (measurementMass_sum M hRho)]
    apply sSup_le
    rintro z ⟨r, hr, rfl⟩
    have hW := povmWeightedObservable_posDef M r hr
    calc
      logRenyiBits alpha (vectorObjective alpha (measurementMass M rho) (measurementMass M sigma) r) ≤
          logRenyiBits alpha (matrixObjective alpha rho sigma (povmWeightedObservable M r)) :=
        logRenyiBits_antitone ha1 (matrixObjective_pos hRho hSigma hW ha0 ha1).le
          (matrixObjective_le_vectorObjective M hRho.1 ha ha1 r hr)
      _ ≤ variationalMeasuredDivergence alpha rho sigma :=
        le_sSup ⟨povmWeightedObservable M r, hW, rfl⟩
  · apply sSup_le
    rintro z ⟨W, hW, rfl⟩
    let M := unitaryFinitePOVM hW.1.eigenvectorUnitary
    let r : Fin (Fintype.card ι) → ℝ := fun j => hW.1.eigenvalues ((Fintype.equivFin ι).symm j)
    have hr : ∀ j, 0 < r j := fun j => hW.eigenvalues_pos _
    rw [matrixObjective_eq_spectral hW]
    calc
      logRenyiBits alpha (vectorObjective alpha (measurementMass M rho) (measurementMass M sigma) r) ≤
          logRenyiBits alpha (vectorTrace alpha (measurementMass M rho) (measurementMass M sigma)) :=
        logRenyiBits_antitone ha1
          (vectorTrace_nonneg alpha _ _ (measurementMass_nonneg M hRho.1) (measurementMass_nonneg M hSigma))
          (vectorTrace_le_objective ha0 ha1 _ _ _
            (measurementMass_nonneg M hRho.1) (measurementMass_nonneg M hSigma) hr)
      _ = classicalRenyiDivergence (measurementMass M rho) (measurementMass M sigma) alpha :=
        (classicalRenyiDivergence_eq_log ha0 ha1 _ _).symm
      _ ≤ measuredDivergence rho sigma alpha := le_sSup ⟨Fintype.card ι, M, rfl⟩

theorem measuredDivergence_variational_explicit {rho sigma : CMat ι} (hRho : IsState rho)
    (hSigma : sigma.PosSemidef) {alpha : ℝ}
    (ha : (1 / 2 : ℝ) ≤ alpha) (ha1 : alpha < 1) :
    measuredDivergence rho sigma alpha = sSup
      {z : EReal | ∃ W : CMat ι, W.PosDef ∧
        z = ((logTwo (alpha * tracePair rho (matrixRpow W ((alpha - 1) / alpha)) +
          (1 - alpha) * tracePair sigma W) / (alpha - 1) : ℝ) : EReal)} := by
  rw [measuredDivergence_variational hRho hSigma ha ha1]
  unfold variationalMeasuredDivergence
  congr 1
  ext z
  constructor <;> rintro ⟨W, hW, hz⟩ <;> refine ⟨W, hW, ?_⟩
  · rw [logRenyiBits, if_neg (matrixObjective_pos hRho hSigma hW (by linarith) ha1).ne'] at hz
    simpa only [matrixObjective, renyiExponent] using hz
  · rw [logRenyiBits, if_neg (matrixObjective_pos hRho hSigma hW (by linarith) ha1).ne']
    simpa only [matrixObjective, renyiExponent] using hz

theorem variationalRenyiTrace_finite_nonneg {rho sigma : CMat ι}
    (hRho : IsState rho) (hSigma : sigma.PosSemidef) {alpha : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    0 ≤ variationalRenyiTrace alpha rho sigma ∧
      variationalRenyiTrace alpha rho sigma ≠ ⊤ ∧ variationalRenyiTrace alpha rho sigma ≠ ⊥ := by
  have h0 : (0 : EReal) ≤ variationalRenyiTrace alpha rho sigma := by
    apply le_sInf
    rintro z ⟨W, hW, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (matrixObjective_pos hRho hSigma hW ha ha1).le
  have hu : variationalRenyiTrace alpha rho sigma ≤ (matrixObjective alpha rho sigma 1 : EReal) :=
    sInf_le ⟨1, Matrix.PosDef.one, rfl⟩
  refine ⟨h0, ne_of_lt (hu.trans_lt (EReal.coe_lt_top _)), ?_⟩
  exact ne_of_gt ((EReal.bot_lt_coe (0 : ℝ)).trans_le h0)

theorem exists_matrixObjective_lt {alpha : ℝ} {rho sigma : CMat ι} {t : ℝ}
    (ht : variationalRenyiTrace alpha rho sigma < (t : EReal)) :
    ∃ W : CMat ι, W.PosDef ∧ matrixObjective alpha rho sigma W < t := by
  by_contra hn
  have hb : (t : EReal) ≤ variationalRenyiTrace alpha rho sigma := by
    apply le_sInf
    rintro z ⟨W, hW, rfl⟩
    apply EReal.coe_le_coe_iff.mpr
    exact le_of_not_gt (fun h => hn ⟨W, hW, h⟩)
  exact not_le_of_gt ht hb

theorem measuredDivergence_eq_log_variationalRenyiTrace {rho sigma : CMat ι}
    (hRho : IsState rho) (hSigma : sigma.PosSemidef) {alpha : ℝ}
    (ha : (1 / 2 : ℝ) ≤ alpha) (ha1 : alpha < 1) :
    measuredDivergence rho sigma alpha =
      logRenyiBits alpha (variationalRenyiTrace alpha rho sigma).toReal := by
  have ha0 : 0 < alpha := by linarith
  obtain ⟨hQ0, hQt, hQb⟩ := variationalRenyiTrace_finite_nonneg hRho hSigma ha0 ha1
  let q := (variationalRenyiTrace alpha rho sigma).toReal
  have hqid : (q : EReal) = variationalRenyiTrace alpha rho sigma := EReal.coe_toReal hQt hQb
  have hq0 : 0 ≤ q := by
    rw [← hqid] at hQ0
    exact EReal.coe_le_coe_iff.mp hQ0
  rw [measuredDivergence_variational hRho hSigma ha ha1]
  apply le_antisymm
  · apply sSup_le
    rintro z ⟨W, hW, rfl⟩
    have hl : q ≤ matrixObjective alpha rho sigma W := by
      apply EReal.coe_le_coe_iff.mp
      rw [hqid]
      exact sInf_le ⟨W, hW, rfl⟩
    exact logRenyiBits_antitone ha1 hq0 hl
  · by_contra hn
    obtain ⟨b, hb, hbq⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
    let threshold := Real.exp (b * (alpha - 1) * Real.log 2)
    have hqsmall : q < threshold := by
      by_cases hqz : q = 0
      · rw [hqz]
        exact Real.exp_pos _
      have hqp : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
      change (b : EReal) < logRenyiBits alpha q at hbq
      rw [logRenyiBits, if_neg hqz] at hbq
      have hdiv := (lt_div_iff_of_neg (sub_neg.mpr ha1)).mp (EReal.coe_lt_coe_iff.mp hbq)
      have hlog : Real.log q < b * (alpha - 1) * Real.log 2 :=
        (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp hdiv
      simpa only [Real.exp_log hqp] using Real.exp_lt_exp.mpr hlog
    have hstrict : variationalRenyiTrace alpha rho sigma < (threshold : EReal) := by
      rw [← hqid]
      exact EReal.coe_lt_coe_iff.mpr hqsmall
    obtain ⟨W, hW, hsmall⟩ := exists_matrixObjective_lt hstrict
    have hpos := matrixObjective_pos hRho hSigma hW ha0 ha1
    have hlog : Real.log (matrixObjective alpha rho sigma W) <
        b * (alpha - 1) * Real.log 2 := by
      have hh := Real.log_lt_log hpos hsmall
      simpa [threshold] using hh
    have hlarge : b < logTwo (matrixObjective alpha rho sigma W) / (alpha - 1) := by
      apply (lt_div_iff_of_neg (sub_neg.mpr ha1)).mpr
      exact (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog
    have hm : logRenyiBits alpha (matrixObjective alpha rho sigma W) ≤
        variationalMeasuredDivergence alpha rho sigma := le_sSup ⟨W, hW, rfl⟩
    rw [logRenyiBits, if_neg hpos.ne'] at hm
    exact not_lt_of_ge hm (hb.trans (EReal.coe_lt_coe_iff.mpr hlarge))

theorem measuredDivergence_eq_log_measuredRenyiTrace {rho sigma : CMat ι}
    (hRho : IsState rho) (hSigma : sigma.PosSemidef) {alpha : ℝ}
    (ha : (1 / 2 : ℝ) ≤ alpha) (ha1 : alpha < 1) :
    measuredDivergence rho sigma alpha =
      logRenyiBits alpha (measuredRenyiTrace alpha rho sigma).toReal := by
  rw [measuredRenyiTrace_variational hRho.1 hSigma ha ha1]
  exact measuredDivergence_eq_log_variationalRenyiTrace hRho hSigma ha ha1

theorem measuredDivergence_eq_top_iff_trace_eq_zero {rho sigma : CMat ι}
    (hRho : IsState rho) (hSigma : sigma.PosSemidef) {alpha : ℝ}
    (ha : (1 / 2 : ℝ) ≤ alpha) (ha1 : alpha < 1) :
    measuredDivergence rho sigma alpha = ⊤ ↔ measuredRenyiTrace alpha rho sigma = 0 := by
  obtain ⟨_, hQt, hQb⟩ := variationalRenyiTrace_finite_nonneg hRho hSigma (by linarith) ha1
  rw [measuredDivergence_eq_log_variationalRenyiTrace hRho hSigma ha ha1,
    measuredRenyiTrace_variational hRho.1 hSigma ha ha1,
    ← EReal.coe_toReal hQt hQb]
  by_cases hz : (variationalRenyiTrace alpha rho sigma).toReal = 0 <;>
    simp [logRenyiBits, hz]

theorem measuredDivergence_zero_reference {rho : CMat ι} (hRho : IsState rho)
    {alpha : ℝ} (ha : (1 / 2 : ℝ) ≤ alpha) (ha1 : alpha < 1) :
    measuredDivergence rho 0 alpha = ⊤ := by
  apply le_antisymm le_top
  have hc : classicalRenyiDivergence (measurementMass (singleOutcomePOVM (ι := ι)) rho)
      (measurementMass (singleOutcomePOVM (ι := ι)) 0) alpha = ⊤ := by
    rw [classicalRenyiDivergence_eq_log (by linarith) ha1]
    have hz : vectorTrace alpha (measurementMass (singleOutcomePOVM (ι := ι)) rho)
        (measurementMass (singleOutcomePOVM (ι := ι)) 0) = 0 := by
      simp [vectorTrace, scalarTrace, measurementMass, tracePair,
        Real.zero_rpow (sub_pos.mpr ha1).ne']
    simp [logRenyiBits, hz]
  rw [← hc]
  exact le_sSup ⟨1, singleOutcomePOVM, rfl⟩

theorem measuredRenyiTrace_zero_reference {rho : CMat ι} (hRho : IsState rho)
    {alpha : ℝ} (ha : (1 / 2 : ℝ) ≤ alpha) (ha1 : alpha < 1) :
    measuredRenyiTrace alpha rho 0 = 0 :=
  (measuredDivergence_eq_top_iff_trace_eq_zero hRho Matrix.PosSemidef.zero ha ha1).mp
    (measuredDivergence_zero_reference hRho ha ha1)

end QuantumProver.MeasuredRenyiVariational
