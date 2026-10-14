import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.InstrumentNormalization

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology
open MeasureTheory Filter Set

namespace QuantumProver.WernerEndpoint.LocalChannelMoments

noncomputable section

set_option maxHeartbeats 1200000

variable {I J O : Type*} [Fintype I] [Fintype J] [Fintype O]
  [DecidableEq I] [DecidableEq J] [DecidableEq O]

def matrixSandwichCLM (K : Matrix J I ℂ) :
    Matrix I I ℂ →L[ℂ] Matrix J J ℂ :=
  (QuantumProver.ElegantJointMeasurement.CP.sandwichMap K).toContinuousLinearMap

@[simp] theorem matrixSandwichCLM_apply (K : Matrix J I ℂ) (X : Matrix I I ℂ) :
    matrixSandwichCLM K X = K * X * Kᴴ :=
  QuantumProver.ElegantJointMeasurement.CP.sandwichMap_apply K X

theorem continuous_matrixSandwichCLM :
    Continuous (matrixSandwichCLM : Matrix J I ℂ → Matrix I I ℂ →L[ℂ] Matrix J J ℂ) := by
  apply continuous_clm_apply.mpr
  intro X
  simp only [matrixSandwichCLM_apply]
  fun_prop

theorem matrixSandwichCLM_mul (K : Matrix J I ℂ) (S : Matrix I I ℂ) :
    matrixSandwichCLM (K * S) = (matrixSandwichCLM K).comp (matrixSandwichCLM S) := by
  ext X
  simp only [ContinuousLinearMap.comp_apply, matrixSandwichCLM_apply,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem matrixSandwichCLM_one :
    matrixSandwichCLM (1 : Matrix I I ℂ) = ContinuousLinearMap.id ℂ (Matrix I I ℂ) := by
  ext X
  simp

theorem matrixSandwichCLM_real_smul (r : ℝ) (K : Matrix J I ℂ) :
    matrixSandwichCLM (r • K) = (r * r) • matrixSandwichCLM K := by
  ext X
  simp only [matrixSandwichCLM_apply, smul_apply,
    Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]

abbrev JointMatrix (a b : ℕ) := Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ

def leftSandwichCLM {a b p : ℕ} (K : Matrix (Fin p) (Fin a) ℂ) :
    JointMatrix a b →L[ℂ] JointMatrix p b :=
  matrixSandwichCLM (K ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))

def rightSandwichCLM {a b p : ℕ} (K : Matrix (Fin p) (Fin b) ℂ) :
    JointMatrix a b →L[ℂ] JointMatrix a p :=
  matrixSandwichCLM ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K)

@[simp] theorem leftSandwichCLM_apply {a b p : ℕ}
    (K : Matrix (Fin p) (Fin a) ℂ) (X : JointMatrix a b) :
    leftSandwichCLM K X = (K ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * X *
      (K ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ :=
  matrixSandwichCLM_apply _ X

@[simp] theorem rightSandwichCLM_apply {a b p : ℕ}
    (K : Matrix (Fin p) (Fin b) ℂ) (X : JointMatrix a b) :
    rightSandwichCLM K X = ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K) * X *
      ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K)ᴴ :=
  matrixSandwichCLM_apply _ X

theorem continuous_leftSandwichCLM {a b p : ℕ} :
    Continuous (leftSandwichCLM : Matrix (Fin p) (Fin a) ℂ →
      JointMatrix a b →L[ℂ] JointMatrix p b) := by
  apply continuous_matrixSandwichCLM.comp
  apply continuous_matrix
  intro i j
  change Continuous (fun K : Matrix (Fin p) (Fin a) ℂ =>
    K i.1 j.1 * (1 : Matrix (Fin b) (Fin b) ℂ) i.2 j.2)
  exact (continuous_apply_apply i.1 j.1).mul continuous_const

theorem continuous_rightSandwichCLM {a b p : ℕ} :
    Continuous (rightSandwichCLM : Matrix (Fin p) (Fin b) ℂ →
      JointMatrix a b →L[ℂ] JointMatrix a p) := by
  apply continuous_matrixSandwichCLM.comp
  apply continuous_matrix
  intro i j
  change Continuous (fun K : Matrix (Fin p) (Fin b) ℂ =>
    (1 : Matrix (Fin a) (Fin a) ℂ) i.1 j.1 * K i.2 j.2)
  exact continuous_const.mul (continuous_apply_apply i.2 j.2)

@[simp] theorem leftSandwichCLM_one {a b : ℕ} :
    leftSandwichCLM (b := b) (1 : Matrix (Fin a) (Fin a) ℂ) =
      ContinuousLinearMap.id ℂ (JointMatrix a b) := by
  simp only [leftSandwichCLM, Matrix.one_kronecker_one, matrixSandwichCLM_one]

@[simp] theorem rightSandwichCLM_one {a b : ℕ} :
    rightSandwichCLM (a := a) (1 : Matrix (Fin b) (Fin b) ℂ) =
      ContinuousLinearMap.id ℂ (JointMatrix a b) := by
  simp only [rightSandwichCLM, Matrix.one_kronecker_one, matrixSandwichCLM_one]

theorem leftSandwichCLM_mul {a b p : ℕ} (K : Matrix (Fin p) (Fin a) ℂ)
    (S : Matrix (Fin a) (Fin a) ℂ) :
    leftSandwichCLM (b := b) (K * S) =
      (leftSandwichCLM K).comp (leftSandwichCLM S) := by
  simp only [leftSandwichCLM, ← matrixSandwichCLM_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem rightSandwichCLM_mul {a b p : ℕ} (K : Matrix (Fin p) (Fin b) ℂ)
    (S : Matrix (Fin b) (Fin b) ℂ) :
    rightSandwichCLM (a := a) (K * S) =
      (rightSandwichCLM K).comp (rightSandwichCLM S) := by
  simp only [rightSandwichCLM, ← matrixSandwichCLM_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem leftSandwichCLM_weightedKraus {a b p : ℕ} (w : ℝ)
    (K : Matrix (Fin p) (Fin a) ℂ) (hw : 0 ≤ w) :
    leftSandwichCLM (b := b) (QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus w K) =
      w • leftSandwichCLM K := by
  simp only [QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus, leftSandwichCLM,
    Matrix.smul_kronecker, matrixSandwichCLM_real_smul, Real.mul_self_sqrt hw]

theorem rightSandwichCLM_weightedKraus {a b p : ℕ} (w : ℝ)
    (K : Matrix (Fin p) (Fin b) ℂ) (hw : 0 ≤ w) :
    rightSandwichCLM (a := a) (QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus w K) =
      w • rightSandwichCLM K := by
  simp only [QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus, rightSandwichCLM,
    Matrix.kronecker_smul, matrixSandwichCLM_real_smul, Real.mul_self_sqrt hw]

theorem normalized_left_channel_moment_limit {a b p : ℕ} (n : ℕ → ℕ)
    (K : (k : ℕ) → Fin (n k) → Matrix (Fin p) (Fin a) ℂ)
    (Φ : (k : ℕ) → Fin (n k) → JointMatrix p b →L[ℂ] Matrix O O ℂ)
    (hGram : Tendsto (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.gramTotal K) atTop (nhds 1))
    (F : JointMatrix a b →L[ℂ] Matrix O O ℂ)
    (hMoment : Tendsto (fun k => ∑ i, (Φ k i).comp (leftSandwichCLM (K k i)))
      atTop (nhds F)) :
    Tendsto (fun k => ∑ i, (Φ k i).comp
      (leftSandwichCLM (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus K k i)))
      atTop (nhds F) := by
  classical
  have hN : Tendsto (fun k => leftSandwichCLM (b := b)
      (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizer K k)) atTop
      (nhds (ContinuousLinearMap.id ℂ (JointMatrix a b))) := by
    simpa only [Function.comp_def, leftSandwichCLM_one] using
      (continuous_leftSandwichCLM.tendsto (1 : Matrix (Fin a) (Fin a) ℂ)).comp
        (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizer_tendsto K hGram)
  have hc : Continuous (fun z : (JointMatrix a b →L[ℂ] Matrix O O ℂ) ×
      (JointMatrix a b →L[ℂ] JointMatrix a b) => z.1.comp z.2) :=
    continuous_fst.clm_comp continuous_snd
  have ht := (hc.tendsto (F, ContinuousLinearMap.id ℂ (JointMatrix a b))).comp
    (hMoment.prodMk_nhds hN)
  have hvalue (k : ℕ) : (∑ i, (Φ k i).comp
      (leftSandwichCLM (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus K k i))) =
      (∑ i, (Φ k i).comp (leftSandwichCLM (K k i))).comp
        (leftSandwichCLM (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizer K k)) := by
    ext X
    simp only [QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus, leftSandwichCLM_mul,
      sum_apply, ContinuousLinearMap.comp_apply]
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
    ht.congr' (Eventually.of_forall fun k => (hvalue k).symm)

theorem normalized_right_channel_moment_limit {a b p : ℕ} (n : ℕ → ℕ)
    (K : (k : ℕ) → Fin (n k) → Matrix (Fin p) (Fin b) ℂ)
    (Φ : (k : ℕ) → Fin (n k) → JointMatrix a p →L[ℂ] Matrix O O ℂ)
    (hGram : Tendsto (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.gramTotal K) atTop (nhds 1))
    (F : JointMatrix a b →L[ℂ] Matrix O O ℂ)
    (hMoment : Tendsto (fun k => ∑ i, (Φ k i).comp (rightSandwichCLM (K k i)))
      atTop (nhds F)) :
    Tendsto (fun k => ∑ i, (Φ k i).comp
      (rightSandwichCLM (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus K k i)))
      atTop (nhds F) := by
  classical
  have hN : Tendsto (fun k => rightSandwichCLM (a := a)
      (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizer K k)) atTop
      (nhds (ContinuousLinearMap.id ℂ (JointMatrix a b))) := by
    simpa only [Function.comp_def, rightSandwichCLM_one] using
      (continuous_rightSandwichCLM.tendsto (1 : Matrix (Fin b) (Fin b) ℂ)).comp
        (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizer_tendsto K hGram)
  have hc : Continuous (fun z : (JointMatrix a b →L[ℂ] Matrix O O ℂ) ×
      (JointMatrix a b →L[ℂ] JointMatrix a b) => z.1.comp z.2) :=
    continuous_fst.clm_comp continuous_snd
  have ht := (hc.tendsto (F, ContinuousLinearMap.id ℂ (JointMatrix a b))).comp
    (hMoment.prodMk_nhds hN)
  have hvalue (k : ℕ) : (∑ i, (Φ k i).comp
      (rightSandwichCLM (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus K k i))) =
      (∑ i, (Φ k i).comp (rightSandwichCLM (K k i))).comp
        (rightSandwichCLM (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizer K k)) := by
    ext X
    simp only [QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus, rightSandwichCLM_mul,
      sum_apply, ContinuousLinearMap.comp_apply]
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
    ht.congr' (Eventually.of_forall fun k => (hvalue k).symm)

theorem exists_normalized_left_channel_quadrature_on {Ω : Type*} [MeasurableSpace Ω]
    {a b p : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Matrix (Fin p) (Fin a) ℂ)
    (Φ : Ω → JointMatrix p b →L[ℂ] Matrix O O ℂ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hMoment : Integrable (fun ω => (Φ ω).comp (leftSandwichCLM (K ω))) μ)
    (hComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1)
    (s : Set Ω) (hs : ∀ᵐ ω ∂μ, ω ∈ s) :
    ∃ (n : ℕ → ℕ) (Ks : (k : ℕ) → Fin (n k) → Matrix (Fin p) (Fin a) ℂ)
      (point : (k : ℕ) → Fin (n k) → Ω),
      (∀ k, (∑ i, (Ks k i)ᴴ * Ks k i) = 1) ∧
      (∀ k i, point k i ∈ s) ∧
      Tendsto (fun k => ∑ i, (Φ (point k i)).comp (leftSandwichCLM (Ks k i)))
        atTop (nhds (∫ ω, (Φ ω).comp (leftSandwichCLM (K ω)) ∂μ)) := by
  classical
  obtain ⟨n, w, point, hw, _, hpoint, hGramLimit, hMomentLimit⟩ :=
    QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.exists_joint_sampled_kraus_quadrature_on μ K
      (fun ω => (Φ ω).comp (leftSandwichCLM (K ω)))
      (hGram.prodMk hMoment) s hs
  let P : (k : ℕ) → Fin (n k) → Matrix (Fin p) (Fin a) ℂ :=
    fun k i => QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus (w k i) (K (point k i))
  have hP : Tendsto (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.gramTotal P) atTop (nhds 1) := by
    change Tendsto (fun k => ∑ i, (P k i)ᴴ * P k i) atTop (nhds 1)
    simpa only [P, hComplete] using hGramLimit
  have hvalues (k : ℕ) : (∑ i, (Φ (point k i)).comp (leftSandwichCLM (P k i))) =
      ∑ i, w k i • (Φ (point k i)).comp (leftSandwichCLM (K (point k i))) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [P]
    rw [leftSandwichCLM_weightedKraus _ _ (hw k i), ContinuousLinearMap.comp_smul]
  have hRaw := hMomentLimit.congr' (Eventually.of_forall fun k => (hvalues k).symm)
  have hRepaired := normalized_left_channel_moment_limit n P
    (fun k i => Φ (point k i)) hP _ hRaw
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus_complete P hP)
  refine ⟨fun k => n (k + N),
    fun k i => QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus P (k + N) i,
    fun k i => point (k + N) i, ?_, fun k i => hpoint (k + N) i, ?_⟩
  · intro k
    exact hN (k + N) (by omega)
  · simpa only [Function.comp_def] using hRepaired.comp (tendsto_add_atTop_nat N)

theorem exists_normalized_right_channel_quadrature_on {Ω : Type*} [MeasurableSpace Ω]
    {a b p : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : Ω → Matrix (Fin p) (Fin b) ℂ)
    (Φ : Ω → JointMatrix a p →L[ℂ] Matrix O O ℂ)
    (hGram : Integrable (fun ω => (K ω)ᴴ * K ω) μ)
    (hMoment : Integrable (fun ω => (Φ ω).comp (rightSandwichCLM (K ω))) μ)
    (hComplete : (∫ ω, (K ω)ᴴ * K ω ∂μ) = 1)
    (s : Set Ω) (hs : ∀ᵐ ω ∂μ, ω ∈ s) :
    ∃ (n : ℕ → ℕ) (Ks : (k : ℕ) → Fin (n k) → Matrix (Fin p) (Fin b) ℂ)
      (point : (k : ℕ) → Fin (n k) → Ω),
      (∀ k, (∑ i, (Ks k i)ᴴ * Ks k i) = 1) ∧
      (∀ k i, point k i ∈ s) ∧
      Tendsto (fun k => ∑ i, (Φ (point k i)).comp (rightSandwichCLM (Ks k i)))
        atTop (nhds (∫ ω, (Φ ω).comp (rightSandwichCLM (K ω)) ∂μ)) := by
  classical
  obtain ⟨n, w, point, hw, _, hpoint, hGramLimit, hMomentLimit⟩ :=
    QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.exists_joint_sampled_kraus_quadrature_on μ K
      (fun ω => (Φ ω).comp (rightSandwichCLM (K ω)))
      (hGram.prodMk hMoment) s hs
  let P : (k : ℕ) → Fin (n k) → Matrix (Fin p) (Fin b) ℂ :=
    fun k i => QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus (w k i) (K (point k i))
  have hP : Tendsto (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.gramTotal P) atTop (nhds 1) := by
    change Tendsto (fun k => ∑ i, (P k i)ᴴ * P k i) atTop (nhds 1)
    simpa only [P, hComplete] using hGramLimit
  have hvalues (k : ℕ) : (∑ i, (Φ (point k i)).comp (rightSandwichCLM (P k i))) =
      ∑ i, w k i • (Φ (point k i)).comp (rightSandwichCLM (K (point k i))) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [P]
    rw [rightSandwichCLM_weightedKraus _ _ (hw k i), ContinuousLinearMap.comp_smul]
  have hRaw := hMomentLimit.congr' (Eventually.of_forall fun k => (hvalues k).symm)
  have hRepaired := normalized_right_channel_moment_limit n P
    (fun k i => Φ (point k i)) hP _ hRaw
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus_complete P hP)
  refine ⟨fun k => n (k + N),
    fun k i => QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus P (k + N) i,
    fun k i => point (k + N) i, ?_, fun k i => hpoint (k + N) i, ?_⟩
  · intro k
    exact hN (k + N) (by omega)
  · simpa only [Function.comp_def] using hRepaired.comp (tendsto_add_atTop_nat N)

end

end QuantumProver.WernerEndpoint.LocalChannelMoments
