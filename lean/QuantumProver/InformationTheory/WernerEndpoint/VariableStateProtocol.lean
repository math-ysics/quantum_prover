import QuantumProver.InformationTheory.WernerEndpoint.MatrixContinuousCPProtocol
import QuantumProver.InformationTheory.WernerEndpoint.FiniteHeterogeneousProtocol
import QuantumProver.InformationTheory.WernerEndpoint.HeterogeneousChannelBound
import QuantumProver.InformationTheory.WernerEndpoint.VariableFiniteChildReplacement

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace QuantumProver.WernerEndpoint.MatrixVariableStateProtocol

open OperationalEndpointCost MatrixContinuousStateProtocol MeasureTheory Filter
open QuantumProver.SuperchannelDiscrimination
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

abbrev JointMatrix (a b : ℕ) := MatrixContinuousStateProtocol.JointMatrix a b
abbrev Channel (c d a b : ℕ) := MatrixContinuousStateProtocol.Channel c d a b

private theorem measurable_fiberElim {D : Type*} (F : D → Type*)
    [∀ d, MeasurableSpace (F d)] {E : Type*} [MeasurableSpace E]
    (f : Sigma F → E) (hf : ∀ d, Measurable (fun x : F d => f ⟨d, x⟩)) :
    Measurable f := by
  intro s hs
  change MeasurableSet[⨅ d, (inferInstance : MeasurableSpace (F d)).map (Sigma.mk d)]
    (f ⁻¹' s)
  rw [MeasurableSpace.measurableSet_iInf]
  intro d
  exact hf d hs

abbrev AliceFiber (c d a b p : ℕ) :=
  Matrix (Fin p) (Fin a) ℂ × Channel c d p b
abbrev BobFiber (c d a b p : ℕ) :=
  Matrix (Fin p) (Fin b) ℂ × Channel c d a p

theorem measurable_alice_gram (c d a b : ℕ) :
    Measurable (fun z : Sigma (AliceFiber c d a b) => z.2.1.conjTranspose * z.2.1) := by
  apply measurable_fiberElim
  intro p
  exact (continuous_fst.matrix_conjTranspose.matrix_mul continuous_fst).measurable

theorem measurable_bob_gram (c d a b : ℕ) :
    Measurable (fun z : Sigma (BobFiber c d a b) => z.2.1.conjTranspose * z.2.1) := by
  apply measurable_fiberElim
  intro p
  exact (continuous_fst.matrix_conjTranspose.matrix_mul continuous_fst).measurable

theorem measurable_alice_moment (c d a b : ℕ) :
    Measurable (fun z : Sigma (AliceFiber c d a b) =>
      z.2.2.comp (LocalChannelMoments.leftSandwichCLM z.2.1)) := by
  apply measurable_fiberElim
  intro p
  exact (continuous_snd.clm_comp
    (LocalChannelMoments.continuous_leftSandwichCLM.comp continuous_fst)).measurable

theorem measurable_bob_moment (c d a b : ℕ) :
    Measurable (fun z : Sigma (BobFiber c d a b) =>
      z.2.2.comp (LocalChannelMoments.rightSandwichCLM z.2.1)) := by
  apply measurable_fiberElim
  intro p
  exact (continuous_snd.clm_comp
    (LocalChannelMoments.continuous_rightSandwichCLM.comp continuous_fst)).measurable

theorem measurable_fiber_dimension {F : ℕ → Type*} [∀ p, MeasurableSpace (F p)] :
    Measurable (Sigma.fst : Sigma F → ℕ) := by
  apply measurable_fiberElim
  intro p
  exact measurable_const

theorem integrable_varying_gram_of_complete {Ω : Type*} [MeasurableSpace Ω]
    {a : ℕ} (μ : Measure Ω) (p : Ω → ℕ)
    (K : ∀ x, Matrix (Fin (p x)) (Fin a) ℂ)
    (hComplete : (∫ x, (K x).conjTranspose * K x ∂μ) = 1) :
    Integrable (fun x => (K x).conjTranspose * K x) μ := by
  classical
  by_cases hInput : Nonempty (Fin a)
  · let := hInput
    by_contra hNot
    have hZero := integral_undef hNot
    rw [hComplete] at hZero
    exact one_ne_zero hZero
  · let : IsEmpty (Fin a) := not_nonempty_iff.mp hInput
    have hZero : (fun x => (K x).conjTranspose * K x) =
        (0 : Ω → Matrix (Fin a) (Fin a) ℂ) := by
      ext x i j
      exact isEmptyElim i
    rw [hZero]
    exact integrable_zero Ω (Matrix (Fin a) (Fin a) ℂ) μ

private theorem finiteChannel_cptp {c d a b : ℕ} (T : FiniteLocalProtocol c d a b) :
    CPTPKraus.CompletelyPositive (finiteChannel T).toLinearMap ∧
      CPTPKraus.TracePreserving (finiteChannel T).toLinearMap := by
  have hMap : (finiteChannel T).toLinearMap = QuantumProver.ElegantJointMeasurement.CP.krausMap T.leafKraus := by
    apply LinearMap.ext
    intro X
    exact T.apply_eq_leafKraus X
  refine ⟨?_, fun X => T.apply_trace X⟩
  rw [hMap]
  exact (CPTPKraus.completelyPositive_iff_EJMCP _).mpr
    (QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive T.leafKraus)

private theorem cptpSet_isClosed (c d a b : ℕ) :
    IsClosed {Φ : Channel c d a b | CPTPKraus.CompletelyPositive Φ.toLinearMap ∧
      CPTPKraus.TracePreserving Φ.toLinearMap} := by
  have hCP : IsClosed {Φ : Channel c d a b |
      CPTPKraus.CompletelyPositive Φ.toLinearMap} := by
    simp only [CPTPKraus.CompletelyPositive, Set.ofPred_forall]
    apply isClosed_iInter
    intro r
    apply isClosed_iInter
    intro X
    apply isClosed_iInter
    intro hX
    apply Matrix.posSemidef_is_closed.preimage
    apply continuous_matrix
    intro i j
    change Continuous (fun Φ : Channel c d a b =>
      Φ (fun s t => X (s, i.2) (t, j.2)) i.1 j.1)
    fun_prop
  have hTP : IsClosed {Φ : Channel c d a b |
      CPTPKraus.TracePreserving Φ.toLinearMap} := by
    simp only [CPTPKraus.TracePreserving, Set.ofPred_forall]
    apply isClosed_iInter
    intro X
    exact isClosed_eq ((continuous_id.clm_apply continuous_const).matrix_trace)
      continuous_const
  exact hCP.inter hTP

theorem cptp_of_finite_channel_approx {c d a b : ℕ} (Φ : Channel c d a b)
    (hApprox : ∀ ε : ℝ, 0 < ε → ∃ T : FiniteLocalProtocol c d a b,
      ‖finiteChannel T - Φ‖ < ε) :
    CPTPKraus.CompletelyPositive Φ.toLinearMap ∧
      CPTPKraus.TracePreserving Φ.toLinearMap := by
  have hMem : Φ ∈ closure {Ψ : Channel c d a b |
      ∃ T : FiniteLocalProtocol c d a b, Ψ = finiteChannel T} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨T, hT⟩ := hApprox ε hε
    exact ⟨finiteChannel T, ⟨T, rfl⟩, by simpa only [dist_eq_norm, norm_sub_rev] using hT⟩
  exact closure_minimal (fun Ψ hΨ => by
    rcases hΨ with ⟨T, rfl⟩
    exact finiteChannel_cptp T) (cptpSet_isClosed c d a b) hMem

theorem exists_complete_varying_quadrature {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {a : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ] (p : Ω → ℕ)
    (K : ∀ x, Matrix (Fin (p x)) (Fin a) ℂ) (F : Ω → V)
    (hGram : Integrable (fun x => (K x).conjTranspose * K x) μ)
    (hMoment : Integrable F μ)
    (hComplete : (∫ x, (K x).conjTranspose * K x ∂μ) = 1) :
    ∃ (n : ℕ → ℕ) (w : (k : ℕ) → Fin (n k) → ℝ)
      (point : (k : ℕ) → Fin (n k) → Ω) (R : ℕ → Matrix (Fin a) (Fin a) ℂ),
      (∀ k i, 0 ≤ w k i) ∧
      (∀ k, ∑ i,
        (QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus (w k i) (K (point k i)) * R k).conjTranspose *
          (QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus (w k i) (K (point k i)) * R k) = 1) ∧
      Tendsto R atTop (nhds 1) ∧
      Tendsto (fun k => ∑ i, w k i • F (point k i)) atTop (nhds (∫ x, F x ∂μ)) := by
  classical
  let f : Ω → Matrix (Fin a) (Fin a) ℂ × V := fun x =>
    ((K x).conjTranspose * K x, F x)
  have hf : Integrable f μ := hGram.prodMk hMoment
  obtain ⟨n, w, point, hw, _, hlim⟩ :=
    QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.exists_integral_actual_point_quadrature μ f hf
  have hGramLimit : Tendsto (fun k => ∑ i, w k i •
      ((K (point k i)).conjTranspose * K (point k i))) atTop (nhds 1) := by
    simpa only [Function.comp_def, f, Prod.fst_sum, Prod.smul_fst, fst_integral hf,
      hComplete] using (continuous_fst.tendsto _).comp hlim
  have hMomentLimit : Tendsto (fun k => ∑ i, w k i • F (point k i))
      atTop (nhds (∫ x, F x ∂μ)) := by
    simpa only [Function.comp_def, f, Prod.snd_sum, Prod.smul_snd, snd_integral hf] using
      (continuous_snd.tendsto _).comp hlim
  let P : (k : ℕ) → (i : Fin (n k)) → Matrix (Fin (p (point k i))) (Fin a) ℂ :=
    fun k i => QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus (w k i) (K (point k i))
  let Q : (k : ℕ) → Fin (n k) →
      Matrix (Fin (QuantumProver.ElegantJointMeasurement.CP.commonOutputDimension (fun i => p (point k i)))) (Fin a) ℂ :=
    fun k i => FiniteHeterogeneousProtocol.paddedKraus (fun i => p (point k i)) (P k) i
  have hQGram (k : ℕ) : QuantumProver.ElegantJointMeasurement.InstrumentNormalization.gramTotal Q k =
      ∑ i, w k i • ((K (point k i)).conjTranspose * K (point k i)) := by
    simp only [QuantumProver.ElegantJointMeasurement.InstrumentNormalization.gramTotal, Q,
      FiniteHeterogeneousProtocol.paddedKraus_gram, P,
      QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus_gram _ _ (hw _ _)]
  have hQ : Tendsto (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.gramTotal Q) atTop (nhds 1) :=
    hGramLimit.congr' (Eventually.of_forall fun k => (hQGram k).symm)
  let R : ℕ → Matrix (Fin a) (Fin a) ℂ := QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizer Q
  have hCorrectGram (k : ℕ) (i : Fin (n k)) :
      (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus Q k i).conjTranspose *
        QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus Q k i =
      (P k i * R k).conjTranspose * (P k i * R k) := by
    calc
      _ = (R k).conjTranspose * ((Q k i).conjTranspose * Q k i) * R k := by
        simp only [QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus, R,
          Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (R k).conjTranspose * ((P k i).conjTranspose * P k i) * R k := by
        dsimp only [Q]
        rw [FiniteHeterogeneousProtocol.paddedKraus_gram]
      _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hCompleteTail : ∀ᶠ k in atTop, ∑ i, (P k i * R k).conjTranspose * (P k i * R k) = 1 := by
    filter_upwards [QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizedKraus_complete Q hQ] with k hk
    simpa only [hCorrectGram] using hk
  obtain ⟨N, hN⟩ := eventually_atTop.mp hCompleteTail
  refine ⟨fun k => n (k + N), fun k i => w (k + N) i,
    fun k i => point (k + N) i, fun k => R (k + N), fun k i => hw (k + N) i,
    fun k => hN (k + N) (by omega), ?_, ?_⟩
  · exact (QuantumProver.ElegantJointMeasurement.InstrumentNormalization.normalizer_tendsto Q hQ).comp (tendsto_add_atTop_nat N)
  · exact hMomentLimit.comp (tendsto_add_atTop_nat N)

private theorem left_repair_limit {c d a b : ℕ}
    (F : ℕ → Channel c d a b) (R : ℕ → Matrix (Fin a) (Fin a) ℂ)
    (L : Channel c d a b) (hF : Tendsto F atTop (nhds L))
    (hR : Tendsto R atTop (nhds 1)) :
    Tendsto (fun k => (F k).comp (LocalChannelMoments.leftSandwichCLM (R k)))
      atTop (nhds L) := by
  have hS : Tendsto (fun k => LocalChannelMoments.leftSandwichCLM (b := b) (R k))
      atTop (nhds (ContinuousLinearMap.id ℂ (JointMatrix a b))) := by
    simpa only [Function.comp_def, LocalChannelMoments.leftSandwichCLM_one] using
      (LocalChannelMoments.continuous_leftSandwichCLM.tendsto
        (1 : Matrix (Fin a) (Fin a) ℂ)).comp hR
  have hc : Continuous (fun z : Channel c d a b × Channel a b a b => z.1.comp z.2) :=
    continuous_fst.clm_comp continuous_snd
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
    (hc.tendsto (L, ContinuousLinearMap.id ℂ (JointMatrix a b))).comp
      (hF.prodMk_nhds hS)

private theorem right_repair_limit {c d a b : ℕ}
    (F : ℕ → Channel c d a b) (R : ℕ → Matrix (Fin b) (Fin b) ℂ)
    (L : Channel c d a b) (hF : Tendsto F atTop (nhds L))
    (hR : Tendsto R atTop (nhds 1)) :
    Tendsto (fun k => (F k).comp (LocalChannelMoments.rightSandwichCLM (R k)))
      atTop (nhds L) := by
  have hS : Tendsto (fun k => LocalChannelMoments.rightSandwichCLM (a := a) (R k))
      atTop (nhds (ContinuousLinearMap.id ℂ (JointMatrix a b))) := by
    simpa only [Function.comp_def, LocalChannelMoments.rightSandwichCLM_one] using
      (LocalChannelMoments.continuous_rightSandwichCLM.tendsto
        (1 : Matrix (Fin b) (Fin b) ℂ)).comp hR
  have hc : Continuous (fun z : Channel c d a b × Channel a b a b => z.1.comp z.2) :=
    continuous_fst.clm_comp continuous_snd
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
    (hc.tendsto (L, ContinuousLinearMap.id ℂ (JointMatrix a b))).comp
      (hF.prodMk_nhds hS)

private theorem approximate_alice {Ω : Type*} [MeasurableSpace Ω]
    {c d a b : ℕ} (hc : 0 < c) (hd : 0 < d)
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : Ω → ℕ)
    (K : ∀ x, Matrix (Fin (p x)) (Fin a) ℂ) (Φ : ∀ x, Channel c d (p x) b)
    (hGram : Integrable (fun x => (K x).conjTranspose * K x) μ)
    (hMoment : Integrable (fun x => (Φ x).comp (LocalChannelMoments.leftSandwichCLM (K x))) μ)
    (hComplete : (∫ x, (K x).conjTranspose * K x ∂μ) = 1)
    (hChild : ∀ x (η : ℝ), 0 < η →
      ∃ U : FiniteLocalProtocol c d (p x) b, ‖finiteChannel U - Φ x‖ < η)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : FiniteLocalProtocol c d a b,
      ‖finiteChannel U - (∫ x, (Φ x).comp (LocalChannelMoments.leftSandwichCLM (K x)) ∂μ)‖ < ε := by
  classical
  obtain ⟨n, w, point, R, hw, hCompleteSamples, hR, hMomentLimit⟩ :=
    exists_complete_varying_quadrature μ p K
      (fun x => (Φ x).comp (LocalChannelMoments.leftSandwichCLM (K x)))
      hGram hMoment hComplete
  let W : (k : ℕ) → (i : Fin (n k)) → Matrix (Fin (p (point k i))) (Fin a) ℂ :=
    fun k i => QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus (w k i) (K (point k i)) * R k
  have hValues (k : ℕ) : (∑ i, (Φ (point k i)).comp (LocalChannelMoments.leftSandwichCLM (W k i))) =
      (∑ i, w k i • (Φ (point k i)).comp
        (LocalChannelMoments.leftSandwichCLM (K (point k i)))).comp
          (LocalChannelMoments.leftSandwichCLM (R k)) := by
    ext X : 1
    simp only [W, LocalChannelMoments.leftSandwichCLM_mul,
      LocalChannelMoments.leftSandwichCLM_weightedKraus _ _ (hw _ _),
      sum_apply, ContinuousLinearMap.comp_apply, smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact ((Φ (point k i)).restrictScalars ℝ).map_smul (w k i) _
  have hLimit := (left_repair_limit _ R _ hMomentLimit hR).congr'
    (Eventually.of_forall fun k => (hValues k).symm)
  obtain ⟨k, hk⟩ := (Metric.tendsto_nhds.mp hLimit (ε / 2) (half_pos hε)).exists
  rw [dist_eq_norm] at hk
  obtain ⟨U, hU⟩ := VariableFiniteChildReplacement.approximate_alice_with_finite_children
    hc hd (fun i => p (point k i)) (W k) (hCompleteSamples k)
    (fun i => Φ (point k i)) (fun i η hη => hChild (point k i) η hη)
    (ε / 2) (half_pos hε)
  refine ⟨U, ?_⟩
  calc
    _ ≤ ‖finiteChannel U - (∑ i, (Φ (point k i)).comp
          (LocalChannelMoments.leftSandwichCLM (W k i)))‖ +
      ‖(∑ i, (Φ (point k i)).comp (LocalChannelMoments.leftSandwichCLM (W k i))) -
        (∫ x, (Φ x).comp (LocalChannelMoments.leftSandwichCLM (K x)) ∂μ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hU hk
    _ = ε := by ring

private theorem approximate_bob {Ω : Type*} [MeasurableSpace Ω]
    {c d a b : ℕ} (hc : 0 < c) (hd : 0 < d)
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : Ω → ℕ)
    (K : ∀ x, Matrix (Fin (p x)) (Fin b) ℂ) (Φ : ∀ x, Channel c d a (p x))
    (hGram : Integrable (fun x => (K x).conjTranspose * K x) μ)
    (hMoment : Integrable (fun x => (Φ x).comp (LocalChannelMoments.rightSandwichCLM (K x))) μ)
    (hComplete : (∫ x, (K x).conjTranspose * K x ∂μ) = 1)
    (hChild : ∀ x (η : ℝ), 0 < η →
      ∃ U : FiniteLocalProtocol c d a (p x), ‖finiteChannel U - Φ x‖ < η)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : FiniteLocalProtocol c d a b,
      ‖finiteChannel U - (∫ x, (Φ x).comp (LocalChannelMoments.rightSandwichCLM (K x)) ∂μ)‖ < ε := by
  classical
  obtain ⟨n, w, point, R, hw, hCompleteSamples, hR, hMomentLimit⟩ :=
    exists_complete_varying_quadrature μ p K
      (fun x => (Φ x).comp (LocalChannelMoments.rightSandwichCLM (K x)))
      hGram hMoment hComplete
  let W : (k : ℕ) → (i : Fin (n k)) → Matrix (Fin (p (point k i))) (Fin b) ℂ :=
    fun k i => QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus (w k i) (K (point k i)) * R k
  have hValues (k : ℕ) : (∑ i, (Φ (point k i)).comp (LocalChannelMoments.rightSandwichCLM (W k i))) =
      (∑ i, w k i • (Φ (point k i)).comp
        (LocalChannelMoments.rightSandwichCLM (K (point k i)))).comp
          (LocalChannelMoments.rightSandwichCLM (R k)) := by
    ext X : 1
    simp only [W, LocalChannelMoments.rightSandwichCLM_mul,
      LocalChannelMoments.rightSandwichCLM_weightedKraus _ _ (hw _ _),
      sum_apply, ContinuousLinearMap.comp_apply, smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact ((Φ (point k i)).restrictScalars ℝ).map_smul (w k i) _
  have hLimit := (right_repair_limit _ R _ hMomentLimit hR).congr'
    (Eventually.of_forall fun k => (hValues k).symm)
  obtain ⟨k, hk⟩ := (Metric.tendsto_nhds.mp hLimit (ε / 2) (half_pos hε)).exists
  rw [dist_eq_norm] at hk
  obtain ⟨U, hU⟩ := VariableFiniteChildReplacement.approximate_bob_with_finite_children
    hc hd (fun i => p (point k i)) (W k) (hCompleteSamples k)
    (fun i => Φ (point k i)) (fun i η hη => hChild (point k i) η hη)
    (ε / 2) (half_pos hε)
  refine ⟨U, ?_⟩
  calc
    _ ≤ ‖finiteChannel U - (∑ i, (Φ (point k i)).comp
          (LocalChannelMoments.rightSandwichCLM (W k i)))‖ +
      ‖(∑ i, (Φ (point k i)).comp (LocalChannelMoments.rightSandwichCLM (W k i))) -
        (∫ x, (Φ x).comp (LocalChannelMoments.rightSandwichCLM (K x)) ∂μ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hU hk
    _ = ε := by ring

universe u

inductive Tree (c d : ℕ) : (a b height : ℕ) → Type (u + 1) where
  | finite {a b : ℕ} (height : ℕ) (T : MatrixCPProtocol.FiniteCPProtocol c d a b) :
      Tree c d a b height
  | alice {a b height : ℕ} (Ω : Type u) (mΩ : MeasurableSpace Ω)
      (μ : @Measure Ω mΩ) (p : Ω → ℕ)
      (K : ∀ x, Matrix (Fin (p x)) (Fin a) ℂ)
      (child : ∀ x, Tree c d (p x) b height) : Tree c d a b (height + 1)
  | bob {a b height : ℕ} (Ω : Type u) (mΩ : MeasurableSpace Ω)
      (μ : @Measure Ω mΩ) (p : Ω → ℕ)
      (K : ∀ x, Matrix (Fin (p x)) (Fin b) ℂ)
      (child : ∀ x, Tree c d a (p x) height) : Tree c d a b (height + 1)

def channel {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height → Channel c d a b
  | _, _, _, .finite _ T => MatrixContinuousCPProtocol.finiteCPChannel T
  | _, _, _, .alice _ mΩ μ _ K child =>
      letI := mΩ
      ∫ x, (channel (child x)).comp (LocalChannelMoments.leftSandwichCLM (K x)) ∂μ
  | _, _, _, .bob _ mΩ μ _ K child =>
      letI := mΩ
      ∫ x, (channel (child x)).comp (LocalChannelMoments.rightSandwichCLM (K x)) ∂μ

def Regular {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height → Prop
  | _, _, _, .finite _ _ => True
  | a, b, _, .alice _ mΩ μ p K child =>
      letI := mΩ
      IsFiniteMeasure μ ∧
      Measurable (fun x => (⟨p x, (K x, channel (child x))⟩ : Sigma (AliceFiber c d a b))) ∧
      (∫ x, (K x).conjTranspose * K x ∂μ) = 1 ∧ ∀ x, Regular (child x)
  | a, b, _, .bob _ mΩ μ p K child =>
      letI := mΩ
      IsFiniteMeasure μ ∧
      Measurable (fun x => (⟨p x, (K x, channel (child x))⟩ : Sigma (BobFiber c d a b))) ∧
      (∫ x, (K x).conjTranspose * K x ∂μ) = 1 ∧ ∀ x, Regular (child x)

def IntegrableMoments {c d : ℕ} : {a b height : ℕ} → Tree.{u} c d a b height → Prop
  | _, _, _, .finite _ _ => True
  | _, _, _, .alice _ mΩ μ _ K child =>
      letI := mΩ
      Integrable (fun x => (K x).conjTranspose * K x) μ ∧
      Integrable (fun x => (channel (child x)).comp (LocalChannelMoments.leftSandwichCLM (K x))) μ ∧
        ∀ x, IntegrableMoments (child x)
  | _, _, _, .bob _ mΩ μ _ K child =>
      letI := mΩ
      Integrable (fun x => (K x).conjTranspose * K x) μ ∧
      Integrable (fun x => (channel (child x)).comp (LocalChannelMoments.rightSandwichCLM (K x))) μ ∧
        ∀ x, IntegrableMoments (child x)

theorem regular_spec {c d a b height : ℕ} (T : Tree.{u} c d a b height)
    (hT : Regular T) (hc : 0 < c) (hd : 0 < d) :
    IntegrableMoments T ∧
      (∀ ε : ℝ, 0 < ε → ∃ U : FiniteLocalProtocol c d a b, ‖finiteChannel U - channel T‖ < ε) ∧
      CPTPKraus.CompletelyPositive (channel T).toLinearMap ∧
      CPTPKraus.TracePreserving (channel T).toLinearMap := by
  classical
  revert hT
  induction T with
  | finite height U =>
      intro _
      have hApprox : ∀ ε : ℝ, 0 < ε → ∃ V : FiniteLocalProtocol c d _ _,
          ‖finiteChannel V - channel (Tree.finite.{u} height U)‖ < ε := by
        intro ε hε
        refine ⟨U.represented_toMatrix, ?_⟩
        rw [channel, MatrixContinuousCPProtocol.finiteCPChannel_eq_matrix]
        simpa only [sub_self, norm_zero] using hε
      exact ⟨trivial, hApprox, cptp_of_finite_channel_approx _ hApprox⟩
  | @alice a b height Ω mΩ μ p K child ih =>
      let := mΩ
      intro hT
      rcases hT with ⟨hμ, hPacked, hComplete, hChild⟩
      let := hμ
      have hIH := fun x => ih x (hChild x)
      have hGram := integrable_varying_gram_of_complete μ p K hComplete
      have hMeas := (measurable_alice_moment c d a b).comp hPacked
      let C : ℝ := (Fintype.card (Fin a × Fin b) : ℝ) *
        ‖ContinuousChannelIntegrability.leftGramLiftCLM (I := Fin a) (Fin b)‖
      have hMoment : Integrable (fun x => (channel (child x)).comp
          (LocalChannelMoments.leftSandwichCLM (K x))) μ := by
        refine ⟨hMeas.aestronglyMeasurable,
          (hGram.norm.const_mul C).hasFiniteIntegral.mono'
            (f := fun x => (channel (child x)).comp
              (LocalChannelMoments.leftSandwichCLM (K x))) ?_⟩
        exact Eventually.of_forall fun x =>
          HeterogeneousChannelBound.norm_cptp_comp_left_sandwich_le_gram
            (channel (child x)) (hIH x).2.2.1 (hIH x).2.2.2 (K x)
      have hApprox : ∀ ε : ℝ, 0 < ε → ∃ U : FiniteLocalProtocol c d a b,
          ‖finiteChannel U - channel (Tree.alice Ω mΩ μ p K child)‖ < ε := by
        intro ε hε
        exact approximate_alice hc hd μ p K (fun x => channel (child x)) hGram hMoment hComplete
          (fun x η hη => (hIH x).2.1 η hη) ε hε
      exact ⟨⟨hGram, hMoment, fun x => (hIH x).1⟩, hApprox,
        cptp_of_finite_channel_approx _ hApprox⟩
  | @bob a b height Ω mΩ μ p K child ih =>
      let := mΩ
      intro hT
      rcases hT with ⟨hμ, hPacked, hComplete, hChild⟩
      let := hμ
      have hIH := fun x => ih x (hChild x)
      have hGram := integrable_varying_gram_of_complete μ p K hComplete
      have hMeas := (measurable_bob_moment c d a b).comp hPacked
      let C : ℝ := (Fintype.card (Fin a × Fin b) : ℝ) *
        ‖ContinuousChannelIntegrability.rightGramLiftCLM (I := Fin b) (Fin a)‖
      have hMoment : Integrable (fun x => (channel (child x)).comp
          (LocalChannelMoments.rightSandwichCLM (K x))) μ := by
        refine ⟨hMeas.aestronglyMeasurable,
          (hGram.norm.const_mul C).hasFiniteIntegral.mono'
            (f := fun x => (channel (child x)).comp
              (LocalChannelMoments.rightSandwichCLM (K x))) ?_⟩
        exact Eventually.of_forall fun x =>
          HeterogeneousChannelBound.norm_cptp_comp_right_sandwich_le_gram
            (channel (child x)) (hIH x).2.2.1 (hIH x).2.2.2 (K x)
      have hApprox : ∀ ε : ℝ, 0 < ε → ∃ U : FiniteLocalProtocol c d a b,
          ‖finiteChannel U - channel (Tree.bob Ω mΩ μ p K child)‖ < ε := by
        intro ε hε
        exact approximate_bob hc hd μ p K (fun x => channel (child x)) hGram hMoment hComplete
          (fun x η hη => (hIH x).2.1 η hη) ε hε
      exact ⟨⟨hGram, hMoment, fun x => (hIH x).1⟩, hApprox,
        cptp_of_finite_channel_approx _ hApprox⟩

theorem integrableMoments_of_regular {c d a b height : ℕ} (T : Tree.{u} c d a b height)
    (hT : Regular T) (hc : 0 < c) (hd : 0 < d) : IntegrableMoments T :=
  (regular_spec T hT hc hd).1

theorem channel_cptp {c d a b height : ℕ} (T : Tree.{u} c d a b height)
    (hT : Regular T) (hc : 0 < c) (hd : 0 < d) :
    CPTPKraus.CompletelyPositive (channel T).toLinearMap ∧
      CPTPKraus.TracePreserving (channel T).toLinearMap := (regular_spec T hT hc hd).2.2

theorem exists_finiteProtocol_channel_approx {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) (hc : 0 < c) (hd : 0 < d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : FiniteLocalProtocol c d a b, ‖finiteChannel U - channel T‖ < ε :=
  (regular_spec T hT hc hd).2.1 ε hε

theorem exists_finiteProtocol_output_approx {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) (hc : 0 < c) (hd : 0 < d)
    (ρ : JointMatrix a b) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : FiniteLocalProtocol c d a b, ‖U.apply ρ - channel T ρ‖ < ε :=
  exists_output_approx_of_channel_approx (channel T)
    (fun η hη => exists_finiteProtocol_channel_approx T hT hc hd η hη) ρ ε hε

theorem channel_pureOutput_mem_outputClosure {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) (hc : 0 < c) (hd : 0 < d)
    (ψ : Fin a × Fin b → ℂ) :
    channel T (pureDensity ψ) ∈ EndpointProtocolClosure.outputClosure ψ := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨U, hU⟩ := exists_finiteProtocol_output_approx T hT hc hd (pureDensity ψ) ε hε
  exact ⟨U.apply (pureDensity ψ), ⟨U, rfl⟩,
    by simpa only [dist_eq_norm, norm_sub_rev] using hU⟩

theorem channel_pureOutput_isDensity {c d a b height : ℕ}
    (T : Tree.{u} c d a b height) (hT : Regular T) (hc : 0 < c) (hd : 0 < d)
    (ψ : Fin a × Fin b → ℂ) (hψ : vectorNormSq ψ = 1) :
    (channel T (pureDensity ψ)).PosSemidef ∧ (channel T (pureDensity ψ)).trace = 1 :=
  EndpointProtocolClosure.outputClosure_isDensity ψ hψ
    (channel_pureOutput_mem_outputClosure T hT hc hd ψ)

end QuantumProver.WernerEndpoint.MatrixVariableStateProtocol
