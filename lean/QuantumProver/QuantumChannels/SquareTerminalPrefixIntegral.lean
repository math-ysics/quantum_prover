import QuantumProver.QuantumChannels.SquareQuantumTerminal
import QuantumProver.InformationTheory.ElegantJointMeasurement.SquareProcess

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace QuantumProver.MatrixSquareTerminalPrefixIntegral

open MeasureTheory ProbabilityTheory Matrix Filter
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.WernerEndpoint LocalChannelMoments
open QuantumProver.MatrixSquareQuantumTerminal QuantumProver.SuperchannelDiscrimination
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

universe u

variable {R : Type u} [MeasurableSpace R] {a b c d : ℕ}

def historyMeasure (P : SquareProcess a b R) :
    (n : ℕ) → Measure (History R n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => P.prefixMeasure n

def cumulativeOp (P : SquareProcess a b R) :
    (n : ℕ) → History R n → QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix a b
  | 0, _ => 1
  | n + 1, h => P.pathOp n h

@[simp] theorem historyMeasure_zero (P : SquareProcess a b R) :
    historyMeasure P 0 = Measure.dirac PUnit.unit := rfl

@[simp] theorem historyMeasure_succ (P : SquareProcess a b R) (n : ℕ) :
    historyMeasure P (n + 1) = P.prefixMeasure n := rfl

@[simp] theorem cumulativeOp_zero (P : SquareProcess a b R) (h : History R 0) :
    cumulativeOp P 0 h = 1 := rfl

@[simp] theorem cumulativeOp_succ (P : SquareProcess a b R) (n : ℕ)
    (h : History R (n + 1)) : cumulativeOp P (n + 1) h = P.pathOp n h := rfl

theorem historyMeasure_isProbability (P : SquareProcess a b R) (n : ℕ) :
    IsProbabilityMeasure (historyMeasure P n) := by
  cases n with
  | zero => change IsProbabilityMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ n => exact P.prefixMeasure_isProbability n

theorem historyMeasure_successor (P : SquareProcess a b R) (n : ℕ) :
    historyMeasure P (n + 1) =
      ((historyMeasure P n) ⊗ₘ P.kernel n).map (appendHistory n) := by
  cases n with
  | zero =>
      let := P.markov 0
      symm
      apply Measure.ext_of_lintegral
      intro f hf
      rw [lintegral_map_equiv f (appendHistory 0)]
      have hm : Measurable (fun z : History R 0 × R => f (appendHistory 0 z)) :=
        hf.comp (appendHistory 0).measurable
      rw [Measure.lintegral_compProd hm]
      change (∫⁻ h, ∫⁻ r, f (appendHistory 0 (h,r)) ∂P.kernel 0 h
        ∂Measure.dirac PUnit.unit) = _
      rw [lintegral_dirac' _ hm.lintegral_kernel_prod_right']
      change (∫⁻ r, f (firstRecordEquiv r) ∂P.kernel 0 PUnit.unit) =
        ∫⁻ h, f h ∂(P.kernel 0 PUnit.unit).map firstRecordEquiv
      exact (lintegral_map_equiv f firstRecordEquiv).symm
  | succ n => rfl

theorem cumulativeOp_append (P : SquareProcess a b R) (n : ℕ)
    (h : History R n) (r : R) :
    cumulativeOp P (n + 1) (appendHistory n (h,r)) =
      P.localOp n h r * cumulativeOp P n h := by
  cases n with
  | zero =>
      cases h
      simp [cumulativeOp, SquareProcess.pathOp, appendHistory]
  | succ n =>
      simp only [cumulativeOp, SquareProcess.pathOp, appendHistory,
        MeasurableEquiv.symm_apply_apply]

theorem cumulativeOp_measurable (P : SquareProcess a b R) (n : ℕ) :
    Measurable (cumulativeOp P n) := by
  cases n with
  | zero => exact measurable_const
  | succ n => exact P.measurable_pathOp n

theorem cumulativeGram_integrable (P : SquareProcess a b R) (n : ℕ) :
    Integrable (fun h => (cumulativeOp P n h)ᴴ * cumulativeOp P n h)
      (historyMeasure P n) := by
  cases n with
  | zero => simpa only [cumulativeOp, historyMeasure, Matrix.conjTranspose_one,
      Matrix.one_mul] using
      (integrable_const (1 : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix a b) :
        Integrable (fun _ : PUnit => (1 : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix a b))
          (Measure.dirac PUnit.unit))
  | succ n => exact P.pathGram_integrable n

theorem cumulativeGram_integral (P : SquareProcess a b R) (n : ℕ) :
    (∫ h, (cumulativeOp P n h)ᴴ * cumulativeOp P n h ∂historyMeasure P n) = 1 := by
  cases n with
  | zero => simp [historyMeasure, cumulativeOp]
  | succ n => exact P.pathGram_integral n

private theorem continuation_cptp (P : SquareProcess a b R)
    (Q : TerminalPolicy a b c d R) (height n : ℕ) (h : History R n)
    (hc : 0 < c) (hd : 0 < d) :
    CPTPKraus.CompletelyPositive (quantumChannelFrom P Q height n h).toLinearMap ∧
      CPTPKraus.TracePreserving (quantumChannelFrom P Q height n h).toLinearMap := by
  rw [← treeFrom_channel P Q height n h]
  exact MatrixVariableCPDensityProtocol.channel_cptp _
    (treeFrom_regular P Q height n h) hc hd

private def conditionalMoment (P : SquareProcess a b R)
    (Q : TerminalPolicy a b c d R) (height n : ℕ) (h : History R n) (r : R) :
    Channel c d a b :=
  (quantumChannelFrom P Q height (n + 1) (appendHistory n (h,r))).comp
    (matrixSandwichCLM (P.localOp n h r))

private theorem conditionalMoment_integrable (P : SquareProcess a b R)
    (Q : TerminalPolicy a b c d R) (height n : ℕ) (h : History R n)
    (hc : 0 < c) (hd : 0 < d) :
    Integrable (conditionalMoment P Q height n h) (P.kernel n h) := by
  have hm : Measurable (fun z : History R n × R =>
      (quantumChannelFrom P Q height (n + 1) (appendHistory n z)).comp
        (matrixSandwichCLM (P.localOp n z.1 z.2))) :=
    (continuous_fst.clm_comp continuous_snd).measurable.comp
      (((quantumChannelFrom_measurable P Q height (n + 1)).comp
        (appendHistory n).measurable).prodMk
          (continuous_matrixSandwichCLM.measurable.comp (P.measurable_localOp n)))
  exact HeterogeneousChannelBound.integrable_varying_cptp_moment
    (P.kernel n h) (P.localOp n h)
    (fun r => quantumChannelFrom P Q height (n + 1) (appendHistory n (h,r)))
    (fun r => (continuation_cptp P Q height (n + 1) _ hc hd).1)
    (fun r => (continuation_cptp P Q height (n + 1) _ hc hd).2)
    (hm.comp measurable_prodMk_left).stronglyMeasurable.aestronglyMeasurable
    (P.localGram_integrable n h)

private theorem quantumChannelFrom_successor (P : SquareProcess a b R)
    (Q : TerminalPolicy a b c d R) (height n : ℕ) (h : History R n) :
    quantumChannelFrom P Q (height + 1) n h =
      ∫ r, conditionalMoment P Q height n h r ∂P.kernel n h := by
  classical
  by_cases ht : P.aliceTurn n h = true
  · simp only [quantumChannelFrom, ite_eq_left ht]
    apply integral_congr_ae
    exact Eventually.of_forall fun r => by
      simp only [conditionalMoment, SquareProcess.localOp, ite_eq_left ht,
        leftSandwichCLM]
  · simp only [quantumChannelFrom, ite_eq_right ht]
    apply integral_congr_ae
    exact Eventually.of_forall fun r => by
      simp only [conditionalMoment, SquareProcess.localOp, ite_eq_right ht,
        rightSandwichCLM]

private def prefixMomentIntegrand (P : SquareProcess a b R)
    (Q : TerminalPolicy a b c d R) (height k : ℕ) (h : Prefix R k) :
    Channel c d a b :=
  (quantumChannelFrom P Q height (k + 1) h).comp (matrixSandwichCLM (P.pathOp k h))

private def prefixMoment (P : SquareProcess a b R)
    (Q : TerminalPolicy a b c d R) (height k : ℕ) : Channel c d a b :=
  ∫ h, prefixMomentIntegrand P Q height k h ∂P.prefixMeasure k

private theorem prefixMomentIntegrand_integrable (P : SquareProcess a b R)
    (Q : TerminalPolicy a b c d R) (height k : ℕ) (hc : 0 < c) (hd : 0 < d) :
    Integrable (prefixMomentIntegrand P Q height k) (P.prefixMeasure k) := by
  have hm : Measurable (prefixMomentIntegrand P Q height k) :=
    (continuous_fst.clm_comp continuous_snd).measurable.comp
      ((quantumChannelFrom_measurable P Q height (k + 1)).prodMk
        (continuous_matrixSandwichCLM.measurable.comp (P.measurable_pathOp k)))
  exact HeterogeneousChannelBound.integrable_varying_cptp_moment
    (P.prefixMeasure k) (P.pathOp k) (quantumChannelFrom P Q height (k + 1))
    (fun h => (continuation_cptp P Q height (k + 1) h hc hd).1)
    (fun h => (continuation_cptp P Q height (k + 1) h hc hd).2)
    hm.stronglyMeasurable.aestronglyMeasurable (P.pathGram_integrable k)

private theorem prefixMoment_step (P : SquareProcess a b R)
    (Q : TerminalPolicy a b c d R) (height k : ℕ) (hc : 0 < c) (hd : 0 < d) :
    prefixMoment P Q (height + 1) k = prefixMoment P Q height (k + 1) := by
  let := P.markov (k + 1)
  have hG : Integrable (fun z =>
      prefixMomentIntegrand P Q height (k + 1) (prefixStepEquiv k z))
      ((P.prefixMeasure k) ⊗ₘ P.kernel (k + 1)) := by
    exact (integrable_map_equiv (prefixStepEquiv k)
      (prefixMomentIntegrand P Q height (k + 1))).mp
      (by simpa only [SquareProcess.prefixMeasure] using
        prefixMomentIntegrand_integrable P Q height (k + 1) hc hd)
  have hpoint (h : Prefix R k) :
      (∫ r, prefixMomentIntegrand P Q height (k + 1)
        (prefixStepEquiv k (h,r)) ∂P.kernel (k + 1) h) =
        prefixMomentIntegrand P Q (height + 1) k h := by
    let L := (ContinuousLinearMap.compL ℂ
      (QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix a b) (QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix a b)
      (QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix c d)).flip (matrixSandwichCLM (P.pathOp k h))
    have heq : (fun r => prefixMomentIntegrand P Q height (k + 1)
        (prefixStepEquiv k (h,r))) =
        (fun r => L (conditionalMoment P Q height (k + 1) h r)) := by
      funext r
      change (quantumChannelFrom P Q height (k + 1 + 1)
          (prefixStepEquiv k (h,r))).comp
          (matrixSandwichCLM (P.pathOp (k + 1) (prefixStepEquiv k (h,r)))) =
        ((quantumChannelFrom P Q height (k + 1 + 1)
          (appendHistory (k + 1) (h,r))).comp
            (matrixSandwichCLM (P.localOp (k + 1) h r))).comp
          (matrixSandwichCLM (P.pathOp k h))
      simp only [SquareProcess.pathOp, MeasurableEquiv.symm_apply_apply,
        matrixSandwichCLM_mul, appendHistory, ContinuousLinearMap.comp_assoc]
    rw [heq, L.integral_comp_comm
      (conditionalMoment_integrable P Q height (k + 1) h hc hd)]
    rw [← quantumChannelFrom_successor P Q height (k + 1) h]
    rfl
  symm
  change (∫ h, prefixMomentIntegrand P Q height (k + 1) h
    ∂P.prefixMeasure (k + 1)) = _
  rw [SquareProcess.prefixMeasure, integral_map_equiv, Measure.integral_compProd hG]
  exact integral_congr_ae (Eventually.of_forall hpoint)

private theorem prefixMoment_iter (P : SquareProcess a b R)
    (Q : TerminalPolicy a b c d R) (height k : ℕ) (hc : 0 < c) (hd : 0 < d) :
    prefixMoment P Q height k = prefixMoment P Q 0 (k + height) := by
  induction height generalizing k with
  | zero => simp
  | succ height ih =>
      rw [prefixMoment_step P Q height k hc hd, ih (k + 1)]
      congr 1
      omega

private theorem rootMoment (P : SquareProcess a b R)
    (Q : TerminalPolicy a b c d R) (height : ℕ) :
    quantumChannelFrom P Q (height + 1) 0 PUnit.unit = prefixMoment P Q height 0 := by
  rw [quantumChannelFrom_successor, prefixMoment, SquareProcess.prefixMeasure,
    integral_map_equiv]
  apply integral_congr_ae
  exact Eventually.of_forall fun r => by
    simp only [conditionalMoment, prefixMomentIntegrand, SquareProcess.pathOp,
      MeasurableEquiv.symm_apply_apply, appendHistory]
    rfl

def terminalIntegrand (P : SquareProcess a b R) (N : ℕ)
    (Q : FinalTerminal a b c d R N) (X : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix a b)
    (h : History R N) : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix c d :=
  terminalChannel (Q.toPolicy P) N h
    (cumulativeOp P N h * X * (cumulativeOp P N h)ᴴ)

private theorem terminalIntegrand_integrable_pos (P : SquareProcess a b R) (N : ℕ)
    (Q : FinalTerminal a b c d R N) (X : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix a b)
    (hc : 0 < c) (hd : 0 < d) :
    Integrable (terminalIntegrand P N Q X) (historyMeasure P N) := by
  cases N with
  | zero =>
      have heq : terminalIntegrand P 0 Q X =
          fun _ => terminalChannel (Q.toPolicy P) 0 PUnit.unit X := by
        funext h
        cases h
        simp [terminalIntegrand, cumulativeOp]
      rw [heq]
      change Integrable (fun _ : PUnit => terminalChannel (Q.toPolicy P) 0 PUnit.unit X)
        (Measure.dirac PUnit.unit)
      exact integrable_const _
  | succ N =>
      change Integrable (terminalIntegrand P (N + 1) Q X) (P.prefixMeasure N)
      have heq : terminalIntegrand P (N + 1) Q X =
          fun h => prefixMomentIntegrand P (Q.toPolicy P) 0 N h X := by
        funext h
        simp only [terminalIntegrand, cumulativeOp, prefixMomentIntegrand,
          quantumChannelFrom, ContinuousLinearMap.comp_apply, matrixSandwichCLM_apply]
      rw [heq]
      have hm : Measurable (prefixMomentIntegrand P (Q.toPolicy P) 0 N) :=
        (continuous_fst.clm_comp continuous_snd).measurable.comp
          ((quantumChannelFrom_measurable P (Q.toPolicy P) 0 (N + 1)).prodMk
            (continuous_matrixSandwichCLM.measurable.comp (P.measurable_pathOp N)))
      have hEval : Measurable (fun h => prefixMomentIntegrand P (Q.toPolicy P) 0 N h X) :=
        (ContinuousLinearMap.apply ℂ (QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix c d) X).continuous.measurable.comp hm
      refine ⟨hEval.stronglyMeasurable.aestronglyMeasurable, ?_⟩
      exact ((prefixMomentIntegrand_integrable P (Q.toPolicy P) 0 N hc hd).hasFiniteIntegral.norm.mul_const ‖X‖).mono'
          (Eventually.of_forall fun h =>
            (prefixMomentIntegrand P (Q.toPolicy P) 0 N h).le_opNorm X)

private theorem terminalIntegral_eq_pos (P : SquareProcess a b R) (N : ℕ)
    (Q : FinalTerminal a b c d R N) (X : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix a b)
    (hc : 0 < c) (hd : 0 < d) :
    (∫ h, terminalIntegrand P N Q X h ∂historyMeasure P N) =
      finiteHorizonChannel P N Q X := by
  cases N with
  | zero => simp [terminalIntegrand, historyMeasure, cumulativeOp, finiteHorizonChannel,
      quantumChannelFrom]
  | succ N =>
      have hChannel : finiteHorizonChannel P (N + 1) Q =
          prefixMoment P (Q.toPolicy P) 0 N := by
        change quantumChannelFrom P (Q.toPolicy P) (N + 1) 0 PUnit.unit = _
        rw [rootMoment, prefixMoment_iter P (Q.toPolicy P) N 0 hc hd]
        simp only [Nat.zero_add]
      rw [hChannel, prefixMoment, ContinuousLinearMap.integral_apply
        (prefixMomentIntegrand_integrable P (Q.toPolicy P) 0 N hc hd) X]
      change (∫ h, terminalIntegrand P (N + 1) Q X h ∂P.prefixMeasure N) = _
      apply integral_congr_ae
      exact Eventually.of_forall fun h => by
        simp only [terminalIntegrand, cumulativeOp, prefixMomentIntegrand,
          quantumChannelFrom, ContinuousLinearMap.comp_apply, matrixSandwichCLM_apply]

theorem terminalIntegrand_integrable (P : SquareProcess a b R) (N : ℕ)
    (Q : FinalTerminal a b c d R N) (X : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix a b) :
    Integrable (terminalIntegrand P N Q X) (historyMeasure P N) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · have heq : terminalIntegrand P N Q X = fun _ => 0 :=
      funext fun _ => Subsingleton.elim _ _
    rw [heq]
    exact integrable_zero _ _ _
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · have heq : terminalIntegrand P N Q X = fun _ => 0 :=
        funext fun _ => Subsingleton.elim _ _
      rw [heq]
      exact integrable_zero _ _ _
    · exact terminalIntegrand_integrable_pos P N Q X hc hd

theorem terminalIntegral_eq_finiteHorizonChannel (P : SquareProcess a b R) (N : ℕ)
    (Q : FinalTerminal a b c d R N) (X : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix a b) :
    (∫ h, terminalIntegrand P N Q X h ∂historyMeasure P N) =
      finiteHorizonChannel P N Q X := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · exact Subsingleton.elim _ _
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact Subsingleton.elim _ _
    · exact terminalIntegral_eq_pos P N Q X hc hd

end QuantumProver.MatrixSquareTerminalPrefixIntegral
