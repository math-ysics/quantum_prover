import QuantumProver.InformationTheory.ElegantJointMeasurement.SquareProcess
import QuantumProver.InformationTheory.WernerEndpoint.VariableCPDensityProtocol

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace QuantumProver.MatrixSquareQuantumTerminal

open MeasureTheory ProbabilityTheory Matrix Filter
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess
open QuantumProver.WernerEndpoint
open LocalChannelMoments
open QuantumProver.SuperchannelDiscrimination
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

universe u

abbrev LocalMap := MatrixVariableCPDensityProtocol.LocalMap
abbrev Channel := MatrixVariableCPDensityProtocol.Channel
abbrev JointMatrix := QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.JointMatrix

variable {R : Type u} [MeasurableSpace R] {a b c d : ℕ}

structure TerminalPolicy (a b c d : ℕ) (R : Type u) [MeasurableSpace R] where
  alice : (n : ℕ) → History R n → LocalMap a c
  bob : (n : ℕ) → History R n → LocalMap b d
  alice_measurable : ∀ n, Measurable (alice n)
  bob_measurable : ∀ n, Measurable (bob n)
  alice_cp : ∀ n h, CPTPKraus.CompletelyPositive (alice n h).toLinearMap
  bob_cp : ∀ n h, CPTPKraus.CompletelyPositive (bob n h).toLinearMap
  alice_tp : ∀ n h, CPTPKraus.TracePreserving (alice n h).toLinearMap
  bob_tp : ∀ n h, CPTPKraus.TracePreserving (bob n h).toLinearMap

structure FinalTerminal (a b c d : ℕ) (R : Type u) [MeasurableSpace R] (N : ℕ) where
  alice : History R N → LocalMap a c
  bob : History R N → LocalMap b d
  alice_measurable : Measurable alice
  bob_measurable : Measurable bob
  alice_cp : ∀ h, CPTPKraus.CompletelyPositive (alice h).toLinearMap
  bob_cp : ∀ h, CPTPKraus.CompletelyPositive (bob h).toLinearMap
  alice_tp : ∀ h, CPTPKraus.TracePreserving (alice h).toLinearMap
  bob_tp : ∀ h, CPTPKraus.TracePreserving (bob h).toLinearMap

theorem history_nonempty (P : SquareProcess a b R) (N : ℕ) : Nonempty (History R N) := by
  cases N with
  | zero => exact inferInstance
  | succ N =>
      let := P.prefixMeasure_isProbability N
      exact nonempty_of_isProbabilityMeasure (P.prefixMeasure N)

namespace FinalTerminal

variable {N : ℕ} (Q : FinalTerminal a b c d R N) (P : SquareProcess a b R)

def extendAlice (n : ℕ) (h : History R n) : LocalMap a c :=
  if hn : n = N then Q.alice (hn ▸ h)
  else Q.alice (Classical.choice (history_nonempty P N))

def extendBob (n : ℕ) (h : History R n) : LocalMap b d :=
  if hn : n = N then Q.bob (hn ▸ h)
  else Q.bob (Classical.choice (history_nonempty P N))

def toPolicy : TerminalPolicy a b c d R where
  alice := Q.extendAlice P
  bob := Q.extendBob P
  alice_measurable n := by
    classical
    change Measurable (fun h : History R n => Q.extendAlice P n h)
    by_cases hn : n = N
    · subst n
      simpa [extendAlice] using Q.alice_measurable
    · simp [extendAlice, hn]
  bob_measurable n := by
    classical
    change Measurable (fun h : History R n => Q.extendBob P n h)
    by_cases hn : n = N
    · subst n
      simpa [extendBob] using Q.bob_measurable
    · simp [extendBob, hn]
  alice_cp n h := by
    classical
    unfold extendAlice
    split <;> apply Q.alice_cp
  bob_cp n h := by
    classical
    unfold extendBob
    split <;> apply Q.bob_cp
  alice_tp n h := by
    classical
    unfold extendAlice
    split <;> apply Q.alice_tp
  bob_tp n h := by
    classical
    unfold extendBob
    split <;> apply Q.bob_tp

@[simp] theorem toPolicy_alice_final (h : History R N) :
    (Q.toPolicy P).alice N h = Q.alice h := by
  simp [toPolicy, extendAlice]

@[simp] theorem toPolicy_bob_final (h : History R N) :
    (Q.toPolicy P).bob N h = Q.bob h := by
  simp [toPolicy, extendBob]

end FinalTerminal

theorem continuous_aliceReference {a b p : ℕ} :
    Continuous (fun Φ : LocalMap a p => ContinuousCPProtocol.aliceReferenceCLM
      (b := b) Φ.toLinearMap) := by
  apply continuous_clm_apply.mpr
  intro X
  apply continuous_matrix
  intro i j
  change Continuous (fun Φ : LocalMap a p =>
    Φ (fun k l => X (k, i.2) (l, j.2)) i.1 j.1)
  fun_prop

theorem continuous_bobReference {a b p : ℕ} :
    Continuous (fun Φ : LocalMap b p => ContinuousCPProtocol.bobReferenceCLM
      (a := a) Φ.toLinearMap) := by
  apply continuous_clm_apply.mpr
  intro X
  apply continuous_matrix
  intro i j
  change Continuous (fun Φ : LocalMap b p =>
    Φ (fun k l => X (i.1, k) (j.1, l)) i.2 j.2)
  fun_prop

def terminalChannel (Q : TerminalPolicy a b c d R) (n : ℕ) (h : History R n) :
    Channel c d a b :=
  (ContinuousCPProtocol.bobReferenceCLM (a := c) (Q.bob n h).toLinearMap).comp
    (ContinuousCPProtocol.aliceReferenceCLM (b := b) (Q.alice n h).toLinearMap)

def terminalProtocol (Q : TerminalPolicy a b c d R) (n : ℕ) (h : History R n) :
    MatrixCPProtocol.FiniteCPProtocol c d a b :=
  .alice (h := 1) (fun _ => (Q.alice n h).toLinearMap) (fun _ => Q.alice_cp n h)
    (by intro X; simpa using Q.alice_tp n h X) (fun _ =>
      .bob (h := 1) (fun _ => (Q.bob n h).toLinearMap) (fun _ => Q.bob_cp n h)
        (by intro X; simpa using Q.bob_tp n h X) (fun _ =>
          .terminal (1 : LocalMatrix c) (1 : LocalMatrix d) (by simp) (by simp)))

theorem terminalProtocol_apply (Q : TerminalPolicy a b c d R)
    (n : ℕ) (h : History R n) (X : JointMatrix a b) :
    (terminalProtocol Q n h).apply X = terminalChannel Q n h X := by
  simp [terminalProtocol, MatrixCPProtocol.FiniteCPProtocol.apply, terminalChannel,
    ContinuousCPProtocol.aliceReferenceCLM_apply, ContinuousCPProtocol.bobReferenceCLM_apply]

theorem terminalProtocol_channel (Q : TerminalPolicy a b c d R)
    (n : ℕ) (h : History R n) :
    MatrixContinuousCPProtocol.finiteCPChannel (terminalProtocol Q n h) =
      terminalChannel Q n h := by
  apply ContinuousLinearMap.ext
  intro X
  exact terminalProtocol_apply Q n h X

theorem terminalChannel_measurable (Q : TerminalPolicy a b c d R) (n : ℕ) :
    Measurable (terminalChannel Q n) := by
  have ha := (continuous_aliceReference (a := a) (b := b) (p := c)).measurable.comp
    (Q.alice_measurable n)
  have hb := (continuous_bobReference (a := c) (b := b) (p := d)).measurable.comp
    (Q.bob_measurable n)
  have hm : Continuous (fun z : Channel c d c b × Channel c b a b => z.1.comp z.2) :=
    continuous_fst.clm_comp continuous_snd
  exact hm.measurable.comp (hb.prodMk ha)

theorem sandwich_completelyPositive (K : LocalMatrix a) :
    CPTPKraus.CompletelyPositive (matrixSandwichCLM K).toLinearMap :=
  (CPTPKraus.completelyPositive_iff_EJMCP _).mpr (QuantumProver.ElegantJointMeasurement.CP.sandwichMap_completelyPositive K)

theorem aliceReference_sandwich (K : LocalMatrix a) :
    ContinuousCPProtocol.aliceReferenceCLM (b := b) (matrixSandwichCLM K).toLinearMap =
      leftSandwichCLM K := by
  ext X i j
  change QuantumProver.ElegantJointMeasurement.CP.leftApplication (QuantumProver.ElegantJointMeasurement.CP.sandwichMap K) X i j = _
  rw [QuantumProver.ElegantJointMeasurement.CP.leftApplication_sandwichMap]
  simp only [QuantumProver.ElegantJointMeasurement.CP.leftKrausApplication, leftSandwichCLM_apply,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

theorem bobReference_sandwich (K : LocalMatrix b) :
    ContinuousCPProtocol.bobReferenceCLM (a := a) (matrixSandwichCLM K).toLinearMap =
      rightSandwichCLM K := by
  ext X i j
  change QuantumProver.ElegantJointMeasurement.CP.rightApplication (QuantumProver.ElegantJointMeasurement.CP.sandwichMap K) X i j = _
  rw [QuantumProver.ElegantJointMeasurement.CP.rightApplication_sandwichMap]
  simp only [QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication, rightSandwichCLM_apply,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

def traceMulCLM (X : LocalMatrix a) : LocalMatrix a →L[ℂ] ℂ :=
  ({ toFun := fun G => (G * X).trace
     map_add' := by intro G H; simp [Matrix.add_mul]
     map_smul' := by intro z G; simp } :
      LocalMatrix a →ₗ[ℂ] ℂ).toContinuousLinearMap

theorem sandwich_trace (K X : LocalMatrix a) :
    (matrixSandwichCLM K X).trace = traceMulCLM X (Kᴴ * K) := by
  rw [matrixSandwichCLM_apply]
  change (K * X * Kᴴ).trace = (Kᴴ * K * X).trace
  rw [Matrix.trace_mul_comm (K * X) Kᴴ, Matrix.mul_assoc]

theorem alice_trace_complete (P : SquareProcess a b R) (n : ℕ) (h : History R n)
    (ht : P.aliceTurn n h = true) (X : LocalMatrix a) :
    (∫ x, (matrixSandwichCLM (P.aliceK n h x) X).trace ∂P.kernel n h) = X.trace := by
  simp only [sandwich_trace]
  rw [(traceMulCLM X).integral_comp_comm (P.alice_integrable n h ht),
    P.alice_complete n h ht]
  simp [traceMulCLM]

theorem bob_trace_complete (P : SquareProcess a b R) (n : ℕ) (h : History R n)
    (ht : P.aliceTurn n h ≠ true) (X : LocalMatrix b) :
    (∫ x, (matrixSandwichCLM (P.bobK n h x) X).trace ∂P.kernel n h) = X.trace := by
  simp only [sandwich_trace]
  rw [(traceMulCLM X).integral_comp_comm (P.bob_integrable n h ht),
    P.bob_complete n h ht]
  simp [traceMulCLM]

def quantumChannelFrom (P : SquareProcess a b R) (Q : TerminalPolicy a b c d R) :
    (height n : ℕ) → History R n → Channel c d a b
  | 0, n, h => terminalChannel Q n h
  | height + 1, n, h =>
      let next := fun x => quantumChannelFrom P Q height (n + 1) (appendHistory n (h,x))
      if P.aliceTurn n h = true then
        ∫ x, (next x).comp (leftSandwichCLM (P.aliceK n h x)) ∂P.kernel n h
      else ∫ x, (next x).comp (rightSandwichCLM (P.bobK n h x)) ∂P.kernel n h

theorem quantumChannelFrom_measurable (P : SquareProcess a b R)
    (Q : TerminalPolicy a b c d R) (height n : ℕ) :
    Measurable (quantumChannelFrom P Q height n) := by
  classical
  induction height generalizing n with
  | zero => exact terminalChannel_measurable Q n
  | succ height ih =>
      have hc : Measurable (fun z : History R n × R =>
          quantumChannelFrom P Q height (n + 1) (appendHistory n z)) :=
        (ih (n + 1)).comp (appendHistory n).measurable
      have hm : Continuous (fun z : Channel c d a b × Channel a b a b => z.1.comp z.2) :=
        continuous_fst.clm_comp continuous_snd
      have ha : Measurable (fun z : History R n × R =>
          (quantumChannelFrom P Q height (n + 1) (appendHistory n z)).comp
            (leftSandwichCLM (P.aliceK n z.1 z.2))) :=
        hm.measurable.comp (hc.prodMk
          (continuous_leftSandwichCLM.measurable.comp (P.alice_measurable n)))
      have hb : Measurable (fun z : History R n × R =>
          (quantumChannelFrom P Q height (n + 1) (appendHistory n z)).comp
            (rightSandwichCLM (P.bobK n z.1 z.2))) :=
        hm.measurable.comp (hc.prodMk
          (continuous_rightSandwichCLM.measurable.comp (P.bob_measurable n)))
      have haI := (ha.stronglyMeasurable.integral_kernel_prod_right'
        (E := Channel c d a b) (κ := P.kernel n)).measurable
      have hbI := (hb.stronglyMeasurable.integral_kernel_prod_right'
        (E := Channel c d a b) (κ := P.kernel n)).measurable
      have ht : MeasurableSet {h : History R n | P.aliceTurn n h = true} :=
        measurableSet_eq_fun (P.turn_measurable n) measurable_const
      simp only [quantumChannelFrom]
      exact Measurable.ite ht haI hbI

def treeFrom (P : SquareProcess a b R) (Q : TerminalPolicy a b c d R) :
    (height n : ℕ) → History R n → MatrixVariableCPDensityProtocol.Tree.{u} c d a b height
  | 0, n, h => .finite 0 (terminalProtocol Q n h)
  | height + 1, n, h =>
      let child := fun x => treeFrom P Q height (n + 1) (appendHistory n (h,x))
      if P.aliceTurn n h = true then
        .alice R inferInstance (P.kernel n h) (fun _ => a)
          (fun x => matrixSandwichCLM (P.aliceK n h x)) child
      else .bob R inferInstance (P.kernel n h) (fun _ => b)
        (fun x => matrixSandwichCLM (P.bobK n h x)) child

theorem treeFrom_channel (P : SquareProcess a b R) (Q : TerminalPolicy a b c d R)
    (height n : ℕ) (h : History R n) :
    MatrixVariableCPDensityProtocol.channel (treeFrom P Q height n h) =
      quantumChannelFrom P Q height n h := by
  classical
  induction height generalizing n with
  | zero => exact terminalProtocol_channel Q n h
  | succ height ih =>
      by_cases ht : P.aliceTurn n h = true
      · simp only [treeFrom, quantumChannelFrom, ite_eq_left ht, MatrixVariableCPDensityProtocol.channel]
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by dsimp only; rw [ih, aliceReference_sandwich])
      · simp only [treeFrom, quantumChannelFrom, ite_eq_right ht, MatrixVariableCPDensityProtocol.channel]
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by dsimp only; rw [ih, bobReference_sandwich])

private theorem measurable_fiberMk {D : Type*} (F : D → Type*)
    [∀ i, MeasurableSpace (F i)] (i : D) : Measurable (Sigma.mk i : F i → Sigma F) := by
  intro s hs
  change MeasurableSet[⨅ j, (inferInstance : MeasurableSpace (F j)).map (Sigma.mk j)] s at hs
  rw [MeasurableSpace.measurableSet_iInf] at hs
  exact hs i

theorem treeFrom_regular (P : SquareProcess a b R) (Q : TerminalPolicy a b c d R)
    (height n : ℕ) (h : History R n) :
    MatrixVariableCPDensityProtocol.Regular (treeFrom P Q height n h) := by
  classical
  induction height generalizing n with
  | zero => trivial
  | succ height ih =>
      have hc : Measurable (fun x => MatrixVariableCPDensityProtocol.channel
          (treeFrom P Q height (n + 1) (appendHistory n (h,x)))) := by
        simpa only [treeFrom_channel, Function.comp_def, id_eq] using
          (quantumChannelFrom_measurable P Q height (n + 1)).comp
            ((appendHistory n).measurable.comp (measurable_const.prodMk measurable_id))
      have hchild := fun x => ih (n + 1) (appendHistory n (h,x))
      by_cases ht : P.aliceTurn n h = true
      · simp only [treeFrom, ite_eq_left ht, MatrixVariableCPDensityProtocol.Regular]
        refine ⟨?_, fun x => sandwich_completelyPositive _,
          alice_trace_complete P n h ht, hchild⟩
        exact (measurable_fiberMk (MatrixVariableCPDensityProtocol.AliceFiber c d a b) a).comp
          ((continuous_matrixSandwichCLM.measurable.comp
            ((P.alice_measurable n).comp (measurable_const.prodMk measurable_id))).prodMk hc)
      · simp only [treeFrom, ite_eq_right ht, MatrixVariableCPDensityProtocol.Regular]
        refine ⟨?_, fun x => sandwich_completelyPositive _,
          bob_trace_complete P n h ht, hchild⟩
        exact (measurable_fiberMk (MatrixVariableCPDensityProtocol.BobFiber c d a b) b).comp
          ((continuous_matrixSandwichCLM.measurable.comp
            ((P.bob_measurable n).comp (measurable_const.prodMk measurable_id))).prodMk hc)

theorem quantumChannelFrom_congr_final (P : SquareProcess a b R)
    (Q Q' : TerminalPolicy a b c d R) (height n : ℕ)
    (ha : Q.alice (height+n) = Q'.alice (height+n))
    (hb : Q.bob (height+n) = Q'.bob (height+n)) (h : History R n) :
    quantumChannelFrom P Q height n h = quantumChannelFrom P Q' height n h := by
  classical
  induction height generalizing n with
  | zero =>
      have ha' : Q.alice n = Q'.alice n :=
        Eq.mp (congrArg (fun k : ℕ => Q.alice k = Q'.alice k) (Nat.zero_add n)) ha
      have hb' : Q.bob n = Q'.bob n :=
        Eq.mp (congrArg (fun k : ℕ => Q.bob k = Q'.bob k) (Nat.zero_add n)) hb
      simp only [quantumChannelFrom, terminalChannel, ha', hb']
  | succ height ih =>
      have hindex : height + (n+1) = height+1+n := by omega
      have ha' : Q.alice (height+(n+1)) = Q'.alice (height+(n+1)) := by
        rw [hindex]
        exact ha
      have hb' : Q.bob (height+(n+1)) = Q'.bob (height+(n+1)) := by
        rw [hindex]
        exact hb
      have he : ∀ x, quantumChannelFrom P Q height (n+1) (appendHistory n (h,x)) =
          quantumChannelFrom P Q' height (n+1) (appendHistory n (h,x)) :=
        fun x => ih (n+1) ha' hb' (appendHistory n (h,x))
      simp only [quantumChannelFrom, he]

def finiteHorizonChannel (P : SquareProcess a b R) (N : ℕ)
    (Q : FinalTerminal a b c d R N) : Channel c d a b :=
  quantumChannelFrom P (Q.toPolicy P) N 0 PUnit.unit

def finiteHorizonTree (P : SquareProcess a b R) (N : ℕ)
    (Q : FinalTerminal a b c d R N) : MatrixVariableCPDensityProtocol.Tree.{u} c d a b N :=
  treeFrom P (Q.toPolicy P) N 0 PUnit.unit

theorem finiteHorizonTree_channel (P : SquareProcess a b R) (N : ℕ)
    (Q : FinalTerminal a b c d R N) :
    MatrixVariableCPDensityProtocol.channel (finiteHorizonTree P N Q) = finiteHorizonChannel P N Q :=
  treeFrom_channel P (Q.toPolicy P) N 0 PUnit.unit

theorem finiteHorizonTree_regular (P : SquareProcess a b R) (N : ℕ)
    (Q : FinalTerminal a b c d R N) :
    MatrixVariableCPDensityProtocol.Regular (finiteHorizonTree P N Q) :=
  treeFrom_regular P (Q.toPolicy P) N 0 PUnit.unit

theorem finiteHorizonChannel_cptp (P : SquareProcess a b R) (N : ℕ)
    (Q : FinalTerminal a b c d R N) (hc : 0 < c) (hd : 0 < d) :
    CPTPKraus.CompletelyPositive (finiteHorizonChannel P N Q).toLinearMap ∧
      CPTPKraus.TracePreserving (finiteHorizonChannel P N Q).toLinearMap := by
  rw [← finiteHorizonTree_channel]
  exact MatrixVariableCPDensityProtocol.channel_cptp _ (finiteHorizonTree_regular P N Q) hc hd

theorem exists_finiteProtocol_channel_approx (P : SquareProcess a b R) (N : ℕ)
    (Q : FinalTerminal a b c d R N) (hc : 0 < c) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : OperationalEndpointCost.FiniteLocalProtocol c d a b,
      ‖MatrixContinuousStateProtocol.finiteChannel U - finiteHorizonChannel P N Q‖ < ε := by
  rw [← finiteHorizonTree_channel]
  exact MatrixVariableCPDensityProtocol.exists_finiteProtocol_channel_approx
    _ (finiteHorizonTree_regular P N Q) hc hd ε hε

theorem exists_finiteProtocol_output_approx (P : SquareProcess a b R) (N : ℕ)
    (Q : FinalTerminal a b c d R N) (hc : 0 < c) (hd : 0 < d)
    (X : JointMatrix a b) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : OperationalEndpointCost.FiniteLocalProtocol c d a b,
      ‖U.apply X - finiteHorizonChannel P N Q X‖ < ε := by
  rw [← finiteHorizonTree_channel]
  exact MatrixVariableCPDensityProtocol.exists_finiteProtocol_output_approx
    _ (finiteHorizonTree_regular P N Q) hc hd X ε hε

theorem pureOutput_mem_outputClosure (P : SquareProcess a b R) (N : ℕ)
    (Q : FinalTerminal a b c d R N) (hc : 0 < c) (hd : 0 < d)
    (ψ : Fin a × Fin b → ℂ) :
    finiteHorizonChannel P N Q (QuantumProver.WernerEndpoint.pureDensity ψ) ∈
      EndpointProtocolClosure.outputClosure ψ := by
  rw [← finiteHorizonTree_channel]
  exact MatrixVariableCPDensityProtocol.channel_pureOutput_mem_outputClosure
    _ (finiteHorizonTree_regular P N Q) hc hd ψ

theorem pureOutput_isDensity (P : SquareProcess a b R) (N : ℕ)
    (Q : FinalTerminal a b c d R N) (hc : 0 < c) (hd : 0 < d)
    (ψ : Fin a × Fin b → ℂ) (hψ : QuantumProver.WernerEndpoint.vectorNormSq ψ = 1) :
    QuantumProver.QuantumEntropy.IsDensity
      (finiteHorizonChannel P N Q (QuantumProver.WernerEndpoint.pureDensity ψ)) := by
  rw [← finiteHorizonTree_channel]
  exact MatrixVariableCPDensityProtocol.channel_pureOutput_isDensity
    _ (finiteHorizonTree_regular P N Q) hc hd ψ hψ

end QuantumProver.MatrixSquareQuantumTerminal
