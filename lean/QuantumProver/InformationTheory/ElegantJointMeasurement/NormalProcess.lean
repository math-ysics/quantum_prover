import QuantumProver.QuantumChannels.SquareTerminalPrefixIntegral
import QuantumProver.QuantumChannels.NuclearKernelTransport
import QuantumProver.QuantumChannels.NuclearContinuationTransport
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalInstrumentRealization
import QuantumProver.InformationTheory.ElegantJointMeasurement.SquareProcess
import QuantumProver.InformationTheory.ElegantJointMeasurement.HilbertPendingTensor
import QuantumProver.QuantumChannels.NormalTensorInstrument
import QuantumProver.QuantumChannels.NormalRightTensor
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalFiniteTerminal
import QuantumProver.QuantumChannels.SquareQuantumTerminal
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCostModels
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalAncillaPreparation
import QuantumProver.QuantumChannels.NormalAmplifiedInstrument
import QuantumProver.QuantumChannels.NormalStateKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace QuantumProver.ElegantJointMeasurement.NormalProcess

open MeasureTheory ProbabilityTheory Set Function Filter InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess
open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
open QuantumProver.HilbertNuclearCompression
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

local instance workspaceNuclearMeasurable : MeasurableSpace (Nuclear Workspace) := borel _
local instance workspaceNuclearBorel : BorelSpace (Nuclear Workspace) := ⟨rfl⟩
local instance inputChannelMeasurable (d : ℕ) : MeasurableSpace (InputChannel d) := borel _
local instance inputChannelBorel (d : ℕ) : BorelSpace (InputChannel d) := ⟨rfl⟩

instance workspaceSeparable : TopologicalSpace.SeparableSpace Workspace := by
  have hs : TopologicalSpace.IsSeparable
      (closure (Submodule.span ℂ (Set.range commonBasis) : Set Workspace)) :=
    ((Set.countable_range commonBasis).isSeparable.span (R := ℂ)).closure
  have hc : closure (Submodule.span ℂ (Set.range commonBasis) : Set Workspace) = Set.univ := by
    rw [← Submodule.topologicalClosure_coe, commonBasis.dense_span, Submodule.top_coe]
  exact TopologicalSpace.isSeparable_univ_iff.mp (hc ▸ hs)

section Reindexing
variable {E F H Z Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [MeasurableSpace H] [MeasurableSpace Z] [MeasurableSpace Ω]

def pullbackInstrument
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument F E H Ω)
    (f : Z → H) (hf : Measurable f) :
    QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument F E Z Ω where
  operation z s := P.operation (f z) s
  empty z := P.empty (f z)
  countable_additivity z s hs hd T := P.countable_additivity (f z) s hs hd T
  completelyPositive z s hs := P.completelyPositive (f z) s hs
  measurable_coordinate s hs T x y := (P.measurable_coordinate s hs T x y).comp hf
  trace_preserving z T := P.trace_preserving (f z) T

@[simp] theorem pullbackInstrument_operation
    (P : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument F E H Ω)
    (f : Z → H) (hf : Measurable f) (z : Z) (s : Set Ω) (T : Nuclear F) :
    (pullbackInstrument P f hf).operation z s T = P.operation (f z) s T := rfl

end Reindexing

variable {R : Type*} [MeasurableSpace R]

def coarseHistory (n : ℕ) (h : History (FineRecord R) n) : History R n :=
  ((QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess.historyPairEquiv n).symm h).1

theorem measurable_coarseHistory (n : ℕ) :
    Measurable (coarseHistory (R := R) n) :=
  measurable_fst.comp
    (QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess.historyPairEquiv n).symm.measurable

theorem coarseHistory_append (n : ℕ)
    (h : History (FineRecord R) n) (r : FineRecord R) :
    coarseHistory (n+1) (appendHistory n (h,r)) =
      appendHistory n (coarseHistory n h,r.1) := by
  let e := QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess.historyPairEquiv
    (R := R) (Q := ℕ × ℕ) n
  have he := QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess.historyPair_append n
    (e.symm h).1 (e.symm h).2 r.1 r.2
  have hh : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess.historyPairEquiv n
      ((e.symm h).1,(e.symm h).2) = h := e.apply_symm_apply h
  rw [hh] at he
  have ht := congrArg (fun u =>
    ((QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess.historyPairEquiv (n+1)).symm u).1) he
  simpa only [MeasurableEquiv.symm_apply_apply, coarseHistory] using ht.symm

structure PendingLayer (a b : ℕ) (R : Type*) [MeasurableSpace R] (n : ℕ) where
  aliceRecovery : History (FineRecord R) n → InputChannel a
  bobRecovery : History (FineRecord R) n → InputChannel b
  alice_measurable : Measurable aliceRecovery
  bob_measurable : Measurable bobRecovery
  alice_cp : ∀ h, CompletelyPositive (operationOperator (aliceRecovery h).toLinearMap)
  bob_cp : ∀ h, CompletelyPositive (operationOperator (bobRecovery h).toLinearMap)
  alice_trace : ∀ h X, QuantumProver.HilbertNuclearTrace.trace (aliceRecovery h X) = Matrix.trace X
  bob_trace : ∀ h X, QuantumProver.HilbertNuclearTrace.trace (bobRecovery h X) = Matrix.trace X

section Initial
variable {d : ℕ}

def initialChannel (J : EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] Workspace) : InputChannel d :=
  QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery (commonBasis 0) J.toContinuousLinearMap

theorem positiveInput_isometry (J : EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] Workspace) :
    QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInput J.toContinuousLinearMap = 1 := by
  have hJ : J.toContinuousLinearMap.adjoint ∘L J.toContinuousLinearMap = 1 :=
    (ContinuousLinearMap.isometry_iff_adjoint_comp_self _).mp J.isometry
  rw [QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInput, QuantumProver.ElegantJointMeasurement.HilbertPolar.gram, hJ, CFC.sqrt_one]

theorem initialChannel_apply (J : EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] Workspace)
    (X : InputMatrix d) :
    initialChannel J X = compose J.toContinuousLinearMap J.toContinuousLinearMap.adjoint
      (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix X) := by
  have ht := QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearRecovery_square (commonBasis 0)
    J.toContinuousLinearMap (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix X)
  rw [positiveInput_isometry] at ht
  have hid : compose (1 : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
      (1 : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
      (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix X) = QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix X := by
    apply QuantumProver.NuclearOperator.toOperator_injective
    rw [toOperator_compose]
    rfl
  rw [hid] at ht
  exact ht

theorem initialChannel_cp (J : EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] Workspace) :
    CompletelyPositive (operationOperator (initialChannel J).toLinearMap) :=
  QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery_completelyPositive _ _

theorem initialChannel_trace (J : EuclideanSpace ℂ (Fin d) →ₗᵢ[ℂ] Workspace)
    (X : InputMatrix d) :
    QuantumProver.HilbertNuclearTrace.trace (initialChannel J X) = Matrix.trace X :=
  QuantumProver.ElegantJointMeasurement.HilbertRecovery.trace_matrixRecovery _ (commonBasis.orthonormal.norm_eq_one 0) _ X

end Initial

namespace MatrixProcess
variable {a b : ℕ} (P : MatrixProcess a b R)

def initialPending : PendingLayer a b R 0 where
  aliceRecovery _ := initialChannel P.initialAlice
  bobRecovery _ := initialChannel P.initialBob
  alice_measurable := measurable_const
  bob_measurable := measurable_const
  alice_cp _ := initialChannel_cp _
  bob_cp _ := initialChannel_cp _
  alice_trace _ := initialChannel_trace _
  bob_trace _ := initialChannel_trace _

def absorbedAlice (n : ℕ) (L : PendingLayer a b R n) :
    Instrument (Fin a) Workspace (History (FineRecord R) n) R :=
  QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.absorbInstrument
    (pullbackInstrument (P.alice n) (coarseHistory n) (measurable_coarseHistory n))
    L.aliceRecovery L.alice_cp
    (QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization.stronglyMeasurable_finite_evaluation _ L.alice_measurable)
    L.alice_trace

def absorbedBob (n : ℕ) (L : PendingLayer a b R n) :
    Instrument (Fin b) Workspace (History (FineRecord R) n) R :=
  QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.absorbInstrument
    (pullbackInstrument (P.bob n) (coarseHistory n) (measurable_coarseHistory n))
    L.bobRecovery L.bob_cp
    (QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization.stronglyMeasurable_finite_evaluation _ L.bob_measurable)
    L.bob_trace

@[simp] theorem absorbedAlice_operation (n : ℕ) (L : PendingLayer a b R n)
    (h : History (FineRecord R) n) (s : Set R) (X : InputMatrix a) :
    (P.absorbedAlice n L).operation h s X =
      (P.alice n).operation (coarseHistory n h) s (L.aliceRecovery h X) := rfl

@[simp] theorem absorbedBob_operation (n : ℕ) (L : PendingLayer a b R n)
    (h : History (FineRecord R) n) (s : Set R) (X : InputMatrix b) :
    (P.absorbedBob n L).operation h s X =
      (P.bob n).operation (coarseHistory n h) s (L.bobRecovery h X) := rfl

end MatrixProcess

section Packet
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]

local instance packetOperationMeasurable : MeasurableSpace (PhysicalOperation I Workspace) := borel _
local instance packetOperationBorel : BorelSpace (PhysicalOperation I Workspace) := ⟨rfl⟩
local instance packetKrausMeasurable :
    MeasurableSpace (EuclideanSpace ℂ I →L[ℂ] Workspace) := borel _
local instance packetKrausBorel : BorelSpace (EuclideanSpace ℂ I →L[ℂ] Workspace) := ⟨rfl⟩

structure SquareCompilation (P : Instrument I Workspace H Ω) where
  square : H → Ω × ℕ → Matrix I I ℂ
  recovery : H → Ω × ℕ → PhysicalOperation I Workspace
  kraus : H → Ω × ℕ → Unit ⊕ I → EuclideanSpace ℂ I →L[ℂ] Workspace
  kraus_measurable : ∀ q, Measurable (fun z : H × (Ω × ℕ) => kraus z.1 z.2 q)
  kraus_complete : ∀ h z, ∑ q, (kraus h z q).adjoint ∘L kraus h z q = 1
  recovery_eq_kraus : ∀ h z X, recovery h z X =
    ∑ q, compose (kraus h z q) (kraus h z q).adjoint (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix X)
  square_measurable : Measurable (fun z : H × (Ω × ℕ) => square z.1 z.2)
  recovery_measurable : Measurable (fun z : H × (Ω × ℕ) => recovery z.1 z.2)
  recovery_cp : ∀ h z, CompletelyPositive (operationOperator (recovery h z).toLinearMap)
  recovery_trace : ∀ h z X, QuantumProver.HilbertNuclearTrace.trace (recovery h z X) = Matrix.trace X
  action_integrable : ∀ h X, Integrable
    (fun z : Ω × ℕ => recovery h z (square h z * X * star (square h z)))
    (fineProbabilityKernel P h)
  event_action : ∀ h (s : Set Ω), MeasurableSet s → ∀ X,
    (∫ z : Ω × ℕ, recovery h z (square h z * X * star (square h z))
      ∂((P.referenceKernel h).restrict s).prod labelProbability) = P.operation h s X
  gram_integrable : ∀ h, Integrable (fun z : Ω × ℕ => star (square h z) * square h z)
    (fineProbabilityKernel P h)
  gram_complete : ∀ h, (∫ z : Ω × ℕ, star (square h z) * square h z
    ∂fineProbabilityKernel P h) = 1

theorem exists_squareCompilation
    [MeasurableSpace.CountableOrCountablyGenerated H Ω]
    (P : Instrument I Workspace H Ω) : Nonempty (SquareCompilation P) := by
  let φ : Workspace := commonBasis 0
  have hφ : ‖φ‖ = 1 := commonBasis.orthonormal.norm_eq_one 0
  obtain ⟨W, hK, hS, hR, hCP, hTP, hI, hE, hG, hC⟩ :=
    QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization.exists_physical_separable_probability_square_compilation_with_fallback
      P φ (fun _ => hφ)
  have hSm : @Measurable (H × (Ω × ℕ)) (Matrix I I ℂ) _ (borel (Matrix I I ℂ))
      (fun z => QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W z.1 z.2))) := hS
  exact ⟨{ square := fun h z => QuantumProver.ElegantJointMeasurement.HilbertPolar.positiveInputMatrix (unvectorize (W h z))
           recovery := fun h z => QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ (unvectorize (W h z))
           kraus := fun h z => QuantumProver.ElegantJointMeasurement.HilbertRecovery.recoveryKraus φ (unvectorize (W h z))
           kraus_measurable := fun q =>
             (QuantumProver.ElegantJointMeasurement.HilbertRecovery.measurable_recoveryKraus φ q).comp hK
           kraus_complete := fun h z => QuantumProver.ElegantJointMeasurement.HilbertRecovery.recoveryKraus_complete φ hφ _
           recovery_eq_kraus := by
             intro h z X
             simp only [QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery, ContinuousLinearMap.comp_apply,
               QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearRecovery, sum_apply,
               QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearSandwich]
           square_measurable := by
             apply Measurable.of_eval
             intro i
             apply Measurable.of_eval
             intro j
             letI : MeasurableSpace (Matrix I I ℂ) := borel _
             letI : BorelSpace (Matrix I I ℂ) := ⟨rfl⟩
             exact (QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.matrixEntry i j).continuous.measurable.comp hSm
           recovery_measurable := hR
           recovery_cp := hCP
           recovery_trace := hTP
           action_integrable := hI
           event_action := hE
           gram_integrable := hG
           gram_complete := hC }⟩

def squareCompilation [MeasurableSpace.CountableOrCountablyGenerated H Ω]
    (P : Instrument I Workspace H Ω) : SquareCompilation P :=
  Classical.choice (exists_squareCompilation P)

end Packet

end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess

open MeasureTheory ProbabilityTheory Set Function Filter InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
open QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

def aliceRefineEquiv {R : Type*} [MeasurableSpace R] :
    ((R × ℕ) × ℕ) ≃ᵐ FineRecord R := MeasurableEquiv.prodAssoc

def bobRefineEquiv {R : Type*} [MeasurableSpace R] :
    ((R × ℕ) × ℕ) ≃ᵐ FineRecord R :=
  MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl R) MeasurableEquiv.prodComm)

section Fine
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable (C : Instrument I Workspace H Ω)

def aliceFineKernel : Kernel H (FineRecord Ω) :=
  ((fineProbabilityKernel C).prod (Kernel.const H labelProbability)).map aliceRefineEquiv

def bobFineKernel : Kernel H (FineRecord Ω) :=
  ((fineProbabilityKernel C).prod (Kernel.const H labelProbability)).map bobRefineEquiv

instance aliceFineKernel_markov : IsMarkovKernel (aliceFineKernel C) :=
  Kernel.IsMarkovKernel.map _ aliceRefineEquiv.measurable

instance bobFineKernel_markov : IsMarkovKernel (bobFineKernel C) :=
  Kernel.IsMarkovKernel.map _ bobRefineEquiv.measurable

theorem aliceFineKernel_apply (h : H) :
    aliceFineKernel C h = ((fineProbabilityKernel C h).prod labelProbability).map
      aliceRefineEquiv := by
  rw [aliceFineKernel, Kernel.map_apply _ aliceRefineEquiv.measurable,
    Kernel.prod_apply, Kernel.const_apply]

theorem bobFineKernel_apply (h : H) :
    bobFineKernel C h = ((fineProbabilityKernel C h).prod labelProbability).map
      bobRefineEquiv := by
  rw [bobFineKernel, Kernel.map_apply _ bobRefineEquiv.measurable,
    Kernel.prod_apply, Kernel.const_apply]

variable (Q : SquareCompilation C)

def aliceFineSquare (z : H × FineRecord Ω) : Matrix I I ℂ :=
  Q.square z.1 (z.2.1,z.2.2.1)

def bobFineSquare (z : H × FineRecord Ω) : Matrix I I ℂ :=
  Q.square z.1 (z.2.1,z.2.2.2)

theorem measurable_aliceFineSquare : Measurable (aliceFineSquare C Q) :=
  Q.square_measurable.comp
    (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.fst))

theorem measurable_bobFineSquare : Measurable (bobFineSquare C Q) :=
  Q.square_measurable.comp
    (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.snd))

theorem aliceFineSquare_gram_integrable (h : H) :
    Integrable (fun r => star (aliceFineSquare C Q (h,r)) * aliceFineSquare C Q (h,r))
      (aliceFineKernel C h) := by
  rw [aliceFineKernel_apply, integrable_map_equiv]
  change Integrable (fun r : (Ω × ℕ) × ℕ => star (Q.square h r.1) * Q.square h r.1)
    ((fineProbabilityKernel C h).prod labelProbability)
  exact (Q.gram_integrable h).comp_fst _

theorem bobFineSquare_gram_integrable (h : H) :
    Integrable (fun r => star (bobFineSquare C Q (h,r)) * bobFineSquare C Q (h,r))
      (bobFineKernel C h) := by
  rw [bobFineKernel_apply, integrable_map_equiv]
  change Integrable (fun r : (Ω × ℕ) × ℕ => star (Q.square h r.1) * Q.square h r.1)
    ((fineProbabilityKernel C h).prod labelProbability)
  exact (Q.gram_integrable h).comp_fst _

theorem integral_aliceFineSquare_gram (h : H) :
    (∫ r, star (aliceFineSquare C Q (h,r)) * aliceFineSquare C Q (h,r)
      ∂aliceFineKernel C h) = 1 := by
  rw [aliceFineKernel_apply, integral_map_equiv]
  change (∫ r : (Ω × ℕ) × ℕ, star (Q.square h r.1) * Q.square h r.1
    ∂(fineProbabilityKernel C h).prod labelProbability) = 1
  have hi := integral_fun_fst (μ := fineProbabilityKernel C h) (ν := labelProbability)
    (fun r => star (Q.square h r) * Q.square h r)
  refine hi.trans ?_
  rw [Q.gram_complete]
  simp

theorem integral_bobFineSquare_gram (h : H) :
    (∫ r, star (bobFineSquare C Q (h,r)) * bobFineSquare C Q (h,r)
      ∂bobFineKernel C h) = 1 := by
  rw [bobFineKernel_apply, integral_map_equiv]
  change (∫ r : (Ω × ℕ) × ℕ, star (Q.square h r.1) * Q.square h r.1
    ∂(fineProbabilityKernel C h).prod labelProbability) = 1
  have hi := integral_fun_fst (μ := fineProbabilityKernel C h) (ν := labelProbability)
    (fun r => star (Q.square h r) * Q.square h r)
  refine hi.trans ?_
  rw [Q.gram_complete]
  simp

theorem integral_aliceFineSquare_recovered_event (h : H) (s : Set Ω)
    (hs : MeasurableSet s) (X : Matrix I I ℂ) :
    (∫ r : FineRecord Ω,
      Q.recovery h (r.1,r.2.1)
        (aliceFineSquare C Q (h,r) * X * star (aliceFineSquare C Q (h,r)))
      ∂((((C.referenceKernel h).restrict s).prod labelProbability).prod labelProbability).map
        aliceRefineEquiv) = C.operation h s X := by
  rw [integral_map_equiv]
  change (∫ r : (Ω × ℕ) × ℕ,
    Q.recovery h r.1 (Q.square h r.1 * X * star (Q.square h r.1))
    ∂(((C.referenceKernel h).restrict s).prod labelProbability).prod labelProbability) = _
  have hi := integral_fun_fst
    (μ := ((C.referenceKernel h).restrict s).prod labelProbability) (ν := labelProbability)
    (fun z : Ω × ℕ => Q.recovery h z (Q.square h z * X * star (Q.square h z)))
  refine hi.trans ?_
  rw [Q.event_action h s hs X]
  simp

theorem integral_bobFineSquare_recovered_event (h : H) (s : Set Ω)
    (hs : MeasurableSet s) (X : Matrix I I ℂ) :
    (∫ r : FineRecord Ω,
      Q.recovery h (r.1,r.2.2)
        (bobFineSquare C Q (h,r) * X * star (bobFineSquare C Q (h,r)))
      ∂((((C.referenceKernel h).restrict s).prod labelProbability).prod labelProbability).map
        bobRefineEquiv) = C.operation h s X := by
  rw [integral_map_equiv]
  change (∫ r : (Ω × ℕ) × ℕ,
    Q.recovery h r.1 (Q.square h r.1 * X * star (Q.square h r.1))
    ∂(((C.referenceKernel h).restrict s).prod labelProbability).prod labelProbability) = _
  have hi := integral_fun_fst
    (μ := ((C.referenceKernel h).restrict s).prod labelProbability) (ν := labelProbability)
    (fun z : Ω × ℕ => Q.recovery h z (Q.square h z * X * star (Q.square h z)))
  refine hi.trans ?_
  rw [Q.event_action h s hs X]
  simp

end Fine
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess

open MeasureTheory ProbabilityTheory Set Function InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.HilbertChoi
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

variable {a b : ℕ} {R : Type*} [MeasurableSpace R]
local instance recursionInputChannelMeasurable (d : ℕ) : MeasurableSpace (InputChannel d) := borel _
local instance recursionInputChannelBorel (d : ℕ) : BorelSpace (InputChannel d) := ⟨rfl⟩

namespace MatrixProcess
variable (P : MatrixProcess a b R)

def fineTurn (n : ℕ) (h : History (FineRecord R) n) : Bool :=
  P.aliceTurn n (coarseHistory n h)

theorem measurable_fineTurn (n : ℕ) : Measurable (P.fineTurn n) :=
  (P.turn_measurable n).comp (measurable_coarseHistory n)

def aliceNextProjection (n : ℕ) (h : History (FineRecord R) (n+1)) :
    History (FineRecord R) n × (R × ℕ) :=
  let z := (appendHistory n).symm h
  (z.1,(z.2.1,z.2.2.1))

def bobNextProjection (n : ℕ) (h : History (FineRecord R) (n+1)) :
    History (FineRecord R) n × (R × ℕ) :=
  let z := (appendHistory n).symm h
  (z.1,(z.2.1,z.2.2.2))

theorem measurable_aliceNextProjection (n : ℕ) :
    Measurable (aliceNextProjection (R := R) n) :=
  (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.fst)).comp
    (appendHistory n).symm.measurable

theorem measurable_bobNextProjection (n : ℕ) :
    Measurable (bobNextProjection (R := R) n) :=
  (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.snd)).comp
    (appendHistory n).symm.measurable

section Step
variable [NeZero a] [NeZero b]
variable (n : ℕ) (L : PendingLayer a b R n)
variable (A : SquareCompilation (P.absorbedAlice n L))
variable (B : SquareCompilation (P.absorbedBob n L))

def nextAliceRecovery (h : History (FineRecord R) (n+1)) : InputChannel a :=
  let z := (appendHistory n).symm h
  if P.fineTurn n z.1 = true then
    A.recovery (aliceNextProjection n h).1 (aliceNextProjection n h).2
  else L.aliceRecovery z.1

def nextBobRecovery (h : History (FineRecord R) (n+1)) : InputChannel b :=
  let z := (appendHistory n).symm h
  if P.fineTurn n z.1 = true then L.bobRecovery z.1
  else B.recovery (bobNextProjection n h).1 (bobNextProjection n h).2

theorem measurable_nextAliceRecovery : Measurable (P.nextAliceRecovery n L A) := by
  have hm : Measurable (fun h : History (FineRecord R) (n+1) =>
      (appendHistory n).symm h) := (appendHistory n).symm.measurable
  exact Measurable.ite
    (measurableSet_eq_fun ((P.measurable_fineTurn n).comp hm.fst) measurable_const)
    (A.recovery_measurable.comp (measurable_aliceNextProjection n))
    (L.alice_measurable.comp hm.fst)

theorem measurable_nextBobRecovery : Measurable (P.nextBobRecovery n L B) := by
  have hm : Measurable (fun h : History (FineRecord R) (n+1) =>
      (appendHistory n).symm h) := (appendHistory n).symm.measurable
  exact Measurable.ite
    (measurableSet_eq_fun ((P.measurable_fineTurn n).comp hm.fst) measurable_const)
    (L.bob_measurable.comp hm.fst)
    (B.recovery_measurable.comp (measurable_bobNextProjection n))

def nextPendingWith : PendingLayer a b R (n+1) where
  aliceRecovery := P.nextAliceRecovery n L A
  bobRecovery := P.nextBobRecovery n L B
  alice_measurable := P.measurable_nextAliceRecovery n L A
  bob_measurable := P.measurable_nextBobRecovery n L B
  alice_cp h := by
    dsimp [nextAliceRecovery]
    split_ifs
    · exact A.recovery_cp _ _
    · exact L.alice_cp _
  bob_cp h := by
    dsimp [nextBobRecovery]
    split_ifs
    · exact L.bob_cp _
    · exact B.recovery_cp _ _
  alice_trace h X := by
    dsimp [nextAliceRecovery]
    split_ifs
    · exact A.recovery_trace _ _ X
    · exact L.alice_trace _ X
  bob_trace h X := by
    dsimp [nextBobRecovery]
    split_ifs
    · exact L.bob_trace _ X
    · exact B.recovery_trace _ _ X

end Step

section Compiler
variable [NeZero a] [NeZero b] [StandardBorelSpace R]

def aliceCompilation (n : ℕ) (L : PendingLayer a b R n) :
    SquareCompilation (P.absorbedAlice n L) := squareCompilation _

def bobCompilation (n : ℕ) (L : PendingLayer a b R n) :
    SquareCompilation (P.absorbedBob n L) := squareCompilation _

def nextPending (n : ℕ) (L : PendingLayer a b R n) : PendingLayer a b R (n+1) :=
  P.nextPendingWith n L (P.aliceCompilation n L) (P.bobCompilation n L)

def layers (P : MatrixProcess a b R) : (n : ℕ) → PendingLayer a b R n
  | 0 => P.initialPending
  | n+1 => P.nextPending n (P.layers n)

def stepKernel (n : ℕ) (L : PendingLayer a b R n) :
    Kernel (History (FineRecord R) n) (FineRecord R) :=
  Kernel.piecewise (measurableSet_eq_fun (P.measurable_fineTurn n) (measurable_const (a := true)))
    (aliceFineKernel (P.absorbedAlice n L)) (bobFineKernel (P.absorbedBob n L))

instance stepKernel_markov (n : ℕ) (L : PendingLayer a b R n) :
    IsMarkovKernel (P.stepKernel n L) := by
  unfold stepKernel
  infer_instance

theorem stepKernel_eq_alice (n : ℕ) (L : PendingLayer a b R n)
    (h : History (FineRecord R) n) (hh : P.fineTurn n h = true) :
    P.stepKernel n L h = aliceFineKernel (P.absorbedAlice n L) h := by
  simp only [stepKernel, Kernel.piecewise_apply, mem_setOf_eq, if_pos hh]

theorem stepKernel_eq_bob (n : ℕ) (L : PendingLayer a b R n)
    (h : History (FineRecord R) n) (hh : P.fineTurn n h ≠ true) :
    P.stepKernel n L h = bobFineKernel (P.absorbedBob n L) h := by
  simp only [stepKernel, Kernel.piecewise_apply, mem_setOf_eq, if_neg hh]

def squareProcess : SquareProcess a b (FineRecord R) where
  kernel n := P.stepKernel n (P.layers n)
  markov n := P.stepKernel_markov n _
  aliceTurn := P.fineTurn
  turn_measurable := P.measurable_fineTurn
  aliceK n h r := aliceFineSquare (P.absorbedAlice n (P.layers n))
    (P.aliceCompilation n (P.layers n)) (h,r)
  bobK n h r := bobFineSquare (P.absorbedBob n (P.layers n))
    (P.bobCompilation n (P.layers n)) (h,r)
  alice_measurable n := measurable_aliceFineSquare _ _
  bob_measurable n := measurable_bobFineSquare _ _
  alice_integrable n h hh := by
    rw [P.stepKernel_eq_alice n _ h hh]
    exact aliceFineSquare_gram_integrable _ _ h
  bob_integrable n h hh := by
    rw [P.stepKernel_eq_bob n _ h hh]
    exact bobFineSquare_gram_integrable _ _ h
  alice_complete n h hh := by
    rw [P.stepKernel_eq_alice n _ h hh]
    exact integral_aliceFineSquare_gram _ _ h
  bob_complete n h hh := by
    rw [P.stepKernel_eq_bob n _ h hh]
    exact integral_bobFineSquare_gram _ _ h

end Compiler
end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess

open MeasureTheory ProbabilityTheory Set Function InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

section FineAction
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable (C : Instrument I Workspace H Ω) (Q : SquareCompilation C)

theorem aliceFineSquare_recovered_integrable (h : H) (X : Matrix I I ℂ) :
    Integrable (fun r : FineRecord Ω => Q.recovery h (r.1,r.2.1)
      (aliceFineSquare C Q (h,r) * X * star (aliceFineSquare C Q (h,r))))
      (aliceFineKernel C h) := by
  rw [aliceFineKernel_apply, integrable_map_equiv]
  change Integrable (fun r : (Ω × ℕ) × ℕ =>
    Q.recovery h r.1 (Q.square h r.1 * X * star (Q.square h r.1)))
    ((fineProbabilityKernel C h).prod labelProbability)
  exact (Q.action_integrable h X).comp_fst _

theorem bobFineSquare_recovered_integrable (h : H) (X : Matrix I I ℂ) :
    Integrable (fun r : FineRecord Ω => Q.recovery h (r.1,r.2.2)
      (bobFineSquare C Q (h,r) * X * star (bobFineSquare C Q (h,r))))
      (bobFineKernel C h) := by
  rw [bobFineKernel_apply, integrable_map_equiv]
  change Integrable (fun r : (Ω × ℕ) × ℕ =>
    Q.recovery h r.1 (Q.square h r.1 * X * star (Q.square h r.1)))
    ((fineProbabilityKernel C h).prod labelProbability)
  exact (Q.action_integrable h X).comp_fst _

end FineAction

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

theorem layers_alice_succ_of_alice (n : ℕ) (h : History (FineRecord R) n)
    (r : FineRecord R) (hh : P.fineTurn n h = true) :
    (P.layers (n+1)).aliceRecovery (appendHistory n (h,r)) =
      (P.aliceCompilation n (P.layers n)).recovery h (r.1,r.2.1) := by
  change (P.nextPending n (P.layers n)).aliceRecovery _ = _
  simp only [nextPending, nextPendingWith, nextAliceRecovery, aliceNextProjection,
    MeasurableEquiv.symm_apply_apply, hh, if_true]

theorem layers_bob_succ_of_alice (n : ℕ) (h : History (FineRecord R) n)
    (r : FineRecord R) (hh : P.fineTurn n h = true) :
    (P.layers (n+1)).bobRecovery (appendHistory n (h,r)) = (P.layers n).bobRecovery h := by
  change (P.nextPending n (P.layers n)).bobRecovery _ = _
  simp only [nextPending, nextPendingWith, nextBobRecovery,
    MeasurableEquiv.symm_apply_apply, hh, if_true]

theorem layers_alice_succ_of_bob (n : ℕ) (h : History (FineRecord R) n)
    (r : FineRecord R) (hh : P.fineTurn n h ≠ true) :
    (P.layers (n+1)).aliceRecovery (appendHistory n (h,r)) = (P.layers n).aliceRecovery h := by
  change (P.nextPending n (P.layers n)).aliceRecovery _ = _
  simp only [nextPending, nextPendingWith, nextAliceRecovery,
    MeasurableEquiv.symm_apply_apply, if_neg hh]

theorem layers_bob_succ_of_bob (n : ℕ) (h : History (FineRecord R) n)
    (r : FineRecord R) (hh : P.fineTurn n h ≠ true) :
    (P.layers (n+1)).bobRecovery (appendHistory n (h,r)) =
      (P.bobCompilation n (P.layers n)).recovery h (r.1,r.2.2) := by
  change (P.nextPending n (P.layers n)).bobRecovery _ = _
  simp only [nextPending, nextPendingWith, nextBobRecovery, bobNextProjection,
    MeasurableEquiv.symm_apply_apply, if_neg hh]

theorem layers_alice_action_integrable (n : ℕ) (h : History (FineRecord R) n)
    (hh : P.fineTurn n h = true) (X : InputMatrix a) :
    Integrable (fun r : FineRecord R => (P.layers (n+1)).aliceRecovery (appendHistory n (h,r))
      (P.squareProcess.aliceK n h r * X * star (P.squareProcess.aliceK n h r)))
      (P.squareProcess.kernel n h) := by
  simp_rw [P.layers_alice_succ_of_alice n h _ hh]
  change Integrable (fun r : FineRecord R =>
    (P.aliceCompilation n (P.layers n)).recovery h (r.1,r.2.1)
      (aliceFineSquare (P.absorbedAlice n (P.layers n)) (P.aliceCompilation n (P.layers n)) (h,r) * X *
        star (aliceFineSquare (P.absorbedAlice n (P.layers n))
          (P.aliceCompilation n (P.layers n)) (h,r)))) (P.stepKernel n (P.layers n) h)
  rw [P.stepKernel_eq_alice n _ h hh]
  exact aliceFineSquare_recovered_integrable _ _ h X

theorem layers_bob_action_integrable (n : ℕ) (h : History (FineRecord R) n)
    (hh : P.fineTurn n h ≠ true) (X : InputMatrix b) :
    Integrable (fun r : FineRecord R => (P.layers (n+1)).bobRecovery (appendHistory n (h,r))
      (P.squareProcess.bobK n h r * X * star (P.squareProcess.bobK n h r)))
      (P.squareProcess.kernel n h) := by
  simp_rw [P.layers_bob_succ_of_bob n h _ hh]
  change Integrable (fun r : FineRecord R =>
    (P.bobCompilation n (P.layers n)).recovery h (r.1,r.2.2)
      (bobFineSquare (P.absorbedBob n (P.layers n)) (P.bobCompilation n (P.layers n)) (h,r) * X *
        star (bobFineSquare (P.absorbedBob n (P.layers n))
          (P.bobCompilation n (P.layers n)) (h,r)))) (P.stepKernel n (P.layers n) h)
  rw [P.stepKernel_eq_bob n _ h hh]
  exact bobFineSquare_recovered_integrable _ _ h X

theorem layers_alice_physical_event (n : ℕ) (h : History (FineRecord R) n)
    (hh : P.fineTurn n h = true) (s : Set R) (hs : MeasurableSet s) (X : InputMatrix a) :
    (∫ r : FineRecord R, (P.layers (n+1)).aliceRecovery (appendHistory n (h,r))
      (P.squareProcess.aliceK n h r * X * star (P.squareProcess.aliceK n h r))
      ∂(((((P.absorbedAlice n (P.layers n)).referenceKernel h).restrict s).prod labelProbability).prod
        labelProbability).map aliceRefineEquiv) =
      (P.alice n).operation (coarseHistory n h) s ((P.layers n).aliceRecovery h X) := by
  simp_rw [P.layers_alice_succ_of_alice n h _ hh]
  exact integral_aliceFineSquare_recovered_event (P.absorbedAlice n (P.layers n))
    (P.aliceCompilation n (P.layers n)) h s hs X

theorem layers_bob_physical_event (n : ℕ) (h : History (FineRecord R) n)
    (hh : P.fineTurn n h ≠ true) (s : Set R) (hs : MeasurableSet s) (X : InputMatrix b) :
    (∫ r : FineRecord R, (P.layers (n+1)).bobRecovery (appendHistory n (h,r))
      (P.squareProcess.bobK n h r * X * star (P.squareProcess.bobK n h r))
      ∂(((((P.absorbedBob n (P.layers n)).referenceKernel h).restrict s).prod labelProbability).prod
        labelProbability).map bobRefineEquiv) =
      (P.bob n).operation (coarseHistory n h) s ((P.layers n).bobRecovery h X) := by
  simp_rw [P.layers_bob_succ_of_bob n h _ hh]
  exact integral_bobFineSquare_recovered_event (P.absorbedBob n (P.layers n))
    (P.bobCompilation n (P.layers n)) h s hs X

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set Function InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

section RestrictedKernel
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable (C : Instrument I Workspace H Ω)

theorem aliceFineKernel_restrict (h : H) (s : Set Ω) :
    (aliceFineKernel C h).restrict {r : FineRecord Ω | r.1 ∈ s} =
      ((((C.referenceKernel h).restrict s).prod labelProbability).prod labelProbability).map
        aliceRefineEquiv := by
  rw [aliceFineKernel_apply, aliceRefineEquiv.restrict_map]
  congr 1
  rw [fineProbabilityKernel_apply]
  have he : aliceRefineEquiv ⁻¹' {r : FineRecord Ω | r.1 ∈ s} =
      (s ×ˢ (Set.univ : Set ℕ)) ×ˢ (Set.univ : Set ℕ) := by
    ext z
    simp [aliceRefineEquiv]
    rfl
  rw [he, ← Measure.restrict_prod_eq_prod_univ, ← Measure.restrict_prod_eq_prod_univ]

theorem bobFineKernel_restrict (h : H) (s : Set Ω) :
    (bobFineKernel C h).restrict {r : FineRecord Ω | r.1 ∈ s} =
      ((((C.referenceKernel h).restrict s).prod labelProbability).prod labelProbability).map
        bobRefineEquiv := by
  rw [bobFineKernel_apply, bobRefineEquiv.restrict_map]
  congr 1
  rw [fineProbabilityKernel_apply]
  have he : bobRefineEquiv ⁻¹' {r : FineRecord Ω | r.1 ∈ s} =
      (s ×ˢ (Set.univ : Set ℕ)) ×ˢ (Set.univ : Set ℕ) := by
    ext z
    simp [bobRefineEquiv]
    rfl
  rw [he, ← Measure.restrict_prod_eq_prod_univ, ← Measure.restrict_prod_eq_prod_univ]

end RestrictedKernel

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] (P : MatrixProcess a b R)

theorem record_nonempty [NeZero a] (P : MatrixProcess a b R) : Nonempty R :=
  nonempty_of_isProbabilityMeasure ((P.absorbedAlice 0 P.initialPending).referenceKernel PUnit.unit)

theorem fineRecord_nonempty [NeZero a] (P : MatrixProcess a b R) : Nonempty (FineRecord R) := by
  letI : Nonempty R := P.record_nonempty
  infer_instance

variable [NeZero a] [NeZero b] [StandardBorelSpace R]

theorem layers_alice_physical_setIntegral (n : ℕ) (h : History (FineRecord R) n)
    (hh : P.fineTurn n h = true) (s : Set R) (hs : MeasurableSet s) (X : InputMatrix a) :
    (∫ r in {r : FineRecord R | r.1 ∈ s},
      (P.layers (n+1)).aliceRecovery (appendHistory n (h,r))
        (P.squareProcess.aliceK n h r * X * star (P.squareProcess.aliceK n h r))
      ∂P.squareProcess.kernel n h) =
      (P.alice n).operation (coarseHistory n h) s ((P.layers n).aliceRecovery h X) := by
  change (∫ r, (P.layers (n+1)).aliceRecovery (appendHistory n (h,r))
    (P.squareProcess.aliceK n h r * X * star (P.squareProcess.aliceK n h r))
    ∂(P.stepKernel n (P.layers n) h).restrict {r : FineRecord R | r.1 ∈ s}) = _
  rw [P.stepKernel_eq_alice n _ h hh, aliceFineKernel_restrict]
  exact P.layers_alice_physical_event n h hh s hs X

theorem layers_bob_physical_setIntegral (n : ℕ) (h : History (FineRecord R) n)
    (hh : P.fineTurn n h ≠ true) (s : Set R) (hs : MeasurableSet s) (X : InputMatrix b) :
    (∫ r in {r : FineRecord R | r.1 ∈ s},
      (P.layers (n+1)).bobRecovery (appendHistory n (h,r))
        (P.squareProcess.bobK n h r * X * star (P.squareProcess.bobK n h r))
      ∂P.squareProcess.kernel n h) =
      (P.bob n).operation (coarseHistory n h) s ((P.layers n).bobRecovery h X) := by
  change (∫ r, (P.layers (n+1)).bobRecovery (appendHistory n (h,r))
    (P.squareProcess.bobK n h r * X * star (P.squareProcess.bobK n h r))
    ∂(P.stepKernel n (P.layers n) h).restrict {r : FineRecord R | r.1 ∈ s}) = _
  rw [P.stepKernel_eq_bob n _ h hh, bobFineKernel_restrict]
  exact P.layers_bob_physical_event n h hh s hs X

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set Function InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.HilbertNuclearCompression
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

abbrev RecoveryFamily (d : ℕ) :=
  Unit ⊕ Fin d → EuclideanSpace ℂ (Fin d) →L[ℂ] Workspace

local instance familyKrausMeasurable (d : ℕ) :
    MeasurableSpace (EuclideanSpace ℂ (Fin d) →L[ℂ] Workspace) := borel _
local instance familyKrausBorel (d : ℕ) :
    BorelSpace (EuclideanSpace ℂ (Fin d) →L[ℂ] Workspace) := ⟨rfl⟩

def recoveryFamilyAction {d : ℕ} (K : RecoveryFamily d) (X : InputMatrix d) : Nuclear Workspace :=
  ∑ q, compose (K q) (K q).adjoint (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix X)

theorem matrixRecovery_eq_familyAction {d : ℕ} (φ : Workspace)
    (K : EuclideanSpace ℂ (Fin d) →L[ℂ] Workspace) (X : InputMatrix d) :
    QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery φ K X =
      recoveryFamilyAction (QuantumProver.ElegantJointMeasurement.HilbertRecovery.recoveryKraus φ K) X := by
  simp only [recoveryFamilyAction, QuantumProver.ElegantJointMeasurement.HilbertRecovery.matrixRecovery,
    ContinuousLinearMap.comp_apply, QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearRecovery, sum_apply,
    QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearSandwich]

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

def layersAliceKraus (P : MatrixProcess a b R) :
    (n : ℕ) → History (FineRecord R) n → RecoveryFamily a
  | 0, _ => QuantumProver.ElegantJointMeasurement.HilbertRecovery.recoveryKraus
      (QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.commonBasis 0) P.initialAlice.toContinuousLinearMap
  | n+1, h =>
      let z := (appendHistory n).symm h
      if P.fineTurn n z.1 = true then
        (P.aliceCompilation n (P.layers n)).kraus z.1 (z.2.1,z.2.2.1)
      else P.layersAliceKraus n z.1

def layersBobKraus (P : MatrixProcess a b R) :
    (n : ℕ) → History (FineRecord R) n → RecoveryFamily b
  | 0, _ => QuantumProver.ElegantJointMeasurement.HilbertRecovery.recoveryKraus
      (QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.commonBasis 0) P.initialBob.toContinuousLinearMap
  | n+1, h =>
      let z := (appendHistory n).symm h
      if P.fineTurn n z.1 = true then P.layersBobKraus n z.1
      else (P.bobCompilation n (P.layers n)).kraus z.1 (z.2.1,z.2.2.2)

theorem layersAliceKraus_append (n : ℕ) (h : History (FineRecord R) n) (r : FineRecord R) :
    P.layersAliceKraus (n+1) (appendHistory n (h,r)) =
      if P.fineTurn n h = true then (P.aliceCompilation n (P.layers n)).kraus h (r.1,r.2.1)
      else P.layersAliceKraus n h := by
  simp only [layersAliceKraus, MeasurableEquiv.symm_apply_apply]

theorem layersBobKraus_append (n : ℕ) (h : History (FineRecord R) n) (r : FineRecord R) :
    P.layersBobKraus (n+1) (appendHistory n (h,r)) =
      if P.fineTurn n h = true then P.layersBobKraus n h
      else (P.bobCompilation n (P.layers n)).kraus h (r.1,r.2.2) := by
  simp only [layersBobKraus, MeasurableEquiv.symm_apply_apply]

theorem layersAliceKraus_complete (n : ℕ) :
    ∀ h, ∑ q, (P.layersAliceKraus n h q).adjoint ∘L P.layersAliceKraus n h q = 1 := by
  induction n with
  | zero =>
    intro h
    exact QuantumProver.ElegantJointMeasurement.HilbertRecovery.recoveryKraus_complete _
      (QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.commonBasis.orthonormal.norm_eq_one 0) _
  | succ n ih =>
    intro h
    rcases (appendHistory n).surjective h with ⟨⟨g,r⟩,rfl⟩
    rw [P.layersAliceKraus_append]
    split_ifs
    · exact (P.aliceCompilation n (P.layers n)).kraus_complete _ _
    · exact ih g

theorem layersBobKraus_complete (n : ℕ) :
    ∀ h, ∑ q, (P.layersBobKraus n h q).adjoint ∘L P.layersBobKraus n h q = 1 := by
  induction n with
  | zero =>
    intro h
    exact QuantumProver.ElegantJointMeasurement.HilbertRecovery.recoveryKraus_complete _
      (QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.commonBasis.orthonormal.norm_eq_one 0) _
  | succ n ih =>
    intro h
    rcases (appendHistory n).surjective h with ⟨⟨g,r⟩,rfl⟩
    rw [P.layersBobKraus_append]
    split_ifs
    · exact ih g
    · exact (P.bobCompilation n (P.layers n)).kraus_complete _ _

theorem layers_aliceRecovery_eq_familyAction (n : ℕ) :
    ∀ h X, (P.layers n).aliceRecovery h X = recoveryFamilyAction (P.layersAliceKraus n h) X := by
  induction n with
  | zero =>
    intro h X
    exact matrixRecovery_eq_familyAction _ _ X
  | succ n ih =>
    intro h X
    rcases (appendHistory n).surjective h with ⟨⟨g,r⟩,rfl⟩
    by_cases hh : P.fineTurn n g = true
    · rw [P.layers_alice_succ_of_alice n g r hh, P.layersAliceKraus_append, if_pos hh]
      exact (P.aliceCompilation n (P.layers n)).recovery_eq_kraus _ _ X
    · rw [P.layers_alice_succ_of_bob n g r hh, P.layersAliceKraus_append, if_neg hh]
      exact ih g X

theorem layers_bobRecovery_eq_familyAction (n : ℕ) :
    ∀ h X, (P.layers n).bobRecovery h X = recoveryFamilyAction (P.layersBobKraus n h) X := by
  induction n with
  | zero =>
    intro h X
    exact matrixRecovery_eq_familyAction _ _ X
  | succ n ih =>
    intro h X
    rcases (appendHistory n).surjective h with ⟨⟨g,r⟩,rfl⟩
    by_cases hh : P.fineTurn n g = true
    · rw [P.layers_bob_succ_of_alice n g r hh, P.layersBobKraus_append, if_pos hh]
      exact ih g X
    · rw [P.layers_bob_succ_of_bob n g r hh, P.layersBobKraus_append, if_neg hh]
      exact (P.bobCompilation n (P.layers n)).recovery_eq_kraus _ _ X

theorem measurable_layersAliceKraus (n : ℕ) : Measurable (P.layersAliceKraus n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hm : Measurable (fun h : History (FineRecord R) (n+1) =>
        (appendHistory n).symm h) := (appendHistory n).symm.measurable
    have hA : Measurable (fun h : History (FineRecord R) (n+1) =>
        (P.aliceCompilation n (P.layers n)).kraus
          (aliceNextProjection n h).1 (aliceNextProjection n h).2) := by
      apply Measurable.of_eval
      intro q
      exact ((P.aliceCompilation n (P.layers n)).kraus_measurable q).comp
        (measurable_aliceNextProjection n)
    exact Measurable.ite
      (measurableSet_eq_fun ((P.measurable_fineTurn n).comp hm.fst) measurable_const)
      hA (ih.comp hm.fst)

theorem measurable_layersBobKraus (n : ℕ) : Measurable (P.layersBobKraus n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hm : Measurable (fun h : History (FineRecord R) (n+1) =>
        (appendHistory n).symm h) := (appendHistory n).symm.measurable
    have hB : Measurable (fun h : History (FineRecord R) (n+1) =>
        (P.bobCompilation n (P.layers n)).kraus
          (bobNextProjection n h).1 (bobNextProjection n h).2) := by
      apply Measurable.of_eval
      intro q
      exact ((P.bobCompilation n (P.layers n)).kraus_measurable q).comp
        (measurable_bobNextProjection n)
    exact Measurable.ite
      (measurableSet_eq_fun ((P.measurable_fineTurn n).comp hm.fst) measurable_const)
      (ih.comp hm.fst) hB

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.HilbertPendingTensor QuantumProver.ElegantJointMeasurement.HilbertFiniteKrausPredual QuantumProver.ElegantJointMeasurement.NormalCPInstruments
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator Kronecker

abbrev JointWorkspace := Joint Workspace Workspace
abbrev JointInputMatrix (a b : ℕ) := Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ
abbrev workspaceTensor : Nuclear Workspace →L[ℂ]
    Nuclear Workspace →L[ℂ] Nuclear JointWorkspace :=
  tensorNuclear (E := Workspace) (F := Workspace) (E' := Workspace) (F' := Workspace)

local instance jointColumnWorkspaceMeasurable : MeasurableSpace Workspace := borel _
local instance jointColumnWorkspaceBorel : BorelSpace Workspace := ⟨rfl⟩
local instance jointColumnMapMeasurable (d : ℕ) :
    MeasurableSpace (EuclideanSpace ℂ (Fin d) →L[ℂ] Workspace) := borel _
local instance jointColumnMapBorel (d : ℕ) :
    BorelSpace (EuclideanSpace ℂ (Fin d) →L[ℂ] Workspace) := ⟨rfl⟩

theorem recoveryFamilyAction_eq_finiteKrausOperation {d : ℕ}
    (K : RecoveryFamily d) (X : InputMatrix d) :
    recoveryFamilyAction K X = finiteKrausOperation K X := by
  simp only [recoveryFamilyAction, finiteKrausOperation, finiteKrausChannel,
    ContinuousLinearMap.comp_apply, sum_apply, QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearSandwich]

theorem stronglyMeasurable_recoveryFamily_column
    {H : Type*} [MeasurableSpace H] {d : ℕ}
    (K : H → RecoveryFamily d) (hK : Measurable K)
    (q : Unit ⊕ Fin d) (i : Fin d) :
    StronglyMeasurable (fun h => K h q (EuclideanSpace.basisFun (Fin d) ℂ i)) := by
  have hrow : Measurable (fun h => K h q) := (measurable_pi_apply q).comp hK
  let eval : (EuclideanSpace ℂ (Fin d) →L[ℂ] Workspace) →L[ℂ] Workspace :=
    ContinuousLinearMap.apply ℂ Workspace (EuclideanSpace.basisFun (Fin d) ℂ i)
  exact (eval.continuous.measurable.comp hrow).stronglyMeasurable

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

def jointPendingOperation (n : ℕ) (h : History (FineRecord R) n) :
    PhysicalOperation (Fin a × Fin b) JointWorkspace :=
  jointOperation (P.layersAliceKraus n h) (P.layersBobKraus n h)

theorem jointPendingOperation_completelyPositive
    (n : ℕ) (h : History (FineRecord R) n) :
    CompletelyPositive (operationOperator (P.jointPendingOperation n h).toLinearMap) :=
  completelyPositive_jointOperation _ _

theorem jointPendingOperation_trace
    (n : ℕ) (h : History (FineRecord R) n) (X : JointInputMatrix a b) :
    QuantumProver.HilbertNuclearTrace.trace (P.jointPendingOperation n h X) = Matrix.trace X :=
  trace_jointOperation _ _ (P.layersAliceKraus_complete n h)
    (P.layersBobKraus_complete n h) X

theorem jointPendingOperation_product
    (n : ℕ) (h : History (FineRecord R) n) (X : InputMatrix a) (Y : InputMatrix b) :
    P.jointPendingOperation n h (X ⊗ₖ Y) =
      workspaceTensor ((P.layers n).aliceRecovery h X) ((P.layers n).bobRecovery h Y) := by
  have hA : finiteKrausOperation (P.layersAliceKraus n h) X = (P.layers n).aliceRecovery h X :=
    (recoveryFamilyAction_eq_finiteKrausOperation _ X).symm.trans
      (P.layers_aliceRecovery_eq_familyAction n h X).symm
  have hB : finiteKrausOperation (P.layersBobKraus n h) Y = (P.layers n).bobRecovery h Y :=
    (recoveryFamilyAction_eq_finiteKrausOperation _ Y).symm.trans
      (P.layers_bobRecovery_eq_familyAction n h Y).symm
  exact (jointOperation_product (P.layersAliceKraus n h) (P.layersBobKraus n h) X Y).trans
    (congrArg₂ (fun T U : Nuclear Workspace => workspaceTensor T U) hA hB)

theorem stronglyMeasurable_jointPendingOperation (n : ℕ) :
    StronglyMeasurable (P.jointPendingOperation n) := by
  exact stronglyMeasurable_jointOperation_of_basis _ _
    (fun q i => stronglyMeasurable_recoveryFamily_column _
      (P.measurable_layersAliceKraus n) q i)
    (fun q i => stronglyMeasurable_recoveryFamily_column _
      (P.measurable_layersBobKraus n) q i)

theorem stronglyMeasurable_jointPendingOperation_apply (n : ℕ)
    (X : History (FineRecord R) n → JointInputMatrix a b) (hX : StronglyMeasurable X) :
    StronglyMeasurable (fun h => P.jointPendingOperation n h (X h)) :=
  stronglyMeasurable_jointOperation_apply_of_basis _ _
    (fun q i => stronglyMeasurable_recoveryFamily_column _
      (P.measurable_layersAliceKraus n) q i)
    (fun q i => stronglyMeasurable_recoveryFamily_column _
      (P.measurable_layersBobKraus n) q i) X hX

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set Function InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator Kronecker

theorem jointInputMatrix_eq_columnBlocks {a b : ℕ} (X : JointInputMatrix a b) :
    X = ∑ st : Fin b × Fin b,
      Matrix.of (fun i j => X (i,st.1) (j,st.2)) ⊗ₖ Matrix.single st.1 st.2 (1 : ℂ) := by
  classical
  ext i j
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Matrix.single,
    Fintype.sum_prod_type, mul_ite, ite_and]

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

def physicalAliceInstrument (n : ℕ) :
    QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument JointWorkspace JointWorkspace (History R n) R :=
  QuantumProver.MatrixNormalTensorInstrument.tensorInstrument (G := Workspace) (P.alice n)

theorem physicalAliceInstrument_product (n : ℕ) (h : History R n)
    (s : Set R) (hs : MeasurableSet s) (T U : Nuclear Workspace) :
    (P.physicalAliceInstrument n).operation h s (workspaceTensor T U) =
      workspaceTensor ((P.alice n).operation h s T) U :=
  QuantumProver.MatrixNormalTensorInstrument.tensorInstrument_product_action (P.alice n) h s hs T U

def recoveredJointStep (n : ℕ) (h : History (FineRecord R) n)
    (r : FineRecord R) (X : JointInputMatrix a b) : Nuclear JointWorkspace :=
  P.jointPendingOperation (n+1) (appendHistory n (h,r))
    (P.squareProcess.localOp n h r * X * star (P.squareProcess.localOp n h r))

theorem recoveredJointStep_eq_columnBlocks (n : ℕ) (h : History (FineRecord R) n)
    (r : FineRecord R) (X : JointInputMatrix a b) :
    P.recoveredJointStep n h r X = ∑ st : Fin b × Fin b,
      P.recoveredJointStep n h r
        (Matrix.of (fun i j => X (i,st.1) (j,st.2)) ⊗ₖ Matrix.single st.1 st.2 (1 : ℂ)) := by
  calc
    _ = P.recoveredJointStep n h r (∑ st : Fin b × Fin b,
        Matrix.of (fun i j => X (i,st.1) (j,st.2)) ⊗ₖ Matrix.single st.1 st.2 (1 : ℂ)) :=
      congrArg (P.recoveredJointStep n h r) (jointInputMatrix_eq_columnBlocks X)
    _ = _ := by
      simp only [recoveredJointStep, Matrix.mul_sum, Matrix.sum_mul, map_sum]

theorem jointPendingOperation_eq_columnBlocks (n : ℕ) (h : History (FineRecord R) n)
    (X : JointInputMatrix a b) :
    P.jointPendingOperation n h X = ∑ st : Fin b × Fin b,
      P.jointPendingOperation n h
        (Matrix.of (fun i j => X (i,st.1) (j,st.2)) ⊗ₖ Matrix.single st.1 st.2 (1 : ℂ)) := by
  calc
    _ = P.jointPendingOperation n h (∑ st : Fin b × Fin b,
        Matrix.of (fun i j => X (i,st.1) (j,st.2)) ⊗ₖ Matrix.single st.1 st.2 (1 : ℂ)) :=
      congrArg (P.jointPendingOperation n h) (jointInputMatrix_eq_columnBlocks X)
    _ = _ := map_sum _ _ _

theorem recoveredJointStep_product_of_alice (n : ℕ) (h : History (FineRecord R) n)
    (hh : P.fineTurn n h = true) (r : FineRecord R) (X : InputMatrix a) (Y : InputMatrix b) :
    P.recoveredJointStep n h r (X ⊗ₖ Y) =
      workspaceTensor ((P.layers (n+1)).aliceRecovery (appendHistory n (h,r))
        (P.squareProcess.aliceK n h r * X * star (P.squareProcess.aliceK n h r)))
        ((P.layers n).bobRecovery h Y) := by
  have hl : P.squareProcess.localOp n h r =
      P.squareProcess.aliceK n h r ⊗ₖ (1 : InputMatrix b) := by
    change (if P.fineTurn n h = true then _ else _) = _
    exact if_pos hh
  unfold recoveredJointStep
  rw [hl]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have hb : (P.layers (n+1)).bobRecovery (appendHistory n (h,r)) Y =
      (P.layers n).bobRecovery h Y :=
    congrArg (fun C : InputChannel b => C Y) (P.layers_bob_succ_of_alice n h r hh)
  exact (P.jointPendingOperation_product (n+1) (appendHistory n (h,r))
    (P.squareProcess.aliceK n h r * X * star (P.squareProcess.aliceK n h r)) Y).trans
      (congrArg (fun U : Nuclear Workspace => workspaceTensor
        ((P.layers (n+1)).aliceRecovery (appendHistory n (h,r))
          (P.squareProcess.aliceK n h r * X * star (P.squareProcess.aliceK n h r))) U) hb)

theorem recoveredJointStep_product_integrable_of_alice
    (n : ℕ) (h : History (FineRecord R) n) (hh : P.fineTurn n h = true)
    (X : InputMatrix a) (Y : InputMatrix b) :
    Integrable (fun r => P.recoveredJointStep n h r (X ⊗ₖ Y)) (P.squareProcess.kernel n h) := by
  let L : Nuclear Workspace →L[ℂ] Nuclear JointWorkspace :=
    (workspaceTensor).flip
      ((P.layers n).bobRecovery h Y)
  have hi := L.integrable_comp (P.layers_alice_action_integrable n h hh X)
  exact hi.congr (ae_of_all _ (fun r =>
    (P.recoveredJointStep_product_of_alice n h hh r X Y).symm))

theorem recoveredJointStep_integrable_of_alice
    (n : ℕ) (h : History (FineRecord R) n) (hh : P.fineTurn n h = true)
    (X : JointInputMatrix a b) :
    Integrable (fun r => P.recoveredJointStep n h r X) (P.squareProcess.kernel n h) := by
  have hsum : Integrable (fun r => ∑ st : Fin b × Fin b,
      P.recoveredJointStep n h r
        (Matrix.of (fun i j => X (i,st.1) (j,st.2)) ⊗ₖ Matrix.single st.1 st.2 (1 : ℂ)))
      (P.squareProcess.kernel n h) :=
    integrable_finsetSum (μ := P.squareProcess.kernel n h)
      (f := fun st : Fin b × Fin b => fun r : FineRecord R =>
        P.recoveredJointStep n h r
          (Matrix.of (fun i j => X (i,st.1) (j,st.2)) ⊗ₖ Matrix.single st.1 st.2 (1 : ℂ)))
      Finset.univ
      (fun st _ => P.recoveredJointStep_product_integrable_of_alice n h hh
        (Matrix.of (fun i j => X (i,st.1) (j,st.2))) (Matrix.single st.1 st.2 (1 : ℂ)))
  exact hsum.congr (ae_of_all _ (fun r =>
    (P.recoveredJointStep_eq_columnBlocks n h r X).symm))

theorem recoveredJointStep_product_physical_setIntegral_of_alice
    (n : ℕ) (h : History (FineRecord R) n) (hh : P.fineTurn n h = true)
    (s : Set R) (hs : MeasurableSet s) (X : InputMatrix a) (Y : InputMatrix b) :
    (∫ r in {r : FineRecord R | r.1 ∈ s}, P.recoveredJointStep n h r (X ⊗ₖ Y)
      ∂P.squareProcess.kernel n h) =
      (P.physicalAliceInstrument n).operation (coarseHistory n h) s
        (P.jointPendingOperation n h (X ⊗ₖ Y)) := by
  let L : Nuclear Workspace →L[ℂ] Nuclear JointWorkspace :=
    (workspaceTensor).flip
      ((P.layers n).bobRecovery h Y)
  let μ := (P.squareProcess.kernel n h).restrict {r : FineRecord R | r.1 ∈ s}
  let f : FineRecord R → Nuclear Workspace := fun r =>
    (P.layers (n+1)).aliceRecovery (appendHistory n (h,r))
      (P.squareProcess.aliceK n h r * X * star (P.squareProcess.aliceK n h r))
  have hi : Integrable f μ := (P.layers_alice_action_integrable n h hh X).restrict
  have ht : (P.physicalAliceInstrument n).operation (coarseHistory n h) s
      (P.jointPendingOperation n h (X ⊗ₖ Y)) =
      L ((P.alice n).operation (coarseHistory n h) s ((P.layers n).aliceRecovery h X)) :=
    (congrArg ((P.physicalAliceInstrument n).operation (coarseHistory n h) s)
      (P.jointPendingOperation_product n h X Y)).trans
        (P.physicalAliceInstrument_product n (coarseHistory n h) s hs
          ((P.layers n).aliceRecovery h X) ((P.layers n).bobRecovery h Y))
  calc
    (∫ r, P.recoveredJointStep n h r (X ⊗ₖ Y) ∂μ) = ∫ r, L (f r) ∂μ :=
      integral_congr_ae (ae_of_all _ (fun r =>
        P.recoveredJointStep_product_of_alice n h hh r X Y))
    _ = L (∫ r, f r ∂μ) := L.integral_comp_comm hi
    _ = L ((P.alice n).operation (coarseHistory n h) s ((P.layers n).aliceRecovery h X)) :=
      congrArg L (P.layers_alice_physical_setIntegral n h hh s hs X)
    _ = _ := ht.symm

theorem recoveredJointStep_physical_setIntegral_of_alice
    (n : ℕ) (h : History (FineRecord R) n) (hh : P.fineTurn n h = true)
    (s : Set R) (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    (∫ r in {r : FineRecord R | r.1 ∈ s}, P.recoveredJointStep n h r X
      ∂P.squareProcess.kernel n h) =
      (P.physicalAliceInstrument n).operation (coarseHistory n h) s
        (P.jointPendingOperation n h X) := by
  let μ := (P.squareProcess.kernel n h).restrict {r : FineRecord R | r.1 ∈ s}
  let block : Fin b × Fin b → InputMatrix a :=
    fun st => Matrix.of (fun i j => X (i,st.1) (j,st.2))
  let unit : Fin b × Fin b → InputMatrix b := fun st => Matrix.single st.1 st.2 (1 : ℂ)
  let Op := (P.physicalAliceInstrument n).operation (coarseHistory n h) s
  have hi (st : Fin b × Fin b) :
      Integrable (fun r => P.recoveredJointStep n h r (block st ⊗ₖ unit st)) μ :=
    (P.recoveredJointStep_product_integrable_of_alice n h hh (block st) (unit st)).restrict
  calc
    (∫ r, P.recoveredJointStep n h r X ∂μ) =
        ∫ r, ∑ st : Fin b × Fin b, P.recoveredJointStep n h r (block st ⊗ₖ unit st) ∂μ :=
      integral_congr_ae (ae_of_all _ (fun r => P.recoveredJointStep_eq_columnBlocks n h r X))
    _ = ∑ st : Fin b × Fin b, ∫ r, P.recoveredJointStep n h r (block st ⊗ₖ unit st) ∂μ :=
      integral_finsetSum Finset.univ (fun st _ => hi st)
    _ = ∑ st : Fin b × Fin b, Op (P.jointPendingOperation n h (block st ⊗ₖ unit st)) :=
      Finset.sum_congr rfl (fun st _ =>
        P.recoveredJointStep_product_physical_setIntegral_of_alice n h hh s hs (block st) (unit st))
    _ = Op (P.jointPendingOperation n h X) :=
      (map_sum Op (fun st => P.jointPendingOperation n h (block st ⊗ₖ unit st)) Finset.univ).symm.trans
        (congrArg Op (P.jointPendingOperation_eq_columnBlocks n h X).symm)

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set Function InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator Kronecker

theorem jointInputMatrix_eq_rowBlocks {a b : ℕ} (X : JointInputMatrix a b) :
    X = ∑ st : Fin a × Fin a,
      Matrix.single st.1 st.2 (1 : ℂ) ⊗ₖ Matrix.of (fun i j => X (st.1,i) (st.2,j)) := by
  classical
  ext i j
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Matrix.single,
    Fintype.sum_prod_type, ite_mul, ite_and]

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

def physicalBobInstrument (n : ℕ) :
    QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument JointWorkspace JointWorkspace (History R n) R :=
  QuantumProver.MatrixNormalRightTensor.rightTensorInstrument (G := Workspace) (P.bob n)

theorem physicalBobInstrument_product (n : ℕ) (h : History R n)
    (s : Set R) (hs : MeasurableSet s) (T U : Nuclear Workspace) :
    (P.physicalBobInstrument n).operation h s (workspaceTensor T U) =
      workspaceTensor T ((P.bob n).operation h s U) :=
  QuantumProver.MatrixNormalRightTensor.rightTensorInstrument_product_action (P.bob n) h s hs T U

theorem recoveredJointStep_eq_rowBlocks (n : ℕ) (h : History (FineRecord R) n)
    (r : FineRecord R) (X : JointInputMatrix a b) :
    P.recoveredJointStep n h r X = ∑ st : Fin a × Fin a,
      P.recoveredJointStep n h r
        (Matrix.single st.1 st.2 (1 : ℂ) ⊗ₖ Matrix.of (fun i j => X (st.1,i) (st.2,j))) := by
  calc
    _ = P.recoveredJointStep n h r (∑ st : Fin a × Fin a,
        Matrix.single st.1 st.2 (1 : ℂ) ⊗ₖ Matrix.of (fun i j => X (st.1,i) (st.2,j))) :=
      congrArg (P.recoveredJointStep n h r) (jointInputMatrix_eq_rowBlocks X)
    _ = _ := by
      simp only [recoveredJointStep, Matrix.mul_sum, Matrix.sum_mul, map_sum]

theorem jointPendingOperation_eq_rowBlocks (n : ℕ) (h : History (FineRecord R) n)
    (X : JointInputMatrix a b) :
    P.jointPendingOperation n h X = ∑ st : Fin a × Fin a,
      P.jointPendingOperation n h
        (Matrix.single st.1 st.2 (1 : ℂ) ⊗ₖ Matrix.of (fun i j => X (st.1,i) (st.2,j))) := by
  calc
    _ = P.jointPendingOperation n h (∑ st : Fin a × Fin a,
        Matrix.single st.1 st.2 (1 : ℂ) ⊗ₖ Matrix.of (fun i j => X (st.1,i) (st.2,j))) :=
      congrArg (P.jointPendingOperation n h) (jointInputMatrix_eq_rowBlocks X)
    _ = _ := map_sum _ _ _

theorem recoveredJointStep_product_of_bob (n : ℕ) (h : History (FineRecord R) n)
    (hh : P.fineTurn n h ≠ true) (r : FineRecord R) (X : InputMatrix a) (Y : InputMatrix b) :
    P.recoveredJointStep n h r (X ⊗ₖ Y) =
      workspaceTensor ((P.layers n).aliceRecovery h X)
        ((P.layers (n+1)).bobRecovery (appendHistory n (h,r))
          (P.squareProcess.bobK n h r * Y * star (P.squareProcess.bobK n h r))) := by
  have hl : P.squareProcess.localOp n h r =
      (1 : InputMatrix a) ⊗ₖ P.squareProcess.bobK n h r := by
    change (if P.fineTurn n h = true then _ else _) = _
    exact if_neg hh
  unfold recoveredJointStep
  rw [hl]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have ha : (P.layers (n+1)).aliceRecovery (appendHistory n (h,r)) X =
      (P.layers n).aliceRecovery h X :=
    congrArg (fun C : InputChannel a => C X) (P.layers_alice_succ_of_bob n h r hh)
  exact (P.jointPendingOperation_product (n+1) (appendHistory n (h,r)) X
    (P.squareProcess.bobK n h r * Y * star (P.squareProcess.bobK n h r))).trans
      (congrArg (fun T : Nuclear Workspace => workspaceTensor T
        ((P.layers (n+1)).bobRecovery (appendHistory n (h,r))
          (P.squareProcess.bobK n h r * Y * star (P.squareProcess.bobK n h r)))) ha)

theorem recoveredJointStep_product_integrable_of_bob
    (n : ℕ) (h : History (FineRecord R) n) (hh : P.fineTurn n h ≠ true)
    (X : InputMatrix a) (Y : InputMatrix b) :
    Integrable (fun r => P.recoveredJointStep n h r (X ⊗ₖ Y)) (P.squareProcess.kernel n h) := by
  let L : Nuclear Workspace →L[ℂ] Nuclear JointWorkspace :=
    workspaceTensor ((P.layers n).aliceRecovery h X)
  have hi := L.integrable_comp (P.layers_bob_action_integrable n h hh Y)
  exact hi.congr (ae_of_all _ (fun r =>
    (P.recoveredJointStep_product_of_bob n h hh r X Y).symm))

theorem recoveredJointStep_integrable_of_bob
    (n : ℕ) (h : History (FineRecord R) n) (hh : P.fineTurn n h ≠ true)
    (X : JointInputMatrix a b) :
    Integrable (fun r => P.recoveredJointStep n h r X) (P.squareProcess.kernel n h) := by
  have hsum : Integrable (fun r => ∑ st : Fin a × Fin a,
      P.recoveredJointStep n h r
        (Matrix.single st.1 st.2 (1 : ℂ) ⊗ₖ Matrix.of (fun i j => X (st.1,i) (st.2,j))))
      (P.squareProcess.kernel n h) :=
    integrable_finsetSum (μ := P.squareProcess.kernel n h)
      (f := fun st : Fin a × Fin a => fun r : FineRecord R =>
        P.recoveredJointStep n h r
          (Matrix.single st.1 st.2 (1 : ℂ) ⊗ₖ Matrix.of (fun i j => X (st.1,i) (st.2,j))))
      Finset.univ
      (fun st _ => P.recoveredJointStep_product_integrable_of_bob n h hh
        (Matrix.single st.1 st.2 (1 : ℂ)) (Matrix.of (fun i j => X (st.1,i) (st.2,j))))
  exact hsum.congr (ae_of_all _ (fun r =>
    (P.recoveredJointStep_eq_rowBlocks n h r X).symm))

theorem recoveredJointStep_product_physical_setIntegral_of_bob
    (n : ℕ) (h : History (FineRecord R) n) (hh : P.fineTurn n h ≠ true)
    (s : Set R) (hs : MeasurableSet s) (X : InputMatrix a) (Y : InputMatrix b) :
    (∫ r in {r : FineRecord R | r.1 ∈ s}, P.recoveredJointStep n h r (X ⊗ₖ Y)
      ∂P.squareProcess.kernel n h) =
      (P.physicalBobInstrument n).operation (coarseHistory n h) s
        (P.jointPendingOperation n h (X ⊗ₖ Y)) := by
  let L : Nuclear Workspace →L[ℂ] Nuclear JointWorkspace :=
    workspaceTensor ((P.layers n).aliceRecovery h X)
  let μ := (P.squareProcess.kernel n h).restrict {r : FineRecord R | r.1 ∈ s}
  let f : FineRecord R → Nuclear Workspace := fun r =>
    (P.layers (n+1)).bobRecovery (appendHistory n (h,r))
      (P.squareProcess.bobK n h r * Y * star (P.squareProcess.bobK n h r))
  have hi : Integrable f μ := (P.layers_bob_action_integrable n h hh Y).restrict
  have ht : (P.physicalBobInstrument n).operation (coarseHistory n h) s
      (P.jointPendingOperation n h (X ⊗ₖ Y)) =
      L ((P.bob n).operation (coarseHistory n h) s ((P.layers n).bobRecovery h Y)) :=
    (congrArg ((P.physicalBobInstrument n).operation (coarseHistory n h) s)
      (P.jointPendingOperation_product n h X Y)).trans
        (P.physicalBobInstrument_product n (coarseHistory n h) s hs
          ((P.layers n).aliceRecovery h X) ((P.layers n).bobRecovery h Y))
  calc
    (∫ r, P.recoveredJointStep n h r (X ⊗ₖ Y) ∂μ) = ∫ r, L (f r) ∂μ :=
      integral_congr_ae (ae_of_all _ (fun r =>
        P.recoveredJointStep_product_of_bob n h hh r X Y))
    _ = L (∫ r, f r ∂μ) := L.integral_comp_comm hi
    _ = L ((P.bob n).operation (coarseHistory n h) s ((P.layers n).bobRecovery h Y)) :=
      congrArg L (P.layers_bob_physical_setIntegral n h hh s hs Y)
    _ = _ := ht.symm

theorem recoveredJointStep_physical_setIntegral_of_bob
    (n : ℕ) (h : History (FineRecord R) n) (hh : P.fineTurn n h ≠ true)
    (s : Set R) (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    (∫ r in {r : FineRecord R | r.1 ∈ s}, P.recoveredJointStep n h r X
      ∂P.squareProcess.kernel n h) =
      (P.physicalBobInstrument n).operation (coarseHistory n h) s
        (P.jointPendingOperation n h X) := by
  let μ := (P.squareProcess.kernel n h).restrict {r : FineRecord R | r.1 ∈ s}
  let block : Fin a × Fin a → InputMatrix b :=
    fun st => Matrix.of (fun i j => X (st.1,i) (st.2,j))
  let unit : Fin a × Fin a → InputMatrix a := fun st => Matrix.single st.1 st.2 (1 : ℂ)
  let Op := (P.physicalBobInstrument n).operation (coarseHistory n h) s
  have hi (st : Fin a × Fin a) :
      Integrable (fun r => P.recoveredJointStep n h r (unit st ⊗ₖ block st)) μ :=
    (P.recoveredJointStep_product_integrable_of_bob n h hh (unit st) (block st)).restrict
  calc
    (∫ r, P.recoveredJointStep n h r X ∂μ) =
        ∫ r, ∑ st : Fin a × Fin a, P.recoveredJointStep n h r (unit st ⊗ₖ block st) ∂μ :=
      integral_congr_ae (ae_of_all _ (fun r => P.recoveredJointStep_eq_rowBlocks n h r X))
    _ = ∑ st : Fin a × Fin a, ∫ r, P.recoveredJointStep n h r (unit st ⊗ₖ block st) ∂μ :=
      integral_finsetSum Finset.univ (fun st _ => hi st)
    _ = ∑ st : Fin a × Fin a, Op (P.jointPendingOperation n h (unit st ⊗ₖ block st)) :=
      Finset.sum_congr rfl (fun st _ =>
        P.recoveredJointStep_product_physical_setIntegral_of_bob n h hh s hs (unit st) (block st))
    _ = Op (P.jointPendingOperation n h X) :=
      (map_sum Op (fun st => P.jointPendingOperation n h (unit st ⊗ₖ block st)) Finset.univ).symm.trans
        (congrArg Op (P.jointPendingOperation_eq_rowBlocks n h X).symm)

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set Function InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator Kronecker

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

def represented_physicalStepInstrument (n : ℕ) :
    QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument JointWorkspace JointWorkspace (History R n) R where
  operation h s := if P.aliceTurn n h = true then
    (P.physicalAliceInstrument n).operation h s else (P.physicalBobInstrument n).operation h s
  empty h := by
    split
    · exact (P.physicalAliceInstrument n).empty h
    · exact (P.physicalBobInstrument n).empty h
  countable_additivity h s hs hd T := by
    by_cases hh : P.aliceTurn n h = true
    · simpa only [if_pos hh] using (P.physicalAliceInstrument n).countable_additivity h s hs hd T
    · simpa only [if_neg hh] using (P.physicalBobInstrument n).countable_additivity h s hs hd T
  completelyPositive h s hs := by
    split
    · exact (P.physicalAliceInstrument n).completelyPositive h s hs
    · exact (P.physicalBobInstrument n).completelyPositive h s hs
  measurable_coordinate s hs T x y := by
    classical
    have hcond := measurableSet_eq_fun (P.turn_measurable n) (measurable_const (a := true))
    have hm : Measurable (fun h : History R n => if P.aliceTurn n h = true then
        inner ℂ x (QuantumProver.NuclearOperator.toOperator
          ((P.physicalAliceInstrument n).operation h s T) y) else
        inner ℂ x (QuantumProver.NuclearOperator.toOperator
          ((P.physicalBobInstrument n).operation h s T) y)) := Measurable.ite hcond
      ((P.physicalAliceInstrument n).measurable_coordinate s hs T x y)
      ((P.physicalBobInstrument n).measurable_coordinate s hs T x y)
    convert hm using 1
    funext h
    by_cases hh : P.aliceTurn n h = true
    · simp only [if_pos hh]
    · simp only [if_neg hh]
  trace_preserving h T := by
    split
    · exact (P.physicalAliceInstrument n).trace_preserving h T
    · exact (P.physicalBobInstrument n).trace_preserving h T

theorem physicalStepInstrument_of_alice (n : ℕ) (h : History (FineRecord R) n)
    (hh : P.fineTurn n h = true) (s : Set R) :
    (P.represented_physicalStepInstrument n).operation (coarseHistory n h) s =
      (P.physicalAliceInstrument n).operation (coarseHistory n h) s := by
  change (if P.aliceTurn n (coarseHistory n h) = true then _ else _) = _
  exact if_pos hh

theorem physicalStepInstrument_of_bob (n : ℕ) (h : History (FineRecord R) n)
    (hh : P.fineTurn n h ≠ true) (s : Set R) :
    (P.represented_physicalStepInstrument n).operation (coarseHistory n h) s =
      (P.physicalBobInstrument n).operation (coarseHistory n h) s := by
  change (if P.aliceTurn n (coarseHistory n h) = true then _ else _) = _
  exact if_neg hh

theorem recoveredJointStep_integrable (n : ℕ) (h : History (FineRecord R) n)
    (X : JointInputMatrix a b) :
    Integrable (fun r => P.recoveredJointStep n h r X) (P.squareProcess.kernel n h) := by
  by_cases hh : P.fineTurn n h = true
  · exact P.recoveredJointStep_integrable_of_alice n h hh X
  · exact P.recoveredJointStep_integrable_of_bob n h hh X

theorem recoveredJointStep_physical_setIntegral (n : ℕ) (h : History (FineRecord R) n)
    (s : Set R) (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    (∫ r in {r : FineRecord R | r.1 ∈ s}, P.recoveredJointStep n h r X
      ∂P.squareProcess.kernel n h) =
      (P.represented_physicalStepInstrument n).operation (coarseHistory n h) s
        (P.jointPendingOperation n h X) := by
  by_cases hh : P.fineTurn n h = true
  · exact (P.recoveredJointStep_physical_setIntegral_of_alice n h hh s hs X).trans
      (congrArg (fun Op => Op (P.jointPendingOperation n h X))
        (P.physicalStepInstrument_of_alice n h hh s).symm)
  · exact (P.recoveredJointStep_physical_setIntegral_of_bob n h hh s hs X).trans
      (congrArg (fun Op => Op (P.jointPendingOperation n h X))
        (P.physicalStepInstrument_of_bob n h hh s).symm)

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set Function InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalFiniteTerminal
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator Kronecker

structure NormalTerminal (R : Type*) [MeasurableSpace R] (N c d : ℕ) where
  alice : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument
    Workspace (EuclideanSpace ℂ (Fin c)) (History R N) PUnit
  bob : QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption.Instrument
    Workspace (EuclideanSpace ℂ (Fin d)) (History R N) PUnit

local instance terminalMapMeasurable (a c : ℕ) :
    MeasurableSpace (InputMatrix a →L[ℂ] InputMatrix c) := borel _
local instance terminalMapBorel (a c : ℕ) :
    BorelSpace (InputMatrix a →L[ℂ] InputMatrix c) := ⟨rfl⟩

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)
variable {N c d : ℕ} (Q : NormalTerminal R N c d)

def finiteTerminalAlice (h : History (FineRecord R) N) : InputMatrix a →L[ℂ] InputMatrix c :=
  finiteTerminalMap ((P.layers N).aliceRecovery h)
    (Q.alice.operation (coarseHistory N h) univ)

def finiteTerminalBob (h : History (FineRecord R) N) : InputMatrix b →L[ℂ] InputMatrix d :=
  finiteTerminalMap ((P.layers N).bobRecovery h)
    (Q.bob.operation (coarseHistory N h) univ)

theorem finiteTerminalAlice_nuclear_action (h : History (FineRecord R) N) (X : InputMatrix a) :
    QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix (P.finiteTerminalAlice Q h X) =
      Q.alice.operation (coarseHistory N h) univ ((P.layers N).aliceRecovery h X) :=
  nuclearMatrix_finiteTerminalMap_apply _ _ X

theorem finiteTerminalBob_nuclear_action (h : History (FineRecord R) N) (X : InputMatrix b) :
    QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix (P.finiteTerminalBob Q h X) =
      Q.bob.operation (coarseHistory N h) univ ((P.layers N).bobRecovery h X) :=
  nuclearMatrix_finiteTerminalMap_apply _ _ X

theorem finiteTerminalAlice_completelyPositive (h : History (FineRecord R) N) :
    QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive
      (P.finiteTerminalAlice Q h).toLinearMap :=
  completelyPositive_finiteTerminalMap _ _ ((P.layers N).alice_cp h)
    (Q.alice.completelyPositive (coarseHistory N h) univ MeasurableSet.univ)

theorem finiteTerminalBob_completelyPositive (h : History (FineRecord R) N) :
    QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive
      (P.finiteTerminalBob Q h).toLinearMap :=
  completelyPositive_finiteTerminalMap _ _ ((P.layers N).bob_cp h)
    (Q.bob.completelyPositive (coarseHistory N h) univ MeasurableSet.univ)

theorem finiteTerminalAlice_tracePreserving (h : History (FineRecord R) N) :
    QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving
      (P.finiteTerminalAlice Q h).toLinearMap :=
  tracePreserving_finiteTerminalMap _ _ ((P.layers N).alice_trace h)
    (Q.alice.trace_preserving (coarseHistory N h))

theorem finiteTerminalBob_tracePreserving (h : History (FineRecord R) N) :
    QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving
      (P.finiteTerminalBob Q h).toLinearMap :=
  tracePreserving_finiteTerminalMap _ _ ((P.layers N).bob_trace h)
    (Q.bob.trace_preserving (coarseHistory N h))

theorem measurable_finiteTerminalAlice : Measurable (P.finiteTerminalAlice Q) := by
  exact measurable_finiteTerminalMap_of_coordinate_fields
    ((P.layers N).aliceRecovery)
    (fun h => Q.alice.operation (coarseHistory N h) univ)
    (QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization.stronglyMeasurable_finite_evaluation _
      ((P.layers N).alice_measurable))
    (fun T x y => (Q.alice.measurable_coordinate univ MeasurableSet.univ T x y).comp
      (measurable_coarseHistory N))

theorem measurable_finiteTerminalBob : Measurable (P.finiteTerminalBob Q) := by
  exact measurable_finiteTerminalMap_of_coordinate_fields
    ((P.layers N).bobRecovery)
    (fun h => Q.bob.operation (coarseHistory N h) univ)
    (QuantumProver.ElegantJointMeasurement.NormalInstrumentRealization.stronglyMeasurable_finite_evaluation _
      ((P.layers N).bob_measurable))
    (fun T x y => (Q.bob.measurable_coordinate univ MeasurableSet.univ T x y).comp
      (measurable_coarseHistory N))

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory Set
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess
open scoped Topology Matrix.Norms.L2Operator

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)
variable {N c d : ℕ} (Q : NormalTerminal R N c d)

def compiledTerminal :
    QuantumProver.MatrixSquareQuantumTerminal.FinalTerminal a b c d (FineRecord R) N where
  alice := P.finiteTerminalAlice Q
  bob := P.finiteTerminalBob Q
  alice_measurable := P.measurable_finiteTerminalAlice Q
  bob_measurable := P.measurable_finiteTerminalBob Q
  alice_cp := P.finiteTerminalAlice_completelyPositive Q
  bob_cp := P.finiteTerminalBob_completelyPositive Q
  alice_tp := P.finiteTerminalAlice_tracePreserving Q
  bob_tp := P.finiteTerminalBob_tracePreserving Q

def compiledQuantumOutput (X : JointInputMatrix a b) : JointInputMatrix c d :=
  QuantumProver.MatrixSquareQuantumTerminal.finiteHorizonChannel P.squareProcess N
    (P.compiledTerminal Q) X

theorem compiledQuantumOutput_finite_approx (hc : 0 < c) (hd : 0 < d)
    (X : JointInputMatrix a b) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol c d a b,
      ‖U.apply X - P.compiledQuantumOutput Q X‖ < ε :=
  QuantumProver.MatrixSquareQuantumTerminal.exists_finiteProtocol_output_approx
    P.squareProcess N (P.compiledTerminal Q) hc hd X ε hε

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory Set InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
open QuantumProver.ElegantJointMeasurement.HilbertPendingTensor QuantumProver.ElegantJointMeasurement.HilbertFiniteKrausPredual
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator Kronecker

abbrev PhysicalChoiWorkspace (a b : ℕ) := BlockSpace (Fin a × Fin b) JointWorkspace

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

def initialJointMap : EuclideanSpace ℂ (Fin a × Fin b) →L[ℂ] JointWorkspace :=
  jointKraus (fun _ : Unit => P.initialAlice.toContinuousLinearMap)
    (fun _ : Unit => P.initialBob.toContinuousLinearMap) ((),())

theorem initialJointMap_adjoint_comp :
    P.initialJointMap.adjoint ∘L P.initialJointMap = 1 := by
  have hA : (∑ q : Unit, P.initialAlice.toContinuousLinearMap.adjoint ∘L
      P.initialAlice.toContinuousLinearMap) = 1 := by
    simpa only [Fintype.sum_unique] using P.initialAlice.adjoint_comp_self
  have hB : (∑ q : Unit, P.initialBob.toContinuousLinearMap.adjoint ∘L
      P.initialBob.toContinuousLinearMap) = 1 := by
    simpa only [Fintype.sum_unique] using P.initialBob.adjoint_comp_self
  simpa only [Fintype.sum_prod_type, Fintype.sum_unique, initialJointMap] using
    jointKraus_complete (fun _ : Unit => P.initialAlice.toContinuousLinearMap)
      (fun _ : Unit => P.initialBob.toContinuousLinearMap) hA hB

def initialJointEmbedding : EuclideanSpace ℂ (Fin a × Fin b) →ₗᵢ[ℂ] JointWorkspace where
  toLinearMap := P.initialJointMap.toLinearMap
  norm_map' := ((ContinuousLinearMap.isometry_iff_adjoint_comp_self _).mpr
    P.initialJointMap_adjoint_comp).norm_map_of_map_zero (map_zero P.initialJointMap)

def initialJointOperation : PhysicalOperation (Fin a × Fin b) JointWorkspace :=
  finiteKrausOperation (fun _ : Unit => P.initialJointMap)

theorem initialJointOperation_completelyPositive :
    CompletelyPositive (operationOperator P.initialJointOperation.toLinearMap) :=
  completelyPositive_finiteKrausOperation (fun _ : Unit => P.initialJointMap)

theorem initialJointOperation_trace (X : JointInputMatrix a b) :
    QuantumProver.HilbertNuclearTrace.trace (P.initialJointOperation X) = Matrix.trace X :=
  tracePreserving_finiteKrausOperation (fun _ : Unit => P.initialJointMap)
    (by simpa only [Fintype.sum_unique] using P.initialJointMap_adjoint_comp) X

theorem initialJointOperation_product (X : InputMatrix a) (Y : InputMatrix b) :
    P.initialJointOperation (X ⊗ₖ Y) = workspaceTensor
      (compose P.initialAlice.toContinuousLinearMap P.initialAlice.toContinuousLinearMap.adjoint
        (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix X))
      (compose P.initialBob.toContinuousLinearMap P.initialBob.toContinuousLinearMap.adjoint
        (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix Y)) := by
  simpa only [initialJointOperation, finiteKrausOperation, finiteKrausChannel,
    ContinuousLinearMap.comp_apply, sum_apply, Fintype.sum_unique,
    QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearSandwich, initialJointMap] using
    jointKraus_product_sandwich (fun _ : Unit => P.initialAlice.toContinuousLinearMap)
      (fun _ : Unit => P.initialBob.toContinuousLinearMap) ((),()) X Y

theorem jointPendingOperation_zero (X : JointInputMatrix a b) :
    P.jointPendingOperation 0 PUnit.unit X = P.initialJointOperation X := by
  have hp (A : InputMatrix a) (B : InputMatrix b) :
      P.jointPendingOperation 0 PUnit.unit (A ⊗ₖ B) =
        P.initialJointOperation (A ⊗ₖ B) := by
    have hA : (P.layers 0).aliceRecovery PUnit.unit A =
        compose P.initialAlice.toContinuousLinearMap P.initialAlice.toContinuousLinearMap.adjoint
          (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix A) := initialChannel_apply P.initialAlice A
    have hB : (P.layers 0).bobRecovery PUnit.unit B =
        compose P.initialBob.toContinuousLinearMap P.initialBob.toContinuousLinearMap.adjoint
          (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix B) := initialChannel_apply P.initialBob B
    exact (P.jointPendingOperation_product 0 PUnit.unit A B).trans
      ((congrArg₂ (fun T U : Nuclear Workspace => workspaceTensor T U) hA hB).trans
        (P.initialJointOperation_product A B).symm)
  calc
    _ = ∑ st : Fin b × Fin b, P.jointPendingOperation 0 PUnit.unit
        (Matrix.of (fun i j => X (i,st.1) (j,st.2)) ⊗ₖ Matrix.single st.1 st.2 (1 : ℂ)) :=
      P.jointPendingOperation_eq_columnBlocks 0 PUnit.unit X
    _ = ∑ st : Fin b × Fin b, P.initialJointOperation
        (Matrix.of (fun i j => X (i,st.1) (j,st.2)) ⊗ₖ Matrix.single st.1 st.2 (1 : ℂ)) :=
      Finset.sum_congr rfl (fun st _ => hp _ _)
    _ = P.initialJointOperation (∑ st : Fin b × Fin b,
        Matrix.of (fun i j => X (i,st.1) (j,st.2)) ⊗ₖ Matrix.single st.1 st.2 (1 : ℂ)) :=
      (map_sum P.initialJointOperation _ Finset.univ).symm
    _ = _ := congrArg P.initialJointOperation (jointInputMatrix_eq_columnBlocks X).symm

def initialChoiState : Nuclear (PhysicalChoiWorkspace a b) :=
  (((Fintype.card (Fin a × Fin b) : ℝ)⁻¹ : ℂ) • nuclearChoi P.initialJointOperation)

theorem initialChoiState_isPositive :
    (QuantumProver.NuclearOperator.toOperator P.initialChoiState).IsPositive := by
  rw [initialChoiState, map_smul]
  apply (nuclearChoi_isPositive _ P.initialJointOperation_completelyPositive).smul_of_nonneg
  exact_mod_cast (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Fin a × Fin b))) :
    0 ≤ (Fintype.card (Fin a × Fin b) : ℝ)⁻¹)

theorem initialChoiState_trace : QuantumProver.HilbertNuclearTrace.trace P.initialChoiState = 1 := by
  have hc : (Fintype.card (Fin a × Fin b) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Fin a × Fin b)
  rw [initialChoiState, map_smul, trace_nuclearChoi, P.initialJointOperation_trace]
  rw [Matrix.trace_one]
  simp only [smul_eq_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
  exact inv_mul_cancel₀ hc

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory Set InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

instance jointWorkspaceSeparable : TopologicalSpace.SeparableSpace JointWorkspace :=
  QuantumProver.ElegantJointMeasurement.NormalAncillaPreparation.separableSpace_joint

instance physicalChoiWorkspaceSeparable (a b : ℕ) :
    TopologicalSpace.SeparableSpace (PhysicalChoiWorkspace a b) := by
  change TopologicalSpace.SeparableSpace (PiLp 2 (fun _ : Fin a × Fin b => JointWorkspace))
  infer_instance

theorem normalAmplification_nuclearChoi {I : Type} [Fintype I] [DecidableEq I]
    (Φ : NormalOperation JointWorkspace JointWorkspace)
    (ρ : PhysicalOperation I JointWorkspace) :
    normalAmplification (R := I) Φ (nuclearChoi ρ) = nuclearChoi (Φ.comp ρ) := by
  have he : nuclearChoi ρ = nuclearAssembly (fun i j => ρ (matrixUnit i j)) := by
    simpa only [nuclearAssembly] using nuclearChoi_eq ρ
  rw [normalAmplification_apply, he]
  simp only [nuclearBlock_nuclearAssembly]
  rw [nuclearChoi_eq]
  rfl

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

def represented_physicalReferenceInstrument (n : ℕ) :
    Instrument (PhysicalChoiWorkspace a b) (PhysicalChoiWorkspace a b) (History R n) R :=
  QuantumProver.MatrixNormalAmplifiedInstrument.amplifiedInstrument (Fin a × Fin b)
    (P.represented_physicalStepInstrument n)

theorem physicalReferenceInstrument_Choi (n : ℕ) (h : History R n) (s : Set R)
    (ρ : PhysicalOperation (Fin a × Fin b) JointWorkspace) :
    (P.represented_physicalReferenceInstrument n).operation h s (nuclearChoi ρ) =
      nuclearChoi (((P.represented_physicalStepInstrument n).operation h s).comp ρ) :=
  normalAmplification_nuclearChoi _ ρ

theorem stronglyMeasurable_physicalReferenceInstrument (n : ℕ) (s : Set R)
    (hs : MeasurableSet s) (T : Nuclear (PhysicalChoiWorkspace a b)) :
    StronglyMeasurable (fun h => (P.represented_physicalReferenceInstrument n).operation h s T) :=
  QuantumProver.MatrixNormalAmplifiedInstrument.stronglyMeasurable_amplifiedInstrument_operation
    (P.represented_physicalStepInstrument n) s hs T

theorem stronglyMeasurable_physicalReferenceInstrument_variable (n : ℕ) (s : Set R)
    (hs : MeasurableSet s) (T : History R n → Nuclear (PhysicalChoiWorkspace a b))
    (hT : StronglyMeasurable T) :
    StronglyMeasurable (fun h => (P.represented_physicalReferenceInstrument n).operation h s (T h)) :=
  QuantumProver.MatrixNormalAmplifiedInstrument.stronglyMeasurable_amplifiedInstrument_operation_variable
    (P.represented_physicalStepInstrument n) s hs T hT

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixNormalStateKernel
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

local instance physicalStateNuclearMeasurable (a b : ℕ) :
    MeasurableSpace (Nuclear (PhysicalChoiWorkspace a b)) := borel _
local instance physicalStateNuclearBorel (a b : ℕ) :
    BorelSpace (Nuclear (PhysicalChoiWorkspace a b)) := ⟨rfl⟩

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

structure PhysicalStateLayer (n : ℕ) where
  state : History R n → Nuclear (PhysicalChoiWorkspace a b)
  stronglyMeasurable_state : StronglyMeasurable state
  positive : ∀ h, (QuantumProver.NuclearOperator.toOperator (state h)).IsPositive
  trace_one : ∀ h, QuantumProver.HilbertNuclearTrace.trace (state h) = 1

def initialPhysicalStateLayer : PhysicalStateLayer (a := a) (b := b) (R := R) 0 where
  state _ := P.initialChoiState
  stronglyMeasurable_state := stronglyMeasurable_const
  positive _ := P.initialChoiState_isPositive
  trace_one _ := P.initialChoiState_trace

namespace PhysicalStateLayer
variable {n : ℕ} (L : PhysicalStateLayer (a := a) (b := b) (R := R) n)

def kernel : Kernel (History R n) R :=
  bornKernel (P.represented_physicalReferenceInstrument n) L.state L.positive
    L.stronglyMeasurable_state L.trace_one

instance isMarkovKernel_kernel : IsMarkovKernel (L.kernel P) :=
  isMarkovKernel_bornKernel _ _ _ _ _

def nextState : History R n × R → Nuclear (PhysicalChoiWorkspace a b) :=
  posterior (P.represented_physicalReferenceInstrument n) L.state L.positive
    L.stronglyMeasurable_state L.trace_one

def successor : PhysicalStateLayer (a := a) (b := b) (R := R) (n + 1) where
  state h := L.nextState P ((appendHistory (R := R) n).symm h)
  stronglyMeasurable_state :=
    (stronglyMeasurable_posterior (P.represented_physicalReferenceInstrument n) L.state L.positive
      L.stronglyMeasurable_state L.trace_one).comp_measurable
        (appendHistory (R := R) n).symm.measurable
  positive h := posterior_isPositive (P.represented_physicalReferenceInstrument n) L.state L.positive
    L.stronglyMeasurable_state L.trace_one
      ((appendHistory (R := R) n).symm h).1 ((appendHistory (R := R) n).symm h).2
  trace_one h := posterior_trace (P.represented_physicalReferenceInstrument n) L.state L.positive
    L.stronglyMeasurable_state L.trace_one
      ((appendHistory (R := R) n).symm h).1 ((appendHistory (R := R) n).symm h).2

theorem successor_append (h : History R n) (r : R) :
    (L.successor P).state (appendHistory n (h,r)) = L.nextState P (h,r) := by
  change L.nextState P ((appendHistory (R := R) n).symm (appendHistory n (h,r))) = _
  rw [MeasurableEquiv.symm_apply_apply]

theorem nextState_integrable (h : History R n) :
    Integrable (fun r => L.nextState P (h,r)) (L.kernel P h) :=
  integrable_posterior (P.represented_physicalReferenceInstrument n) L.state L.positive
    L.stronglyMeasurable_state L.trace_one h

theorem nextState_setIntegral (h : History R n) (s : Set R) (hs : MeasurableSet s) :
    (∫ r in s, L.nextState P (h,r) ∂L.kernel P h) =
      (P.represented_physicalReferenceInstrument n).operation h s (L.state h) :=
  setIntegral_posterior (P.represented_physicalReferenceInstrument n) L.state L.positive
    L.stronglyMeasurable_state L.trace_one h s hs

end PhysicalStateLayer

def represented_physicalStateLayers (P : MatrixProcess a b R) :
    (n : ℕ) → PhysicalStateLayer (a := a) (b := b) (R := R) n
  | 0 => P.initialPhysicalStateLayer
  | n + 1 => (P.represented_physicalStateLayers n).successor P

def represented_physicalBornKernel (n : ℕ) : Kernel (History R n) R :=
  (P.represented_physicalStateLayers n).kernel P

instance represented_physicalBornKernel_markov (n : ℕ) : IsMarkovKernel (P.represented_physicalBornKernel n) :=
  PhysicalStateLayer.isMarkovKernel_kernel P _

def represented_physicalState (n : ℕ) : History R n → Nuclear (PhysicalChoiWorkspace a b) :=
  (P.represented_physicalStateLayers n).state

theorem stronglyMeasurable_physicalState (n : ℕ) : StronglyMeasurable (P.represented_physicalState n) :=
  (P.represented_physicalStateLayers n).stronglyMeasurable_state

theorem physicalState_isPositive (n : ℕ) (h : History R n) :
    (QuantumProver.NuclearOperator.toOperator (P.represented_physicalState n h)).IsPositive :=
  (P.represented_physicalStateLayers n).positive h

theorem physicalState_trace (n : ℕ) (h : History R n) :
    QuantumProver.HilbertNuclearTrace.trace (P.represented_physicalState n h) = 1 :=
  (P.represented_physicalStateLayers n).trace_one h

theorem physicalState_norm (n : ℕ) (h : History R n) : ‖P.represented_physicalState n h‖ = 1 := by
  obtain ⟨L, basis, _⟩ := exists_hilbertBasis ℂ (PhysicalChoiWorkspace a b)
  rw [norm_positive_nuclear_eq_re_trace basis _ (P.physicalState_isPositive n h),
    P.physicalState_trace]
  rfl

theorem physicalBornKernel_apply (n : ℕ) (h : History R n) (s : Set R)
    (hs : MeasurableSet s) :
    P.represented_physicalBornKernel n h s = ENNReal.ofReal
      (QuantumProver.HilbertNuclearTrace.trace
        ((P.represented_physicalReferenceInstrument n).operation h s (P.represented_physicalState n h))).re :=
  bornKernel_apply (P.represented_physicalReferenceInstrument n) (P.represented_physicalStateLayers n).state
    (P.represented_physicalStateLayers n).positive (P.represented_physicalStateLayers n).stronglyMeasurable_state
    (P.represented_physicalStateLayers n).trace_one h s hs

theorem physicalState_successor (n : ℕ) (h : History R n) (r : R) :
    P.represented_physicalState (n + 1) (appendHistory n (h,r)) =
      (P.represented_physicalStateLayers n).nextState P (h,r) :=
  PhysicalStateLayer.successor_append P (P.represented_physicalStateLayers n) h r

theorem physicalState_successor_integrable (n : ℕ) (h : History R n) :
    Integrable (fun r => P.represented_physicalState (n + 1) (appendHistory n (h,r)))
      (P.represented_physicalBornKernel n h) := by
  simp_rw [P.physicalState_successor]
  exact (P.represented_physicalStateLayers n).nextState_integrable P h

theorem represented_physicalState_successor_setIntegral (n : ℕ) (h : History R n)
    (s : Set R) (hs : MeasurableSet s) :
    (∫ r in s, P.represented_physicalState (n + 1) (appendHistory n (h,r))
      ∂P.represented_physicalBornKernel n h) =
      (P.represented_physicalReferenceInstrument n).operation h s (P.represented_physicalState n h) := by
  simp_rw [P.physicalState_successor]
  exact (P.represented_physicalStateLayers n).nextState_setIntegral P h s hs

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

local instance physicalPrefixNuclearMeasurable (a b : ℕ) :
    MeasurableSpace (Nuclear (PhysicalChoiWorkspace a b)) := borel _
local instance physicalPrefixNuclearBorel (a b : ℕ) :
    BorelSpace (Nuclear (PhysicalChoiWorkspace a b)) := ⟨rfl⟩

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

def represented_physicalPrefixMeasure (P : MatrixProcess a b R) : (n : ℕ) → Measure (History R n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => ((P.represented_physicalPrefixMeasure n) ⊗ₘ P.represented_physicalBornKernel n).map (appendHistory n)

instance represented_physicalPrefixMeasure_probability (n : ℕ) :
    IsProbabilityMeasure (P.represented_physicalPrefixMeasure n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ n ih =>
      letI : IsProbabilityMeasure (P.represented_physicalPrefixMeasure n) := ih
      change IsProbabilityMeasure
        (((P.represented_physicalPrefixMeasure n) ⊗ₘ P.represented_physicalBornKernel n).map (appendHistory n))
      infer_instance

theorem represented_physicalState_integrable (n : ℕ) :
    Integrable (P.represented_physicalState n) (P.represented_physicalPrefixMeasure n) := by
  refine (integrable_const (1 : ℝ)).mono'
    (P.stronglyMeasurable_physicalState n).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun h => (P.physicalState_norm n h).le)

theorem physicalState_append_integrable (n : ℕ) :
    Integrable (fun z : History R n × R => P.represented_physicalState (n + 1) (appendHistory n z))
      ((P.represented_physicalPrefixMeasure n) ⊗ₘ P.represented_physicalBornKernel n) := by
  refine (integrable_const (1 : ℝ)).mono'
    ((P.stronglyMeasurable_physicalState (n + 1)).comp_measurable
      (appendHistory (R := R) n).measurable).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall
    (fun z => (P.physicalState_norm (n + 1) (appendHistory n z)).le)

def represented_physicalPrefixVectorMeasure (n : ℕ) :
    VectorMeasure (History R n) (Nuclear (PhysicalChoiWorkspace a b)) :=
  (P.represented_physicalPrefixMeasure n).withDensityᵥ (P.represented_physicalState n)

theorem represented_physicalPrefixVectorMeasure_apply (n : ℕ) (s : Set (History R n))
    (hs : MeasurableSet s) :
    P.represented_physicalPrefixVectorMeasure n s = ∫ h in s, P.represented_physicalState n h
      ∂P.represented_physicalPrefixMeasure n :=
  MeasureTheory.withDensityᵥ_apply (P.represented_physicalState_integrable n) hs

def successorEvent (n : ℕ) (s : Set (History R n)) (t : Set R) :
    Set (History R (n + 1)) := (appendHistory (R := R) n).symm ⁻¹' (s ×ˢ t)

theorem measurableSet_successorEvent (n : ℕ) (s : Set (History R n)) (t : Set R)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (successorEvent n s t) :=
  (hs.prod ht).preimage (appendHistory (R := R) n).symm.measurable

theorem represented_physicalPrefixVectorMeasure_successorEvent (n : ℕ)
    (s : Set (History R n)) (t : Set R) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    P.represented_physicalPrefixVectorMeasure (n + 1) (successorEvent n s t) =
      ∫ h in s, (P.represented_physicalReferenceInstrument n).operation h t (P.represented_physicalState n h)
        ∂P.represented_physicalPrefixMeasure n := by
  rw [P.represented_physicalPrefixVectorMeasure_apply (n + 1) _
    (measurableSet_successorEvent n s t hs ht)]
  change (∫ h in successorEvent n s t, P.represented_physicalState (n + 1) h
    ∂(((P.represented_physicalPrefixMeasure n) ⊗ₘ P.represented_physicalBornKernel n).map (appendHistory n))) = _
  rw [setIntegral_map_equiv]
  have hp : (appendHistory (R := R) n) ⁻¹' successorEvent n s t = s ×ˢ t := by
    ext z
    simp only [successorEvent, Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
  rw [hp, Measure.setIntegral_compProd hs ht (P.physicalState_append_integrable n).integrableOn]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun h => P.represented_physicalState_successor_setIntegral n h t ht)

def represented_physicalPrefixAction (n : ℕ) (s : Set (History R n))
    (X : JointInputMatrix a b) : Nuclear JointWorkspace :=
  (Fintype.card (Fin a × Fin b) : ℂ) •
    nuclearDecode X (P.represented_physicalPrefixVectorMeasure n s)

theorem physicalPrefixAction_apply (n : ℕ) (s : Set (History R n))
    (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    P.represented_physicalPrefixAction n s X = (Fintype.card (Fin a × Fin b) : ℂ) •
      nuclearDecode X (∫ h in s, P.represented_physicalState n h ∂P.represented_physicalPrefixMeasure n) := by
  rw [represented_physicalPrefixAction, P.represented_physicalPrefixVectorMeasure_apply n s hs]

theorem physicalPrefixAction_zero_univ (X : JointInputMatrix a b) :
    P.represented_physicalPrefixAction 0 Set.univ X = P.initialJointOperation X := by
  have hc : (Fintype.card (Fin a × Fin b) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Fin a × Fin b)
  rw [P.physicalPrefixAction_apply 0 Set.univ MeasurableSet.univ X]
  change (Fintype.card (Fin a × Fin b) : ℂ) • nuclearDecode X
    (∫ _ : PUnit in Set.univ, P.initialChoiState ∂Measure.dirac PUnit.unit) = _
  rw [setIntegral_univ, integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul,
    initialChoiState, map_smul, nuclearDecode_nuclearChoi,
    Complex.ofReal_inv, Complex.ofReal_natCast, smul_smul, mul_inv_cancel₀ hc]

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus QuantumProver.ElegantJointMeasurement.HilbertFiniteKrausPredual
open QuantumProver.ElegantJointMeasurement.HilbertPendingTensor
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

local instance fineChoiNuclearMeasurable (a b : ℕ) :
    MeasurableSpace (Nuclear (PhysicalChoiWorkspace a b)) := borel _
local instance fineChoiNuclearBorel (a b : ℕ) :
    BorelSpace (Nuclear (PhysicalChoiWorkspace a b)) := ⟨rfl⟩

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

def finePrefixMeasure (P : MatrixProcess a b R) : (n : ℕ) → Measure (History (FineRecord R) n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => P.squareProcess.prefixMeasure n

instance finePrefixMeasure_probability (n : ℕ) : IsProbabilityMeasure (P.finePrefixMeasure n) := by
  cases n with
  | zero => change IsProbabilityMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ n => change IsProbabilityMeasure (P.squareProcess.prefixMeasure n); infer_instance

def cumulativeSquare (P : MatrixProcess a b R) :
    (n : ℕ) → History (FineRecord R) n → JointInputMatrix a b
  | 0, _ => 1
  | n + 1, h => P.squareProcess.pathOp n h

theorem measurable_cumulativeSquare (n : ℕ) : Measurable (P.cumulativeSquare n) := by
  cases n with
  | zero => exact measurable_const
  | succ n => exact P.squareProcess.measurable_pathOp n

theorem cumulativeSquare_append (n : ℕ) (h : History (FineRecord R) n) (r : FineRecord R) :
    P.cumulativeSquare (n + 1) (appendHistory n (h,r)) =
      P.squareProcess.localOp n h r * P.cumulativeSquare n h := by
  cases n with
  | zero =>
      cases h
      change P.squareProcess.localOp 0 PUnit.unit (firstRecordEquiv.symm (firstRecordEquiv r)) =
        P.squareProcess.localOp 0 PUnit.unit r * 1
      rw [MeasurableEquiv.symm_apply_apply, Matrix.mul_one]
  | succ n =>
      change P.squareProcess.localOp (n + 1)
          ((prefixStepEquiv n).symm (prefixStepEquiv n (h,r))).1
          ((prefixStepEquiv n).symm (prefixStepEquiv n (h,r))).2 *
          P.squareProcess.pathOp n ((prefixStepEquiv n).symm (prefixStepEquiv n (h,r))).1 = _
      simp only [MeasurableEquiv.symm_apply_apply]
      rfl

def fineCumulativeChannel (n : ℕ) (h : History (FineRecord R) n) :
    PhysicalOperation (Fin a × Fin b) JointWorkspace :=
  finiteKrausOperation (fun q : (Unit ⊕ Fin a) × (Unit ⊕ Fin b) =>
    jointKraus (P.layersAliceKraus n h) (P.layersBobKraus n h) q ∘L
      QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator (P.cumulativeSquare n h))

theorem fineCumulativeChannel_apply (n : ℕ) (h : History (FineRecord R) n)
    (X : JointInputMatrix a b) :
    P.fineCumulativeChannel n h X = P.jointPendingOperation n h
      (P.cumulativeSquare n h * X * star (P.cumulativeSquare n h)) := by
  let K := jointKraus (P.layersAliceKraus n h) (P.layersBobKraus n h)
  let V := P.cumulativeSquare n h
  apply QuantumProver.NuclearOperator.toOperator_injective
  change QuantumProver.NuclearOperator.toOperator
      (finiteKrausOperation (fun q => K q ∘L QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator V) X) =
    QuantumProver.NuclearOperator.toOperator (finiteKrausOperation K (V * X * star V))
  rw [toOperator_finiteKrausOperation, toOperator_finiteKrausOperation]
  apply Finset.sum_congr rfl
  intro q _
  simp only [map_mul, map_star, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.comp_assoc]

theorem fineCumulativeChannel_completelyPositive (n : ℕ) (h : History (FineRecord R) n) :
    CompletelyPositive (operationOperator (P.fineCumulativeChannel n h).toLinearMap) :=
  completelyPositive_finiteKrausOperation _

theorem fineCumulativeChannel_trace (n : ℕ) (h : History (FineRecord R) n)
    (X : JointInputMatrix a b) :
    QuantumProver.HilbertNuclearTrace.trace (P.fineCumulativeChannel n h X) =
      Matrix.trace (star (P.cumulativeSquare n h) * P.cumulativeSquare n h * X) := by
  rw [P.fineCumulativeChannel_apply, P.jointPendingOperation_trace]
  rw [Matrix.trace_mul_cycle]

theorem stronglyMeasurable_fineCumulativeChannel_apply (n : ℕ) (X : JointInputMatrix a b) :
    StronglyMeasurable (fun h => P.fineCumulativeChannel n h X) := by
  simp_rw [P.fineCumulativeChannel_apply]
  apply P.stronglyMeasurable_jointPendingOperation_apply
  have hV := (P.measurable_cumulativeSquare n).stronglyMeasurable
  exact (hV.mul stronglyMeasurable_const).mul hV.star

attribute [local irreducible] fineCumulativeChannel

theorem stronglyMeasurable_fineCumulativeChannel (n : ℕ) :
    StronglyMeasurable (P.fineCumulativeChannel n) :=
  stronglyMeasurable_operation_of_units (P.fineCumulativeChannel n)
    (fun i j => P.stronglyMeasurable_fineCumulativeChannel_apply n (matrixUnit i j))

def fineChoiDensity (n : ℕ) (h : History (FineRecord R) n) :
    Nuclear (PhysicalChoiWorkspace a b) :=
  (((Fintype.card (Fin a × Fin b) : ℝ)⁻¹ : ℂ) • nuclearChoi (P.fineCumulativeChannel n h))

theorem stronglyMeasurable_fineChoiDensity (n : ℕ) : StronglyMeasurable (P.fineChoiDensity n) := by
  change StronglyMeasurable (fun h =>
    (((Fintype.card (Fin a × Fin b) : ℝ)⁻¹ : ℂ) •
      choiMap (P.fineCumulativeChannel n h)))
  exact (choiMap.continuous.comp_stronglyMeasurable
    (P.stronglyMeasurable_fineCumulativeChannel n)).fun_const_smul _

theorem fineChoiDensity_isPositive (n : ℕ) (h : History (FineRecord R) n) :
    (QuantumProver.NuclearOperator.toOperator (P.fineChoiDensity n h)).IsPositive := by
  rw [fineChoiDensity, map_smul]
  apply (nuclearChoi_isPositive _ (P.fineCumulativeChannel_completelyPositive n h)).smul_of_nonneg
  exact_mod_cast (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Fin a × Fin b))) :
    0 ≤ (Fintype.card (Fin a × Fin b) : ℝ)⁻¹)

theorem fineChoiDensity_trace (n : ℕ) (h : History (FineRecord R) n) :
    QuantumProver.HilbertNuclearTrace.trace (P.fineChoiDensity n h) =
      (((Fintype.card (Fin a × Fin b) : ℝ)⁻¹ : ℂ) *
        Matrix.trace (star (P.cumulativeSquare n h) * P.cumulativeSquare n h)) := by
  rw [fineChoiDensity, map_smul, trace_nuclearChoi, P.fineCumulativeChannel_trace,
    Matrix.mul_one, smul_eq_mul]

theorem fineChoiDensity_norm (n : ℕ) (h : History (FineRecord R) n) :
    ‖P.fineChoiDensity n h‖ = (Fintype.card (Fin a × Fin b) : ℝ)⁻¹ *
      (Matrix.trace (star (P.cumulativeSquare n h) * P.cumulativeSquare n h)).re := by
  obtain ⟨L, basis, _⟩ := exists_hilbertBasis ℂ (PhysicalChoiWorkspace a b)
  rw [norm_positive_nuclear_eq_re_trace basis _ (P.fineChoiDensity_isPositive n h),
    P.fineChoiDensity_trace]
  simp only [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus QuantumProver.ElegantJointMeasurement.HilbertFiniteKrausPredual
open QuantumProver.ElegantJointMeasurement.HilbertPendingTensor
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

local instance fineIntegralNuclearMeasurable (a b : ℕ) :
    MeasurableSpace (Nuclear (PhysicalChoiWorkspace a b)) := borel _
local instance fineIntegralNuclearBorel (a b : ℕ) :
    BorelSpace (Nuclear (PhysicalChoiWorkspace a b)) := ⟨rfl⟩

section ChoiIntegration
variable {a b : ℕ} {H : Type*} [MeasurableSpace H]
variable (μ : Measure H) (Φ : H → PhysicalOperation (Fin a × Fin b) JointWorkspace)

theorem integrable_charged_nuclearChoi
    (hΦ : ∀ i j, Integrable (fun h => Φ h (matrixUnit i j)) μ) :
    Integrable (fun h => nuclearChoi (Φ h)) μ := by
  let C (i j : Fin a × Fin b) : Nuclear JointWorkspace →L[ℂ]
      Nuclear (PhysicalChoiWorkspace a b) :=
    compose (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i)
      (PiLp.proj 2 (fun _ : Fin a × Fin b => JointWorkspace) j)
  have hi (i j : Fin a × Fin b) :
      Integrable (fun h => C i j (Φ h (matrixUnit i j))) μ :=
    (C i j).integrable_comp (hΦ i j)
  have hsum : Integrable (fun h => ∑ i : Fin a × Fin b, ∑ j : Fin a × Fin b,
      C i j (Φ h (matrixUnit i j))) μ :=
    integrable_finsetSum (μ := μ)
      (f := fun i h => ∑ j : Fin a × Fin b, C i j (Φ h (matrixUnit i j))) Finset.univ
      (fun i _ => integrable_finsetSum (μ := μ)
        (f := fun j h => C i j (Φ h (matrixUnit i j))) Finset.univ (fun j _ => hi i j))
  have he : (fun h => nuclearChoi (Φ h)) =
      (fun h => ∑ i : Fin a × Fin b, ∑ j : Fin a × Fin b,
        C i j (Φ h (matrixUnit i j))) := by
    funext h
    exact nuclearChoi_eq (Φ h)
  rw [he]
  exact hsum

theorem integral_charged_nuclearChoi_eq
    (Ψ : PhysicalOperation (Fin a × Fin b) JointWorkspace)
    (hΦ : ∀ i j, Integrable (fun h => Φ h (matrixUnit i j)) μ)
    (hEq : ∀ i j, (∫ h, Φ h (matrixUnit i j) ∂μ) = Ψ (matrixUnit i j)) :
    (∫ h, nuclearChoi (Φ h) ∂μ) = nuclearChoi Ψ := by
  let C (i j : Fin a × Fin b) : Nuclear JointWorkspace →L[ℂ]
      Nuclear (PhysicalChoiWorkspace a b) :=
    compose (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert i)
      (PiLp.proj 2 (fun _ : Fin a × Fin b => JointWorkspace) j)
  have hi (i j : Fin a × Fin b) :
      Integrable (fun h => C i j (Φ h (matrixUnit i j))) μ :=
    (C i j).integrable_comp (hΦ i j)
  have hci (i j : Fin a × Fin b) :
      (∫ h, C i j (Φ h (matrixUnit i j)) ∂μ) = C i j (Ψ (matrixUnit i j)) := by
    rw [(C i j).integral_comp_comm (hΦ i j), hEq i j]
  have hrow (i : Fin a × Fin b) :
      (∫ h, ∑ j, C i j (Φ h (matrixUnit i j)) ∂μ) =
        ∑ j, C i j (Ψ (matrixUnit i j)) := by
    rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
    simp_rw [hci]
  simp_rw [nuclearChoi_eq]
  change (∫ h, ∑ i, ∑ j, C i j (Φ h (matrixUnit i j)) ∂μ) =
    ∑ i, ∑ j, C i j (Ψ (matrixUnit i j))
  rw [integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  simp_rw [hrow]

end ChoiIntegration

def chargedTraceCLM (a b : ℕ) : JointInputMatrix a b →L[ℂ] ℂ :=
  ∑ i : Fin a × Fin b, matrixEntry i i

theorem chargedTraceCLM_apply (a b : ℕ) (X : JointInputMatrix a b) :
    chargedTraceCLM a b X = Matrix.trace X := by
  simp [chargedTraceCLM, matrixEntry, Matrix.trace, Matrix.diag]
  rfl

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

attribute [local irreducible] fineCumulativeChannel

theorem finePrefixMeasure_successor (n : ℕ) :
    P.finePrefixMeasure (n + 1) =
      ((P.finePrefixMeasure n) ⊗ₘ P.squareProcess.kernel n).map (appendHistory n) := by
  cases n with
  | zero =>
      letI := P.squareProcess.markov 0
      have he : Measure.dirac PUnit.unit ⊗ₘ P.squareProcess.kernel 0 =
          (P.squareProcess.kernel 0 PUnit.unit).map (fun r => (PUnit.unit,r)) := by
        ext s hs
        rw [Measure.dirac_compProd_apply hs, Measure.map_apply measurable_prodMk_left hs]
      rw [finePrefixMeasure, finePrefixMeasure, he,
        Measure.map_map (appendHistory (R := FineRecord R) 0).measurable measurable_prodMk_left]
      rfl
  | succ n => rfl

theorem cumulativeGram_integrable (n : ℕ) :
    Integrable (fun h => star (P.cumulativeSquare n h) * P.cumulativeSquare n h)
      (P.finePrefixMeasure n) := by
  cases n with
  | zero =>
      letI : IsProbabilityMeasure (P.finePrefixMeasure 0) := P.finePrefixMeasure_probability 0
      simpa only [cumulativeSquare, star_one, Matrix.one_mul] using
        (integrable_const (1 : JointInputMatrix a b) :
          Integrable (fun _ : History (FineRecord R) 0 => (1 : JointInputMatrix a b))
            (P.finePrefixMeasure 0))
  | succ n => exact P.squareProcess.pathGram_integrable n

theorem fineChoiDensity_integrable (n : ℕ) :
    Integrable (P.fineChoiDensity n) (P.finePrefixMeasure n) := by
  have hi : Integrable
      (fun h => (Matrix.trace (star (P.cumulativeSquare n h) * P.cumulativeSquare n h)).re)
      (P.finePrefixMeasure n) := by
    simpa only [chargedTraceCLM_apply, ContinuousLinearMap.comp_apply, Complex.reCLM_apply] using
      Complex.reCLM.integrable_comp
        ((chargedTraceCLM a b).integrable_comp (P.cumulativeGram_integrable n))
  apply (integrable_norm_iff (P.stronglyMeasurable_fineChoiDensity n).aestronglyMeasurable).mp
  convert hi.const_mul (Fintype.card (Fin a × Fin b) : ℝ)⁻¹ using 1
  funext h
  exact P.fineChoiDensity_norm n h

def finePrefixVectorMeasure (n : ℕ) :
    VectorMeasure (History (FineRecord R) n) (Nuclear (PhysicalChoiWorkspace a b)) :=
  (P.finePrefixMeasure n).withDensityᵥ (P.fineChoiDensity n)

theorem finePrefixVectorMeasure_apply (n : ℕ) (s : Set (History (FineRecord R) n))
    (hs : MeasurableSet s) :
    P.finePrefixVectorMeasure n s =
      ∫ h in s, P.fineChoiDensity n h ∂P.finePrefixMeasure n :=
  MeasureTheory.withDensityᵥ_apply (P.fineChoiDensity_integrable n) hs

theorem fineChoiDensity_append_integrable (n : ℕ) :
    Integrable (fun z : History (FineRecord R) n × FineRecord R =>
        P.fineChoiDensity (n + 1) (appendHistory n z))
      ((P.finePrefixMeasure n) ⊗ₘ P.squareProcess.kernel n) := by
  have hi : Integrable (P.fineChoiDensity (n + 1))
      (((P.finePrefixMeasure n) ⊗ₘ P.squareProcess.kernel n).map (appendHistory n)) := by
    rw [← P.finePrefixMeasure_successor]
    exact P.fineChoiDensity_integrable (n + 1)
  exact (integrable_map_equiv (appendHistory (R := FineRecord R) n)
    (P.fineChoiDensity (n + 1))).mp hi

theorem fineCumulativeChannel_append_apply (n : ℕ) (h : History (FineRecord R) n)
    (r : FineRecord R) (X : JointInputMatrix a b) :
    P.fineCumulativeChannel (n + 1) (appendHistory n (h,r)) X =
      P.recoveredJointStep n h r (P.cumulativeSquare n h * X * star (P.cumulativeSquare n h)) := by
  rw [P.fineCumulativeChannel_apply, P.cumulativeSquare_append]
  unfold recoveredJointStep
  simp only [star_mul, Matrix.mul_assoc]

theorem fineCumulativeChannel_append_integrable (n : ℕ) (h : History (FineRecord R) n)
    (X : JointInputMatrix a b) :
    Integrable (fun r => P.fineCumulativeChannel (n + 1) (appendHistory n (h,r)) X)
      (P.squareProcess.kernel n h) := by
  simp_rw [P.fineCumulativeChannel_append_apply]
  exact P.recoveredJointStep_integrable n h _

theorem fineChoiDensity_fibre_integrable (n : ℕ) (h : History (FineRecord R) n) :
    Integrable (fun r => P.fineChoiDensity (n + 1) (appendHistory n (h,r)))
      (P.squareProcess.kernel n h) := by
  have hi := integrable_charged_nuclearChoi (P.squareProcess.kernel n h)
    (fun r => P.fineCumulativeChannel (n + 1) (appendHistory n (h,r)))
    (fun i j => P.fineCumulativeChannel_append_integrable n h (matrixUnit i j))
  exact hi.fun_smul (((Fintype.card (Fin a × Fin b) : ℝ)⁻¹ : ℂ))

theorem fineChoiDensity_physical_setIntegral (n : ℕ) (h : History (FineRecord R) n)
    (s : Set R) (hs : MeasurableSet s) :
    (∫ r in {r : FineRecord R | r.1 ∈ s},
      P.fineChoiDensity (n + 1) (appendHistory n (h,r)) ∂P.squareProcess.kernel n h) =
      (P.represented_physicalReferenceInstrument n).operation (coarseHistory n h) s (P.fineChoiDensity n h) := by
  let μ := (P.squareProcess.kernel n h).restrict {r : FineRecord R | r.1 ∈ s}
  let c : ℂ := ((Fintype.card (Fin a × Fin b) : ℝ)⁻¹ : ℂ)
  let Φ : FineRecord R → PhysicalOperation (Fin a × Fin b) JointWorkspace :=
    fun r => P.fineCumulativeChannel (n + 1) (appendHistory n (h,r))
  let Ψ : PhysicalOperation (Fin a × Fin b) JointWorkspace :=
    ((P.represented_physicalStepInstrument n).operation (coarseHistory n h) s).comp
      (P.fineCumulativeChannel n h)
  have hi (i j : Fin a × Fin b) : Integrable (fun r => Φ r (matrixUnit i j)) μ :=
    (P.fineCumulativeChannel_append_integrable n h (matrixUnit i j)).restrict
  have he (i j : Fin a × Fin b) :
      (∫ r, Φ r (matrixUnit i j) ∂μ) = Ψ (matrixUnit i j) := by
    simp only [Φ, Ψ, ContinuousLinearMap.comp_apply, P.fineCumulativeChannel_append_apply]
    exact (P.recoveredJointStep_physical_setIntegral n h s hs _).trans
      (congrArg ((P.represented_physicalStepInstrument n).operation (coarseHistory n h) s)
        (P.fineCumulativeChannel_apply n h (matrixUnit i j)).symm)
  change (∫ r, c • nuclearChoi (Φ r) ∂μ) = _
  rw [integral_smul]
  rw [integral_charged_nuclearChoi_eq μ Φ Ψ hi he]
  rw [fineChoiDensity, map_smul, P.physicalReferenceInstrument_Choi]

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixNuclearKernelTransport
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

local instance globalPrefixNuclearMeasurable (a b : ℕ) :
    MeasurableSpace (Nuclear (PhysicalChoiWorkspace a b)) := borel _
local instance globalPrefixNuclearBorel (a b : ℕ) :
    BorelSpace (Nuclear (PhysicalChoiWorkspace a b)) := ⟨rfl⟩

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

theorem fineCumulativeChannel_zero : P.fineCumulativeChannel 0 PUnit.unit = P.initialJointOperation := by
  ext X
  rw [P.fineCumulativeChannel_apply]
  change P.jointPendingOperation 0 PUnit.unit (1 * X * star 1) = _
  rw [star_one, Matrix.one_mul, Matrix.mul_one, P.jointPendingOperation_zero]

theorem fineChoiDensity_zero : P.fineChoiDensity 0 PUnit.unit = P.initialChoiState := by
  rw [fineChoiDensity, P.fineCumulativeChannel_zero]
  rfl

theorem physical_fine_prefix_setIntegral (n : ℕ) (s : Set (History R n))
    (hs : MeasurableSet s) :
    (∫ h in coarseHistory n ⁻¹' s, P.fineChoiDensity n h ∂P.finePrefixMeasure n) =
      ∫ h in s, P.represented_physicalState n h ∂P.represented_physicalPrefixMeasure n := by
  induction n with
  | zero =>
      have hc : coarseHistory (R := R) 0 = id := by funext h; cases h; rfl
      have hd : P.fineChoiDensity 0 = fun _ : PUnit => P.initialChoiState := by
        funext h
        cases h
        exact P.fineChoiDensity_zero
      rw [hc, Set.preimage_id, hd]
      rfl
  | succ n ih =>
      letI : IsMarkovKernel (P.squareProcess.kernel n) := P.squareProcess.markov n
      have hset : ∀ t : Set (History R n), MeasurableSet t →
          (∫ h in coarseHistory n ⁻¹' t, P.fineChoiDensity n h ∂P.finePrefixMeasure n) =
            ∫ h in t, P.represented_physicalState n h ∂P.represented_physicalPrefixMeasure n := by
        intro t ht
        exact ih t ht
      have he := setIntegral_kernel_transport (P.represented_physicalReferenceInstrument n)
        (measurable_coarseHistory (R := R) n) (measurable_fst (α := R) (β := ℕ × ℕ))
        (P.fineChoiDensity_integrable n) (P.represented_physicalState_integrable n) hset
        (P.squareProcess.kernel n) (P.represented_physicalBornKernel n)
        (P.fineChoiDensity_append_integrable n) (P.physicalState_append_integrable n)
        (fun h t ht => P.fineChoiDensity_physical_setIntegral n h t ht)
        (fun h t ht => P.represented_physicalState_successor_setIntegral n h t ht)
        ((appendHistory (R := R) n) ⁻¹' s) (hs.preimage (appendHistory (R := R) n).measurable)
      rw [P.finePrefixMeasure_successor, represented_physicalPrefixMeasure,
        setIntegral_map_equiv, setIntegral_map_equiv]
      have hc : (appendHistory (R := FineRecord R) n) ⁻¹' (coarseHistory (n + 1) ⁻¹' s) =
          Prod.map (coarseHistory (R := R) n) (Prod.fst : FineRecord R → R) ⁻¹'
            ((appendHistory (R := R) n) ⁻¹' s) := by
        ext z
        rcases z with ⟨h,r⟩
        change coarseHistory (n + 1) (appendHistory n (h,r)) ∈ s ↔
          appendHistory n (coarseHistory n h,r.1) ∈ s
        rw [QuantumProver.ElegantJointMeasurement.NormalProcess.coarseHistory_append n h r]
      rw [hc]
      exact he

theorem physical_fine_prefixVectorMeasure (n : ℕ) :
    (P.finePrefixVectorMeasure n).map (coarseHistory n) = P.represented_physicalPrefixVectorMeasure n := by
  ext s hs
  rw [VectorMeasure.map_apply _ (measurable_coarseHistory n) hs,
    P.finePrefixVectorMeasure_apply n _ (hs.preimage (measurable_coarseHistory n)),
    P.represented_physicalPrefixVectorMeasure_apply n s hs]
  exact P.physical_fine_prefix_setIntegral n s hs

theorem fineChoiDensity_decode (n : ℕ) (h : History (FineRecord R) n)
    (X : JointInputMatrix a b) :
    (Fintype.card (Fin a × Fin b) : ℂ) • nuclearDecode X (P.fineChoiDensity n h) =
      P.fineCumulativeChannel n h X := by
  have hc : (Fintype.card (Fin a × Fin b) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Fin a × Fin b)
  rw [fineChoiDensity, map_smul, nuclearDecode_nuclearChoi, smul_smul]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast, mul_inv_cancel₀ hc, one_smul]

theorem physicalPrefixAction_eq_compiled (n : ℕ) (s : Set (History R n))
    (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    P.represented_physicalPrefixAction n s X = ∫ h in coarseHistory n ⁻¹' s,
      P.fineCumulativeChannel n h X ∂P.finePrefixMeasure n := by
  rw [P.physicalPrefixAction_apply n s hs X, ← P.physical_fine_prefix_setIntegral n s hs]
  have hi := (P.fineChoiDensity_integrable n).restrict
    (s := coarseHistory n ⁻¹' s)
  rw [← (nuclearDecode X).integral_comp_comm hi, ← integral_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun h => P.fineChoiDensity_decode n h X)

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi Preorder
open QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM (ConsistentCylinderPOVM)
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

attribute [local irreducible] fineCumulativeChannel

theorem fineCumulativeChannel_integrable (n : ℕ) (X : JointInputMatrix a b) :
    Integrable (fun h => P.fineCumulativeChannel n h X) (P.finePrefixMeasure n) := by
  have hi := ((nuclearDecode X).integrable_comp (P.fineChoiDensity_integrable n)).fun_smul
    (Fintype.card (Fin a × Fin b) : ℂ)
  simpa only [P.fineChoiDensity_decode n] using hi

def represented_physicalCylinderEffect (P : MatrixProcess a b R) (N : ℕ)
    (s : Set (Prefix R N)) : JointInputMatrix a b :=
  fun i j => QuantumProver.HilbertNuclearTrace.trace
    (P.represented_physicalPrefixAction (N + 1) s (Matrix.single j i (1 : ℂ)))

theorem physicalCylinderEffect_eq_compiled (N : ℕ) (s : Set (Prefix R N))
    (hs : MeasurableSet s) :
    P.represented_physicalCylinderEffect N s =
      P.squareProcess.cylinderEffect N (coarseHistory (N + 1) ⁻¹' s) := by
  let D : Set (Prefix (FineRecord R) N) := coarseHistory (N + 1) ⁻¹' s
  ext i j
  change QuantumProver.HilbertNuclearTrace.trace
    (P.represented_physicalPrefixAction (N + 1) s (Matrix.single j i (1 : ℂ))) = _
  rw [P.physicalPrefixAction_eq_compiled (N + 1) s hs]
  have hi := (P.fineCumulativeChannel_integrable (N + 1) (Matrix.single j i (1 : ℂ))).restrict
    (s := D)
  change QuantumProver.HilbertNuclearTrace.trace
    (∫ h in D, P.fineCumulativeChannel (N + 1) h (Matrix.single j i (1 : ℂ))
      ∂P.finePrefixMeasure (N + 1)) =
    SquareProcess.entryCLM i j (∫ h in D, P.squareProcess.pathGram N h
      ∂P.squareProcess.prefixMeasure N)
  rw [← QuantumProver.HilbertNuclearTrace.trace.integral_comp_comm hi]
  have hpoint (h : Prefix (FineRecord R) N) :
      QuantumProver.HilbertNuclearTrace.trace
        (P.fineCumulativeChannel (N + 1) h (Matrix.single j i (1 : ℂ))) =
          P.squareProcess.pathGram N h i j := by
    rw [P.fineCumulativeChannel_trace]
    change Matrix.trace (P.squareProcess.pathGram N h * Matrix.single j i (1 : ℂ)) = _
    rw [Matrix.trace_mul_single]
    simp
  simp_rw [hpoint]
  exact (SquareProcess.entryCLM i j).integral_comp_comm
    (P.squareProcess.pathGram_integrable N).restrict

theorem physicalPrefixAction_trace (N : ℕ) (s : Set (Prefix R N))
    (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    QuantumProver.HilbertNuclearTrace.trace (P.represented_physicalPrefixAction (N + 1) s X) =
      Matrix.trace (P.represented_physicalCylinderEffect N s * X) := by
  let D : Set (Prefix (FineRecord R) N) := coarseHistory (N + 1) ⁻¹' s
  let T : JointInputMatrix a b →L[ℂ] ℂ :=
    (QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.MatrixProbe.bornComplexLinear X).toContinuousLinearMap
  rw [P.physicalPrefixAction_eq_compiled (N + 1) s hs,
    P.physicalCylinderEffect_eq_compiled N s hs]
  have hi := (P.fineCumulativeChannel_integrable (N + 1) X).restrict (s := D)
  change QuantumProver.HilbertNuclearTrace.trace
    (∫ h in D, P.fineCumulativeChannel (N + 1) h X ∂P.finePrefixMeasure (N + 1)) =
      T (∫ h in D, P.squareProcess.pathGram N h ∂P.squareProcess.prefixMeasure N)
  rw [← QuantumProver.HilbertNuclearTrace.trace.integral_comp_comm hi]
  have hpoint (h : Prefix (FineRecord R) N) :
      QuantumProver.HilbertNuclearTrace.trace (P.fineCumulativeChannel (N + 1) h X) =
        T (P.squareProcess.pathGram N h) := by
    exact P.fineCumulativeChannel_trace (N + 1) h X
  simp_rw [hpoint]
  exact T.integral_comp_comm (P.squareProcess.pathGram_integrable N).restrict

def represented_physicalCylinderPOVM (P : MatrixProcess a b R) : ConsistentCylinderPOVM R (Fin a × Fin b) where
  effect := P.represented_physicalCylinderEffect
  empty := by
    intro N
    rw [P.physicalCylinderEffect_eq_compiled N ∅ MeasurableSet.empty, Set.preimage_empty,
      P.squareProcess.cylinderEffect_empty]
  positive := by
    intro N s hs
    rw [P.physicalCylinderEffect_eq_compiled N s hs]
    exact P.squareProcess.cylinderEffect_posSemidef N _
  total := by
    intro N
    rw [P.physicalCylinderEffect_eq_compiled N univ MeasurableSet.univ, Set.preimage_univ,
      P.squareProcess.cylinderEffect_univ]
  coordinate_additive := by
    intro N s hs hd i j
    simp_rw [P.physicalCylinderEffect_eq_compiled N _ (hs _)]
    rw [P.physicalCylinderEffect_eq_compiled N _ (MeasurableSet.iUnion hs), Set.preimage_iUnion]
    exact P.squareProcess.cylinderEffect_coordinate_additive N _
      (fun k => (hs k).preimage (measurable_coarseHistory (N + 1)))
      (hd.mono fun _ _ => Disjoint.preimage _) i j
  consistent := by
    intro n m hnm s hs
    have hpre : coarseHistory (m + 1) ⁻¹'
        ((frestrictLe₂ (π := fun _ => R) hnm) ⁻¹' s) =
      (frestrictLe₂ (π := fun _ => FineRecord R) hnm) ⁻¹'
        (coarseHistory (n + 1) ⁻¹' s) := rfl
    rw [P.physicalCylinderEffect_eq_compiled m _
      (hs.preimage (SquareProcess.measurable_prefixRestrict hnm)),
      P.physicalCylinderEffect_eq_compiled n s hs, hpre]
    exact P.squareProcess.cylinderEffect_consistent n m hnm _
      (hs.preimage (measurable_coarseHistory (n + 1)))

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory Set Function Filter Preorder QuantumProver.ElegantJointMeasurement.HilbertSquareProcess
open QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM (Transcript vectorMeasure_eq_of_prefix)
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

def coarseTranscript {R : Type*} [MeasurableSpace R]
    (ω : Transcript (FineRecord R)) : Transcript R := fun n => (ω n).1

theorem measurable_coarseTranscript {R : Type*} [MeasurableSpace R] :
    Measurable (coarseTranscript (R := R)) :=
  Measurable.of_eval fun n => (measurable_pi_apply n).fst

theorem coarseTranscript_prefix {R : Type*} [MeasurableSpace R]
    (ω : Transcript (FineRecord R)) (N : ℕ) :
    coarseHistory (N + 1) ((frestrictLe (π := fun _ => FineRecord R) N) ω) =
      (frestrictLe (π := fun _ => R) N) (coarseTranscript ω) := rfl

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

def represented_physicalTranscriptVectorMeasure (P : MatrixProcess a b R) :
    VectorMeasure (Transcript R) (JointInputMatrix a b) := by
  letI : Nonempty R := P.record_nonempty
  exact P.represented_physicalCylinderPOVM.fullVectorMeasure

theorem represented_physicalTranscriptVectorMeasure_prefix (N : ℕ) (s : Set (Prefix R N))
    (hs : MeasurableSet s) :
    P.represented_physicalTranscriptVectorMeasure ((frestrictLe (π := fun _ => R) N) ⁻¹' s) =
      P.represented_physicalCylinderEffect N s := by
  letI : Nonempty R := P.record_nonempty
  exact P.represented_physicalCylinderPOVM.fullVectorMeasure_prefix N s hs

theorem represented_physicalTranscriptVectorMeasure_unique
    (F : VectorMeasure (Transcript R) (JointInputMatrix a b))
    (hF : ∀ N (s : Set (Prefix R N)), MeasurableSet s →
      F ((frestrictLe (π := fun _ => R) N) ⁻¹' s) = P.represented_physicalCylinderEffect N s) :
    F = P.represented_physicalTranscriptVectorMeasure := by
  letI : Nonempty R := P.record_nonempty
  apply vectorMeasure_eq_of_prefix
  intro N s hs
  exact (hF N s hs).trans (P.represented_physicalTranscriptVectorMeasure_prefix N s hs).symm

theorem physicalTranscriptVectorMeasure_eq_compiled :
    P.represented_physicalTranscriptVectorMeasure =
      letI : Nonempty (FineRecord R) := P.fineRecord_nonempty
      P.squareProcess.cylinderPOVM.fullVectorMeasure.map coarseTranscript := by
  letI : Nonempty (FineRecord R) := P.fineRecord_nonempty
  letI : Nonempty R := P.record_nonempty
  apply vectorMeasure_eq_of_prefix
  intro N s hs
  rw [P.represented_physicalTranscriptVectorMeasure_prefix N s hs,
    VectorMeasure.map_apply _ measurable_coarseTranscript ((measurable_frestrictLe N) hs)]
  have he : coarseTranscript ⁻¹' ((frestrictLe (π := fun _ => R) N) ⁻¹' s) =
      (frestrictLe (π := fun _ => FineRecord R) N) ⁻¹' (coarseHistory (N + 1) ⁻¹' s) := rfl
  rw [he, P.squareProcess.cylinderPOVM.fullVectorMeasure_prefix N _
    (hs.preimage (measurable_coarseHistory (N + 1)))]
  exact P.physicalCylinderEffect_eq_compiled N s hs

theorem physicalTranscriptVectorMeasure_positive (s : Set (Transcript R))
    (hs : MeasurableSet s) : (P.represented_physicalTranscriptVectorMeasure s).PosSemidef := by
  letI : Nonempty R := P.record_nonempty
  exact P.represented_physicalCylinderPOVM.fullVectorMeasure_positive s hs

theorem physicalTranscriptVectorMeasure_total : P.represented_physicalTranscriptVectorMeasure univ = 1 := by
  letI : Nonempty R := P.record_nonempty
  exact P.represented_physicalCylinderPOVM.fullVectorMeasure_total

def represented_physicalBornMeasure (P : MatrixProcess a b R) (ρ : JointInputMatrix a b)
    (hρ : ρ.PosSemidef) : Measure (Transcript R) := by
  letI : Nonempty R := P.record_nonempty
  exact P.represented_physicalCylinderPOVM.fullBornMeasure ρ hρ

theorem physicalBornMeasure_prefix (ρ : JointInputMatrix a b) (hρ : ρ.PosSemidef)
    (N : ℕ) (s : Set (Prefix R N)) (hs : MeasurableSet s) :
    P.represented_physicalBornMeasure ρ hρ ((frestrictLe (π := fun _ => R) N) ⁻¹' s) =
      ENNReal.ofReal (QuantumProver.HilbertNuclearTrace.trace (P.represented_physicalPrefixAction (N + 1) s ρ)).re := by
  letI : Nonempty R := P.record_nonempty
  rw [represented_physicalBornMeasure, P.represented_physicalCylinderPOVM.fullBornMeasure_prefix ρ hρ N s hs]
  exact congrArg (fun z : ℂ => ENNReal.ofReal z.re)
    (P.physicalPrefixAction_trace N s hs ρ).symm

theorem physicalBornMeasure_isProbability (ρ : JointInputMatrix a b) (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) : IsProbabilityMeasure (P.represented_physicalBornMeasure ρ hρ) := by
  letI : Nonempty R := P.record_nonempty
  exact P.represented_physicalCylinderPOVM.fullBornMeasure_isProbability ρ hρ htrace

theorem physicalBornMeasure_apply (ρ : JointInputMatrix a b) (hρ : ρ.PosSemidef)
    (s : Set (Transcript R)) (hs : MeasurableSet s) :
    P.represented_physicalBornMeasure ρ hρ s =
      ENNReal.ofReal ((P.represented_physicalTranscriptVectorMeasure s * ρ).trace.re) := by
  letI : Nonempty R := P.record_nonempty
  exact P.represented_physicalCylinderPOVM.fullBornMeasure_apply ρ hρ s hs

def physicalInfiniteReportedEffect (P : MatrixProcess a b R) (J : Transcript R → Fin 4)
    (j : Fin 4) : JointInputMatrix a b :=
  P.represented_physicalTranscriptVectorMeasure {ω | J ω = j}

theorem physicalInfiniteReportedEffect_eq_compiled (J : Transcript R → Fin 4)
    (hJ : Measurable J) (j : Fin 4) :
    P.physicalInfiniteReportedEffect J j =
      letI : Nonempty (FineRecord R) := P.fineRecord_nonempty
      P.squareProcess.cylinderPOVM.reportedEffect (J ∘ coarseTranscript) j := by
  letI : Nonempty (FineRecord R) := P.fineRecord_nonempty
  rw [physicalInfiniteReportedEffect, P.physicalTranscriptVectorMeasure_eq_compiled,
    VectorMeasure.map_apply _ measurable_coarseTranscript (measurableSet_eq_fun hJ measurable_const)]
  exact (P.squareProcess.cylinderPOVM.reportedEffect_eq_physical
    (J ∘ coarseTranscript) (hJ.comp measurable_coarseTranscript) j).symm

theorem physicalInfiniteReportedEffect_mem_actual_finite_tree_closure (J : Transcript R → Fin 4)
    (hJ : Measurable J) :
    P.physicalInfiniteReportedEffect J ∈
      closure (QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.finiteKrausReportedEffectSet a b) := by
  letI : Nonempty (FineRecord R) := P.fineRecord_nonempty
  have he : P.physicalInfiniteReportedEffect J =
      P.squareProcess.cylinderPOVM.reportedEffect (J ∘ coarseTranscript) :=
    funext fun j => P.physicalInfiniteReportedEffect_eq_compiled J hJ j
  rw [he]
  exact P.squareProcess.infinite_report_mem_actual_finite_tree_closure _
    (hJ.comp measurable_coarseTranscript)

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus QuantumProver.ElegantJointMeasurement.NormalFiniteTerminal
open QuantumProver.ElegantJointMeasurement.HilbertFiniteKrausPredual QuantumProver.ElegantJointMeasurement.HilbertPendingTensor
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixNormalTensorInstrument QuantumProver.MatrixNormalRightTensor
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator Kronecker

abbrev TerminalWorkspace (c d : ℕ) :=
  Joint (EuclideanSpace ℂ (Fin c)) (EuclideanSpace ℂ (Fin d))

def finiteJointChart (c d : ℕ) :
    JointInputMatrix c d →L[ℂ] Nuclear (TerminalWorkspace c d) :=
  jointOperation (fun _ : Unit => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin c)))
    (fun _ : Unit => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)))

theorem finiteJointChart_product {c d : ℕ} (X : InputMatrix c) (Y : InputMatrix d) :
    finiteJointChart c d (X ⊗ₖ Y) =
      tensorNuclear (E := EuclideanSpace ℂ (Fin c)) (E' := EuclideanSpace ℂ (Fin c))
        (F := EuclideanSpace ℂ (Fin d)) (F' := EuclideanSpace ℂ (Fin d))
        (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix X)
        (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix Y) := by
  have he := jointOperation_product
    (fun _ : Unit => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin c)))
    (fun _ : Unit => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d))) X Y
  simpa only [finiteJointChart, finiteKrausOperation, finiteKrausChannel,
    Fintype.sum_unique, QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearSandwich, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_id,
    QuantumProver.MatrixNormalTensorExtension.compose_id_id_apply] using he

theorem finiteJointChart_sandwich (c d : ℕ) (X : JointInputMatrix c d) :
    finiteJointChart c d X =
      compose (finiteTensorEmbedding (Fin c) (Fin d)).toContinuousLinearMap
        (finiteTensorEmbedding (Fin c) (Fin d)).toContinuousLinearMap.adjoint
        (QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix X) := by
  simp only [finiteJointChart, jointOperation, finiteKrausOperation, finiteKrausChannel,
    ContinuousLinearMap.comp_apply, sum_apply, Fintype.sum_unique, jointKraus,
    tensorMap_id_id, ContinuousLinearMap.id_comp, QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearSandwich]
  simp only [Fintype.sum_prod_type, Fintype.sum_unique]

def finiteJointDecode (c d : ℕ) :
    Nuclear (TerminalWorkspace c d) →L[ℂ] JointInputMatrix c d :=
  (matrixDecode (C := Fin c × Fin d)).comp
    (compose (finiteTensorEmbedding (Fin c) (Fin d)).toContinuousLinearMap.adjoint
      (finiteTensorEmbedding (Fin c) (Fin d)).toContinuousLinearMap)

theorem finiteJointDecode_chart (c d : ℕ) (X : JointInputMatrix c d) :
    finiteJointDecode c d (finiteJointChart c d X) = X := by
  let J := (finiteTensorEmbedding (Fin c) (Fin d)).toContinuousLinearMap
  have hJ : J.adjoint ∘L J = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin c × Fin d)) :=
    (ContinuousLinearMap.isometry_iff_adjoint_comp_self J).mp
      (finiteTensorEmbedding (Fin c) (Fin d)).isometry
  have he : compose J.adjoint J (finiteJointChart c d X) =
      QuantumProver.ElegantJointMeasurement.HilbertRecovery.nuclearMatrix X := by
    rw [finiteJointChart_sandwich]
    apply QuantumProver.NuclearOperator.toOperator_injective
    simp only [toOperator_compose, ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.comp_assoc J.adjoint J, hJ,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  change matrixDecode (compose J.adjoint J (finiteJointChart c d X)) = X
  rw [he, matrixDecode_nuclearMatrix]

def terminalJointOperation {R : Type*} [MeasurableSpace R] {N c d : ℕ}
    (Q : NormalTerminal R N c d) (h : History R N) :
    Nuclear JointWorkspace →L[ℂ] Nuclear (TerminalWorkspace c d) :=
  (rightTensorOperation (G := EuclideanSpace ℂ (Fin c)) Q.bob h univ).comp
    (tensorOperation (G := Workspace) Q.alice h univ)

theorem terminalJointOperation_product {R : Type*} [MeasurableSpace R] {N c d : ℕ}
    (Q : NormalTerminal R N c d) (h : History R N) (T U : Nuclear Workspace) :
    terminalJointOperation Q h (workspaceTensor T U) =
      tensorNuclear (E := EuclideanSpace ℂ (Fin c)) (E' := EuclideanSpace ℂ (Fin c))
        (F := EuclideanSpace ℂ (Fin d)) (F' := EuclideanSpace ℂ (Fin d))
        (Q.alice.operation h univ T) (Q.bob.operation h univ U) := by
  change rightTensorOperation (G := EuclideanSpace ℂ (Fin c)) Q.bob h univ
    (tensorOperation (G := Workspace) Q.alice h univ
      (tensorNuclear (E := Workspace) (E' := Workspace) (F := Workspace) (F' := Workspace) T U)) = _
  rw [tensorOperation_tensor Q.alice h univ MeasurableSet.univ,
    rightTensorOperation_tensor Q.bob h univ MeasurableSet.univ]

theorem stronglyMeasurable_terminalJointOperation {R : Type*} [MeasurableSpace R]
    {N c d : ℕ} (Q : NormalTerminal R N c d) (T : Nuclear JointWorkspace) :
    StronglyMeasurable (fun h => terminalJointOperation Q h T) := by
  exact stronglyMeasurable_rightTensorOperation_variable Q.bob univ MeasurableSet.univ
    (fun h => tensorOperation (G := Workspace) Q.alice h univ T)
    (stronglyMeasurable_tensorOperation Q.alice univ MeasurableSet.univ T)

theorem terminalJointOperation_norm_apply {R : Type*} [MeasurableSpace R]
    {N c d : ℕ} (Q : NormalTerminal R N c d) (h : History R N)
    (T : Nuclear JointWorkspace) : ‖terminalJointOperation Q h T‖ ≤ ‖T‖ := by
  have hA := QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.normalOperation_norm_le_of_cp_trace_nonincreasing
    (tensorOperation (G := Workspace) Q.alice h univ)
    (tensorOperation_completelyPositive Q.alice h univ MeasurableSet.univ)
    (tensorOperation_traceNonincreasing Q.alice h univ MeasurableSet.univ) T
  have hB := QuantumProver.ElegantJointMeasurement.NormalCompleteContraction.normalOperation_norm_le_of_cp_trace_nonincreasing
    (rightTensorOperation (G := EuclideanSpace ℂ (Fin c)) Q.bob h univ)
    (rightTensorOperation_completelyPositive Q.bob h univ MeasurableSet.univ)
    (rightTensorOperation_traceNonincreasing Q.bob h univ MeasurableSet.univ)
    (tensorOperation (G := Workspace) Q.alice h univ T)
  exact hB.trans hA

theorem terminalJointOperation_norm_le_one {R : Type*} [MeasurableSpace R]
    {N c d : ℕ} (Q : NormalTerminal R N c d) (h : History R N) :
    ‖terminalJointOperation Q h‖ ≤ 1 := by
  apply (terminalJointOperation Q h).opNorm_le_bound zero_le_one
  intro T
  simpa only [one_mul] using terminalJointOperation_norm_apply Q h T

theorem terminalJointOperation_trace {R : Type*} [MeasurableSpace R]
    {N c d : ℕ} (Q : NormalTerminal R N c d) (h : History R N)
    (T : Nuclear JointWorkspace) :
    QuantumProver.HilbertNuclearTrace.trace (terminalJointOperation Q h T) =
      QuantumProver.HilbertNuclearTrace.trace T := by
  rw [terminalJointOperation, ContinuousLinearMap.comp_apply,
    rightTensorOperation_trace_preserving Q.bob h,
    tensorOperation_trace_preserving Q.alice h]

end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus QuantumProver.ElegantJointMeasurement.NormalFiniteTerminal
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixNuclearContinuationTransport
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator Kronecker

def chargedDecode {a b : ℕ} (X : JointInputMatrix a b) :
    Nuclear (PhysicalChoiWorkspace a b) →L[ℂ] Nuclear JointWorkspace :=
  (Fintype.card (Fin a × Fin b) : ℂ) • nuclearDecode X

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

def represented_physicalInputDensity (n : ℕ) (X : JointInputMatrix a b) (h : History R n) :
    Nuclear JointWorkspace := chargedDecode X (P.represented_physicalState n h)

theorem physicalInputDensity_integrable (n : ℕ) (X : JointInputMatrix a b) :
    Integrable (P.represented_physicalInputDensity n X) (P.represented_physicalPrefixMeasure n) :=
  (chargedDecode X).integrable_comp (P.represented_physicalState_integrable n)

theorem physicalPrefixAction_eq_physicalInputDensity (n : ℕ) (s : Set (History R n))
    (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    P.represented_physicalPrefixAction n s X =
      ∫ h in s, P.represented_physicalInputDensity n X h ∂P.represented_physicalPrefixMeasure n := by
  rw [P.physicalPrefixAction_apply n s hs X]
  exact (chargedDecode X).integral_comp_comm (P.represented_physicalState_integrable n).restrict |>.symm

variable {c d : ℕ}

def physicalQuantumNuclearOutput (N : ℕ) (Q : NormalTerminal R N c d)
    (X : JointInputMatrix a b) : Nuclear (TerminalWorkspace c d) :=
  ∫ h, terminalJointOperation Q h (P.represented_physicalInputDensity N X h)
    ∂P.represented_physicalPrefixMeasure N

def represented_physicalQuantumOutput (N : ℕ) (Q : NormalTerminal R N c d)
    (X : JointInputMatrix a b) : JointInputMatrix c d :=
  finiteJointDecode c d (P.physicalQuantumNuclearOutput N Q X)

theorem physicalQuantumOutput_integrable (N : ℕ) (Q : NormalTerminal R N c d)
    (X : JointInputMatrix a b) :
    Integrable (fun h => terminalJointOperation Q h (P.represented_physicalInputDensity N X h))
      (P.represented_physicalPrefixMeasure N) := by
  have hi := integrable_continuation_field measurable_id (P.physicalInputDensity_integrable N X)
    (terminalJointOperation Q) (stronglyMeasurable_terminalJointOperation Q)
    (terminalJointOperation_norm_le_one Q)
  simpa only [id_eq] using hi

theorem physicalQuantumNuclearOutput_eq_fine_integral (N : ℕ) (Q : NormalTerminal R N c d)
    (X : JointInputMatrix a b) :
    P.physicalQuantumNuclearOutput N Q X =
      ∫ h, terminalJointOperation Q (coarseHistory N h)
        (P.fineCumulativeChannel N h X) ∂P.finePrefixMeasure N := by
  let Ψ : History R N → Nuclear (PhysicalChoiWorkspace a b) →L[ℂ]
      Nuclear (TerminalWorkspace c d) :=
    fun h => (terminalJointOperation Q h).comp (chargedDecode X)
  have hΨ (T : Nuclear (PhysicalChoiWorkspace a b)) : StronglyMeasurable (fun h => Ψ h T) :=
    stronglyMeasurable_terminalJointOperation Q (chargedDecode X T)
  have hbound (h : History R N) : ‖Ψ h‖ ≤ ‖chargedDecode X‖ := by
    have hm := mul_le_mul_of_nonneg_right (terminalJointOperation_norm_le_one Q h)
      (norm_nonneg (chargedDecode X))
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [one_mul] using hm)
  have he := integral_continuation_eq_of_preimage_setIntegral_eq
    (measurable_coarseHistory (R := R) N)
    (P.fineChoiDensity_integrable N) (P.represented_physicalState_integrable N)
    (fun s hs => P.physical_fine_prefix_setIntegral N s hs)
    Ψ hΨ (norm_nonneg (chargedDecode X)) hbound
  change (∫ h, Ψ h (P.represented_physicalState N h) ∂P.represented_physicalPrefixMeasure N) = _
  rw [← he]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun h => by
    change terminalJointOperation Q (coarseHistory N h)
      ((Fintype.card (Fin a × Fin b) : ℂ) • nuclearDecode X (P.fineChoiDensity N h)) = _
    rw [P.fineChoiDensity_decode])

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.ElegantJointMeasurement.NormalInstrumentKraus
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixNuclearKernelTransport
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

theorem chargedDecode_normalAmplification {a b : ℕ}
    (Φ : NormalOperation JointWorkspace JointWorkspace) (X : JointInputMatrix a b)
    (T : Nuclear (PhysicalChoiWorkspace a b)) :
    chargedDecode X (normalAmplification (R := Fin a × Fin b) Φ T) =
      Φ (chargedDecode X T) := by
  have he : nuclearDecode X (normalAmplification (R := Fin a × Fin b) Φ T) =
      Φ (nuclearDecode X T) := by
    rw [normalAmplification_apply]
    simp only [nuclearDecode, sum_apply, smul_apply]
    change (∑ i, ∑ j, X i j • nuclearBlock i j
      (nuclearAssembly (fun p q => Φ (nuclearBlock p q T)))) =
      Φ (∑ i, ∑ j, X i j • nuclearBlock i j T)
    simp only [nuclearBlock_nuclearAssembly, map_sum, map_smul]
  change (Fintype.card (Fin a × Fin b) : ℂ) •
      nuclearDecode X (normalAmplification Φ T) =
    Φ ((Fintype.card (Fin a × Fin b) : ℂ) • nuclearDecode X T)
  rw [he, map_smul]

theorem history_countable {R : Type*} [MeasurableSpace R] [Countable R] (n : ℕ) :
    Countable (History R n) := by
  cases n with
  | zero => infer_instance
  | succ n => change Countable (Prefix R n); infer_instance

theorem history_measurableSingletonClass {R : Type*} [MeasurableSpace R]
    [MeasurableSingletonClass R] (n : ℕ) : MeasurableSingletonClass (History R n) := by
  cases n with
  | zero => infer_instance
  | succ n => change MeasurableSingletonClass (Prefix R n); infer_instance

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)

theorem physicalPrefixAction_successorEvent (n : ℕ) (s : Set (History R n))
    (t : Set R) (hs : MeasurableSet s) (ht : MeasurableSet t) (X : JointInputMatrix a b) :
    P.represented_physicalPrefixAction (n + 1) (successorEvent n s t) X =
      ∫ h in s, (P.represented_physicalStepInstrument n).operation h t (P.represented_physicalInputDensity n X h)
        ∂P.represented_physicalPrefixMeasure n := by
  change chargedDecode X (P.represented_physicalPrefixVectorMeasure (n + 1) (successorEvent n s t)) = _
  rw [P.represented_physicalPrefixVectorMeasure_successorEvent n s t hs ht]
  have hi : Integrable (fun h => (P.represented_physicalReferenceInstrument n).operation h t
      (P.represented_physicalState n h)) (P.represented_physicalPrefixMeasure n) := by
    simpa only [id_eq] using integrable_event_operation_field
      (P.represented_physicalReferenceInstrument n) measurable_id t ht (P.represented_physicalState_integrable n)
  rw [← (chargedDecode X).integral_comp_comm hi.restrict]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun h =>
    chargedDecode_normalAmplification ((P.represented_physicalStepInstrument n).operation h t)
      X (P.represented_physicalState n h))

theorem physicalPrefixAction_zero_singleton (X : JointInputMatrix a b) :
    P.represented_physicalPrefixAction 0 {PUnit.unit} X = P.initialJointOperation X := by
  have he : ({PUnit.unit} : Set PUnit) = univ := by
    ext h
    cases h
    simp
  rw [he, P.physicalPrefixAction_zero_univ]

theorem successorEvent_singletons (n : ℕ) (h : History R n) (r : R) :
    successorEvent n {h} {r} = {appendHistory n (h,r)} := by
  ext z
  change (appendHistory n).symm z ∈ ({h} ×ˢ {r}) ↔ z = appendHistory n (h,r)
  constructor
  · rintro ⟨hh,hr⟩
    change ((appendHistory n).symm z).1 = h at hh
    change ((appendHistory n).symm z).2 = r at hr
    have he : (appendHistory n).symm z = (h,r) := Prod.ext hh hr
    exact ((appendHistory n).apply_symm_apply z).symm.trans (congrArg (appendHistory n) he)
  · intro hz
    subst z
    simp

theorem physicalPrefixAction_singleton_successor [MeasurableSingletonClass R]
    (n : ℕ) (h : History R n) (r : R) (X : JointInputMatrix a b) :
    P.represented_physicalPrefixAction (n + 1) {appendHistory n (h,r)} X =
      (P.represented_physicalStepInstrument n).operation h {r} (P.represented_physicalPrefixAction n {h} X) := by
  letI := history_measurableSingletonClass (R := R) n
  rw [← successorEvent_singletons n h r,
    P.physicalPrefixAction_successorEvent n {h} {r} (measurableSet_singleton h)
      (measurableSet_singleton r) X,
    P.physicalPrefixAction_eq_physicalInputDensity n {h} (measurableSet_singleton h) X]
  have he : (∫ z in {h}, (P.represented_physicalStepInstrument n).operation z {r}
      (P.represented_physicalInputDensity n X z) ∂P.represented_physicalPrefixMeasure n) =
    ∫ z in {h}, (P.represented_physicalStepInstrument n).operation h {r}
      (P.represented_physicalInputDensity n X z) ∂P.represented_physicalPrefixMeasure n := by
    apply setIntegral_congr_fun (measurableSet_singleton h)
    intro z hz
    have hz' : z = h := Set.mem_singleton_iff.mp hz
    subst z
    rfl
  rw [he]
  exact ((P.represented_physicalStepInstrument n).operation h {r}).integral_comp_comm
    (P.physicalInputDensity_integrable n X).restrict

theorem hasSum_terminal_physicalPrefixAction [Countable R] [MeasurableSingletonClass R]
    {c d : ℕ} (N : ℕ) (Q : NormalTerminal R N c d) (X : JointInputMatrix a b) :
    HasSum (fun h : History R N =>
      terminalJointOperation Q h (P.represented_physicalPrefixAction N {h} X))
      (P.physicalQuantumNuclearOutput N Q X) := by
  letI := history_countable (R := R) N
  letI := history_measurableSingletonClass (R := R) N
  have he (h : History R N) :
      (∫ z in {h}, terminalJointOperation Q z (P.represented_physicalInputDensity N X z)
        ∂P.represented_physicalPrefixMeasure N) =
      terminalJointOperation Q h (P.represented_physicalPrefixAction N {h} X) := by
    rw [P.physicalPrefixAction_eq_physicalInputDensity N {h} (measurableSet_singleton h) X]
    have he' : (∫ z in {h}, terminalJointOperation Q z (P.represented_physicalInputDensity N X z)
        ∂P.represented_physicalPrefixMeasure N) =
      ∫ z in {h}, terminalJointOperation Q h (P.represented_physicalInputDensity N X z)
        ∂P.represented_physicalPrefixMeasure N := by
      apply setIntegral_congr_fun (measurableSet_singleton h)
      intro z hz
      have hz' : z = h := Set.mem_singleton_iff.mp hz
      subst z
      rfl
    rw [he']
    exact (terminalJointOperation Q h).integral_comp_comm
      (P.physicalInputDensity_integrable N X).restrict
  have hd : Pairwise (fun h k : History R N => Disjoint ({h} : Set (History R N)) {k}) := by
    intro h k hne
    exact Set.disjoint_singleton.mpr hne
  have hs := hasSum_integral_iUnion (fun h : History R N => measurableSet_singleton h) hd
    (P.physicalQuantumOutput_integrable N Q X).integrableOn
  simpa only [Set.iUnion_of_singleton, setIntegral_univ, he, physicalQuantumNuclearOutput] using hs

theorem physicalQuantumOutput_eq_of_hasSum [Countable R] [MeasurableSingletonClass R]
    {c d : ℕ} (N : ℕ) (Q : NormalTerminal R N c d) (X : JointInputMatrix a b)
    (Y : JointInputMatrix c d)
    (hY : HasSum (fun h : History R N =>
      terminalJointOperation Q h (P.represented_physicalPrefixAction N {h} X)) (finiteJointChart c d Y)) :
    P.represented_physicalQuantumOutput N Q X = Y := by
  have he := (P.hasSum_terminal_physicalPrefixAction N Q X).unique hY
  rw [represented_physicalQuantumOutput, he, finiteJointDecode_chart]

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess

namespace QuantumProver.ElegantJointMeasurement.NormalProcess
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.ElegantJointMeasurement.NormalCPInstruments QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixSquareQuantumTerminal
open scoped BigOperators Topology ComplexOrder Matrix.Norms.L2Operator Kronecker

def pairFiniteChannel {a b c d : ℕ}
    (Φ : InputMatrix a →L[ℂ] InputMatrix c) (Ψ : InputMatrix b →L[ℂ] InputMatrix d) :
    JointInputMatrix a b →L[ℂ] JointInputMatrix c d :=
  (QuantumProver.WernerEndpoint.ContinuousCPProtocol.bobReferenceCLM (a := c) Ψ.toLinearMap).comp
    (QuantumProver.WernerEndpoint.ContinuousCPProtocol.aliceReferenceCLM (b := b) Φ.toLinearMap)

theorem pairFiniteChannel_product {a b c d : ℕ}
    (Φ : InputMatrix a →L[ℂ] InputMatrix c) (Ψ : InputMatrix b →L[ℂ] InputMatrix d)
    (X : InputMatrix a) (Y : InputMatrix b) :
    pairFiniteChannel Φ Ψ (X ⊗ₖ Y) = Φ X ⊗ₖ Ψ Y := by
  have hA : QuantumProver.WernerEndpoint.ContinuousCPProtocol.aliceReferenceCLM
      (b := b) Φ.toLinearMap (X ⊗ₖ Y) = Φ X ⊗ₖ Y := by
    ext i j
    change Φ (fun k l => X k l * Y i.2 j.2) i.1 j.1 = Φ X i.1 j.1 * Y i.2 j.2
    have he : (fun k l => X k l * Y i.2 j.2) = Y i.2 j.2 • X := by
      ext k l
      change X k l * Y i.2 j.2 = Y i.2 j.2 * X k l
      exact mul_comm _ _
    rw [he, map_smul]
    change Y i.2 j.2 * Φ X i.1 j.1 = Φ X i.1 j.1 * Y i.2 j.2
    exact mul_comm _ _
  have hB : QuantumProver.WernerEndpoint.ContinuousCPProtocol.bobReferenceCLM
      (a := c) Ψ.toLinearMap (Φ X ⊗ₖ Y) = Φ X ⊗ₖ Ψ Y := by
    ext i j
    change Ψ (fun k l => Φ X i.1 j.1 * Y k l) i.2 j.2 = Φ X i.1 j.1 * Ψ Y i.2 j.2
    have he : (fun k l => Φ X i.1 j.1 * Y k l) = Φ X i.1 j.1 • Y := rfl
    rw [he, map_smul]
    rfl
  change QuantumProver.WernerEndpoint.ContinuousCPProtocol.bobReferenceCLM Ψ.toLinearMap
    (QuantumProver.WernerEndpoint.ContinuousCPProtocol.aliceReferenceCLM Φ.toLinearMap (X ⊗ₖ Y)) = _
  rw [hA, hB]

namespace MatrixProcess
variable {a b : ℕ} {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable [NeZero a] [NeZero b] (P : MatrixProcess a b R)
variable {N c d : ℕ} (Q : NormalTerminal R N c d)

attribute [local irreducible] fineCumulativeChannel

theorem terminalChannel_compiled (h : History (FineRecord R) N) :
    terminalChannel ((P.compiledTerminal Q).toPolicy P.squareProcess) N h =
      pairFiniteChannel (P.finiteTerminalAlice Q h) (P.finiteTerminalBob Q h) := by
  simp only [terminalChannel, FinalTerminal.toPolicy_alice_final,
    FinalTerminal.toPolicy_bob_final, compiledTerminal, pairFiniteChannel]

attribute [local irreducible] layers layersAliceKraus layersBobKraus
  jointPendingOperation finiteTerminalAlice finiteTerminalBob

theorem terminalJointOperation_pending (h : History (FineRecord R) N)
    (X : JointInputMatrix a b) :
    terminalJointOperation Q (coarseHistory N h) (P.jointPendingOperation N h X) =
      finiteJointChart c d
        (pairFiniteChannel (P.finiteTerminalAlice Q h) (P.finiteTerminalBob Q h) X) := by
  have hp (A : InputMatrix a) (B : InputMatrix b) :
      terminalJointOperation Q (coarseHistory N h) (P.jointPendingOperation N h (A ⊗ₖ B)) =
        finiteJointChart c d
          (pairFiniteChannel (P.finiteTerminalAlice Q h) (P.finiteTerminalBob Q h) (A ⊗ₖ B)) := by
    rw [P.jointPendingOperation_product N h A B,
      terminalJointOperation_product Q (coarseHistory N h)
        ((P.layers N).aliceRecovery h A) ((P.layers N).bobRecovery h B),
      pairFiniteChannel_product, finiteJointChart_product]
    exact congrArg₂ (fun T : Nuclear (EuclideanSpace ℂ (Fin c)) =>
      fun U : Nuclear (EuclideanSpace ℂ (Fin d)) =>
        tensorNuclear (E := EuclideanSpace ℂ (Fin c)) (E' := EuclideanSpace ℂ (Fin c))
          (F := EuclideanSpace ℂ (Fin d)) (F' := EuclideanSpace ℂ (Fin d)) T U)
      (P.finiteTerminalAlice_nuclear_action Q h A).symm
      (P.finiteTerminalBob_nuclear_action Q h B).symm
  calc
    _ = terminalJointOperation Q (coarseHistory N h)
        (∑ st : Fin b × Fin b, P.jointPendingOperation N h
          (Matrix.of (fun i j => X (i,st.1) (j,st.2)) ⊗ₖ Matrix.single st.1 st.2 (1 : ℂ))) :=
      congrArg (terminalJointOperation Q (coarseHistory N h))
        (P.jointPendingOperation_eq_columnBlocks N h X)
    _ = ∑ st : Fin b × Fin b, terminalJointOperation Q (coarseHistory N h)
        (P.jointPendingOperation N h
          (Matrix.of (fun i j => X (i,st.1) (j,st.2)) ⊗ₖ Matrix.single st.1 st.2 (1 : ℂ))) :=
      map_sum _ _ _
    _ = ∑ st : Fin b × Fin b, finiteJointChart c d
        (pairFiniteChannel (P.finiteTerminalAlice Q h) (P.finiteTerminalBob Q h)
          (Matrix.of (fun i j => X (i,st.1) (j,st.2)) ⊗ₖ Matrix.single st.1 st.2 (1 : ℂ))) :=
      Finset.sum_congr rfl (fun st _ => hp _ _)
    _ = _ := by
      have he := congrArg (fun Y : JointInputMatrix a b => finiteJointChart c d
        (pairFiniteChannel (P.finiteTerminalAlice Q h) (P.finiteTerminalBob Q h) Y))
        (jointInputMatrix_eq_columnBlocks X)
      simp only [map_sum] at he
      exact he.symm

theorem finePrefixMeasure_eq_historyMeasure (n : ℕ) :
    P.finePrefixMeasure n = QuantumProver.MatrixSquareTerminalPrefixIntegral.historyMeasure P.squareProcess n := by
  cases n <;> rfl

theorem cumulativeSquare_eq_cumulativeOp (n : ℕ) (h : History (FineRecord R) n) :
    P.cumulativeSquare n h =
      QuantumProver.MatrixSquareTerminalPrefixIntegral.cumulativeOp P.squareProcess n h := by
  cases n <;> rfl

theorem terminal_fineCumulativeChannel_chart (h : History (FineRecord R) N)
    (X : JointInputMatrix a b) :
    terminalJointOperation Q (coarseHistory N h) (P.fineCumulativeChannel N h X) =
      finiteJointChart c d
        (QuantumProver.MatrixSquareTerminalPrefixIntegral.terminalIntegrand
          P.squareProcess N (P.compiledTerminal Q) X h) := by
  unfold QuantumProver.MatrixSquareTerminalPrefixIntegral.terminalIntegrand
  rw [P.fineCumulativeChannel_apply, P.terminalJointOperation_pending,
    P.terminalChannel_compiled, ← P.cumulativeSquare_eq_cumulativeOp]
  rfl

theorem physicalQuantumNuclearOutput_eq_compiled_chart (N : ℕ)
    (Q : NormalTerminal R N c d) (X : JointInputMatrix a b) :
    P.physicalQuantumNuclearOutput N Q X = finiteJointChart c d (P.compiledQuantumOutput Q X) := by
  rw [P.physicalQuantumNuclearOutput_eq_fine_integral]
  simp_rw [P.terminal_fineCumulativeChannel_chart Q]
  rw [P.finePrefixMeasure_eq_historyMeasure,
    (finiteJointChart c d).integral_comp_comm
      (QuantumProver.MatrixSquareTerminalPrefixIntegral.terminalIntegrand_integrable
        P.squareProcess N (P.compiledTerminal Q) X),
    QuantumProver.MatrixSquareTerminalPrefixIntegral.terminalIntegral_eq_finiteHorizonChannel]
  rfl

theorem physicalQuantumOutput_eq_compiled (N : ℕ) (Q : NormalTerminal R N c d)
    (X : JointInputMatrix a b) :
    P.represented_physicalQuantumOutput N Q X = P.compiledQuantumOutput Q X := by
  rw [represented_physicalQuantumOutput, P.physicalQuantumNuclearOutput_eq_compiled_chart,
    finiteJointDecode_chart]

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.NormalProcess
