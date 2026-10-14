import QuantumProver.InformationTheory.WernerEndpoint.NormalSingletCost
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalProcess
import QuantumProver.InformationTheory.ElegantJointMeasurement.FiniteNormalOperationalBridge
import QuantumProver.QuantumChannels.PhysicalProtocolData
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalOutputTransport
import QuantumProver.InformationTheory.ElegantJointMeasurement.CommonPhysicalQuantumOutput
import QuantumProver.QuantumChannels.PhysicalUniverseTransport
import QuantumProver.InformationTheory.ElegantJointMeasurement.PhysicalFreePreparationSerialization

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable section
universe u v w

namespace QuantumProver.WernerEndpoint

open OperationalEndpointCost QuantumProver.ElegantJointMeasurement.NormalProcess
open scoped Topology ComplexOrder Matrix.Norms.L2Operator

section PhysicalOutputLimit

variable {R : Type*} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b c d : ℕ} [NeZero a] [NeZero b]

theorem physicalNormalQuantumOutputLimit_mem_outputClosure
    (P : MatrixProcess a b R) (Q : (N : ℕ) → NormalTerminal R N c d)
    (hc : 0 < c) (hd : 0 < d) (ψ : Fin a × Fin b → ℂ)
    (σ : EndpointProtocolClosure.OutputMatrix c d)
    (hLimit : Filter.Tendsto
      (fun N => P.represented_physicalQuantumOutput N (Q N) (pureDensity ψ))
      Filter.atTop (nhds σ)) : σ ∈ EndpointProtocolClosure.outputClosure ψ := by
  have represented_hPhysical :
      (fun N => P.represented_physicalQuantumOutput N (Q N) (pureDensity ψ)) =
      (fun N => QuantumProver.MatrixSquareQuantumTerminal.finiteHorizonChannel
        P.squareProcess N (P.compiledTerminal (Q N)) (pureDensity ψ)) := by
    funext N
    simpa only [MatrixProcess.compiledQuantumOutput] using
      P.physicalQuantumOutput_eq_compiled N (Q N) (pureDensity ψ)
  rw [represented_hPhysical] at hLimit
  exact squareQuantumOutputLimit_mem_outputClosure P.squareProcess
    (fun N => P.compiledTerminal (Q N)) hc hd ψ σ hLimit

theorem physicalNormalQuantumOutputLimit_exists_finiteProtocol_approx
    (P : MatrixProcess a b R) (Q : (N : ℕ) → NormalTerminal R N c d)
    (hc : 0 < c) (hd : 0 < d) (X : JointInputMatrix a b)
    (σ : JointInputMatrix c d)
    (hLimit : Filter.Tendsto (fun N => P.represented_physicalQuantumOutput N (Q N) X)
      Filter.atTop (nhds σ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : FiniteLocalProtocol c d a b, ‖U.apply X - σ‖ < ε := by
  have represented_hPhysical : (fun N => P.represented_physicalQuantumOutput N (Q N) X) =
      (fun N => QuantumProver.MatrixSquareQuantumTerminal.finiteHorizonChannel
        P.squareProcess N (P.compiledTerminal (Q N)) X) := by
    funext N
    simpa only [MatrixProcess.compiledQuantumOutput] using
      P.physicalQuantumOutput_eq_compiled N (Q N) X
  rw [represented_hPhysical] at hLimit
  exact squareQuantumOutputLimit_exists_finiteProtocol_approx P.squareProcess
    (fun N => P.compiledTerminal (Q N)) hc hd X σ hLimit ε hε

theorem physicalNormalQuantumOutputLimit_isDensity
    (P : MatrixProcess a b R) (Q : (N : ℕ) → NormalTerminal R N c d)
    (hc : 0 < c) (hd : 0 < d) (ψ : Fin a × Fin b → ℂ)
    (hψ : vectorNormSq ψ = 1) (σ : JointInputMatrix c d)
    (hLimit : Filter.Tendsto
      (fun N => P.represented_physicalQuantumOutput N (Q N) (pureDensity ψ))
      Filter.atTop (nhds σ)) : QuantumProver.QuantumEntropy.IsDensity σ :=
  EndpointProtocolClosure.outputClosure_isDensity ψ hψ
    (physicalNormalQuantumOutputLimit_mem_outputClosure P Q hc hd ψ σ hLimit)

end PhysicalOutputLimit

private theorem physicalSinglet_output_dimension_pos (d n : ℕ) (hd : 2 ≤ d) :
    0 < Fintype.card (PhysicalPower d n) := by
  rw [physicalPower_card]
  exact pow_pos (by omega) n

local instance physicalSinglet_input_neZero (m : ℕ) :
    NeZero (Fintype.card (PhysicalPower 2 m)) := by
  constructor
  rw [physicalPower_card]
  exact pow_ne_zero m (by decide)

def ordinaryNormalSingletHHTAchievableRate (d : ℕ) (r : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
    ∃ n m : ℕ, 0 < n ∧ ∃ (R : Type u) (mR : MeasurableSpace R),
      letI := mR
      ∃ hR : StandardBorelSpace R,
        letI := hR
        ∃ P : MatrixProcess (Fintype.card (PhysicalPower 2 m))
          (Fintype.card (PhysicalPower 2 m)) R,
        ∃ Q : (N : ℕ) → NormalTerminal R N (Fintype.card (PhysicalPower d n))
          (Fintype.card (PhysicalPower d n)),
        ∃ σ : SingletOutputMatrix d n,
          Filter.Tendsto (fun N => P.represented_physicalQuantumOutput N (Q N)
            (pureDensity (finiteSingletPairPowerVector m))) Filter.atTop (nhds σ) ∧
          |r - (m : ℝ) / (n : ℝ)| ≤ delta ∧
          FidelityError.buresDistance (physicalSingletOutput d n σ)
            (physicalAntisymmetricState d n) ≤ epsilon

def ordinaryNormalSingletHHTCost (d : ℕ) : ℝ :=
  sInf {r : ℝ | ordinaryNormalSingletHHTAchievableRate.{u} d r}

theorem ordinaryNormalSingletHHTAchievableRate_lower (d : ℕ) (hd : 2 ≤ d) (r : ℝ)
    (hRate : ordinaryNormalSingletHHTAchievableRate.{u} d r) : 1 ≤ r := by
  apply singletOutputClosure_HHTRate_lower d hd r
  intro epsilon hEpsilon delta hDelta
  obtain ⟨n, m, hn, R, mR, hR, P, Q, σ, hLimit, hRatio, hBures⟩ :=
    hRate epsilon hEpsilon delta hDelta
  letI := mR
  letI := hR
  have hPositive := physicalSinglet_output_dimension_pos d n hd
  exact ⟨n, m, hn, σ,
    physicalNormalQuantumOutputLimit_mem_outputClosure P Q hPositive hPositive
      (finiteSingletPairPowerVector m) σ hLimit, hRatio, hBures⟩

theorem finiteSingletHHTAchievableRate_implies_ordinaryNormal
    (d : ℕ) (hd : 2 ≤ d) (r : ℝ) (hRate : finiteSingletHHTAchievableRate d r) :
    ordinaryNormalSingletHHTAchievableRate.{u} d r := by
  intro epsilon hEpsilon delta hDelta
  obtain ⟨n, m, hn, U, hRatio, hBures⟩ := hRate epsilon hEpsilon delta hDelta
  have hPositive := physicalSinglet_output_dimension_pos d n hd
  refine ⟨n, m, hn, ULift.{u} ℕ, inferInstance, inferInstance,
    QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalRecordLift.liftedOfProtocol.{u} U,
    (fun N => QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalOperationalBridge.physicalLiftedFiniteNormalTerminal
      U N hPositive hPositive),
    U.apply (pureDensity (finiteSingletPairPowerVector m)), ?_, hRatio, ?_⟩
  · exact QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalOperationalBridge.tendsto_physicalQuantumOutput_liftedOfProtocol
      U hPositive hPositive (pureDensity (finiteSingletPairPowerVector m))
  · exact hBures

theorem ordinaryNormalSingletHHTAchievableRate_one (d : ℕ) (hd : 2 ≤ d) :
    ordinaryNormalSingletHHTAchievableRate.{u} d 1 :=
  finiteSingletHHTAchievableRate_implies_ordinaryNormal d hd 1
    ((finiteSingletHHTAchievableRate_iff d 1).mpr (finiteHHTAchievableRate_one d hd))

theorem ordinaryNormalSingletHHTCost_eq_one (d : ℕ) (hd : 2 ≤ d) :
    ordinaryNormalSingletHHTCost.{u} d = 1 := by
  unfold ordinaryNormalSingletHHTCost
  have hOne : (1 : ℝ) ∈ {r : ℝ | ordinaryNormalSingletHHTAchievableRate.{u} d r} :=
    ordinaryNormalSingletHHTAchievableRate_one d hd
  have hLower : ∀ r ∈ {r : ℝ | ordinaryNormalSingletHHTAchievableRate.{u} d r}, (1 : ℝ) ≤ r :=
    fun r hr => ordinaryNormalSingletHHTAchievableRate_lower d hd r hr
  exact le_antisymm (csInf_le ⟨1, hLower⟩ hOne) (le_csInf ⟨1, hOne⟩ hLower)

section PhysicalPhysicalOutput

open QuantumProver.ElegantJointMeasurement.PhysicalCost
open QuantumProver.ElegantJointMeasurement.NormalPhysicalTerminalAdmission

variable {a b c d : ℕ} [NeZero a] [NeZero b]

def physicalPhysicalQuantumOutput (P : PhysicalProtocol.{u,v,w} a b)
    (N : ℕ) (Q : PhysicalReadout P N c d) (X : JointInputMatrix a b) :
    JointInputMatrix c d :=
  QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge.represented_physicalPhysicalQuantumOutput
    P.Outcomes P.domains P.aliceSections P.bobSections
    P.aliceOutputSections P.bobOutputSections P.aliceWiring P.bobWiring
    P.aliceInstrument P.bobInstrument P.chargedAlice P.chargedBob
    N c d Q.alice Q.bob X

theorem physicalPhysicalQuantumOutput_eq_matrix
    (P : PhysicalProtocol.{u,v,w} a b) (N : ℕ) (Q : PhysicalReadout P N c d)
    (hc : 0 < c) (hd : 0 < d) (X : JointInputMatrix a b) :
    physicalPhysicalQuantumOutput P N Q X =
      P.represented.represented_physicalQuantumOutput N (Q.represented hc hd) X := by
  exact QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge.physicalPhysicalQuantumOutput_eq_admitted
    P.Outcomes P.domains P.aliceSections P.bobSections
    P.aliceOutputSections P.bobOutputSections P.aliceWiring P.bobWiring
    P.aliceInstrument P.bobInstrument P.chargedAlice P.chargedBob
    N c d Q.alice Q.bob hc hd X

theorem physicalPhysicalQuantumOutputLimit_exists_finiteProtocol_approx
    (P : PhysicalProtocol.{u,v,w} a b)
    (Q : (N : ℕ) → PhysicalReadout P N c d) (hc : 0 < c) (hd : 0 < d)
    (X : JointInputMatrix a b) (σ : JointInputMatrix c d)
    (hLimit : Filter.Tendsto (fun N => physicalPhysicalQuantumOutput P N (Q N) X)
      Filter.atTop (nhds σ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : FiniteLocalProtocol c d a b, ‖U.apply X - σ‖ < ε := by
  have he : (fun N => physicalPhysicalQuantumOutput P N (Q N) X) =
      (fun N => P.represented.represented_physicalQuantumOutput N ((Q N).represented hc hd) X) := by
    funext N
    exact physicalPhysicalQuantumOutput_eq_matrix P N (Q N) hc hd X
  rw [he] at hLimit
  exact physicalNormalQuantumOutputLimit_exists_finiteProtocol_approx
    P.represented (fun N => (Q N).represented hc hd) hc hd X σ hLimit ε hε

theorem physicalPhysicalQuantumOutputLimit_mem_outputClosure
    (P : PhysicalProtocol.{u,v,w} a b)
    (Q : (N : ℕ) → PhysicalReadout P N c d) (hc : 0 < c) (hd : 0 < d)
    (ψ : Fin a × Fin b → ℂ) (σ : JointInputMatrix c d)
    (hLimit : Filter.Tendsto
      (fun N => physicalPhysicalQuantumOutput P N (Q N) (pureDensity ψ))
      Filter.atTop (nhds σ)) : σ ∈ EndpointProtocolClosure.outputClosure ψ := by
  have he : (fun N => physicalPhysicalQuantumOutput P N (Q N) (pureDensity ψ)) =
      (fun N => P.represented.represented_physicalQuantumOutput N ((Q N).represented hc hd) (pureDensity ψ)) := by
    funext N
    exact physicalPhysicalQuantumOutput_eq_matrix P N (Q N) hc hd (pureDensity ψ)
  rw [he] at hLimit
  exact physicalNormalQuantumOutputLimit_mem_outputClosure P.represented
    (fun N => (Q N).represented hc hd) hc hd ψ σ hLimit

theorem physicalPhysicalQuantumOutputLimit_isDensity
    (P : PhysicalProtocol.{u,v,w} a b)
    (Q : (N : ℕ) → PhysicalReadout P N c d) (hc : 0 < c) (hd : 0 < d)
    (ψ : Fin a × Fin b → ℂ) (hψ : vectorNormSq ψ = 1) (σ : JointInputMatrix c d)
    (hLimit : Filter.Tendsto
      (fun N => physicalPhysicalQuantumOutput P N (Q N) (pureDensity ψ))
      Filter.atTop (nhds σ)) : QuantumProver.QuantumEntropy.IsDensity σ :=
  EndpointProtocolClosure.outputClosure_isDensity ψ hψ
    (physicalPhysicalQuantumOutputLimit_mem_outputClosure P Q hc hd ψ σ hLimit)

end PhysicalPhysicalOutput

section PhysicalMixedPreparationOutput

open QuantumProver.ElegantJointMeasurement.PhysicalCost QuantumProver.ElegantJointMeasurement.PhysicalFreePreparationSerialization
open QuantumProver.ElegantJointMeasurement.NormalPreparedChronology

variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b c d : ℕ} [NeZero a] [NeZero b]
variable {FA FB : Type*}
  [NormedAddCommGroup FA] [InnerProductSpace ℂ FA] [CompleteSpace FA]
  [TopologicalSpace.SeparableSpace FA]
  [NormedAddCommGroup FB] [InnerProductSpace ℂ FB] [CompleteSpace FB]
  [TopologicalSpace.SeparableSpace FB]
  (P : MatrixProcess a b R)
  (τA : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear FA) (τB : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear FB)
  (hA : (QuantumProver.NuclearOperator.toOperator τA).IsPositive)
  (hB : (QuantumProver.NuclearOperator.toOperator τB).IsPositive)
  (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
  (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1)

theorem physicalMixedPreparationQuantumOutputLimit_exists_physical
    (Q : (N : ℕ) → NormalTerminal R N c d) (hc : 0 < c) (hd : 0 < d)
    (X : JointInputMatrix a b) (σ : JointInputMatrix c d)
    (hLimit : Filter.Tendsto
      (fun N => seededQuantumOutput P
        (preparedPhysicalStateLayer P τA τB hA hB hAT hBT) N (Q N) X)
      Filter.atTop (nhds σ)) :
    ∃ P' : PhysicalProtocol.{u,v,w} a b,
      ∃ Q' : (N : ℕ) → PhysicalReadout P' N c d,
        Filter.Tendsto (fun N => physicalPhysicalQuantumOutput P' N (Q' N) X)
          Filter.atTop (nhds σ) := by
  let P₁ := physicalMixedProtocol P τA τB hA hB hAT hBT
  let Q₁ := physicalMixedReadoutFamily P τA τB hA hB hAT hBT Q
  let P' : PhysicalProtocol.{u,v,w} a b := P₁.ulift
  let Q' : (N : ℕ) → PhysicalReadout P' N c d := fun N => (Q₁ N).ulift
  refine ⟨P', Q', ?_⟩
  have he : (fun N => physicalPhysicalQuantumOutput P' N (Q' N) X) =
      (fun N => physicalQuantumOutput P₁ (Q₁ N) X) := by
    funext N
    exact QuantumProver.MatrixPhysicalUniverseTransport.protocolQuantumOutput_ulift
      P₁ (Q₁ N) hc hd X
  rw [he]
  exact physical_mixed_quantum_output_tendsto P τA τB hA hB hAT hBT Q hc hd X σ hLimit

theorem physicalMixedPreparationQuantumOutputLimit_exists_finiteProtocol_approx
    (Q : (N : ℕ) → NormalTerminal R N c d) (hc : 0 < c) (hd : 0 < d)
    (X : JointInputMatrix a b) (σ : JointInputMatrix c d)
    (hLimit : Filter.Tendsto
      (fun N => seededQuantumOutput P
        (preparedPhysicalStateLayer P τA τB hA hB hAT hBT) N (Q N) X)
      Filter.atTop (nhds σ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : FiniteLocalProtocol c d a b, ‖U.apply X - σ‖ < ε := by
  refine physicalPhysicalQuantumOutputLimit_exists_finiteProtocol_approx
    (physicalMixedProtocol P τA τB hA hB hAT hBT)
    (physicalMixedReadoutFamily P τA τB hA hB hAT hBT Q) hc hd X σ ?_ ε hε
  exact physical_mixed_quantum_output_tendsto P τA τB hA hB hAT hBT Q hc hd X σ hLimit

theorem physicalMixedPreparationQuantumOutputLimit_mem_outputClosure
    (Q : (N : ℕ) → NormalTerminal R N c d) (hc : 0 < c) (hd : 0 < d)
    (ψ : Fin a × Fin b → ℂ) (σ : JointInputMatrix c d)
    (hLimit : Filter.Tendsto
      (fun N => seededQuantumOutput P
        (preparedPhysicalStateLayer P τA τB hA hB hAT hBT) N (Q N) (pureDensity ψ))
      Filter.atTop (nhds σ)) : σ ∈ EndpointProtocolClosure.outputClosure ψ := by
  apply physicalPhysicalQuantumOutputLimit_mem_outputClosure
    (physicalMixedProtocol P τA τB hA hB hAT hBT)
    (physicalMixedReadoutFamily P τA τB hA hB hAT hBT Q) hc hd ψ σ
  exact physical_mixed_quantum_output_tendsto P τA τB hA hB hAT hBT Q hc hd
    (pureDensity ψ) σ hLimit

end PhysicalMixedPreparationOutput

open QuantumProver.ElegantJointMeasurement.PhysicalCost

def ordinaryPhysicalSingletHHTAchievableRate (d : ℕ) (r : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
    ∃ n m : ℕ, 0 < n ∧
      ∃ P : PhysicalProtocol.{u,v,w} (Fintype.card (PhysicalPower 2 m))
        (Fintype.card (PhysicalPower 2 m)),
      ∃ Q : (N : ℕ) → PhysicalReadout P N (Fintype.card (PhysicalPower d n))
        (Fintype.card (PhysicalPower d n)),
      ∃ σ : SingletOutputMatrix d n,
        Filter.Tendsto (fun N => physicalPhysicalQuantumOutput P N (Q N)
          (pureDensity (finiteSingletPairPowerVector m))) Filter.atTop (nhds σ) ∧
        |r - (m : ℝ) / (n : ℝ)| ≤ delta ∧
        FidelityError.buresDistance (physicalSingletOutput d n σ)
          (physicalAntisymmetricState d n) ≤ epsilon

def ordinaryPhysicalSingletHHTCost (d : ℕ) : ℝ :=
  sInf {r : ℝ | ordinaryPhysicalSingletHHTAchievableRate.{u,v,w} d r}

theorem ordinaryPhysicalSingletHHTAchievableRate_implies_ordinaryNormal
    (d : ℕ) (hd : 2 ≤ d) (r : ℝ)
    (hRate : ordinaryPhysicalSingletHHTAchievableRate.{u,v,w} d r) :
    ordinaryNormalSingletHHTAchievableRate.{u} d r := by
  intro epsilon hEpsilon delta hDelta
  obtain ⟨n, m, hn, P, Q, σ, hLimit, hRatio, hBures⟩ :=
    hRate epsilon hEpsilon delta hDelta
  have hPositive := physicalSinglet_output_dimension_pos d n hd
  refine ⟨n, m, hn, QuantumProver.ElegantJointMeasurement.HilbertRecordCoding.CommonRecord P.Outcomes,
    inferInstance, inferInstance, P.represented,
    (fun N => (Q N).represented hPositive hPositive), σ, ?_, hRatio, hBures⟩
  have he : (fun N => physicalPhysicalQuantumOutput P N (Q N)
      (pureDensity (finiteSingletPairPowerVector m))) =
      (fun N => P.represented.represented_physicalQuantumOutput N ((Q N).represented hPositive hPositive)
        (pureDensity (finiteSingletPairPowerVector m))) := by
    funext N
    exact physicalPhysicalQuantumOutput_eq_matrix P N (Q N) hPositive hPositive _
  rw [he] at hLimit
  exact hLimit

theorem ordinaryNormalSingletHHTAchievableRate_implies_ordinaryPhysical
    (d : ℕ) (hd : 2 ≤ d) (r : ℝ)
    (hRate : ordinaryNormalSingletHHTAchievableRate.{u} d r) :
    ordinaryPhysicalSingletHHTAchievableRate.{u,v,w} d r := by
  intro epsilon hEpsilon delta hDelta
  obtain ⟨n, m, hn, R, mR, hR, P₀, Q₀, σ, hLimit, hRatio, hBures⟩ :=
    hRate epsilon hEpsilon delta hDelta
  letI := mR
  letI := hR
  have hPositive := physicalSinglet_output_dimension_pos d n hd
  let P₁ := commonPhysicalProtocol P₀
  let Q₁ := fun N => commonPhysicalReadout P₀ N (Q₀ N)
  let P : PhysicalProtocol.{u,v,w} (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m)) := P₁.ulift
  let Q : (N : ℕ) → PhysicalReadout P N (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) := fun N => (Q₁ N).ulift
  refine ⟨n, m, hn, P, Q, σ, ?_, hRatio, hBures⟩
  have he : (fun N => physicalPhysicalQuantumOutput P N (Q N)
      (pureDensity (finiteSingletPairPowerVector m))) =
      (fun N => P₀.represented_physicalQuantumOutput N (Q₀ N)
        (pureDensity (finiteSingletPairPowerVector m))) := by
    funext N
    exact (QuantumProver.MatrixPhysicalUniverseTransport.protocolQuantumOutput_ulift
      P₁ (Q₁ N) hPositive hPositive (pureDensity (finiteSingletPairPowerVector m))).trans
      (common_physicalQuantumOutput_eq_physical P₀ N (Q₀ N) hPositive hPositive
        (pureDensity (finiteSingletPairPowerVector m)))
  rw [he]
  exact hLimit

theorem ordinaryPhysicalSingletHHTAchievableRate_iff_ordinaryNormal
    (d : ℕ) (hd : 2 ≤ d) (r : ℝ) :
    ordinaryPhysicalSingletHHTAchievableRate.{u,v,w} d r ↔
      ordinaryNormalSingletHHTAchievableRate.{u} d r :=
  ⟨ordinaryPhysicalSingletHHTAchievableRate_implies_ordinaryNormal d hd r,
    ordinaryNormalSingletHHTAchievableRate_implies_ordinaryPhysical d hd r⟩

theorem ordinaryPhysicalSingletHHTAchievableRate_lower (d : ℕ) (hd : 2 ≤ d) (r : ℝ)
    (hRate : ordinaryPhysicalSingletHHTAchievableRate.{u,v,w} d r) : 1 ≤ r := by
  apply singletOutputClosure_HHTRate_lower d hd r
  intro epsilon hEpsilon delta hDelta
  obtain ⟨n, m, hn, P, Q, σ, hLimit, hRatio, hBures⟩ :=
    hRate epsilon hEpsilon delta hDelta
  have hPositive := physicalSinglet_output_dimension_pos d n hd
  exact ⟨n, m, hn, σ,
    physicalPhysicalQuantumOutputLimit_mem_outputClosure P Q hPositive hPositive
      (finiteSingletPairPowerVector m) σ hLimit, hRatio, hBures⟩

theorem finiteSingletHHTAchievableRate_implies_ordinaryPhysical
    (d : ℕ) (hd : 2 ≤ d) (r : ℝ) (hRate : finiteSingletHHTAchievableRate d r) :
    ordinaryPhysicalSingletHHTAchievableRate.{u,v,w} d r := by
  intro epsilon hEpsilon delta hDelta
  obtain ⟨n, m, hn, U, hRatio, hBures⟩ := hRate epsilon hEpsilon delta hDelta
  have hPositive := physicalSinglet_output_dimension_pos d n hd
  let P₀ := QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalRecordLift.liftedOfProtocol.{u} U
  let Q₀ := fun N => QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalOperationalBridge.physicalLiftedFiniteNormalTerminal
    U N hPositive hPositive
  let P₁ := QuantumProver.ElegantJointMeasurement.PhysicalCost.commonPhysicalProtocol P₀
  let Q₁ := fun N => QuantumProver.ElegantJointMeasurement.PhysicalCost.commonPhysicalReadout P₀ N (Q₀ N)
  let P : PhysicalProtocol.{u,v,w} (Fintype.card (PhysicalPower 2 m))
      (Fintype.card (PhysicalPower 2 m)) := P₁.ulift
  let Q : (N : ℕ) → PhysicalReadout P N (Fintype.card (PhysicalPower d n))
      (Fintype.card (PhysicalPower d n)) := fun N => (Q₁ N).ulift
  refine ⟨n, m, hn, P, Q, U.apply (pureDensity (finiteSingletPairPowerVector m)),
    ?_, hRatio, hBures⟩
  have he : (fun N => physicalPhysicalQuantumOutput P N (Q N)
      (pureDensity (finiteSingletPairPowerVector m))) =
      (fun N => P₀.represented_physicalQuantumOutput N (Q₀ N)
        (pureDensity (finiteSingletPairPowerVector m))) := by
    funext N
    exact (QuantumProver.MatrixPhysicalUniverseTransport.protocolQuantumOutput_ulift
      P₁ (Q₁ N) hPositive hPositive (pureDensity (finiteSingletPairPowerVector m))).trans
      (common_physicalQuantumOutput_eq_physical P₀ N (Q₀ N) hPositive hPositive
        (pureDensity (finiteSingletPairPowerVector m)))
  rw [he]
  exact QuantumProver.ElegantJointMeasurement.HilbertFiniteNormalOperationalBridge.tendsto_physicalQuantumOutput_liftedOfProtocol
    U hPositive hPositive (pureDensity (finiteSingletPairPowerVector m))

theorem ordinaryPhysicalSingletHHTAchievableRate_one (d : ℕ) (hd : 2 ≤ d) :
    ordinaryPhysicalSingletHHTAchievableRate.{u,v,w} d 1 :=
  finiteSingletHHTAchievableRate_implies_ordinaryPhysical d hd 1
    ((finiteSingletHHTAchievableRate_iff d 1).mpr (finiteHHTAchievableRate_one d hd))

theorem ordinaryPhysicalSingletHHTCost_eq_one (d : ℕ) (hd : 2 ≤ d) :
    ordinaryPhysicalSingletHHTCost.{u,v,w} d = 1 := by
  unfold ordinaryPhysicalSingletHHTCost
  have hOne : (1 : ℝ) ∈ {r : ℝ | ordinaryPhysicalSingletHHTAchievableRate.{u,v,w} d r} :=
    ordinaryPhysicalSingletHHTAchievableRate_one d hd
  have hLower : ∀ r ∈ {r : ℝ | ordinaryPhysicalSingletHHTAchievableRate.{u,v,w} d r}, (1 : ℝ) ≤ r :=
    fun r hr => ordinaryPhysicalSingletHHTAchievableRate_lower d hd r hr
  exact le_antisymm (csInf_le ⟨1, hLower⟩ hOne) (le_csInf ⟨1, hOne⟩ hLower)

end QuantumProver.WernerEndpoint
