import QuantumProver.QuantumChannels.PhysicalProtocolData
import QuantumProver.QuantumChannels.PhysicalUniverseTransport
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCost
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalBornTransport
import QuantumProver.InformationTheory.ElegantJointMeasurement.CommonPhysicalQuantumOutput
import QuantumProver.InformationTheory.ElegantJointMeasurement.PhysicalEJMReport
import QuantumProver.InformationTheory.ElegantJointMeasurement.PhysicalFreePreparationSerialization

universe u v w t

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Matrix Set Filter Function
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertRecordCoding
open QuantumProver.ElegantJointMeasurement.NormalPhysicalOperationalBridge QuantumProver.ElegantJointMeasurement.PhysicalTranscriptCoding
open QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM QuantumProver.ElegantJointMeasurement.NormalCost
open QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel QuantumProver.ElegantJointMeasurement.PreparedReports QuantumProver.ElegantJointMeasurement.Teleportation
open QuantumProver.ElegantJointMeasurement.GeneralResource QuantumProver.ElegantJointMeasurement.ClosureJoin.RecordTransport
open scoped BigOperators Topology ComplexConjugate ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.PhysicalCost
namespace PhysicalProtocol

variable {m n : ℕ} [NeZero m] [NeZero n]

def represented_physicalBornMeasure (P : PhysicalProtocol.{u,v,w} m n)
    (X : JointInputMatrix m n) (hX : X.PosSemidef) : Measure (PhysicalTranscript P.Outcomes) :=
  physicalBornMeasure P.Outcomes P.domains P.aliceSections P.bobSections
    P.aliceOutputSections P.bobOutputSections P.aliceWiring P.bobWiring
    P.aliceInstrument P.bobInstrument P.chargedAlice P.chargedBob X hX

theorem represented_physicalBornMeasure_map (P : PhysicalProtocol.{u,v,w} m n)
    (X : JointInputMatrix m n) (hX : X.PosSemidef) :
    (P.represented_physicalBornMeasure X hX).map (encodePhysicalTranscript P.Outcomes) =
      P.represented.represented_physicalBornMeasure X hX :=
  physicalBornMeasure_map P.Outcomes P.domains P.aliceSections P.bobSections
    P.aliceOutputSections P.bobOutputSections P.aliceWiring P.bobWiring
    P.aliceInstrument P.bobInstrument P.chargedAlice P.chargedBob X hX

theorem represented_physicalReport_nullMeasurable (P : PhysicalProtocol.{u,v,w} m n)
    (X : JointInputMatrix m n) (hX : X.PosSemidef)
    (J : PhysicalTranscript P.Outcomes → Fin 4)
    (hJ : NullMeasurable J (P.represented_physicalBornMeasure X hX)) :
    NullMeasurable (liftPhysicalReport P.Outcomes J) (P.represented.represented_physicalBornMeasure X hX) :=
  physicalReport_nullMeasurable P.Outcomes P.domains P.aliceSections P.bobSections
    P.aliceOutputSections P.bobOutputSections P.aliceWiring P.bobWiring
    P.aliceInstrument P.bobInstrument P.chargedAlice P.chargedBob X hX J hJ

section Resource
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def physicalResourceOutput (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : PhysicalProtocol.{u,v,w} m n) (J : PhysicalTranscript P.Outcomes → Fin 4)
    (Ψ : Matrix κ κ ℂ) (σ : Matrix SystemIndex SystemIndex ℂ) (hσ : σ.PosSemidef) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  physicalSharedReportState P.Outcomes
    (P.represented_physicalBornMeasure (matrixCodeMatrix ea eb Ψ * σ * (matrixCodeMatrix ea eb Ψ)ᴴ)
      (hσ.mul_mul_conjTranspose_same (matrixCodeMatrix ea eb Ψ))) J

theorem physicalResourceOutput_eq_normal (ea : (Fin 2 × κ) ≃ Fin m)
    (eb : (Fin 2 × κ) ≃ Fin n) (P : PhysicalProtocol.{u,v,w} m n)
    (J : PhysicalTranscript P.Outcomes → Fin 4) (Ψ : Matrix κ κ ℂ)
    (σ : Matrix SystemIndex SystemIndex ℂ) (hσ : σ.PosSemidef) :
    P.physicalResourceOutput ea eb J Ψ σ hσ =
      physicalResourceDensityOutput ea eb P.represented (liftPhysicalReport P.Outcomes J) Ψ σ hσ := by
  have hm := commonSharedReportState_map_encode P.Outcomes
    (P.represented_physicalBornMeasure (matrixCodeMatrix ea eb Ψ * σ * (matrixCodeMatrix ea eb Ψ)ᴴ)
      (hσ.mul_mul_conjTranspose_same (matrixCodeMatrix ea eb Ψ))) J
  rw [P.represented_physicalBornMeasure_map] at hm
  exact hm.symm

end Resource
end PhysicalProtocol

def ImplementsInPhysicalExact {κ : Type} [Fintype κ] [DecidableEq κ]
    (Ψ : Matrix κ κ ℂ) : Prop :=
  ∃ (m n : ℕ) (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (hm : NeZero m) (hn : NeZero n),
    letI : NeZero m := hm
    letI : NeZero n := hn
    ∃ (P : PhysicalProtocol.{u,v,w} m n) (J : PhysicalTranscript P.Outcomes → Fin 4),
      NullMeasurable J (P.represented_physicalBornMeasure
        (preparedReference (matrixCodeMatrix ea eb Ψ))
        (preparedReference_positive (matrixCodeMatrix ea eb Ψ))) ∧
      ∀ (σ : Matrix SystemIndex SystemIndex ℂ) (hσ : σ.PosSemidef), σ.trace = 1 →
        P.physicalResourceOutput ea eb J Ψ σ hσ = physicalClassicalChannel σ

def ImplementsInPhysicalOperational {κ : Type} [Fintype κ] [DecidableEq κ]
    (Ψ : Matrix κ κ ℂ) : Prop :=
  ∃ (m n : ℕ) (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (hm : NeZero m) (hn : NeZero n),
    letI : NeZero m := hm
    letI : NeZero n := hn
    ∃ (P : ℕ → PhysicalProtocol.{u,v,w} m n)
      (J : (k : ℕ) → PhysicalTranscript (P k).Outcomes → Fin 4),
      (∀ k, NullMeasurable (J k) ((P k).represented_physicalBornMeasure
        (preparedReference (matrixCodeMatrix ea eb Ψ))
        (preparedReference_positive (matrixCodeMatrix ea eb Ψ)))) ∧
      ∀ (σ : Matrix SystemIndex SystemIndex ℂ) (hσ : σ.PosSemidef), σ.trace = 1 →
        Tendsto (fun k => (P k).physicalResourceOutput ea eb (J k) Ψ σ hσ)
          atTop (𝓝 (physicalClassicalChannel σ))

theorem physical_exact_implies_operational {κ : Type} [Fintype κ] [DecidableEq κ]
    (Ψ : Matrix κ κ ℂ) (h : ImplementsInPhysicalExact.{u,v,w} Ψ) :
    ImplementsInPhysicalOperational.{u,v,w} Ψ := by
  rcases h with ⟨m,n,ea,eb,hm,hn,P,J,hJ,hC⟩
  letI : NeZero m := hm
  letI : NeZero n := hn
  refine ⟨m,n,ea,eb,hm,hn,(fun _ => P),(fun _ => J),(fun _ => hJ),?_⟩
  intro σ hσ ht
  simpa only [hC σ hσ ht] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => physicalClassicalChannel σ) atTop
      (𝓝 (physicalClassicalChannel σ)))

theorem physical_operational_implies_physicalNormal {κ : Type} [Fintype κ] [DecidableEq κ]
    (Ψ : Matrix κ κ ℂ) (h : ImplementsInPhysicalOperational.{u,v,w} Ψ) :
    ImplementsInPhysicalNormalOperational.{u} Ψ := by
  rcases h with ⟨m,n,ea,eb,hm,hn,P,J,hJ,hC⟩
  letI : NeZero m := hm
  letI : NeZero n := hn
  let R : ℕ → Type u := fun k => CommonRecord (P k).Outcomes
  letI : ∀ k, MeasurableSpace (R k) := fun k => inferInstance
  letI : ∀ k, StandardBorelSpace (R k) := fun k => inferInstance
  refine ⟨m,n,ea,eb,hm,hn,R,(fun k => inferInstance),(fun k => inferInstance),
    (fun k => (P k).represented),(fun k => liftPhysicalReport (P k).Outcomes (J k)),?_,?_⟩
  · intro k
    exact (P k).represented_physicalReport_nullMeasurable
      (preparedReference (matrixCodeMatrix ea eb Ψ))
      (preparedReference_positive (matrixCodeMatrix ea eb Ψ)) (J k) (hJ k)
  · intro σ hσ ht
    have he (k : ℕ) := (P k).physicalResourceOutput_eq_normal ea eb (J k) Ψ σ hσ
    simpa only [← he] using hC σ hσ ht

theorem physical_operational_resource_entropy_ge_one
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (Ψ : Matrix κ κ ℂ) (hΨ : (Ψ * Ψᴴ).trace = 1)
    (h : ImplementsInPhysicalOperational.{u,v,w} Ψ) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) :=
  physicalNormal_operational_implementation_entropy_ge_one Ψ hΨ
    (physical_operational_implies_physicalNormal Ψ h)

theorem physical_exact_resource_entropy_ge_one
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (Ψ : Matrix κ κ ℂ) (hΨ : (Ψ * Ψᴴ).trace = 1)
    (h : ImplementsInPhysicalExact.{u,v,w} Ψ) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) :=
  physical_operational_resource_entropy_ge_one Ψ hΨ
    (physical_exact_implies_operational Ψ h)

def physicalExactCostSet : Set ℝ :=
  {c | ∃ (r : ℕ) (_hr : 0 < r) (Ψ : Matrix (Fin r) (Fin r) ℂ),
    (Ψ * Ψᴴ).trace = 1 ∧ ImplementsInPhysicalExact.{u,v,w} Ψ ∧
      QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) = c}

def physicalOperationalCostSet : Set ℝ :=
  {c | ∃ (r : ℕ) (_hr : 0 < r) (Ψ : Matrix (Fin r) (Fin r) ℂ),
    (Ψ * Ψᴴ).trace = 1 ∧ ImplementsInPhysicalOperational.{u,v,w} Ψ ∧
      QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) = c}

theorem physicalExactCostSet_subset_operational :
    physicalExactCostSet.{u,v,w} ⊆ physicalOperationalCostSet.{u,v,w} := by
  rintro c ⟨r,hr,Ψ,hΨ,hI,he⟩
  exact ⟨r,hr,Ψ,hΨ,physical_exact_implies_operational Ψ hI,he⟩

theorem physicalOperationalCostSet_lower {c : ℝ}
    (hc : c ∈ physicalOperationalCostSet.{u,v,w}) : 1 ≤ c := by
  rcases hc with ⟨r,hr,Ψ,hΨ,hI,he⟩
  rw [← he]
  exact physical_operational_resource_entropy_ge_one Ψ hΨ hI

theorem physicalExactCostSet_lower {c : ℝ}
    (hc : c ∈ physicalExactCostSet.{u,v,w}) : 1 ≤ c :=
  physicalOperationalCostSet_lower (physicalExactCostSet_subset_operational hc)

end QuantumProver.ElegantJointMeasurement.PhysicalCost

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Matrix Set Filter Function TopologicalSpace Preorder
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertRecordCoding
open QuantumProver.ElegantJointMeasurement.PhysicalEJMReport QuantumProver.ElegantJointMeasurement.HilbertFiniteEJMProtocol QuantumProver.ElegantJointMeasurement.NormalCost
open QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM QuantumProver.ElegantJointMeasurement.PreparedReports QuantumProver.ElegantJointMeasurement.HilbertSquareCostModel
open QuantumProver.ElegantJointMeasurement.HilbertFiniteCostModel
open QuantumProver.ElegantJointMeasurement.GeneralResource QuantumProver.ElegantJointMeasurement.ClosureJoin.RecordTransport
open QuantumProver.ElegantJointMeasurement.Teleportation QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.MatrixPhysicalUniverseTransport QuantumProver.MatrixNormalFreePreparationChronology
open QuantumProver.WernerEndpoint.MatrixCommonPhysicalRealization
open scoped BigOperators Topology ComplexConjugate ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.PhysicalCost

def oneEbitPhysicalProtocol : PhysicalProtocol.{u,v,w} 4 4 :=
  (finitePhysicalProtocol.{u} oneEbitProtocol).ulift.{v,w}

theorem oneEbitPhysicalProtocol_physicalBornMeasure
    (ρ : Matrix SystemIndex SystemIndex ℂ) (hρ : ρ.PosSemidef) :
    oneEbitPhysicalProtocol.{u,v,w}.represented_physicalBornMeasure
      (oneEbitChargedInput ρ) (oneEbitChargedInput_posSemidef ρ hρ) =
        physicalOneEbitBornMeasure.{u} ρ hρ := by
  change protocolBornMeasure ((finitePhysicalProtocol.{u} oneEbitProtocol).ulift.{v,w})
    (oneEbitChargedInput ρ) (oneEbitChargedInput_posSemidef ρ hρ) = _
  rw [protocolBornMeasure_ulift]
  rfl

theorem oneEbitPhysicalProtocol_physicalResourceOutput
    (ρ : Matrix SystemIndex SystemIndex ℂ) (hρ : ρ.PosSemidef) :
    oneEbitPhysicalProtocol.{u,v,w}.physicalResourceOutput
      alicePhysicalEquiv bobPhysicalEquiv physicalOneEbitReport resource ρ hρ =
        physicalClassicalChannel ρ := by
  unfold PhysicalProtocol.physicalResourceOutput
  change physicalSharedReportState _
    (oneEbitPhysicalProtocol.{u,v,w}.represented_physicalBornMeasure
      (oneEbitChargedInput ρ) (oneEbitChargedInput_posSemidef ρ hρ)) physicalOneEbitReport = _
  rw [oneEbitPhysicalProtocol_physicalBornMeasure]
  exact oneEbit_physicalSharedReport_output ρ hρ

theorem oneEbit_implements_in_physical_exact :
    ImplementsInPhysicalExact.{u,v,w} resource := by
  refine ⟨4,4,alicePhysicalEquiv,bobPhysicalEquiv,inferInstance,inferInstance,
    oneEbitPhysicalProtocol,physicalOneEbitReport,?_,?_⟩
  · exact measurable_physicalOneEbitReport.nullMeasurable
  · intro σ hσ ht
    exact oneEbitPhysicalProtocol_physicalResourceOutput σ hσ

theorem one_mem_physicalExactCostSet : (1 : ℝ) ∈ physicalExactCostSet.{u,v,w} :=
  ⟨2,by decide,resource,physicalOneEbit_resource_normalized,
    oneEbit_implements_in_physical_exact,physicalOneEbit_resource_entropy⟩

theorem one_mem_physicalOperationalCostSet : (1 : ℝ) ∈ physicalOperationalCostSet.{u,v,w} :=
  physicalExactCostSet_subset_operational one_mem_physicalExactCostSet

theorem physical_exact_cost_eq_one : sInf physicalExactCostSet.{u,v,w} = 1 := by
  apply le_antisymm
  · exact csInf_le ⟨1,fun _ hc => physicalExactCostSet_lower hc⟩ one_mem_physicalExactCostSet
  · exact le_csInf ⟨1,one_mem_physicalExactCostSet⟩ fun _ hc => physicalExactCostSet_lower hc

theorem physical_operational_cost_eq_one : sInf physicalOperationalCostSet.{u,v,w} = 1 := by
  apply le_antisymm
  · exact csInf_le ⟨1,fun _ hc => physicalOperationalCostSet_lower hc⟩
      one_mem_physicalOperationalCostSet
  · exact le_csInf ⟨1,one_mem_physicalOperationalCostSet⟩
      fun _ hc => physicalOperationalCostSet_lower hc

def physicalPaddedExactCostSet : Set ℝ :=
  {c | ∃ (rA rB : ℕ) (_hrA : 0 < rA) (_hrB : 0 < rB)
      (Ψ : Matrix (Fin rA) (Fin rB) ℂ),
    (Ψ * Ψᴴ).trace = 1 ∧
      ImplementsInPhysicalExact.{u,v,w} (QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.coefficient Ψ) ∧
      QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) = c}

def physicalPaddedOperationalCostSet : Set ℝ :=
  {c | ∃ (rA rB : ℕ) (_hrA : 0 < rA) (_hrB : 0 < rB)
      (Ψ : Matrix (Fin rA) (Fin rB) ℂ),
    (Ψ * Ψᴴ).trace = 1 ∧
      ImplementsInPhysicalOperational.{u,v,w} (QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.coefficient Ψ) ∧
      QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) = c}

theorem rectangular_resource_actual_padding {κ η : Type}
    [Fintype κ] [DecidableEq κ] [Fintype η] [DecidableEq η]
    (Ψ : Matrix κ η ℂ) :
    QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.coefficient Ψ =
      QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.aliceEmbedding (κ := κ) (η := η) * Ψ *
        (QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.bobEmbedding (κ := κ) (η := η))ᵀ ∧
    (QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.aliceEmbedding (κ := κ) (η := η))ᴴ *
        QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.aliceEmbedding (κ := κ) (η := η) = 1 ∧
    (QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.bobEmbedding (κ := κ) (η := η))ᴴ *
        QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.bobEmbedding (κ := κ) (η := η) = 1 ∧
    QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits
      (QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.coefficient Ψ *
        (QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.coefficient Ψ)ᴴ) =
      QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) :=
  ⟨QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.coefficient_eq_local_embeddings Ψ,
    QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.aliceEmbedding_gram (κ := κ) (η := η),
    QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.bobEmbedding_gram (κ := κ) (η := η),
    QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.coefficient_entropy Ψ⟩

theorem physicalPaddedExactCostSet_subset_operational :
    physicalPaddedExactCostSet.{u,v,w} ⊆ physicalPaddedOperationalCostSet.{u,v,w} := by
  rintro c ⟨rA,rB,hrA,hrB,Ψ,hΨ,hI,he⟩
  exact ⟨rA,rB,hrA,hrB,Ψ,hΨ,physical_exact_implies_operational _ hI,he⟩

theorem physicalPaddedOperationalCostSet_lower {c : ℝ}
    (hc : c ∈ physicalPaddedOperationalCostSet.{u,v,w}) : 1 ≤ c := by
  rcases hc with ⟨rA,rB,hrA,hrB,Ψ,hΨ,hI,he⟩
  have h := physical_operational_resource_entropy_ge_one
    (QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.coefficient Ψ)
    (QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.normalized_coefficient Ψ hΨ) hI
  simpa only [QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding.coefficient_entropy, he] using h

def physicalAllFiniteExactCostSet : Set ℝ :=
  physicalExactCostSet.{u,v,w} ∪ physicalPaddedExactCostSet.{u,v,w}

def physicalAllFiniteOperationalCostSet : Set ℝ :=
  physicalOperationalCostSet.{u,v,w} ∪ physicalPaddedOperationalCostSet.{u,v,w}

theorem physicalAllFiniteExactCostSet_subset_operational :
    physicalAllFiniteExactCostSet.{u,v,w} ⊆ physicalAllFiniteOperationalCostSet.{u,v,w} :=
  Set.union_subset_union physicalExactCostSet_subset_operational
    physicalPaddedExactCostSet_subset_operational

theorem physicalAllFiniteOperationalCostSet_lower {c : ℝ}
    (hc : c ∈ physicalAllFiniteOperationalCostSet.{u,v,w}) : 1 ≤ c := by
  rcases hc with hc | hc
  · exact physicalOperationalCostSet_lower hc
  · exact physicalPaddedOperationalCostSet_lower hc

theorem physicalAllFiniteExactCostSet_lower {c : ℝ}
    (hc : c ∈ physicalAllFiniteExactCostSet.{u,v,w}) : 1 ≤ c :=
  physicalAllFiniteOperationalCostSet_lower
    (physicalAllFiniteExactCostSet_subset_operational hc)

theorem one_mem_physicalAllFiniteExactCostSet :
    (1 : ℝ) ∈ physicalAllFiniteExactCostSet.{u,v,w} := Or.inl one_mem_physicalExactCostSet

theorem one_mem_physicalAllFiniteOperationalCostSet :
    (1 : ℝ) ∈ physicalAllFiniteOperationalCostSet.{u,v,w} :=
  physicalAllFiniteExactCostSet_subset_operational one_mem_physicalAllFiniteExactCostSet

theorem physical_all_finite_exact_cost_eq_one :
    sInf physicalAllFiniteExactCostSet.{u,v,w} = 1 := by
  apply le_antisymm
  · exact csInf_le ⟨1,fun _ hc => physicalAllFiniteExactCostSet_lower hc⟩
      one_mem_physicalAllFiniteExactCostSet
  · exact le_csInf ⟨1,one_mem_physicalAllFiniteExactCostSet⟩
      fun _ hc => physicalAllFiniteExactCostSet_lower hc

theorem physical_all_finite_operational_cost_eq_one :
    sInf physicalAllFiniteOperationalCostSet.{u,v,w} = 1 := by
  apply le_antisymm
  · exact csInf_le ⟨1,fun _ hc => physicalAllFiniteOperationalCostSet_lower hc⟩
      one_mem_physicalAllFiniteOperationalCostSet
  · exact le_csInf ⟨1,one_mem_physicalAllFiniteOperationalCostSet⟩
      fun _ hc => physicalAllFiniteOperationalCostSet_lower hc

section ActualMixedFreePreparation
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
  {a b : ℕ} [NeZero a] [NeZero b]
  {FA FB : Type t}
  [NormedAddCommGroup FA] [InnerProductSpace ℂ FA] [CompleteSpace FA] [SeparableSpace FA]
  [NormedAddCommGroup FB] [InnerProductSpace ℂ FB] [CompleteSpace FB] [SeparableSpace FB]

def mixedPreparationPhysicalProtocol (P : MatrixProcess a b R)
    (τA : Nuclear FA) (τB : Nuclear FB)
    (hA : (QuantumProver.NuclearOperator.toOperator τA).IsPositive)
    (hB : (QuantumProver.NuclearOperator.toOperator τB).IsPositive)
    (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
    (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1) : PhysicalProtocol.{u,v,w} a b :=
  (commonPhysicalProtocol (insertMixedMatrixProcess P τA τB hA hB hAT hBT)).ulift.{v,w}

theorem mixedPreparationPhysicalProtocol_same_charged_maps (P : MatrixProcess a b R)
    (τA : Nuclear FA) (τB : Nuclear FB)
    (hA : (QuantumProver.NuclearOperator.toOperator τA).IsPositive)
    (hB : (QuantumProver.NuclearOperator.toOperator τB).IsPositive)
    (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
    (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1) :
    (mixedPreparationPhysicalProtocol P τA τB hA hB hAT hBT : PhysicalProtocol.{u,v,w} a b).represented.initialAlice =
      P.initialAlice ∧
    (mixedPreparationPhysicalProtocol P τA τB hA hB hAT hBT : PhysicalProtocol.{u,v,w} a b).represented.initialBob =
      P.initialBob := by
  simp only [mixedPreparationPhysicalProtocol, PhysicalProtocol.matrix_ulift,
    commonPhysicalProtocol_matrix, realization_initialAlice, realization_initialBob,
    insertMixedMatrixProcess_initialAlice, insertMixedMatrixProcess_initialBob, and_self]

end ActualMixedFreePreparation

section CompletedPreparedReports

open QuantumProver.ElegantJointMeasurement.PhysicalFreePreparationSerialization

variable {κ : Type} [Fintype κ] [DecidableEq κ]
  {m n : ℕ} [NeZero m] [NeZero n]
  {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
  {FA FB : Type t}
  [NormedAddCommGroup FA] [InnerProductSpace ℂ FA] [CompleteSpace FA] [SeparableSpace FA]
  [NormedAddCommGroup FB] [InnerProductSpace ℂ FB] [CompleteSpace FB] [SeparableSpace FB]

def mixedPreparedDensityOutput (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixProcess m n R) (τA : Nuclear FA) (τB : Nuclear FB)
    (hA : (QuantumProver.NuclearOperator.toOperator τA).IsPositive)
    (hB : (QuantumProver.NuclearOperator.toOperator τB).IsPositive)
    (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
    (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1)
    (J : Transcript R → Fin 4) (Ψ : Matrix κ κ ℂ)
    (σ : Matrix SystemIndex SystemIndex ℂ) (hσ : σ.PosSemidef) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  ∑ j : Fin 4,
    (((preparedBornMeasure P τA τB hA hB hAT hBT
      (matrixCodeMatrix ea eb Ψ * σ * (matrixCodeMatrix ea eb Ψ)ᴴ)
      (hσ.mul_mul_conjTranspose_same (matrixCodeMatrix ea eb Ψ))
      {ω | J ω = j}).toReal : ℝ) : ℂ) • Tomography.sharedProjector j

theorem mixedPreparedReport_nullMeasurable_density
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixProcess m n R) (τA : Nuclear FA) (τB : Nuclear FB)
    (hA : (QuantumProver.NuclearOperator.toOperator τA).IsPositive)
    (hB : (QuantumProver.NuclearOperator.toOperator τB).IsPositive)
    (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
    (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1)
    (J : Transcript R → Fin 4) (Ψ : Matrix κ κ ℂ)
    (hJ : NullMeasurable J (preparedBornMeasure P τA τB hA hB hAT hBT
      (preparedReference (matrixCodeMatrix ea eb Ψ))
      (preparedReference_positive (matrixCodeMatrix ea eb Ψ))))
    (σ : Matrix SystemIndex SystemIndex ℂ) (hσ : σ.PosSemidef) (ht : σ.trace = 1) :
    NullMeasurable J (preparedBornMeasure P τA τB hA hB hAT hBT
      (matrixCodeMatrix ea eb Ψ * σ * (matrixCodeMatrix ea eb Ψ)ᴴ)
      (hσ.mul_mul_conjTranspose_same (matrixCodeMatrix ea eb Ψ))) := by
  let C := matrixCodeMatrix ea eb Ψ
  let S := serialized P τA τB hA hB hAT hBT
  have hd := prepared_density_cap C σ hσ ht
  have ha := bornMeasure_absolutelyContinuous_of_input_domination
    S.represented_physicalCylinderPOVM (Fintype.card SystemIndex : NNReal)
    (preparedReference C) (C * σ * Cᴴ) (preparedReference_positive C)
    (hσ.mul_mul_conjTranspose_same C) hd
  have hm := ha.map (measurable_dropPreparationTranscript P)
  intro s hs
  exact (hJ hs).mono_ac hm

theorem mixedPreparationPhysicalProtocol_prepared_completion
    (P : MatrixProcess m n R) (τA : Nuclear FA) (τB : Nuclear FB)
    (hA : (QuantumProver.NuclearOperator.toOperator τA).IsPositive)
    (hB : (QuantumProver.NuclearOperator.toOperator τB).IsPositive)
    (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
    (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1)
    (J : Transcript R → Fin 4) (X : JointInputMatrix m n) (hX : X.PosSemidef)
    (hJ : NullMeasurable J (preparedBornMeasure P τA τB hA hB hAT hBT X hX)) :
    NullMeasurable (liftedPreparedReport P J)
      ((mixedPreparationPhysicalProtocol P τA τB hA hB hAT hBT :
        PhysicalProtocol.{u,v,w} m n).represented_physicalBornMeasure X hX) := by
  change NullMeasurable (liftedPreparedReport P J)
    (protocolBornMeasure ((commonPhysicalProtocol (serialized P τA τB hA hB hAT hBT)).ulift.{v,w}) X hX)
  rw [protocolBornMeasure_ulift]
  change NullMeasurable (liftedPreparedReport P J)
    (QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology.constantPhysicalBornMeasure
      (serialized P τA τB hA hB hAT hBT) X hX)
  rw [QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology.constantPhysicalBornMeasure_eq_physical]
  exact nullMeasurable_liftedPreparedReport P τA τB hA hB hAT hBT J X hX hJ

theorem mixedPreparedDensityOutput_eq_physical
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : MatrixProcess m n R) (τA : Nuclear FA) (τB : Nuclear FB)
    (hA : (QuantumProver.NuclearOperator.toOperator τA).IsPositive)
    (hB : (QuantumProver.NuclearOperator.toOperator τB).IsPositive)
    (hAT : QuantumProver.HilbertNuclearTrace.trace τA = 1)
    (hBT : QuantumProver.HilbertNuclearTrace.trace τB = 1)
    (J : Transcript R → Fin 4) (Ψ : Matrix κ κ ℂ)
    (hJ : NullMeasurable J (preparedBornMeasure P τA τB hA hB hAT hBT
      (preparedReference (matrixCodeMatrix ea eb Ψ))
      (preparedReference_positive (matrixCodeMatrix ea eb Ψ))))
    (σ : Matrix SystemIndex SystemIndex ℂ) (hσ : σ.PosSemidef) (ht : σ.trace = 1) :
    (mixedPreparationPhysicalProtocol P τA τB hA hB hAT hBT : PhysicalProtocol.{u,v,w} m n).physicalResourceOutput
        ea eb (liftedPreparedReport P J) Ψ σ hσ =
      mixedPreparedDensityOutput ea eb P τA τB hA hB hAT hBT J Ψ σ hσ := by
  let X := matrixCodeMatrix ea eb Ψ * σ * (matrixCodeMatrix ea eb Ψ)ᴴ
  let hX := hσ.mul_mul_conjTranspose_same (matrixCodeMatrix ea eb Ψ)
  have hJσ := mixedPreparedReport_nullMeasurable_density ea eb P τA τB hA hB hAT hBT J Ψ hJ σ hσ ht
  change physicalSharedReportState _
    (protocolBornMeasure ((commonPhysicalProtocol (serialized P τA τB hA hB hAT hBT)).ulift.{v,w}) X hX)
    (liftedPreparedReport P J) = _
  rw [protocolBornMeasure_ulift]
  unfold physicalSharedReportState mixedPreparedDensityOutput
  apply Finset.sum_congr rfl
  intro j hj
  have he := physical_completed_report_probability P τA τB hA hB hAT hBT J j X hX hJσ
  exact congrArg (fun z : ENNReal => (z.toReal : ℂ) • Tomography.sharedProjector j) he

end CompletedPreparedReports

section MixedPreparationOperationalCost

open QuantumProver.ElegantJointMeasurement.PhysicalFreePreparationSerialization

variable {κ : Type} [Fintype κ] [DecidableEq κ]
  {m n : ℕ} [NeZero m] [NeZero n]
  {R : ℕ → Type u} [∀ k, MeasurableSpace (R k)] [∀ k, StandardBorelSpace (R k)]
  {FA FB : ℕ → Type t}
  [∀ k, NormedAddCommGroup (FA k)] [∀ k, InnerProductSpace ℂ (FA k)]
  [∀ k, CompleteSpace (FA k)] [∀ k, SeparableSpace (FA k)]
  [∀ k, NormedAddCommGroup (FB k)] [∀ k, InnerProductSpace ℂ (FB k)]
  [∀ k, CompleteSpace (FB k)] [∀ k, SeparableSpace (FB k)]

theorem mixed_free_preparation_operational_entropy_ge_one
    (Ψ : Matrix κ κ ℂ) (hΨ : (Ψ * Ψᴴ).trace = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (P : (k : ℕ) → MatrixProcess m n (R k))
    (τA : (k : ℕ) → Nuclear (FA k)) (τB : (k : ℕ) → Nuclear (FB k))
    (hA : ∀ k, (QuantumProver.NuclearOperator.toOperator (τA k)).IsPositive)
    (hB : ∀ k, (QuantumProver.NuclearOperator.toOperator (τB k)).IsPositive)
    (hAT : ∀ k, QuantumProver.HilbertNuclearTrace.trace (τA k) = 1)
    (hBT : ∀ k, QuantumProver.HilbertNuclearTrace.trace (τB k) = 1)
    (J : (k : ℕ) → Transcript (R k) → Fin 4)
    (hJ : ∀ k, NullMeasurable (J k) (preparedBornMeasure (P k) (τA k) (τB k)
      (hA k) (hB k) (hAT k) (hBT k) (preparedReference (matrixCodeMatrix ea eb Ψ))
      (preparedReference_positive (matrixCodeMatrix ea eb Ψ))))
    (hC : ∀ (σ : Matrix SystemIndex SystemIndex ℂ) (hσ : σ.PosSemidef), σ.trace = 1 →
      Tendsto (fun k => mixedPreparedDensityOutput ea eb (P k) (τA k) (τB k)
        (hA k) (hB k) (hAT k) (hBT k) (J k) Ψ σ hσ)
        atTop (𝓝 (physicalClassicalChannel σ))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  let PP (k : ℕ) : PhysicalProtocol.{u,0,0} m n :=
    mixedPreparationPhysicalProtocol (P k) (τA k) (τB k) (hA k) (hB k) (hAT k) (hBT k)
  apply physical_operational_resource_entropy_ge_one Ψ hΨ
  refine ⟨m,n,ea,eb,inferInstance,inferInstance,PP,
    (fun k => liftedPreparedReport (P k) (J k)),?_,?_⟩
  · intro k
    exact mixedPreparationPhysicalProtocol_prepared_completion (P k) (τA k) (τB k)
      (hA k) (hB k) (hAT k) (hBT k) (J k) _ _ (hJ k)
  · intro σ hσ ht
    have he (k : ℕ) :
        (PP k).physicalResourceOutput ea eb (liftedPreparedReport (P k) (J k)) Ψ σ hσ =
          mixedPreparedDensityOutput ea eb (P k) (τA k) (τB k)
            (hA k) (hB k) (hAT k) (hBT k) (J k) Ψ σ hσ :=
      mixedPreparedDensityOutput_eq_physical ea eb (P k) (τA k) (τB k)
        (hA k) (hB k) (hAT k) (hBT k) (J k) Ψ (hJ k) σ hσ ht
    simpa only [he] using hC σ hσ ht

end MixedPreparationOperationalCost

theorem physical_entanglement_cost_eq_one :
    sInf physicalAllFiniteExactCostSet.{u,v,w} = 1 ∧
      sInf physicalAllFiniteOperationalCostSet.{u,v,w} = 1 :=
  ⟨physical_all_finite_exact_cost_eq_one, physical_all_finite_operational_cost_eq_one⟩

end QuantumProver.ElegantJointMeasurement.PhysicalCost
