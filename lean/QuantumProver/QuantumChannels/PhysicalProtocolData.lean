import QuantumProver.InformationTheory.ElegantJointMeasurement.Teleportation
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalAdmission
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalPhysicalTerminalAdmission
import QuantumProver.InformationTheory.ElegantJointMeasurement.PhysicalTranscriptCoding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open MeasureTheory Matrix Set Filter Function InnerProductSpace
open QuantumProver.ElegantJointMeasurement.NormalPhysicalAdmission QuantumProver.ElegantJointMeasurement.MeasurableHilbertField
open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertRecordCoding QuantumProver.ElegantJointMeasurement.PhysicalTranscriptCoding
open QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM
open scoped BigOperators Topology ComplexConjugate ComplexOrder

namespace QuantumProver.ElegantJointMeasurement.PhysicalCost

structure PhysicalOutcome where
  carrier : Type u
  measurable : MeasurableSpace carrier
  standard : letI := measurable; StandardBorelSpace carrier

instance : CoeSort PhysicalOutcome.{u} (Type u) := ⟨PhysicalOutcome.carrier⟩
instance (S : PhysicalOutcome.{u}) : MeasurableSpace S := S.measurable
instance (S : PhysicalOutcome.{u}) : StandardBorelSpace S := S.standard

structure PhysicalHilbert where
  carrier : Type v
  normed : NormedAddCommGroup carrier
  innerProduct : letI := normed; InnerProductSpace ℂ carrier
  complete : letI := normed; CompleteSpace carrier

instance : CoeSort PhysicalHilbert.{v} (Type v) := ⟨PhysicalHilbert.carrier⟩
instance (E : PhysicalHilbert.{v}) : NormedAddCommGroup E := E.normed
instance (E : PhysicalHilbert.{v}) : InnerProductSpace ℂ E := E.innerProduct
instance (E : PhysicalHilbert.{v}) : CompleteSpace E := E.complete

structure PhysicalProtocol (a b : ℕ) where
  outcome : ℕ → PhysicalOutcome.{u}
  domains : PhysicalDomains (fun n => outcome n)
  alice : (n : ℕ) → domains.admissible n → PhysicalHilbert.{v}
  bob : (n : ℕ) → domains.admissible n → PhysicalHilbert.{v}
  aliceSections : (n : ℕ) → FundamentalFamily (fun h => alice n h)
  bobSections : (n : ℕ) → FundamentalFamily (fun h => bob n h)
  aliceOutput : (n : ℕ) → domains.actingDomain n true × outcome n → PhysicalHilbert.{w}
  bobOutput : (n : ℕ) → domains.actingDomain n false × outcome n → PhysicalHilbert.{w}
  aliceOutputSections : (n : ℕ) → FundamentalFamily (fun z => aliceOutput n z)
  bobOutputSections : (n : ℕ) → FundamentalFamily (fun z => bobOutput n z)
  aliceWiring : PhysicalMemoryWiring (fun n => outcome n) domains true
    aliceSections aliceOutputSections
  bobWiring : PhysicalMemoryWiring (fun n => outcome n) domains false
    bobSections bobOutputSections
  aliceInstrument : PhysicalLocalFamily (fun n => outcome n) domains true
    aliceSections aliceOutputSections
  bobInstrument : PhysicalLocalFamily (fun n => outcome n) domains false
    bobSections bobOutputSections
  chargedAlice : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] alice 0 domains.initialHistory
  chargedBob : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] bob 0 domains.initialHistory

namespace PhysicalProtocol

variable {a b : ℕ}

abbrev Outcomes (P : PhysicalProtocol.{u,v,w} a b) : ℕ → Type u := fun n => P.outcome n

def represented (P : PhysicalProtocol.{u,v,w} a b) : MatrixProcess a b (CommonRecord P.Outcomes) :=
  ofPhysicalFamilies P.Outcomes P.domains P.aliceSections P.bobSections
    P.aliceOutputSections P.bobOutputSections P.aliceWiring P.bobWiring
    P.aliceInstrument P.bobInstrument P.chargedAlice P.chargedBob

theorem matrix_initialAlice (P : PhysicalProtocol.{u,v,w} a b) :
    P.represented.initialAlice =
      ((P.aliceSections 0).embedding P.domains.initialHistory).comp P.chargedAlice := rfl

theorem matrix_initialBob (P : PhysicalProtocol.{u,v,w} a b) :
    P.represented.initialBob =
      ((P.bobSections 0).embedding P.domains.initialHistory).comp P.chargedBob := rfl

theorem matrix_physicalParty (P : PhysicalProtocol.{u,v,w} a b)
    (n : ℕ) (h : P.domains.admissible n) :
    P.represented.aliceTurn n (encodeHistory P.Outcomes n h.val) = P.domains.party n h := by
  exact ofPhysicalFamilies_party P.Outcomes P.domains P.aliceSections P.bobSections
    P.aliceOutputSections P.bobOutputSections P.aliceWiring P.bobWiring
    P.aliceInstrument P.bobInstrument P.chargedAlice P.chargedBob n h

end PhysicalProtocol

section FullPhysicalQuantifiers

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
  [∀ n, StandardBorelSpace (Ω n)] (D : PhysicalDomains Ω)
  {EA EB : (n : ℕ) → D.admissible n → Type v}
  [∀ n h, NormedAddCommGroup (EA n h)] [∀ n h, InnerProductSpace ℂ (EA n h)]
  [∀ n h, CompleteSpace (EA n h)]
  [∀ n h, NormedAddCommGroup (EB n h)] [∀ n h, InnerProductSpace ℂ (EB n h)]
  [∀ n h, CompleteSpace (EB n h)]
  (FA : (n : ℕ) → FundamentalFamily (EA n))
  (FB : (n : ℕ) → FundamentalFamily (EB n))
  {GA : (n : ℕ) → D.actingDomain n true × Ω n → Type w}
  {GB : (n : ℕ) → D.actingDomain n false × Ω n → Type w}
  [∀ n z, NormedAddCommGroup (GA n z)] [∀ n z, InnerProductSpace ℂ (GA n z)]
  [∀ n z, CompleteSpace (GA n z)]
  [∀ n z, NormedAddCommGroup (GB n z)] [∀ n z, InnerProductSpace ℂ (GB n z)]
  [∀ n z, CompleteSpace (GB n z)]
  (QA : (n : ℕ) → FundamentalFamily (GA n))
  (QB : (n : ℕ) → FundamentalFamily (GB n))
  (WA : PhysicalMemoryWiring Ω D true FA QA)
  (WB : PhysicalMemoryWiring Ω D false FB QB)
  (PA : PhysicalLocalFamily Ω D true FA QA)
  (PB : PhysicalLocalFamily Ω D false FB QB)
  {a b : ℕ}
  (JA : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EA 0 D.initialHistory)
  (JB : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EB 0 D.initialHistory)

def packagePhysicalFamilies : PhysicalProtocol.{u,v,w} a b where
  outcome n := ⟨Ω n, inferInstance, inferInstance⟩
  domains := D
  alice n h := ⟨EA n h, inferInstance, inferInstance, inferInstance⟩
  bob n h := ⟨EB n h, inferInstance, inferInstance, inferInstance⟩
  aliceSections := FA
  bobSections := FB
  aliceOutput n z := ⟨GA n z, inferInstance, inferInstance, inferInstance⟩
  bobOutput n z := ⟨GB n z, inferInstance, inferInstance, inferInstance⟩
  aliceOutputSections := QA
  bobOutputSections := QB
  aliceWiring := WA
  bobWiring := WB
  aliceInstrument := PA
  bobInstrument := PB
  chargedAlice := JA
  chargedBob := JB

theorem packagePhysicalFamilies_matrix :
    (packagePhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB).represented =
      ofPhysicalFamilies Ω D FA FB QA QB WA WB PA PB JA JB := rfl

end FullPhysicalQuantifiers

structure PhysicalReadout {a b : ℕ} (P : PhysicalProtocol.{u,v,w} a b) (N c d : ℕ) where
  alice : QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument.MatrixInstrument (P.aliceSections N)
    (QuantumProver.ElegantJointMeasurement.NormalPhysicalTerminalAdmission.finiteOutputFamily
      (H := P.domains.admissible N) c) PUnit.{u+1}
  bob : QuantumProver.ElegantJointMeasurement.MeasurableNormalInstrument.MatrixInstrument (P.bobSections N)
    (QuantumProver.ElegantJointMeasurement.NormalPhysicalTerminalAdmission.finiteOutputFamily
      (H := P.domains.admissible N) d) PUnit.{u+1}

namespace PhysicalReadout

def represented {a b N c d : ℕ} {P : PhysicalProtocol.{u,v,w} a b}
    (Q : PhysicalReadout P N c d) (hc : 0 < c) (hd : 0 < d) :
    NormalTerminal (CommonRecord P.Outcomes) N c d :=
  QuantumProver.ElegantJointMeasurement.NormalPhysicalTerminalAdmission.ofPhysicalTerminal P.Outcomes P.domains
    P.aliceSections P.bobSections P.aliceOutputSections P.bobOutputSections
    P.aliceWiring P.bobWiring N c d Q.alice Q.bob hc hd

end PhysicalReadout

section LiteralSharedReport

variable (Ω : ℕ → Type u) [∀ n, MeasurableSpace (Ω n)]
  [∀ n, StandardBorelSpace (Ω n)]

def physicalSharedReportState (μ : Measure (PhysicalTranscript Ω))
    (J : PhysicalTranscript Ω → Fin 4) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  ∑ j : Fin 4, (((μ {t | J t = j}).toReal : ℝ) : ℂ) •
    QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.sharedProjector j

def commonSharedReportState (ν : Measure (Transcript (CommonRecord Ω)))
    (K : Transcript (CommonRecord Ω) → Fin 4) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  ∑ j : Fin 4, (((ν {t | K t = j}).toReal : ℝ) : ℂ) •
    QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.sharedProjector j

theorem commonSharedReportState_map_encode
    (μ : Measure (PhysicalTranscript Ω)) (J : PhysicalTranscript Ω → Fin 4) :
    commonSharedReportState Ω (μ.map (encodePhysicalTranscript Ω)) (liftPhysicalReport Ω J) =
      physicalSharedReportState Ω μ J := by
  apply Finset.sum_congr rfl
  intro j hj
  have he := liftPhysicalReport_event_probability Ω μ J {j}
  have he' : (μ.map (encodePhysicalTranscript Ω)) {t | liftPhysicalReport Ω J t = j} =
      μ {t | J t = j} := by
    simpa only [Set.preimage, Set.mem_singleton_iff] using he
  rw [he']

theorem physicalPreparedReport_completion
    (μ : Measure (PhysicalTranscript Ω)) (J : PhysicalTranscript Ω → Fin 4)
    (hJ : NullMeasurable J μ) :
    NullMeasurable (liftPhysicalReport Ω J) (μ.map (encodePhysicalTranscript Ω)) :=
  nullMeasurable_liftPhysicalReport Ω μ J hJ

end LiteralSharedReport
end QuantumProver.ElegantJointMeasurement.PhysicalCost
