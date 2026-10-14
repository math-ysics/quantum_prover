import QuantumProver.InformationTheory.WernerEndpoint.PurityTheorems
import QuantumProver.InformationTheory.WernerEndpoint.OperationalEndpointCost
import QuantumProver.InformationTheory.WernerEndpoint.LocalProtocolReindex
import QuantumProver.InformationTheory.WernerEndpoint.EntropyCostCertificate
import QuantumProver.InformationTheory.WernerEndpoint.FidelityError
import QuantumProver.InformationTheory.WernerEndpoint.CompanionMaximum
import QuantumProver.InformationTheory.WernerEndpoint.CPProtocol
import QuantumProver.InformationTheory.WernerEndpoint.ContinuousCPRepresentation
import QuantumProver.InformationTheory.ConditionalEntropy.WeightedContinuity

noncomputable section

namespace QuantumProver.WernerEndpoint.Corollaries

open scoped BigOperators ComplexOrder
universe u

def stinespringLinearMap {Y B E : Type*} [Fintype Y] [Fintype B] [Fintype E] [DecidableEq Y]
    (N : Stinespring Y B E) : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ where
  toFun := N.apply
  map_add' rho sigma := by
    change partialTraceLeft (N.coeff * (rho + sigma) * N.coeff.conjTranspose) = _
    rw [Matrix.mul_add, Matrix.add_mul]
    exact OperationalEndpointCost.partialTraceLeftLinearMap.map_add _ _
  map_smul' z rho := by
    change partialTraceLeft (N.coeff * (z • rho) * N.coeff.conjTranspose) = _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact OperationalEndpointCost.partialTraceLeftLinearMap.map_smul z _

theorem cptp_companion_purity_optimum {d : ℕ} (hd : 2 ≤ d)
    {Y B : Type*} [Fintype Y] [Fintype B] [DecidableEq Y] [DecidableEq B]
    (Φ : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Φ)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Φ) (β : ℝ)
    (hbound : ∀ v : Y → ℂ, vectorNormSq v = 1 → purity (Φ (pureDensity v)) ≤ β)
    (hmax : ∃ v : Y → ℂ, vectorNormSq v = 1 ∧ purity (Φ (pureDensity v)) = β) :
    (∀ Ψ : Edge d × Y → ℂ, vectorNormSq Ψ = 1 →
      purity (((antisymmetricStinespring d).tensor (stinespringOfCPTP Φ hCP hTP)).apply
        (pureDensity Ψ)) ≤ β / 2) ∧
    ∃ Ψ : Edge d × Y → ℂ, vectorNormSq Ψ = 1 ∧
      purity (((antisymmetricStinespring d).tensor (stinespringOfCPTP Φ hCP hTP)).apply
        (pureDensity Ψ)) = β / 2 := by
  constructor
  · intro Ψ hΨ
    exact antisymmetric_cptp_companion_purity_le_half hd Φ hCP hTP β hbound Ψ hΨ
  · obtain ⟨v, hv, hp⟩ := hmax
    let e := firstEndpointEdge d hd
    refine ⟨fun xy => coordinateSlater e xy.1 * v xy.2, ?_, ?_⟩
    · rw [product_vectorNormSq, coordinateSlater_normSq, hv, one_mul]
    · rw [Stinespring.tensor_product_purity, stinespringOfCPTP_apply,
        ← antisymmetricChannel_eq_stinespring, antisymmetricChannel_slater_purity, hp]
      ring

theorem cptp_companion_purityMaximum {d : ℕ} (hd : 2 ≤ d)
    {Y B : Type*} [Fintype Y] [Fintype B] [DecidableEq Y] [DecidableEq B] [Nonempty Y]
    (Phi : Matrix Y Y ℂ →ₗ[ℂ] Matrix B B ℂ)
    (hCP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.CompletelyPositive Phi)
    (hTP : QuantumProver.SuperchannelDiscrimination.CPTPKraus.TracePreserving Phi) :
    CompanionMaximum.pureOutputPurityMaximum
      (stinespringLinearMap ((antisymmetricStinespring d).tensor
        (stinespringOfCPTP Phi hCP hTP))) =
      CompanionMaximum.pureOutputPurityMaximum Phi / 2 := by
  letI : Nonempty (Edge d) := ⟨firstEndpointEdge d hd⟩
  let L := stinespringLinearMap ((antisymmetricStinespring d).tensor
    (stinespringOfCPTP Phi hCP hTP))
  have hOpt := cptp_companion_purity_optimum hd Phi hCP hTP
    (CompanionMaximum.pureOutputPurityMaximum Phi)
    (CompanionMaximum.pureOutputPurity_le_maximum Phi)
    (CompanionMaximum.exists_pureOutputPurity_eq_maximum Phi)
  change CompanionMaximum.pureOutputPurityMaximum L = _
  apply le_antisymm
  · apply csSup_le (CompanionMaximum.pureOutputPurityRange_nonempty L)
    rintro p ⟨v, hv, rfl⟩
    exact hOpt.1 v hv
  · exact le_csSup (CompanionMaximum.pureOutputPurityRange_bddAbove L) hOpt.2

theorem endpoint_all_copy_purity_and_finiteFormation (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    (∀ ψ : PhysicalPower d n × PhysicalPower d n → ℂ,
      vectorNormSq ψ = 1 →
      HasAntisymmetricSupport d n (fun a b => ψ (a,b)) →
      purity (partialTraceLeft (pureDensity ψ)) ≤ (1 / 2 : ℝ) ^ n) ∧
    (∃ ψ : PhysicalPower d n × PhysicalPower d n → ℂ,
      vectorNormSq ψ = 1 ∧
      HasAntisymmetricSupport d n (fun a b => ψ (a,b)) ∧
      purity (partialTraceLeft (pureDensity ψ)) = (1 / 2 : ℝ) ^ n) ∧
    (∀ ψ : PhysicalPower d n × PhysicalPower d n → ℂ,
      vectorNormSq ψ = 1 →
      HasAntisymmetricSupport d n (fun a b => ψ (a,b)) →
      (n : ℝ) ≤ physicalAliceEntropy d n ψ) ∧
    AntisymmetricEnsembleCost.finiteConvexRoof (physicalAntisymmetricState d n) =
      (n : EReal) := by
  have hp := antisymmetric_physical_purity_optimum d hd n
  exact ⟨hp.1, hp.2, antisymmetric_physical_entropy_lower d hd n,
    physicalAntisymmetricState_finiteConvexRoof_eq d hd n⟩

theorem endpoint_one_copy_finitePreparation (d : ℕ) (hd : 2 ≤ d) :
    ∃ T : OperationalEndpointCost.FiniteLocalProtocol d d 2 2,
      T.apply (pureDensity OperationalEndpointCost.bellVector) =
        (Fintype.card (Edge d) : ℂ)⁻¹ • wedgeProjector d :=
  OperationalEndpointCost.exists_finiteLocalProtocol_endpoint_preparation d hd

theorem finiteCPProtocol_finiteConvexRoof_le {c d a b : ℕ}
    (T : MatrixCPProtocol.FiniteCPProtocol c d a b)
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    AntisymmetricEnsembleCost.finiteConvexRoof (T.apply ρ) ≤
      AntisymmetricEnsembleCost.finiteConvexRoof ρ := by
  rw [← T.represented_toMatrix_apply ρ]
  exact LocalEntropy.finiteLocalProtocol_finiteConvexRoof_le T.represented_toMatrix ρ

theorem endpoint_matrix_singlet_cost (d : ℕ) (hd : 2 ≤ d) :
    (∀ n : ℕ, AntisymmetricEnsembleCost.finiteConvexRoof
      (physicalAntisymmetricState d n) = (n : EReal)) ∧
    finiteSingletHHTCost d = 1 ∧ finiteHeightSingletHHTCost.{u} d = 1 := by
  exact ⟨fun n => physicalAntisymmetricState_finiteConvexRoof_eq d hd n,
    finiteSingletHHTCost_eq_one d hd, finiteHeightSingletHHTCost_eq_one d hd⟩

end QuantumProver.WernerEndpoint.Corollaries
