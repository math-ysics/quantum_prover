import QuantumProver.InformationTheory.QuantumTypicalCarrier
import QuantumProver.InformationTheory.QuantumDecouplingRobust

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable section

namespace QuantumProver.QuantumRedistributionCarrierDecoupling

open Matrix
open QuantumProver.QuantumTypicalCarrier QuantumProver.QuantumDecoupling
open QuantumProver.QuantumEntropy QuantumProver.SandwichedDPI QuantumProver.UnitarySecondMoment
open QuantumProver.SuperchannelDiscrimination
open FlaggedStates
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

variable {B Y J K : Type*} [Fintype B] [DecidableEq B]
  [Fintype Y] [DecidableEq Y] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]
variable {d : ℕ}

def carrierUniformReference (K : Type*) [Fintype K] [DecidableEq K]
    (ρ : Matrix (B × Y) (B × Y) ℂ) : Matrix (K × Y) (K × Y) ℂ :=
  (((Fintype.card K : ℂ)⁻¹) • (1 : Matrix K K ℂ)) ⊗ₖ partialTrace_left ρ

def physicalCarrierDecouplingCost (d : ℕ) (K : Type*) [Fintype K]
    (ν : Matrix (B × Y) (B × Y) ℂ) : ℝ :=
  if Fintype.card K = 1 then 0 else
    (Fintype.card K : ℝ)^2 * (partialTrace_left ν).rank * (ν * ν).trace.re / (d : ℝ)

def carrierPhysicalKraus (V : Matrix B (Fin d) ℂ) (U : UGroup d) :
    Matrix (Fin d) B ℂ := (U : CMat d) * Vᴴ

def carrierRotatedState (V : Matrix B (Fin d) ℂ)
    (ρ : Matrix (B × Y) (B × Y) ℂ) (U : UGroup d) :
    Matrix (Fin d × Y) (Fin d × Y) ℂ :=
  carrierLift (carrierPhysicalKraus V U) Y * ρ *
    (carrierLift (carrierPhysicalKraus V U) Y)ᴴ

def carrierDecoupledMarginal (e : Fin d ≃ J × K) (V : Matrix B (Fin d) ℂ)
    (ρ : Matrix (B × Y) (B × Y) ℂ) (U : UGroup d) :
    Matrix (K × Y) (K × Y) ℂ :=
  partialTrace_left (Matrix.reindex (spectatorChart e) (spectatorChart e)
    (carrierRotatedState V ρ U))

def carrierDecouplingError (e : Fin d ≃ J × K) (V : Matrix B (Fin d) ℂ)
    (ρ : Matrix (B × Y) (B × Y) ℂ) (U : UGroup d) :
    Matrix (K × Y) (K × Y) ℂ :=
  carrierDecoupledMarginal e V ρ U - carrierUniformReference K ρ

theorem carrierPhysicalKraus_gram (V : Matrix B (Fin d) ℂ) (U : UGroup d) :
    (carrierPhysicalKraus V U)ᴴ * carrierPhysicalKraus V U = V * Vᴴ := by
  have hU : (U : CMat d)ᴴ * (U : CMat d) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  unfold carrierPhysicalKraus
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    (V * (U : CMat d)ᴴ) * ((U : CMat d) * Vᴴ) =
      V * ((U : CMat d)ᴴ * (U : CMat d)) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = V * Vᴴ := by rw [hU, Matrix.mul_one]

theorem carrierRotatedState_eq_localUnitary_compression
    (V : Matrix B (Fin d) ℂ) (ρ : Matrix (B × Y) (B × Y) ℂ) (U : UGroup d) :
    carrierRotatedState V ρ U =
      ((U : CMat d) ⊗ₖ (1 : Matrix Y Y ℂ)) * carrierCompression V Y ρ *
        ((U : CMat d) ⊗ₖ (1 : Matrix Y Y ℂ))ᴴ := by
  unfold carrierRotatedState carrierPhysicalKraus
  change carrierLift ((U : CMat d) * Vᴴ) Y * ρ *
    (carrierLift ((U : CMat d) * Vᴴ) Y)ᴴ =
      carrierLift (U : CMat d) Y * carrierCompression V Y ρ *
        (carrierLift (U : CMat d) Y)ᴴ
  rw [carrierLift_mul, carrierLift_star, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [carrierCompression, Matrix.mul_assoc]

theorem carrierDecoupledMarginal_eq_compressed (e : Fin d ≃ J × K)
    (V : Matrix B (Fin d) ℂ) (ρ : Matrix (B × Y) (B × Y) ℂ) (U : UGroup d) :
    carrierDecoupledMarginal e V ρ U =
      decoupledMarginal e (carrierCompression V Y ρ) U := by
  unfold carrierDecoupledMarginal decoupledMarginal
  rw [carrierRotatedState_eq_localUnitary_compression]

theorem carrierCompression_uniformReference {V : Matrix B (Fin d) ℂ}
    {P : Matrix B B ℂ} (hV : V * Vᴴ = P)
    {ρ : Matrix (B × Y) (B × Y) ℂ} (hs : carrierSupport P ρ) :
    uniformReference (K := K) (carrierCompression V Y ρ) = carrierUniformReference K ρ := by
  unfold uniformReference carrierUniformReference
  rw [carrierCompression_partialTrace_left hV hs]

theorem carrierDecouplingError_eq_compressed (e : Fin d ≃ J × K)
    {V : Matrix B (Fin d) ℂ} {P : Matrix B B ℂ} (hV : V * Vᴴ = P)
    {ρ : Matrix (B × Y) (B × Y) ℂ} (hs : carrierSupport P ρ) (U : UGroup d) :
    carrierDecouplingError e V ρ U =
      decouplingError e (carrierCompression V Y ρ) U := by
  unfold carrierDecouplingError decouplingError
  rw [carrierDecoupledMarginal_eq_compressed, carrierCompression_uniformReference hV hs]

theorem carrierCompression_reference_rank {V : Matrix B (Fin d) ℂ}
    {P : Matrix B B ℂ} (hV : V * Vᴴ = P)
    {ν : Matrix (B × Y) (B × Y) ℂ} (hs : carrierSupport P ν) :
    (partialTrace_left (carrierCompression V Y ν)).rank = (partialTrace_left ν).rank :=
  congrArg Matrix.rank (carrierCompression_partialTrace_left hV hs)

theorem carrierCompression_decouplingCost {V : Matrix B (Fin d) ℂ}
    {P : Matrix B B ℂ} (hV : V * Vᴴ = P)
    {ν : Matrix (B × Y) (B × Y) ℂ} (hs : carrierSupport P ν) :
    decouplingCost (K := K) (carrierCompression V Y ν) = physicalCarrierDecouplingCost d K ν := by
  unfold decouplingCost physicalCarrierDecouplingCost
  rw [carrierCompression_partialTrace_left hV hs, carrierCompression_purity hV hs]

theorem physicalCarrierDecouplingCost_nonneg {V : Matrix B (Fin d) ℂ}
    {P : Matrix B B ℂ} (hV : V * Vᴴ = P)
    {ν : Matrix (B × Y) (B × Y) ℂ} (hν : ν.PosSemidef) (hs : carrierSupport P ν) :
    0 ≤ physicalCarrierDecouplingCost d K ν := by
  rw [← carrierCompression_decouplingCost hV hs]
  exact decouplingCost_nonneg (carrierCompression_posSemidef V hν)

theorem physicalCarrierDecouplingCost_singleton (ν : Matrix (B × Y) (B × Y) ℂ)
    (hk : Fintype.card K = 1) : physicalCarrierDecouplingCost d K ν = 0 := by
  simp only [physicalCarrierDecouplingCost, hk, if_true]

theorem paddedCompression_isDensity (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P)
    (d : ℕ) (hrank : P.rank ≤ d) {ρ : Matrix (B × Y) (B × Y) ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hs : carrierSupport P ρ) :
    FlaggedStates.IsDensity (carrierCompression (paddedCarrier P hP d hrank) Y ρ) :=
  carrierCompression_isDensity (paddedCarrier_projection P hP d hrank) hρ hs

theorem paddedCompression_reference (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P)
    (d : ℕ) (hrank : P.rank ≤ d) {ρ : Matrix (B × Y) (B × Y) ℂ}
    (hs : carrierSupport P ρ) :
    partialTrace_left (carrierCompression (paddedCarrier P hP d hrank) Y ρ) =
      partialTrace_left ρ :=
  carrierCompression_partialTrace_left (paddedCarrier_projection P hP d hrank) hs

theorem paddedCompression_reference_rank (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P)
    (d : ℕ) (hrank : P.rank ≤ d) {ν : Matrix (B × Y) (B × Y) ℂ}
    (hs : carrierSupport P ν) :
    (partialTrace_left (carrierCompression (paddedCarrier P hP d hrank) Y ν)).rank =
      (partialTrace_left ν).rank :=
  carrierCompression_reference_rank (paddedCarrier_projection P hP d hrank) hs

theorem paddedCompression_purity (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P)
    (d : ℕ) (hrank : P.rank ≤ d) {ν : Matrix (B × Y) (B × Y) ℂ}
    (hs : carrierSupport P ν) :
    (carrierCompression (paddedCarrier P hP d hrank) Y ν *
      carrierCompression (paddedCarrier P hP d hrank) Y ν).trace.re = (ν * ν).trace.re :=
  carrierCompression_purity (paddedCarrier_projection P hP d hrank) hs

theorem paddedCompression_decouplingCost (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P)
    (d : ℕ) (hrank : P.rank ≤ d) {ν : Matrix (B × Y) (B × Y) ℂ}
    (hs : carrierSupport P ν) :
    decouplingCost (K := K) (carrierCompression (paddedCarrier P hP d hrank) Y ν) =
      physicalCarrierDecouplingCost d K ν :=
  carrierCompression_decouplingCost (paddedCarrier_projection P hP d hrank) hs

theorem paddedCompression_difference_traceNorm (P : Matrix B B ℂ)
    (hP : PetzSmoothing.IsProjection P) (d : ℕ) (hrank : P.rank ≤ d)
    {ρ ν : Matrix (B × Y) (B × Y) ℂ} (hρ : carrierSupport P ρ) (hν : carrierSupport P ν) :
    traceNorm (carrierCompression (paddedCarrier P hP d hrank) Y ρ -
      carrierCompression (paddedCarrier P hP d hrank) Y ν) = traceNorm (ρ - ν) :=
  carrierCompression_difference_traceNorm hP (paddedCarrier_projection P hP d hrank) hρ hν

section CommonUnitary

variable {J₁ K₁ Y₁ J₂ K₂ Y₂ : Type*}
  [Fintype J₁] [DecidableEq J₁] [Fintype K₁] [DecidableEq K₁]
  [Fintype Y₁] [DecidableEq Y₁]
  [Fintype J₂] [DecidableEq J₂] [Fintype K₂] [DecidableEq K₂]
  [Fintype Y₂] [DecidableEq Y₂]

theorem exists_common_carrier_decoupling_unitary
    (e₁ : Fin d ≃ J₁ × K₁) (e₂ : Fin d ≃ J₂ × K₂)
    {V : Matrix B (Fin d) ℂ} {P : Matrix B B ℂ}
    (hP : PetzSmoothing.IsProjection P) (hV : V * Vᴴ = P)
    (ρ₁ ν₁ : Matrix (B × Y₁) (B × Y₁) ℂ)
    (ρ₂ ν₂ : Matrix (B × Y₂) (B × Y₂) ℂ)
    (hν₁ : ν₁.PosSemidef) (hν₂ : ν₂.PosSemidef)
    (hsρ₁ : carrierSupport P ρ₁) (hsν₁ : carrierSupport P ν₁)
    (hsρ₂ : carrierSupport P ρ₂) (hsν₂ : carrierSupport P ν₂)
    {ε₁ ε₂ : ℝ} (hclose₁ : traceNorm (ρ₁ - ν₁) ≤ ε₁)
    (hclose₂ : traceNorm (ρ₂ - ν₂) ≤ ε₂) :
    ∃ U : UGroup d,
      traceNorm (carrierDecouplingError e₁ V ρ₁ U) ≤
        Real.sqrt (3 * physicalCarrierDecouplingCost d K₁ ν₁) + 2 * ε₁ ∧
      traceNorm (carrierDecouplingError e₂ V ρ₂ U) ≤
        Real.sqrt (3 * physicalCarrierDecouplingCost d K₂ ν₂) + 2 * ε₂ := by
  have hc₁ : traceNorm (carrierCompression V Y₁ ρ₁ - carrierCompression V Y₁ ν₁) ≤ ε₁ := by
    rw [carrierCompression_difference_traceNorm hP hV hsρ₁ hsν₁]
    exact hclose₁
  have hc₂ : traceNorm (carrierCompression V Y₂ ρ₂ - carrierCompression V Y₂ ν₂) ≤ ε₂ := by
    rw [carrierCompression_difference_traceNorm hP hV hsρ₂ hsν₂]
    exact hclose₂
  obtain ⟨U, h₁, h₂⟩ := QuantumDecouplingRobust.exists_common_decoupling_unitary_robust
    e₁ e₂ (carrierCompression V Y₁ ρ₁) (carrierCompression V Y₁ ν₁)
    (carrierCompression V Y₂ ρ₂) (carrierCompression V Y₂ ν₂)
    (carrierCompression_posSemidef V hν₁) (carrierCompression_posSemidef V hν₂) hc₁ hc₂
  refine ⟨U, ?_, ?_⟩
  · rw [carrierDecouplingError_eq_compressed e₁ hV hsρ₁ U,
      ← carrierCompression_decouplingCost hV hsν₁]
    exact h₁
  · rw [carrierDecouplingError_eq_compressed e₂ hV hsρ₂ U,
      ← carrierCompression_decouplingCost hV hsν₂]
    exact h₂

theorem exists_padded_normalized_common_decoupling_unitary
    (P : Matrix B B ℂ) (hP : PetzSmoothing.IsProjection P)
    (d : ℕ) (hrank : P.rank ≤ d)
    (e₁ : Fin d ≃ J₁ × K₁) (e₂ : Fin d ≃ J₂ × K₂)
    (ρ₁ ν₁ : Matrix (B × Y₁) (B × Y₁) ℂ)
    (ρ₂ ν₂ : Matrix (B × Y₂) (B × Y₂) ℂ)
    (hρ₁ : FlaggedStates.IsDensity ρ₁) (hρ₂ : FlaggedStates.IsDensity ρ₂)
    (hν₁ : ν₁.PosSemidef) (hν₂ : ν₂.PosSemidef)
    (hsρ₁ : carrierSupport P ρ₁) (hsν₁ : carrierSupport P ν₁)
    (hsρ₂ : carrierSupport P ρ₂) (hsν₂ : carrierSupport P ν₂)
    {ε₁ ε₂ : ℝ} (hclose₁ : traceNorm (ρ₁ - ν₁) ≤ ε₁)
    (hclose₂ : traceNorm (ρ₂ - ν₂) ≤ ε₂) :
    ∃ U : UGroup d,
      FlaggedStates.IsDensity (carrierCompression (paddedCarrier P hP d hrank) Y₁ ρ₁) ∧
      FlaggedStates.IsDensity (carrierCompression (paddedCarrier P hP d hrank) Y₂ ρ₂) ∧
      traceNorm (carrierDecouplingError e₁ (paddedCarrier P hP d hrank) ρ₁ U) ≤
        Real.sqrt (3 * physicalCarrierDecouplingCost d K₁ ν₁) + 2 * ε₁ ∧
      traceNorm (carrierDecouplingError e₂ (paddedCarrier P hP d hrank) ρ₂ U) ≤
        Real.sqrt (3 * physicalCarrierDecouplingCost d K₂ ν₂) + 2 * ε₂ := by
  obtain ⟨U, h₁, h₂⟩ := exists_common_carrier_decoupling_unitary e₁ e₂ hP
    (paddedCarrier_projection P hP d hrank) ρ₁ ν₁ ρ₂ ν₂ hν₁ hν₂
    hsρ₁ hsν₁ hsρ₂ hsν₂ hclose₁ hclose₂
  exact ⟨U, paddedCompression_isDensity P hP d hrank hρ₁ hsρ₁,
    paddedCompression_isDensity P hP d hrank hρ₂ hsρ₂, h₁, h₂⟩

end CommonUnitary

end QuantumProver.QuantumRedistributionCarrierDecoupling
