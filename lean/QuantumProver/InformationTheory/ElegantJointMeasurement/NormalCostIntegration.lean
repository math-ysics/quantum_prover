import QuantumProver.InformationTheory.ElegantJointMeasurement.EntanglementBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open Set Filter
open QuantumProver.ElegantJointMeasurement.GeneralResource
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Topology

namespace QuantumProver.ElegantJointMeasurement.NormalCostIntegration

section OperationalClosure

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {m n : ℕ}

theorem effect_closure_density_limit_entropy_ge_one
    (Ψ : Matrix κ κ ℂ) (hΨ : (Ψ * Ψᴴ).trace = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (F : ℕ → Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ)
    (hF : ∀ a, F a ∈ closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb))
    (hChannel : ∀ ρ : Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ,
      ρ.PosSemidef → ρ.trace = 1 →
      Tendsto (fun a => QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
        (codeMatrix Ψ) (F a) ρ) atTop
        (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  classical
  letI : NormedAddCommGroup
      (Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ) :=
    inferInstanceAs (NormedAddCommGroup
      (Fin 4 → QuantumProver.ElegantJointMeasurement.Augmented.Index κ → QuantumProver.ElegantJointMeasurement.Augmented.Index κ → ℂ))
  have hApprox : ∀ a : ℕ, ∃ G ∈ QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb,
      dist (F a) G < 1 / ((a : ℝ) + 1) := by
    intro a
    exact Metric.mem_closure_iff.mp (hF a) _ (by positivity)
  choose G hG hdist using hApprox
  have hDelta : Tendsto (fun a => G a - F a) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro a
    rw [← dist_eq_norm, dist_comm]
    exact (hdist a).le
  change ∀ a, ∃ (T : QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree m n)
    (report : Fin T.terminalBraPairs.length → Fin 4),
    G a = fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect T ea eb report j at hG
  choose T report hEq using hG
  apply QuantumProver.ElegantJointMeasurement.FiniteTreeCostModel.entropy_ge_one_of_density_channel_limit Ψ hΨ T ea eb report
  intro ρ hρ ht
  let L : (Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ) →
      Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
    fun H => QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel (codeMatrix Ψ) H ρ
  have hContinuous : Continuous L := by
    unfold L QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
    fun_prop
  have hZero : L 0 = 0 := by
    simp [L, QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel]
  have hSub : ∀ A B, L (A - B) = L A - L B := by
    intro A B
    simp only [L, QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel,
      Pi.sub_apply, Matrix.sub_mul, Matrix.trace_sub, sub_smul, Finset.sum_sub_distrib]
  have hDifference : Tendsto (fun a => L (G a) - L (F a)) atTop (nhds 0) := by
    have h := (hContinuous.tendsto 0).comp hDelta
    simpa only [Function.comp_def, hZero, hSub] using h
  have hPhysical : Tendsto (fun a => L (F a)) atTop
      (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ)) := hChannel ρ hρ ht
  have hActual : Tendsto (fun a => L (G a)) atTop
      (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ)) := by
    simpa only [sub_add_cancel, zero_add] using hDifference.add hPhysical
  simpa only [hEq, L] using hActual

theorem physical_output_density_limit_entropy_ge_one_of_effect_bridge
    (Ψ : Matrix κ κ ℂ) (hΨ : (Ψ * Ψᴴ).trace = 1)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (F : ℕ → Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) (QuantumProver.ElegantJointMeasurement.Augmented.Index κ) ℂ)
    (output : ℕ → Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ →
      Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (hF : ∀ a, F a ∈ closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb))
    (hOutput : ∀ a ρ, ρ.PosSemidef → ρ.trace = 1 →
      output a ρ = QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
        (codeMatrix Ψ) (F a) ρ)
    (hLimit : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      Tendsto (fun a => output a ρ) atTop
        (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  apply effect_closure_density_limit_entropy_ge_one Ψ hΨ ea eb F hF
  intro ρ hρ ht
  simpa only [hOutput _ ρ hρ ht] using hLimit ρ hρ ht

end OperationalClosure

section RectangularResource

open QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding
variable {κ η : Type*} [Fintype κ] [DecidableEq κ] [Fintype η] [DecidableEq η]
  {m n : ℕ}

theorem rectangular_physical_output_density_limit_entropy_ge_one_of_effect_bridge
    (Ψ : Matrix κ η ℂ) (hΨ : (Ψ * Ψᴴ).trace = 1)
    (ea : (Fin 2 × (κ ⊕ η)) ≃ Fin m) (eb : (Fin 2 × (κ ⊕ η)) ≃ Fin n)
    (F : ℕ → Fin 4 → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index (κ ⊕ η))
      (QuantumProver.ElegantJointMeasurement.Augmented.Index (κ ⊕ η)) ℂ)
    (output : ℕ → Matrix QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex QuantumProver.ElegantJointMeasurement.Teleportation.SystemIndex ℂ →
      Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (hF : ∀ a, F a ∈ closure (QuantumProver.ElegantJointMeasurement.TailReference.finiteTreeEffectSet ea eb))
    (hOutput : ∀ a ρ, ρ.PosSemidef → ρ.trace = 1 →
      output a ρ = QuantumProver.ElegantJointMeasurement.Teleportation.Tomography.resourceMeasurementChannel
        (codeMatrix (coefficient Ψ)) (F a) ρ)
    (hLimit : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      Tendsto (fun a => output a ρ) atTop
        (nhds (QuantumProver.ElegantJointMeasurement.Teleportation.physicalClassicalChannel ρ))) :
    1 ≤ QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (Ψ * Ψᴴ) := by
  have h := physical_output_density_limit_entropy_ge_one_of_effect_bridge
    (coefficient Ψ) (normalized_coefficient Ψ hΨ) ea eb F output hF hOutput hLimit
  simpa only [coefficient_entropy] using h

end RectangularResource

end QuantumProver.ElegantJointMeasurement.NormalCostIntegration
