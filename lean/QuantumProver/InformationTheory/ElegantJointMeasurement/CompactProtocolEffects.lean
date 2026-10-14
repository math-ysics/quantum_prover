import QuantumProver.InformationTheory.ElegantJointMeasurement.ProtocolEffectLimits
import QuantumProver.InformationTheory.ElegantJointMeasurement.ContinuousProtocol

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix
open QuantumProver.ElegantJointMeasurement.Augmented QuantumProver.ElegantJointMeasurement.Concurrence QuantumProver.ElegantJointMeasurement.ProtocolEffects QuantumProver.ElegantJointMeasurement.ProtocolEffectLimits

namespace QuantumProver.ElegantJointMeasurement.CompactProtocolEffects

noncomputable section

set_option maxHeartbeats 600000

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {m n : ℕ}

theorem tree_effect_subsequence (k : κ)
    (T : ℕ → FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : (a : ℕ) → Fin (T a).terminalBraPairs.length → Fin 4) :
    ∃ (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Filter.Tendsto (fun a j => groupedEffect (T (φ a)) ea eb (report (φ a)) j)
        Filter.atTop (nhds F) := by
  let f : ℕ → Fin 4 → Augmented κ :=
    fun a j => groupedRecord (T a) ea eb (fun _ => 0) k (report a) j
  let S : Set (Fin 4 → Augmented κ) :=
    {y | ∀ j, y j ∈ boundedScaledHull (Fintype.card (Index κ) : ℝ)
      (atoms (fun _ : κ => 0) k)}
  have hcompact : IsCompact S :=
    isCompact_pi_infinite fun _ => isCompact_boundedScaledHull
      (Fintype.card (Index κ) : ℝ) (isCompact_atoms (fun _ => 0) k)
  have hmem : ∀ a, f a ∈ S := by
    intro a j
    obtain ⟨r, p, heq⟩ := groupedRecord_finite_raw (T a) ea eb (fun _ => 0) k (report a) j
    have htrace : massLinear (f a j) ≤ (Fintype.card (Index κ) : ℝ) :=
      groupedEffect_trace_le_dimension (T a) ea eb (report a) j
    change f a j ∈ boundedScaledHull (Fintype.card (Index κ) : ℝ)
      (atoms (fun _ : κ => 0) k)
    change (∑ i, augmentedMap (fun _ : κ => 0) k (p i)) = f a j at heq
    rw [← heq] at htrace ⊢
    exact raw_product_sum_mem_boundedScaledHull (fun _ => 0) k
      (Fintype.card (Index κ) : ℝ) p htrace
  have : FirstCountableTopology (Fin 4 → Augmented κ) := by
    change FirstCountableTopology (Fin 4 → ((Index κ → Index κ → ℂ) × ℝ))
    infer_instance
  obtain ⟨x, hx, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hmem
  refine ⟨fun j => (x j).1, φ, hφ, ?_⟩
  have hc : Continuous (fun y : Fin 4 → Augmented κ => fun j => (y j).1) := by
    fun_prop
  have h := (hc.tendsto x).comp hlim
  simpa only [Function.comp_def, f, groupedRecord] using h

theorem tree_effect_subsequence_of_compressed_limit
    {ι : Type*} [Fintype ι] (k : κ)
    (T : ℕ → FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : (a : ℕ) → Fin (T a).terminalBraPairs.length → Fin 4)
    (J : Matrix (Index κ) ι ℂ) (E : Fin 4 → Matrix ι ι ℂ)
    (hcomp : ∀ j, Filter.Tendsto
      (fun a => Jᴴ * groupedEffect (T a) ea eb (report a) j * J)
      Filter.atTop (nhds (E j))) :
    ∃ (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Filter.Tendsto (fun a j => groupedEffect (T (φ a)) ea eb (report (φ a)) j)
        Filter.atTop (nhds F) ∧
      (∀ j, Jᴴ * F j * J = E j) ∧
      (∑ j, F j) = 1 ∧
      (∀ j, (F j).PosSemidef ∧ (1 - F j).PosSemidef) := by
  obtain ⟨F, φ, hφ, hlim⟩ := tree_effect_subsequence k T ea eb report
  refine ⟨F, φ, hφ, hlim, ?_, ?_, ?_⟩
  · intro j
    have hc : Continuous (fun G : Fin 4 → Matrix (Index κ) (Index κ) ℂ =>
        Jᴴ * G j * J) := by
      fun_prop
    exact tendsto_nhds_unique ((hc.tendsto F).comp hlim)
      ((hcomp j).comp hφ.tendsto_atTop)
  · exact tree_effect_limit_complete (fun a => T (φ a)) ea eb
      (fun a => report (φ a)) F hlim
  · intro j
    exact ⟨tree_effect_limit_posSemidef (fun a => T (φ a)) ea eb
      (fun a => report (φ a)) F hlim j,
      tree_effect_limit_upper (fun a => T (φ a)) ea eb (fun a => report (φ a)) F hlim j⟩

theorem groupedEffect_eq_matrix_pullback
    (T : FiniteLocalKrausTree m n) (ea : (Fin 2 × κ) ≃ Fin m)
    (eb : (Fin 2 × κ) ≃ Fin n) (report : Fin T.terminalBraPairs.length → Fin 4)
    (j : Fin 4) :
    groupedEffect T ea eb report j = pullbackEffect ea eb
      (QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.finiteKrausReportedEffect T report j) := by
  classical
  unfold groupedEffect outcomeSum QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.finiteKrausReportedEffect
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp only [physicalEffect_eq_pullback, map_zero]

theorem matrix_effect_sequence_pulled_back
    (T : ℕ → FiniteLocalKrausTree m n)
    (report : (k : ℕ) → Fin (T k).terminalBraPairs.length → Fin 4)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (F : Fin 4 → QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.JointMatrix m n)
    (hF : Filter.Tendsto
      (fun k => QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.finiteKrausReportedEffect (T k) (report k))
      Filter.atTop (nhds F)) :
    Filter.Tendsto (fun k j => groupedEffect (T k) ea eb (report k) j)
      Filter.atTop (nhds (fun j => pullbackEffect ea eb (F j))) := by
  have hc : Continuous (fun G : Fin 4 → QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.JointMatrix m n =>
      fun j => pullbackEffect ea eb (G j)) :=
    continuous_pi fun j => (pullbackEffect ea eb).toContinuousLinearMap.continuous.comp
      (continuous_apply j)
  simpa only [Function.comp_def, groupedEffect_eq_matrix_pullback] using
    (hc.tendsto F).comp hF

end

end QuantumProver.ElegantJointMeasurement.CompactProtocolEffects
