import QuantumProver.InformationTheory.ElegantJointMeasurement.ProtocolEffects

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
open InnerProductSpace QuantumProver.ElegantJointMeasurement.Augmented QuantumProver.ElegantJointMeasurement.Concurrence QuantumProver.ElegantJointMeasurement.ProtocolEffects

namespace QuantumProver.ElegantJointMeasurement.ProtocolEffectLimits

noncomputable section

set_option maxHeartbeats 600000

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {m n : ℕ} {η : Type*} {l : Filter η} [l.NeBot]

private theorem groupedCost_zero (T : FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (k : κ) (report : Fin T.terminalBraPairs.length → Fin 4) (j : Fin 4) :
    groupedCost T ea eb (fun _ => 0) k report j = 0 := by
  simp [groupedCost, outcomeSum, SystemBraPair.tailCost]

theorem tree_effect_limit_complete
    (T : η → FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : (a : η) → Fin (T a).terminalBraPairs.length → Fin 4)
    (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ)
    (hlim : Filter.Tendsto (fun a j => groupedEffect (T a) ea eb (report a) j) l (nhds F)) :
    (∑ j, F j) = 1 := by
  have hsum : Continuous (fun G : Fin 4 → Matrix (Index κ) (Index κ) ℂ => ∑ j, G j) := by
    fun_prop
  have h := (hsum.tendsto F).comp hlim
  change Filter.Tendsto (fun a => ∑ j, groupedEffect (T a) ea eb (report a) j)
    l (nhds (∑ j, F j)) at h
  have hconst : Filter.Tendsto (fun _ : η => (1 : Matrix (Index κ) (Index κ) ℂ))
      l (nhds (∑ j, F j)) := by
    simpa only [groupedEffect_sum] using h
  exact tendsto_nhds_unique hconst tendsto_const_nhds

theorem tree_effect_limit_posSemidef
    (T : η → FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : (a : η) → Fin (T a).terminalBraPairs.length → Fin 4)
    (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ)
    (hlim : Filter.Tendsto (fun a j => groupedEffect (T a) ea eb (report a) j) l (nhds F)) :
    ∀ j, (F j).PosSemidef := by
  intro j
  apply Matrix.posSemidef_is_closed.mem_of_tendsto ((tendsto_pi_nhds.mp hlim) j)
  exact Filter.Eventually.of_forall (fun a => groupedEffect_posSemidef (T a) ea eb (report a) j)

private theorem tree_effect_limit_raw_pairs (k : κ)
    (T : η → FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : (a : η) → Fin (T a).terminalBraPairs.length → Fin 4)
    (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ)
    (hlim : Filter.Tendsto (fun a j => groupedEffect (T a) ea eb (report a) j) l (nhds F)) :
    ∀ j, ∃ (r : ℕ) (p : Fin r → Local κ × Local κ),
      (∑ i, effectMatrix (product (p i))) = F j := by
  obtain ⟨c, hc, htotal, hrepr⟩ := finite_outcome_effect_limit_cost_representation
    (fun _ : κ => 0) k (fun _ => (Fintype.card (Index κ) : ℝ)) 0
    (fun a j => groupedRecord (T a) ea eb (fun _ => 0) k (report a) j) F hlim
    (Filter.Eventually.of_forall fun a => groupedRecord_finite_raw (T a) ea eb (fun _ => 0) k (report a))
    (Filter.Eventually.of_forall fun a => groupedEffect_trace_le_dimension (T a) ea eb (report a))
    (Filter.Eventually.of_forall fun a => by simp only [groupedRecord, groupedCost_zero, Finset.sum_const_zero, le_refl])
  intro j
  obtain ⟨r, hr, w, p, hw, hp, hmass, hF, hcost⟩ := hrepr j
  refine ⟨r, fun i => QuantumProver.ElegantJointMeasurement.ClosureJoin.rawPair (w i) (p i), ?_⟩
  simpa only [QuantumProver.ElegantJointMeasurement.ClosureJoin.rawPair_effect _ (hw _)] using hF

theorem tree_effect_limit_raw_realization (k : κ)
    (T : η → FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : (a : η) → Fin (T a).terminalBraPairs.length → Fin 4)
    (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ)
    (hlim : Filter.Tendsto (fun a j => groupedEffect (T a) ea eb (report a) j) l (nhds F)) :
    ∃ (r : Fin 4 → ℕ)
      (A B : (j : Fin 4) → Fin (r j) → Matrix (Fin 2) κ ℂ),
      (∀ j, (∑ i, effectMatrix (QuantumProver.ElegantJointMeasurement.ResourceCode.productKet (A j i) (B j i))) = F j) ∧
      (∑ j, ∑ i, effectMatrix (QuantumProver.ElegantJointMeasurement.ResourceCode.productKet (A j i) (B j i))) = 1 := by
  classical
  choose r p hp using tree_effect_limit_raw_pairs k T ea eb report F hlim
  refine ⟨r, fun j i => localMatrix (p j i).1, fun j i => localMatrix (p j i).2, ?_, ?_⟩
  · exact hp
  · change (∑ j, ∑ i, effectMatrix (product (p j i))) = 1
    simp only [hp]
    exact tree_effect_limit_complete T ea eb report F hlim

theorem tree_effect_limit_properties
    (T : η → FiniteLocalKrausTree m n)
    (ea : (Fin 2 × κ) ≃ Fin m) (eb : (Fin 2 × κ) ≃ Fin n)
    (report : (a : η) → Fin (T a).terminalBraPairs.length → Fin 4)
    (F : Fin 4 → Matrix (Index κ) (Index κ) ℂ)
    (hlim : Filter.Tendsto (fun a j => groupedEffect (T a) ea eb (report a) j) l (nhds F)) :
    (∑ j, F j) = 1 ∧
      (∀ j, (F j).PosSemidef ∧ (F j).IsHermitian ∧ (1 - F j).PosSemidef ∧
        0 ≤ effectMass (F j) ∧ effectMass (F j) ≤ (Fintype.card (Index κ) : ℝ)) ∧
      (∑ j, effectMass (F j)) = (Fintype.card (Index κ) : ℝ) := by
  have hcomplete := tree_effect_limit_complete T ea eb report F hlim
  have hpos := tree_effect_limit_posSemidef T ea eb report F hlim
  have hupper := tree_effect_limit_upper T ea eb report F hlim
  refine ⟨hcomplete, ?_, ?_⟩
  · intro j
    have hnonneg := (RCLike.nonneg_iff (K := ℂ)).mp (hpos j).trace_nonneg
    have hbound := (RCLike.nonneg_iff (K := ℂ)).mp (hupper j).trace_nonneg
    simp only [Matrix.trace_sub, Matrix.trace_one, Complex.sub_re, Complex.natCast_re] at hbound
    exact ⟨hpos j, (hpos j).isHermitian, hupper j, hnonneg.1, sub_nonneg.mp hbound.1⟩
  · have h := congrArg (fun M : Matrix (Index κ) (Index κ) ℂ => M.trace.re) hcomplete
    simpa [effectMass, Matrix.trace_sum] using h

end

end QuantumProver.ElegantJointMeasurement.ProtocolEffectLimits
