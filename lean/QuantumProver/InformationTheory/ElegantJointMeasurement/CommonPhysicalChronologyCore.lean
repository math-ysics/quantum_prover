import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalProcess

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory ProbabilityTheory Set Filter Function InnerProductSpace
open scoped BigOperators Topology ComplexOrder
namespace QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology
open QuantumProver.ElegantJointMeasurement.NormalProcess QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.HilbertNuclearCompression QuantumProver.MatrixNuclearTensor
open QuantumProver.MatrixNuclearKernelTransport
universe u
local instance chronologyCoreNuclearMeasurable (a b : ℕ) :
    MeasurableSpace (Nuclear (PhysicalChoiWorkspace a b)) := borel _
local instance chronologyCoreNuclearBorel (a b : ℕ) :
    BorelSpace (Nuclear (PhysicalChoiWorkspace a b)) := ⟨rfl⟩
section LocalEventTransport

variable {R S : Type u}
  [MeasurableSpace R] [StandardBorelSpace R]
  [MeasurableSpace S] [StandardBorelSpace S]
  {a b : ℕ} [NeZero a] [NeZero b]
  (P : MatrixProcess a b R) (Q : MatrixProcess a b S)
  (e : ℕ → R → S) (he : ∀ n, Measurable (e n))
  (c : (n : ℕ) → History R n → History S n)
  (hc : ∀ n, Measurable (c n))
  (hc0 : ∀ h : History R 0, c 0 h = h)
  (hcAppend : ∀ n (h : History R n) (r : R),
    c (n+1) (appendHistory n (h,r)) = appendHistory n (c n h,e n r))
  (hInitial : P.initialChoiState = Q.initialChoiState)
  (hEvent : ∀ n (h : History R n) (s : Set S), MeasurableSet s →
    (Q.represented_physicalReferenceInstrument n).operation (c n h) s =
      (P.represented_physicalReferenceInstrument n).operation h (e n ⁻¹' s))

include he hc hc0 hcAppend hInitial hEvent

theorem prefix_setIntegral_of_local_events (n : ℕ) (s : Set (History S n))
    (hs : MeasurableSet s) :
    (∫ h in c n ⁻¹' s, P.represented_physicalState n h ∂P.represented_physicalPrefixMeasure n) =
      ∫ h in s, Q.represented_physicalState n h ∂Q.represented_physicalPrefixMeasure n := by
  induction n with
  | zero =>
      have hcid : c 0 = id := funext hc0
      rw [hcid, Set.preimage_id]
      change (∫ _ : PUnit in s, P.initialChoiState ∂Measure.dirac PUnit.unit) =
        ∫ _ : PUnit in s, Q.initialChoiState ∂Measure.dirac PUnit.unit
      rw [hInitial]
  | succ n ih =>
      have hset : ∀ t : Set (History S n), MeasurableSet t →
          (∫ h in c n ⁻¹' t, P.represented_physicalState n h ∂P.represented_physicalPrefixMeasure n) =
            ∫ h in t, Q.represented_physicalState n h ∂Q.represented_physicalPrefixMeasure n := ih
      have hLocal : ∀ h (t : Set S), MeasurableSet t →
          (∫ r in e n ⁻¹' t, P.represented_physicalState (n+1) (appendHistory n (h,r))
            ∂P.represented_physicalBornKernel n h) =
          (Q.represented_physicalReferenceInstrument n).operation (c n h) t (P.represented_physicalState n h) := by
        intro h t ht
        rw [P.represented_physicalState_successor_setIntegral n h (e n ⁻¹' t) (he n ht),
          hEvent n h t ht]
      have hStep := setIntegral_kernel_transport (Q.represented_physicalReferenceInstrument n)
        (hc n) (he n) (P.represented_physicalState_integrable n) (Q.represented_physicalState_integrable n)
        hset (P.represented_physicalBornKernel n) (Q.represented_physicalBornKernel n)
        (P.physicalState_append_integrable n) (Q.physicalState_append_integrable n)
        hLocal (fun h t ht => Q.represented_physicalState_successor_setIntegral n h t ht)
        ((appendHistory (R := S) n) ⁻¹' s)
        (hs.preimage (appendHistory (R := S) n).measurable)
      change (∫ h in c (n+1) ⁻¹' s, P.represented_physicalState (n+1) h
        ∂((P.represented_physicalPrefixMeasure n) ⊗ₘ P.represented_physicalBornKernel n).map (appendHistory n)) =
        ∫ h in s, Q.represented_physicalState (n+1) h
          ∂((Q.represented_physicalPrefixMeasure n) ⊗ₘ Q.represented_physicalBornKernel n).map (appendHistory n)
      rw [setIntegral_map_equiv, setIntegral_map_equiv]
      have hPre : (appendHistory (R := R) n) ⁻¹' (c (n+1) ⁻¹' s) =
          Prod.map (c n) (e n) ⁻¹' ((appendHistory (R := S) n) ⁻¹' s) := by
        ext z
        rcases z with ⟨h,r⟩
        change c (n+1) (appendHistory n (h,r)) ∈ s ↔
          appendHistory n (c n h,e n r) ∈ s
        rw [hcAppend]
      rw [hPre]
      exact hStep

theorem prefixAction_of_local_events (n : ℕ) (s : Set (History S n))
    (hs : MeasurableSet s) (X : JointInputMatrix a b) :
    P.represented_physicalPrefixAction n (c n ⁻¹' s) X = Q.represented_physicalPrefixAction n s X := by
  rw [P.physicalPrefixAction_apply n _ (hc n hs) X,
    Q.physicalPrefixAction_apply n s hs X,
    prefix_setIntegral_of_local_events P Q e he c hc hc0 hcAppend hInitial hEvent n s hs]

theorem prefixMeasure_of_local_events (n : ℕ) :
    (P.represented_physicalPrefixMeasure n).map (c n) = Q.represented_physicalPrefixMeasure n := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (hc n) hs]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have ht := congrArg QuantumProver.HilbertNuclearTrace.trace
    (prefix_setIntegral_of_local_events P Q e he c hc hc0 hcAppend hInitial hEvent n s hs)
  rw [← (QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ)
      (E := PhysicalChoiWorkspace a b)).integral_comp_comm
        (P.represented_physicalState_integrable n).restrict,
    ← (QuantumProver.HilbertNuclearTrace.trace (𝕜 := ℂ)
      (E := PhysicalChoiWorkspace a b)).integral_comp_comm
        (Q.represented_physicalState_integrable n).restrict] at ht
  simp_rw [P.physicalState_trace n, Q.physicalState_trace n] at ht
  have hr := congrArg Complex.re ht
  have hReal (r : ℝ) : (r • (1 : ℂ)).re = r := by
    simp [Algebra.smul_def]
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ,
    hReal] using hr

theorem state_ae_of_local_events (n : ℕ) (hEmbed : MeasurableEmbedding (c n)) :
    (fun h => Q.represented_physicalState n (c n h)) =ᵐ[P.represented_physicalPrefixMeasure n] P.represented_physicalState n := by
  have hInt : Integrable (fun h => Q.represented_physicalState n (c n h)) (P.represented_physicalPrefixMeasure n) := by
    have hi := Q.represented_physicalState_integrable n
    rw [← prefixMeasure_of_local_events P Q e he c hc hc0 hcAppend hInitial hEvent n] at hi
    exact hi.comp_measurable hEmbed.measurable
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hInt (P.represented_physicalState_integrable n)
  intro s hs _
  have h := prefix_setIntegral_of_local_events P Q e he c hc hc0 hcAppend hInitial hEvent
    n (c n '' s) (hEmbed.measurableSet_image' hs)
  rw [hEmbed.injective.preimage_image s,
    ← prefixMeasure_of_local_events P Q e he c hc hc0 hcAppend hInitial hEvent n,
    hEmbed.setIntegral_map, hEmbed.injective.preimage_image s] at h
  exact h.symm

end LocalEventTransport
end QuantumProver.ElegantJointMeasurement.HilbertCommonPhysicalChronology
