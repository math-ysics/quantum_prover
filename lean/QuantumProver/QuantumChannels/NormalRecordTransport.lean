import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCostModels

noncomputable section
set_option autoImplicit false

universe u v w z

namespace QuantumProver.ElegantJointMeasurement.NormalRecordTransport

open MeasureTheory Set Function
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess QuantumProver.ElegantJointMeasurement.NormalProcess
open QuantumProver.ElegantJointMeasurement.NormalInstrumentAbsorption QuantumProver.ElegantJointMeasurement.NormalCPInstruments

section Histories

variable {R : Type u} {S : Type v} [MeasurableSpace R] [MeasurableSpace S]

def historyEquiv (e : R ≃ᵐ S) : (n : ℕ) → History R n ≃ᵐ History S n
  | 0 => MeasurableEquiv.ofUniqueOfUnique _ _
  | n + 1 =>
      { toFun h i := e (h i)
        invFun h i := e.symm (h i)
        left_inv h := by funext i; exact e.symm_apply_apply (h i)
        right_inv h := by funext i; exact e.apply_symm_apply (h i)
        measurable_toFun := Measurable.of_eval (fun i => e.measurable.comp (measurable_pi_apply i))
        measurable_invFun := Measurable.of_eval (fun i => e.symm.measurable.comp (measurable_pi_apply i)) }

@[simp] theorem historyEquiv_succ_apply (e : R ≃ᵐ S) (n : ℕ)
    (h : History R (n + 1)) (i : Finset.Iic n) :
    historyEquiv e (n + 1) h i = e (h i) := rfl

@[simp] theorem historyEquiv_succ_symm_apply (e : R ≃ᵐ S) (n : ℕ)
    (h : History S (n + 1)) (i : Finset.Iic n) :
    (historyEquiv e (n + 1)).symm h i = e.symm (h i) := rfl

theorem historyEquiv_append (e : R ≃ᵐ S) (n : ℕ) (h : History R n) (r : R) :
    historyEquiv e (n + 1) (appendHistory n (h, r)) =
      appendHistory n (historyEquiv e n h, e r) := by
  cases n with
  | zero => funext i; rfl
  | succ n =>
    funext i
    by_cases hi : i.val ≤ n
    · simp [historyEquiv, appendHistory, prefixStepEquiv,
        MeasurableEquiv.coe_IicProdIoc, IicProdIoc, MeasurableEquiv.piSingleton, hi] <;> rfl
    · simp [historyEquiv, appendHistory, prefixStepEquiv,
        MeasurableEquiv.coe_IicProdIoc, IicProdIoc, MeasurableEquiv.piSingleton, hi] <;> rfl

theorem historyEquiv_symm_append (e : R ≃ᵐ S) (n : ℕ) (h : History S n) (r : S) :
    (historyEquiv e (n + 1)).symm (appendHistory n (h, r)) =
      appendHistory n ((historyEquiv e n).symm h, e.symm r) := by
  apply (historyEquiv e (n + 1)).injective
  rw [MeasurableEquiv.apply_symm_apply, historyEquiv_append,
    MeasurableEquiv.apply_symm_apply, MeasurableEquiv.apply_symm_apply]

theorem historyEquiv_preimage_singleton (e : R ≃ᵐ S) (n : ℕ) (h : History S n) :
    historyEquiv e n ⁻¹' {h} = {(historyEquiv e n).symm h} := by
  ext x
  simp only [mem_preimage, mem_singleton_iff]
  exact (historyEquiv e n).toEquiv.eq_symm_apply.symm

end Histories

section RawInstrument

variable {F E : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {H : Type w} {K : Type z} {X : Type u} {Y : Type v}
  [MeasurableSpace H] [MeasurableSpace K] [MeasurableSpace X] [MeasurableSpace Y]

def rawInstrumentReindex (P : Instrument F E H X) (f : K → H) (hf : Measurable f)
    (e : X ≃ᵐ Y) : Instrument F E K Y where
  operation h s := P.operation (f h) (e ⁻¹' s)
  empty h := by simpa only [preimage_empty] using P.empty (f h)
  countable_additivity h s hs hd T := by
    have hdis : Pairwise (Disjoint on (fun n => e ⁻¹' s n)) := by
      intro i j hij
      change Disjoint (e ⁻¹' s i) (e ⁻¹' s j)
      rw [disjoint_left]
      intro x hxi hxj
      exact disjoint_left.mp (hd hij) hxi hxj
    simpa only [preimage_iUnion] using P.countable_additivity (f h)
      (fun n => e ⁻¹' s n) (fun n => (hs n).preimage e.measurable) hdis T
  completelyPositive h s hs :=
    P.completelyPositive (f h) (e ⁻¹' s) (hs.preimage e.measurable)
  measurable_coordinate s hs T x y :=
    (P.measurable_coordinate (e ⁻¹' s) (hs.preimage e.measurable) T x y).comp hf
  trace_preserving h T := by
    simpa only [preimage_univ] using P.trace_preserving (f h) T

@[simp] theorem rawInstrumentReindex_operation (P : Instrument F E H X)
    (f : K → H) (hf : Measurable f) (e : X ≃ᵐ Y) (h : K) (s : Set Y) :
    (rawInstrumentReindex P f hf e).operation h s = P.operation (f h) (e ⁻¹' s) := rfl

end RawInstrument

section Processes

variable {a b : ℕ} {R : Type u} {S : Type v}
  [MeasurableSpace R] [MeasurableSpace S]

def recordEquivProcess (P : MatrixProcess a b R) (e : R ≃ᵐ S) : MatrixProcess a b S where
  initialAlice := P.initialAlice
  initialBob := P.initialBob
  alice n := rawInstrumentReindex (P.alice n) (historyEquiv e n).symm
    (historyEquiv e n).symm.measurable e
  bob n := rawInstrumentReindex (P.bob n) (historyEquiv e n).symm
    (historyEquiv e n).symm.measurable e
  aliceTurn n h := P.aliceTurn n ((historyEquiv e n).symm h)
  turn_measurable n := (P.turn_measurable n).comp (historyEquiv e n).symm.measurable

@[simp] theorem recordEquivProcess_initialAlice (P : MatrixProcess a b R) (e : R ≃ᵐ S) :
    (recordEquivProcess P e).initialAlice = P.initialAlice := rfl

@[simp] theorem recordEquivProcess_initialBob (P : MatrixProcess a b R) (e : R ≃ᵐ S) :
    (recordEquivProcess P e).initialBob = P.initialBob := rfl

@[simp] theorem recordEquivProcess_alice_operation (P : MatrixProcess a b R)
    (e : R ≃ᵐ S) (n : ℕ) (h : History S n) (s : Set S) :
    ((recordEquivProcess P e).alice n).operation h s =
      (P.alice n).operation ((historyEquiv e n).symm h) (e ⁻¹' s) := rfl

@[simp] theorem recordEquivProcess_bob_operation (P : MatrixProcess a b R)
    (e : R ≃ᵐ S) (n : ℕ) (h : History S n) (s : Set S) :
    ((recordEquivProcess P e).bob n).operation h s =
      (P.bob n).operation ((historyEquiv e n).symm h) (e ⁻¹' s) := rfl

@[simp] theorem recordEquivProcess_aliceTurn (P : MatrixProcess a b R)
    (e : R ≃ᵐ S) (n : ℕ) (h : History S n) :
    (recordEquivProcess P e).aliceTurn n h =
      P.aliceTurn n ((historyEquiv e n).symm h) := rfl

theorem recordEquivProcess_alice_physical_history (P : MatrixProcess a b R)
    (e : R ≃ᵐ S) (n : ℕ) (h : History R n) (s : Set S) :
    ((recordEquivProcess P e).alice n).operation (historyEquiv e n h) s =
      (P.alice n).operation h (e ⁻¹' s) := by
  simp only [recordEquivProcess_alice_operation, MeasurableEquiv.symm_apply_apply]

theorem recordEquivProcess_bob_physical_history (P : MatrixProcess a b R)
    (e : R ≃ᵐ S) (n : ℕ) (h : History R n) (s : Set S) :
    ((recordEquivProcess P e).bob n).operation (historyEquiv e n h) s =
      (P.bob n).operation h (e ⁻¹' s) := by
  simp only [recordEquivProcess_bob_operation, MeasurableEquiv.symm_apply_apply]

end Processes

def natLiftEquiv : ℕ ≃ᵐ ULift.{u} ℕ := MeasurableEquiv.ulift.symm

theorem liftedNat_standardBorel : StandardBorelSpace (ULift.{u} ℕ) := by infer_instance

theorem liftedNat_countable : Countable (ULift.{u} ℕ) := by infer_instance

def liftNatProcess {a b : ℕ} (P : MatrixProcess a b ℕ) : MatrixProcess a b (ULift.{u} ℕ) :=
  recordEquivProcess P natLiftEquiv

end QuantumProver.ElegantJointMeasurement.NormalRecordTransport
