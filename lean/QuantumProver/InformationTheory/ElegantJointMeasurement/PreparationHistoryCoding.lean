import QuantumProver.QuantumChannels.NormalFreePreparationChronology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace QuantumProver.ElegantJointMeasurement.HilbertPreparationHistoryCoding

open MeasureTheory Set Function Preorder
open QuantumProver.ElegantJointMeasurement.HilbertSquareProcess (History appendHistory firstRecordEquiv prefixStepEquiv)
open QuantumProver.MatrixNormalFreePreparationChronology
  (PreparationRecord padHistory padHistory_append)

universe u
variable {R : Type u} [MeasurableSpace R]

private theorem prefixStepEquiv_le (n : ℕ)
    (h : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.Prefix R n) (r : R)
    (i : Finset.Iic (n+1)) (hi : i.val ≤ n) :
    prefixStepEquiv n (h,r) i = h ⟨i.val, Finset.mem_Iic.mpr hi⟩ := by
  simp only [prefixStepEquiv, MeasurableEquiv.coe_trans, Function.comp_apply,
    MeasurableEquiv.coe_IicProdIoc, _root_.IicProdIoc, hi, ↓reduceDIte]
  rfl

private theorem prefixStepEquiv_last (n : ℕ)
    (h : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.Prefix R n) (r : R) :
    prefixStepEquiv n (h,r) ⟨n+1, Finset.mem_Iic.mpr (by omega)⟩ = r := by
  simp only [prefixStepEquiv, MeasurableEquiv.coe_trans, Function.comp_apply,
    MeasurableEquiv.coe_IicProdIoc, _root_.IicProdIoc, Nat.not_succ_le_self,
    ↓reduceDIte]
  rfl

theorem padHistory_physical_coordinate (n : ℕ)
    (h : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.Prefix R n) (i : Finset.Iic n) :
    padHistory (n+1) h ⟨i.val+2, Finset.mem_Iic.mpr (by
      have hi := Finset.mem_Iic.mp i.property
      omega)⟩ = Sum.inr (h i) := by
  induction n with
  | zero =>
      have hi : i = ⟨0, by simp⟩ := Subtype.ext
        (Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property))
      subst i
      rfl
  | succ n ih =>
      let z := (appendHistory (R := R) (n+1)).symm h
      have hz : appendHistory (n+1) z = h := (appendHistory (n+1)).apply_symm_apply h
      rw [← hz, padHistory_append]
      simp only [appendHistory]
      by_cases hi : i.val ≤ n
      · have hi' : i.val+2 ≤ n+2 := by omega
        rw [prefixStepEquiv_le (n+2) _ _ _ hi', prefixStepEquiv_le n _ _ _ hi]
        exact ih z.1 ⟨i.val, Finset.mem_Iic.mpr hi⟩
      · have hv : i.val = n+1 := by
          have hip := Finset.mem_Iic.mp i.property
          omega
        have he : i = ⟨n+1, by simp⟩ := Subtype.ext hv
        subst i
        rw [prefixStepEquiv_last, prefixStepEquiv_last]
        rfl

def physicalRecord (r0 : R) : PreparationRecord R → R :=
  Sum.elim (fun _ => r0) id

omit [MeasurableSpace R] in
@[simp] theorem physicalRecord_inr (r0 r : R) :
    physicalRecord r0 (Sum.inr r) = r := rfl

theorem measurable_physicalRecord (r0 : R) : Measurable (physicalRecord r0) :=
  measurable_const.sumElim measurable_id

def dropPrefix (r0 : R) (n : ℕ)
    (h : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.Prefix (PreparationRecord R) (n+2)) :
    QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.Prefix R n :=
  fun i => physicalRecord r0 (h ⟨i.val+2, Finset.mem_Iic.mpr (by
    have hi := Finset.mem_Iic.mp i.property
    omega)⟩)

theorem measurable_dropPrefix (r0 : R) (n : ℕ) :
    Measurable (dropPrefix r0 n) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_physicalRecord r0).comp (measurable_pi_apply _)

@[simp] theorem dropPrefix_padHistory (r0 : R) (n : ℕ)
    (h : QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.Prefix R n) :
    dropPrefix r0 n (padHistory (n+1) h) = h := by
  funext i
  simp only [dropPrefix, padHistory_physical_coordinate, physicalRecord_inr]

def dropHistory (r0 : R) :
    (n : ℕ) → History (PreparationRecord R) (n+2) → History R n
  | 0, _ => PUnit.unit
  | n+1, h => dropPrefix r0 n h

theorem measurable_dropHistory (r0 : R) (n : ℕ) :
    Measurable (dropHistory r0 n) := by
  cases n with
  | zero => exact measurable_const
  | succ n => exact measurable_dropPrefix r0 n

@[simp] theorem dropHistory_padHistory (r0 : R) (n : ℕ) (h : History R n) :
    dropHistory r0 n (padHistory n h) = h := by
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n => exact dropPrefix_padHistory r0 n h

end QuantumProver.ElegantJointMeasurement.HilbertPreparationHistoryCoding
