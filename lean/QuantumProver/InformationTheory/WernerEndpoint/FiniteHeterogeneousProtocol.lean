import Mathlib
import QuantumProver.InformationTheory.WernerEndpoint.OperationalEndpointCost
import QuantumProver.InformationTheory.ElegantJointMeasurement.IConcurrence

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace QuantumProver.WernerEndpoint.FiniteHeterogeneousProtocol

open OperationalEndpointCost Matrix
open scoped BigOperators Kronecker

abbrev JointMatrix (a b : ℕ) := Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ
abbrev DecoderIndex (P : ℕ) := Fin (Fintype.card (Unit ⊕ Fin P))

def decoderKraus {p P : ℕ} (hp : 0 < p) (h : p ≤ P) :
    DecoderIndex P → Matrix (Fin p) (Fin P) ℂ :=
  fun k => QuantumProver.ElegantJointMeasurement.CP.unpadKraus hp h ((Fintype.equivFin (Unit ⊕ Fin P)).symm k)

theorem decoderKraus_complete {p P : ℕ} (hp : 0 < p) (h : p ≤ P) :
    ∑ k, (decoderKraus hp h k).conjTranspose * decoderKraus hp h k = 1 := by
  simp only [decoderKraus]
  rw [(Fintype.equivFin (Unit ⊕ Fin P)).symm.sum_comp
    (fun q => (QuantumProver.ElegantJointMeasurement.CP.unpadKraus hp h q).conjTranspose * QuantumProver.ElegantJointMeasurement.CP.unpadKraus hp h q)]
  exact QuantumProver.ElegantJointMeasurement.CP.unpadKraus_complete hp h

theorem decoder_alice_recover {p P b : ℕ} (hp : 0 < p) (h : p ≤ P)
    (ρ : JointMatrix p b) :
    (∑ k, (decoderKraus hp h k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) *
      ((QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * ρ *
        (QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose) *
      (decoderKraus hp h k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose) = ρ := by
  simp only [decoderKraus]
  rw [(Fintype.equivFin (Unit ⊕ Fin P)).symm.sum_comp (fun q =>
    (QuantumProver.ElegantJointMeasurement.CP.unpadKraus hp h q ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) *
      ((QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * ρ *
        (QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose) *
      (QuantumProver.ElegantJointMeasurement.CP.unpadKraus hp h q ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose)]
  simp_rw [QuantumProver.ElegantJointMeasurement.CP.kraus_sandwich_comp, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [Fintype.sum_sum_type]
  simp only [QuantumProver.ElegantJointMeasurement.CP.unpadKraus, Fintype.sum_unique, QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix_isometry,
    QuantumProver.ElegantJointMeasurement.CP.unpadFallback_mul_inclusion, Matrix.one_kronecker_one,
    Matrix.zero_kronecker, Matrix.one_mul, Matrix.conjTranspose_one,
    Matrix.mul_one, Matrix.zero_mul, Matrix.conjTranspose_zero, Matrix.mul_zero,
    Finset.sum_const_zero, add_zero]

theorem decoder_bob_recover {p P a : ℕ} (hp : 0 < p) (h : p ≤ P)
    (ρ : JointMatrix a p) :
    (∑ k, ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ decoderKraus hp h k) *
      (((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h) * ρ *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h).conjTranspose) *
      ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ decoderKraus hp h k).conjTranspose) = ρ := by
  simp only [decoderKraus]
  rw [(Fintype.equivFin (Unit ⊕ Fin P)).symm.sum_comp (fun q =>
    ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ QuantumProver.ElegantJointMeasurement.CP.unpadKraus hp h q) *
      (((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h) * ρ *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h).conjTranspose) *
      ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ QuantumProver.ElegantJointMeasurement.CP.unpadKraus hp h q).conjTranspose)]
  simp_rw [QuantumProver.ElegantJointMeasurement.CP.kraus_sandwich_comp, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [Fintype.sum_sum_type]
  simp only [QuantumProver.ElegantJointMeasurement.CP.unpadKraus, Fintype.sum_unique, QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix_isometry,
    QuantumProver.ElegantJointMeasurement.CP.unpadFallback_mul_inclusion, Matrix.one_kronecker_one,
    Matrix.kronecker_zero, Matrix.one_mul, Matrix.conjTranspose_one,
    Matrix.mul_one, Matrix.zero_mul, Matrix.conjTranspose_zero, Matrix.mul_zero,
    Finset.sum_const_zero, add_zero]

def prepare {c d a b : ℕ} (hc : 0 < c) (hd : 0 < d) :
    FiniteLocalProtocol c d a b :=
  .alice (fun (_ : Fin 1) (k : Fin a) => QuantumProver.ElegantJointMeasurement.CP.resetRow hc k)
    (by simpa only [Fin.sum_univ_one] using (QuantumProver.ElegantJointMeasurement.CP.resetRow_complete (m := a) hc))
    (fun _ => .bob (fun (_ : Fin 1) (k : Fin b) => QuantumProver.ElegantJointMeasurement.CP.resetRow hd k)
      (by simpa only [Fin.sum_univ_one] using (QuantumProver.ElegantJointMeasurement.CP.resetRow_complete (m := b) hd))
      (fun _ => .terminal (1 : Matrix (Fin c) (Fin c) ℂ)
        (1 : Matrix (Fin d) (Fin d) ℂ) (by simp) (by simp)))

@[simp] theorem protocol_apply_zero {c d a b : ℕ} (T : FiniteLocalProtocol c d a b) :
    T.apply (0 : JointMatrix a b) = 0 := map_zero T.toLinearMap

def unpadAlice {c d p P b : ℕ} (T : FiniteLocalProtocol c d p b)
    (hp : 0 < p) (h : p ≤ P) : FiniteLocalProtocol c d P b :=
  .alice (fun (_ : Fin 1) k => decoderKraus hp h k)
    (by simpa only [Fin.sum_univ_one] using decoderKraus_complete hp h)
    (fun _ => T)

def unpadBob {c d p P a : ℕ} (T : FiniteLocalProtocol c d a p)
    (hp : 0 < p) (h : p ≤ P) : FiniteLocalProtocol c d a P :=
  .bob (fun (_ : Fin 1) k => decoderKraus hp h k)
    (by simpa only [Fin.sum_univ_one] using decoderKraus_complete hp h)
    (fun _ => T)

theorem unpadAlice_apply {c d p P b : ℕ} (T : FiniteLocalProtocol c d p b)
    (hp : 0 < p) (h : p ≤ P) (ρ : JointMatrix p b) :
    (unpadAlice T hp h).apply
      ((QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * ρ *
        (QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose) =
      T.apply ρ := by
  rw [unpadAlice, FiniteLocalProtocol.apply]
  simp only [Fin.sum_univ_one]
  rw [decoder_alice_recover]

theorem unpadBob_apply {c d p P a : ℕ} (T : FiniteLocalProtocol c d a p)
    (hp : 0 < p) (h : p ≤ P) (ρ : JointMatrix a p) :
    (unpadBob T hp h).apply
      (((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h) * ρ *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h).conjTranspose) =
      T.apply ρ := by
  rw [unpadBob, FiniteLocalProtocol.apply]
  simp only [Fin.sum_univ_one]
  rw [decoder_bob_recover]

def padAliceContinuation {c d p P b : ℕ} (T : FiniteLocalProtocol c d p b)
    (hc : 0 < c) (hd : 0 < d) (h : p ≤ P) : FiniteLocalProtocol c d P b :=
  if hp : 0 < p then unpadAlice T hp h else prepare hc hd

def padBobContinuation {c d p P a : ℕ} (T : FiniteLocalProtocol c d a p)
    (hc : 0 < c) (hd : 0 < d) (h : p ≤ P) : FiniteLocalProtocol c d a P :=
  if hp : 0 < p then unpadBob T hp h else prepare hc hd

theorem padAliceContinuation_apply {c d p P b : ℕ} (T : FiniteLocalProtocol c d p b)
    (hc : 0 < c) (hd : 0 < d) (h : p ≤ P) (ρ : JointMatrix p b) :
    (padAliceContinuation T hc hd h).apply
      ((QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * ρ *
        (QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose) =
      T.apply ρ := by
  by_cases hp : 0 < p
  · rw [padAliceContinuation, dite_eq_left hp]
    exact unpadAlice_apply T hp h ρ
  · have hp0 : p = 0 := Nat.eq_zero_of_not_pos hp
    subst p
    have hρ : ρ = 0 := by ext x y; exact Fin.elim0 x.1
    simp only [hρ, Matrix.mul_zero, Matrix.zero_mul, protocol_apply_zero]

theorem padBobContinuation_apply {c d p P a : ℕ} (T : FiniteLocalProtocol c d a p)
    (hc : 0 < c) (hd : 0 < d) (h : p ≤ P) (ρ : JointMatrix a p) :
    (padBobContinuation T hc hd h).apply
      (((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h) * ρ *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix h).conjTranspose) =
      T.apply ρ := by
  by_cases hp : 0 < p
  · rw [padBobContinuation, dite_eq_left hp]
    exact unpadBob_apply T hp h ρ
  · have hp0 : p = 0 := Nat.eq_zero_of_not_pos hp
    subst p
    have hρ : ρ = 0 := by ext x y; exact Fin.elim0 x.2
    simp only [hρ, Matrix.mul_zero, Matrix.zero_mul, protocol_apply_zero]

def paddedKraus {h a : ℕ} (p : Fin h → ℕ)
    (K : ∀ j, Matrix (Fin (p j)) (Fin a) ℂ) (j : Fin h) :
    Matrix (Fin (QuantumProver.ElegantJointMeasurement.CP.commonOutputDimension p)) (Fin a) ℂ :=
  QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix (QuantumProver.ElegantJointMeasurement.CP.le_commonOutputDimension p j) * K j

theorem paddedKraus_gram {h a : ℕ} (p : Fin h → ℕ)
    (K : ∀ j, Matrix (Fin (p j)) (Fin a) ℂ) (j : Fin h) :
    (paddedKraus p K j).conjTranspose * paddedKraus p K j = (K j).conjTranspose * K j := by
  calc
    _ = (K j).conjTranspose *
        ((QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix (QuantumProver.ElegantJointMeasurement.CP.le_commonOutputDimension p j)).conjTranspose *
          QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix (QuantumProver.ElegantJointMeasurement.CP.le_commonOutputDimension p j)) * K j := by
      simp only [paddedKraus, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix_isometry, Matrix.mul_one]

theorem paddedKraus_complete {h a : ℕ} (p : Fin h → ℕ)
    (K : ∀ j, Matrix (Fin (p j)) (Fin a) ℂ)
    (hK : ∑ j, (K j).conjTranspose * K j = 1) :
    ∑ j, (paddedKraus p K j).conjTranspose * paddedKraus p K j = 1 := by
  simp_rw [paddedKraus_gram]
  exact hK

def aliceNode {h a b c d : ℕ} (hc : 0 < c) (hd : 0 < d) (p : Fin h → ℕ)
    (K : ∀ j, Matrix (Fin (p j)) (Fin a) ℂ)
    (hK : ∑ j, (K j).conjTranspose * K j = 1)
    (next : ∀ j, FiniteLocalProtocol c d (p j) b) : FiniteLocalProtocol c d a b :=
  .alice (fun j (_ : Fin 1) => paddedKraus p K j)
    (by simpa only [Fin.sum_univ_one] using paddedKraus_complete p K hK)
    (fun j => padAliceContinuation (next j) hc hd (QuantumProver.ElegantJointMeasurement.CP.le_commonOutputDimension p j))

def bobNode {h a b c d : ℕ} (hc : 0 < c) (hd : 0 < d) (p : Fin h → ℕ)
    (K : ∀ j, Matrix (Fin (p j)) (Fin b) ℂ)
    (hK : ∑ j, (K j).conjTranspose * K j = 1)
    (next : ∀ j, FiniteLocalProtocol c d a (p j)) : FiniteLocalProtocol c d a b :=
  .bob (fun j (_ : Fin 1) => paddedKraus p K j)
    (by simpa only [Fin.sum_univ_one] using paddedKraus_complete p K hK)
    (fun j => padBobContinuation (next j) hc hd (QuantumProver.ElegantJointMeasurement.CP.le_commonOutputDimension p j))

theorem aliceNode_apply {h a b c d : ℕ} (hc : 0 < c) (hd : 0 < d) (p : Fin h → ℕ)
    (K : ∀ j, Matrix (Fin (p j)) (Fin a) ℂ)
    (hK : ∑ j, (K j).conjTranspose * K j = 1)
    (next : ∀ j, FiniteLocalProtocol c d (p j) b) (ρ : JointMatrix a b) :
    (aliceNode hc hd p K hK next).apply ρ =
      ∑ j, (next j).apply ((K j ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * ρ *
        (K j ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose) := by
  rw [aliceNode, FiniteLocalProtocol.apply]
  simp only [Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intro j _
  have hj : paddedKraus p K j ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ) =
      (QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix (QuantumProver.ElegantJointMeasurement.CP.le_commonOutputDimension p j) ⊗ₖ
        (1 : Matrix (Fin b) (Fin b) ℂ)) *
      (K j ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
    rfl
  rw [hj, ← QuantumProver.ElegantJointMeasurement.CP.kraus_sandwich_comp]
  exact padAliceContinuation_apply (next j) hc hd (QuantumProver.ElegantJointMeasurement.CP.le_commonOutputDimension p j) _

theorem bobNode_apply {h a b c d : ℕ} (hc : 0 < c) (hd : 0 < d) (p : Fin h → ℕ)
    (K : ∀ j, Matrix (Fin (p j)) (Fin b) ℂ)
    (hK : ∑ j, (K j).conjTranspose * K j = 1)
    (next : ∀ j, FiniteLocalProtocol c d a (p j)) (ρ : JointMatrix a b) :
    (bobNode hc hd p K hK next).apply ρ =
      ∑ j, (next j).apply (((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j) * ρ *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j).conjTranspose) := by
  rw [bobNode, FiniteLocalProtocol.apply]
  simp only [Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ paddedKraus p K j =
      ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ
        QuantumProver.ElegantJointMeasurement.CP.inclusionMatrix (QuantumProver.ElegantJointMeasurement.CP.le_commonOutputDimension p j)) *
      ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
    rfl
  rw [hj, ← QuantumProver.ElegantJointMeasurement.CP.kraus_sandwich_comp]
  exact padBobContinuation_apply (next j) hc hd (QuantumProver.ElegantJointMeasurement.CP.le_commonOutputDimension p j) _

theorem exists_aliceNode_allComplex {h a b c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (p : Fin h → ℕ) (K : ∀ j, Matrix (Fin (p j)) (Fin a) ℂ)
    (hK : ∑ j, (K j).conjTranspose * K j = 1)
    (next : ∀ j, FiniteLocalProtocol c d (p j) b) :
    ∃ U : FiniteLocalProtocol c d a b, ∀ ρ : JointMatrix a b,
      U.apply ρ = ∑ j, (next j).apply ((K j ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * ρ *
        (K j ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose) :=
  ⟨aliceNode hc hd p K hK next, aliceNode_apply hc hd p K hK next⟩

theorem exists_bobNode_allComplex {h a b c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (p : Fin h → ℕ) (K : ∀ j, Matrix (Fin (p j)) (Fin b) ℂ)
    (hK : ∑ j, (K j).conjTranspose * K j = 1)
    (next : ∀ j, FiniteLocalProtocol c d a (p j)) :
    ∃ U : FiniteLocalProtocol c d a b, ∀ ρ : JointMatrix a b,
      U.apply ρ = ∑ j, (next j).apply (((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j) * ρ *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j).conjTranspose) :=
  ⟨bobNode hc hd p K hK next, bobNode_apply hc hd p K hK next⟩

end QuantumProver.WernerEndpoint.FiniteHeterogeneousProtocol
