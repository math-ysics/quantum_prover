import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.ParallelSchedulerHistory

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

theorem idleCallThenB_eq_constructor (p : ℝ) {a b af bf : ℕ}
    (Q : FiniteProtocol p a b af bf) :
    idleCallThenB p Q =
      .alice (groundPrepareInstrumentB a) (fun _ =>
        .call (.bob (discardQubitInstrumentB b) (fun _ => Q))) := rfl

theorem idleCallsThenB_zero (p : ℝ) {a b af bf : ℕ}
    (Q : FiniteProtocol p a b af bf) : idleCallsThenB p 0 Q = Q := rfl

theorem idleCallsThenB_succ (p : ℝ) {a b af bf : ℕ} (n : ℕ)
    (Q : FiniteProtocol p a b af bf) :
    idleCallsThenB p (n + 1) Q = idleCallThenB p (idleCallsThenB p n Q) := rfl

def idleWordKrausB (p : ℝ) (a b : ℕ) : (n : ℕ) →
    (Fin n → Qubit) → (Fin n → Qubit) → BipartiteMatrix a b
  | 0, _, _ => 1
  | n + 1, r, z => idleWordKrausB p a b n (Fin.tail r) (Fin.tail z) *
      idleCallKrausB p a b (r 0) (z 0)

abbrev IdleGroundWordB {n : ℕ} (r z : Fin n → Qubit) : Prop :=
  ∀ i, r i = 0 ∧ z i = 0

theorem IdleGroundWordB_succ {n : ℕ} (r z : Fin (n + 1) → Qubit) :
    IdleGroundWordB r z ↔ (r 0 = 0 ∧ z 0 = 0) ∧ IdleGroundWordB (Fin.tail r) (Fin.tail z) := by
  simp only [IdleGroundWordB, Fin.forall_fin_succ, Fin.tail]

theorem IdleGroundWordB_iff_unique {n : ℕ} (r z : Fin n → Qubit) :
    IdleGroundWordB r z ↔ r = (fun _ => 0) ∧ z = (fun _ => 0) := by
  constructor
  · intro h
    exact ⟨funext fun i => (h i).1, funext fun i => (h i).2⟩
  · rintro ⟨rfl, rfl⟩
    exact fun _ => ⟨rfl, rfl⟩

theorem idleWordKrausB_eq_identity (p : ℝ) (a b n : ℕ) (r z : Fin n → Qubit) :
    idleWordKrausB p a b n r z = if IdleGroundWordB r z then 1 else 0 := by
  induction n with
  | zero => simp [idleWordKrausB, IdleGroundWordB]
  | succ n ih =>
    rw [idleWordKrausB, ih, idleCallKrausB_eq_identity]
    simp only [IdleGroundWordB_succ]
    by_cases ht : IdleGroundWordB (Fin.tail r) (Fin.tail z)
    · by_cases hh : r 0 = 0 ∧ z 0 = 0
      · simp only [ite_eq_left ht, ite_eq_left hh, ite_eq_left (And.intro hh ht), Matrix.one_mul]
      · have hc : ¬ ((r 0 = 0 ∧ z 0 = 0) ∧ IdleGroundWordB (Fin.tail r) (Fin.tail z)) :=
          fun h => hh h.1
        simp only [ite_eq_left ht, ite_eq_right hh, ite_eq_right hc, Matrix.mul_zero]
    · have hc : ¬ ((r 0 = 0 ∧ z 0 = 0) ∧ IdleGroundWordB (Fin.tail r) (Fin.tail z)) :=
        fun h => ht h.2
      simp only [ite_eq_right ht, ite_eq_right hc, Matrix.zero_mul]

theorem idleWordKrausB_then_eq {p : ℝ} {a b n : ℕ} {I : Type*}
    (K : Matrix I (Fin a × Fin b) ℂ) (r z : Fin n → Qubit) :
    K * idleWordKrausB p a b n r z = if IdleGroundWordB r z then K else 0 := by
  rw [idleWordKrausB_eq_identity]
  by_cases h : IdleGroundWordB r z
  · simp only [ite_eq_left h, Matrix.mul_one]
  · simp only [ite_eq_right h, Matrix.mul_zero]

theorem idleWordKrausB_cross_eq (p : ℝ) {a b n : ℕ}
    (ρ : BipartiteMatrix a b) (r z r' z' : Fin n → Qubit) :
    idleWordKrausB p a b n r z * ρ * (idleWordKrausB p a b n r' z')ᴴ =
      if IdleGroundWordB r z ∧ IdleGroundWordB r' z' then ρ else 0 := by
  rw [idleWordKrausB_eq_identity, idleWordKrausB_eq_identity]
  by_cases h : IdleGroundWordB r z
  · by_cases h' : IdleGroundWordB r' z'
    · simp only [ite_eq_left h, ite_eq_left h', ite_eq_left (And.intro h h'),
        Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    · have hc : ¬ (IdleGroundWordB r z ∧ IdleGroundWordB r' z') := fun hc => h' hc.2
      simp only [ite_eq_left h, ite_eq_right h', ite_eq_right hc, Matrix.conjTranspose_zero,
        Matrix.mul_zero]
  · have hc : ¬ (IdleGroundWordB r z ∧ IdleGroundWordB r' z') := fun hc => h hc.1
    simp only [ite_eq_right h, ite_eq_right hc, Matrix.zero_mul]

inductive UniformPaddingDerivationB (p : ℝ) : (m : ℕ) →
    {a b af bf : ℕ} → FiniteProtocol p a b af bf → FiniteProtocol p a b af bf → Prop
  | done (a b m : ℕ) : UniformPaddingDerivationB p m
      (.done a b) (idleCallsThenB p m (.done a b))
  | alice {a b ao af bf k m : ℕ} (K : KrausInstrument a ao k)
      (P Q : Fin k → FiniteProtocol p ao b af bf)
      (next : ∀ z, UniformPaddingDerivationB p m (P z) (Q z)) :
      UniformPaddingDerivationB p m (.alice K P) (.alice K Q)
  | bob {a b bo af bf k m : ℕ} (K : KrausInstrument b bo k)
      (P Q : Fin k → FiniteProtocol p a bo af bf)
      (next : ∀ z, UniformPaddingDerivationB p m (P z) (Q z)) :
      UniformPaddingDerivationB p m (.bob K P) (.bob K Q)
  | call {a b af bf m : ℕ} (P Q : FiniteProtocol p a (2 * b) af bf)
      (next : UniformPaddingDerivationB p m P Q) :
      UniformPaddingDerivationB p (m + 1) (.call P) (.call Q)

theorem UniformPaddingDerivationB.output_eq {p : ℝ} {a b af bf m : ℕ}
    {P Q : FiniteProtocol p a b af bf} (h : UniformPaddingDerivationB p m P Q) :
    ∀ ρ, Q.output ρ = P.output ρ := by
  induction h with
  | done a b m => intro ρ; exact idleCallsThenB_output p m (.done a b) ρ
  | alice K P Q next ih =>
    intro ρ
    simp only [FiniteProtocol.output]
    exact Finset.sum_congr rfl fun z _ => ih z _
  | bob K P Q next ih =>
    intro ρ
    simp only [FiniteProtocol.output]
    exact Finset.sum_congr rfl fun z _ => ih z _
  | call P Q next ih => intro ρ; exact ih _

theorem UniformPaddingDerivationB.uniform {p : ℝ} {a b af bf m : ℕ}
    {P Q : FiniteProtocol p a b af bf} (h : UniformPaddingDerivationB p m P Q) :
    Q.UniformCallsB m := by
  induction h with
  | done a b m =>
    simpa only [Nat.zero_add] using idleCallsThenB_uniformCalls p (m := 0) m
      (Q := FiniteProtocol.done (p := p) a b) rfl
  | alice K P Q next ih => exact fun z => ih z
  | bob K P Q next ih => exact fun z => ih z
  | call P Q next ih => exact ⟨_, rfl, ih⟩

theorem UniformPaddingDerivationB.calls_le {p : ℝ} {a b af bf m : ℕ}
    {P Q : FiniteProtocol p a b af bf} (h : UniformPaddingDerivationB p m P Q) :
    Q.calls ≤ m := h.uniform.calls_le

theorem FiniteProtocol.exists_uniform_padding_derivationB {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) :
    ∀ m, P.calls ≤ m → ∃ Q : FiniteProtocol p a b af bf,
      UniformPaddingDerivationB p m P Q := by
  induction P with
  | done a b => intro m _; exact ⟨idleCallsThenB p m (.done a b), .done a b m⟩
  | alice K next ih =>
    intro m hm
    have hn : ∀ j, (next j).calls ≤ m := by
      intro j
      exact (Finset.le_sup (f := fun z => (next z).calls) (Finset.mem_univ j)).trans hm
    choose Q hQ using fun j => ih j m (hn j)
    exact ⟨.alice K Q, .alice K next Q hQ⟩
  | bob K next ih =>
    intro m hm
    have hn : ∀ j, (next j).calls ≤ m := by
      intro j
      exact (Finset.le_sup (f := fun z => (next z).calls) (Finset.mem_univ j)).trans hm
    choose Q hQ using fun j => ih j m (hn j)
    exact ⟨.bob K Q, .bob K next Q hQ⟩
  | call next ih =>
    intro m hm
    change next.calls + 1 ≤ m at hm
    rcases ih (m - 1) (by omega) with ⟨Q, hQ⟩
    refine ⟨.call Q, ?_⟩
    have hm' : m - 1 + 1 = m := by omega
    simpa only [hm'] using UniformPaddingDerivationB.call next Q hQ

theorem FiniteProtocol.exists_uniform_padding_with_derivationB {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) (m : ℕ) (hP : P.calls ≤ m) :
    ∃ Q : FiniteProtocol p a b af bf,
      UniformPaddingDerivationB p m P Q ∧ Q.calls ≤ m ∧ Q.UniformCallsB m ∧
      ∀ ρ, Q.output ρ = P.output ρ := by
  rcases P.exists_uniform_padding_derivationB m hP with ⟨Q, hQ⟩
  exact ⟨Q, hQ, hQ.calls_le, hQ.uniform, hQ.output_eq⟩

theorem FiniteProtocol.exists_independent_lanes_with_padding_derivationB
    {p : ℝ} {a b af bf : ℕ} (P : FiniteProtocol p a b af bf)
    (m : ℕ) (hP : P.calls ≤ m) (n : ℕ) :
    ∃ Q : FiniteProtocol p a b af bf,
      UniformPaddingDerivationB p m P Q ∧ Q.calls ≤ m ∧ Q.UniformCallsB m ∧
      (∀ ρ, Q.output ρ = P.output ρ) ∧
      ∃ R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
        (lanePowerDimB n af) (lanePowerDimB n bf),
        IndependentLanesDerivationB p Q n R ∧ R.calls ≤ m ∧ R.UniformCallsB m ∧
        R.represented_toMatrix.calls ≤ (n + 1) * m ∧ ∀ ρ,
        R.output (lanePowerMatrixB ρ n) = lanePowerMatrixB (P.output ρ) n := by
  rcases P.exists_uniform_padding_with_derivationB m hP with ⟨Q, hQ, hC, hU, hO⟩
  rcases Q.exists_uniform_lanes_with_derivationB hU n with ⟨R, hR, hRC, hRU, hN, hRO⟩
  refine ⟨Q, hQ, hC, hU, hO, R, hR, hRC, hRU, hN, ?_⟩
  intro ρ
  rw [hRO, hO]

end QuantumProver.AmplitudeDamping.FiniteModel
