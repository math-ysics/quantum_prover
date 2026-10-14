import QuantumProver.Computability.CollisionTradeoff.Definitions

/-!
Finite register and complex Hilbert-space support.  Every retained register is
included in the basis below.  Cardinality and a fixed encoding into qubits are
proved; neither is used as a substitute for an actual oracle query program or
for proving that such a program stays inside this register set.
-/

namespace CollisionTradeoff

open scoped BigOperators Classical

def markerScratchEquiv (n k : ℕ) :
    MarkerScratch n k ≃ (BitVec n × BitVec n × BitVec k × Bool) where
  toFun s := (s.first, s.second, s.index, s.parity)
  invFun s := ⟨s.1, s.2.1, s.2.2.1, s.2.2.2⟩
  left_inv s := by cases s; rfl
  right_inv s := by rcases s with ⟨a, b, j, p⟩; rfl

noncomputable instance markerScratchFintype (n k : ℕ) : Fintype (MarkerScratch n k) :=
  Fintype.ofEquiv (BitVec n × BitVec n × BitVec k × Bool) (markerScratchEquiv n k).symm

theorem bitVec_card_exp (w : ℕ) : Fintype.card (BitVec w) = 2 ^ w := by
  simpa using Fintype.card_congr (BitVec.equivFin (m := w)).toEquiv

theorem markerScratch_card (n k : ℕ) :
    Fintype.card (MarkerScratch n k) = 2 ^ (2 * n + k + 1) := by
  rw [Fintype.card_congr (markerScratchEquiv n k)]
  simp only [Fintype.card_prod, bitVec_card_exp, Fintype.card_bool]
  rw [show 2 * n = n + n by omega]
  simp only [pow_add, pow_one]
  ring

/-- A complete retained register basis, including a separate physical oracle port. -/
structure CollisionRegisters (r b n k c : ℕ) where
  table : Fin r → BitVec b
  good : Bool
  mainAddress : BitVec n
  physicalOracleAddress : BitVec n
  scratch : MarkerScratch n k
  controller : BitVec c
  outputFirst : BitVec n
  outputSecond : BitVec n
  outputValid : Bool
  deriving DecidableEq

def collisionRegistersEquiv (r b n k c : ℕ) :
    CollisionRegisters r b n k c ≃
      ((Fin r → BitVec b) × Bool × BitVec n × BitVec n ×
        MarkerScratch n k × BitVec c × BitVec n × BitVec n × Bool) where
  toFun s := (s.table, s.good, s.mainAddress, s.physicalOracleAddress,
    s.scratch, s.controller, s.outputFirst, s.outputSecond, s.outputValid)
  invFun s :=
    { table := s.1
      good := s.2.1
      mainAddress := s.2.2.1
      physicalOracleAddress := s.2.2.2.1
      scratch := s.2.2.2.2.1
      controller := s.2.2.2.2.2.1
      outputFirst := s.2.2.2.2.2.2.1
      outputSecond := s.2.2.2.2.2.2.2.1
      outputValid := s.2.2.2.2.2.2.2.2 }
  left_inv s := by cases s; rfl
  right_inv s := by rcases s with ⟨a, g, x, q, t, j, u, v, ok⟩; rfl

noncomputable instance collisionRegistersFintype (r b n k c : ℕ) :
    Fintype (CollisionRegisters r b n k c) :=
  Fintype.ofEquiv _ (collisionRegistersEquiv r b n k c).symm

/-- Table bits; six n-bit fields; lookup index; controller; three retained flags. -/
def registerWidth (r b n k c : ℕ) : ℕ := r * b + 6 * n + k + c + 3

theorem collisionRegisters_card (r b n k c : ℕ) :
    Fintype.card (CollisionRegisters r b n k c) = 2 ^ registerWidth r b n k c := by
  rw [Fintype.card_congr (collisionRegistersEquiv r b n k c)]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    bitVec_card_exp, Fintype.card_bool, markerScratch_card, registerWidth]
  rw [← pow_mul, Nat.mul_comm b r]
  rw [show 6 * n = n + n + n + n + n + n by omega,
    show 2 * n = n + n by omega]
  simp only [pow_add, pow_succ, pow_one]
  ring

/-- This static encoding is independent of the oracle function. -/
noncomputable def collisionRegisterEncoding (r b n k c : ℕ) :
    CollisionRegisters r b n k c ≃ BitVec (registerWidth r b n k c) :=
  Fintype.equivOfCardEq
    ((collisionRegisters_card r b n k c).trans (bitVec_card_exp _).symm)

theorem registerWidth_bound {r b n k : ℕ} (hk : k ≤ n) (hn : 1 ≤ n) :
    registerWidth r b n k (4 * n) ≤ r * b + 14 * n := by
  unfold registerWidth
  omega

/-- A finite basis relabeling acts on actual complex amplitudes as an isometry. -/
noncomputable def basisEquivUnitary {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ β :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

theorem basisEquivUnitary_apply {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (v : EuclideanSpace ℂ α) (y : β) :
    basisEquivUnitary e v y = v (e.symm y) := rfl

theorem basisEquivUnitary_single {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (x : α) (z : ℂ) :
    basisEquivUnitary e (PiLp.single 2 x z) = PiLp.single 2 (e x) z :=
  LinearIsometryEquiv.piLpCongrLeft_single e x z

theorem basisEquivUnitary_norm {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (v : EuclideanSpace ℂ α) : ‖basisEquivUnitary e v‖ = ‖v‖ :=
  (basisEquivUnitary e).norm_map v

theorem basisEquivUnitary_trans {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] (e : α ≃ β) (d : β ≃ γ) :
    (basisEquivUnitary e).trans (basisEquivUnitary d) = basisEquivUnitary (e.trans d) := by
  ext v y
  rfl

def involutionBasisEquiv {α : Type*} (g : α → α) (hg : Function.Involutive g) : α ≃ α where
  toFun := g
  invFun := g
  left_inv := hg
  right_inv := hg

noncomputable def involutionBasisUnitary {α : Type*} [Fintype α]
    (g : α → α) (hg : Function.Involutive g) :
    EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α :=
  basisEquivUnitary (involutionBasisEquiv g hg)

theorem involutionBasisUnitary_apply {α : Type*} [Fintype α]
    (g : α → α) (hg : Function.Involutive g) (v : EuclideanSpace ℂ α) (x : α) :
    involutionBasisUnitary g hg v x = v (g x) := rfl

theorem involutionBasisUnitary_involutive {α : Type*} [Fintype α]
    (g : α → α) (hg : Function.Involutive g) :
    Function.Involutive (involutionBasisUnitary g hg) := by
  intro v
  ext x
  change v (g (g x)) = v x
  rw [hg]

/-- The complete finite frame has an actual fixed complex qubit-space encoding. -/
noncomputable def collisionRegisterHilbertEncoding (r b n k c : ℕ) :
    EuclideanSpace ℂ (CollisionRegisters r b n k c) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (BitVec (registerWidth r b n k c)) :=
  basisEquivUnitary (collisionRegisterEncoding r b n k c)

end CollisionTradeoff
