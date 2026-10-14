import Mathlib

/-!
Finite probability laws, numerical fingerprints, query parameters and register ledgers
for collision finding with a coherent value oracle.
-/

namespace CollisionTradeoff

open scoped BigOperators

/-- An actual finite probability law, specified by nonnegative normalized weights. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

def prob (μ : FiniteLaw Ω) (E : Finset Ω) : ℝ := ∑ ω ∈ E, μ.weight ω

def expect (μ : FiniteLaw Ω) (X : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * X ω

def variance (μ : FiniteLaw Ω) (X : Ω → ℝ) : ℝ :=
  μ.expect (fun ω => (X ω - μ.expect X) ^ 2)

end FiniteLaw

/-- The fixed numerical tag; `B` is a power of two in the construction. -/
def tag (B : ℕ) (y : ℕ) : ℕ := y % B

/-- Table slots are fixed original sample addresses, so no index array is stored. -/
def sampleAddress {r N : ℕ} (hr : r ≤ N) (i : Fin r) : Fin N := i.castLE hr

def tagTable {r N : ℕ} (hr : r ≤ N) (B : ℕ) (f : Fin N → Fin N) : Fin r → ℕ :=
  fun i => tag B (f (sampleAddress hr i)).val

def GoodTable {r : ℕ} (a : Fin r → ℕ) : Prop := Function.Injective a

/-- The finite set scanned by the reversible equality-controlled XOR lookup. -/
def matchingSlots {r : ℕ} (a : Fin r → ℕ) (y : ℕ) : Finset (Fin r) :=
  Finset.univ.filter (fun i => a i = y)

/-- The actual `k`-bit XOR index register, including on a table with duplicates. -/
def scanWord {r : ℕ} (k : ℕ) (a : Fin r → ℕ) (y : ℕ) : BitVec k :=
  (matchingSlots a y).fold (fun u v => u ^^^ v) 0 (fun i => BitVec.ofNat k i.val)

/-- The parity bit produced by toggling once for each tag match. -/
def scanParity {r : ℕ} (a : Fin r → ℕ) (y : ℕ) : Bool :=
  decide ((matchingSlots a y).card % 2 = 1)

/-- Every XOR index is a valid address if the entire `k`-bit register fits the domain. -/
def selectedAddress {r N : ℕ} (k : ℕ) (hk : 2 ^ k ≤ N)
    (a : Fin r → ℕ) (y : ℕ) : Fin N :=
  ⟨(scanWord k a y).toNat, lt_of_lt_of_le (BitVec.isLt _) hk⟩

/-- Exact full-value predicate implemented after the short-tag table scan. -/
def markerPredicate {r N : ℕ} (hr : r ≤ N) (k : ℕ) (hk : 2 ^ k ≤ N)
    (B : ℕ) (f : Fin N → Fin N) (x : Fin N) : Prop :=
  let a := tagTable hr B f
  let y := tag B (f x).val
  GoodTable a ∧ scanParity a y = true ∧ f (selectedAddress k hk a y) = f x

/-- A true collision with a sampled address. Distinctness follows for an outside `x`. -/
def sampleCollision {r N : ℕ} (hr : r ≤ N) (f : Fin N → Fin N) (x : Fin N) : Prop :=
  ∃ i : Fin r, f (sampleAddress hr i) = f x

/-- Fixed query ledger: setup, four queries per clean marker, and final verification. -/
def queryCount (r m : ℕ) : ℕ := 2 * r + 4 * m + 2

/-- A register ledger, not an assertion that an unspecified circuit attains it. -/
def workspaceLedger (r b n C : ℕ) : ℕ := r * b + C * n

/-- Exact natural-number versions of the ceiling-log parameters. -/
def addressWidth (N : ℕ) : ℕ := Nat.clog 2 N

def auxiliaryWidth (N : ℕ) : ℕ := Nat.clog 2 (addressWidth N)

def sampleSize (N : ℕ) : ℕ := addressWidth N / auxiliaryWidth N

def tagWidth (r : ℕ) : ℕ := Nat.clog 2 (64 * r ^ 2)

def indexWidth (r : ℕ) : ℕ := Nat.clog 2 r

/-- The live lookup/response registers in the basis-state calculation. -/
structure MarkerScratch (n k : ℕ) where
  first : BitVec n
  second : BitVec n
  index : BitVec k
  parity : Bool
  deriving DecidableEq

def zeroScratch (n k : ℕ) : MarkerScratch n k := ⟨0, 0, 0, false⟩

/-- One ordinary coherent XOR value-oracle call at the candidate address. -/
def queryCandidate {N n k : ℕ} (f : Fin N → Fin N) (x : Fin N)
    (s : MarkerScratch n k) : MarkerScratch n k :=
  { s with first := s.first ^^^ BitVec.ofNat n (f x).val }

/-- A reversible scan of the retained table, using the response already in data registers. -/
def lookupGate {r n k : ℕ} (a : Fin r → ℕ) (B : ℕ)
    (s : MarkerScratch n k) : MarkerScratch n k :=
  { s with index := s.index ^^^ scanWord k a (tag B s.first.toNat)
           parity := s.parity ^^ scanParity a (tag B s.first.toNat) }

/-- One coherent value-oracle call at the scanned index, valid even on bad tables. -/
def querySelected {N n k : ℕ} (hk : 2 ^ k ≤ N) (f : Fin N → Fin N)
    (s : MarkerScratch n k) : MarkerScratch n k :=
  let j : Fin N := ⟨s.index.toNat, lt_of_lt_of_le s.index.isLt hk⟩
  { s with second := s.second ^^^ BitVec.ofNat n (f j).val }

/-- Scalar sign on a basis vector. It is mathematical bookkeeping, not free storage. -/
def markerSign {n k : ℕ} (F : Bool) (s : MarkerScratch n k) : ℂ :=
  if F = true ∧ s.parity = true ∧ s.first = s.second then -1 else 1

/-- The four-query compute/sign/uncompute sequence on a basis vector.
The table and good-table flag are data supplied at this checkpoint. -/
def cleanMarker {r N n k : ℕ} (hk : 2 ^ k ≤ N) (a : Fin r → ℕ)
    (B : ℕ) (F : Bool) (f : Fin N → Fin N) (x : Fin N)
    (s : MarkerScratch n k) : ℂ × MarkerScratch n k :=
  let s₁ := queryCandidate f x s
  let s₂ := lookupGate a B s₁
  let s₃ := querySelected hk f s₂
  let z := markerSign F s₃
  let s₄ := querySelected hk f s₃
  let s₅ := lookupGate a B s₄
  (z, queryCandidate f x s₅)

end CollisionTradeoff
