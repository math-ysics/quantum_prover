import QuantumProver.Computability.CollisionTradeoff.PaddedAddress

/-!
The explicit n-bit XOR value oracle, acting through one charged physical port.
Valid explicit addresses use the original f:Fin N -> Fin N; invalid addresses
have zero response and identity action.  All-basis permutation/unitarity and
source agreement are derived.  These are oracle semantics, not a complete
algorithm, a free f-dependent gate, or a query/space cost certificate.
-/

namespace CollisionTradeoff

open scoped BigOperators Classical

/-- The zero extension of the original function's value word. -/
def registerOracleValue {N n : ℕ} (f : Fin N → Fin N) (x : BitVec n) : BitVec n :=
  if hx : x.toNat < N then BitVec.ofNat n (f ⟨x.toNat, hx⟩).val else 0

theorem registerOracleValue_valid {N n : ℕ} (f : Fin N → Fin N)
    (x : BitVec n) (hx : x.toNat < N) :
    registerOracleValue f x = BitVec.ofNat n (f ⟨x.toNat, hx⟩).val := by
  simp [registerOracleValue, hx]

theorem registerOracleValue_invalid {N n : ℕ} (f : Fin N → Fin N)
    (x : BitVec n) (hx : N ≤ x.toNat) : registerOracleValue f x = 0 := by
  simp [registerOracleValue, not_lt_of_ge hx]

theorem sourceAddress_toNat {N n : ℕ} (hn : N ≤ 2 ^ n) (x : Fin N) :
    (BitVec.ofNat n x.val).toNat = x.val := by
  simp [Nat.mod_eq_of_lt (lt_of_lt_of_le x.isLt hn)]

theorem sourceAddress_injective {N n : ℕ} (hn : N ≤ 2 ^ n) :
    Function.Injective (fun x : Fin N => BitVec.ofNat n x.val) := by
  intro x y h
  apply Fin.ext
  have hv := congrArg BitVec.toNat h
  simpa only [sourceAddress_toNat hn] using hv

def sourceAddressEmbedding {N n : ℕ} (hn : N ≤ 2 ^ n) : Fin N ↪ BitVec n :=
  ⟨fun x => BitVec.ofNat n x.val, sourceAddress_injective hn⟩

theorem registerOracleValue_encoded {N n : ℕ} (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) (x : Fin N) :
    registerOracleValue f (BitVec.ofNat n x.val) = BitVec.ofNat n (f x).val := by
  have hx : (BitVec.ofNat n x.val).toNat < N := by
    rw [sourceAddress_toNat hn]
    exact x.isLt
  rw [registerOracleValue_valid f _ hx]
  have he : (⟨(BitVec.ofNat n x.val).toNat, hx⟩ : Fin N) = x := by
    apply Fin.ext
    exact sourceAddress_toNat hn x
  rw [he]

theorem registerOracleValue_outside {N r n : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) (i : Fin (N - r)) :
    registerOracleValue f (outsideBitEmbedding hrN hn i) =
      BitVec.ofNat n (f (outsideAddress hrN i)).val := by
  exact registerOracleValue_encoded hn f (outsideAddress hrN i)

def sourceXorOracle {N n : ℕ} (f : Fin N → Fin N)
    (p : Fin N × BitVec n) : Fin N × BitVec n :=
  (p.1, p.2 ^^^ BitVec.ofNat n (f p.1).val)

def registerXorOracle {N n : ℕ} (f : Fin N → Fin N)
    (p : BitVec n × BitVec n) : BitVec n × BitVec n :=
  (p.1, p.2 ^^^ registerOracleValue f p.1)

theorem sourceXorOracle_involutive {N n : ℕ} (f : Fin N → Fin N) :
    Function.Involutive (sourceXorOracle (n := n) f) := by
  intro p
  cases p
  simp [sourceXorOracle, xor_cancel_right]

theorem registerXorOracle_involutive {N n : ℕ} (f : Fin N → Fin N) :
    Function.Involutive (registerXorOracle (n := n) f) := by
  intro p
  cases p
  simp [registerXorOracle, xor_cancel_right]

def registerXorOracleEquiv {N n : ℕ} (f : Fin N → Fin N) :
    (BitVec n × BitVec n) ≃ (BitVec n × BitVec n) :=
  involutionBasisEquiv (registerXorOracle f) (registerXorOracle_involutive f)

noncomputable def sourceXorOracleUnitary {N n : ℕ} (f : Fin N → Fin N) :
    EuclideanSpace ℂ (Fin N × BitVec n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N × BitVec n) :=
  involutionBasisUnitary (sourceXorOracle f) (sourceXorOracle_involutive f)

noncomputable def registerXorOracleUnitary {N n : ℕ} (f : Fin N → Fin N) :
    EuclideanSpace ℂ (BitVec n × BitVec n) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (BitVec n × BitVec n) :=
  involutionBasisUnitary (registerXorOracle f) (registerXorOracle_involutive f)

theorem registerXorOracleUnitary_single {N n : ℕ} (f : Fin N → Fin N)
    (p : BitVec n × BitVec n) (z : ℂ) :
    registerXorOracleUnitary f (PiLp.single 2 p z) =
      PiLp.single 2 (registerXorOracle f p) z :=
  basisEquivUnitary_single _ p z

theorem registerXorOracle_invalid {N n : ℕ} (f : Fin N → Fin N)
    (x y : BitVec n) (hx : N ≤ x.toNat) : registerXorOracle f (x, y) = (x, y) := by
  simp [registerXorOracle, registerOracleValue_invalid f x hx]

def sourcePortEmbedding {N n : ℕ} (hn : N ≤ 2 ^ n) :
    (Fin N × BitVec n) ↪ (BitVec n × BitVec n) :=
  (sourceAddressEmbedding hn).prodMap (Function.Embedding.refl (BitVec n))

theorem registerXorOracle_source {N n : ℕ} (hn : N ≤ 2 ^ n) (f : Fin N → Fin N)
    (p : Fin N × BitVec n) :
    registerXorOracle f (sourcePortEmbedding hn p) =
      sourcePortEmbedding hn (sourceXorOracle f p) := by
  cases p
  simp [registerXorOracle, sourceXorOracle, sourcePortEmbedding,
    sourceAddressEmbedding, registerOracleValue_encoded hn]

/-- A basis involution compatible with an injection preserves its zero extension. -/
theorem involutionBasisUnitary_pad {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) (g : α → α) (hg : Function.Involutive g)
    (h : β → β) (hh : Function.Involutive h) (he : ∀ a, h (e a) = e (g a))
    (v : EuclideanSpace ℂ α) :
    involutionBasisUnitary h hh (finiteAddressPad e v) =
      finiteAddressPad e (involutionBasisUnitary g hg v) := by
  ext b
  rw [involutionBasisUnitary_apply]
  by_cases hb : b ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hb
    rw [he, finiteAddressPad_at, finiteAddressPad_at, involutionBasisUnitary_apply]
  · have hhbr : h b ∉ Set.range e := by
      intro hc
      obtain ⟨a, ha⟩ := hc
      have hback : e (g a) = b := by
        calc
          e (g a) = h (e a) := (he a).symm
          _ = h (h b) := congrArg h ha
          _ = b := hh b
      exact hb ⟨g a, hback⟩
    rw [finiteAddressPad_off e _ (h b) hhbr, finiteAddressPad_off e _ b hb]

/-- The explicit oracle agrees with the original source on all embedded amplitudes. -/
theorem registerXorOracleUnitary_source_pad {N n : ℕ} (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) (v : EuclideanSpace ℂ (Fin N × BitVec n)) :
    registerXorOracleUnitary f (finiteAddressPad (sourcePortEmbedding hn) v) =
      finiteAddressPad (sourcePortEmbedding hn) (sourceXorOracleUnitary f v) := by
  exact involutionBasisUnitary_pad _ _ (sourceXorOracle_involutive f) _
    (registerXorOracle_involutive f) (registerXorOracle_source hn f) v

/-- The one physical address/first-response port on the complete counted frame. -/
def registerFrameOracle {N r b n k c : ℕ} (f : Fin N → Fin N)
    (s : CollisionRegisters r b n k c) : CollisionRegisters r b n k c :=
  { s with scratch := { s.scratch with
      first := s.scratch.first ^^^ registerOracleValue f s.physicalOracleAddress } }

theorem registerFrameOracle_involutive {N r b n k c : ℕ} (f : Fin N → Fin N) :
    Function.Involutive (registerFrameOracle (r := r) (b := b) (n := n) (k := k) (c := c) f) := by
  intro s
  cases s with
  | mk table good mainAddress physicalOracleAddress scratch controller outputFirst outputSecond outputValid =>
    cases scratch
    simp [registerFrameOracle, xor_cancel_right]

def registerFrameOracleEquiv {N r b n k c : ℕ} (f : Fin N → Fin N) :
    CollisionRegisters r b n k c ≃ CollisionRegisters r b n k c :=
  involutionBasisEquiv (registerFrameOracle f) (registerFrameOracle_involutive f)

/-- Actual Hilbert action of the physical oracle on every retained basis state. -/
noncomputable def registerFrameUnitary {N r b n k c : ℕ} (f : Fin N → Fin N) :
    EuclideanSpace ℂ (CollisionRegisters r b n k c) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (CollisionRegisters r b n k c) :=
  involutionBasisUnitary (registerFrameOracle f) (registerFrameOracle_involutive f)

theorem registerFrameUnitary_apply {N r b n k c : ℕ} (f : Fin N → Fin N)
    (v : EuclideanSpace ℂ (CollisionRegisters r b n k c))
    (s : CollisionRegisters r b n k c) :
    registerFrameUnitary f v s = v (registerFrameOracle f s) := rfl

theorem registerFrameUnitary_single {N r b n k c : ℕ} (f : Fin N → Fin N)
    (s : CollisionRegisters r b n k c) (z : ℂ) :
    registerFrameUnitary f (PiLp.single 2 s z) =
      PiLp.single 2 (registerFrameOracle f s) z :=
  basisEquivUnitary_single _ s z

theorem registerFrameUnitary_involutive {N r b n k c : ℕ} (f : Fin N → Fin N) :
    Function.Involutive (registerFrameUnitary (r := r) (b := b) (n := n) (k := k) (c := c) f) :=
  involutionBasisUnitary_involutive _ _

theorem registerFrameOracle_invalid {N r b n k c : ℕ} (f : Fin N → Fin N)
    (s : CollisionRegisters r b n k c) (hx : N ≤ s.physicalOracleAddress.toNat) :
    registerFrameOracle f s = s := by
  cases s with
  | mk table good mainAddress physicalOracleAddress scratch controller outputFirst outputSecond outputValid =>
    cases scratch
    simp_all [registerFrameOracle, registerOracleValue_invalid]

theorem registerFrameUnitary_invalid_single {N r b n k c : ℕ} (f : Fin N → Fin N)
    (s : CollisionRegisters r b n k c) (hx : N ≤ s.physicalOracleAddress.toNat) (z : ℂ) :
    registerFrameUnitary f (PiLp.single 2 s z) = PiLp.single 2 s z := by
  rw [registerFrameUnitary_single, registerFrameOracle_invalid f s hx]

theorem registerFrameOracle_candidate {N r b n k c : ℕ} (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) (x : Fin N) (s : CollisionRegisters r b n k c) :
    registerFrameOracle f {s with physicalOracleAddress := BitVec.ofNat n x.val} =
      {s with
        physicalOracleAddress := BitVec.ofNat n x.val
        scratch := queryCandidate f x s.scratch} := by
  simp only [registerFrameOracle, registerOracleValue_encoded hn, queryCandidate]

theorem registerFrameOracle_outside {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) (i : Fin (N - r)) (s : CollisionRegisters r b n k c) :
    registerFrameOracle f {s with physicalOracleAddress := outsideBitEmbedding hrN hn i} =
      {s with
        physicalOracleAddress := outsideBitEmbedding hrN hn i
        scratch := queryCandidate f (outsideAddress hrN i) s.scratch} :=
  registerFrameOracle_candidate hn f (outsideAddress hrN i) s

/-- A fixed response-port swap, independent of f and of retained data values. -/
def registerFrameResponseSwap {r b n k c : ℕ}
    (s : CollisionRegisters r b n k c) : CollisionRegisters r b n k c :=
  { s with scratch := { s.scratch with first := s.scratch.second, second := s.scratch.first } }

theorem registerFrameResponseSwap_involutive {r b n k c : ℕ} :
    Function.Involutive (registerFrameResponseSwap (r := r) (b := b) (n := n) (k := k) (c := c)) := by
  intro s
  cases s with
  | mk table good mainAddress physicalOracleAddress scratch controller outputFirst outputSecond outputValid =>
    cases scratch
    rfl

noncomputable def registerResponseSwapUnitary (r b n k c : ℕ) :
    EuclideanSpace ℂ (CollisionRegisters r b n k c) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (CollisionRegisters r b n k c) :=
  involutionBasisUnitary registerFrameResponseSwap registerFrameResponseSwap_involutive

theorem registerFrameOracle_second {N r b n k c : ℕ} (f : Fin N → Fin N)
    (s : CollisionRegisters r b n k c) :
    registerFrameResponseSwap (registerFrameOracle f (registerFrameResponseSwap s)) =
      {s with scratch := {s.scratch with
        second := s.scratch.second ^^^ registerOracleValue f s.physicalOracleAddress}} := by
  cases s with
  | mk table good mainAddress physicalOracleAddress scratch controller outputFirst outputSecond outputValid =>
    cases scratch
    rfl

end CollisionTradeoff
