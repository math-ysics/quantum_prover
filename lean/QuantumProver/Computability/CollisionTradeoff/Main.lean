import QuantumProver.Computability.CollisionTradeoff.Lemmas
import QuantumProver.Computability.CollisionTradeoff.RegisterEncoding
import QuantumProver.Computability.CollisionTradeoff.FiberUnitaryLift
import QuantumProver.Computability.CollisionTradeoff.RegisterOracle
import QuantumProver.Computability.CollisionTradeoff.RegisterPreparation

/-!
Exact explicit query-program, uniform-function Born probability and complete
register-space certificate for the collision construction. Fixed gates
are parameter-only operations on retained data; unknown f enters through the
single charged standard value-oracle instruction.
-/

noncomputable section

namespace CollisionTradeoff

open scoped BigOperators Classical

theorem matchingSlots_at_good {r : ℕ} (a : Fin r → ℕ) (ha : GoodTable a) (i : Fin r) :
    matchingSlots a (a i) = {i} := by
  ext j
  simp only [matchingSlots, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  exact ⟨fun h => ha h, fun h => h ▸ rfl⟩

theorem scanWord_at_good {r : ℕ} (k : ℕ) (a : Fin r → ℕ)
    (ha : GoodTable a) (i : Fin r) :
    scanWord k a (a i) = BitVec.ofNat k i.val := by
  simp [scanWord, matchingSlots_at_good a ha i]

theorem scanParity_at_good {r : ℕ} (a : Fin r → ℕ)
    (ha : GoodTable a) (i : Fin r) : scanParity a (a i) = true := by
  simp [scanParity, matchingSlots_at_good a ha i]

theorem scanParity_true_exists {r : ℕ} (a : Fin r → ℕ) (y : ℕ)
    (hp : scanParity a y = true) : ∃ i : Fin r, a i = y := by
  have hn : matchingSlots a y ≠ ∅ := by
    intro he
    simp [scanParity, he] at hp
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hn
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

theorem selectedAddress_at_good {r N : ℕ} (hr : r ≤ N)
    (k : ℕ) (hw : r ≤ 2 ^ k) (hk : 2 ^ k ≤ N)
    (a : Fin r → ℕ) (ha : GoodTable a) (i : Fin r) :
    selectedAddress k hk a (a i) = sampleAddress hr i := by
  apply Fin.ext
  have hi : i.val < 2 ^ k := lt_of_lt_of_le i.isLt hw
  simp [selectedAddress, scanWord_at_good k a ha i, sampleAddress,
    Nat.mod_eq_of_lt hi]

/-- Duplicate tables still produce legal oracle addresses, without a promise of goodness. -/
theorem selectedAddress_valid {r N : ℕ} (k : ℕ) (hk : 2 ^ k ≤ N)
    (a : Fin r → ℕ) (y : ℕ) :
    (selectedAddress k hk a y).val < N :=
  (selectedAddress k hk a y).isLt

theorem goodTable_fullValues_injective {r N : ℕ} (hr : r ≤ N) (B : ℕ)
    (f : Fin N → Fin N) (hg : GoodTable (tagTable hr B f)) :
    Function.Injective (fun i => f (sampleAddress hr i)) := by
  intro i j hij
  apply hg
  simp only [tagTable]
  exact congrArg (fun y : Fin N => tag B y.val) hij

theorem goodTable_image_card {r N : ℕ} (hr : r ≤ N) (B : ℕ)
    (f : Fin N → Fin N) (hg : GoodTable (tagTable hr B f)) :
    (Finset.univ.image (fun i : Fin r => f (sampleAddress hr i))).card = r := by
  rw [Finset.card_image_of_injective _ (goodTable_fullValues_injective hr B f hg)]
  simp

/-- On a good table, the four-query marker's full-value predicate is exact. -/
theorem markerPredicate_iff_sampleCollision {r N : ℕ} (hr : r ≤ N)
    (k : ℕ) (hw : r ≤ 2 ^ k) (hk : 2 ^ k ≤ N) (B : ℕ)
    (f : Fin N → Fin N) (hg : GoodTable (tagTable hr B f)) (x : Fin N) :
    markerPredicate hr k hk B f x ↔ sampleCollision hr f x := by
  let a := tagTable hr B f
  let y := tag B (f x).val
  change (GoodTable a ∧ scanParity a y = true ∧
    f (selectedAddress k hk a y) = f x) ↔ ∃ i : Fin r, f (sampleAddress hr i) = f x
  constructor
  · rintro ⟨_, hp, hf⟩
    obtain ⟨i, hi⟩ := scanParity_true_exists a y hp
    refine ⟨i, ?_⟩
    rw [← hi, selectedAddress_at_good hr k hw hk a hg i] at hf
    exact hf
  · rintro ⟨i, hi⟩
    have ht : y = a i := by
      dsimp [a, y, tagTable]
      rw [hi]
    refine ⟨hg, ?_, ?_⟩
    · rw [ht]
      exact scanParity_at_good a hg i
    · rw [ht, selectedAddress_at_good hr k hw hk a hg i]
      exact hi

/-- The retained good-table bit makes the marker inactive on every bad table. -/
theorem markerPredicate_false_of_bad {r N : ℕ} (hr : r ≤ N)
    (k : ℕ) (hk : 2 ^ k ≤ N) (B : ℕ) (f : Fin N → Fin N)
    (hg : ¬ GoodTable (tagTable hr B f)) (x : Fin N) :
    ¬ markerPredicate hr k hk B f x := by
  intro hp
  exact hg hp.1

/-- A marked outside address yields a distinct valid collision pair. -/
theorem marked_outside_gives_distinct_collision {r N : ℕ} (hr : r ≤ N)
    (k : ℕ) (hw : r ≤ 2 ^ k) (hk : 2 ^ k ≤ N) (B : ℕ)
    (f : Fin N → Fin N) (x : Fin N) (hx : r ≤ x.val)
    (hp : markerPredicate hr k hk B f x) :
    let j := selectedAddress k hk (tagTable hr B f) (tag B (f x).val)
    j ≠ x ∧ f j = f x := by
  have hg : GoodTable (tagTable hr B f) := hp.1
  obtain ⟨i, hi⟩ := scanParity_true_exists (tagTable hr B f) (tag B (f x).val) hp.2.1
  have hj : selectedAddress k hk (tagTable hr B f) (tag B (f x).val) =
      sampleAddress hr i := by
    rw [← hi]
    exact selectedAddress_at_good hr k hw hk _ hg i
  constructor
  · rw [hj]
    intro he
    have hv : i.val = x.val := congrArg Fin.val he
    have hil := i.isLt
    omega
  · exact hp.2.2

/-- The resource ledger is identical for all oracle functions and table outcomes. -/
theorem fixedQueryCount (r m : ℕ) : queryCount r m = 2 * r + 4 * m + 2 := rfl

/-- A ceiling-log tag really fits in the claimed number of bits. -/
theorem tagWidth_covers (r : ℕ) : 64 * r ^ 2 ≤ 2 ^ tagWidth r :=
  Nat.le_pow_clog (by norm_num) _

theorem tagWidth_le_addressWidth {r N : ℕ} (hN : 64 * r ^ 2 ≤ N) :
    tagWidth r ≤ addressWidth N :=
  Nat.clog_mono_right 2 hN

/-- The selected-address register needs fewer than twice as many encodings as slots. -/
theorem indexWidth_encodings_lt {r : ℕ} (hr : 1 < r) :
    2 ^ indexWidth r < 2 * r := by
  have hk : 0 < Nat.clog 2 r := Nat.clog_pos (by norm_num) hr
  have hp : 2 ^ (Nat.clog 2 r).pred < r :=
    Nat.pow_pred_clog_lt_self (by norm_num) hr
  have he : (Nat.clog 2 r).pred + 1 = Nat.clog 2 r :=
    Nat.succ_pred_eq_of_pos hk
  calc
    2 ^ indexWidth r = 2 ^ ((Nat.clog 2 r).pred + 1) := by rw [he]; rfl
    _ = 2 ^ (Nat.clog 2 r).pred * 2 := by rw [pow_succ]
    _ < 2 * r := by omega

/-- No divisibility hypothesis is used in the tag-width estimate. -/
theorem tagWidth_le_auxiliary {r n ℓ : ℕ} (hr : r ≤ n) (hn : n ≤ 2 ^ ℓ) :
    tagWidth r ≤ 6 + 2 * ℓ := by
  apply Nat.clog_le_of_le_pow
  have h : r ≤ 2 ^ ℓ := hr.trans hn
  calc
    64 * r ^ 2 ≤ 64 * (2 ^ ℓ) ^ 2 := by gcongr
    _ = 2 ^ (6 + 2 * ℓ) := by
      rw [pow_add, Nat.mul_comm 2 ℓ, pow_mul]
      norm_num

/-- The `r=floor(n/ℓ)` choice charges at most `3n` tag bits once `ℓ≥6`. -/
theorem shortTagTable_space_bound {n ℓ : ℕ} (hℓ : 6 ≤ ℓ) (hn : n ≤ 2 ^ ℓ) :
    (n / ℓ) * tagWidth (n / ℓ) ≤ 3 * n := by
  have hr : n / ℓ ≤ n := Nat.div_le_self n ℓ
  have hb : tagWidth (n / ℓ) ≤ 6 + 2 * ℓ := tagWidth_le_auxiliary hr hn
  have hd : (n / ℓ) * ℓ ≤ n := Nat.div_mul_le_self n ℓ
  nlinarith

/-- This is an exact bound on the ledger, not a circuit-existence assertion. -/
theorem shortTag_workspaceLedger_bound {n ℓ C : ℕ} (hℓ : 6 ≤ ℓ)
    (hn : n ≤ 2 ^ ℓ) :
    workspaceLedger (n / ℓ) (tagWidth (n / ℓ)) n C ≤ (3 + C) * n := by
  have ht := shortTagTable_space_bound hℓ hn
  simp only [workspaceLedger]
  nlinarith

theorem queryCandidate_involutive {N n k : ℕ} (f : Fin N → Fin N) (x : Fin N) :
    Function.Involutive (queryCandidate (n := n) (k := k) f x) := by
  intro s
  cases s
  simp [queryCandidate, xor_cancel_right]

theorem lookupGate_involutive {r n k : ℕ} (a : Fin r → ℕ) (B : ℕ) :
    Function.Involutive (lookupGate (n := n) (k := k) a B) := by
  intro s
  cases s
  simp [lookupGate, xor_cancel_right]

theorem querySelected_involutive {N n k : ℕ} (hk : 2 ^ k ≤ N) (f : Fin N → Fin N) :
    Function.Involutive (querySelected (n := n) hk f) := by
  intro s
  cases s
  simp [querySelected, xor_cancel_right]

/-- A global gate takes a retained finite-bit table as state data. -/
def tableLookupGate {r b n k : ℕ}
    (s : (Fin r → BitVec b) × MarkerScratch n k) :
    (Fin r → BitVec b) × MarkerScratch n k :=
  (s.1, lookupGate (fun i => (s.1 i).toNat) (2 ^ b) s.2)

/-- This reversible gate is uniform over all possible retained tables. -/
theorem tableLookupGate_involutive {r b n k : ℕ} :
    Function.Involutive (tableLookupGate (r := r) (b := b) (n := n) (k := k)) := by
  rintro ⟨a, s⟩
  change (a, lookupGate (fun i => (a i).toNat) (2 ^ b)
    (lookupGate (fun i => (a i).toNat) (2 ^ b) s)) = (a, s)
  rw [lookupGate_involutive]

def tableGoodFlagGate {r b : ℕ} (s : (Fin r → BitVec b) × Bool) :
    (Fin r → BitVec b) × Bool :=
  (s.1, s.2 ^^ decide (Function.Injective s.1))

theorem tableGoodFlagGate_involutive {r b : ℕ} :
    Function.Involutive (tableGoodFlagGate (r := r) (b := b)) := by
  rintro ⟨a, F⟩
  have h (p q : Bool) : ((p ^^ q) ^^ q) = p := by
    cases p <;> cases q <;> rfl
  change (a, (F ^^ decide (Function.Injective a)) ^^ decide (Function.Injective a)) = (a, F)
  rw [h]

/-- Copying a short response tag into a table slot is itself a reversible gate. -/
def tableTagCopyGate {r b n : ℕ} (i : Fin r)
    (s : (Fin r → BitVec b) × BitVec n) : (Fin r → BitVec b) × BitVec n :=
  (Function.update s.1 i (s.1 i ^^^ BitVec.ofNat b s.2.toNat), s.2)

theorem tableTagCopyGate_involutive {r b n : ℕ} (i : Fin r) :
    Function.Involutive (tableTagCopyGate (b := b) (n := n) i) := by
  rintro ⟨a, y⟩
  apply Prod.ext
  · ext j
    by_cases hj : j = i
    · subst j
      simp [tableTagCopyGate, xor_cancel_right]
    · simp [tableTagCopyGate]
  · rfl

/-- A fixed sample oracle call acts on the response, with the whole table retained as data. -/
def sampleQueryGate {r N b n : ℕ} (hr : r ≤ N) (f : Fin N → Fin N) (i : Fin r)
    (s : (Fin r → BitVec b) × BitVec n) : (Fin r → BitVec b) × BitVec n :=
  (s.1, s.2 ^^^ BitVec.ofNat n (f (sampleAddress hr i)).val)

theorem sampleQueryGate_involutive {r N b n : ℕ} (hr : r ≤ N)
    (f : Fin N → Fin N) (i : Fin r) :
    Function.Involutive (sampleQueryGate (b := b) (n := n) hr f i) := by
  rintro ⟨a, y⟩
  simp [sampleQueryGate, xor_cancel_right]

def setupTableSlot {r N b n : ℕ} (hr : r ≤ N) (f : Fin N → Fin N) (i : Fin r)
    (s : (Fin r → BitVec b) × BitVec n) : (Fin r → BitVec b) × BitVec n :=
  sampleQueryGate hr f i (tableTagCopyGate i (sampleQueryGate hr f i s))

/-- Two sample value calls copy the short tag and erase the entire response. -/
theorem setupTableSlot_zero_response {r N b n : ℕ} (hr : r ≤ N) (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) (i : Fin r) (a : Fin r → BitVec b) :
    setupTableSlot hr f i (a, (0 : BitVec n)) =
      (Function.update a i (a i ^^^ BitVec.ofNat b (f (sampleAddress hr i)).val), 0) := by
  have hv : (f (sampleAddress hr i)).val < 2 ^ n :=
    lt_of_lt_of_le (f (sampleAddress hr i)).isLt hn
  simp [setupTableSlot, sampleQueryGate, tableTagCopyGate, Nat.mod_eq_of_lt hv]

/-- The four oracle calls clean every scratch register on every table and input. -/
theorem cleanMarker_restores_scratch {r N n k : ℕ} (hk : 2 ^ k ≤ N)
    (a : Fin r → ℕ) (B : ℕ) (F : Bool) (f : Fin N → Fin N) (x : Fin N)
    (s : MarkerScratch n k) : (cleanMarker hk a B F f x s).2 = s := by
  change queryCandidate f x (lookupGate a B (querySelected hk f
    (querySelected hk f (lookupGate a B (queryCandidate f x s))))) = s
  rw [querySelected_involutive hk f (lookupGate a B (queryCandidate f x s)),
    lookupGate_involutive a B (queryCandidate f x s), queryCandidate_involutive f x s]

theorem encode_value_toNat {N n : ℕ} (hn : N ≤ 2 ^ n) (v : Fin N) :
    (BitVec.ofNat n v.val).toNat = v.val := by
  simp [Nat.mod_eq_of_lt (lt_of_lt_of_le v.isLt hn)]

theorem encode_value_injective {N n : ℕ} (hn : N ≤ 2 ^ n) :
    Function.Injective (fun v : Fin N => BitVec.ofNat n v.val) := by
  intro u v huv
  apply Fin.ext
  have h := congrArg BitVec.toNat huv
  simpa only [encode_value_toNat hn] using h

/-- All function-dependent information here remains in the supplied table data. -/
theorem computedScratch_from_zero {r N n k : ℕ} (hk : 2 ^ k ≤ N)
    (hn : N ≤ 2 ^ n) (a : Fin r → ℕ) (B : ℕ) (f : Fin N → Fin N) (x : Fin N) :
    querySelected hk f (lookupGate a B (queryCandidate f x (zeroScratch n k))) =
      { first := BitVec.ofNat n (f x).val
        second := BitVec.ofNat n (f (selectedAddress k hk a (tag B (f x).val))).val
        index := scanWord k a (tag B (f x).val)
        parity := scanParity a (tag B (f x).val) } := by
  simp [querySelected, lookupGate, queryCandidate, zeroScratch,
    selectedAddress, encode_value_toNat hn]

/-- The basis-vector scalar of the actual compute/sign/uncompute sequence is exact. -/
theorem cleanMarker_sign {r N n k : ℕ} (hr : r ≤ N) (hk : 2 ^ k ≤ N)
    (hn : N ≤ 2 ^ n) (B : ℕ) (f : Fin N → Fin N) (x : Fin N) :
    (cleanMarker hk (tagTable hr B f) B (decide (GoodTable (tagTable hr B f)))
      f x (zeroScratch n k)).1 =
      if markerPredicate hr k hk B f x then (-1 : ℂ) else 1 := by
  change markerSign (decide (GoodTable (tagTable hr B f)))
    (querySelected hk f (lookupGate (tagTable hr B f) B
      (queryCandidate f x (zeroScratch n k)))) = _
  rw [computedScratch_from_zero hk hn]
  have he : ∀ u v : Fin N, BitVec.ofNat n u.val = BitVec.ofNat n v.val ↔ u = v :=
    fun u v => ⟨fun h => encode_value_injective hn h,
      congrArg (fun t : Fin N => BitVec.ofNat n t.val)⟩
  simp only [markerSign, markerPredicate, decide_eq_true_eq, he]
  congr 1
  apply propext
  constructor <;> rintro ⟨hF, hC, hV⟩ <;> exact ⟨hF, hC, hV.symm⟩

/-- A coarse elementary phase-error estimate is enough for the success constant. -/
theorem sin_sq_ge_three_quarters {t : ℝ} (ht : |t - Real.pi / 2| ≤ 1 / 2) :
    3 / 4 ≤ Real.sin t ^ 2 := by
  have he := abs_le.mp ht
  have hs : (t - Real.pi / 2) ^ 2 ≤ 1 / 4 := by nlinarith
  have hb : Real.sin (t - Real.pi / 2) ^ 2 ≤ (t - Real.pi / 2) ^ 2 :=
    Real.sin_sq_le_sq
  have hi := Real.sin_sq_add_cos_sq (t - Real.pi / 2)
  have hc : Real.cos (t - Real.pi / 2) = Real.sin t := by
    simp [Real.cos_sub]
  rw [hc] at hi
  nlinarith

/-- The arcsine estimate is proved using the elementary cubic lower bound on sine. -/
theorem arcsin_ratio_bounds {a p : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 10)
    (hp₁ : (3 / 4) * a ^ 2 ≤ p) (hp₂ : p ≤ (5 / 4) * a ^ 2) :
    5 / 6 ≤ Real.arcsin (Real.sqrt p) / a ∧
      Real.arcsin (Real.sqrt p) / a ≤ 7 / 6 := by
  have hp0 : 0 ≤ p := le_trans (by positivity) hp₁
  have hu0 : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  have husq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0
  have hulo : (5 / 6) * a ≤ Real.sqrt p :=
    (sq_le_sq₀ (by positivity) hu0).mp (by nlinarith)
  have huhi : Real.sqrt p ≤ (9 / 8) * a :=
    (sq_le_sq₀ hu0 (by positivity)).mp (by nlinarith)
  have hu1 : Real.sqrt p ≤ 1 := by linarith
  have hθ0 : 0 ≤ Real.arcsin (Real.sqrt p) := Real.arcsin_nonneg.mpr hu0
  have hθlo : Real.sqrt p ≤ Real.arcsin (Real.sqrt p) := by
    have h := Real.sin_le hθ0
    rw [Real.sin_arcsin (by linarith) hu1] at h
    exact h
  have ha2 : a ^ 2 ≤ 1 / 100 := by nlinarith
  have ha3 : a ^ 3 ≤ a / 100 := by
    nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr ha2)]
  have hs : (9 / 8) * a ≤ Real.sin ((7 / 6) * a) := by
    have h := Real.sin_ge_sub_cube (x := (7 / 6) * a) (by positivity)
    nlinarith
  have hθhi : Real.arcsin (Real.sqrt p) ≤ (7 / 6) * a := by
    apply (Real.arcsin_le_iff_le_sin ⟨by linarith, hu1⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩).mpr
    exact huhi.trans hs
  constructor
  · exact (le_div_iff₀ ha0).mpr (hulo.trans hθlo)
  · exact (div_le_iff₀ ha0).mpr hθhi

/-- Numerical success of the exact rational/floor iteration choice.
This theorem is about the derived Grover expression, not an assumed algorithm. -/
theorem fixedGrover_probability_bound {a p : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 10)
    (hp₁ : (3 / 4) * a ^ 2 ≤ p) (hp₂ : p ≤ (5 / 4) * a ^ 2) :
    3 / 4 ≤ Real.sin ((2 * (Nat.floor (3 / (4 * a)) : ℝ) + 1) *
      Real.arcsin (Real.sqrt p)) ^ 2 := by
  let m := Nat.floor (3 / (4 * a))
  let β := (2 * (m : ℝ) + 1) * a
  let q := Real.arcsin (Real.sqrt p) / a
  have hf₁ : (m : ℝ) * (4 * a) ≤ 3 :=
    (le_div_iff₀ (by positivity)).mp (Nat.floor_le (by positivity))
  have hf₂ : 3 < ((m : ℝ) + 1) * (4 * a) :=
    (div_lt_iff₀ (by positivity)).mp (Nat.lt_floor_add_one (3 / (4 * a)))
  have hβ₁ : 7 / 5 ≤ β := by dsimp [β]; nlinarith
  have hβ₂ : β ≤ 8 / 5 := by dsimp [β]; nlinarith
  obtain ⟨hq₁, hq₂⟩ := arcsin_ratio_bounds ha0 ha hp₁ hp₂
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hphase₁ : 7 / 6 ≤ β * q := by
    have h := mul_le_mul hβ₁ hq₁ (by norm_num) (by linarith : 0 ≤ β)
    norm_num at h
    exact h
  have hphase₂ : β * q ≤ 28 / 15 := by
    have h := mul_le_mul hβ₂ hq₂ hq0 (by norm_num : (0 : ℝ) ≤ 8 / 5)
    norm_num at h
    exact h
  have hphase : |β * q - Real.pi / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [Real.pi_gt_three, Real.pi_lt_d2]
  have he : β * q = (2 * (m : ℝ) + 1) * Real.arcsin (Real.sqrt p) := by
    dsimp [β, q]
    field_simp [ha0.ne']
  have h := sin_sq_ge_three_quarters hphase
  rw [he] at h
  exact h

/-- The numerical Grover parameters follow from the actual `N,r,K` bounds. -/
theorem fixedGrover_from_countBounds {N r : ℕ} (hr : 1024 ≤ r)
    (hN : 64 * r ^ 2 ≤ N) (K : ℝ) (hK₁ : 3 * (r : ℝ) / 4 ≤ K)
    (hK₂ : K ≤ 5 * (r : ℝ) / 4) :
    let L : ℝ := (N - r : ℕ)
    let a := Real.sqrt ((r : ℝ) / L)
    3 / 4 ≤ Real.sin ((2 * (Nat.floor (3 / (4 * a)) : ℝ) + 1) *
      Real.arcsin (Real.sqrt (K / L))) ^ 2 := by
  let L : ℝ := (N - r : ℕ)
  let a := Real.sqrt ((r : ℝ) / L)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hquad : 1024 * r ≤ r ^ 2 := by
    nlinarith [Nat.mul_le_mul_left r hr]
  have hrN : r ≤ N := by nlinarith
  have hsub : N - r + r = N := Nat.sub_add_cancel hrN
  have hNL : 100 * r ≤ N - r := by nlinarith
  have hL0 : (0 : ℝ) < L := by
    dsimp [L]
    exact_mod_cast (by nlinarith : 0 < N - r)
  have hdiv0 : 0 < (r : ℝ) / L := div_pos hr0 hL0
  have ha0 : 0 < a := Real.sqrt_pos.mpr hdiv0
  have ha2 : a ^ 2 = (r : ℝ) / L := Real.sq_sqrt hdiv0.le
  have hratio : (r : ℝ) / L ≤ 1 / 100 := by
    apply (div_le_iff₀ hL0).mpr
    have h : 100 * (r : ℝ) ≤ L := by dsimp [L]; exact_mod_cast hNL
    nlinarith
  have ha : a ≤ 1 / 10 :=
    (sq_le_sq₀ ha0.le (by norm_num : (0 : ℝ) ≤ 1 / 10)).mp (by nlinarith)
  have hp₁ : (3 / 4) * a ^ 2 ≤ K / L := by
    rw [ha2]
    apply (le_div_iff₀ hL0).mpr
    field_simp [hL0.ne']
    linarith
  have hp₂ : K / L ≤ (5 / 4) * a ^ 2 := by
    rw [ha2]
    apply (div_le_iff₀ hL0).mpr
    field_simp [hL0.ne']
    linarith
  exact fixedGrover_probability_bound ha0 ha hp₁ hp₂

def groverStep (θ : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos (2 * θ) * v.1 + Real.sin (2 * θ) * v.2,
    -Real.sin (2 * θ) * v.1 + Real.cos (2 * θ) * v.2)

def markedSignCoordinates (v : ℝ × ℝ) : ℝ × ℝ := (-v.1, v.2)

def uniformReflectionCoordinates (θ : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  let d := Real.sin θ * v.1 + Real.cos θ * v.2
  (2 * Real.sin θ * d - v.1, 2 * Real.cos θ * d - v.2)

/-- The two-dimensional reflection/mark calculation is derived, not assumed. -/
theorem reflection_after_mark_eq_groverStep (θ : ℝ) (v : ℝ × ℝ) :
    uniformReflectionCoordinates θ (markedSignCoordinates v) = groverStep θ v := by
  have hθ := Real.sin_sq_add_cos_sq θ
  apply Prod.ext
  · simp only [uniformReflectionCoordinates, markedSignCoordinates, groverStep,
      Real.cos_two_mul, Real.sin_two_mul]
    nlinarith [congrArg (fun t : ℝ => v.1 * t) hθ]
  · simp only [uniformReflectionCoordinates, markedSignCoordinates, groverStep,
      Real.cos_two_mul, Real.sin_two_mul]
    ring

theorem groverStep_angle (θ t : ℝ) :
    groverStep θ (Real.sin t, Real.cos t) =
      (Real.sin (t + 2 * θ), Real.cos (t + 2 * θ)) := by
  apply Prod.ext <;> simp only [groverStep, Real.sin_add, Real.cos_add] <;> ring

/-- Exact arbitrary-iteration marked/unmarked coordinate formula. -/
theorem groverCoordinates_iterate (θ : ℝ) (m : ℕ) :
    (groverStep θ)^[m] (Real.sin θ, Real.cos θ) =
      (Real.sin ((2 * (m : ℝ) + 1) * θ), Real.cos ((2 * (m : ℝ) + 1) * θ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, groverStep_angle]
    have he : (2 * (m : ℝ) + 1) * θ + 2 * θ =
        (2 * ((m + 1 : ℕ) : ℝ) + 1) * θ := by push_cast; ring
    rw [he]

open Filter in
theorem ceilingLog_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => (Nat.clog 2 n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  have hl : Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    Real.isLittleO_logb_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n : ℕ => (Real.logb 2 (n : ℝ) + 1) / (n : ℝ))
      atTop (nhds 0) := by
    simpa only [add_div, add_zero] using hl.add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  apply squeeze_zero (fun n => by positivity) ?_ hu
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg (by norm_num) hn1
  have hceil := (Nat.ceil_lt_add_one hlog).le
  have hclog : Nat.ceil (Real.logb (2 : ℝ) (n : ℝ)) = Nat.clog 2 n := by
    simpa using Real.natCeil_logb_natCast 2 n
  rw [hclog] at hceil
  exact div_le_div_of_nonneg_right hceil (by positivity)

open Filter in
theorem addressWidth_tendsto_atTop : Tendsto addressWidth atTop atTop := by
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [eventually_ge_atTop (2 ^ n + 1)] with N hN
  have hn : n < Nat.clog 2 N := (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by omega)
  exact hn.le

/- The exact ceiling-log quotient used in the asymptotic contradiction. -/
open Filter in
theorem auxiliaryWidth_ratio_tendsto_zero :
    Tendsto (fun N : ℕ => (auxiliaryWidth N : ℝ) / (addressWidth N : ℝ))
      atTop (nhds 0) := by
  exact ceilingLog_ratio_tendsto_zero.comp addressWidth_tendsto_atTop

/-- Elementary query-budget algebra after preprocessing becomes negligible. -/
theorem realQueryBudget_sq_le {r M m : ℝ} (hr : 1 ≤ r) (hM : r ^ 3 ≤ M)
    (hm0 : 0 ≤ m) (hm : 4 * m ≤ 3 * Real.sqrt (M / r)) :
    (2 * r + 4 * m + 2) ^ 2 ≤ 49 * M / r := by
  have hr0 : 0 < r := by linarith
  have hM0 : 0 ≤ M := le_trans (by positivity) hM
  have hq0 : 0 ≤ M / r := div_nonneg hM0 hr0.le
  have hs0 : 0 ≤ Real.sqrt (M / r) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (M / r) ^ 2 = M / r := Real.sq_sqrt hq0
  have hr2 : r ^ 2 ≤ M / r := (le_div_iff₀ hr0).mpr (by nlinarith)
  have hrs : r ≤ Real.sqrt (M / r) := (sq_le_sq₀ hr0.le hs0).mp (by nlinarith)
  have ht0 : 0 ≤ 2 * r + 4 * m + 2 := by positivity
  have ht : 2 * r + 4 * m + 2 ≤ 7 * Real.sqrt (M / r) := by nlinarith
  have ht2 := (sq_le_sq₀ ht0 (by positivity)).mpr ht
  calc
    _ ≤ (7 * Real.sqrt (M / r)) ^ 2 := ht2
    _ = 49 * (M / r) := by rw [mul_pow, hs2]; norm_num
    _ = _ := by ring

theorem queryCount_sq_le {N r m : ℕ} (hr : 1 ≤ r) (hN : r ^ 3 ≤ N)
    (hm : 4 * (m : ℝ) ≤ 3 * Real.sqrt ((N : ℝ) / (r : ℝ))) :
    (queryCount r m : ℝ) ^ 2 ≤ 49 * (N : ℝ) / (r : ℝ) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hN' : (r : ℝ) ^ 3 ≤ N := by exact_mod_cast hN
  simpa only [queryCount, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    realQueryBudget_sq_le hr' hN' (by positivity : (0 : ℝ) ≤ m) hm

/-- Explicit product bound for the query/register ledger.
Circuit existence and success are intentionally not premises or conclusions. -/
theorem queryLedger_product_bound {N n ℓ C m : ℕ} (hℓ : 6 ≤ ℓ)
    (hn : n ≤ 2 ^ ℓ) (hr : 1 ≤ n / ℓ) (hN : (n / ℓ) ^ 3 ≤ N)
    (hm : 4 * (m : ℝ) ≤ 3 * Real.sqrt ((N : ℝ) / ((n / ℓ : ℕ) : ℝ))) :
    (queryCount (n / ℓ) m : ℝ) ^ 2 *
        (workspaceLedger (n / ℓ) (tagWidth (n / ℓ)) n C : ℝ) ≤
      98 * (3 + (C : ℝ)) * (N : ℝ) * (ℓ : ℝ) := by
  let r := n / ℓ
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have ht := queryCount_sq_le hr hN hm
  have hs : (workspaceLedger (n / ℓ) (tagWidth (n / ℓ)) n C : ℝ) ≤
      (3 + (C : ℝ)) * (n : ℝ) := by
    exact_mod_cast shortTag_workspaceLedger_bound (C := C) hℓ hn
  have hnr : n ≤ 2 * r * ℓ := by
    have h := Nat.lt_mul_div_succ n (by omega : 0 < ℓ)
    dsimp [r]
    nlinarith
  have hnr' : (n : ℝ) ≤ 2 * (r : ℝ) * (ℓ : ℝ) := by exact_mod_cast hnr
  have hh : (n : ℝ) / (r : ℝ) ≤ 2 * (ℓ : ℝ) :=
    (div_le_iff₀ hr0).mpr (by nlinarith)
  calc
    _ ≤ (49 * (N : ℝ) / (r : ℝ)) * ((3 + (C : ℝ)) * (n : ℝ)) := by
      apply mul_le_mul ht hs (by positivity) (by positivity)
    _ = 49 * (3 + (C : ℝ)) * (N : ℝ) * ((n : ℝ) / (r : ℝ)) := by ring
    _ ≤ 49 * (3 + (C : ℝ)) * (N : ℝ) * (2 * (ℓ : ℝ)) := by gcongr
    _ = _ := by ring

open Filter in
theorem dividedByCeilingLog_tendsto_atTop :
    Tendsto (fun n : ℕ => n / Nat.clog 2 n) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  have he : ∀ᶠ n : ℕ in atTop,
      (Nat.clog 2 n : ℝ) / (n : ℝ) < 1 / ((M : ℝ) + 1) :=
    ceilingLog_ratio_tendsto_zero.eventually (gt_mem_nhds (by positivity))
  filter_upwards [he, eventually_ge_atTop 2] with n h hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm0 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hc := (div_lt_div_iff₀ hn0 hm0).mp h
  have hc' : (Nat.clog 2 n : ℝ) * ((M : ℝ) + 1) < n := by simpa using hc
  have hnat : Nat.clog 2 n * (M + 1) < n := by exact_mod_cast hc'
  have hℓ : 0 < Nat.clog 2 n := Nat.clog_pos (by norm_num) (by omega)
  apply (Nat.le_div_iff_mul_le hℓ).mpr
  nlinarith

open Filter in
theorem sampleSize_tendsto_atTop : Tendsto sampleSize atTop atTop := by
  exact dividedByCeilingLog_tendsto_atTop.comp addressWidth_tendsto_atTop

theorem cubic_doubling {n : ℕ} (hn : 4 ≤ n) : (n + 1) ^ 3 ≤ 2 * n ^ 3 := by
  let j := n - 4
  have he : n = j + 4 := by dsimp [j]; omega
  rw [he]
  nlinarith [Nat.zero_le (j ^ 2), Nat.zero_le (j ^ 3)]

theorem cubic_le_twoPow_pred {n : ℕ} (hn : 12 ≤ n) : n ^ 3 ≤ 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hd := cubic_doubling (by omega : 4 ≤ n)
    calc
      (n + 1) ^ 3 ≤ 2 * n ^ 3 := hd
      _ ≤ 2 * 2 ^ (n - 1) := by gcongr
      _ = 2 ^ (n + 1 - 1) := by
        have he : n - 1 + 1 = n := by omega
        rw [mul_comm, ← pow_succ, he]
        congr 1

theorem addressWidth_cube_le {N : ℕ} (hN : 1 < N) (hn : 12 ≤ addressWidth N) :
    addressWidth N ^ 3 ≤ N := by
  have hc := cubic_le_twoPow_pred hn
  have hp := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN
  simp only [Nat.pred_eq_sub_one] at hp
  exact hc.trans hp.le

/-! Actual finite complex Hilbert-space operations. The reflection is fixed by
`L` alone. The marked-set phase is an analysis representation of the already
proved clean marker, not a freely supplied input-dependent algorithm gate. -/

abbrev AddressHilbert (L : ℕ) := EuclideanSpace ℂ (Fin L)

def addressBlock {L : ℕ} (M : Finset (Fin L)) (a b : ℂ) : AddressHilbert L :=
  WithLp.toLp 2 (fun x => if x ∈ M then a else b)

def uniformAddress (L : ℕ) : AddressHilbert L :=
  WithLp.toLp 2 (fun _ => (((Real.sqrt (L : ℝ))⁻¹ : ℝ) : ℂ))

def fixedUniformReflection (L : ℕ) : AddressHilbert L ≃ₗᵢ[ℂ] AddressHilbert L :=
  (Submodule.span ℂ {uniformAddress L}).reflection

def markedAddressPhase {L : ℕ} (M : Finset (Fin L)) :
    AddressHilbert L ≃ₗᵢ[ℂ] AddressHilbert L :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun x => if x ∈ M then LinearIsometryEquiv.neg ℂ else
      LinearIsometryEquiv.refl ℂ ℂ)

theorem addressBlock_sum {L : ℕ} (M : Finset (Fin L)) (a b : ℂ) :
    (∑ x : Fin L, addressBlock M a b x) =
      (M.card : ℂ) * a + ((L - M.card : ℕ) : ℂ) * b := by
  change (∑ x : Fin L, if x ∈ M then a else b) = _
  rw [Finset.sum_ite]
  have hM : Finset.univ.filter (fun x : Fin L => x ∈ M) = M := by ext; simp
  have hU : Finset.univ.filter (fun x : Fin L => x ∉ M) = Mᶜ := by ext; simp
  rw [hM, hU]
  simp [Finset.card_compl]

theorem inner_uniformAddress_block {L : ℕ} (M : Finset (Fin L)) (a b : ℂ) :
    inner ℂ (uniformAddress L) (addressBlock M a b) =
      (((Real.sqrt (L : ℝ))⁻¹ : ℝ) : ℂ) *
        ((M.card : ℂ) * a + ((L - M.card : ℕ) : ℂ) * b) := by
  rw [PiLp.inner_apply]
  calc
    _ = (((Real.sqrt (L : ℝ))⁻¹ : ℝ) : ℂ) *
        ∑ x : Fin L, addressBlock M a b x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [uniformAddress, mul_comm]
    _ = _ := by rw [addressBlock_sum]

theorem uniformAddress_norm {L : ℕ} (hL : 0 < L) : ‖uniformAddress L‖ = 1 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hsq : Real.sqrt (L : ℝ) ^ 2 = L := Real.sq_sqrt hL0.le
  have hnorm : ‖uniformAddress L‖ ^ 2 = 1 := by
    calc
      _ = ∑ _ : Fin L, ((Real.sqrt (L : ℝ))⁻¹ : ℝ) ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        simp [uniformAddress, Complex.norm_real, Real.norm_eq_abs]
      _ = (L : ℝ) * (Real.sqrt (L : ℝ))⁻¹ ^ 2 := by simp
      _ = 1 := by rw [inv_pow, hsq]; exact mul_inv_cancel₀ hL0.ne'
  nlinarith [norm_nonneg (uniformAddress L)]

theorem fixedUniformReflection_apply {L : ℕ} (hL : 0 < L) (v : AddressHilbert L) :
    fixedUniformReflection L v =
      (2 : ℂ) • (inner ℂ (uniformAddress L) v) • uniformAddress L - v := by
  rw [fixedUniformReflection, Submodule.reflection_apply,
    Submodule.starProjection_unit_singleton ℂ (uniformAddress_norm hL)]
  simp only [two_smul]

theorem markedAddressPhase_apply {L : ℕ} (M : Finset (Fin L))
    (v : AddressHilbert L) (x : Fin L) :
    markedAddressPhase M v x = if x ∈ M then -v x else v x := by
  by_cases hx : x ∈ M <;> simp [markedAddressPhase, hx]

theorem markedAddressPhase_block {L : ℕ} (M : Finset (Fin L)) (a b : ℂ) :
    markedAddressPhase M (addressBlock M a b) = addressBlock M (-a) b := by
  ext x
  rw [markedAddressPhase_apply]
  by_cases hx : x ∈ M <;> simp [addressBlock, hx]

/-- The input-independent reflection on actual complex amplitudes has the
derived two-block action, before any oracle-dependent angular coordinates. -/
theorem fixedUniformReflection_block {L : ℕ} (hL : 0 < L)
    (M : Finset (Fin L)) (a b : ℂ) :
    let q : ℂ := (((Real.sqrt (L : ℝ))⁻¹ : ℝ) : ℂ)
    let d := q * ((M.card : ℂ) * a + ((L - M.card : ℕ) : ℂ) * b)
    fixedUniformReflection L (addressBlock M a b) =
      addressBlock M (2 * d * q - a) (2 * d * q - b) := by
  dsimp
  rw [fixedUniformReflection_apply hL, inner_uniformAddress_block]
  ext x
  by_cases hx : x ∈ M <;> simp [uniformAddress, addressBlock, hx, mul_assoc]

/-- The actual computational-basis Born sum on the marked addresses. -/
theorem addressBlock_marked_born {L : ℕ} (M : Finset (Fin L)) (a b : ℂ) :
    (∑ x ∈ M, ‖addressBlock M a b x‖ ^ 2) = (M.card : ℝ) * ‖a‖ ^ 2 := by
  calc
    _ = ∑ _x ∈ M, ‖a‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [addressBlock, hx]
    _ = _ := by simp

def normalizedAddressBlock {L : ℕ} (M : Finset (Fin L)) (v : ℝ × ℝ) :
    AddressHilbert L :=
  addressBlock M (((v.1 * (Real.sqrt (M.card : ℝ))⁻¹ : ℝ) : ℂ))
    (((v.2 * (Real.sqrt ((L - M.card : ℕ) : ℝ))⁻¹ : ℝ) : ℂ))

/-- Normalized marked/unmarked coordinates give the actual marked Born sum. -/
theorem normalizedAddressBlock_marked_born {L : ℕ} (M : Finset (Fin L))
    (hM : 0 < M.card) (v : ℝ × ℝ) :
    (∑ x ∈ M, ‖normalizedAddressBlock M v x‖ ^ 2) = v.1 ^ 2 := by
  have hK0 : (0 : ℝ) < M.card := by exact_mod_cast hM
  have hs : Real.sqrt (M.card : ℝ) ^ 2 = M.card := Real.sq_sqrt hK0.le
  rw [normalizedAddressBlock, addressBlock_marked_born]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, inv_pow, hs]
  field_simp [hK0.ne']

/-- The angle is derived from the actual marked-set cardinality, solely for analysis. -/
theorem markedAngle_coordinates {L : ℕ} (M : Finset (Fin L)) (hU : M.card < L) :
    let θ := Real.arcsin (Real.sqrt ((M.card : ℝ) / (L : ℝ)))
    Real.sin θ = Real.sqrt (M.card : ℝ) / Real.sqrt (L : ℝ) ∧
      Real.cos θ = Real.sqrt ((L - M.card : ℕ) : ℝ) / Real.sqrt (L : ℝ) := by
  have hK0 : (0 : ℝ) ≤ M.card := by positivity
  have hKL : (M.card : ℝ) < L := by exact_mod_cast hU
  have hL0 : (0 : ℝ) < L := hK0.trans_lt hKL
  have hp0 : 0 ≤ (M.card : ℝ) / (L : ℝ) := div_nonneg hK0 hL0.le
  have hp1 : (M.card : ℝ) / (L : ℝ) ≤ 1 := (div_le_one hL0).mpr hKL.le
  have hx1 : Real.sqrt ((M.card : ℝ) / (L : ℝ)) ≤ 1 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
      (by simpa only [Real.sq_sqrt hp0, one_pow] using hp1)
  have he : 1 - (M.card : ℝ) / (L : ℝ) = ((L - M.card : ℕ) : ℝ) / (L : ℝ) := by
    rw [Nat.cast_sub hU.le]
    field_simp
  dsimp
  constructor
  · rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg ((M.card : ℝ) / (L : ℝ))]) hx1,
      Real.sqrt_div hK0]
  · rw [Real.cos_arcsin, Real.sq_sqrt hp0, he, Real.sqrt_div (by positivity)]

theorem uniformAddress_coordinates {L : ℕ} (M : Finset (Fin L))
    (hM : 0 < M.card) (hU : M.card < L) (θ : ℝ)
    (hs : Real.sin θ = Real.sqrt (M.card : ℝ) / Real.sqrt (L : ℝ))
    (hc : Real.cos θ = Real.sqrt ((L - M.card : ℕ) : ℝ) / Real.sqrt (L : ℝ)) :
    uniformAddress L = normalizedAddressBlock M (Real.sin θ, Real.cos θ) := by
  have hA : Real.sqrt (M.card : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hM)).ne'
  have hB : Real.sqrt ((L - M.card : ℕ) : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < L - M.card))).ne'
  have hR : Real.sqrt (L : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < L))).ne'
  have heA : (Real.sqrt (L : ℝ))⁻¹ =
      Real.sin θ * (Real.sqrt (M.card : ℝ))⁻¹ := by rw [hs]; field_simp [hA, hR]
  have heB : (Real.sqrt (L : ℝ))⁻¹ =
      Real.cos θ * (Real.sqrt ((L - M.card : ℕ) : ℝ))⁻¹ := by rw [hc]; field_simp [hB, hR]
  ext x
  by_cases hx : x ∈ M
  · simpa [uniformAddress, normalizedAddressBlock, addressBlock, hx] using
      congrArg Complex.ofReal heA
  · simpa [uniformAddress, normalizedAddressBlock, addressBlock, hx] using
      congrArg Complex.ofReal heB

/-- The implemented reflection has no angle parameter; the angle only describes
its restriction to the actual normalized marked/unmarked vectors. -/
theorem fixedUniformReflection_groverCoordinates {L : ℕ} (M : Finset (Fin L))
    (hM : 0 < M.card) (hU : M.card < L) (θ : ℝ)
    (hs : Real.sin θ = Real.sqrt (M.card : ℝ) / Real.sqrt (L : ℝ))
    (hc : Real.cos θ = Real.sqrt ((L - M.card : ℕ) : ℝ) / Real.sqrt (L : ℝ))
    (v : ℝ × ℝ) :
    fixedUniformReflection L (markedAddressPhase M (normalizedAddressBlock M v)) =
      normalizedAddressBlock M (groverStep θ v) := by
  let A := Real.sqrt (M.card : ℝ)
  let B := Real.sqrt ((L - M.card : ℕ) : ℝ)
  let R := Real.sqrt (L : ℝ)
  have hA : A ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hM)).ne'
  have hB : B ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < L - M.card))).ne'
  have hR : R ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < L))).ne'
  have hAsq : A ^ 2 = M.card := Real.sq_sqrt (by positivity)
  have hBsq : B ^ 2 = (L - M.card : ℕ) := Real.sq_sqrt (by positivity)
  have hs' : Real.sin θ = A / R := hs
  have hc' : Real.cos θ = B / R := hc
  have hleft :
      2 * (R⁻¹ * ((M.card : ℝ) * (-(v.1 * A⁻¹)) +
        ((L - M.card : ℕ) : ℝ) * (v.2 * B⁻¹))) * R⁻¹ - (-(v.1 * A⁻¹)) =
      (Real.cos (2 * θ) * v.1 + Real.sin (2 * θ) * v.2) * A⁻¹ := by
    rw [Real.cos_two_mul_eq_one_sub, Real.sin_two_mul, hs', hc', ← hAsq, ← hBsq]
    field_simp [hA, hB, hR]
    ring
  have hright :
      2 * (R⁻¹ * ((M.card : ℝ) * (-(v.1 * A⁻¹)) +
        ((L - M.card : ℕ) : ℝ) * (v.2 * B⁻¹))) * R⁻¹ - v.2 * B⁻¹ =
      (-Real.sin (2 * θ) * v.1 + Real.cos (2 * θ) * v.2) * B⁻¹ := by
    rw [Real.cos_two_mul, Real.sin_two_mul, hs', hc', ← hAsq, ← hBsq]
    field_simp [hA, hB, hR]
    ring
  simp only [normalizedAddressBlock, markedAddressPhase_block,
    fixedUniformReflection_block (by omega : 0 < L), groverStep]
  ext x
  by_cases hx : x ∈ M
  · simp only [addressBlock, PiLp.toLp_apply, ite_eq_left hx]
    exact_mod_cast hleft
  · simp only [addressBlock, PiLp.toLp_apply, ite_eq_right hx]
    exact_mod_cast hright

/-- The actual unitary is phase marking followed by the fixed interval reflection. -/
def actualGroverStep {L : ℕ} (M : Finset (Fin L)) :
    AddressHilbert L ≃ₗᵢ[ℂ] AddressHilbert L :=
  (markedAddressPhase M).trans (fixedUniformReflection L)

/-- An exact arbitrary-iteration identity for the actual finite-space unitaries. -/
theorem actualGrover_iterate {L : ℕ} (M : Finset (Fin L))
    (hM : 0 < M.card) (hU : M.card < L) (θ : ℝ)
    (hs : Real.sin θ = Real.sqrt (M.card : ℝ) / Real.sqrt (L : ℝ))
    (hc : Real.cos θ = Real.sqrt ((L - M.card : ℕ) : ℝ) / Real.sqrt (L : ℝ))
    (m : ℕ) :
    (actualGroverStep M)^[m] (uniformAddress L) =
      normalizedAddressBlock M
        (Real.sin ((2 * (m : ℝ) + 1) * θ), Real.cos ((2 * (m : ℝ) + 1) * θ)) := by
  induction m with
  | zero => simpa using uniformAddress_coordinates M hM hU θ hs hc
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    change fixedUniformReflection L (markedAddressPhase M _) = _
    rw [fixedUniformReflection_groverCoordinates M hM hU θ hs hc, groverStep_angle]
    have he : (2 * (m : ℝ) + 1) * θ + 2 * θ =
        (2 * ((m + 1 : ℕ) : ℝ) + 1) * θ := by push_cast; ring
    rw [he]

/-- The actual fixed-reflection unitary's computational-basis marked Born probability. -/
theorem actualGrover_marked_born {L : ℕ} (M : Finset (Fin L))
    (hM : 0 < M.card) (hU : M.card < L) (m : ℕ) :
    (∑ x ∈ M, ‖((actualGroverStep M)^[m] (uniformAddress L)) x‖ ^ 2) =
      Real.sin ((2 * (m : ℝ) + 1) *
        Real.arcsin (Real.sqrt ((M.card : ℝ) / (L : ℝ)))) ^ 2 := by
  obtain ⟨hs, hc⟩ := markedAngle_coordinates M hU
  rw [actualGrover_iterate M hM hU _ hs hc, normalizedAddressBlock_marked_born M hM]

/-- Fixed schedule determined by known dimensions, independent of every oracle
and marked count. Its explicit integer-controller equality is recorded separately. -/
def fixedSearchIterations (N r : ℕ) : ℕ :=
  Nat.floor (3 / (4 * Real.sqrt ((r : ℝ) / ((N - r : ℕ) : ℝ))))

theorem actualGrover_countBounds_success {N r : ℕ} (hr : 1024 ≤ r)
    (hN : 64 * r ^ 2 ≤ N) (M : Finset (Fin (N - r)))
    (hK₁ : 3 * (r : ℝ) / 4 ≤ M.card) (hK₂ : (M.card : ℝ) ≤ 5 * (r : ℝ) / 4) :
    (3 : ℝ) / 4 ≤ ∑ x ∈ M,
      ‖((actualGroverStep M)^[fixedSearchIterations N r] (uniformAddress (N - r))) x‖ ^ 2 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hK0 : (0 : ℝ) < M.card := lt_of_lt_of_le (by positivity) hK₁
  have hM : 0 < M.card := by exact_mod_cast hK0
  have hquad : 1024 * r ≤ r ^ 2 := by nlinarith [Nat.mul_le_mul_left r hr]
  have hrN : r ≤ N := by nlinarith
  have hsub : N - r + r = N := Nat.sub_add_cancel hrN
  have hL : 2 * r ≤ N - r := by nlinarith
  have hL' : 2 * (r : ℝ) ≤ ((N - r : ℕ) : ℝ) := by exact_mod_cast hL
  have hU : M.card < N - r := by
    have h : (M.card : ℝ) < ((N - r : ℕ) : ℝ) := by linarith
    exact_mod_cast h
  rw [actualGrover_marked_born M hM hU]
  exact fixedGrover_from_countBounds hr hN (M.card : ℝ) hK₁ hK₂

def outsideMarkerSet {N r : ℕ} (hrN : r ≤ N) (k : ℕ) (hk : 2 ^ k ≤ N)
    (B : ℕ) (f : Fin N → Fin N) : Finset (Fin (N - r)) :=
  Finset.univ.filter (fun i => markerPredicate hrN k hk B f (outsideAddress hrN i))

theorem outsideMarkerSet_good {N r : ℕ} (hrN : r ≤ N) (k : ℕ)
    (hw : r ≤ 2 ^ k) (hk : 2 ^ k ≤ N) (B : ℕ) (f : Fin N → Fin N)
    (hg : GoodTable (tagTable hrN B f)) :
    outsideMarkerSet hrN k hk B f =
      Finset.univ.filter (fun i => sampleCollision hrN f (outsideAddress hrN i)) := by
  ext i
  simp only [outsideMarkerSet, Finset.mem_filter, Finset.mem_univ, true_and,
    markerPredicate_iff_sampleCollision hrN k hw hk B f hg]

theorem outsideMarkerSet_card_good {N r : ℕ} (hrN : r ≤ N) (k : ℕ)
    (hw : r ≤ 2 ^ k) (hk : 2 ^ k ≤ N) (B : ℕ) (f : Fin N → Fin N)
    (hg : GoodTable (tagTable hrN B f)) :
    ((outsideMarkerSet hrN k hk B f).card : ℝ) = sampleCollisionCount hrN f := by
  rw [outsideMarkerSet_good hrN k hw hk B f hg]
  exact (sampleCollisionCount_eq_card hrN f).symm

/-- The actual finite diagonal phase is exactly the four-query clean-marker scalar. -/
theorem markedAddressPhase_cleanMarker {N r n : ℕ} (hrN : r ≤ N)
    (k : ℕ) (hk : 2 ^ k ≤ N) (hn : N ≤ 2 ^ n) (B : ℕ) (f : Fin N → Fin N)
    (v : AddressHilbert (N - r)) (i : Fin (N - r)) :
    markedAddressPhase (outsideMarkerSet hrN k hk B f) v i =
      (cleanMarker hk (tagTable hrN B f) B (decide (GoodTable (tagTable hrN B f)))
        f (outsideAddress hrN i) (zeroScratch n k)).1 * v i := by
  rw [markedAddressPhase_apply, cleanMarker_sign hrN hk hn]
  simp only [outsideMarkerSet, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> simp

theorem outsideMarkerSet_output_valid {N r : ℕ} (hrN : r ≤ N) (k : ℕ)
    (hw : r ≤ 2 ^ k) (hk : 2 ^ k ≤ N) (B : ℕ) (f : Fin N → Fin N)
    (i : Fin (N - r)) (hi : i ∈ outsideMarkerSet hrN k hk B f) :
    let x := outsideAddress hrN i
    let j := selectedAddress k hk (tagTable hrN B f) (tag B (f x).val)
    j ≠ x ∧ f j = f x := by
  exact marked_outside_gives_distinct_collision hrN k hw hk B f
    (outsideAddress hrN i) (outsideAddress_ge hrN i) (Finset.mem_filter.mp hi).2

def outsideMarkerBorn {N r : ℕ} (hrN : r ≤ N) (k : ℕ) (hk : 2 ^ k ≤ N)
    (B m : ℕ) (f : Fin N → Fin N) : ℝ :=
  let M := outsideMarkerSet hrN k hk B f
  ∑ i ∈ M, ‖((actualGroverStep M)^[m] (uniformAddress (N - r))) i‖ ^ 2

theorem outsideMarkerBorn_nonneg {N r : ℕ} (hrN : r ≤ N) (k : ℕ)
    (hk : 2 ^ k ≤ N) (B m : ℕ) (f : Fin N → Fin N) :
    0 ≤ outsideMarkerBorn hrN k hk B m f := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- An actual finite-unitary Born average over the same uniform complete oracle.
This is a success supporting theorem, not yet a complete circuit-cost certificate. -/
theorem uniform_outside_marker_born_ge {N r B : ℕ} [NeZero N] [NeZero B]
    (hrN : r ≤ N) (hr : 1024 ≤ r) (hN : 64 * r ^ 2 ≤ N)
    (hB : 64 * r ^ 2 ≤ B) (k : ℕ) (hw : r ≤ 2 ^ k) (hk : 2 ^ k ≤ N) :
    (2835 : ℝ) / 4096 ≤ (FiniteLaw.uniform (Fin N → Fin N)).expect
      (outsideMarkerBorn hrN k hk B (fixedSearchIterations N r)) := by
  apply uniform_function_outcome_ge hrN hr hN hB
  · intro f
    exact outsideMarkerBorn_nonneg hrN k hk B _ f
  · intro f hg hlow hhigh
    have hcard := outsideMarkerSet_card_good hrN k hw hk B f hg
    have hK₁ : 3 * (r : ℝ) / 4 ≤ (outsideMarkerSet hrN k hk B f).card := by
      rw [hcard]
      exact hlow
    have hK₂ : ((outsideMarkerSet hrN k hk B f).card : ℝ) ≤ 5 * (r : ℝ) / 4 := by
      rw [hcard]
      exact hhigh
    exact actualGrover_countBounds_success hr hN (outsideMarkerSet hrN k hk B f) hK₁ hK₂

theorem natFloor_sqrt_eq_sqrt_floor {x : ℝ} (hx : 0 ≤ x) :
    Nat.floor (Real.sqrt x) = Nat.sqrt (Nat.floor x) := by
  let m := Nat.sqrt (Nat.floor x)
  have hlo : (m : ℝ) ^ 2 ≤ x := by
    calc
      _ ≤ (Nat.floor x : ℝ) := by exact_mod_cast Nat.sqrt_le' (Nat.floor x)
      _ ≤ x := Nat.floor_le hx
  have hhiN : Nat.floor x + 1 ≤ (m + 1) ^ 2 := by
    have h : Nat.floor x < (m + 1) ^ 2 := Nat.sqrt_lt'.mp (Nat.lt_succ_self m)
    omega
  have hhi : x < ((m : ℝ) + 1) ^ 2 := by
    calc
      _ < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
      _ ≤ _ := by exact_mod_cast hhiN
  apply (Nat.floor_eq_iff (Real.sqrt_nonneg x)).mpr
  constructor <;> nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt hx,
    (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

/-- The schedule has an exact ordinary natural-number implementation. -/
theorem fixedSearchIterations_eq_integerRoot {N r : ℕ} (hr : 0 < r) (hrN : r < N) :
    fixedSearchIterations N r = Nat.sqrt (9 * (N - r) / (16 * r)) := by
  let L : ℝ := ((N - r : ℕ) : ℝ)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hL0 : 0 < L := by dsimp [L]; exact_mod_cast (by omega : 0 < N - r)
  have hratio : 0 < (r : ℝ) / L := div_pos hr0 hL0
  have hq : 0 ≤ 9 * L / (16 * (r : ℝ)) := by positivity
  have he : 3 / (4 * Real.sqrt ((r : ℝ) / L)) =
      Real.sqrt (9 * L / (16 * (r : ℝ))) := by
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [div_pow, mul_pow, Real.sq_sqrt hratio.le, Real.sq_sqrt hq]
    norm_num
    field_simp [hr0.ne', hL0.ne']
  have hf : Nat.floor (9 * L / (16 * (r : ℝ))) = 9 * (N - r) / (16 * r) := by
    have hcast : 9 * L / (16 * (r : ℝ)) =
        ((9 * (N - r) : ℕ) : ℝ) / ((16 * r : ℕ) : ℝ) := by
      norm_num [L]
    rw [hcast]
    exact Nat.floor_div_eq_div _ _
  change Nat.floor (3 / (4 * Real.sqrt ((r : ℝ) / L))) = _
  rw [he, natFloor_sqrt_eq_sqrt_floor hq, hf]

theorem actualGrover_norm {L : ℕ} (M : Finset (Fin L)) (m : ℕ) :
    ‖(actualGroverStep M)^[m] (uniformAddress L)‖ = ‖uniformAddress L‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', LinearIsometryEquiv.norm_map, ih]

/-- The sum is a normalized Born subprobability, for every table and oracle. -/
theorem outsideMarkerBorn_le_one {N r : ℕ} (hrN : r ≤ N) (hL : r < N) (k : ℕ)
    (hk : 2 ^ k ≤ N) (B m : ℕ) (f : Fin N → Fin N) :
    outsideMarkerBorn hrN k hk B m f ≤ 1 := by
  let M := outsideMarkerSet hrN k hk B f
  let v := (actualGroverStep M)^[m] (uniformAddress (N - r))
  have hv : ‖v‖ = 1 := by
    rw [actualGrover_norm, uniformAddress_norm (by omega : 0 < N - r)]
  have ht : (∑ i : Fin (N - r), ‖v i‖ ^ 2) = 1 := by
    rw [← PiLp.norm_sq_eq_of_L2, hv]
    norm_num
  calc
    _ ≤ ∑ i : Fin (N - r), ‖v i‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M)
      intro i _ _
      exact sq_nonneg _
    _ = 1 := ht

theorem uniform_outside_marker_register_born_ge {N r B : ℕ} [NeZero N] [NeZero B]
    (hrN : r ≤ N) (hr : 1024 ≤ r) (hN : 64 * r ^ 2 ≤ N)
    (hB : 64 * r ^ 2 ≤ B) (k : ℕ) (hw : r ≤ 2 ^ k) (hk : 2 ^ k ≤ N) :
    (2835 : ℝ) / 4096 ≤ (FiniteLaw.uniform (Fin N → Fin N)).expect
      (outsideMarkerBorn hrN k hk B (Nat.sqrt (9 * (N - r) / (16 * r)))) := by
  have hquad : 1024 * r ≤ r ^ 2 := by nlinarith [Nat.mul_le_mul_left r hr]
  have hlt : r < N := by nlinarith
  rw [← fixedSearchIterations_eq_integerRoot (by omega : 0 < r) hlt]
  exact uniform_outside_marker_born_ge hrN hr hN hB k hw hk

/-- The exact integer-root loop schedule obeys the query-budget bound. -/
theorem registerIterations_bound {N r : ℕ} (hr : 0 < r) :
    4 * (Nat.sqrt (9 * (N - r) / (16 * r)) : ℝ) ≤
      3 * Real.sqrt ((N : ℝ) / (r : ℝ)) := by
  let m := Nat.sqrt (9 * (N - r) / (16 * r))
  have hm : m ^ 2 ≤ 9 * (N - r) / (16 * r) := Nat.sqrt_le' _
  have hprod : m ^ 2 * (16 * r) ≤ 9 * (N - r) :=
    (Nat.mul_le_mul_right (16 * r) hm).trans (Nat.div_mul_le_self _ _)
  have hboundN : 16 * r * m ^ 2 ≤ 9 * N := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      hprod.trans (Nat.mul_le_mul_left 9 (Nat.sub_le N r))
  have hbound : 16 * (r : ℝ) * (m : ℝ) ^ 2 ≤ 9 * (N : ℝ) := by exact_mod_cast hboundN
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    _ = 16 * (m : ℝ) ^ 2 := by ring
    _ ≤ 9 * (N : ℝ) / (r : ℝ) := (le_div_iff₀ hr0).mpr (by nlinarith)
    _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity)]; ring

theorem registerQueryLedger_product_bound {N n ℓ C : ℕ} (hℓ : 6 ≤ ℓ)
    (hn : n ≤ 2 ^ ℓ) (hr : 1 ≤ n / ℓ) (hN : (n / ℓ) ^ 3 ≤ N) :
    (queryCount (n / ℓ) (Nat.sqrt (9 * (N - n / ℓ) / (16 * (n / ℓ)))) : ℝ) ^ 2 *
        (workspaceLedger (n / ℓ) (tagWidth (n / ℓ)) n C : ℝ) ≤
      98 * (3 + (C : ℝ)) * (N : ℝ) * (ℓ : ℝ) :=
  queryLedger_product_bound hℓ hn hr hN (registerIterations_bound (by omega))

def registerQueryBudget (N : ℕ) : ℕ :=
  queryCount (sampleSize N)
    (Nat.sqrt (9 * (N - sampleSize N) / (16 * sampleSize N)))

/-- All agreed live register fields, including query port, controller and outputs. -/
def chargedRegisterBudget (N : ℕ) : ℕ :=
  registerWidth (sampleSize N) (tagWidth (sampleSize N)) (addressWidth N)
    (indexWidth (sampleSize N)) (4 * addressWidth N)

/- Exact asymptotic arithmetic for the explicit query/register budgets.
The program attaining these budgets is constructed below. -/
open Filter in
theorem registerChargedLedger_ratio_tendsto_zero :
    Tendsto (fun N : ℕ => (registerQueryBudget N : ℝ) ^ 2 *
      (chargedRegisterBudget N : ℝ) / ((N : ℝ) * (addressWidth N : ℝ)))
      atTop (nhds 0) := by
  have hu : Tendsto (fun N : ℕ => (1666 : ℝ) *
      ((auxiliaryWidth N : ℝ) / (addressWidth N : ℝ))) atTop (nhds 0) := by
    simpa using Tendsto.const_mul (1666 : ℝ) auxiliaryWidth_ratio_tendsto_zero
  apply squeeze_zero' (Eventually.of_forall (fun N => by positivity)) ?_ hu
  filter_upwards [eventually_ge_atTop 2,
    addressWidth_tendsto_atTop.eventually (eventually_ge_atTop 64),
    sampleSize_tendsto_atTop.eventually (eventually_ge_atTop 1)] with N hN hn hr
  have hc : addressWidth N ^ 3 ≤ N := addressWidth_cube_le (by omega) (by omega)
  have hrn : sampleSize N ≤ addressWidth N := Nat.div_le_self _ _
  have hrN : sampleSize N ≤ N :=
    hrn.trans ((Nat.le_self_pow (by norm_num : (3 : ℕ) ≠ 0) _).trans hc)
  have hrpow : sampleSize N ^ 3 ≤ N := by
    calc
      _ ≤ addressWidth N ^ 3 := by gcongr
      _ ≤ N := hc
  have hℓ : 6 ≤ auxiliaryWidth N := by
    have h : 5 < Nat.clog 2 (addressWidth N) :=
      (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num; omega)
    exact Nat.succ_le_of_lt h
  have hpow : addressWidth N ≤ 2 ^ auxiliaryWidth N :=
    Nat.le_pow_clog (by norm_num) _
  have hk : indexWidth (sampleSize N) ≤ addressWidth N := Nat.clog_mono_right 2 hrN
  have hspaceN : chargedRegisterBudget N ≤
      workspaceLedger (sampleSize N) (tagWidth (sampleSize N)) (addressWidth N) 14 := by
    simpa only [chargedRegisterBudget, workspaceLedger] using
      registerWidth_bound (r := sampleSize N) (b := tagWidth (sampleSize N)) hk (by omega)
  have hspace : (chargedRegisterBudget N : ℝ) ≤
      (workspaceLedger (sampleSize N) (tagWidth (sampleSize N)) (addressWidth N) 14 : ℝ) := by
    exact_mod_cast hspaceN
  have hb : (registerQueryBudget N : ℝ) ^ 2 *
      (workspaceLedger (sampleSize N) (tagWidth (sampleSize N)) (addressWidth N) 14 : ℝ) ≤
      1666 * (N : ℝ) * (auxiliaryWidth N : ℝ) := by
    have h := registerQueryLedger_product_bound (C := 14) hℓ hpow hr hrpow
    norm_num at h
    simpa only [registerQueryBudget, sampleSize] using h
  have hfull : (registerQueryBudget N : ℝ) ^ 2 * (chargedRegisterBudget N : ℝ) ≤
      1666 * (N : ℝ) * (auxiliaryWidth N : ℝ) :=
    (mul_le_mul_of_nonneg_left hspace (sq_nonneg _)).trans hb
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn0 : (0 : ℝ) < addressWidth N := by exact_mod_cast (by omega : 0 < addressWidth N)
  apply (div_le_iff₀ (mul_pos hN0 hn0)).mpr
  have he : (1666 : ℝ) * ((auxiliaryWidth N : ℝ) / (addressWidth N : ℝ)) *
      ((N : ℝ) * (addressWidth N : ℝ)) = 1666 * (N : ℝ) * (auxiliaryWidth N : ℝ) := by
    field_simp [hn0.ne']
  rw [he]
  exact hfull

/- Register program syntax contains fixed full-frame gates and one charged oracle
primitive. The program constructors below have no unknown-function argument. -/
abbrev RegisterHilbert (r b n k c : ℕ) :=
  EuclideanSpace ℂ (CollisionRegisters r b n k c)

inductive RegisterInstruction (r b n k c : ℕ) where
  | fixed (U : RegisterHilbert r b n k c ≃ₗᵢ[ℂ] RegisterHilbert r b n k c)
  | valueQuery

abbrev RegisterWord (r b n k c : ℕ) := List (RegisterInstruction r b n k c)

def registerInstructionCost {r b n k c : ℕ} : RegisterInstruction r b n k c → ℕ
  | .fixed _ => 0
  | .valueQuery => 1

def registerWordCost {r b n k c : ℕ} (w : RegisterWord r b n k c) : ℕ :=
  (w.map registerInstructionCost).sum

def registerInstructionUnitary {N r b n k c : ℕ} (f : Fin N → Fin N) :
    RegisterInstruction r b n k c →
      (RegisterHilbert r b n k c ≃ₗᵢ[ℂ] RegisterHilbert r b n k c)
  | .fixed U => U
  | .valueQuery => registerFrameUnitary f

def registerWordUnitary {N r b n k c : ℕ} (f : Fin N → Fin N) :
    RegisterWord r b n k c →
      (RegisterHilbert r b n k c ≃ₗᵢ[ℂ] RegisterHilbert r b n k c)
  | [] => LinearIsometryEquiv.refl ℂ _
  | a :: w => (registerInstructionUnitary f a).trans (registerWordUnitary f w)

theorem registerWordCost_append {r b n k c : ℕ} (u v : RegisterWord r b n k c) :
    registerWordCost (u ++ v) = registerWordCost u + registerWordCost v := by
  simp [registerWordCost]

theorem registerWordUnitary_append {N r b n k c : ℕ} (f : Fin N → Fin N)
    (u v : RegisterWord r b n k c) :
    registerWordUnitary f (u ++ v) =
      (registerWordUnitary f u).trans (registerWordUnitary f v) := by
  induction u with
  | nil => ext z s; rfl
  | cons a u ih =>
    simp only [List.cons_append, registerWordUnitary, ih]
    ext z s
    rfl

theorem registerWordUnitary_norm {N r b n k c : ℕ} (f : Fin N → Fin N)
    (w : RegisterWord r b n k c) (v : RegisterHilbert r b n k c) :
    ‖registerWordUnitary f w v‖ = ‖v‖ := (registerWordUnitary f w).norm_map v

def frameConstantPort {r b n k c : ℕ} (x : BitVec n)
    (s : CollisionRegisters r b n k c) : CollisionRegisters r b n k c :=
  {s with physicalOracleAddress := s.physicalOracleAddress ^^^ x}

def frameMainPort {r b n k c : ℕ}
    (s : CollisionRegisters r b n k c) : CollisionRegisters r b n k c :=
  frameConstantPort s.mainAddress s

def frameIndexPort {r b n k c : ℕ}
    (s : CollisionRegisters r b n k c) : CollisionRegisters r b n k c :=
  frameConstantPort (BitVec.ofNat n s.scratch.index.toNat) s

theorem frameConstantPort_involutive {r b n k c : ℕ} (x : BitVec n) :
    Function.Involutive (frameConstantPort (r := r) (b := b) (k := k) (c := c) x) := by
  intro s
  cases s
  simp [frameConstantPort, xor_cancel_right]

theorem frameMainPort_involutive {r b n k c : ℕ} :
    Function.Involutive (frameMainPort (r := r) (b := b) (n := n) (k := k) (c := c)) := by
  intro s
  cases s
  simp [frameMainPort, frameConstantPort, xor_cancel_right]

theorem frameIndexPort_involutive {r b n k c : ℕ} :
    Function.Involutive (frameIndexPort (r := r) (b := b) (n := n) (k := k) (c := c)) := by
  intro s
  cases s
  simp [frameIndexPort, frameConstantPort, xor_cancel_right]

def frameLookup {r b n k c : ℕ}
    (s : CollisionRegisters r b n k c) : CollisionRegisters r b n k c :=
  {s with scratch := lookupGate (fun i => (s.table i).toNat) (2 ^ b) s.scratch}

theorem frameLookup_involutive {r b n k c : ℕ} :
    Function.Involutive (frameLookup (r := r) (b := b) (n := n) (k := k) (c := c)) := by
  intro s
  cases s
  dsimp only [frameLookup]
  rw [lookupGate_involutive]

def frameGoodFlag {r b n k c : ℕ}
    (s : CollisionRegisters r b n k c) : CollisionRegisters r b n k c :=
  {s with good := s.good ^^ decide (Function.Injective s.table)}

theorem frameGoodFlag_involutive {r b n k c : ℕ} :
    Function.Involutive (frameGoodFlag (r := r) (b := b) (n := n) (k := k) (c := c)) := by
  intro s
  have h (p q : Bool) : ((p ^^ q) ^^ q) = p := by cases p <;> cases q <;> rfl
  cases s
  dsimp only [frameGoodFlag]
  rw [h]

def frameTagCopy {r b n k c : ℕ} (i : Fin r)
    (s : CollisionRegisters r b n k c) : CollisionRegisters r b n k c :=
  {s with table := (Function.update s.table i
    (s.table i ^^^ BitVec.ofNat b s.scratch.first.toNat))}

theorem frameTagCopy_involutive {r b n k c : ℕ} (i : Fin r) :
    Function.Involutive (frameTagCopy (b := b) (n := n) (k := k) (c := c) i) := by
  intro s
  cases s
  simp only [frameTagCopy]
  congr 1
  ext j
  by_cases hj : j = i
  · subst j
    simp [xor_cancel_right]
  · simp [hj]

def fixedBasisInstruction {r b n k c : ℕ}
    (g : CollisionRegisters r b n k c → CollisionRegisters r b n k c)
    (hg : Function.Involutive g) : RegisterInstruction r b n k c :=
  .fixed (involutionBasisUnitary g hg)

def candidateQueryWord (r b n k c : ℕ) : RegisterWord r b n k c :=
  [fixedBasisInstruction frameMainPort frameMainPort_involutive,
    .valueQuery, fixedBasisInstruction frameMainPort frameMainPort_involutive]

def selectedQueryWord (r b n k c : ℕ) : RegisterWord r b n k c :=
  [fixedBasisInstruction frameIndexPort frameIndexPort_involutive,
    .fixed (registerResponseSwapUnitary r b n k c), .valueQuery,
    .fixed (registerResponseSwapUnitary r b n k c),
    fixedBasisInstruction frameIndexPort frameIndexPort_involutive]

def sampleQueryWord {r : ℕ} (b n k c : ℕ) (i : Fin r) : RegisterWord r b n k c :=
  [fixedBasisInstruction (frameConstantPort (BitVec.ofNat n i.val))
      (frameConstantPort_involutive _), .valueQuery,
    fixedBasisInstruction (frameConstantPort (BitVec.ofNat n i.val))
      (frameConstantPort_involutive _)]

def setupSlotWord {r : ℕ} (b n k c : ℕ) (i : Fin r) : RegisterWord r b n k c :=
  sampleQueryWord b n k c i ++
    [fixedBasisInstruction (frameTagCopy i) (frameTagCopy_involutive i)] ++
    sampleQueryWord b n k c i

def frameMarkerPhase (r b n k c : ℕ) :
    RegisterHilbert r b n k c ≃ₗᵢ[ℂ] RegisterHilbert r b n k c :=
  finiteSubsetPhase (Finset.univ.filter (fun s : CollisionRegisters r b n k c =>
    s.good = true ∧ s.scratch.parity = true ∧ s.scratch.first = s.scratch.second))

def registerMarkerWord (r b n k c : ℕ) : RegisterWord r b n k c :=
  candidateQueryWord r b n k c ++
    [fixedBasisInstruction frameLookup frameLookup_involutive] ++
    selectedQueryWord r b n k c ++ [.fixed (frameMarkerPhase r b n k c)] ++
    selectedQueryWord r b n k c ++
    [fixedBasisInstruction frameLookup frameLookup_involutive] ++
    candidateQueryWord r b n k c

def registerOutsideReflection {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n) :
    RegisterHilbert r b n k c ≃ₗᵢ[ℂ] RegisterHilbert r b n k c :=
  collisionMainUnitary r b n k c
    (paddedAddressReflection (outsideBitEmbedding hrN hn) (uniformAddress (N - r)))

def registerGroverWord {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n) :
    RegisterWord r b n k c :=
  registerMarkerWord r b n k c ++ [.fixed (registerOutsideReflection hrN hn)]

def repeatRegisterWord {r b n k c : ℕ} (w : RegisterWord r b n k c) : ℕ → RegisterWord r b n k c
  | 0 => []
  | m + 1 => w ++ repeatRegisterWord w m

theorem repeatRegisterWord_cost {r b n k c : ℕ} (w : RegisterWord r b n k c) (m : ℕ) :
    registerWordCost (repeatRegisterWord w m) = m * registerWordCost w := by
  induction m with
  | zero => simp [repeatRegisterWord, registerWordCost]
  | succ m ih =>
    rw [repeatRegisterWord, registerWordCost_append, ih, Nat.succ_mul]
    omega

theorem repeatRegisterWord_unitary {N r b n k c : ℕ} (f : Fin N → Fin N)
    (w : RegisterWord r b n k c) (m : ℕ) (v : RegisterHilbert r b n k c) :
    registerWordUnitary f (repeatRegisterWord w m) v = (registerWordUnitary f w)^[m] v := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    rw [repeatRegisterWord, registerWordUnitary_append]
    change registerWordUnitary f (repeatRegisterWord w m) (registerWordUnitary f w v) = _
    rw [ih, Function.iterate_succ_apply]

theorem registerMarkerWord_cost (r b n k c : ℕ) :
    registerWordCost (registerMarkerWord r b n k c) = 4 := by
  simp [registerMarkerWord, registerWordCost, candidateQueryWord, selectedQueryWord,
    fixedBasisInstruction, registerInstructionCost]

theorem registerGroverWord_cost {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n) :
    registerWordCost (registerGroverWord (b := b) (k := k) (c := c) hrN hn) = 4 := by
  rw [registerGroverWord, registerWordCost_append, registerMarkerWord_cost]
  simp [registerWordCost, registerInstructionCost]

theorem setupSlotWord_cost {r : ℕ} (b n k c : ℕ) (i : Fin r) :
    registerWordCost (setupSlotWord b n k c i) = 2 := by
  simp [setupSlotWord, sampleQueryWord, registerWordCost,
    fixedBasisInstruction, registerInstructionCost]

theorem registerProgram_all_states_encoded {r b n k c : ℕ} (_w : RegisterWord r b n k c) :
    Nonempty (RegisterHilbert r b n k c ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (BitVec (registerWidth r b n k c))) :=
  ⟨collisionRegisterHilbertEncoding r b n k c⟩

theorem fixedBasisInstruction_single {N r b n k c : ℕ} (f : Fin N → Fin N)
    (g : CollisionRegisters r b n k c → CollisionRegisters r b n k c)
    (hg : Function.Involutive g) (s : CollisionRegisters r b n k c) (z : ℂ) :
    registerInstructionUnitary f (fixedBasisInstruction g hg) (PiLp.single 2 s z) =
      PiLp.single 2 (g s) z := basisEquivUnitary_single _ s z

theorem registerSwap_single {r b n k c : ℕ}
    (s : CollisionRegisters r b n k c) (z : ℂ) :
    registerResponseSwapUnitary r b n k c (PiLp.single 2 s z) =
      PiLp.single 2 (registerFrameResponseSwap s) z := basisEquivUnitary_single _ s z

def candidateQueryBasis {N r b n k c : ℕ} (f : Fin N → Fin N)
    (s : CollisionRegisters r b n k c) : CollisionRegisters r b n k c :=
  frameMainPort (registerFrameOracle f (frameMainPort s))

def selectedQueryBasis {N r b n k c : ℕ} (f : Fin N → Fin N)
    (s : CollisionRegisters r b n k c) : CollisionRegisters r b n k c :=
  frameIndexPort (registerFrameResponseSwap (registerFrameOracle f
    (registerFrameResponseSwap (frameIndexPort s))))

def sampleQueryBasis {N r b n k c : ℕ} (f : Fin N → Fin N) (i : Fin r)
    (s : CollisionRegisters r b n k c) : CollisionRegisters r b n k c :=
  frameConstantPort (BitVec.ofNat n i.val)
    (registerFrameOracle f (frameConstantPort (BitVec.ofNat n i.val) s))

theorem candidateQueryWord_single {N r b n k c : ℕ} (f : Fin N → Fin N)
    (s : CollisionRegisters r b n k c) (z : ℂ) :
    registerWordUnitary f (candidateQueryWord r b n k c) (PiLp.single 2 s z) =
      PiLp.single 2 (candidateQueryBasis f s) z := by
  change registerInstructionUnitary f (fixedBasisInstruction frameMainPort frameMainPort_involutive)
    (registerFrameUnitary f (registerInstructionUnitary f
      (fixedBasisInstruction frameMainPort frameMainPort_involutive) (PiLp.single 2 s z))) = _
  rw [fixedBasisInstruction_single, registerFrameUnitary_single, fixedBasisInstruction_single]
  rfl

theorem selectedQueryWord_single {N r b n k c : ℕ} (f : Fin N → Fin N)
    (s : CollisionRegisters r b n k c) (z : ℂ) :
    registerWordUnitary f (selectedQueryWord r b n k c) (PiLp.single 2 s z) =
      PiLp.single 2 (selectedQueryBasis f s) z := by
  change registerInstructionUnitary f (fixedBasisInstruction frameIndexPort frameIndexPort_involutive)
    (registerResponseSwapUnitary r b n k c (registerFrameUnitary f
      (registerResponseSwapUnitary r b n k c (registerInstructionUnitary f
        (fixedBasisInstruction frameIndexPort frameIndexPort_involutive) (PiLp.single 2 s z))))) = _
  rw [fixedBasisInstruction_single, registerSwap_single, registerFrameUnitary_single,
    registerSwap_single, fixedBasisInstruction_single]
  rfl

theorem sampleQueryWord_single {N r b n k c : ℕ} (f : Fin N → Fin N) (i : Fin r)
    (s : CollisionRegisters r b n k c) (z : ℂ) :
    registerWordUnitary f (sampleQueryWord b n k c i) (PiLp.single 2 s z) =
      PiLp.single 2 (sampleQueryBasis f i s) z := by
  change registerInstructionUnitary f (fixedBasisInstruction
      (frameConstantPort (BitVec.ofNat n i.val)) (frameConstantPort_involutive _))
    (registerFrameUnitary f (registerInstructionUnitary f (fixedBasisInstruction
      (frameConstantPort (BitVec.ofNat n i.val)) (frameConstantPort_involutive _))
        (PiLp.single 2 s z))) = _
  rw [fixedBasisInstruction_single, registerFrameUnitary_single, fixedBasisInstruction_single]
  rfl

theorem candidateQueryBasis_source {N r b n k c : ℕ} (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) (x : Fin N) (s : CollisionRegisters r b n k c)
    (hq : s.physicalOracleAddress = 0) (hx : s.mainAddress = BitVec.ofNat n x.val) :
    candidateQueryBasis f s = {s with scratch := queryCandidate f x s.scratch} := by
  cases s with
  | mk table good mainAddress physicalOracleAddress scratch controller outputFirst outputSecond outputValid =>
    cases scratch
    simp_all [candidateQueryBasis, frameMainPort, frameConstantPort,
      registerFrameOracle, registerOracleValue_encoded hn, queryCandidate]

theorem registerOracleValue_index {N n k : ℕ} (hk : 2 ^ k ≤ N) (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) (j : BitVec k) :
    registerOracleValue f (BitVec.ofNat n j.toNat) =
      BitVec.ofNat n (f ⟨j.toNat, lt_of_lt_of_le j.isLt hk⟩).val :=
  registerOracleValue_encoded hn f ⟨j.toNat, lt_of_lt_of_le j.isLt hk⟩

theorem selectedQueryBasis_source {N r b n k c : ℕ} (hk : 2 ^ k ≤ N)
    (hn : N ≤ 2 ^ n) (f : Fin N → Fin N) (s : CollisionRegisters r b n k c)
    (hq : s.physicalOracleAddress = 0) :
    selectedQueryBasis f s = {s with scratch := querySelected hk f s.scratch} := by
  cases s with
  | mk table good mainAddress physicalOracleAddress scratch controller outputFirst outputSecond outputValid =>
    cases scratch with
    | mk first second index parity =>
      simp_all [selectedQueryBasis, frameIndexPort, frameConstantPort,
        registerFrameResponseSwap, registerFrameOracle, querySelected]
      simpa only [BitVec.ofNat_toNat] using registerOracleValue_index hk hn f index

theorem sampleQueryBasis_source {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) (i : Fin r) (s : CollisionRegisters r b n k c)
    (hq : s.physicalOracleAddress = 0) :
    sampleQueryBasis f i s = {s with scratch := queryCandidate f (sampleAddress hrN i) s.scratch} := by
  have hv := registerOracleValue_encoded hn f (sampleAddress hrN i)
  cases s with
  | mk table good mainAddress physicalOracleAddress scratch controller outputFirst outputSecond outputValid =>
    cases scratch
    simp_all [sampleQueryBasis, frameConstantPort, registerFrameOracle, queryCandidate, sampleAddress]

theorem candidateQueryBasis_involutive {N r b n k c : ℕ} (f : Fin N → Fin N) :
    Function.Involutive (candidateQueryBasis (r := r) (b := b) (n := n) (k := k) (c := c) f) := by
  intro s
  unfold candidateQueryBasis
  rw [frameMainPort_involutive, registerFrameOracle_involutive, frameMainPort_involutive]

theorem selectedQueryBasis_involutive {N r b n k c : ℕ} (f : Fin N → Fin N) :
    Function.Involutive (selectedQueryBasis (r := r) (b := b) (n := n) (k := k) (c := c) f) := by
  intro s
  unfold selectedQueryBasis
  rw [frameIndexPort_involutive, registerFrameResponseSwap_involutive,
    registerFrameOracle_involutive, registerFrameResponseSwap_involutive, frameIndexPort_involutive]

theorem frameMarkerPhase_single {r b n k c : ℕ}
    (s : CollisionRegisters r b n k c) (z : ℂ) :
    frameMarkerPhase r b n k c (PiLp.single 2 s z) =
      PiLp.single 2 s (markerSign s.good s.scratch * z) := by
  ext t
  rw [frameMarkerPhase, finiteSubsetPhase_apply]
  by_cases ht : t = s
  · subst t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, PiLp.single_apply, ite_true]
    unfold markerSign
    split_ifs <;> simp_all
  · simp [ht]

def computedFrameBasis {N r b n k c : ℕ} (f : Fin N → Fin N)
    (s : CollisionRegisters r b n k c) : CollisionRegisters r b n k c :=
  selectedQueryBasis f (frameLookup (candidateQueryBasis f s))

theorem registerMarkerWord_single {N r b n k c : ℕ} (f : Fin N → Fin N)
    (s : CollisionRegisters r b n k c) (z : ℂ) :
    registerWordUnitary f (registerMarkerWord r b n k c) (PiLp.single 2 s z) =
      PiLp.single 2 s
        (markerSign (computedFrameBasis f s).good (computedFrameBasis f s).scratch * z) := by
  simp only [registerMarkerWord, registerWordUnitary_append, LinearIsometryEquiv.trans_apply]
  rw [candidateQueryWord_single]
  change registerWordUnitary f (candidateQueryWord r b n k c)
    (registerInstructionUnitary f (fixedBasisInstruction frameLookup frameLookup_involutive)
      (registerWordUnitary f (selectedQueryWord r b n k c)
        (frameMarkerPhase r b n k c (registerWordUnitary f (selectedQueryWord r b n k c)
          (registerInstructionUnitary f (fixedBasisInstruction frameLookup frameLookup_involutive)
            (PiLp.single 2 (candidateQueryBasis f s) z)))))) = _
  rw [fixedBasisInstruction_single, selectedQueryWord_single, frameMarkerPhase_single,
    selectedQueryWord_single, selectedQueryBasis_involutive,
    fixedBasisInstruction_single, frameLookup_involutive,
    candidateQueryWord_single, candidateQueryBasis_involutive]
  rfl

def setupPrefixWord (r b n k c : ℕ) : RegisterWord r b n k c :=
  (List.finRange r).flatMap (setupSlotWord b n k c) ++
    [fixedBasisInstruction frameGoodFlag frameGoodFlag_involutive]

theorem setupSlotList_cost {r b n k c : ℕ} (is : List (Fin r)) :
    registerWordCost (is.flatMap (setupSlotWord b n k c)) = 2 * is.length := by
  induction is with
  | nil => simp [registerWordCost]
  | cons i is ih =>
    rw [List.flatMap_cons, registerWordCost_append, setupSlotWord_cost, ih]
    simp only [List.length_cons]
    omega

theorem setupPrefixWord_cost (r b n k c : ℕ) :
    registerWordCost (setupPrefixWord r b n k c) = 2 * r := by
  rw [setupPrefixWord, registerWordCost_append, setupSlotList_cost]
  simp [registerWordCost, registerInstructionCost, fixedBasisInstruction]

def frameWriteOutput {r b n k c : ℕ}
    (s : CollisionRegisters r b n k c) : CollisionRegisters r b n k c :=
  {s with
    outputFirst := s.outputFirst ^^^ s.mainAddress
    outputSecond := s.outputSecond ^^^ BitVec.ofNat n s.scratch.index.toNat
    outputValid := s.outputValid ^^ decide
      (s.good = true ∧ s.scratch.parity = true ∧ s.scratch.first = s.scratch.second ∧
        s.mainAddress ≠ BitVec.ofNat n s.scratch.index.toNat)}

theorem frameWriteOutput_involutive {r b n k c : ℕ} :
    Function.Involutive (frameWriteOutput (r := r) (b := b) (n := n) (k := k) (c := c)) := by
  intro s
  have h (p q : Bool) : ((p ^^ q) ^^ q) = p := by cases p <;> cases q <;> rfl
  cases s
  dsimp only [frameWriteOutput]
  rw [xor_cancel_right, xor_cancel_right, h]

def verificationWord (r b n k c : ℕ) : RegisterWord r b n k c :=
  candidateQueryWord r b n k c ++
    [fixedBasisInstruction frameLookup frameLookup_involutive] ++
    selectedQueryWord r b n k c ++
    [fixedBasisInstruction frameWriteOutput frameWriteOutput_involutive]

theorem verificationWord_cost (r b n k c : ℕ) :
    registerWordCost (verificationWord r b n k c) = 2 := by
  simp [verificationWord, registerWordCost, candidateQueryWord, selectedQueryWord,
    fixedBasisInstruction, registerInstructionCost]

theorem verificationWord_single {N r b n k c : ℕ} (f : Fin N → Fin N)
    (s : CollisionRegisters r b n k c) (z : ℂ) :
    registerWordUnitary f (verificationWord r b n k c) (PiLp.single 2 s z) =
      PiLp.single 2 (frameWriteOutput (computedFrameBasis f s)) z := by
  simp only [verificationWord, registerWordUnitary_append, LinearIsometryEquiv.trans_apply]
  rw [candidateQueryWord_single]
  change registerInstructionUnitary f (fixedBasisInstruction frameWriteOutput frameWriteOutput_involutive)
    (registerWordUnitary f (selectedQueryWord r b n k c)
      (registerInstructionUnitary f (fixedBasisInstruction frameLookup frameLookup_involutive)
        (PiLp.single 2 (candidateQueryBasis f s) z))) = _
  rw [fixedBasisInstruction_single, selectedQueryWord_single, fixedBasisInstruction_single]
  rfl

def cleanFrame {r b n k c : ℕ} (t : Fin r → BitVec b) (g : Bool) (x : BitVec n) :
    CollisionRegisters r b n k c :=
  {table := t, good := g, mainAddress := x, physicalOracleAddress := 0,
    scratch := zeroScratch n k, controller := 0, outputFirst := 0,
    outputSecond := 0, outputValid := false}

def registerTagTable {N r : ℕ} (hrN : r ≤ N) (b : ℕ) (f : Fin N → Fin N) :
    Fin r → BitVec b := fun i => BitVec.ofNat b (f (sampleAddress hrN i)).val

theorem registerTagTable_toNat {N r : ℕ} (hrN : r ≤ N) (b : ℕ)
    (f : Fin N → Fin N) (i : Fin r) :
    (registerTagTable hrN b f i).toNat = tagTable hrN (2 ^ b) f i := rfl

theorem registerTagTable_good {N r : ℕ} (hrN : r ≤ N) (b : ℕ) (f : Fin N → Fin N) :
    Function.Injective (registerTagTable hrN b f) ↔ GoodTable (tagTable hrN (2 ^ b) f) := by
  constructor
  · intro h i j hij
    apply h
    apply BitVec.eq_of_toNat_eq
    simpa only [registerTagTable_toNat] using hij
  · intro h i j hij
    apply h
    simpa only [registerTagTable_toNat] using congrArg BitVec.toNat hij

theorem setupSlotWord_clean {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) (i : Fin r) (t : Fin r → BitVec b) (g : Bool)
    (x : BitVec n) (z : ℂ) :
    registerWordUnitary f (setupSlotWord b n k c i)
      (PiLp.single 2 (cleanFrame (k := k) (c := c) t g x) z) =
      PiLp.single 2 (cleanFrame (k := k) (c := c)
        (Function.update t i (t i ^^^ registerTagTable hrN b f i)) g x) z := by
  simp only [setupSlotWord, registerWordUnitary_append, LinearIsometryEquiv.trans_apply]
  rw [sampleQueryWord_single]
  change registerWordUnitary f (sampleQueryWord b n k c i)
    (registerInstructionUnitary f (fixedBasisInstruction (frameTagCopy i) (frameTagCopy_involutive i))
      (PiLp.single 2 (sampleQueryBasis f i (cleanFrame t g x)) z)) = _
  rw [fixedBasisInstruction_single, sampleQueryWord_single]
  rw [sampleQueryBasis_source hrN hn f i (cleanFrame t g x) (by rfl)]
  rw [sampleQueryBasis_source hrN hn f i _ (by rfl)]
  congr 1
  simp [frameTagCopy, cleanFrame, queryCandidate, zeroScratch, registerTagTable,
    encode_value_toNat hn]

def accumulateTags {r b : ℕ} (v : Fin r → BitVec b) :
    List (Fin r) → (Fin r → BitVec b) → (Fin r → BitVec b)
  | [], t => t
  | i :: is, t => accumulateTags v is (Function.update t i (t i ^^^ v i))

theorem accumulateTags_nodup {r b : ℕ} (v : Fin r → BitVec b) (is : List (Fin r))
    (hn : is.Nodup) (t : Fin r → BitVec b) (j : Fin r) :
    accumulateTags v is t j = t j ^^^ (if j ∈ is then v j else 0) := by
  induction is generalizing t with
  | nil => simp [accumulateTags]
  | cons i is ih =>
    rw [List.nodup_cons] at hn
    rw [accumulateTags, ih hn.2]
    by_cases hj : j = i
    · subst j
      simp [hn.1]
    · simp [hj]

theorem setupSlotList_clean {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) (is : List (Fin r)) (t : Fin r → BitVec b)
    (g : Bool) (x : BitVec n) (z : ℂ) :
    registerWordUnitary f (is.flatMap (setupSlotWord b n k c))
      (PiLp.single 2 (cleanFrame (k := k) (c := c) t g x) z) =
      PiLp.single 2 (cleanFrame (k := k) (c := c)
        (accumulateTags (registerTagTable hrN b f) is t) g x) z := by
  induction is generalizing t with
  | nil => rfl
  | cons i is ih =>
    rw [List.flatMap_cons, registerWordUnitary_append]
    change registerWordUnitary f (is.flatMap (setupSlotWord b n k c))
      (registerWordUnitary f (setupSlotWord b n k c i)
        (PiLp.single 2 (cleanFrame t g x) z)) = _
    rw [setupSlotWord_clean hrN hn, ih]
    rfl

theorem setupPrefixWord_clean {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) (z : ℂ) :
    registerWordUnitary f (setupPrefixWord r b n k c)
      (PiLp.single 2 (cleanFrame (k := k) (c := c) (fun _ => (0 : BitVec b)) false 0) z) =
      PiLp.single 2 (cleanFrame (k := k) (c := c) (registerTagTable hrN b f)
        (decide (GoodTable (tagTable hrN (2 ^ b) f))) 0) z := by
  rw [setupPrefixWord, registerWordUnitary_append]
  change registerInstructionUnitary f (fixedBasisInstruction frameGoodFlag frameGoodFlag_involutive)
    (registerWordUnitary f ((List.finRange r).flatMap (setupSlotWord b n k c))
      (PiLp.single 2 (cleanFrame (fun _ => 0) false 0) z)) = _
  rw [setupSlotList_clean hrN hn]
  have ht : accumulateTags (registerTagTable hrN b f) (List.finRange r) (fun _ => 0) =
      registerTagTable hrN b f := by
    ext i
    rw [accumulateTags_nodup _ _ (List.nodup_finRange r)]
    simp
  rw [ht, fixedBasisInstruction_single]
  congr 1
  simp [frameGoodFlag, cleanFrame, registerTagTable_good]

theorem computedFrameBasis_source {N r b n k c : ℕ} (hn : N ≤ 2 ^ n)
    (hk : 2 ^ k ≤ N) (f : Fin N → Fin N) (x : Fin N)
    (s : CollisionRegisters r b n k c)
    (hq : s.physicalOracleAddress = 0) (hx : s.mainAddress = BitVec.ofNat n x.val) :
    computedFrameBasis f s = {s with scratch := (querySelected hk f
      (lookupGate (fun i => (s.table i).toNat) (2 ^ b) (queryCandidate f x s.scratch)))} := by
  rw [computedFrameBasis, candidateQueryBasis_source hn f x s hq hx]
  simp only [frameLookup]
  exact selectedQueryBasis_source hk hn f
    {s with scratch := (lookupGate (fun i => (s.table i).toNat) (2 ^ b)
      (queryCandidate f x s.scratch))} hq

theorem registerMarkerWord_clean {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (hk : 2 ^ k ≤ N) (f : Fin N → Fin N) (x : Fin N) (z : ℂ) :
    registerWordUnitary f (registerMarkerWord r b n k c)
      (PiLp.single 2 (cleanFrame (k := k) (c := c) (registerTagTable hrN b f)
        (decide (GoodTable (tagTable hrN (2 ^ b) f))) (BitVec.ofNat n x.val)) z) =
      PiLp.single 2 (cleanFrame (k := k) (c := c) (registerTagTable hrN b f)
        (decide (GoodTable (tagTable hrN (2 ^ b) f))) (BitVec.ofNat n x.val))
          ((if markerPredicate hrN k hk (2 ^ b) f x then (-1 : ℂ) else 1) * z) := by
  rw [registerMarkerWord_single, computedFrameBasis_source hn hk f x _ (by rfl) (by rfl)]
  simp only [cleanFrame, registerTagTable_toNat]
  rw [show markerSign (decide (GoodTable (tagTable hrN (2 ^ b) f)))
      (querySelected hk f (lookupGate (tagTable hrN (2 ^ b) f) (2 ^ b)
        (queryCandidate f x (zeroScratch n k)))) =
      if markerPredicate hrN k hk (2 ^ b) f x then (-1 : ℂ) else 1 from
    cleanMarker_sign hrN hk hn (2 ^ b) f x]

theorem finiteHilbert_expansion {α : Type*} [Fintype α] [DecidableEq α]
    (v : EuclideanSpace ℂ α) : (∑ a : α, PiLp.single 2 a (v a)) = v := by
  ext a
  simp

theorem registerUnitary_pad_intertwine {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (e : α ↪ β) (d : α ↪ γ)
    (U : EuclideanSpace ℂ β ≃ₗᵢ[ℂ] EuclideanSpace ℂ γ)
    (V : EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (h : ∀ a z, U (PiLp.single 2 (e a) z) =
      finiteAddressPad d (V (PiLp.single 2 a z))) (v : EuclideanSpace ℂ α) :
    U (finiteAddressPad e v) = finiteAddressPad d (V v) := by
  rw [← finiteHilbert_expansion v]
  simp only [map_sum, finiteAddressPad_single]
  apply Finset.sum_congr rfl
  intro a _
  exact h a (v a)

theorem finiteAddressPad_compose {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (e : α ↪ β) (d : β ↪ γ) (v : EuclideanSpace ℂ α) :
    finiteAddressPad (e.trans d) v = finiteAddressPad d (finiteAddressPad e v) := by
  rw [← finiteHilbert_expansion v]
  simp only [map_sum, finiteAddressPad_single]
  rfl

theorem finiteAddressPad_event_born {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ↪ β) (v : EuclideanSpace ℂ α)
    (P : β → Prop) [DecidablePred P] :
    (∑ b : β, if P b then ‖finiteAddressPad e v b‖ ^ 2 else 0) =
      ∑ a : α, if P (e a) then ‖v a‖ ^ 2 else 0 := by
  calc
    _ = ∑ b ∈ Finset.univ.image e, if P b then ‖finiteAddressPad e v b‖ ^ 2 else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _ hb
      have hbr : b ∉ Set.range e := by
        rintro ⟨a, rfl⟩
        exact hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
      rw [finiteAddressPad_off e v b hbr]
      simp
    _ = _ := by
      rw [Finset.sum_image]
      · simp only [finiteAddressPad_at]
      · intro a _ a' _ h
        exact e.injective h

def oracleOutsideFrameEmbedding {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) : Fin (N - r) ↪ CollisionRegisters r b n k c where
  toFun i := cleanFrame (registerTagTable hrN b f)
    (decide (GoodTable (tagTable hrN (2 ^ b) f))) (outsideBitEmbedding hrN hn i)
  inj' _i _j h := (outsideBitEmbedding hrN hn).injective (congrArg CollisionRegisters.mainAddress h)

def outsideFrameState {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) (v : AddressHilbert (N - r)) : RegisterHilbert r b n k c :=
  finiteAddressPad (oracleOutsideFrameEmbedding hrN hn f) v

theorem markedAddressPhase_single {L : ℕ} (M : Finset (Fin L)) (i : Fin L) (z : ℂ) :
    markedAddressPhase M (PiLp.single 2 i z) =
      PiLp.single 2 i ((if i ∈ M then (-1 : ℂ) else 1) * z) := by
  ext j
  have hp : markedAddressPhase M = finiteSubsetPhase M := rfl
  rw [hp, finiteSubsetPhase_apply]
  by_cases hj : j = i
  · subst j
    simp only [PiLp.single_apply, ite_true]
    split_ifs <;> simp
  · simp [hj]

theorem registerMarkerWord_outsideState {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hk : 2 ^ k ≤ N) (f : Fin N → Fin N)
    (v : AddressHilbert (N - r)) :
    registerWordUnitary f (registerMarkerWord r b n k c) (outsideFrameState hrN hn f v) =
      outsideFrameState hrN hn f (markedAddressPhase (outsideMarkerSet hrN k hk (2 ^ b) f) v) := by
  apply registerUnitary_pad_intertwine (oracleOutsideFrameEmbedding hrN hn f)
    (oracleOutsideFrameEmbedding hrN hn f) _ _ ?_ v
  intro i z
  rw [markedAddressPhase_single, finiteAddressPad_single]
  change registerWordUnitary f (registerMarkerWord r b n k c)
    (PiLp.single 2 (cleanFrame (registerTagTable hrN b f)
      (decide (GoodTable (tagTable hrN (2 ^ b) f)))
      (BitVec.ofNat n (outsideAddress hrN i).val)) z) = _
  rw [registerMarkerWord_clean hrN hn hk]
  simp only [outsideMarkerSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem computedFrameBasis_clean {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (hk : 2 ^ k ≤ N) (f : Fin N → Fin N) (x : Fin N) :
    computedFrameBasis f (cleanFrame (k := k) (c := c) (registerTagTable hrN b f)
      (decide (GoodTable (tagTable hrN (2 ^ b) f))) (BitVec.ofNat n x.val)) =
      {cleanFrame (k := k) (c := c) (registerTagTable hrN b f)
        (decide (GoodTable (tagTable hrN (2 ^ b) f))) (BitVec.ofNat n x.val) with
        scratch :=
          {first := BitVec.ofNat n (f x).val
           second := BitVec.ofNat n
             (f (selectedAddress k hk (tagTable hrN (2 ^ b) f) (tag (2 ^ b) (f x).val))).val
           index := scanWord k (tagTable hrN (2 ^ b) f) (tag (2 ^ b) (f x).val)
           parity := scanParity (tagTable hrN (2 ^ b) f) (tag (2 ^ b) (f x).val)}} := by
  rw [computedFrameBasis_source hn hk f x _ (by rfl) (by rfl)]
  simp only [cleanFrame, registerTagTable_toNat]
  rw [computedScratch_from_zero hk hn]

def verifiedOutsideFrame {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) (i : Fin (N - r)) : CollisionRegisters r b n k c :=
  frameWriteOutput (computedFrameBasis f (oracleOutsideFrameEmbedding hrN hn f i))

def verifiedOutsideFrameEmbedding {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (f : Fin N → Fin N) : Fin (N - r) ↪ CollisionRegisters r b n k c where
  toFun := verifiedOutsideFrame hrN hn f
  inj' i j h := by
    apply (outsideBitEmbedding hrN hn).injective
    have hm := congrArg CollisionRegisters.mainAddress h
    exact hm

theorem verifiedOutsideFrame_addresses {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hk : 2 ^ k ≤ N) (f : Fin N → Fin N) (i : Fin (N - r)) :
    let x := outsideAddress hrN i
    let j := selectedAddress k hk (tagTable hrN (2 ^ b) f) (tag (2 ^ b) (f x).val)
    (verifiedOutsideFrame (b := b) (k := k) (c := c) hrN hn f i).outputFirst =
      BitVec.ofNat n x.val ∧
    (verifiedOutsideFrame (b := b) (k := k) (c := c) hrN hn f i).outputSecond =
      BitVec.ofNat n j.val := by
  dsimp only
  unfold verifiedOutsideFrame
  change (frameWriteOutput (computedFrameBasis f (cleanFrame (registerTagTable hrN b f)
    (decide (GoodTable (tagTable hrN (2 ^ b) f)))
    (BitVec.ofNat n (outsideAddress hrN i).val)))).outputFirst = _ ∧
    (frameWriteOutput (computedFrameBasis f (cleanFrame (registerTagTable hrN b f)
    (decide (GoodTable (tagTable hrN (2 ^ b) f)))
    (BitVec.ofNat n (outsideAddress hrN i).val)))).outputSecond = _
  rw [computedFrameBasis_clean hrN hn hk]
  simp [frameWriteOutput, cleanFrame, selectedAddress]

theorem verifiedOutsideFrame_accept_iff {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hw : r ≤ 2 ^ k) (hk : 2 ^ k ≤ N)
    (f : Fin N → Fin N) (i : Fin (N - r)) :
    (verifiedOutsideFrame (b := b) (k := k) (c := c) hrN hn f i).outputValid = true ↔
      markerPredicate hrN k hk (2 ^ b) f (outsideAddress hrN i) := by
  let x := outsideAddress hrN i
  let j := selectedAddress k hk (tagTable hrN (2 ^ b) f) (tag (2 ^ b) (f x).val)
  have he (u v : Fin N) : BitVec.ofNat n u.val = BitVec.ofNat n v.val ↔ u = v :=
    ⟨fun h => encode_value_injective hn h, congrArg (fun y : Fin N => BitVec.ofNat n y.val)⟩
  have hf : (verifiedOutsideFrame (b := b) (k := k) (c := c) hrN hn f i).outputValid = true ↔
      GoodTable (tagTable hrN (2 ^ b) f) ∧
        scanParity (tagTable hrN (2 ^ b) f) (tag (2 ^ b) (f x).val) = true ∧
        f x = f j ∧ x ≠ j := by
    unfold verifiedOutsideFrame
    change (frameWriteOutput (computedFrameBasis f (cleanFrame (registerTagTable hrN b f)
      (decide (GoodTable (tagTable hrN (2 ^ b) f))) (BitVec.ofNat n x.val)))).outputValid = _ ↔ _
    rw [computedFrameBasis_clean hrN hn hk]
    simp only [frameWriteOutput, cleanFrame, Bool.false_xor, decide_eq_true_eq]
    change (_ ∧ _ ∧ BitVec.ofNat n (f x).val = BitVec.ofNat n (f j).val ∧
      BitVec.ofNat n x.val ≠ BitVec.ofNat n j.val) ↔ _
    simp only [ne_eq, he]
  rw [hf]
  constructor
  · rintro ⟨hg, hp, hv, _⟩
    exact ⟨hg, hp, hv.symm⟩
  · intro hm
    have hd := marked_outside_gives_distinct_collision hrN k hw hk (2 ^ b) f x
      (outsideAddress_ge hrN i) hm
    exact ⟨hm.1, hm.2.1, hm.2.2.symm, hd.1.symm⟩

def ValidRegisterCollision {N r b n k c : ℕ} (f : Fin N → Fin N)
    (s : CollisionRegisters r b n k c) : Prop :=
  ∃ x y : Fin N, s.outputFirst = BitVec.ofNat n x.val ∧
    s.outputSecond = BitVec.ofNat n y.val ∧ x ≠ y ∧ f x = f y

theorem verifiedOutsideFrame_valid {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hw : r ≤ 2 ^ k) (hk : 2 ^ k ≤ N)
    (f : Fin N → Fin N) (i : Fin (N - r))
    (ha : (verifiedOutsideFrame (b := b) (k := k) (c := c) hrN hn f i).outputValid = true) :
    ValidRegisterCollision f (verifiedOutsideFrame (b := b) (k := k) (c := c) hrN hn f i) := by
  have hm := (verifiedOutsideFrame_accept_iff hrN hn hw hk f i).mp ha
  have hd := outsideMarkerSet_output_valid hrN k hw hk (2 ^ b) f i
    (by simpa [outsideMarkerSet] using hm)
  have haddr := verifiedOutsideFrame_addresses (b := b) (c := c) hrN hn hk f i
  refine ⟨outsideAddress hrN i,
    selectedAddress k hk (tagTable hrN (2 ^ b) f)
      (tag (2 ^ b) (f (outsideAddress hrN i)).val), haddr.1, haddr.2, ?_, ?_⟩
  · exact hd.1.symm
  · exact hd.2.symm

theorem verificationWord_outsideState {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (f : Fin N → Fin N) (v : AddressHilbert (N - r)) :
    registerWordUnitary f (verificationWord r b n k c) (outsideFrameState hrN hn f v) =
      finiteAddressPad (verifiedOutsideFrameEmbedding hrN hn f) v := by
  apply registerUnitary_pad_intertwine (oracleOutsideFrameEmbedding hrN hn f)
    (verifiedOutsideFrameEmbedding hrN hn f) _ (LinearIsometryEquiv.refl ℂ _) ?_ v
  intro i z
  change registerWordUnitary f (verificationWord r b n k c)
    (PiLp.single 2 (oracleOutsideFrameEmbedding hrN hn f i) z) =
      finiteAddressPad (verifiedOutsideFrameEmbedding hrN hn f) (PiLp.single 2 i z)
  rw [finiteAddressPad_single]
  exact verificationWord_single f _ z

def oracleRetainedRest {N r b n k c : ℕ} (hrN : r ≤ N) (f : Fin N → Fin N) :
    CollisionRest r b n k c :=
  (registerTagTable hrN b f, decide (GoodTable (tagTable hrN (2 ^ b) f)),
    0, zeroScratch n k, 0, 0, 0, false)

theorem outsideFrameState_eq_pad {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (f : Fin N → Fin N) (v : AddressHilbert (N - r)) :
    outsideFrameState (b := b) (k := k) (c := c) hrN hn f v =
      finiteAddressPad (collisionFrameEmbedding (oracleRetainedRest (b := b) (k := k) (c := c) hrN f))
        (finiteAddressPad (outsideBitEmbedding hrN hn) v) := by
  rw [finiteAddressPad_comp]
  rfl

theorem registerOutsideReflection_outsideState {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (f : Fin N → Fin N) (v : AddressHilbert (N - r)) :
    registerOutsideReflection (b := b) (k := k) (c := c) hrN hn (outsideFrameState hrN hn f v) =
      outsideFrameState hrN hn f (fixedUniformReflection (N - r) v) := by
  unfold registerOutsideReflection
  rw [outsideFrameState_eq_pad, collisionMainUnitary_pad, paddedAddressReflection_pad,
    outsideFrameState_eq_pad]
  rfl

theorem registerGroverWord_outsideState {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hk : 2 ^ k ≤ N) (f : Fin N → Fin N)
    (v : AddressHilbert (N - r)) :
    registerWordUnitary f (registerGroverWord (b := b) (k := k) (c := c) hrN hn)
      (outsideFrameState hrN hn f v) =
      outsideFrameState hrN hn f (actualGroverStep (outsideMarkerSet hrN k hk (2 ^ b) f) v) := by
  rw [registerGroverWord, registerWordUnitary_append]
  change registerOutsideReflection hrN hn
    (registerWordUnitary f (registerMarkerWord r b n k c) (outsideFrameState hrN hn f v)) = _
  rw [registerMarkerWord_outsideState hrN hn hk, registerOutsideReflection_outsideState]
  rfl

theorem registerGroverRepeat_outsideState {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hk : 2 ^ k ≤ N) (f : Fin N → Fin N)
    (v : AddressHilbert (N - r)) (m : ℕ) :
    registerWordUnitary f (repeatRegisterWord (registerGroverWord (b := b) (k := k) (c := c) hrN hn) m)
      (outsideFrameState hrN hn f v) =
      outsideFrameState hrN hn f ((actualGroverStep (outsideMarkerSet hrN k hk (2 ^ b) f))^[m] v) := by
  rw [repeatRegisterWord_unitary]
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, registerGroverWord_outsideState hrN hn hk]
    rw [Function.iterate_succ_apply']

def registerInitialState (r b n k c : ℕ) : RegisterHilbert r b n k c :=
  PiLp.single 2 (cleanFrame (fun _ => (0 : BitVec b)) false (0 : BitVec n)) 1

def registerCollisionWord {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (m : ℕ) : RegisterWord r b n k c :=
  setupPrefixWord r b n k c ++ [.fixed (fixedCollisionPreparation hrN hn)] ++
    repeatRegisterWord (registerGroverWord hrN hn) m ++ verificationWord r b n k c

theorem registerCollisionWord_cost {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (m : ℕ) : registerWordCost (registerCollisionWord (b := b) (k := k) (c := c) hrN hn m) =
      queryCount r m := by
  simp only [registerCollisionWord, registerWordCost_append, setupPrefixWord_cost,
    repeatRegisterWord_cost, registerGroverWord_cost, verificationWord_cost]
  simp [registerWordCost, registerInstructionCost, queryCount]
  omega

theorem registerCollisionWord_finalState {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hr : 0 < r) (hL : r < N) (hk : 2 ^ k ≤ N)
    (f : Fin N → Fin N) (m : ℕ) :
    registerWordUnitary f (registerCollisionWord (b := b) (k := k) (c := c) hrN hn m)
      (registerInitialState r b n k c) =
      finiteAddressPad (verifiedOutsideFrameEmbedding hrN hn f)
        ((actualGroverStep (outsideMarkerSet hrN k hk (2 ^ b) f))^[m] (uniformAddress (N - r))) := by
  simp only [registerCollisionWord, registerWordUnitary_append, LinearIsometryEquiv.trans_apply]
  rw [registerInitialState, setupPrefixWord_clean hrN hn]
  change registerWordUnitary f (verificationWord r b n k c)
    (registerWordUnitary f (repeatRegisterWord (registerGroverWord hrN hn) m)
      (fixedCollisionPreparation hrN hn (PiLp.single 2 (cleanFrame (registerTagTable hrN b f)
        (decide (GoodTable (tagTable hrN (2 ^ b) f))) 0) 1))) = _
  have hp := fixedCollisionPreparation_outside_pad hrN hn hr hL
    (oracleRetainedRest (b := b) (k := k) (c := c) hrN f)
  change fixedCollisionPreparation hrN hn (PiLp.single 2 (cleanFrame (registerTagTable hrN b f)
      (decide (GoodTable (tagTable hrN (2 ^ b) f))) 0) 1) =
    outsideFrameState hrN hn f (uniformAddress (N - r)) at hp
  rw [hp, registerGroverRepeat_outsideState hrN hn hk, verificationWord_outsideState]

def registerAcceptedBorn {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (m : ℕ) (f : Fin N → Fin N) : ℝ :=
  ∑ s : CollisionRegisters r b n k c, if s.outputValid = true then
    ‖registerWordUnitary f (registerCollisionWord hrN hn m) (registerInitialState r b n k c) s‖ ^ 2 else 0

theorem registerAcceptedBorn_eq_outsideMarkerBorn {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hr : 0 < r) (hL : r < N) (hw : r ≤ 2 ^ k) (hk : 2 ^ k ≤ N)
    (f : Fin N → Fin N) (m : ℕ) :
    registerAcceptedBorn (b := b) (k := k) (c := c) hrN hn m f =
      outsideMarkerBorn hrN k hk (2 ^ b) m f := by
  unfold registerAcceptedBorn
  rw [registerCollisionWord_finalState hrN hn hr hL hk, finiteAddressPad_event_born]
  have he (i : Fin (N - r)) :
      (verifiedOutsideFrameEmbedding (b := b) (k := k) (c := c) hrN hn f i).outputValid = true ↔
        markerPredicate hrN k hk (2 ^ b) f (outsideAddress hrN i) :=
    verifiedOutsideFrame_accept_iff hrN hn hw hk f i
  simp_rw [he]
  simp only [outsideMarkerBorn, outsideMarkerSet, Finset.sum_filter]

theorem registerCollisionWord_invalid_output_zero {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hr : 0 < r) (hL : r < N) (hw : r ≤ 2 ^ k) (hk : 2 ^ k ≤ N)
    (f : Fin N → Fin N) (m : ℕ) (s : CollisionRegisters r b n k c)
    (ha : s.outputValid = true) (hv : ¬ ValidRegisterCollision f s) :
    registerWordUnitary f (registerCollisionWord hrN hn m) (registerInitialState r b n k c) s = 0 := by
  rw [registerCollisionWord_finalState hrN hn hr hL hk]
  apply finiteAddressPad_off
  rintro ⟨i, rfl⟩
  exact hv (verifiedOutsideFrame_valid hrN hn hw hk f i ha)

theorem uniform_registerCollisionWord_success {N r b n k c : ℕ} [NeZero N]
    (hrN : r ≤ N) (hn : N ≤ 2 ^ n) (hr : 1024 ≤ r) (hN : 64 * r ^ 2 ≤ N)
    (hB : 64 * r ^ 2 ≤ 2 ^ b) (hw : r ≤ 2 ^ k) (hk : 2 ^ k ≤ N) :
    (2835 : ℝ) / 4096 ≤ (FiniteLaw.uniform (Fin N → Fin N)).expect
      (registerAcceptedBorn (b := b) (k := k) (c := c) hrN hn (Nat.sqrt (9 * (N - r) / (16 * r)))) := by
  have hL : r < N := by nlinarith [Nat.mul_le_mul_left r hr]
  have he : registerAcceptedBorn (b := b) (k := k) (c := c) hrN hn
      (Nat.sqrt (9 * (N - r) / (16 * r))) =
      outsideMarkerBorn hrN k hk (2 ^ b) (Nat.sqrt (9 * (N - r) / (16 * r))) := by
    funext f
    exact registerAcceptedBorn_eq_outsideMarkerBorn hrN hn (by omega) hL hw hk f _
  rw [he]
  exact uniform_outside_marker_register_born_ge hrN hr hN hB k hw hk

def registerCollisionQubitUnitary {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (m : ℕ) (f : Fin N → Fin N) :
    EuclideanSpace ℂ (BitVec (registerWidth r b n k c)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (BitVec (registerWidth r b n k c)) :=
  (collisionRegisterHilbertEncoding r b n k c).symm.trans
    ((registerWordUnitary f (registerCollisionWord hrN hn m)).trans
      (collisionRegisterHilbertEncoding r b n k c))

theorem registerCollisionQubitUnitary_agrees {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (m : ℕ) (f : Fin N → Fin N) (v : RegisterHilbert r b n k c) :
    registerCollisionQubitUnitary hrN hn m f (collisionRegisterHilbertEncoding r b n k c v) =
      collisionRegisterHilbertEncoding r b n k c
        (registerWordUnitary f (registerCollisionWord hrN hn m) v) := by
  simp [registerCollisionQubitUnitary]

abbrev CollisionPortRest (r b n k c : ℕ) :=
  (Fin r → BitVec b) × Bool × BitVec n × BitVec n × BitVec k × Bool ×
    BitVec c × BitVec n × BitVec n × Bool

def collisionPortRestEquiv (r b n k c : ℕ) :
    CollisionRegisters r b n k c ≃ ((BitVec n × BitVec n) × CollisionPortRest r b n k c) where
  toFun s := ((s.physicalOracleAddress, s.scratch.first),
    (s.table, s.good, s.mainAddress, s.scratch.second, s.scratch.index, s.scratch.parity,
      s.controller, s.outputFirst, s.outputSecond, s.outputValid))
  invFun p :=
    {table := p.2.1
     good := p.2.2.1
     mainAddress := p.2.2.2.1
     physicalOracleAddress := p.1.1
     scratch :=
       {first := p.1.2
        second := p.2.2.2.2.1
        index := p.2.2.2.2.2.1
        parity := p.2.2.2.2.2.2.1}
     controller := p.2.2.2.2.2.2.2.1
     outputFirst := p.2.2.2.2.2.2.2.2.1
     outputSecond := p.2.2.2.2.2.2.2.2.2.1
     outputValid := p.2.2.2.2.2.2.2.2.2.2}
  left_inv s := by cases s; case mk _ _ _ _ scratch _ _ _ _ => cases scratch; rfl
  right_inv p := by
    rcases p with ⟨⟨q, y⟩, t, g, x, z, j, p, a, o, o', ok⟩
    rfl

/- This is one ordinary two-port value oracle tensored with the identity on
every retained register, conjugated by a fixed field rearrangement. -/
theorem registerFrameUnitary_one_standard_query {N r b n k c : ℕ} (f : Fin N → Fin N) :
    registerFrameUnitary (r := r) (b := b) (n := n) (k := k) (c := c) f =
      (basisEquivUnitary (collisionPortRestEquiv r b n k c)).trans
        ((fiberUnitaryLift (β := CollisionPortRest r b n k c) (registerXorOracleUnitary f)).trans
          (basisEquivUnitary (collisionPortRestEquiv r b n k c)).symm) := by
  ext v s
  cases s with
  | mk table good mainAddress physicalOracleAddress scratch controller outputFirst outputSecond outputValid =>
    cases scratch
    rfl

theorem registerInitialState_norm (r b n k c : ℕ) : ‖registerInitialState r b n k c‖ = 1 := by
  simp [registerInitialState, PiLp.norm_single]

theorem registerAcceptedBorn_nonneg {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (m : ℕ) (f : Fin N → Fin N) : 0 ≤ registerAcceptedBorn (b := b) (k := k) (c := c) hrN hn m f := by
  apply Finset.sum_nonneg
  intro s _
  split_ifs <;> positivity

theorem registerAcceptedBorn_le_one {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (m : ℕ) (f : Fin N → Fin N) : registerAcceptedBorn (b := b) (k := k) (c := c) hrN hn m f ≤ 1 := by
  let v := registerWordUnitary f (registerCollisionWord (b := b) (k := k) (c := c) hrN hn m)
    (registerInitialState r b n k c)
  have hv : ‖v‖ = 1 := by rw [registerWordUnitary_norm, registerInitialState_norm]
  calc
    _ ≤ ∑ s : CollisionRegisters r b n k c, ‖v s‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      split_ifs
      · exact le_rfl
      · exact sq_nonneg _
    _ = 1 := by rw [← PiLp.norm_sq_eq_of_L2, hv]; norm_num

def registerCorrectBorn {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (m : ℕ) (f : Fin N → Fin N) : ℝ :=
  ∑ s : CollisionRegisters r b n k c,
    if s.outputValid = true ∧ ValidRegisterCollision f s then
      ‖registerWordUnitary f (registerCollisionWord hrN hn m) (registerInitialState r b n k c) s‖ ^ 2 else 0

theorem registerCorrectBorn_eq_accepted {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hr : 0 < r) (hL : r < N) (hw : r ≤ 2 ^ k) (hk : 2 ^ k ≤ N)
    (m : ℕ) (f : Fin N → Fin N) :
    registerCorrectBorn (b := b) (k := k) (c := c) hrN hn m f =
      registerAcceptedBorn (b := b) (k := k) (c := c) hrN hn m f := by
  apply Finset.sum_congr rfl
  intro s _
  by_cases ha : s.outputValid = true
  · by_cases hv : ValidRegisterCollision f s
    · simp [ha, hv]
    · simp only [ha, hv, true_and, ite_false, ite_true]
      rw [registerCollisionWord_invalid_output_zero hrN hn hr hL hw hk f m s ha hv]
      simp
  · simp [ha]

def uniformOracleLaw (N : ℕ) : FiniteLaw (Fin N → Fin N) :=
  letI : Nonempty (Fin N → Fin N) := ⟨id⟩
  FiniteLaw.uniform (Fin N → Fin N)

def registerProfileWord (N : ℕ) (hrN : sampleSize N ≤ N) :
    RegisterWord (sampleSize N) (tagWidth (sampleSize N)) (addressWidth N)
      (indexWidth (sampleSize N)) (4 * addressWidth N) :=
  registerCollisionWord hrN (Nat.le_pow_clog (by norm_num) N)
    (Nat.sqrt (9 * (N - sampleSize N) / (16 * sampleSize N)))

def registerProfileSuccess (N : ℕ) (hrN : sampleSize N ≤ N) : ℝ :=
  (uniformOracleLaw N).expect
    (registerCorrectBorn (b := tagWidth (sampleSize N)) (k := indexWidth (sampleSize N))
      (c := 4 * addressWidth N) hrN (Nat.le_pow_clog (by norm_num) N)
      (Nat.sqrt (9 * (N - sampleSize N) / (16 * sampleSize N))))

theorem registerProfileWord_cost (N : ℕ) (hrN : sampleSize N ≤ N) :
    registerWordCost (registerProfileWord N hrN) = registerQueryBudget N := registerCollisionWord_cost _ _ _

theorem registerProfile_success {N : ℕ} (hN2 : 2 ≤ N) (hrN : sampleSize N ≤ N)
    (hr : 1024 ≤ sampleSize N) (hN : 64 * sampleSize N ^ 2 ≤ N)
    (hk : 2 ^ indexWidth (sampleSize N) ≤ N) : (2 : ℝ) / 3 ≤ registerProfileSuccess N hrN := by
  let : NeZero N := ⟨by omega⟩
  have hL : sampleSize N < N := by nlinarith [Nat.mul_le_mul_left (sampleSize N) hr]
  have hw : sampleSize N ≤ 2 ^ indexWidth (sampleSize N) := Nat.le_pow_clog (by norm_num) _
  have he : registerCorrectBorn (b := tagWidth (sampleSize N)) (k := indexWidth (sampleSize N))
      (c := 4 * addressWidth N) hrN (Nat.le_pow_clog (by norm_num) N)
      (Nat.sqrt (9 * (N - sampleSize N) / (16 * sampleSize N))) =
    registerAcceptedBorn (b := tagWidth (sampleSize N)) (k := indexWidth (sampleSize N))
      (c := 4 * addressWidth N) hrN (Nat.le_pow_clog (by norm_num) N)
      (Nat.sqrt (9 * (N - sampleSize N) / (16 * sampleSize N))) := by
    funext f
    exact registerCorrectBorn_eq_accepted hrN _ (by omega) hL hw hk _ f
  unfold registerProfileSuccess
  rw [he]
  exact (by norm_num : (2 : ℝ) / 3 ≤ 2835 / 4096).trans
    (uniform_registerCollisionWord_success (b := tagWidth (sampleSize N))
      (k := indexWidth (sampleSize N)) (c := 4 * addressWidth N)
      hrN (Nat.le_pow_clog (by norm_num) N)
      hr hN (tagWidth_covers _) hw hk)

/- All numerical hypotheses of the actual program hold eventually for the
same ceiling-log parameter profile. -/
open Filter in
theorem registerProfile_eventually_admissible : ∀ᶠ N : ℕ in atTop,
    2 ≤ N ∧ 1024 ≤ sampleSize N ∧ 64 * sampleSize N ^ 2 ≤ N ∧ sampleSize N ≤ N ∧
      2 ^ indexWidth (sampleSize N) ≤ N ∧ chargedRegisterBudget N ≤ 17 * addressWidth N := by
  filter_upwards [eventually_ge_atTop 2,
    addressWidth_tendsto_atTop.eventually (eventually_ge_atTop 64),
    sampleSize_tendsto_atTop.eventually (eventually_ge_atTop 1024)] with N hN2 hn hr
  have hc : addressWidth N ^ 3 ≤ N := addressWidth_cube_le (by omega) (by omega)
  have hrn : sampleSize N ≤ addressWidth N := Nat.div_le_self _ _
  have hquad : 64 * sampleSize N ^ 2 ≤ N := by
    calc
      _ ≤ 64 * addressWidth N ^ 2 := by gcongr
      _ ≤ addressWidth N ^ 3 := by nlinarith
      _ ≤ N := hc
  have hrN : sampleSize N ≤ N := by nlinarith [Nat.mul_le_mul_left (sampleSize N) hr]
  have henc := indexWidth_encodings_lt (by omega : 1 < sampleSize N)
  have hk : 2 ^ indexWidth (sampleSize N) ≤ N := by nlinarith
  have hℓ : 6 ≤ auxiliaryWidth N := by
    have h : 5 < Nat.clog 2 (addressWidth N) :=
      (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num; omega)
    exact Nat.succ_le_of_lt h
  have hpow : addressWidth N ≤ 2 ^ auxiliaryWidth N := Nat.le_pow_clog (by norm_num) _
  have hkn : indexWidth (sampleSize N) ≤ addressWidth N := Nat.clog_mono_right 2 hrN
  have hs : chargedRegisterBudget N ≤
      workspaceLedger (sampleSize N) (tagWidth (sampleSize N)) (addressWidth N) 14 := by
    simpa only [chargedRegisterBudget, workspaceLedger] using
      registerWidth_bound (r := sampleSize N) (b := tagWidth (sampleSize N)) hkn (by omega)
  have ht := shortTag_workspaceLedger_bound (C := 14) hℓ hpow
  refine ⟨hN2, hr, hquad, hrN, hk, ?_⟩
  exact hs.trans (by simpa only [sampleSize] using ht)

theorem addressWidth_mul_log_two_le {N : ℕ} (hN : 3 ≤ N) :
    (addressWidth N : ℝ) * Real.log 2 ≤ 2 * Real.log (N : ℝ) := by
  have hn : 2 ≤ addressWidth N := by
    have h : 1 < Nat.clog 2 N :=
      (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num; omega)
    exact Nat.succ_le_of_lt h
  have hpN : 2 ^ (addressWidth N - 1) < N :=
    Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hpR : (2 : ℝ) ^ (addressWidth N - 1) < (N : ℝ) := by exact_mod_cast hpN
  have hl := Real.log_lt_log (by positivity : 0 < (2 : ℝ) ^ (addressWidth N - 1)) hpR
  rw [Real.log_pow] at hl
  have hs : (addressWidth N : ℝ) = ((addressWidth N - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ addressWidth N)).symm
  have hm : (addressWidth N : ℝ) ≤ 2 * ((addressWidth N - 1 : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ addressWidth N := by exact_mod_cast hn
    linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hm hlog2.le]

/- The exact complete-program ledgers also beat N times the conventional
natural logarithm; changing the logarithm base only multiplies a constant. -/
open Filter in
theorem registerChargedLedger_naturalLog_ratio_tendsto_zero :
    Tendsto (fun N : ℕ => (registerQueryBudget N : ℝ) ^ 2 * (chargedRegisterBudget N : ℝ) /
      ((N : ℝ) * Real.log (N : ℝ))) atTop (nhds 0) := by
  have hu : Tendsto (fun N : ℕ => (2 / Real.log 2 : ℝ) *
      ((registerQueryBudget N : ℝ) ^ 2 * (chargedRegisterBudget N : ℝ) /
        ((N : ℝ) * (addressWidth N : ℝ)))) atTop (nhds 0) := by
    simpa using Tendsto.const_mul (2 / Real.log 2 : ℝ) registerChargedLedger_ratio_tendsto_zero
  apply squeeze_zero' ?_ ?_ hu
  · exact Eventually.of_forall (fun N =>
      div_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg N) (Real.log_natCast_nonneg N)))
  · filter_upwards [eventually_ge_atTop 3] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hn0 : (0 : ℝ) < addressWidth N := by
      exact_mod_cast Nat.clog_pos (by norm_num : 1 < (2 : ℕ)) (by omega : 1 < N)
    have hl0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have h20 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hratio : (addressWidth N : ℝ) / Real.log (N : ℝ) ≤ 2 / Real.log 2 :=
      (div_le_div_iff₀ hl0 h20).mpr (addressWidth_mul_log_two_le hN)
    have he : (registerQueryBudget N : ℝ) ^ 2 * (chargedRegisterBudget N : ℝ) /
        ((N : ℝ) * Real.log (N : ℝ)) =
        ((registerQueryBudget N : ℝ) ^ 2 * (chargedRegisterBudget N : ℝ) /
          ((N : ℝ) * (addressWidth N : ℝ))) *
          ((addressWidth N : ℝ) / Real.log (N : ℝ)) := by
      field_simp [hN0.ne', hn0.ne', hl0.ne']
    rw [he]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hratio
      (by positivity : 0 ≤ (registerQueryBudget N : ℝ) ^ 2 * (chargedRegisterBudget N : ℝ) /
        ((N : ℝ) * (addressWidth N : ℝ)))

/- A concrete complete-query-program witness, with actual output success,
actual query count, and complete-frame width, defeats every positive proposed
constant in the literal T^2 S >= constant*N*log N assertion. -/
open Filter in
theorem registerCollision_arbitrarily_small_resource_product (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∃ hrN : sampleSize N ≤ N,
      2 ≤ N ∧ (2 : ℝ) / 3 ≤ registerProfileSuccess N hrN ∧
      chargedRegisterBudget N ≤ 17 * addressWidth N ∧
      (registerWordCost (registerProfileWord N hrN) : ℝ) ^ 2 * (chargedRegisterBudget N : ℝ) <
        ε * ((N : ℝ) * Real.log (N : ℝ)) := by
  have hs : ∀ᶠ N : ℕ in atTop,
      (registerQueryBudget N : ℝ) ^ 2 * (chargedRegisterBudget N : ℝ) /
        ((N : ℝ) * Real.log (N : ℝ)) < ε :=
    registerChargedLedger_naturalLog_ratio_tendsto_zero.eventually (gt_mem_nhds hε)
  obtain ⟨N, ⟨⟨⟨hN2, hr, hN, hrN, hk, hwidth⟩, hsmall⟩, hN₀⟩⟩ :=
    ((registerProfile_eventually_admissible.and hs).and (eventually_ge_atTop N₀)).exists
  refine ⟨N, hN₀, hrN, hN2, registerProfile_success hN2 hrN hr hN hk, hwidth, ?_⟩
  rw [registerProfileWord_cost]
  have hden : 0 < (N : ℝ) * Real.log (N : ℝ) := by
    apply mul_pos
    · exact_mod_cast (by omega : 0 < N)
    · exact Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  exact (div_lt_iff₀ hden).mp hsmall

/-- The original successful-pair event, without requiring the verifier flag. -/
def registerWordPairBorn {N r b n k c : ℕ} (w : RegisterWord r b n k c)
    (f : Fin N → Fin N) : ℝ :=
  ∑ s : CollisionRegisters r b n k c, if ValidRegisterCollision f s then
    ‖registerWordUnitary f w (registerInitialState r b n k c) s‖ ^ 2 else 0

def registerWordPairMean (N : ℕ) {r b n k c : ℕ} (w : RegisterWord r b n k c) : ℝ :=
  (uniformOracleLaw N).expect (registerWordPairBorn w)

theorem registerCorrectBorn_le_pairBorn {N r b n k c : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (m : ℕ) (f : Fin N → Fin N) :
    registerCorrectBorn (b := b) (k := k) (c := c) hrN hn m f ≤
      registerWordPairBorn (registerCollisionWord (b := b) (k := k) (c := c) hrN hn m) f := by
  apply Finset.sum_le_sum
  intro s _
  by_cases hv : ValidRegisterCollision f s <;> by_cases ha : s.outputValid = true <;>
    simp [hv, ha]

theorem registerProfileSuccess_le_pairMean (N : ℕ) (hrN : sampleSize N ≤ N) :
    registerProfileSuccess N hrN ≤ registerWordPairMean N (registerProfileWord N hrN) := by
  unfold registerProfileSuccess registerWordPairMean FiniteLaw.expect
  apply Finset.sum_le_sum
  intro f _
  apply mul_le_mul_of_nonneg_left ?_ ((uniformOracleLaw N).nonneg f)
  exact registerCorrectBorn_le_pairBorn hrN _ _ f

def RegisterOutputInDomain {N r b n k c : ℕ} (s : CollisionRegisters r b n k c) : Prop :=
  ∃ x y : Fin N, s.outputFirst = BitVec.ofNat n x.val ∧ s.outputSecond = BitVec.ofNat n y.val

theorem registerCollisionWord_output_domain {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hr : 0 < r) (hL : r < N) (hk : 2 ^ k ≤ N)
    (f : Fin N → Fin N) (m : ℕ) (s : CollisionRegisters r b n k c)
    (hd : ¬ RegisterOutputInDomain (N := N) s) :
    registerWordUnitary f (registerCollisionWord hrN hn m) (registerInitialState r b n k c) s = 0 := by
  rw [registerCollisionWord_finalState hrN hn hr hL hk]
  apply finiteAddressPad_off
  rintro ⟨i, rfl⟩
  apply hd
  have haddr := verifiedOutsideFrame_addresses (b := b) (c := c) hrN hn hk f i
  exact ⟨outsideAddress hrN i, selectedAddress k hk (tagTable hrN (2 ^ b) f)
    (tag (2 ^ b) (f (outsideAddress hrN i)).val), haddr.1, haddr.2⟩

/-- A complete standard-query circuit with the literal measured-pair success event. -/
theorem registerMeasuredCollision_counterexample (ε : ℝ) (hε : 0 < ε) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∃ hrN : sampleSize N ≤ N,
      2 ≤ N ∧ (2 : ℝ) / 3 ≤ registerWordPairMean N (registerProfileWord N hrN) ∧
      chargedRegisterBudget N ≤ 17 * addressWidth N ∧
      (registerWordCost (registerProfileWord N hrN) : ℝ) ^ 2 * (chargedRegisterBudget N : ℝ) <
        ε * ((N : ℝ) * Real.log (N : ℝ)) := by
  obtain ⟨N, hN₀, hrN, hN2, hs, hwidth, hsmall⟩ :=
    registerCollision_arbitrarily_small_resource_product ε hε N₀
  exact ⟨N, hN₀, hrN, hN2, hs.trans (registerProfileSuccess_le_pairMean N hrN), hwidth, hsmall⟩

/-- A proposed universal bound on the ordinary finite standard-query programs. -/
def UniversalRegisterCollisionTradeoff (C : ℝ) (N₀ : ℕ) : Prop :=
  ∀ N : ℕ, N₀ ≤ N → ∀ (r b n k c : ℕ), N ≤ 2 ^ n →
    ∀ w : RegisterWord r b n k c, (2 : ℝ) / 3 ≤ registerWordPairMean N w →
      C * ((N : ℝ) * Real.log (N : ℝ)) ≤
        (registerWordCost w : ℝ) ^ 2 * (registerWidth r b n k c : ℝ)

theorem no_positive_uniform_register_collision_tradeoff :
    ¬ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, UniversalRegisterCollisionTradeoff C N₀ := by
  rintro ⟨C, hC, N₀, hbound⟩
  obtain ⟨N, hN₀, hrN, _hN2, hs, _hwidth, hsmall⟩ := registerMeasuredCollision_counterexample C hC N₀
  have hlo := hbound N hN₀ (sampleSize N) (tagWidth (sampleSize N)) (addressWidth N)
    (indexWidth (sampleSize N)) (4 * addressWidth N) (Nat.le_pow_clog (by norm_num) N)
    (registerProfileWord N hrN) hs
  exact (not_lt_of_ge hlo) hsmall

end CollisionTradeoff
