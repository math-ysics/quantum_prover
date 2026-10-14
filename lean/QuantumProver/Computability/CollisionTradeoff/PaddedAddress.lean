import QuantumProver.Computability.CollisionTradeoff.RegisterEncoding
import QuantumProver.Computability.CollisionTradeoff.TagCollisionLaw

/-!
Zero-extension of a finite address Hilbert space into a explicit register.
The embedding and padded-span reflection are fixed by finite address data.
The reflection restricts exactly to the source reflection and acts as -I on
explicit basis states outside the embedding.  No explicit program or query cost
is assumed by these supporting Hilbert-space statements.
-/

namespace CollisionTradeoff

open scoped BigOperators Classical

section FinitePad

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def finiteAddressPadVector (e : α ↪ β)
    (v : EuclideanSpace ℂ α) : EuclideanSpace ℂ β :=
  WithLp.toLp 2 (Function.extend e (fun a => v a) (fun _ => 0))

@[simp]
theorem finiteAddressPadVector_at (e : α ↪ β) (v : EuclideanSpace ℂ α) (a : α) :
    finiteAddressPadVector e v (e a) = v a := by
  change Function.extend e (fun a => v a) (fun _ => 0) (e a) = v a
  exact e.injective.extend_apply (fun a => v a) (fun _ => 0) a

theorem finiteAddressPadVector_off (e : α ↪ β) (v : EuclideanSpace ℂ α)
    (b : β) (hb : b ∉ Set.range e) : finiteAddressPadVector e v b = 0 := by
  change Function.extend e (fun a => v a) (fun _ => 0) b = 0
  exact Function.extend_apply' (fun a => v a) (fun _ => 0) b hb

noncomputable def finiteAddressPadLinear (e : α ↪ β) :
    EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ β where
  toFun := finiteAddressPadVector e
  map_add' v w := by
    ext b
    by_cases hb : b ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hb
      simp only [finiteAddressPadVector_at, PiLp.add_apply]
    · simp only [finiteAddressPadVector_off e _ b hb, PiLp.add_apply, add_zero]
  map_smul' z v := by
    ext b
    by_cases hb : b ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hb
      simp only [finiteAddressPadVector_at, PiLp.smul_apply, RingHom.id_apply]
    · simp only [finiteAddressPadVector_off e _ b hb, PiLp.smul_apply, smul_zero]

theorem finiteAddressPadVector_sum (e : α ↪ β) (v : EuclideanSpace ℂ α) :
    (∑ b : β, ‖finiteAddressPadVector e v b‖ ^ 2) = ∑ a : α, ‖v a‖ ^ 2 := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image e, ‖finiteAddressPadVector e v b‖ ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b _ hb
      have hbr : b ∉ Set.range e := by
        intro h
        obtain ⟨a, ha⟩ := h
        exact hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)
      rw [finiteAddressPadVector_off e v b hbr]
      simp
    _ = _ := by
      rw [Finset.sum_image]
      · simp only [finiteAddressPadVector_at]
      · intro a _ a' _ h
        exact e.injective h

theorem finiteAddressPadVector_norm (e : α ↪ β) (v : EuclideanSpace ℂ α) :
    ‖finiteAddressPadVector e v‖ = ‖v‖ := by
  have hsq : ‖finiteAddressPadVector e v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    exact finiteAddressPadVector_sum e v
  nlinarith [norm_nonneg (finiteAddressPadVector e v), norm_nonneg v]

/-- Actual complex-linear zero-extension, preserving the Hilbert norm. -/
noncomputable def finiteAddressPad (e : α ↪ β) :
    EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ β where
  toLinearMap := finiteAddressPadLinear e
  norm_map' := finiteAddressPadVector_norm e

@[simp]
theorem finiteAddressPad_at (e : α ↪ β) (v : EuclideanSpace ℂ α) (a : α) :
    finiteAddressPad e v (e a) = v a := finiteAddressPadVector_at e v a

theorem finiteAddressPad_off (e : α ↪ β) (v : EuclideanSpace ℂ α)
    (b : β) (hb : b ∉ Set.range e) : finiteAddressPad e v b = 0 :=
  finiteAddressPadVector_off e v b hb

theorem finiteAddressPad_single [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (a : α) (z : ℂ) :
    finiteAddressPad e (PiLp.single 2 a z) = PiLp.single 2 (e a) z := by
  ext b
  by_cases hb : b ∈ Set.range e
  · obtain ⟨a', rfl⟩ := hb
    simp [PiLp.single_apply, e.injective.eq_iff]
  · have hba : e a ≠ b := fun h => hb ⟨a, h⟩
    simp [finiteAddressPad_off e _ b hb, PiLp.single_apply, hba]

/-- A fixed reflection in the zero-extended source vector. -/
noncomputable def paddedAddressReflection (e : α ↪ β) (u : EuclideanSpace ℂ α) :
    EuclideanSpace ℂ β ≃ₗᵢ[ℂ] EuclideanSpace ℂ β :=
  (Submodule.span ℂ {finiteAddressPad e u}).reflection

/-- Restriction is derived for every source vector, including zero. -/
theorem paddedAddressReflection_pad (e : α ↪ β) (u v : EuclideanSpace ℂ α) :
    paddedAddressReflection e u (finiteAddressPad e v) =
      finiteAddressPad e ((Submodule.span ℂ {u}).reflection v) := by
  rw [paddedAddressReflection, Submodule.reflection_singleton_apply,
    Submodule.reflection_singleton_apply, (finiteAddressPad e).inner_map_map,
    (finiteAddressPad e).norm_map]
  simp only [map_sub, map_smul, map_nsmul]

/-- All explicit basis vectors outside the source image have the required -I action. -/
theorem paddedAddressReflection_off_single [DecidableEq β]
    (e : α ↪ β) (u : EuclideanSpace ℂ α) (b : β) (hb : b ∉ Set.range e) (z : ℂ) :
    paddedAddressReflection e u (PiLp.single 2 b z) = -PiLp.single 2 b z := by
  rw [paddedAddressReflection, Submodule.reflection_singleton_apply,
    EuclideanSpace.inner_single_right, finiteAddressPad_off e u b hb]
  simp

theorem paddedAddressReflection_iterate_pad (e : α ↪ β)
    (u v : EuclideanSpace ℂ α) (m : ℕ) :
    (paddedAddressReflection e u)^[m] (finiteAddressPad e v) =
      finiteAddressPad e (((Submodule.span ℂ {u}).reflection)^[m] v) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Function.iterate_succ_apply', ih, paddedAddressReflection_pad]

/-- The coordinate phase on a proved finite marked subset. -/
noncomputable def finiteSubsetPhase [DecidableEq α] (M : Finset α) :
    EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun a => if a ∈ M then LinearIsometryEquiv.neg ℂ else
      LinearIsometryEquiv.refl ℂ ℂ)

theorem finiteSubsetPhase_apply [DecidableEq α] (M : Finset α)
    (v : EuclideanSpace ℂ α) (a : α) :
    finiteSubsetPhase M v a = if a ∈ M then -v a else v a := by
  by_cases ha : a ∈ M <;> simp [finiteSubsetPhase, ha]

theorem finiteSubsetPhase_pad [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (M : Finset α) (v : EuclideanSpace ℂ α) :
    finiteSubsetPhase (M.image e) (finiteAddressPad e v) =
      finiteAddressPad e (finiteSubsetPhase M v) := by
  ext b
  by_cases hb : b ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hb
    rw [finiteSubsetPhase_apply, finiteAddressPad_at, finiteAddressPad_at,
      finiteSubsetPhase_apply]
    have hmem : e a ∈ M.image e ↔ a ∈ M := by
      simp [Finset.mem_image, e.injective.eq_iff]
    simp only [hmem]
  · rw [finiteSubsetPhase_apply, finiteAddressPad_off e _ b hb,
      finiteAddressPad_off e _ b hb]
    split_ifs <;> simp

theorem finiteSubsetPhase_off_single [DecidableEq α]
    (M : Finset α) (a : α) (ha : a ∉ M) (z : ℂ) :
    finiteSubsetPhase M (PiLp.single 2 a z) = PiLp.single 2 a z := by
  ext b
  rw [finiteSubsetPhase_apply]
  by_cases hb : b ∈ M
  · have hba : b ≠ a := fun h => ha (h ▸ hb)
    simp [hb, PiLp.single_apply, hba]
  · simp [hb]

noncomputable def finiteSourceGrover [DecidableEq α] (M : Finset α)
    (u : EuclideanSpace ℂ α) : EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α :=
  (finiteSubsetPhase M).trans (Submodule.span ℂ {u}).reflection

/-- The full explicit unitary; only the marked phase depends on the proved marker. -/
noncomputable def paddedAddressGrover [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (M : Finset α) (u : EuclideanSpace ℂ α) :
    EuclideanSpace ℂ β ≃ₗᵢ[ℂ] EuclideanSpace ℂ β :=
  (finiteSubsetPhase (M.image e)).trans (paddedAddressReflection e u)

theorem paddedAddressGrover_pad [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (M : Finset α) (u v : EuclideanSpace ℂ α) :
    paddedAddressGrover e M u (finiteAddressPad e v) =
      finiteAddressPad e (finiteSourceGrover M u v) := by
  change paddedAddressReflection e u
      (finiteSubsetPhase (M.image e) (finiteAddressPad e v)) = _
  rw [finiteSubsetPhase_pad, paddedAddressReflection_pad]
  rfl

theorem paddedAddressGrover_iterate_pad [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (M : Finset α) (u v : EuclideanSpace ℂ α) (m : ℕ) :
    (paddedAddressGrover e M u)^[m] (finiteAddressPad e v) =
      finiteAddressPad e ((finiteSourceGrover M u)^[m] v) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Function.iterate_succ_apply', ih, paddedAddressGrover_pad]

theorem paddedAddressGrover_off_single [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (M : Finset α) (u : EuclideanSpace ℂ α)
    (b : β) (hb : b ∉ Set.range e) (z : ℂ) :
    paddedAddressGrover e M u (PiLp.single 2 b z) = -PiLp.single 2 b z := by
  have hM : b ∉ M.image e := by
    intro h
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    exact hb ⟨a, ha⟩
  change paddedAddressReflection e u (finiteSubsetPhase (M.image e) _) = _
  rw [finiteSubsetPhase_off_single _ b hM, paddedAddressReflection_off_single e u b hb]

/-- Computational-basis Born mass transports along the actual finite injection. -/
theorem finiteAddressPad_marked_born [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (v : EuclideanSpace ℂ α) (M : Finset α) :
    (∑ b ∈ M.image e, ‖finiteAddressPad e v b‖ ^ 2) = ∑ a ∈ M, ‖v a‖ ^ 2 := by
  rw [Finset.sum_image]
  · simp only [finiteAddressPad_at]
  · intro a _ a' _ h
    exact e.injective h

theorem paddedAddressGrover_iterate_marked_born [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (M : Finset α) (u v : EuclideanSpace ℂ α) (m : ℕ) :
    (∑ b ∈ M.image e,
      ‖((paddedAddressGrover e M u)^[m] (finiteAddressPad e v)) b‖ ^ 2) =
        ∑ a ∈ M, ‖((finiteSourceGrover M u)^[m] v) a‖ ^ 2 := by
  rw [paddedAddressGrover_iterate_pad]
  exact finiteAddressPad_marked_born e _ M

end FinitePad

/-- The actual numerical outside address is injected into the n-bit register. -/
def outsideBitAddress {N r n : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (i : Fin (N - r)) : BitVec n :=
  BitVec.ofNat n (outsideAddress hrN i).val

@[simp]
theorem outsideBitAddress_toNat {N r n : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (i : Fin (N - r)) : (outsideBitAddress hrN hn i).toNat = r + i.val := by
  unfold outsideBitAddress
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  · rfl
  · exact lt_of_lt_of_le (outsideAddress hrN i).isLt hn

theorem outsideBitAddress_injective {N r n : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n) :
    Function.Injective (outsideBitAddress hrN hn) := by
  intro i j h
  have hv := congrArg BitVec.toNat h
  simp only [outsideBitAddress_toNat] at hv
  apply Fin.ext
  omega

def outsideBitEmbedding {N r n : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n) :
    Fin (N - r) ↪ BitVec n :=
  ⟨outsideBitAddress hrN hn, outsideBitAddress_injective hrN hn⟩

theorem outsideBitAddress_bounds {N r n : ℕ} (hrN : r ≤ N) (hn : N ≤ 2 ^ n)
    (i : Fin (N - r)) :
    r ≤ (outsideBitAddress hrN hn i).toNat ∧ (outsideBitAddress hrN hn i).toNat < N := by
  rw [outsideBitAddress_toNat]
  have hi := i.isLt
  omega

theorem outsideBitEmbedding_mem_range_iff {N r n : ℕ}
    (hrN : r ≤ N) (hn : N ≤ 2 ^ n) (x : BitVec n) :
    x ∈ Set.range (outsideBitEmbedding hrN hn) ↔ r ≤ x.toNat ∧ x.toNat < N := by
  constructor
  · rintro ⟨i, rfl⟩
    exact outsideBitAddress_bounds hrN hn i
  · intro hx
    let i : Fin (N - r) := ⟨x.toNat - r, by omega⟩
    refine ⟨i, ?_⟩
    apply BitVec.eq_of_toNat_eq
    change (outsideBitAddress hrN hn i).toNat = x.toNat
    rw [outsideBitAddress_toNat]
    dsimp [i]
    omega

theorem outsideBitEmbedding_not_mem_of_invalid {N r n : ℕ}
    (hrN : r ≤ N) (hn : N ≤ 2 ^ n) (x : BitVec n) (hx : N ≤ x.toNat) :
    x ∉ Set.range (outsideBitEmbedding hrN hn) := by
  intro h
  obtain ⟨i, rfl⟩ := h
  exact (not_lt_of_ge hx) (outsideBitAddress_bounds hrN hn i).2

theorem outsidePaddedReflection_invalid {N r n : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (u : EuclideanSpace ℂ (Fin (N - r)))
    (x : BitVec n) (hx : N ≤ x.toNat) (z : ℂ) :
    paddedAddressReflection (outsideBitEmbedding hrN hn) u (PiLp.single 2 x z) =
      -PiLp.single 2 x z :=
  paddedAddressReflection_off_single _ u x
    (outsideBitEmbedding_not_mem_of_invalid hrN hn x hx) z

end CollisionTradeoff
