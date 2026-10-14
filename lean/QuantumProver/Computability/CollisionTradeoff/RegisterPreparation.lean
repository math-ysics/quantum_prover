import QuantumProver.Computability.CollisionTradeoff.FiberUnitaryLift
import QuantumProver.Computability.CollisionTradeoff.PaddedAddress

/-!
A fixed, oracle-independent Householder preparation on the explicit address
register and its action on every retained-data fiber of the counted frame.
The algorithm specialization assumes 0 < r < N, so the zero explicit address
is orthogonal to the outside interval.  No r=0 endpoint is silently included.
No oracle function is an argument of any preparation definition.
-/

namespace CollisionTradeoff

open scoped BigOperators Classical

/-- The source constant vector, definitionally identical to A's uniformAddress. -/
noncomputable def outsideUniformVector (L : ℕ) : EuclideanSpace ℂ (Fin L) :=
  WithLp.toLp 2 (fun _ => (((Real.sqrt (L : ℝ))⁻¹ : ℝ) : ℂ))

theorem outsideUniformVector_norm {L : ℕ} (hL : 0 < L) :
    ‖outsideUniformVector L‖ = 1 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hsq : Real.sqrt (L : ℝ) ^ 2 = L := Real.sq_sqrt hL0.le
  have hnorm : ‖outsideUniformVector L‖ ^ 2 = 1 := by
    calc
      _ = ∑ _ : Fin L, ((Real.sqrt (L : ℝ))⁻¹ : ℝ) ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        simp [outsideUniformVector, Complex.norm_real, Real.norm_eq_abs]
      _ = (L : ℝ) * (Real.sqrt (L : ℝ))⁻¹ ^ 2 := by simp
      _ = 1 := by rw [inv_pow, hsq]; exact mul_inv_cancel₀ hL0.ne'
  nlinarith [norm_nonneg (outsideUniformVector L)]

noncomputable def registerOutsideUniform {N r n : ℕ}
    (hrN : r ≤ N) (hn : N ≤ 2 ^ n) : EuclideanSpace ℂ (BitVec n) :=
  finiteAddressPad (outsideBitEmbedding hrN hn) (outsideUniformVector (N - r))

def registerZeroAddress (n : ℕ) : EuclideanSpace ℂ (BitVec n) :=
  PiLp.single 2 (0 : BitVec n) (1 : ℂ)

theorem registerZeroAddress_norm (n : ℕ) : ‖registerZeroAddress n‖ = 1 := by
  simp [registerZeroAddress]

theorem registerOutsideUniform_norm {N r n : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hL : r < N) : ‖registerOutsideUniform hrN hn‖ = 1 := by
  rw [registerOutsideUniform, (finiteAddressPad _).norm_map]
  exact outsideUniformVector_norm (by omega)

theorem registerOutsideUniform_zero {N r n : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hr : 0 < r) : registerOutsideUniform hrN hn (0 : BitVec n) = 0 := by
  have hoff : (0 : BitVec n) ∉ Set.range (outsideBitEmbedding hrN hn) := by
    intro h
    have hbounds := (outsideBitEmbedding_mem_range_iff hrN hn (0 : BitVec n)).mp h
    have hz : r ≤ 0 := by simpa using hbounds.1
    omega
  exact finiteAddressPad_off _ _ _ hoff

theorem registerZeroAddress_orthogonal {N r n : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hr : 0 < r) :
    inner ℂ (registerZeroAddress n) (registerOutsideUniform hrN hn) = 0 := by
  rw [registerZeroAddress, EuclideanSpace.inner_single_left,
    registerOutsideUniform_zero hrN hn hr]
  simp

section Householder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A fixed span-reflection exchanging two orthogonal unit vectors. -/
noncomputable def orthogonalHouseholder (u v : E) : E ≃ₗᵢ[ℂ] E :=
  (Submodule.span ℂ {u + v}).reflection

theorem orthogonalHouseholder_prepares (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℂ u v = 0) : orthogonalHouseholder u v u = v := by
  have hrev : inner ℂ v u = 0 := inner_eq_zero_symm.mp huv
  have hnorm : ‖u + v‖ ^ 2 = (2 : ℝ) := by
    rw [norm_add_sq (𝕜 := ℂ), hu, hv, huv]
    norm_num
  have hnormC : (‖u + v‖ : ℂ) ^ 2 = (2 : ℂ) := by
    exact_mod_cast hnorm
  have hinner : inner ℂ (u + v) u = 1 := by
    rw [inner_add_left, inner_self_eq_norm_sq_to_K, hu, hrev]
    norm_num
  rw [orthogonalHouseholder, Submodule.reflection_singleton_apply (𝕜 := ℂ), hinner]
  change (2 : ℕ) • (((1 : ℂ) / (‖u + v‖ : ℂ) ^ 2) • (u + v)) - u = v
  rw [hnormC]
  norm_num [two_smul, ← add_smul]

theorem orthogonalHouseholder_involutive (u v : E) :
    Function.Involutive (orthogonalHouseholder u v) :=
  Submodule.reflection_involutive _

end Householder

/-- This preparation depends only on the interval/register parameters, never f. -/
noncomputable def fixedOutsidePreparation {N r n : ℕ}
    (hrN : r ≤ N) (hn : N ≤ 2 ^ n) :
    EuclideanSpace ℂ (BitVec n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (BitVec n) :=
  orthogonalHouseholder (registerZeroAddress n) (registerOutsideUniform hrN hn)

theorem fixedOutsidePreparation_prepares {N r n : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hr : 0 < r) (hL : r < N) :
    fixedOutsidePreparation hrN hn (registerZeroAddress n) = registerOutsideUniform hrN hn := by
  exact orthogonalHouseholder_prepares _ _ (registerZeroAddress_norm n)
    (registerOutsideUniform_norm hrN hn hL) (registerZeroAddress_orthogonal hrN hn hr)

theorem fixedOutsidePreparation_unprepares {N r n : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hr : 0 < r) (hL : r < N) :
    fixedOutsidePreparation hrN hn (registerOutsideUniform hrN hn) = registerZeroAddress n := by
  have h : fixedOutsidePreparation hrN hn
      (fixedOutsidePreparation hrN hn (registerZeroAddress n)) = registerZeroAddress n :=
    orthogonalHouseholder_involutive _ _ _
  rw [fixedOutsidePreparation_prepares hrN hn hr hL] at h
  exact h

theorem basisEquivUnitary_symm {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) : (basisEquivUnitary e).symm = basisEquivUnitary e.symm := by
  simp only [basisEquivUnitary, LinearIsometryEquiv.piLpCongrLeft_symm]

theorem basisTensorSlice_single {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (a : α) (b : β) (z : ℂ) :
    basisTensorSlice (PiLp.single 2 a z) b = PiLp.single 2 (a, b) z := by
  ext p
  rcases p with ⟨a', b'⟩
  by_cases hb : b' = b
  · subst b'
    simp [basisTensorSlice, PiLp.single_apply]
  · simp [basisTensorSlice, PiLp.single_apply, hb, Ne.symm hb]

/-- The full counted frame with an arbitrary address vector and retained rest basis. -/
noncomputable def collisionFrameSlice {r b n k c : ℕ}
    (v : EuclideanSpace ℂ (BitVec n)) (rest : CollisionRest r b n k c) :
    EuclideanSpace ℂ (CollisionRegisters r b n k c) :=
  (basisEquivUnitary (collisionAddressRestEquiv r b n k c)).symm (basisTensorSlice v rest)

theorem collisionFrameSlice_apply {r b n k c : ℕ}
    (v : EuclideanSpace ℂ (BitVec n)) (rest : CollisionRest r b n k c)
    (s : CollisionRegisters r b n k c) :
    collisionFrameSlice v rest s =
      if (collisionAddressRestEquiv r b n k c s).2 = rest then v s.mainAddress else 0 := rfl

theorem collisionFrameSlice_single {r b n k c : ℕ} (x : BitVec n)
    (rest : CollisionRest r b n k c) (z : ℂ) :
    collisionFrameSlice (PiLp.single 2 x z) rest =
      PiLp.single 2 ((collisionAddressRestEquiv r b n k c).symm (x, rest)) z := by
  rw [collisionFrameSlice, basisTensorSlice_single, basisEquivUnitary_symm]
  exact basisEquivUnitary_single _ _ z

theorem collisionMainUnitary_slice {r b n k c : ℕ}
    (U : EuclideanSpace ℂ (BitVec n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (BitVec n))
    (v : EuclideanSpace ℂ (BitVec n)) (rest : CollisionRest r b n k c) :
    collisionMainUnitary r b n k c U (collisionFrameSlice v rest) =
      collisionFrameSlice (U v) rest := by
  unfold collisionMainUnitary collisionFrameSlice
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
    fiberUnitaryLift_slice]

theorem collisionMainUnitary_iterate_slice {r b n k c : ℕ}
    (U : EuclideanSpace ℂ (BitVec n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (BitVec n))
    (v : EuclideanSpace ℂ (BitVec n)) (rest : CollisionRest r b n k c) (m : ℕ) :
    (collisionMainUnitary r b n k c U)^[m] (collisionFrameSlice v rest) =
      collisionFrameSlice (U^[m] v) rest := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Function.iterate_succ_apply', ih, collisionMainUnitary_slice]

/-- A fixed rest value is analysis data, not a parameter of the implemented unitary. -/
def collisionFrameEmbedding {r b n k c : ℕ} (rest : CollisionRest r b n k c) :
    BitVec n ↪ CollisionRegisters r b n k c where
  toFun x := (collisionAddressRestEquiv r b n k c).symm (x, rest)
  inj' := by
    intro x y h
    have hp := (collisionAddressRestEquiv r b n k c).symm.injective h
    exact congrArg Prod.fst hp

theorem collisionFrameSlice_eq_pad {r b n k c : ℕ}
    (v : EuclideanSpace ℂ (BitVec n)) (rest : CollisionRest r b n k c) :
    collisionFrameSlice v rest = finiteAddressPad (collisionFrameEmbedding rest) v := by
  ext s
  by_cases hr : (collisionAddressRestEquiv r b n k c s).2 = rest
  · have hs : collisionFrameEmbedding rest s.mainAddress = s := by
      apply (collisionAddressRestEquiv r b n k c).injective
      change (collisionAddressRestEquiv r b n k c)
          ((collisionAddressRestEquiv r b n k c).symm (s.mainAddress, rest)) = _
      rw [Equiv.apply_symm_apply]
      change (s.mainAddress, rest) = (s.mainAddress, (collisionAddressRestEquiv r b n k c s).2)
      rw [hr]
    rw [collisionFrameSlice_apply, if_pos hr]
    symm
    calc
      _ = finiteAddressPad (collisionFrameEmbedding rest) v
          (collisionFrameEmbedding rest s.mainAddress) := congrArg _ hs.symm
      _ = v s.mainAddress := finiteAddressPad_at _ _ _
  · have hoff : s ∉ Set.range (collisionFrameEmbedding rest) := by
      rintro ⟨x, rfl⟩
      have he : (collisionAddressRestEquiv r b n k c (collisionFrameEmbedding rest x)).2 = rest := by
        change ((collisionAddressRestEquiv r b n k c)
          ((collisionAddressRestEquiv r b n k c).symm (x, rest))).2 = rest
        rw [Equiv.apply_symm_apply]
      exact hr he
    rw [collisionFrameSlice_apply, if_neg hr, finiteAddressPad_off _ _ _ hoff]

theorem collisionMainUnitary_pad {r b n k c : ℕ}
    (U : EuclideanSpace ℂ (BitVec n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (BitVec n))
    (v : EuclideanSpace ℂ (BitVec n)) (rest : CollisionRest r b n k c) :
    collisionMainUnitary r b n k c U (finiteAddressPad (collisionFrameEmbedding rest) v) =
      finiteAddressPad (collisionFrameEmbedding rest) (U v) := by
  rw [← collisionFrameSlice_eq_pad v rest, collisionMainUnitary_slice, collisionFrameSlice_eq_pad]

theorem finiteAddressPad_comp {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (e : α ↪ β) (d : β ↪ γ) (v : EuclideanSpace ℂ α) :
    finiteAddressPad d (finiteAddressPad e v) = finiteAddressPad (e.trans d) v := by
  ext b
  by_cases hb : b ∈ Set.range d
  · obtain ⟨y, rfl⟩ := hb
    rw [finiteAddressPad_at]
    by_cases hy : y ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hy
      rw [finiteAddressPad_at]
      exact (finiteAddressPad_at (e.trans d) v a).symm
    · have hoff : d y ∉ Set.range (e.trans d) := by
        rintro ⟨a, ha⟩
        exact hy ⟨a, d.injective ha⟩
      rw [finiteAddressPad_off e v y hy, finiteAddressPad_off _ _ _ hoff]
  · have hoff : b ∉ Set.range (e.trans d) := by
      rintro ⟨a, ha⟩
      exact hb ⟨e a, ha⟩
    rw [finiteAddressPad_off d _ b hb, finiteAddressPad_off _ _ _ hoff]

def outsideFrameEmbedding {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (rest : CollisionRest r b n k c) :
    Fin (N - r) ↪ CollisionRegisters r b n k c :=
  (outsideBitEmbedding hrN hn).trans (collisionFrameEmbedding rest)

/-- A fixed preparation on the complete counted frame, with no hidden ancillary register. -/
noncomputable def fixedCollisionPreparation {N r b n k c : ℕ}
    (hrN : r ≤ N) (hn : N ≤ 2 ^ n) :
    EuclideanSpace ℂ (CollisionRegisters r b n k c) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (CollisionRegisters r b n k c) :=
  collisionMainUnitary r b n k c (fixedOutsidePreparation hrN hn)

theorem fixedCollisionPreparation_prepares {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hr : 0 < r) (hL : r < N) (rest : CollisionRest r b n k c) :
    fixedCollisionPreparation hrN hn (collisionFrameSlice (registerZeroAddress n) rest) =
      collisionFrameSlice (registerOutsideUniform hrN hn) rest := by
  rw [fixedCollisionPreparation, collisionMainUnitary_slice,
    fixedOutsidePreparation_prepares hrN hn hr hL]

theorem fixedCollisionPreparation_single {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hr : 0 < r) (hL : r < N) (rest : CollisionRest r b n k c) :
    fixedCollisionPreparation hrN hn
      (PiLp.single 2 ((collisionAddressRestEquiv r b n k c).symm ((0 : BitVec n), rest)) 1) =
        collisionFrameSlice (registerOutsideUniform hrN hn) rest := by
  rw [← collisionFrameSlice_single, ← registerZeroAddress]
  exact fixedCollisionPreparation_prepares hrN hn hr hL rest

theorem fixedCollisionPreparation_outside_pad {N r b n k c : ℕ} (hrN : r ≤ N)
    (hn : N ≤ 2 ^ n) (hr : 0 < r) (hL : r < N) (rest : CollisionRest r b n k c) :
    fixedCollisionPreparation hrN hn
      (PiLp.single 2 ((collisionAddressRestEquiv r b n k c).symm ((0 : BitVec n), rest)) 1) =
        finiteAddressPad (outsideFrameEmbedding hrN hn rest) (outsideUniformVector (N - r)) := by
  rw [fixedCollisionPreparation_single hrN hn hr hL rest,
    collisionFrameSlice_eq_pad, registerOutsideUniform, finiteAddressPad_comp]
  rfl

end CollisionTradeoff
