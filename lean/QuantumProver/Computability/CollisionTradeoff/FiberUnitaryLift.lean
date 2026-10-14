import QuantumProver.Computability.CollisionTradeoff.RegisterEncoding

/-!
A fixed address-space unitary is lifted over every retained rest-register
value.  Its restriction to a fixed rest basis vector is derived exactly, so
oracle-dependent table data never needs to become an implemented gate parameter.
This supplies a finite Hilbert bridge; it does not assert explicit query cost.
-/

namespace CollisionTradeoff

open scoped BigOperators Classical

def productToFiberEquiv (α β : Type*) : (α × β) ≃ (Σ _b : β, α) where
  toFun p := ⟨p.2, p.1⟩
  invFun p := (p.2, p.1)
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

noncomputable def basisProductCurry (α β : Type*) [Fintype α] [Fintype β] :
    EuclideanSpace ℂ (α × β) ≃ₗᵢ[ℂ] PiLp 2 (fun _b : β => EuclideanSpace ℂ α) :=
  (basisEquivUnitary (productToFiberEquiv α β)).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun _b : β => fun _a : α => ℂ))

theorem basisProductCurry_apply {α β : Type*} [Fintype α] [Fintype β]
    (v : EuclideanSpace ℂ (α × β)) (b : β) (a : α) :
    basisProductCurry α β v b a = v (a, b) := rfl

theorem basisProductCurry_symm_apply {α β : Type*} [Fintype α] [Fintype β]
    (v : PiLp 2 (fun _b : β => EuclideanSpace ℂ α)) (a : α) (b : β) :
    (basisProductCurry α β).symm v (a, b) = v b a := rfl

/-- Apply the same fixed address unitary on every possible retained-data fiber. -/
noncomputable def fiberUnitaryLift {α β : Type*} [Fintype α] [Fintype β]
    (U : EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α) :
    EuclideanSpace ℂ (α × β) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (α × β) :=
  (basisProductCurry α β).trans
    ((LinearIsometryEquiv.piLpCongrRight 2 (fun _b : β => U)).trans
      (basisProductCurry α β).symm)

theorem fiberUnitaryLift_apply {α β : Type*} [Fintype α] [Fintype β]
    (U : EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (v : EuclideanSpace ℂ (α × β)) (a : α) (b : β) :
    fiberUnitaryLift (β := β) U v (a, b) =
      U (WithLp.toLp 2 (fun x : α => v (x, b))) a := rfl

theorem fiberUnitaryLift_norm {α β : Type*} [Fintype α] [Fintype β]
    (U : EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (v : EuclideanSpace ℂ (α × β)) : ‖fiberUnitaryLift U v‖ = ‖v‖ :=
  (fiberUnitaryLift U).norm_map v

/-- An address amplitude vector with a fixed basis value in every other register. -/
def basisTensorSlice {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (v : EuclideanSpace ℂ α) (b₀ : β) : EuclideanSpace ℂ (α × β) :=
  WithLp.toLp 2 (fun p => if p.2 = b₀ then v p.1 else 0)

theorem fiberUnitaryLift_slice {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (U : EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (v : EuclideanSpace ℂ α) (b₀ : β) :
    fiberUnitaryLift U (basisTensorSlice v b₀) = basisTensorSlice (U v) b₀ := by
  ext p
  rcases p with ⟨a, b⟩
  rw [fiberUnitaryLift_apply]
  by_cases hb : b = b₀
  · have hslice : (WithLp.toLp 2 (fun x : α => basisTensorSlice v b₀ (x, b))) = v := by
      ext x
      simp [basisTensorSlice, hb]
    rw [hslice]
    simp [basisTensorSlice, hb]
  · have hslice : (WithLp.toLp 2 (fun x : α => basisTensorSlice v b₀ (x, b))) = 0 := by
      ext x
      simp [basisTensorSlice, hb]
    rw [hslice]
    simp [basisTensorSlice, hb]

theorem fiberUnitaryLift_iterate_slice {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq β]
    (U : EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (v : EuclideanSpace ℂ α) (b₀ : β) (m : ℕ) :
    (fiberUnitaryLift U)^[m] (basisTensorSlice v b₀) =
      basisTensorSlice (U^[m] v) b₀ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [Function.iterate_succ_apply', ih, fiberUnitaryLift_slice]

/-- Marginal address Born mass is preserved by adjoining a fixed retained-data basis. -/
theorem basisTensorSlice_marked_born {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (v : EuclideanSpace ℂ α) (b₀ : β) (M : Finset α) :
    (∑ p : α × β, if p.1 ∈ M then ‖basisTensorSlice v b₀ p‖ ^ 2 else 0) =
      ∑ a ∈ M, ‖v a‖ ^ 2 := by
  have hinner (a : α) :
      (∑ b : β, if a ∈ M then ‖basisTensorSlice v b₀ (a, b)‖ ^ 2 else 0) =
        if a ∈ M then ‖v a‖ ^ 2 else 0 := by
    by_cases ha : a ∈ M
    · simp only [if_pos ha]
      calc
        (∑ b : β, ‖basisTensorSlice v b₀ (a, b)‖ ^ 2) =
            ∑ b : β, if b = b₀ then ‖v a‖ ^ 2 else 0 := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases hb : b = b₀ <;> simp [basisTensorSlice, hb]
        _ = _ := by simp
    · simp [ha]
  rw [Fintype.sum_prod_type]
  simp_rw [hinner]
  have hfilter : Finset.univ.filter (fun a : α => a ∈ M) = M := by ext a; simp
  rw [Finset.sum_ite, hfilter]
  simp

theorem fiberUnitaryLift_iterate_marked_born {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (U : EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α)
    (v : EuclideanSpace ℂ α) (b₀ : β) (M : Finset α) (m : ℕ) :
    (∑ p : α × β, if p.1 ∈ M then
      ‖((fiberUnitaryLift U)^[m] (basisTensorSlice v b₀)) p‖ ^ 2 else 0) =
        ∑ a ∈ M, ‖(U^[m] v) a‖ ^ 2 := by
  rw [fiberUnitaryLift_iterate_slice]
  exact basisTensorSlice_marked_born (U^[m] v) b₀ M

/-- Every retained field except the main address remains in this explicit fiber. -/
abbrev CollisionRest (r b n k c : ℕ) :=
  (Fin r → BitVec b) × Bool × BitVec n × MarkerScratch n k ×
    BitVec c × BitVec n × BitVec n × Bool

def collisionAddressRestEquiv (r b n k c : ℕ) :
    CollisionRegisters r b n k c ≃ (BitVec n × CollisionRest r b n k c) where
  toFun s := (s.mainAddress, (s.table, s.good, s.physicalOracleAddress,
    s.scratch, s.controller, s.outputFirst, s.outputSecond, s.outputValid))
  invFun p :=
    { mainAddress := p.1
      table := p.2.1
      good := p.2.2.1
      physicalOracleAddress := p.2.2.2.1
      scratch := p.2.2.2.2.1
      controller := p.2.2.2.2.2.1
      outputFirst := p.2.2.2.2.2.2.1
      outputSecond := p.2.2.2.2.2.2.2.1
      outputValid := p.2.2.2.2.2.2.2.2 }
  left_inv s := by cases s; rfl
  right_inv p := by rcases p with ⟨x, a, g, q, t, j, u, v, ok⟩; rfl

/-- A fixed n-bit main-address unitary on the complete counted register frame. -/
noncomputable def collisionMainUnitary (r b n k c : ℕ)
    (U : EuclideanSpace ℂ (BitVec n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (BitVec n)) :
    EuclideanSpace ℂ (CollisionRegisters r b n k c) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (CollisionRegisters r b n k c) :=
  let E := basisEquivUnitary (collisionAddressRestEquiv r b n k c)
  E.trans ((fiberUnitaryLift U).trans E.symm)

end CollisionTradeoff
