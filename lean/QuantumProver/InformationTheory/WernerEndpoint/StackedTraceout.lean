import QuantumProver.InformationTheory.WernerEndpoint.OperationalEndpointCost

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

namespace QuantumProver.WernerEndpoint.MatrixStackedTraceout

open OperationalEndpointCost

variable {O H Q I : Type*} [Fintype O] [Fintype H] [Fintype Q] [Fintype I]
  [DecidableEq O] [DecidableEq H] [DecidableEq Q] [DecidableEq I]

def selector (e : Q ≃ O × H) (h : H) : Matrix O Q ℂ :=
  fun o r => if e r = (o, h) then 1 else 0

def stack (e : Q ≃ O × H) (K : H → Matrix O I ℂ) : Matrix Q I ℂ :=
  fun r i => K (e r).2 (e r).1 i

theorem selector_complete (e : Q ≃ O × H) :
    ∑ h : H, (selector e h).conjTranspose * selector e h = 1 := by
  classical
  ext r s
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  change (∑ h : H, ∑ o : O,
    star (if e r = (o, h) then (1 : ℂ) else 0) *
      (if e s = (o, h) then (1 : ℂ) else 0)) = (1 : Matrix Q Q ℂ) r s
  simp only [Matrix.one_apply]
  have hprod : (∑ p : O × H,
      star (if e r = p then (1 : ℂ) else 0) *
        (if e s = p then (1 : ℂ) else 0)) =
      ∑ o : O, ∑ h : H,
        star (if e r = (o, h) then (1 : ℂ) else 0) *
          (if e s = (o, h) then (1 : ℂ) else 0) := by
    rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm, ← hprod]
  change (∑ p : O × H,
    star (if e r = p then (1 : ℂ) else 0) *
      (if e s = p then (1 : ℂ) else 0)) = (if r = s then 1 else 0)
  by_cases hrs : r = s
  · subst s
    simp [Matrix.one_apply]
  · have hes : e r ≠ e s := e.injective.ne hrs
    have hz (p : O × H) :
        star (if e r = p then (1 : ℂ) else 0) *
          (if e s = p then (1 : ℂ) else 0) = 0 := by
      by_cases hr : e r = p
      · have hs : e s ≠ p := fun hs => hes (hr.trans hs.symm)
        simp [hr, hs]
      · simp [hr]
    simp only [hz, Finset.sum_const_zero, Matrix.one_apply, if_neg hrs]

omit [Fintype I] [DecidableEq Q] [DecidableEq I] in

theorem selector_mul_stack (e : Q ≃ O × H) (K : H → Matrix O I ℂ) (h : H) :
    selector e h * stack e K = K h := by
  classical
  ext o i
  simp only [Matrix.mul_apply, selector, stack, ite_mul, one_mul, zero_mul]
  calc
    (∑ r : Q, if e r = (o, h) then K (e r).2 (e r).1 i else 0) =
        ∑ p : O × H, if p = (o, h) then K p.2 p.1 i else 0 :=
      e.sum_comp (fun p : O × H => if p = (o, h) then K p.2 p.1 i else 0)
    _ = K h o i := by simp

omit [Fintype I] [DecidableEq O] [DecidableEq H] [DecidableEq Q] [DecidableEq I] in

theorem stack_gram (e : Q ≃ O × H) (K : H → Matrix O I ℂ) :
    (stack e K).conjTranspose * stack e K =
      ∑ h : H, (K h).conjTranspose * K h := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, stack, Matrix.sum_apply]
  calc
    (∑ r : Q, star (K (e r).2 (e r).1 i) * K (e r).2 (e r).1 j) =
        ∑ p : O × H, star (K p.2 p.1 i) * K p.2 p.1 j :=
      e.sum_comp (fun p : O × H => star (K p.2 p.1 i) * K p.2 p.1 j)
    _ = ∑ h : H, ∑ o : O, star (K h o i) * K h o j := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm

def sandwichLinearMap (K : Matrix O I ℂ) :
    Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ where
  toFun X := K * X * K.conjTranspose
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' z X := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

def sandwichCLM (K : Matrix O I ℂ) :
    Matrix I I ℂ →L[ℂ] Matrix O O ℂ :=
  (sandwichLinearMap K).toContinuousLinearMap

omit [Fintype O] [DecidableEq O] [DecidableEq I] in
@[simp] theorem sandwichCLM_apply (K : Matrix O I ℂ) (X : Matrix I I ℂ) :
    sandwichCLM K X = K * X * K.conjTranspose := rfl

omit [DecidableEq O] [DecidableEq I] in
theorem sandwichCLM_mul {P : Type*} [Fintype P] [DecidableEq P]
    (D : Matrix P O ℂ) (K : Matrix O I ℂ) :
    (sandwichCLM D).comp (sandwichCLM K) = sandwichCLM (D * K) := by
  ext X : 1
  simp only [ContinuousLinearMap.comp_apply, sandwichCLM_apply,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

def leftSandwichCLM (R : Type*) [Fintype R] [DecidableEq R]
    (K : Matrix O I ℂ) : Matrix (I × R) (I × R) ℂ →L[ℂ]
      Matrix (O × R) (O × R) ℂ :=
  sandwichCLM (K ⊗ₖ (1 : Matrix R R ℂ))

def rightSandwichCLM (R : Type*) [Fintype R] [DecidableEq R]
    (K : Matrix O I ℂ) : Matrix (R × I) (R × I) ℂ →L[ℂ]
      Matrix (R × O) (R × O) ℂ :=
  sandwichCLM ((1 : Matrix R R ℂ) ⊗ₖ K)

theorem leftSandwichCLM_mul {P R : Type*} [Fintype P] [DecidableEq P]
    [Fintype R] [DecidableEq R] (D : Matrix P O ℂ) (K : Matrix O I ℂ) :
    (leftSandwichCLM R D).comp (leftSandwichCLM R K) =
      leftSandwichCLM R (D * K) := by
  rw [leftSandwichCLM, leftSandwichCLM, sandwichCLM_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rfl

theorem rightSandwichCLM_mul {P R : Type*} [Fintype P] [DecidableEq P]
    [Fintype R] [DecidableEq R] (D : Matrix P O ℂ) (K : Matrix O I ℂ) :
    (rightSandwichCLM R D).comp (rightSandwichCLM R K) =
      rightSandwichCLM R (D * K) := by
  rw [rightSandwichCLM, rightSandwichCLM, sandwichCLM_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rfl

theorem left_selector_stack_channel (R : Type*) [Fintype R] [DecidableEq R]
    (e : Q ≃ O × H) (K : H → Matrix O I ℂ) :
    (∑ h : H, leftSandwichCLM R (selector e h)).comp
        (leftSandwichCLM R (stack e K)) = ∑ h : H, leftSandwichCLM R (K h) := by
  ext X : 1
  simp only [ContinuousLinearMap.comp_apply, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro h _
  change ((leftSandwichCLM R (selector e h)).comp
    (leftSandwichCLM R (stack e K))) X = (leftSandwichCLM R (K h)) X
  rw [leftSandwichCLM_mul, selector_mul_stack]

theorem right_selector_stack_channel (R : Type*) [Fintype R] [DecidableEq R]
    (e : Q ≃ O × H) (K : H → Matrix O I ℂ) :
    (∑ h : H, rightSandwichCLM R (selector e h)).comp
        (rightSandwichCLM R (stack e K)) = ∑ h : H, rightSandwichCLM R (K h) := by
  ext X : 1
  simp only [ContinuousLinearMap.comp_apply, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro h _
  change ((rightSandwichCLM R (selector e h)).comp
    (rightSandwichCLM R (stack e K))) X = (rightSandwichCLM R (K h)) X
  rw [rightSandwichCLM_mul, selector_mul_stack]

section MatrixProtocol

variable {c d p q a b : ℕ}

private theorem selector_complete_fin (e : Fin q ≃ Fin p × H) :
    (∑ k : Fin (Fintype.card H),
      (selector e ((Fintype.equivFin H).symm k)).conjTranspose *
        selector e ((Fintype.equivFin H).symm k)) = 1 := by
  calc
    _ = ∑ h : H, (selector e h).conjTranspose * selector e h :=
      (Fintype.equivFin H).symm.sum_comp
        (fun h : H => (selector e h).conjTranspose * selector e h)
    _ = 1 := selector_complete e

def aliceTraceoutPrefix (e : Fin q ≃ Fin p × H)
    (U : FiniteLocalProtocol c d p b) : FiniteLocalProtocol c d q b :=
  .alice (h := 1) (z := Fintype.card H)
    (fun _ k => selector e ((Fintype.equivFin H).symm k))
    (by simpa only [Fin.sum_univ_one] using selector_complete_fin e) (fun _ => U)

def bobTraceoutPrefix (e : Fin q ≃ Fin p × H)
    (U : FiniteLocalProtocol c d a p) : FiniteLocalProtocol c d a q :=
  .bob (h := 1) (z := Fintype.card H)
    (fun _ k => selector e ((Fintype.equivFin H).symm k))
    (by simpa only [Fin.sum_univ_one] using selector_complete_fin e) (fun _ => U)

theorem aliceTraceoutPrefix_apply (e : Fin q ≃ Fin p × H)
    (U : FiniteLocalProtocol c d p b)
    (X : Matrix (Fin q × Fin b) (Fin q × Fin b) ℂ) :
    (aliceTraceoutPrefix e U).apply X =
      ∑ h : H, U.apply (leftSandwichCLM (Fin b) (selector e h) X) := by
  simp only [aliceTraceoutPrefix, FiniteLocalProtocol.apply, Fin.sum_univ_one]
  change U.apply (∑ k : Fin (Fintype.card H),
      leftSandwichCLM (Fin b) (selector e ((Fintype.equivFin H).symm k)) X) = _
  calc
    _ = U.apply (∑ h : H, leftSandwichCLM (Fin b) (selector e h) X) :=
      congrArg U.apply ((Fintype.equivFin H).symm.sum_comp
        (fun h : H => leftSandwichCLM (Fin b) (selector e h) X))
    _ = _ := map_sum U.toLinearMap _ _

theorem bobTraceoutPrefix_apply (e : Fin q ≃ Fin p × H)
    (U : FiniteLocalProtocol c d a p)
    (X : Matrix (Fin a × Fin q) (Fin a × Fin q) ℂ) :
    (bobTraceoutPrefix e U).apply X =
      ∑ h : H, U.apply (rightSandwichCLM (Fin a) (selector e h) X) := by
  simp only [bobTraceoutPrefix, FiniteLocalProtocol.apply, Fin.sum_univ_one]
  change U.apply (∑ k : Fin (Fintype.card H),
      rightSandwichCLM (Fin a) (selector e ((Fintype.equivFin H).symm k)) X) = _
  calc
    _ = U.apply (∑ h : H, rightSandwichCLM (Fin a) (selector e h) X) :=
      congrArg U.apply ((Fintype.equivFin H).symm.sum_comp
        (fun h : H => rightSandwichCLM (Fin a) (selector e h) X))
    _ = _ := map_sum U.toLinearMap _ _

def finiteChannel (U : FiniteLocalProtocol c d a b) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ →L[ℂ]
      Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ :=
  U.toLinearMap.toContinuousLinearMap

@[simp] theorem finiteChannel_apply (U : FiniteLocalProtocol c d a b)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    finiteChannel U X = U.apply X := rfl

theorem aliceTraceoutPrefix_channel (e : Fin q ≃ Fin p × H)
    (U : FiniteLocalProtocol c d p b) :
    finiteChannel (aliceTraceoutPrefix e U) =
      ∑ h : H, (finiteChannel U).comp (leftSandwichCLM (Fin b) (selector e h)) := by
  ext X : 1
  simpa only [_root_.sum_apply, ContinuousLinearMap.comp_apply,
    finiteChannel_apply] using aliceTraceoutPrefix_apply e U X

theorem bobTraceoutPrefix_channel (e : Fin q ≃ Fin p × H)
    (U : FiniteLocalProtocol c d a p) :
    finiteChannel (bobTraceoutPrefix e U) =
      ∑ h : H, (finiteChannel U).comp (rightSandwichCLM (Fin a) (selector e h)) := by
  ext X : 1
  simpa only [_root_.sum_apply, ContinuousLinearMap.comp_apply,
    finiteChannel_apply] using bobTraceoutPrefix_apply e U X

def aliceTraceout (e : Fin q ≃ Fin p × H) (b : ℕ) : FiniteLocalProtocol p b q b :=
  aliceTraceoutPrefix e (.terminal 1 1 (by simp) (by simp))

def bobTraceout (e : Fin q ≃ Fin p × H) (a : ℕ) : FiniteLocalProtocol a p a q :=
  bobTraceoutPrefix e (.terminal 1 1 (by simp) (by simp))

theorem aliceTraceout_apply (e : Fin q ≃ Fin p × H) (b : ℕ)
    (X : Matrix (Fin q × Fin b) (Fin q × Fin b) ℂ) :
    (aliceTraceout e b).apply X = ∑ h : H, leftSandwichCLM (Fin b) (selector e h) X := by
  rw [aliceTraceout, aliceTraceoutPrefix_apply]
  simp only [FiniteLocalProtocol.apply, Matrix.one_kronecker_one,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem bobTraceout_apply (e : Fin q ≃ Fin p × H) (a : ℕ)
    (X : Matrix (Fin a × Fin q) (Fin a × Fin q) ℂ) :
    (bobTraceout e a).apply X = ∑ h : H, rightSandwichCLM (Fin a) (selector e h) X := by
  rw [bobTraceout, bobTraceoutPrefix_apply]
  simp only [FiniteLocalProtocol.apply, Matrix.one_kronecker_one,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem aliceTraceoutPrefix_stack_channel (e : Fin q ≃ Fin p × H)
    (K : H → Matrix (Fin p) (Fin a) ℂ) (U : FiniteLocalProtocol c d p b) :
    (finiteChannel (aliceTraceoutPrefix e U)).comp
        (leftSandwichCLM (Fin b) (stack e K)) =
      ∑ h : H, (finiteChannel U).comp (leftSandwichCLM (Fin b) (K h)) := by
  rw [aliceTraceoutPrefix_channel]
  ext X : 1
  simp only [ContinuousLinearMap.comp_apply, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  change ((leftSandwichCLM (Fin b) (selector e h)).comp
    (leftSandwichCLM (Fin b) (stack e K))) X = (leftSandwichCLM (Fin b) (K h)) X
  rw [leftSandwichCLM_mul, selector_mul_stack]

theorem bobTraceoutPrefix_stack_channel (e : Fin q ≃ Fin p × H)
    (K : H → Matrix (Fin p) (Fin b) ℂ) (U : FiniteLocalProtocol c d a p) :
    (finiteChannel (bobTraceoutPrefix e U)).comp
        (rightSandwichCLM (Fin a) (stack e K)) =
      ∑ h : H, (finiteChannel U).comp (rightSandwichCLM (Fin a) (K h)) := by
  rw [bobTraceoutPrefix_channel]
  ext X : 1
  simp only [ContinuousLinearMap.comp_apply, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  change ((rightSandwichCLM (Fin a) (selector e h)).comp
    (rightSandwichCLM (Fin a) (stack e K))) X = (rightSandwichCLM (Fin a) (K h)) X
  rw [rightSandwichCLM_mul, selector_mul_stack]

end MatrixProtocol
end QuantumProver.WernerEndpoint.MatrixStackedTraceout
