import QuantumProver.QuantumGates.ControlledCliffordHierarchy.ControlledFamily

noncomputable section

open scoped Matrix BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

@[simp] theorem conjugate_one {n : ℕ} (P : QuantumMatrix n) :
    conjugate 1 P = P := by simp [conjugate]

@[simp] theorem conjugate_identity {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) : conjugate U 1 = 1 := by
  simpa [conjugate] using hU.2

theorem conjugate_comp {n : ℕ} (U V P : QuantumMatrix n) :
    conjugate (U * V) P = conjugate U (conjugate V P) := by
  simp only [conjugate, Matrix.conjTranspose_mul, mul_assoc]

theorem conjugate_conjugate {n : ℕ} (C U P : QuantumMatrix n) :
    conjugate (conjugate C U) P =
      conjugate C (conjugate U (conjugate C.conjTranspose P)) := by
  simp only [conjugate, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, mul_assoc]

theorem conjugate_smul_right {n : ℕ} (U P : QuantumMatrix n) (a : ℂ) :
    conjugate U (a • P) = a • conjugate U P := by
  simp only [conjugate, mul_smul_comm, smul_mul_assoc]

theorem conjugate_smul_left {n : ℕ} (U P : QuantumMatrix n) {a : ℂ}
    (ha : star a * a = 1) : conjugate (a • U) P = conjugate U P := by
  have ha' : a * star a = 1 := by simpa only [mul_comm] using ha
  simp only [conjugate, Matrix.conjTranspose_smul, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  simp only [ha, ha', one_smul]

theorem conjugate_mul {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (P Q : QuantumMatrix n) :
    conjugate U (P * Q) = conjugate U P * conjugate U Q := by
  have hcancel :
      U * P * U.conjTranspose * (U * Q * U.conjTranspose) =
        U * P * (U.conjTranspose * U) * Q * U.conjTranspose := by
    simp only [mul_assoc]
  rw [conjugate, conjugate, conjugate, hcancel, hU.1, mul_one]
  simp only [mul_assoc]

theorem conjugate_inverse_left {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (P : QuantumMatrix n) :
    conjugate U.conjTranspose (conjugate U P) = P := by
  rw [← conjugate_comp, hU.1, conjugate_one]

theorem conjugate_inverse_right {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (P : QuantumMatrix n) :
    conjugate U (conjugate U.conjTranspose P) = P := by
  rw [← conjugate_comp, hU.2, conjugate_one]

theorem conjugate_unitary {n : ℕ} {U P : QuantumMatrix n}
    (hU : unitaryMatrix U) (hP : unitaryMatrix P) :
    unitaryMatrix (conjugate U P) :=
  unitaryMatrix_mul (unitaryMatrix_mul hU hP) (unitaryMatrix_conjTranspose hU)

theorem actualPauli_conjugate {n : ℕ} {U P : QuantumMatrix n}
    (hU : actualPauli U) (hP : actualPauli P) : actualPauli (conjugate U P) :=
  actualPauli_mul (actualPauli_mul hU hP) (actualPauli_conjTranspose hU)

theorem actualPauli_finite (n : ℕ) : Finite {U : QuantumMatrix n // actualPauli U} := by
  have hphase : Set.Finite {a : ℂ | PauliPhase a} := by
    change Set.Finite ({1} ∪ ({-1} ∪ ({Complex.I} ∪ {-Complex.I})))
    exact (Set.finite_singleton 1).union ((Set.finite_singleton (-1)).union
      ((Set.finite_singleton Complex.I).union (Set.finite_singleton (-Complex.I))))
  letI : Finite {a : ℂ // PauliPhase a} := hphase.to_subtype
  let lift : ({a : ℂ // PauliPhase a} × BitString n × BitString n) →
      {U : QuantumMatrix n // actualPauli U} := fun p =>
    ⟨p.1.val • orderedPauli p.2.1 p.2.2,
      ⟨p.1.val, p.2.1, p.2.2, p.1.property, rfl⟩⟩
  have hlift : Function.Surjective lift := by
    intro P
    rcases P.property with ⟨a, x, z, ha, heq⟩
    refine ⟨(⟨a, ha⟩, x, z), ?_⟩
    apply Subtype.ext
    exact heq.symm
  exact Finite.of_surjective lift hlift

theorem clifford_conjTranspose {n : ℕ} {C : QuantumMatrix n}
    (hC : hierarchy n 2 C) : hierarchy n 2 C.conjTranspose := by
  letI : Finite {P : QuantumMatrix n // actualPauli P} := actualPauli_finite n
  let f : {P : QuantumMatrix n // actualPauli P} →
      {P : QuantumMatrix n // actualPauli P} := fun P =>
    ⟨conjugate C P.val, hC.2 P.val P.property⟩
  have hinj : Function.Injective f := by
    intro P Q heq
    apply Subtype.ext
    have hv : conjugate C P.val = conjugate C Q.val := congrArg Subtype.val heq
    have hinv := congrArg (conjugate C.conjTranspose) hv
    simpa only [conjugate_inverse_left hC.1] using hinv
  have hsurj := Finite.surjective_of_injective hinj
  refine ⟨unitaryMatrix_conjTranspose hC.1, ?_⟩
  intro P hP
  obtain ⟨Q, hQ⟩ := hsurj ⟨P, hP⟩
  have hval : conjugate C Q.val = P := congrArg Subtype.val hQ
  rw [← hval, conjugate_inverse_left hC.1]
  exact Q.property

theorem hierarchy_unitary {n r : ℕ} {U : QuantumMatrix n}
    (hr : 1 ≤ r) (hU : hierarchy n r U) : unitaryMatrix U := by
  cases r with
  | zero => omega
  | succ r =>
    cases r with
    | zero => exact actualPauli_unitary hU
    | succ k => exact hU.1

theorem hierarchy_step {n r : ℕ} {U : QuantumMatrix n}
    (hr : 1 ≤ r) (hU : hierarchy n r U) : hierarchy n (r + 1) U := by
  induction r generalizing U with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero =>
      exact ⟨actualPauli_unitary hU,
        fun P hP => actualPauli_conjugate hU hP⟩
    | succ k =>
      exact ⟨hU.1, fun P hP => ih (by omega) (hU.2 P hP)⟩

theorem hierarchy_mono {n r s : ℕ} {U : QuantumMatrix n}
    (hr : 1 ≤ r) (hrs : r ≤ s) (hU : hierarchy n r U) : hierarchy n s U := by
  induction s, hrs using Nat.le_induction with
  | base => exact hU
  | succ s hrs ih => exact hierarchy_step (by omega) ih

theorem actualPauli_hierarchy {n r : ℕ} {P : QuantumMatrix n}
    (hr : 1 ≤ r) (hP : actualPauli P) : hierarchy n r P :=
  hierarchy_mono (by omega) hr hP

theorem hierarchy_clifford_conjugate {n r : ℕ} {C U : QuantumMatrix n}
    (hr : 1 ≤ r) (hC : hierarchy n 2 C) (hU : hierarchy n r U) :
    hierarchy n r (conjugate C U) := by
  induction r generalizing U with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero => exact hC.2 U hU
    | succ k =>
      refine ⟨conjugate_unitary hC.1 hU.1, ?_⟩
      intro P hP
      rw [conjugate_conjugate]
      exact ih (by omega) (hU.2 _ ((clifford_conjTranspose hC).2 P hP))

theorem hierarchy_clifford_conjugate_iff {n r : ℕ} {C U : QuantumMatrix n}
    (hr : 1 ≤ r) (hC : hierarchy n 2 C) :
    hierarchy n r (conjugate C U) ↔ hierarchy n r U := by
  constructor
  · intro h
    have hi := hierarchy_clifford_conjugate hr (clifford_conjTranspose hC) h
    simpa only [conjugate_inverse_left hC.1] using hi
  · exact hierarchy_clifford_conjugate hr hC

theorem hierarchy_clifford_mul_left {n r : ℕ} {C U : QuantumMatrix n}
    (hr : 2 ≤ r) (hC : hierarchy n 2 C) (hU : hierarchy n r U) :
    hierarchy n r (C * U) := by
  cases r with
  | zero => omega
  | succ r =>
    cases r with
    | zero => omega
    | succ k =>
      refine ⟨unitaryMatrix_mul hC.1 hU.1, ?_⟩
      intro P hP
      rw [conjugate_comp]
      exact hierarchy_clifford_conjugate (by omega) hC (hU.2 P hP)

theorem hierarchy_clifford_mul_right {n r : ℕ} {C U : QuantumMatrix n}
    (hr : 2 ≤ r) (hC : hierarchy n 2 C) (hU : hierarchy n r U) :
    hierarchy n r (U * C) := by
  cases r with
  | zero => omega
  | succ r =>
    cases r with
    | zero => omega
    | succ k =>
      refine ⟨unitaryMatrix_mul hU.1 hC.1, ?_⟩
      intro P hP
      rw [conjugate_comp]
      exact hU.2 _ (hC.2 P hP)

theorem hierarchy_pauli_mul_left {n r : ℕ} {P U : QuantumMatrix n}
    (hr : 1 ≤ r) (hP : actualPauli P) (hU : hierarchy n r U) :
    hierarchy n r (P * U) := by
  by_cases htwo : 2 ≤ r
  · exact hierarchy_clifford_mul_left htwo (actualPauli_hierarchy (by omega) hP) hU
  · have heq : r = 1 := by omega
    subst r
    exact actualPauli_mul hP hU

theorem hierarchy_pauli_mul_right {n r : ℕ} {P U : QuantumMatrix n}
    (hr : 1 ≤ r) (hP : actualPauli P) (hU : hierarchy n r U) :
    hierarchy n r (U * P) := by
  by_cases htwo : 2 ≤ r
  · exact hierarchy_clifford_mul_right htwo (actualPauli_hierarchy (by omega) hP) hU
  · have heq : r = 1 := by omega
    subst r
    exact actualPauli_mul hU hP

theorem hierarchy_pauli_mul_right_iff {n r : ℕ} {P U : QuantumMatrix n}
    (hr : 1 ≤ r) (hP : actualPauli P) :
    hierarchy n r (U * P) ↔ hierarchy n r U := by
  constructor
  · intro h
    have hi := hierarchy_pauli_mul_right hr (actualPauli_conjTranspose hP) h
    simpa only [mul_assoc, (actualPauli_unitary hP).2, mul_one] using hi
  · exact hierarchy_pauli_mul_right hr hP

theorem hierarchy_smul_unit_scalar {n r : ℕ} {a : ℂ} {U : QuantumMatrix n}
    (hr : 2 ≤ r) (ha : star a * a = 1) (hU : hierarchy n r U) :
    hierarchy n r (a • U) := by
  cases r with
  | zero => omega
  | succ r =>
    cases r with
    | zero => omega
    | succ k =>
      refine ⟨unitaryMatrix_smul ha hU.1, ?_⟩
      intro P hP
      rw [conjugate_smul_left U P ha]
      exact hU.2 P hP

theorem hierarchy_smul_unit_scalar_iff {n r : ℕ} {a : ℂ} {U : QuantumMatrix n}
    (hr : 2 ≤ r) (ha : star a * a = 1) :
    hierarchy n r (a • U) ↔ hierarchy n r U := by
  constructor
  · intro h
    have ha' : star (star a) * star a = 1 := by
      simpa only [star_star, mul_comm] using ha
    have hi := hierarchy_smul_unit_scalar hr ha' h
    simpa only [smul_smul, ha, one_smul] using hi
  · exact hierarchy_smul_unit_scalar hr ha

theorem hierarchy_smul_pauliPhase {n r : ℕ} {a : ℂ} {U : QuantumMatrix n}
    (hr : 1 ≤ r) (ha : PauliPhase a) (hU : hierarchy n r U) :
    hierarchy n r (a • U) := by
  by_cases htwo : 2 ≤ r
  · exact hierarchy_smul_unit_scalar htwo (pauliPhase_star_mul ha) hU
  · have heq : r = 1 := by omega
    subst r
    exact actualPauli_smul ha hU

theorem hierarchy_iff_pauliCorrections {n k : ℕ} (U : QuantumMatrix n) :
    hierarchy n (k + 2) U ↔ unitaryMatrix U ∧
      ∀ P : QuantumMatrix n, actualPauli P →
        hierarchy n (k + 1) (pauliCorrection U P) := by
  rw [hierarchy_succ_succ]
  constructor
  · rintro ⟨hU, hconj⟩
    exact ⟨hU, fun P hP => hierarchy_pauli_mul_right (by omega)
      (actualPauli_conjTranspose hP) (hconj P hP)⟩
  · rintro ⟨hU, hcorr⟩
    refine ⟨hU, fun P hP => ?_⟩
    exact (hierarchy_pauli_mul_right_iff (by omega)
      (actualPauli_conjTranspose hP)).mp (hcorr P hP)

theorem exactLevel_of_previous_not {n r : ℕ} {U : QuantumMatrix n}
    (hr : 1 ≤ r) (hU : hierarchy n (r + 1) U)
    (hnot : ¬ hierarchy n r U) : exactLevel (r + 1) U := by
  refine ⟨by omega, hU, ?_⟩
  intro t ht htr hsmall
  exact hnot (hierarchy_mono ht (by omega) hsmall)

theorem pauliPhase_ne_zero {a : ℂ} (ha : PauliPhase a) : a ≠ 0 := by
  intro hz
  have h := pauliPhase_star_mul ha
  rw [hz, star_zero, mul_zero] at h
  exact zero_ne_one h

theorem xMatrix_apply {n : ℕ} (x row col : BitString n) :
    xMatrix x row col = if col = row + x then 1 else 0 := by
  classical
  simp [xMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, shiftPerm, eq_comm]

theorem orderedPauli_apply {n : ℕ} (x z row col : BitString n) :
    orderedPauli x z row col = if col = row + x then character z col else 0 := by
  classical
  simp only [orderedPauli, zMatrix, Matrix.mul_diagonal, xMatrix_apply]
  by_cases h : col = row + x <;> simp [h]

theorem basisCons_add {n : ℕ} (a b : ZMod 2) (x y : BitString n) :
    basisCons a x + basisCons b y = basisCons (a + b) (x + y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [basisCons]

theorem basisCons_eq_cons_iff {n : ℕ} (a b : ZMod 2) (x y : BitString n) :
    basisCons a x = basisCons b y ↔ a = b ∧ x = y := by
  constructor
  · intro h
    constructor
    · simpa only [basisHead_cons] using congrArg basisHead h
    · simpa only [basisTail_cons] using congrArg basisTail h
  · rintro ⟨rfl, rfl⟩
    rfl

theorem dot_cons {n : ℕ} (a b : ZMod 2) (x y : BitString n) :
    dot (basisCons a x) (basisCons b y) = a * b + dot x y := by
  simp [dot, basisCons, Fin.sum_univ_succ]

theorem character_cons {n : ℕ} (a b : ZMod 2) (x y : BitString n) :
    character (basisCons a x) (basisCons b y) = bitSign (a * b) * character x y := by
  rw [character, dot_cons, bitSign_add]
  rfl

theorem orderedPauli_apply_cons {n : ℕ} (a b c d : ZMod 2)
    (x z row col : BitString n) :
    orderedPauli (basisCons a x) (basisCons b z) (basisCons c row) (basisCons d col) =
      if d = c + a then bitSign (b * d) * orderedPauli x z row col else 0 := by
  classical
  simp only [orderedPauli_apply, basisCons_add, basisCons_eq_cons_iff, character_cons]
  by_cases hh : d = c + a <;> by_cases ht : col = row + x <;> simp [hh, ht]

theorem physical_control_bit_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  exact (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a

theorem orderedPauli_zero_head {n : ℕ} (b : ZMod 2) (x z : BitString n) :
    orderedPauli (basisCons 0 x) (basisCons b z) =
      branchMatrix (orderedPauli x z) (bitSign b • orderedPauli x z) := by
  classical
  ext row col
  obtain ⟨⟨c, row⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective row
  obtain ⟨⟨d, col⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective col
  change orderedPauli (basisCons 0 x) (basisCons b z)
      (basisCons c row) (basisCons d col) =
    branchMatrix (orderedPauli x z) (bitSign b • orderedPauli x z)
      (basisCons c row) (basisCons d col)
  rcases physical_control_bit_cases c with rfl | rfl <;>
    rcases physical_control_bit_cases d with rfl | rfl <;>
    norm_num [orderedPauli_apply_cons, branchMatrix_apply_cons,
      Matrix.smul_apply, smul_eq_mul, CharTwo.add_self_eq_zero, CharTwo.two_eq_zero]

theorem branchMatrix_smul {n : ℕ} (a : ℂ) (B A : QuantumMatrix n) :
    branchMatrix (a • B) (a • A) = a • branchMatrix B A := by
  classical
  ext row col
  by_cases hh : basisHead row = basisHead col
  · by_cases hz : basisHead row = 0 <;> simp [branchMatrix, hh, hz]
  · simp [branchMatrix, hh]

theorem branchMatrix_injective {n : ℕ} {B A D C : QuantumMatrix n}
    (h : branchMatrix B A = branchMatrix D C) : B = D ∧ A = C := by
  constructor
  · ext row col
    have he := congrArg (fun M : QuantumMatrix (n + 1) =>
      M (basisCons 0 row) (basisCons 0 col)) h
    simpa using he
  · ext row col
    have he := congrArg (fun M : QuantumMatrix (n + 1) =>
      M (basisCons 1 row) (basisCons 1 col)) h
    simpa using he

theorem actualPauli_lift {n : ℕ} {P : QuantumMatrix n} (hP : actualPauli P) :
    actualPauli (branchMatrix P P) := by
  rcases hP with ⟨a, x, z, ha, rfl⟩
  refine ⟨a, basisCons 0 x, basisCons 0 z, ha, ?_⟩
  rw [orderedPauli_zero_head, bitSign_zero, one_smul, branchMatrix_smul]

theorem actualPauli_branch_blocks {n : ℕ} {B A : QuantumMatrix n}
    (h : actualPauli (branchMatrix B A)) : actualPauli B ∧ actualPauli A := by
  classical
  rcases h with ⟨a, x, z, ha, heq⟩
  obtain ⟨⟨t, x⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective x
  obtain ⟨⟨v, z⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective z
  change branchMatrix B A = a • orderedPauli (basisCons t x) (basisCons v z) at heq
  have ht : t = 0 := by
    by_contra ht
    have he := congrArg (fun M : QuantumMatrix (n + 1) =>
      M 0 (basisCons t x)) heq
    have hb : branchMatrix B A 0 (basisCons t x) = 0 := by
      simp [branchMatrix, basisHead, basisCons, Ne.symm ht]
    have hp : orderedPauli (basisCons t x) (basisCons v z) 0 (basisCons t x) =
        character (basisCons v z) (basisCons t x) := by
      simp [orderedPauli_apply]
    rw [hb, Matrix.smul_apply, smul_eq_mul, hp] at he
    exact (mul_ne_zero (pauliPhase_ne_zero ha)
      (pauliPhase_ne_zero (character_phase _ _))) he.symm
  subst t
  rw [orderedPauli_zero_head, ← branchMatrix_smul] at heq
  obtain ⟨hB, hA⟩ := branchMatrix_injective heq
  refine ⟨⟨a, x, z, ha, hB⟩,
    ⟨a * bitSign v, x, z, pauliPhase_mul ha (bitSign_phase v), ?_⟩⟩
  simpa only [smul_smul] using hA

theorem branchMatrix_unitary_blocks {n : ℕ} {B A : QuantumMatrix n}
    (h : unitaryMatrix (branchMatrix B A)) : unitaryMatrix B ∧ unitaryMatrix A := by
  have hleft := h.1
  have hright := h.2
  rw [branchMatrix_conjTranspose, branchMatrix_mul, ← branchMatrix_one_one n] at hleft
  rw [branchMatrix_conjTranspose, branchMatrix_mul, ← branchMatrix_one_one n] at hright
  obtain ⟨hB₁, hA₁⟩ := branchMatrix_injective hleft
  obtain ⟨hB₂, hA₂⟩ := branchMatrix_injective hright
  exact ⟨⟨hB₁, hB₂⟩, ⟨hA₁, hA₂⟩⟩

theorem conjugate_branch_lift {n : ℕ} (B A P : QuantumMatrix n) :
    conjugate (branchMatrix B A) (branchMatrix P P) =
      branchMatrix (conjugate B P) (conjugate A P) := by
  simp only [conjugate, branchMatrix_conjTranspose, branchMatrix_mul]

theorem hierarchy_branch_blocks {n r : ℕ} {B A : QuantumMatrix n}
    (hr : 1 ≤ r) (h : hierarchy (n + 1) r (branchMatrix B A)) :
    hierarchy n r B ∧ hierarchy n r A := by
  induction r generalizing B A with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero => exact actualPauli_branch_blocks h
    | succ k =>
      obtain ⟨hB, hA⟩ := branchMatrix_unitary_blocks h.1
      have hp : ∀ P : QuantumMatrix n, actualPauli P →
          hierarchy n (k + 1) (conjugate B P) ∧
          hierarchy n (k + 1) (conjugate A P) := by
        intro P hP
        have hc := h.2 (branchMatrix P P) (actualPauli_lift hP)
        rw [conjugate_branch_lift] at hc
        exact ih (by omega) hc
      exact ⟨⟨hB, fun P hP => (hp P hP).1⟩,
        ⟨hA, fun P hP => (hp P hP).2⟩⟩

def physicalHeadX (n : ℕ) : QuantumMatrix (n + 1) := xMatrix (basisCons 1 0)

theorem physicalHeadX_actual (n : ℕ) : actualPauli (physicalHeadX n) := by
  simpa only [physicalHeadX, orderedPauli_x] using
    orderedPauli_actual (basisCons 1 (0 : BitString n)) 0

theorem physicalHeadX_adjoint (n : ℕ) :
    (physicalHeadX n).conjTranspose = physicalHeadX n := xMatrix_conjTranspose _

theorem xMatrix_mul_left {n : ℕ} (x : BitString n) (M : QuantumMatrix n)
    (row col : BitString n) : (xMatrix x * M) row col = M (row + x) col := by
  classical
  change (((shiftPerm x).toPEquiv.toMatrix : QuantumMatrix n) * M) row col = _
  rw [PEquiv.toMatrix_mul_apply, Equiv.toPEquiv_apply]
  rfl

theorem xMatrix_mul_right {n : ℕ} (x : BitString n) (M : QuantumMatrix n)
    (row col : BitString n) : (M * xMatrix x) row col = M row (col + x) := by
  classical
  change (M * ((shiftPerm x).toPEquiv.toMatrix : QuantumMatrix n)) row col = _
  rw [PEquiv.mul_toMatrix_apply, ← Equiv.toPEquiv_symm, Equiv.toPEquiv_apply]
  rfl

theorem physicalHeadX_conjugate_branch {n : ℕ} (B A : QuantumMatrix n) :
    conjugate (physicalHeadX n) (branchMatrix B A) = branchMatrix A B := by
  classical
  ext row col
  simp only [conjugate, physicalHeadX, xMatrix_conjTranspose,
    xMatrix_mul_right, xMatrix_mul_left]
  obtain ⟨⟨c, row⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective row
  obtain ⟨⟨d, col⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective col
  change branchMatrix B A (basisCons c row + basisCons 1 0)
      (basisCons d col + basisCons 1 0) =
    branchMatrix A B (basisCons c row) (basisCons d col)
  rw [basisCons_add, basisCons_add]
  rcases physical_control_bit_cases c with rfl | rfl <;>
    rcases physical_control_bit_cases d with rfl | rfl <;>
    norm_num [branchMatrix_apply_cons, CharTwo.add_self_eq_zero, CharTwo.two_eq_zero] <;>
    simp [show (2 : ZMod 2) = 0 by decide]

theorem pauliCorrection_branch_headX {n : ℕ} (B A : QuantumMatrix n) :
    pauliCorrection (branchMatrix B A) (physicalHeadX n) =
      branchMatrix (B * A.conjTranspose) (A * B.conjTranspose) := by
  rw [pauliCorrection, conjugate, physicalHeadX_adjoint]
  calc
    branchMatrix B A * physicalHeadX n * (branchMatrix B A).conjTranspose * physicalHeadX n =
        branchMatrix B A * conjugate (physicalHeadX n) (branchMatrix B A).conjTranspose := by
      simp only [conjugate, physicalHeadX_adjoint, mul_assoc]
    _ = branchMatrix B A * branchMatrix A.conjTranspose B.conjTranspose := by
      rw [branchMatrix_conjTranspose, physicalHeadX_conjugate_branch]
    _ = _ := branchMatrix_mul _ _ _ _

theorem pauliCorrection_controlled_headX {n : ℕ} (U : QuantumMatrix n) :
    pauliCorrection (controlled U) (physicalHeadX n) = branchMatrix U.conjTranspose U := by
  simp only [controlled, pauliCorrection_branch_headX, Matrix.conjTranspose_one,
    one_mul, mul_one]

theorem pauliCorrection_balanced_headX {n : ℕ} (U : QuantumMatrix n) :
    pauliCorrection (branchMatrix U.conjTranspose U) (physicalHeadX n) =
      branchMatrix (U ^ 2).conjTranspose (U ^ 2) := by
  simp only [pauliCorrection_branch_headX, Matrix.conjTranspose_conjTranspose,
    pow_two, Matrix.conjTranspose_mul]

theorem balancedBranch_dyadic_power_pauli {n a : ℕ} {U : QuantumMatrix n}
    (h : hierarchy (n + 1) (a + 1) (branchMatrix U.conjTranspose U)) :
    actualPauli (U ^ (2 ^ a)) := by
  induction a generalizing U with
  | zero => simpa using (actualPauli_branch_blocks h).2
  | succ a ih =>
    have hc := ((hierarchy_iff_pauliCorrections _).mp h).2 _ (physicalHeadX_actual n)
    rw [pauliCorrection_balanced_headX] at hc
    have hp := ih hc
    simpa only [← pow_mul, ← Nat.pow_succ'] using hp

theorem controlled_dyadic_power_pauli {n a : ℕ} {U : QuantumMatrix n}
    (h : hierarchy (n + 1) (a + 2) (controlled U)) : actualPauli (U ^ (2 ^ a)) := by
  have hc := ((hierarchy_iff_pauliCorrections _).mp h).2 _ (physicalHeadX_actual n)
  rw [pauliCorrection_controlled_headX] at hc
  exact balancedBranch_dyadic_power_pauli hc

theorem controlled_period_lower {n a m : ℕ} {U : QuantumMatrix n}
    (hU : actualPauliPeriod m U)
    (h : hierarchy (n + 1) (a + 2) (controlled U)) : m ≤ a := by
  by_contra hm
  exact hU.2 a (by omega) (controlled_dyadic_power_pauli h)

theorem orderedPauli_commute {n : ℕ} (x z y w : BitString n) :
    orderedPauli x z * orderedPauli y w =
      (character z y * character w x) • (orderedPauli y w * orderedPauli x z) := by
  rw [orderedPauli_mul, orderedPauli_mul, smul_smul]
  rw [add_comm y x, add_comm w z]
  congr 1
  rw [mul_assoc, character_mul_self, mul_one]

theorem actualPauli_commute_sign {n : ℕ} {P Q : QuantumMatrix n}
    (hP : actualPauli P) (hQ : actualPauli Q) :
    ∃ t : ZMod 2, P * Q = bitSign t • (Q * P) := by
  rcases hP with ⟨a, x, z, ha, rfl⟩
  rcases hQ with ⟨b, y, w, hb, rfl⟩
  refine ⟨dot z y + dot w x, ?_⟩
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [orderedPauli_commute, smul_smul, bitSign_add]
  simp only [character]
  congr 1
  ring

theorem actualPauli_conjugate_sign {n : ℕ} {P Q : QuantumMatrix n}
    (hP : actualPauli P) (hQ : actualPauli Q) :
    ∃ t : ZMod 2, conjugate P Q = bitSign t • Q := by
  obtain ⟨t, ht⟩ := actualPauli_commute_sign hP hQ
  refine ⟨t, ?_⟩
  rw [conjugate, ht, smul_mul_assoc, mul_assoc, (actualPauli_unitary hP).2, mul_one]

theorem pauliPhase_square_sign {a : ℂ} (ha : PauliPhase a) :
    ∃ t : ZMod 2, a * a = bitSign t := by
  rcases ha with rfl | rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp [Complex.I_mul_I]⟩
  · exact ⟨1, by simp [Complex.I_mul_I]⟩

theorem actualPauli_square_sign {n : ℕ} {P : QuantumMatrix n}
    (hP : actualPauli P) : ∃ t : ZMod 2, P ^ 2 = bitSign t • (1 : QuantumMatrix n) := by
  rcases hP with ⟨a, x, z, ha, rfl⟩
  obtain ⟨b, hb⟩ := pauliPhase_square_sign ha
  refine ⟨b + dot z x, ?_⟩
  rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hb,
    ← pow_two, orderedPauli_sq, smul_smul, bitSign_add]
  rfl

theorem actualPauli_adjoint_sign {n : ℕ} {P : QuantumMatrix n}
    (hP : actualPauli P) : ∃ t : ZMod 2, P.conjTranspose = bitSign t • P := by
  obtain ⟨t, ht⟩ := actualPauli_square_sign hP
  refine ⟨t, ?_⟩
  have hc : P ^ 2 * P.conjTranspose = P := by
    rw [pow_two, mul_assoc, (actualPauli_unitary hP).2, mul_one]
  have hs : P = bitSign t • P.conjTranspose := by
    calc
      P = P ^ 2 * P.conjTranspose := hc.symm
      _ = bitSign t • P.conjTranspose := by rw [ht, smul_mul_assoc, one_mul]
  calc
    P.conjTranspose = bitSign t • (bitSign t • P.conjTranspose) := by
      rw [smul_smul, bitSign_mul_self, one_smul]
    _ = bitSign t • P := by rw [← hs]

theorem orderedPauli_cons_factor_x {n : ℕ} (a b : ZMod 2) (x z : BitString n) :
    orderedPauli (basisCons a x) (basisCons b z) =
      xMatrix (basisCons a 0) *
        branchMatrix (orderedPauli x z) (bitSign b • orderedPauli x z) := by
  classical
  ext row col
  rw [xMatrix_mul_left]
  obtain ⟨⟨c, row⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective row
  obtain ⟨⟨d, col⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective col
  change orderedPauli (basisCons a x) (basisCons b z)
      (basisCons c row) (basisCons d col) =
    branchMatrix (orderedPauli x z) (bitSign b • orderedPauli x z)
      (basisCons c row + basisCons a 0) (basisCons d col)
  rw [basisCons_add]
  rcases physical_control_bit_cases a with rfl | rfl <;>
    rcases physical_control_bit_cases c with rfl | rfl <;>
    rcases physical_control_bit_cases d with rfl | rfl <;>
    norm_num [orderedPauli_apply_cons, branchMatrix_apply_cons,
      Matrix.smul_apply, smul_eq_mul, CharTwo.add_self_eq_zero, CharTwo.two_eq_zero] <;>
    simp [show (2 : ZMod 2) = 0 by decide]

def matrixHeadPauli (n : ℕ) (a b : ZMod 2) : QuantumMatrix (n + 1) :=
  orderedPauli (basisCons a 0) (basisCons b 0)

theorem matrixHeadPauli_actual (n : ℕ) (a b : ZMod 2) :
    actualPauli (matrixHeadPauli n a b) := orderedPauli_actual _ _

theorem orderedPauli_cons_factor {n : ℕ} (a b : ZMod 2) (x z : BitString n) :
    orderedPauli (basisCons a x) (basisCons b z) =
      matrixHeadPauli n a b * branchMatrix (orderedPauli x z) (orderedPauli x z) := by
  simp only [matrixHeadPauli, orderedPauli_cons_factor_x, orderedPauli_zero,
    mul_assoc, branchMatrix_mul, one_mul, smul_mul_assoc]

theorem branchMatrix_lift_commutes_headX {n : ℕ} (U : QuantumMatrix n) (a : ZMod 2) :
    branchMatrix U U * xMatrix (basisCons a 0) =
      xMatrix (basisCons a 0) * branchMatrix U U := by
  classical
  ext row col
  rw [xMatrix_mul_right, xMatrix_mul_left]
  obtain ⟨⟨c, row⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective row
  obtain ⟨⟨d, col⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective col
  change branchMatrix U U (basisCons c row) (basisCons d col + basisCons a 0) =
    branchMatrix U U (basisCons c row + basisCons a 0) (basisCons d col)
  rw [basisCons_add, basisCons_add]
  rcases physical_control_bit_cases a with rfl | rfl <;>
    rcases physical_control_bit_cases c with rfl | rfl <;>
    rcases physical_control_bit_cases d with rfl | rfl <;>
    norm_num [branchMatrix_apply_cons, CharTwo.add_self_eq_zero, CharTwo.two_eq_zero] <;>
    simp [show (2 : ZMod 2) = 0 by decide]

theorem branchMatrix_lift_commutes_headPauli {n : ℕ}
    (U : QuantumMatrix n) (a b : ZMod 2) :
    branchMatrix U U * matrixHeadPauli n a b =
      matrixHeadPauli n a b * branchMatrix U U := by
  rw [matrixHeadPauli, orderedPauli_cons_factor_x, orderedPauli_zero]
  rw [← mul_assoc, branchMatrix_lift_commutes_headX, mul_assoc, mul_assoc]
  congr 1
  simp only [branchMatrix_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]

theorem conjugate_lift_headPauli {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (a b : ZMod 2) :
    conjugate (branchMatrix U U) (matrixHeadPauli n a b) = matrixHeadPauli n a b := by
  rw [conjugate, branchMatrix_lift_commutes_headPauli, mul_assoc,
    (branchMatrix_unitary hU hU).2, mul_one]

theorem hierarchy_lift {n r : ℕ} {U : QuantumMatrix n}
    (hr : 1 ≤ r) (hU : hierarchy n r U) :
    hierarchy (n + 1) r (branchMatrix U U) := by
  induction r generalizing U with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero => exact actualPauli_lift hU
    | succ k =>
      have hu : unitaryMatrix (branchMatrix U U) := branchMatrix_unitary hU.1 hU.1
      refine ⟨hu, ?_⟩
      intro P hP
      rcases hP with ⟨a, x, z, ha, rfl⟩
      obtain ⟨⟨c, x⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective x
      obtain ⟨⟨d, z⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective z
      change hierarchy (n + 1) (k + 1)
        (conjugate (branchMatrix U U)
          (a • orderedPauli (basisCons c x) (basisCons d z)))
      rw [conjugate_smul_right, orderedPauli_cons_factor, conjugate_mul hu,
        conjugate_lift_headPauli hU.1, conjugate_branch_lift]
      exact hierarchy_smul_pauliPhase (by omega) ha
        (hierarchy_pauli_mul_left (by omega) (matrixHeadPauli_actual n c d)
          (ih (by omega) (hU.2 _ (orderedPauli_actual x z))))

theorem hierarchy_lift_iff {n r : ℕ} {U : QuantumMatrix n} (hr : 1 ≤ r) :
    hierarchy (n + 1) r (branchMatrix U U) ↔ hierarchy n r U := by
  exact ⟨fun h => (hierarchy_branch_blocks hr h).1, hierarchy_lift hr⟩

theorem actualPauli_lift_iff {n : ℕ} {U : QuantumMatrix n} :
    actualPauli (branchMatrix U U) ↔ actualPauli U := by
  exact ⟨fun h => (actualPauli_branch_blocks h).1, actualPauli_lift⟩

theorem exactLevel_lift_iff {n r : ℕ} {U : QuantumMatrix n} :
    exactLevel r (branchMatrix U U) ↔ exactLevel r U := by
  constructor
  · rintro ⟨hr, hU, hlow⟩
    exact ⟨hr, (hierarchy_lift_iff hr).mp hU,
      fun t ht htr hsmall => hlow t ht htr (hierarchy_lift ht hsmall)⟩
  · rintro ⟨hr, hU, hlow⟩
    exact ⟨hr, hierarchy_lift hr hU,
      fun t ht htr hsmall => hlow t ht htr ((hierarchy_lift_iff ht).mp hsmall)⟩

theorem actualPauliPeriod_lift_iff {n m : ℕ} {U : QuantumMatrix n} :
    actualPauliPeriod m (branchMatrix U U) ↔ actualPauliPeriod m U := by
  unfold actualPauliPeriod
  simp only [branchMatrix_pow, actualPauli_lift_iff]

theorem pauliCorrection_smul_right {n : ℕ} (U P : QuantumMatrix n) {a : ℂ}
    (ha : star a * a = 1) : pauliCorrection U (a • P) = pauliCorrection U P := by
  have ha' : a * star a = 1 := by simpa only [mul_comm] using ha
  simp only [pauliCorrection, conjugate_smul_right, Matrix.conjTranspose_smul,
    smul_mul_assoc, mul_smul_comm, smul_smul, ha, ha', one_smul]

theorem pauliCorrection_branchMatrix {n : ℕ} (B A P Q : QuantumMatrix n) :
    pauliCorrection (branchMatrix B A) (branchMatrix P Q) =
      branchMatrix (pauliCorrection B P) (pauliCorrection A Q) := by
  simp only [pauliCorrection, conjugate, branchMatrix_conjTranspose, branchMatrix_mul]

theorem pauliCorrection_controlled_lift {n : ℕ} (U : QuantumMatrix n)
    {P : QuantumMatrix n} (hP : unitaryMatrix P) :
    pauliCorrection (controlled U) (branchMatrix P P) = controlled (pauliCorrection U P) := by
  have hp : pauliCorrection (1 : QuantumMatrix n) P = 1 := by
    simpa only [pauliCorrection, conjugate_one] using hP.2
  simp only [controlled, pauliCorrection_branchMatrix, hp]

theorem pauliCorrection_controlled_headX_branch {n : ℕ}
    (U M N : QuantumMatrix n) :
    pauliCorrection (controlled U) (physicalHeadX n * branchMatrix M N) =
      branchMatrix (conjugate N U.conjTranspose) (U * (M * M.conjTranspose)) := by
  have hm : branchMatrix M N * (controlled U).conjTranspose *
      (branchMatrix M N).conjTranspose =
      branchMatrix (M * M.conjTranspose) (N * U.conjTranspose * N.conjTranspose) := by
    simp only [controlled, branchMatrix_conjTranspose, branchMatrix_mul,
      Matrix.conjTranspose_one, mul_one]
  simp only [pauliCorrection, conjugate, Matrix.conjTranspose_mul, physicalHeadX_adjoint]
  calc
    controlled U * (physicalHeadX n * branchMatrix M N) * (controlled U).conjTranspose *
        ((branchMatrix M N).conjTranspose * physicalHeadX n) =
      controlled U * conjugate (physicalHeadX n)
        (branchMatrix M N * (controlled U).conjTranspose *
          (branchMatrix M N).conjTranspose) := by
      simp only [conjugate, physicalHeadX_adjoint, mul_assoc]
    _ = controlled U * branchMatrix
        (N * U.conjTranspose * N.conjTranspose) (M * M.conjTranspose) := by
      rw [hm, physicalHeadX_conjugate_branch]
    _ = _ := by simp only [controlled, branchMatrix_mul, one_mul, conjugate]

theorem pauliCorrection_controlled_headX_lift {n : ℕ} (U : QuantumMatrix n)
    {P : QuantumMatrix n} (hP : unitaryMatrix P) :
    pauliCorrection (controlled U) (physicalHeadX n * branchMatrix P P) =
      branchMatrix (conjugate P U.conjTranspose) U := by
  rw [pauliCorrection_controlled_headX_branch, hP.2, mul_one]

theorem pauliCorrection_controlled_ordered_zero {n : ℕ}
    (U : QuantumMatrix n) (b : ZMod 2) (x z : BitString n) :
    pauliCorrection (controlled U) (orderedPauli (basisCons 0 x) (basisCons b z)) =
      controlled (pauliCorrection U (orderedPauli x z)) := by
  have hp : pauliCorrection (1 : QuantumMatrix n) (orderedPauli x z) = 1 := by
    simpa only [pauliCorrection, conjugate_one] using (orderedPauli_unitary x z).2
  rw [orderedPauli_zero_head, controlled, pauliCorrection_branchMatrix, hp,
    pauliCorrection_smul_right U (orderedPauli x z) (by simp)]
  rfl

theorem pauliCorrection_controlled_ordered_one {n : ℕ}
    (U : QuantumMatrix n) (b : ZMod 2) (x z : BitString n) :
    pauliCorrection (controlled U) (orderedPauli (basisCons 1 x) (basisCons b z)) =
      branchMatrix (conjugate (orderedPauli x z) U.conjTranspose) U := by
  rw [orderedPauli_cons_factor_x]
  change pauliCorrection (controlled U)
      (physicalHeadX n * branchMatrix (orderedPauli x z) (bitSign b • orderedPauli x z)) = _
  rw [pauliCorrection_controlled_headX_branch,
    conjugate_smul_left (orderedPauli x z) U.conjTranspose (by simp),
    (orderedPauli_unitary x z).2, mul_one]

theorem controlled_hierarchy_iff {n k : ℕ} (U : QuantumMatrix n) :
    hierarchy (n + 1) (k + 2) (controlled U) ↔ unitaryMatrix U ∧
      ∀ P : QuantumMatrix n, actualPauli P →
        hierarchy (n + 1) (k + 1) (controlled (pauliCorrection U P)) ∧
        hierarchy (n + 1) (k + 1) (branchMatrix (conjugate P U.conjTranspose) U) := by
  rw [hierarchy_iff_pauliCorrections]
  constructor
  · rintro ⟨hu, hc⟩
    refine ⟨(branchMatrix_unitary_blocks hu).2, ?_⟩
    intro P hP
    constructor
    · have hh := hc (branchMatrix P P) (actualPauli_lift hP)
      rwa [pauliCorrection_controlled_lift U (actualPauli_unitary hP)] at hh
    · have hh := hc (physicalHeadX n * branchMatrix P P)
        (actualPauli_mul (physicalHeadX_actual n) (actualPauli_lift hP))
      rwa [pauliCorrection_controlled_headX_lift U (actualPauli_unitary hP)] at hh
  · rintro ⟨hu, hc⟩
    refine ⟨controlled_unitary hu, ?_⟩
    intro P hP
    rcases hP with ⟨a, x, z, ha, rfl⟩
    obtain ⟨⟨c, x⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective x
    obtain ⟨⟨d, z⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective z
    change hierarchy (n + 1) (k + 1)
      (pauliCorrection (controlled U) (a • orderedPauli (basisCons c x) (basisCons d z)))
    rw [pauliCorrection_smul_right _ _ (pauliPhase_star_mul ha)]
    rcases physical_control_bit_cases c with rfl | rfl
    · rw [pauliCorrection_controlled_ordered_zero]
      exact (hc _ (orderedPauli_actual x z)).1
    · rw [pauliCorrection_controlled_ordered_one]
      exact (hc _ (orderedPauli_actual x z)).2

theorem controlled_sign_scalar_actual (n : ℕ) (t : ZMod 2) :
    actualPauli (controlled (bitSign t • (1 : QuantumMatrix n))) := by
  simpa only [orderedPauli_zero_head, orderedPauli_zero, controlled] using
    orderedPauli_actual (basisCons 0 (0 : BitString n)) (basisCons t (0 : BitString n))

theorem actualPauli_branch_sign {n : ℕ} {P : QuantumMatrix n}
    (hP : actualPauli P) (t : ZMod 2) : actualPauli (branchMatrix P (bitSign t • P)) := by
  have h := actualPauli_mul (actualPauli_lift hP) (controlled_sign_scalar_actual n t)
  simpa only [controlled, branchMatrix_mul, mul_one, mul_smul_comm] using h

theorem actualPauli_branch_sign_left {n : ℕ} {P : QuantumMatrix n}
    (hP : actualPauli P) (t : ZMod 2) : actualPauli (branchMatrix (bitSign t • P) P) := by
  have h := actualPauli_smul (bitSign_phase t) (actualPauli_branch_sign hP t)
  simpa only [← branchMatrix_smul, smul_smul, bitSign_mul_self, one_smul] using h

theorem controlled_actualPauli_clifford {n : ℕ} {P : QuantumMatrix n}
    (hP : actualPauli P) : hierarchy (n + 1) 2 (controlled P) := by
  apply (controlled_hierarchy_iff P).mpr
  refine ⟨actualPauli_unitary hP, ?_⟩
  intro Q hQ
  constructor
  · obtain ⟨t, ht⟩ := actualPauli_conjugate_sign hP hQ
    have hc : pauliCorrection P Q = bitSign t • (1 : QuantumMatrix n) := by
      rw [pauliCorrection, ht, smul_mul_assoc, (actualPauli_unitary hQ).2]
    rw [hc]
    exact controlled_sign_scalar_actual n t
  · obtain ⟨s, hs⟩ := actualPauli_conjugate_sign hQ (actualPauli_conjTranspose hP)
    obtain ⟨t, ht⟩ := actualPauli_adjoint_sign hP
    rw [hs, ht, smul_smul, ← bitSign_add]
    exact actualPauli_branch_sign_left hP (s + t)

theorem clifford_pow {n : ℕ} {C : QuantumMatrix n} (hC : hierarchy n 2 C) (a : ℕ) :
    hierarchy n 2 (C ^ a) := by
  induction a with
  | zero => simpa using actualPauli_hierarchy (by omega) (actualPauli_one n)
  | succ a ih => simpa only [pow_succ] using hierarchy_clifford_mul_right (by omega) hC ih

theorem unitary_move_matrix {n : ℕ} {C : QuantumMatrix n} (hC : unitaryMatrix C)
    (P : QuantumMatrix n) : P * C = C * conjugate C.conjTranspose P := by
  simp only [conjugate, Matrix.conjTranspose_conjTranspose, ← mul_assoc, hC.2, one_mul]

theorem clifford_pauli_dressed_pow {n : ℕ} {C P : QuantumMatrix n}
    (hC : hierarchy n 2 C) (hP : actualPauli P) (a : ℕ) :
    ∃ Q : QuantumMatrix n, actualPauli Q ∧ (C * P) ^ a = C ^ a * Q := by
  induction a with
  | zero => exact ⟨1, actualPauli_one n, by simp⟩
  | succ a ih =>
    obtain ⟨Q, hQ, heq⟩ := ih
    refine ⟨conjugate C.conjTranspose Q * P,
      actualPauli_mul ((clifford_conjTranspose hC).2 Q hQ) hP, ?_⟩
    rw [pow_succ, heq, pow_succ]
    calc
      (C ^ a * Q) * (C * P) = C ^ a * (Q * C) * P := by simp only [mul_assoc]
      _ = C ^ a * (C * conjugate C.conjTranspose Q) * P := by rw [unitary_move_matrix hC.1]
      _ = _ := by simp only [mul_assoc]

theorem clifford_pauli_dressed_power_actual {n a : ℕ} {C P : QuantumMatrix n}
    (hC : hierarchy n 2 C) (hP : actualPauli P) (hpow : actualPauli (C ^ a)) :
    actualPauli ((C * P) ^ a) := by
  obtain ⟨Q, hQ, heq⟩ := clifford_pauli_dressed_pow hC hP a
  rw [heq]
  exact actualPauli_mul hpow hQ

theorem clifford_two_pauli_dressed_power_actual {n a : ℕ} {C P Q : QuantumMatrix n}
    (hC : hierarchy n 2 C) (hP : actualPauli P) (hQ : actualPauli Q)
    (hpow : actualPauli (C ^ a)) : actualPauli ((P * C * Q) ^ a) := by
  have heq : P * C * Q = C * (conjugate C.conjTranspose P * Q) := by
    rw [unitary_move_matrix hC.1]
    simp only [mul_assoc]
  rw [heq]
  exact clifford_pauli_dressed_power_actual hC
    (actualPauli_mul ((clifford_conjTranspose hC).2 P hP) hQ) hpow

theorem branchMatrix_clifford_factor {n : ℕ} {B : QuantumMatrix n}
    (hB : unitaryMatrix B) (A : QuantumMatrix n) :
    branchMatrix B A = branchMatrix B B * controlled (B.conjTranspose * A) := by
  simp only [controlled, branchMatrix_mul, mul_one, ← mul_assoc, hB.2, one_mul]

theorem controlled_clifford_upper {n a : ℕ} {C : QuantumMatrix n}
    (hC : hierarchy n 2 C) (hpow : actualPauli (C ^ (2 ^ a))) :
    hierarchy (n + 1) (a + 2) (controlled C) := by
  induction a generalizing C with
  | zero => exact controlled_actualPauli_clifford (by simpa using hpow)
  | succ a ih =>
    apply (controlled_hierarchy_iff C).mpr
    refine ⟨hC.1, ?_⟩
    intro P hP
    constructor
    · have hp : actualPauli (pauliCorrection C P) :=
        actualPauli_mul (hC.2 P hP) (actualPauli_conjTranspose hP)
      exact hierarchy_mono (by omega) (by omega) (controlled_actualPauli_clifford hp)
    · let L : QuantumMatrix n := conjugate P C.conjTranspose
      have hL : hierarchy n 2 L :=
        hierarchy_clifford_conjugate (by omega) (actualPauli_hierarchy (by omega) hP)
          (clifford_conjTranspose hC)
      have hT : hierarchy n 2 (L.conjTranspose * C) :=
        hierarchy_clifford_mul_left (by omega) (clifford_conjTranspose hL) hC
      have ht : L.conjTranspose * C =
          P * (C ^ 2) * conjugate C.conjTranspose P.conjTranspose := by
        simp only [L, conjugate, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, pow_two]
        calc
          P * (C * P.conjTranspose) * C = P * C * P.conjTranspose * C := by
            simp only [mul_assoc]
          _ =
              P * C * (C * C.conjTranspose) * P.conjTranspose * C := by
            rw [hC.1.2, mul_one]
          _ = _ := by simp only [mul_assoc]
      have hc2 : actualPauli ((C ^ 2) ^ (2 ^ a)) := by
        simpa only [← pow_mul, ← Nat.pow_succ'] using hpow
      have htPow : actualPauli ((L.conjTranspose * C) ^ (2 ^ a)) := by
        rw [ht]
        exact clifford_two_pauli_dressed_power_actual (clifford_pow hC 2) hP
          ((clifford_conjTranspose hC).2 _ (actualPauli_conjTranspose hP)) hc2
      have hc := ih hT htPow
      change hierarchy (n + 1) (a + 2) (branchMatrix L C)
      rw [branchMatrix_clifford_factor hL.1]
      exact hierarchy_clifford_mul_left (by omega) (hierarchy_lift (by omega) hL) hc

theorem controlled_clifford_iff_dyadic_power {n a : ℕ} {C : QuantumMatrix n}
    (hC : hierarchy n 2 C) :
    hierarchy (n + 1) (a + 2) (controlled C) ↔ actualPauli (C ^ (2 ^ a)) :=
  ⟨controlled_dyadic_power_pauli, controlled_clifford_upper hC⟩

theorem controlled_clifford_exact {n m : ℕ} {C : QuantumMatrix n}
    (hm : 1 ≤ m) (hC : hierarchy n 2 C) (hp : actualPauliPeriod m C) :
    exactLevel (m + 2) (controlled C) := by
  apply exactLevel_of_previous_not (by omega) (controlled_clifford_upper hC hp.1)
  intro hsmall
  have hh : hierarchy (n + 1) ((m - 1) + 2) (controlled C) := by
    convert hsmall using 1 <;> omega
  have hlo := controlled_period_lower hp hh
  omega

theorem character_comm {n : ℕ} (x z : BitString n) :
    character x z = character z x := congrArg bitSign (dot_comm x z)

theorem orderedPauli_projective_faithful {n : ℕ}
    {x z y w : BitString n} {a : ℂ}
    (h : orderedPauli x z = a • orderedPauli y w) :
    x = y ∧ z = w ∧ a = 1 := by
  classical
  have hx : x = y := by
    by_contra hxy
    have hsum : (0 : BitString n) ≠ x + y := by
      intro hs
      apply hxy
      calc
        x = x + (y + y) := by rw [bitString_add_self, add_zero]
        _ = (x + y) + y := by rw [add_assoc]
        _ = y := by rw [← hs, zero_add]
    have he := congrArg (fun M : QuantumMatrix n => M x 0) h
    have he' : (1 : ℂ) = 0 := by
      simpa only [orderedPauli_apply, Matrix.smul_apply, smul_eq_mul,
        bitString_add_self, if_pos rfl, character_zero_basis,
        if_neg hsum, ite_true, ite_false, mul_zero] using he
    exact one_ne_zero he'
  subst y
  have ha : a = 1 := by
    have he := congrArg (fun M : QuantumMatrix n => M x 0) h
    simpa only [orderedPauli_apply, Matrix.smul_apply, smul_eq_mul,
      bitString_add_self, if_pos rfl, ite_true, character_zero_basis, mul_one] using he.symm
  subst a
  have hz : z = w := by
    apply pauli_characters_separate
    intro v
    have he := congrArg (fun M : QuantumMatrix n => M (v + x) v) h
    have hc : character z v = character w v := by
      simpa only [one_smul, orderedPauli_apply, add_assoc, bitString_add_self,
        add_zero, if_pos rfl, ite_true] using he
    calc
      character v z = character z v := character_comm _ _
      _ = character w v := hc
      _ = character v w := character_comm _ _
  exact ⟨rfl, hz, rfl⟩

theorem orderedPauli_projective_label_eq {n : ℕ}
    {p q : PauliLabel n} {a : ℂ}
    (h : orderedPauli p.1 p.2 = a • orderedPauli q.1 q.2) : p = q := by
  obtain ⟨hx, hz, _⟩ := orderedPauli_projective_faithful h
  exact Prod.ext hx hz

end QuantumProver.ControlledCliffordHierarchy

namespace QuantumProver.ControlledCliffordHierarchy

theorem pauliCorrection_smul_left {n : ℕ} (U P : QuantumMatrix n) {z : ℂ}
    (hz : star z * z = 1) : pauliCorrection (z • U) P = pauliCorrection U P := by
  rw [pauliCorrection, conjugate_smul_left U P hz]
  rfl

theorem pauliCorrection_branch_headX_branch {n : ℕ} (B A M N : QuantumMatrix n) :
    pauliCorrection (branchMatrix B A) (physicalHeadX n * branchMatrix M N) =
      branchMatrix (B * conjugate N A.conjTranspose) (A * conjugate M B.conjTranspose) := by
  have hm : branchMatrix M N * (branchMatrix B A).conjTranspose *
      (branchMatrix M N).conjTranspose =
      branchMatrix (conjugate M B.conjTranspose) (conjugate N A.conjTranspose) := by
    simp only [branchMatrix_conjTranspose, branchMatrix_mul, conjugate]
  simp only [pauliCorrection, conjugate, Matrix.conjTranspose_mul, physicalHeadX_adjoint]
  calc
    branchMatrix B A * (physicalHeadX n * branchMatrix M N) * (branchMatrix B A).conjTranspose *
        ((branchMatrix M N).conjTranspose * physicalHeadX n) =
      branchMatrix B A * conjugate (physicalHeadX n)
        (branchMatrix M N * (branchMatrix B A).conjTranspose *
          (branchMatrix M N).conjTranspose) := by
      simp only [conjugate, physicalHeadX_adjoint, mul_assoc]
    _ = branchMatrix B A * branchMatrix
        (conjugate N A.conjTranspose) (conjugate M B.conjTranspose) := by
      rw [hm, physicalHeadX_conjugate_branch]
    _ = _ := branchMatrix_mul _ _ _ _

theorem pauliCorrection_branch_ordered_zero {n : ℕ} (B A : QuantumMatrix n)
    (b : ZMod 2) (x z : BitString n) :
    pauliCorrection (branchMatrix B A) (orderedPauli (basisCons 0 x) (basisCons b z)) =
      branchMatrix (pauliCorrection B (orderedPauli x z)) (pauliCorrection A (orderedPauli x z)) := by
  rw [orderedPauli_zero_head, pauliCorrection_branchMatrix,
    pauliCorrection_smul_right A (orderedPauli x z) (by simp)]

theorem pauliCorrection_branch_ordered_one {n : ℕ} (B A : QuantumMatrix n)
    (b : ZMod 2) (x z : BitString n) :
    pauliCorrection (branchMatrix B A) (orderedPauli (basisCons 1 x) (basisCons b z)) =
      branchMatrix (B * conjugate (orderedPauli x z) A.conjTranspose)
        (A * conjugate (orderedPauli x z) B.conjTranspose) := by
  rw [orderedPauli_cons_factor_x]
  change pauliCorrection (branchMatrix B A)
      (physicalHeadX n * branchMatrix (orderedPauli x z) (bitSign b • orderedPauli x z)) = _
  rw [pauliCorrection_branch_headX_branch,
    conjugate_smul_left (orderedPauli x z) A.conjTranspose (by simp)]

theorem branchMatrix_phase_factor {n : ℕ} (z : ℂ) (B A : QuantumMatrix n) :
    branchMatrix B (z • A) = controlled (z • (1 : QuantumMatrix n)) * branchMatrix B A := by
  simp only [controlled, branchMatrix_mul, one_mul, smul_mul_assoc]

theorem branchMatrix_phase_correction_zero {n : ℕ} (B A : QuantumMatrix n)
    {z : ℂ} (hz : star z * z = 1) (b : ZMod 2) (x w : BitString n) :
    pauliCorrection (branchMatrix B (z • A)) (orderedPauli (basisCons 0 x) (basisCons b w)) =
      pauliCorrection (branchMatrix B A) (orderedPauli (basisCons 0 x) (basisCons b w)) := by
  rw [pauliCorrection_branch_ordered_zero, pauliCorrection_branch_ordered_zero,
    pauliCorrection_smul_left A (orderedPauli x w) hz]

theorem branchMatrix_phase_correction_one {n : ℕ} (B A : QuantumMatrix n)
    {z : ℂ} (hz : star z * z = 1) (b : ZMod 2) (x w : BitString n) :
    pauliCorrection (branchMatrix B (z • A)) (orderedPauli (basisCons 1 x) (basisCons b w)) =
      star z • branchMatrix (B * conjugate (orderedPauli x w) A.conjTranspose)
        ((z ^ 2) • (A * conjugate (orderedPauli x w) B.conjTranspose)) := by
  rw [pauliCorrection_branch_ordered_one, Matrix.conjTranspose_smul,
    conjugate_smul_right, mul_smul_comm, smul_mul_assoc, ← branchMatrix_smul]
  rw [smul_smul]
  have hc : star z * z ^ 2 = z := by rw [pow_two, ← mul_assoc, hz, one_mul]
  rw [hc]

theorem hierarchy_branch_phase {n r a : ℕ} {B A : QuantumMatrix n} {z : ℂ}
    (hr : 2 ≤ r) (hV : hierarchy (n + 1) r (branchMatrix B A))
    (hz : star z * z = 1) (hp : PauliPhase (z ^ (2 ^ a))) :
    hierarchy (n + 1) (max r (a + 2)) (branchMatrix B (z • A)) := by
  induction a generalizing r B A z with
  | zero =>
    have hzP : PauliPhase z := by simpa using hp
    rw [Nat.max_eq_left hr, branchMatrix_phase_factor]
    exact hierarchy_clifford_mul_left hr
      (controlled_actualPauli_clifford (actualPauli_smul hzP (actualPauli_one n))) hV
  | succ a ih =>
    have hs : hierarchy n 2 (z • (1 : QuantumMatrix n)) :=
      hierarchy_smul_unit_scalar (by omega) hz
        (actualPauli_hierarchy (by omega) (actualPauli_one n))
    by_cases hr2 : r = 2
    · subst r
      have hc : hierarchy (n + 1) (a + 3) (controlled (z • (1 : QuantumMatrix n))) :=
        controlled_clifford_upper hs (by
          rw [smul_pow, one_pow]
          exact actualPauli_smul hp (actualPauli_one n))
      rw [Nat.max_eq_right (by omega), branchMatrix_phase_factor]
      exact hierarchy_clifford_mul_right (by omega) hV hc
    · have hr3 : 3 ≤ r := by omega
      let d : ℕ := max (r - 1) (a + 2)
      have hd : 2 ≤ d := by dsimp [d]; omega
      have heq : max r (a + 3) = (d - 1) + 2 := by dsimp [d]; omega
      have hR : hierarchy (n + 1) ((r - 2) + 2) (branchMatrix B A) := by
        convert hV using 1 <;> omega
      have hcor := ((hierarchy_iff_pauliCorrections _).mp hR).2
      obtain ⟨hB, hA⟩ := branchMatrix_unitary_blocks (hierarchy_unitary (by omega) hV)
      rw [heq, hierarchy_iff_pauliCorrections]
      refine ⟨branchMatrix_unitary hB (unitaryMatrix_smul hz hA), ?_⟩
      intro P hP
      rcases hP with ⟨v, x, w, hv, rfl⟩
      obtain ⟨⟨c, x⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective x
      obtain ⟨⟨b, w⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective w
      change hierarchy (n + 1) ((d - 1) + 1)
        (pauliCorrection (branchMatrix B (z • A))
          (v • orderedPauli (basisCons c x) (basisCons b w)))
      rw [pauliCorrection_smul_right _ _ (pauliPhase_star_mul hv)]
      have hbase : hierarchy (n + 1) (r - 1)
          (pauliCorrection (branchMatrix B A)
            (orderedPauli (basisCons c x) (basisCons b w))) := by
        convert hcor _ (orderedPauli_actual (basisCons c x) (basisCons b w)) using 1 <;> omega
      rcases physical_control_bit_cases c with rfl | rfl
      · rw [branchMatrix_phase_correction_zero B A hz]
        have hh := hierarchy_mono (by omega) (show r - 1 ≤ d by dsimp [d]; omega) hbase
        convert hh using 1 <;> omega
      · rw [branchMatrix_phase_correction_one B A hz]
        rw [pauliCorrection_branch_ordered_one] at hbase
        have hz2 : star (z ^ 2) * z ^ 2 = 1 := by
          rw [star_pow, ← mul_pow, hz, one_pow]
        have hp2 : PauliPhase ((z ^ 2) ^ (2 ^ a)) := by
          simpa only [← pow_mul, ← Nat.pow_succ'] using hp
        have hh := ih (by omega) hbase hz2 hp2
        have hz' : star (star z) * star z = 1 := by
          simpa only [star_star, mul_comm] using hz
        have hphase := hierarchy_smul_unit_scalar hd hz' hh
        convert hphase using 1 <;> omega

theorem controlled_scalar_phase_upper {n r a : ℕ} {U : QuantumMatrix n} {z : ℂ}
    (hr : 2 ≤ r) (hU : hierarchy (n + 1) r (controlled U))
    (hz : star z * z = 1) (hp : PauliPhase (z ^ (2 ^ a))) :
    hierarchy (n + 1) (max r (a + 2)) (controlled (z • U)) :=
  hierarchy_branch_phase hr hU hz hp

end QuantumProver.ControlledCliffordHierarchy

namespace QuantumProver.ControlledCliffordHierarchy

theorem conjugate_branchMatrix {n : ℕ} (B A P Q : QuantumMatrix n) :
    conjugate (branchMatrix B A) (branchMatrix P Q) =
      branchMatrix (conjugate B P) (conjugate A Q) := by
  simp only [conjugate, branchMatrix_conjTranspose, branchMatrix_mul]

theorem conjugate_orderedPauli_zero_branch {n : ℕ}
    (B A : QuantumMatrix n) (b : ZMod 2) (x z : BitString n) :
    conjugate (orderedPauli (basisCons 0 x) (basisCons b z)) (branchMatrix B A) =
      branchMatrix (conjugate (orderedPauli x z) B) (conjugate (orderedPauli x z) A) := by
  rw [orderedPauli_zero_head, conjugate_branchMatrix,
    conjugate_smul_left (orderedPauli x z) A (by simp)]

theorem conjugate_orderedPauli_one_branch {n : ℕ}
    (B A : QuantumMatrix n) (b : ZMod 2) (x z : BitString n) :
    conjugate (orderedPauli (basisCons 1 x) (basisCons b z)) (branchMatrix B A) =
      branchMatrix (conjugate (orderedPauli x z) A) (conjugate (orderedPauli x z) B) := by
  rw [orderedPauli_cons_factor_x, conjugate_comp]
  change conjugate (physicalHeadX n)
    (conjugate (branchMatrix (orderedPauli x z) (bitSign b • orderedPauli x z))
      (branchMatrix B A)) = _
  rw [conjugate_branchMatrix,
    conjugate_smul_left (orderedPauli x z) A (by simp), physicalHeadX_conjugate_branch]

def twoControlMatrix {n : ℕ} (F : ZMod 2 → ZMod 2 → QuantumMatrix n) :
    QuantumMatrix ((n + 1) + 1) :=
  branchMatrix (branchMatrix (F 0 0) (F 0 1)) (branchMatrix (F 1 0) (F 1 1))

theorem twoControlMatrix_mul {n : ℕ} (F G : ZMod 2 → ZMod 2 → QuantumMatrix n) :
    twoControlMatrix F * twoControlMatrix G =
      twoControlMatrix (fun c b => F c b * G c b) := by
  simp only [twoControlMatrix, branchMatrix_mul]

theorem twoControlMatrix_adjoint {n : ℕ} (F : ZMod 2 → ZMod 2 → QuantumMatrix n) :
    (twoControlMatrix F).conjTranspose =
      twoControlMatrix (fun c b => (F c b).conjTranspose) := by
  simp only [twoControlMatrix, branchMatrix_conjTranspose]

theorem twoControlMatrix_unitary {n : ℕ} (F : ZMod 2 → ZMod 2 → QuantumMatrix n)
    (hF : ∀ c b, unitaryMatrix (F c b)) : unitaryMatrix (twoControlMatrix F) :=
  branchMatrix_unitary (branchMatrix_unitary (hF 0 0) (hF 0 1))
    (branchMatrix_unitary (hF 1 0) (hF 1 1))

def twoControlCorrectionProfile {n : ℕ} (F : ZMod 2 → ZMod 2 → QuantumMatrix n)
    (ac ab : ZMod 2) (Q : QuantumMatrix n) : ZMod 2 → ZMod 2 → QuantumMatrix n :=
  fun c b => F c b * Q * (F (c + ac) (b + ab)).conjTranspose * Q.conjTranspose

theorem twoControlMatrix_orderedPauli_correction {n : ℕ}
    (F : ZMod 2 → ZMod 2 → QuantumMatrix n)
    (ac ab zc zb : ZMod 2) (x z : BitString n) :
    pauliCorrection (twoControlMatrix F)
      (orderedPauli (basisCons ac (basisCons ab x)) (basisCons zc (basisCons zb z))) =
      twoControlMatrix (twoControlCorrectionProfile F ac ab (orderedPauli x z)) := by
  rcases physical_control_bit_cases ac with rfl | rfl <;>
    rcases physical_control_bit_cases ab with rfl | rfl
  · simp only [twoControlMatrix]
    rw [pauliCorrection_branch_ordered_zero]
    simp only [pauliCorrection_branch_ordered_zero]
    norm_num [twoControlCorrectionProfile, pauliCorrection, conjugate, mul_assoc] <;>
      simp [show (2 : ZMod 2) = 0 by decide]
  · simp only [twoControlMatrix]
    rw [pauliCorrection_branch_ordered_zero]
    simp only [pauliCorrection_branch_ordered_one]
    norm_num [twoControlCorrectionProfile, pauliCorrection, conjugate, mul_assoc] <;>
      simp [show (2 : ZMod 2) = 0 by decide]
  · simp only [twoControlMatrix]
    rw [pauliCorrection_branch_ordered_one]
    simp only [branchMatrix_conjTranspose, conjugate_orderedPauli_zero_branch, branchMatrix_mul]
    norm_num [twoControlCorrectionProfile, pauliCorrection, conjugate, mul_assoc] <;>
      simp [show (2 : ZMod 2) = 0 by decide]
  · simp only [twoControlMatrix]
    rw [pauliCorrection_branch_ordered_one]
    simp only [branchMatrix_conjTranspose, conjugate_orderedPauli_one_branch, branchMatrix_mul]
    norm_num [twoControlCorrectionProfile, pauliCorrection, conjugate, mul_assoc] <;>
      simp [show (2 : ZMod 2) = 0 by decide]

theorem twoControlMatrix_actualPauli_correction {n : ℕ}
    (F : ZMod 2 → ZMod 2 → QuantumMatrix n)
    (ac ab zc zb : ZMod 2) (x z : BitString n) {v : ℂ} (hv : PauliPhase v) :
    pauliCorrection (twoControlMatrix F)
      (v • orderedPauli (basisCons ac (basisCons ab x)) (basisCons zc (basisCons zb z))) =
      twoControlMatrix (twoControlCorrectionProfile F ac ab (orderedPauli x z)) := by
  rw [pauliCorrection_smul_right _ _ (pauliPhase_star_mul hv),
    twoControlMatrix_orderedPauli_correction]

end QuantumProver.ControlledCliffordHierarchy
