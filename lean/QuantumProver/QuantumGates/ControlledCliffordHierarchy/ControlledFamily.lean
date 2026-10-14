import QuantumProver.QuantumGates.ControlledCliffordHierarchy.BinaryMatrixBounds
import QuantumProver.QuantumGates.ControlledCliffordHierarchy.PauliHierarchy

noncomputable section

open scoped BigOperators

namespace QuantumProver.ControlledCliffordHierarchy

def conjugate {n : ℕ} (U P : QuantumMatrix n) : QuantumMatrix n :=
  U * P * U.conjTranspose

def pauliCorrection {n : ℕ} (U P : QuantumMatrix n) : QuantumMatrix n :=
  conjugate U P * P.conjTranspose

def hierarchy (n : ℕ) : ℕ → QuantumMatrix n → Prop
  | 0, _ => False
  | 1, U => actualPauli U
  | k + 2, U => unitaryMatrix U ∧
      ∀ P : QuantumMatrix n, actualPauli P → hierarchy n (k + 1) (conjugate U P)

def exactLevel {n : ℕ} (r : ℕ) (U : QuantumMatrix n) : Prop :=
  1 ≤ r ∧ hierarchy n r U ∧
    ∀ t : ℕ, 1 ≤ t → t < r → ¬ hierarchy n t U

def finiteHierarchy {n : ℕ} (U : QuantumMatrix n) : Prop :=
  ∃ r : ℕ, 1 ≤ r ∧ hierarchy n r U

def actualPauliPeriod {n : ℕ} (m : ℕ) (U : QuantumMatrix n) : Prop :=
  actualPauli (U ^ (2 ^ m)) ∧
    ∀ a : ℕ, a < m → ¬ actualPauli (U ^ (2 ^ a))

@[simp] theorem hierarchy_zero {n : ℕ} (U : QuantumMatrix n) :
    hierarchy n 0 U ↔ False := Iff.rfl

@[simp] theorem hierarchy_one {n : ℕ} (U : QuantumMatrix n) :
    hierarchy n 1 U ↔ actualPauli U := Iff.rfl

theorem hierarchy_succ_succ {n k : ℕ} (U : QuantumMatrix n) :
    hierarchy n (k + 2) U ↔ unitaryMatrix U ∧
      ∀ P : QuantumMatrix n, actualPauli P → hierarchy n (k + 1) (conjugate U P) :=
  Iff.rfl

theorem exactLevel_finiteHierarchy {n r : ℕ} {U : QuantumMatrix n}
    (hU : exactLevel r U) : finiteHierarchy U :=
  ⟨r, hU.1, hU.2.1⟩

def basisHead {n : ℕ} (b : BitString (n + 1)) : ZMod 2 := b 0

def basisTail {n : ℕ} (b : BitString (n + 1)) : BitString n :=
  fun i => b i.succ

def basisCons {n : ℕ} (a : ZMod 2) (b : BitString n) : BitString (n + 1) :=
  Fin.cons a b

@[simp] theorem basisHead_cons {n : ℕ} (a : ZMod 2) (b : BitString n) :
    basisHead (basisCons a b) = a := by
  simp [basisHead, basisCons]

@[simp] theorem basisTail_cons {n : ℕ} (a : ZMod 2) (b : BitString n) :
    basisTail (basisCons a b) = b := by
  funext i
  simp [basisTail, basisCons]

@[simp] theorem basisCons_head_tail {n : ℕ} (b : BitString (n + 1)) :
    basisCons (basisHead b) (basisTail b) = b := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [basisCons, basisHead, basisTail]

def controlBasisEquiv (n : ℕ) : BitString (n + 1) ≃ ZMod 2 × BitString n where
  toFun b := (basisHead b, basisTail b)
  invFun p := basisCons p.1 p.2
  left_inv := basisCons_head_tail
  right_inv p := by simp

def branchMatrix {n : ℕ} (B A : QuantumMatrix n) : QuantumMatrix (n + 1) :=
  fun row col =>
    if basisHead row = basisHead col then
      if basisHead row = 0 then B (basisTail row) (basisTail col)
      else A (basisTail row) (basisTail col)
    else 0

def controlled {n : ℕ} (U : QuantumMatrix n) : QuantumMatrix (n + 1) :=
  branchMatrix 1 U

@[simp] theorem branchMatrix_apply_cons {n : ℕ} (B A : QuantumMatrix n)
    (a b : ZMod 2) (row col : BitString n) :
    branchMatrix B A (basisCons a row) (basisCons b col) =
      if a = b then if a = 0 then B row col else A row col else 0 := by
  simp [branchMatrix]

@[simp] theorem branchMatrix_one_one (n : ℕ) :
    branchMatrix (1 : QuantumMatrix n) 1 = 1 := by
  classical
  ext row col
  by_cases hh : basisHead row = basisHead col
  · by_cases ht : basisTail row = basisTail col
    · have hrc : row = col := (controlBasisEquiv n).injective (Prod.ext hh ht)
      subst col
      simp [branchMatrix]
    · have hrc : row ≠ col := by
        intro hrc
        exact ht (congrArg basisTail hrc)
      simp [branchMatrix, hh, ht, hrc]
  · have hrc : row ≠ col := by
      intro hrc
      exact hh (congrArg basisHead hrc)
    simp [branchMatrix, hh, hrc]

@[simp] theorem controlled_one (n : ℕ) : controlled (1 : QuantumMatrix n) = 1 :=
  branchMatrix_one_one n

theorem branchMatrix_conjTranspose {n : ℕ} (B A : QuantumMatrix n) :
    (branchMatrix B A).conjTranspose = branchMatrix B.conjTranspose A.conjTranspose := by
  classical
  ext row col
  by_cases hh : basisHead row = basisHead col
  · by_cases hz : basisHead row = 0
    · have hz' : basisHead col = 0 := hh.symm.trans hz
      simp only [Matrix.conjTranspose_apply, branchMatrix,
        if_pos hh, if_pos hh.symm, if_pos hz, if_pos hz']
    · have hz' : basisHead col ≠ 0 := by simpa [← hh] using hz
      simp only [Matrix.conjTranspose_apply, branchMatrix,
        if_pos hh, if_pos hh.symm, if_neg hz, if_neg hz']
  · have hh' : basisHead col ≠ basisHead row := Ne.symm hh
    simp only [Matrix.conjTranspose_apply, branchMatrix, if_neg hh, if_neg hh', star_zero]

theorem controlled_conjTranspose {n : ℕ} (U : QuantumMatrix n) :
    (controlled U).conjTranspose = controlled U.conjTranspose := by
  simp only [controlled, branchMatrix_conjTranspose, Matrix.conjTranspose_one]

theorem branchMatrix_mul {n : ℕ} (B A D C : QuantumMatrix n) :
    branchMatrix B A * branchMatrix D C = branchMatrix (B * D) (A * C) := by
  classical
  ext row col
  obtain ⟨⟨a, r⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective row
  obtain ⟨⟨b, t⟩, rfl⟩ := (controlBasisEquiv n).symm.surjective col
  change (branchMatrix B A * branchMatrix D C) (basisCons a r) (basisCons b t) =
    branchMatrix (B * D) (A * C) (basisCons a r) (basisCons b t)
  rw [Matrix.mul_apply,
    ← (controlBasisEquiv n).symm.sum_comp
      (fun k => branchMatrix B A (basisCons a r) k *
        branchMatrix D C k (basisCons b t))]
  change (∑ p : ZMod 2 × BitString n,
      branchMatrix B A (basisCons a r) (basisCons p.1 p.2) *
        branchMatrix D C (basisCons p.1 p.2) (basisCons b t)) = _
  rw [Fintype.sum_prod_type,
    Fintype.sum_eq_single a (by
      intro u hua
      simp [branchMatrix_apply_cons, Ne.symm hua])]
  by_cases hab : a = b
  · subst b
    by_cases ha : a = 0 <;> simp [branchMatrix_apply_cons, ha, Matrix.mul_apply]
  · simp [branchMatrix_apply_cons, hab]

theorem controlled_mul {n : ℕ} (U V : QuantumMatrix n) :
    controlled U * controlled V = controlled (U * V) := by
  simp only [controlled, branchMatrix_mul, one_mul]

theorem branchMatrix_pow {n : ℕ} (B A : QuantumMatrix n) (k : ℕ) :
    (branchMatrix B A) ^ k = branchMatrix (B ^ k) (A ^ k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, branchMatrix_mul, pow_succ, pow_succ]

theorem controlled_pow {n : ℕ} (U : QuantumMatrix n) (k : ℕ) :
    (controlled U) ^ k = controlled (U ^ k) := by
  simp only [controlled, branchMatrix_pow, one_pow]

theorem controlled_scalar_factor {n : ℕ} (a : ℂ) (U : QuantumMatrix n) :
    controlled (a • U) = controlled (a • (1 : QuantumMatrix n)) * controlled U := by
  simp only [controlled, branchMatrix_mul, one_mul, smul_mul_assoc]

theorem branchMatrix_unitary {n : ℕ} {B A : QuantumMatrix n}
    (hB : unitaryMatrix B) (hA : unitaryMatrix A) : unitaryMatrix (branchMatrix B A) := by
  rcases hB with ⟨hB₁, hB₂⟩
  rcases hA with ⟨hA₁, hA₂⟩
  constructor
  · rw [branchMatrix_conjTranspose, branchMatrix_mul, hB₁, hA₁, branchMatrix_one_one]
  · rw [branchMatrix_conjTranspose, branchMatrix_mul, hB₂, hA₂, branchMatrix_one_one]

theorem controlled_unitary {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) : unitaryMatrix (controlled U) :=
  branchMatrix_unitary (unitaryMatrix_one n) hU

abbrev PauliLabel (n : ℕ) := BitString n × BitString n

def implementsPauliLabels {n : ℕ} (U : QuantumMatrix n)
    (F : PauliLabel n → PauliLabel n) : Prop :=
  ∀ x z : BitString n, ∃ a : ℂ, PauliPhase a ∧
    conjugate U (orderedPauli x z) = a • orderedPauli (F (x, z)).1 (F (x, z)).2

def hadamardMatrix {n : ℕ} (wire : Fin n) : QuantumMatrix n :=
  fun row col =>
    if ∀ i : Fin n, i ≠ wire → row i = col i then
      (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * bitSign (row wire * col wire)
    else 0

def cnotBits {n : ℕ} (control target : Fin n) (b : BitString n) : BitString n :=
  fun i => if i = target then b i + b control else b i

def cnotMatrix {n : ℕ} (control target : Fin n) : QuantumMatrix n :=
  if control = target then 1 else
    fun row col => if row = cnotBits control target col then 1 else 0

def czMatrix {n : ℕ} (left right : Fin n) : QuantumMatrix n :=
  Matrix.diagonal (fun b => bitSign (b left * b right))

def hadamardGate (n wire : ℕ) : QuantumMatrix n :=
  if h : wire < n then hadamardMatrix ⟨wire, h⟩ else 1

def cnotGate (n control target : ℕ) : QuantumMatrix n :=
  if hc : control < n then
    if ht : target < n then cnotMatrix ⟨control, hc⟩ ⟨target, ht⟩ else 1
  else 1

def czGate (n left right : ℕ) : QuantumMatrix n :=
  if hl : left < n then
    if hr : right < n then czMatrix ⟨left, hl⟩ ⟨right, hr⟩ else 1
  else 1

def layerC1 (s : ℕ) : QuantumMatrix s :=
  hadamardGate s 0 *
    ((List.range s).map (fun j => cnotGate s (2 * j + 2) (2 * j + 1))).prod

def layerC2 (s : ℕ) : QuantumMatrix s :=
  czGate s 0 1 *
    ((List.range s).map (fun j => cnotGate s (2 * j + 3) (2 * j + 2))).prod

def regularClifford (s : ℕ) : QuantumMatrix s := layerC2 s * layerC1 s

def tensorMatrix {n m : ℕ} (U : QuantumMatrix n) (V : QuantumMatrix m) :
    QuantumMatrix (n + m) :=
  fun row col =>
    U (fun i => row (Fin.castAdd m i)) (fun i => col (Fin.castAdd m i)) *
    V (fun j => row (Fin.natAdd n j)) (fun j => col (Fin.natAdd n j))

def swapBlocksBits (s : ℕ) (b : BitString (s + s)) : BitString (s + s) :=
  fun i => b (finSumFinEquiv (Sum.swap (finSumFinEquiv.symm i)))

def swapBlocksMatrix (s : ℕ) : QuantumMatrix (s + s) :=
  fun row col => if row = swapBlocksBits s col then 1 else 0

def selectorB (s : ℕ) : QuantumMatrix (s + s) :=
  tensorMatrix (layerC1 s) (1 : QuantumMatrix s) * swapBlocksMatrix s

def selectorD (s : ℕ) : QuantumMatrix (s + s) :=
  tensorMatrix (layerC2 s) (layerC1 s)

def selectorA (s : ℕ) : QuantumMatrix (s + s) := selectorB s * selectorD s

def selectorTarget (s : ℕ) : QuantumMatrix ((s + s) + 1) :=
  branchMatrix (selectorB s) (selectorA s)

def blockSize (h : ℕ) : ℕ := if h ≤ 1 then 1 else 2 ^ (h - 2) + 1

def targetSize (h : ℕ) : ℕ := (blockSize h + blockSize h) + 1

@[simp] theorem blockSize_one : blockSize 1 = 1 := by simp [blockSize]

@[simp] theorem targetSize_one : targetSize 1 = 3 := by simp [targetSize]

theorem blockSize_of_two_le {h : ℕ} (hh : 2 ≤ h) :
    blockSize h = 2 ^ (h - 2) + 1 := by
  simp [blockSize, show ¬ h ≤ 1 by omega]

theorem targetSize_of_two_le {h : ℕ} (hh : 2 ≤ h) :
    targetSize h = 2 ^ (h - 1) + 3 := by
  rw [targetSize, blockSize_of_two_le hh]
  have hsub : h - 1 = (h - 2) + 1 := by omega
  rw [hsub, pow_succ]
  omega

theorem blockSize_pos (h : ℕ) : 0 < blockSize h := by
  unfold blockSize
  split_ifs <;> positivity

theorem blockSize_cycle_bounds {h : ℕ} (hh : 1 ≤ h) :
    2 ^ (h - 1) < blockSize h + blockSize h ∧
    blockSize h + blockSize h ≤ 2 ^ h := by
  by_cases h1 : h = 1
  · subst h
    norm_num [blockSize]
  · have hh2 : 2 ≤ h := by omega
    rw [blockSize_of_two_le hh2]
    have hp : 0 < 2 ^ (h - 2) := by positivity
    have hs1 : h - 1 = (h - 2) + 1 := by omega
    have hs2 : h = (h - 2) + 2 := by omega
    have hp1 : 2 ^ (h - 1) = 2 ^ (h - 2) * 2 := by rw [hs1, pow_succ]
    have hp2 : 2 ^ h = 2 ^ (h - 2) * 4 := by
      calc
        2 ^ h = 2 ^ ((h - 2) + 2) := congrArg (fun t : ℕ => 2 ^ t) hs2
        _ = 2 ^ (h - 2) * 4 := by rw [pow_add]; norm_num
    rw [hp1, hp2]
    omega

def scalarPhase (m : ℕ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi : ℂ) / (2 : ℂ) ^ (m + 1))

def compactTarget (h m : ℕ) : QuantumMatrix (targetSize h) :=
  scalarPhase m • selectorTarget (blockSize h)

def compactControlled (h m : ℕ) : QuantumMatrix (targetSize h + 1) :=
  controlled (compactTarget h m)

def compactFamilyStatement : Prop :=
  ∀ h m : ℕ, 1 ≤ h → 2 ≤ m →
    unitaryMatrix (compactTarget h m) ∧
    exactLevel 3 (compactTarget h m) ∧
    actualPauliPeriod m (compactTarget h m) ∧
    exactLevel (max (h + 4) (m + 2)) (compactControlled h m)

theorem pauli_bitSign_injective : Function.Injective bitSign := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · rfl
  · change (1 : ℂ) = -1 at hab
    norm_num at hab
  · change (-1 : ℂ) = 1 at hab
    norm_num at hab
  · rfl

theorem pauli_character_single_unit {n : ℕ} (i : Fin n) (b : BitString n) :
    character (Pi.single i (1 : ZMod 2)) b = bitSign (b i) := by
  classical
  unfold character dot
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Pi.single_apply, hji, Ne.symm hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem pauli_characters_separate {n : ℕ} (row col : BitString n)
    (h : ∀ z : BitString n, character z row = character z col) : row = col := by
  funext i
  apply pauli_bitSign_injective
  simpa only [pauli_character_single_unit] using h (Pi.single i 1)

theorem pauliZ_commutant_offDiagonal {n : ℕ} (U : QuantumMatrix n)
    (hZ : ∀ z : BitString n, U * zMatrix z = zMatrix z * U)
    (row col : BitString n) (hrc : row ≠ col) : U row col = 0 := by
  classical
  have hsep : ∃ z : BitString n, character z row ≠ character z col := by
    by_contra! hn
    exact hrc (pauli_characters_separate row col hn)
  obtain ⟨z, hz⟩ := hsep
  have hentry := congrArg (fun M : QuantumMatrix n => M row col) (hZ z)
  simp only [zMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  have hproduct : (character z col - character z row) * U row col = 0 := by
    linear_combination hentry
  rcases mul_eq_zero.mp hproduct with hsign | hzero
  · exact False.elim (hz (sub_eq_zero.mp hsign).symm)
  · exact hzero

theorem pauliX_commutant_diagonal {n : ℕ} (U : QuantumMatrix n)
    (hX : ∀ x : BitString n, U * xMatrix x = xMatrix x * U)
    (b : BitString n) : U b b = U 0 0 := by
  classical
  have hshiftEntry (x row col : BitString n) :
      xMatrix x row col = if col = row + x then 1 else 0 := by
    simp [xMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, shiftPerm, eq_comm]
  have hcancel (k : BitString n) : (0 : BitString n) = k + b ↔ k = b := by
    constructor
    · intro hk
      have heq := congrArg (fun v : BitString n => v + b) hk.symm
      simpa only [add_assoc, bitString_add_self, add_zero, zero_add] using heq
    · intro hk
      subst k
      exact (bitString_add_self b).symm
  have hentry := congrArg (fun M : QuantumMatrix n => M b 0) (hX b)
  simp only [Matrix.mul_apply, hshiftEntry, hcancel, bitString_add_self] at hentry
  simpa [mul_ite, ite_mul] using hentry

theorem pauli_commutant_scalar {n : ℕ} (U : QuantumMatrix n)
    (hZ : ∀ z : BitString n, U * zMatrix z = zMatrix z * U)
    (hX : ∀ x : BitString n, U * xMatrix x = xMatrix x * U) :
    U = U 0 0 • (1 : QuantumMatrix n) := by
  classical
  ext row col
  by_cases hrc : row = col
  · subst col
    simpa only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one] using
      pauliX_commutant_diagonal U hX row
  · simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, if_neg hrc,
      mul_zero, pauliZ_commutant_offDiagonal U hZ row col hrc]

def controlExponentBit (a : ZMod 2) : ℤ := (a.val : ℤ)

def controlExponentPolynomial (tc tb tq c b : ℤ) : ℤ :=
  tc * c + tb * b + tq * c * b

def controlExponentXor (c a : ℤ) : ℤ := c + a - 2 * c * a

def controlShiftLinearC (tc tq ac ab : ℤ) : ℤ :=
  2 * ac * tc - ab * (1 - 2 * ac) * tq

def controlShiftLinearB (tb tq ac ab : ℤ) : ℤ :=
  2 * ab * tb - ac * (1 - 2 * ab) * tq

def controlShiftQuadratic (tq ac ab : ℤ) : ℤ :=
  2 * (ac + ab - 2 * ac * ab) * tq

theorem controlExponentBit_add (a b : ZMod 2) :
    controlExponentBit (a + b) =
      controlExponentXor (controlExponentBit a) (controlExponentBit b) := by
  fin_cases a <;> fin_cases b
  · change (0 : ℤ) = 0 + 0 - 2 * 0 * 0
    norm_num
  · change (1 : ℤ) = 0 + 1 - 2 * 0 * 1
    norm_num
  · change (1 : ℤ) = 1 + 0 - 2 * 1 * 0
    norm_num
  · change (0 : ℤ) = 1 + 1 - 2 * 1 * 1
    norm_num

theorem controlExponent_normalized_difference (tc tb tq c b ac ab : ℤ) :
    controlExponentPolynomial tc tb tq c b -
      controlExponentPolynomial tc tb tq (controlExponentXor c ac)
        (controlExponentXor b ab) +
      controlExponentPolynomial tc tb tq ac ab =
    controlExponentPolynomial (controlShiftLinearC tc tq ac ab)
      (controlShiftLinearB tb tq ac ab) (controlShiftQuadratic tq ac ab) c b := by
  unfold controlExponentPolynomial controlExponentXor controlShiftLinearC
    controlShiftLinearB controlShiftQuadratic
  ring

theorem controlExponent_normalized_bit_difference (tc tb tq : ℤ)
    (c b ac ab : ZMod 2) :
    controlExponentPolynomial tc tb tq (controlExponentBit c) (controlExponentBit b) -
      controlExponentPolynomial tc tb tq (controlExponentBit (c + ac))
        (controlExponentBit (b + ab)) +
      controlExponentPolynomial tc tb tq (controlExponentBit ac) (controlExponentBit ab) =
    controlExponentPolynomial
      (controlShiftLinearC tc tq (controlExponentBit ac) (controlExponentBit ab))
      (controlShiftLinearB tb tq (controlExponentBit ac) (controlExponentBit ab))
      (controlShiftQuadratic tq (controlExponentBit ac) (controlExponentBit ab))
      (controlExponentBit c) (controlExponentBit b) := by
  rw [controlExponentBit_add, controlExponentBit_add]
  exact controlExponent_normalized_difference _ _ _ _ _ _ _

theorem controlExponent_dyadic_doubling (j : ℕ) (tc tb tq ac ab : ℤ)
    (hc : (2 : ℤ) ^ j ∣ tc) (hb : (2 : ℤ) ^ j ∣ tb)
    (hq : (2 : ℤ) ^ (j + 1) ∣ tq) :
    (2 : ℤ) ^ (j + 1) ∣ controlShiftLinearC tc tq ac ab ∧
    (2 : ℤ) ^ (j + 1) ∣ controlShiftLinearB tb tq ac ab ∧
    (2 : ℤ) ^ (j + 2) ∣ controlShiftQuadratic tq ac ab := by
  obtain ⟨xc, rfl⟩ := hc
  obtain ⟨xb, rfl⟩ := hb
  obtain ⟨xq, rfl⟩ := hq
  refine ⟨⟨ac * xc - ab * (1 - 2 * ac) * xq, ?_⟩,
    ⟨ab * xb - ac * (1 - 2 * ab) * xq, ?_⟩,
    ⟨(ac + ab - 2 * ac * ab) * xq, ?_⟩⟩ <;>
    simp only [controlShiftLinearC, controlShiftLinearB, controlShiftQuadratic, pow_succ] <;>
    ring

abbrev ControlExponentCoefficients := ℤ × ℤ × ℤ

abbrev ControlExponentShift := ZMod 2 × ZMod 2

def controlExponentStep (t : ControlExponentCoefficients)
    (a : ControlExponentShift) : ControlExponentCoefficients :=
  (controlShiftLinearC t.1 t.2.2 (controlExponentBit a.1) (controlExponentBit a.2),
    controlShiftLinearB t.2.1 t.2.2 (controlExponentBit a.1) (controlExponentBit a.2),
    controlShiftQuadratic t.2.2 (controlExponentBit a.1) (controlExponentBit a.2))

def controlExponentDepth (j : ℕ) (t : ControlExponentCoefficients) : Prop :=
  (2 : ℤ) ^ j ∣ t.1 ∧ (2 : ℤ) ^ j ∣ t.2.1 ∧
    (2 : ℤ) ^ (j + 1) ∣ t.2.2

theorem controlExponentStep_depth (j : ℕ) (t : ControlExponentCoefficients)
    (a : ControlExponentShift) (ht : controlExponentDepth j t) :
    controlExponentDepth (j + 1) (controlExponentStep t a) := by
  simpa only [controlExponentDepth, controlExponentStep, Nat.add_assoc] using
    controlExponent_dyadic_doubling j t.1 t.2.1 t.2.2
      (controlExponentBit a.1) (controlExponentBit a.2) ht.1 ht.2.1 ht.2.2

def controlExponentIterate (t : ControlExponentCoefficients) :
    List ControlExponentShift → ControlExponentCoefficients
  | [] => t
  | a :: shifts => controlExponentIterate (controlExponentStep t a) shifts

theorem controlExponentIterate_depth (shifts : List ControlExponentShift)
    (j : ℕ) (t : ControlExponentCoefficients) (ht : controlExponentDepth j t) :
    controlExponentDepth (j + shifts.length) (controlExponentIterate t shifts) := by
  induction shifts generalizing j t with
  | nil => simpa only [controlExponentIterate, List.length_nil, Nat.add_zero] using ht
  | cons a shifts ih =>
    simpa only [controlExponentIterate, List.length_cons, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      ih (j + 1) (controlExponentStep t a) (controlExponentStep_depth j t a ht)

def controlExponentFunction (t : ControlExponentCoefficients)
    (u : ControlExponentShift) : ℤ :=
  controlExponentPolynomial t.1 t.2.1 t.2.2
    (controlExponentBit u.1) (controlExponentBit u.2)

def controlExponentFunctionStep (f : ControlExponentShift → ℤ)
    (a : ControlExponentShift) (u : ControlExponentShift) : ℤ :=
  f u - f (u + a) + f a

theorem controlExponentStep_function (t : ControlExponentCoefficients)
    (a : ControlExponentShift) :
    controlExponentFunctionStep (controlExponentFunction t) a =
      controlExponentFunction (controlExponentStep t a) := by
  funext u
  exact controlExponent_normalized_bit_difference t.1 t.2.1 t.2.2 u.1 u.2 a.1 a.2

def controlExponentFunctionIterate (f : ControlExponentShift → ℤ) :
    List ControlExponentShift → ControlExponentShift → ℤ
  | [] => f
  | a :: shifts =>
      controlExponentFunctionIterate (controlExponentFunctionStep f a) shifts

theorem controlExponentIterate_function (shifts : List ControlExponentShift)
    (t : ControlExponentCoefficients) :
    controlExponentFunctionIterate (controlExponentFunction t) shifts =
      controlExponentFunction (controlExponentIterate t shifts) := by
  induction shifts generalizing t with
  | nil => rfl
  | cons a shifts ih =>
    simpa only [controlExponentFunctionIterate, controlExponentStep_function,
      controlExponentIterate] using ih (controlExponentStep t a)

abbrev MatrixUnitary (n : ℕ) := unitary (QuantumMatrix n)

def matrixUnitaryOf {n : ℕ} (U : QuantumMatrix n) (hU : unitaryMatrix U) :
    MatrixUnitary n :=
  ⟨U, by simpa only [Unitary.mem_iff, Matrix.star_eq_conjTranspose, unitaryMatrix] using hU⟩

@[simp] theorem matrixUnitaryOf_coe {n : ℕ} (U : QuantumMatrix n)
    (hU : unitaryMatrix U) : (matrixUnitaryOf U hU : QuantumMatrix n) = U := rfl

theorem matrixUnitary_unitary {n : ℕ} (U : MatrixUnitary n) :
    unitaryMatrix (U : QuantumMatrix n) := by
  simpa only [Unitary.mem_iff, Matrix.star_eq_conjTranspose, unitaryMatrix] using U.property

theorem matrixUnitary_inv_coe {n : ℕ} (U : MatrixUnitary n) :
    ((U⁻¹ : MatrixUnitary n) : QuantumMatrix n) =
      (U : QuantumMatrix n).conjTranspose := by
  change star (U : QuantumMatrix n) = (U : QuantumMatrix n).conjTranspose
  exact Matrix.star_eq_conjTranspose _

def matrixZpow {n : ℕ} (U : MatrixUnitary n) (k : ℤ) : QuantumMatrix n :=
  (U ^ k : MatrixUnitary n)

@[simp] theorem matrixZpow_nat {n : ℕ} (U : MatrixUnitary n) (k : ℕ) :
    matrixZpow U (k : ℤ) = (U : QuantumMatrix n) ^ k := by
  simp only [matrixZpow, zpow_natCast, SubmonoidClass.coe_pow]

theorem matrixZpow_add {n : ℕ} (U : MatrixUnitary n) (a b : ℤ) :
    matrixZpow U (a + b) = matrixZpow U a * matrixZpow U b := by
  simp only [matrixZpow, zpow_add, Submonoid.coe_mul]

theorem matrixZpow_neg {n : ℕ} (U : MatrixUnitary n) (a : ℤ) :
    matrixZpow U (-a) = (matrixZpow U a).conjTranspose := by
  simp only [matrixZpow, zpow_neg, matrixUnitary_inv_coe]

theorem matrixUnitary_commute_iff {n : ℕ} (U V : MatrixUnitary n) :
    Commute U V ↔ Commute (U : QuantumMatrix n) (V : QuantumMatrix n) := by
  constructor
  · intro h
    exact congrArg (fun T : MatrixUnitary n => (T : QuantumMatrix n)) h.eq
  · intro h
    exact Subtype.ext h.eq

theorem matrixZpow_commute {n : ℕ} {U V : MatrixUnitary n}
    (h : Commute U V) (a b : ℤ) : Commute (matrixZpow U a) (matrixZpow V b) :=
  (matrixUnitary_commute_iff (U ^ a) (V ^ b)).mp (h.zpow_zpow a b)

theorem matrixUnitary_shift_difference {n : ℕ} {T0 T1 : MatrixUnitary n}
    (h : Commute T0 T1) (a b c d : ℤ) :
    (T0 ^ a * T1 ^ b) * (T0 ^ c * T1 ^ d)⁻¹ =
      T0 ^ (a - c) * T1 ^ (b - d) := by
  calc
    (T0 ^ a * T1 ^ b) * (T0 ^ c * T1 ^ d)⁻¹ =
        T0 ^ a * (T1 ^ b * (T1 ^ d)⁻¹) * (T0 ^ c)⁻¹ := by
      rw [mul_inv_rev]
      simp only [mul_assoc]
    _ = T0 ^ a * T1 ^ (b - d) * T0 ^ (-c) := by
      rw [← zpow_sub, zpow_neg]
    _ = T0 ^ a * T0 ^ (-c) * T1 ^ (b - d) := by
      rw [mul_assoc, (h.zpow_zpow (-c) (b - d)).eq.symm, ← mul_assoc]
    _ = T0 ^ (a - c) * T1 ^ (b - d) := by
      rw [← zpow_add, ← Int.sub_eq_add_neg]

def matrixShiftProfile {n : ℕ} (T0 T1 : MatrixUnitary n)
    (t0 t1 : ZMod 2 → ZMod 2 → ℤ) : ZMod 2 → ZMod 2 → QuantumMatrix n :=
  fun c b => matrixZpow T0 (t0 c b) * matrixZpow T1 (t1 c b)

theorem matrixShiftProfile_unitary {n : ℕ} (T0 T1 : MatrixUnitary n)
    (t0 t1 : ZMod 2 → ZMod 2 → ℤ) (c b : ZMod 2) :
    unitaryMatrix (matrixShiftProfile T0 T1 t0 t1 c b) :=
  unitaryMatrix_mul (matrixUnitary_unitary _) (matrixUnitary_unitary _)

theorem matrixShiftProfile_difference {n : ℕ} {T0 T1 : MatrixUnitary n}
    (h : Commute T0 T1) (t0 t1 : ZMod 2 → ZMod 2 → ℤ)
    (ac ab c b : ZMod 2) :
    matrixShiftProfile T0 T1 t0 t1 c b *
      (matrixShiftProfile T0 T1 t0 t1 (c + ac) (b + ab)).conjTranspose =
      matrixZpow T0 (t0 c b - t0 (c + ac) (b + ab)) *
        matrixZpow T1 (t1 c b - t1 (c + ac) (b + ab)) := by
  have hm := congrArg (fun U : MatrixUnitary n => (U : QuantumMatrix n))
    (matrixUnitary_shift_difference h (t0 c b) (t1 c b)
      (t0 (c + ac) (b + ab)) (t1 (c + ac) (b + ab)))
  simpa only [matrixShiftProfile, matrixZpow, matrixUnitary_inv_coe,
    Submonoid.coe_mul] using hm

theorem matrixUnitary_shift_mul {n : ℕ} {T0 T1 : MatrixUnitary n}
    (h : Commute T0 T1) (a b c d : ℤ) :
    (T0 ^ a * T1 ^ b) * (T0 ^ c * T1 ^ d) =
      T0 ^ (a + c) * T1 ^ (b + d) := by
  calc
    (T0 ^ a * T1 ^ b) * (T0 ^ c * T1 ^ d) =
        T0 ^ a * (T1 ^ b * T0 ^ c) * T1 ^ d := by simp only [mul_assoc]
    _ = T0 ^ a * (T0 ^ c * T1 ^ b) * T1 ^ d := by
      rw [(h.zpow_zpow c b).eq.symm]
    _ = (T0 ^ a * T0 ^ c) * (T1 ^ b * T1 ^ d) := by simp only [mul_assoc]
    _ = _ := by rw [← zpow_add, ← zpow_add]

theorem matrixShiftProfile_normalized_difference {n : ℕ} {T0 T1 : MatrixUnitary n}
    (h : Commute T0 T1) (t0 t1 : ZMod 2 → ZMod 2 → ℤ)
    (ac ab c b : ZMod 2) :
    (matrixShiftProfile T0 T1 t0 t1 c b *
      (matrixShiftProfile T0 T1 t0 t1 (c + ac) (b + ab)).conjTranspose) *
      matrixShiftProfile T0 T1 t0 t1 ac ab =
    matrixZpow T0 (t0 c b - t0 (c + ac) (b + ab) + t0 ac ab) *
      matrixZpow T1 (t1 c b - t1 (c + ac) (b + ab) + t1 ac ab) := by
  have hword :
      ((T0 ^ (t0 c b) * T1 ^ (t1 c b)) *
        (T0 ^ (t0 (c+ac) (b+ab)) * T1 ^ (t1 (c+ac) (b+ab)))⁻¹) *
          (T0 ^ (t0 ac ab) * T1 ^ (t1 ac ab)) =
      T0 ^ (t0 c b - t0 (c+ac) (b+ab) + t0 ac ab) *
        T1 ^ (t1 c b - t1 (c+ac) (b+ab) + t1 ac ab) := by
    rw [matrixUnitary_shift_difference h]
    exact matrixUnitary_shift_mul h _ _ _ _
  have hm := congrArg (fun U : MatrixUnitary n => (U : QuantumMatrix n)) hword
  simpa only [matrixShiftProfile, matrixZpow, matrixUnitary_inv_coe,
    Submonoid.coe_mul] using hm

theorem matrixShiftProfile_coefficient_step {n : ℕ} {T0 T1 : MatrixUnitary n}
    (h : Commute T0 T1) (t0 t1 : ControlExponentCoefficients)
    (ac ab c b : ZMod 2) :
    (matrixShiftProfile T0 T1
      (fun c b => controlExponentFunction t0 (c,b))
      (fun c b => controlExponentFunction t1 (c,b)) c b *
      (matrixShiftProfile T0 T1
        (fun c b => controlExponentFunction t0 (c,b))
        (fun c b => controlExponentFunction t1 (c,b)) (c+ac) (b+ab)).conjTranspose) *
      matrixShiftProfile T0 T1
        (fun c b => controlExponentFunction t0 (c,b))
        (fun c b => controlExponentFunction t1 (c,b)) ac ab =
      matrixShiftProfile T0 T1
        (fun c b => controlExponentFunction (controlExponentStep t0 (ac,ab)) (c,b))
        (fun c b => controlExponentFunction (controlExponentStep t1 (ac,ab)) (c,b)) c b := by
  have h0 := congrFun (controlExponentStep_function t0 (ac,ab)) (c,b)
  have h1 := congrFun (controlExponentStep_function t1 (ac,ab)) (c,b)
  change controlExponentFunction t0 (c,b) -
    controlExponentFunction t0 (c+ac,b+ab) + controlExponentFunction t0 (ac,ab) =
    controlExponentFunction (controlExponentStep t0 (ac,ab)) (c,b) at h0
  change controlExponentFunction t1 (c,b) -
    controlExponentFunction t1 (c+ac,b+ab) + controlExponentFunction t1 (ac,ab) =
    controlExponentFunction (controlExponentStep t1 (ac,ab)) (c,b) at h1
  rw [matrixShiftProfile_normalized_difference h]
  simpa only [matrixShiftProfile] using
    congrArg₂ (fun x y : ℤ => matrixZpow T0 x * matrixZpow T1 y) h0 h1

end QuantumProver.ControlledCliffordHierarchy
