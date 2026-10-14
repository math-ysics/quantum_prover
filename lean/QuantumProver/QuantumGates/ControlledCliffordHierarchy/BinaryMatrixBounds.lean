import Mathlib

noncomputable section

open scoped BigOperators Matrix

namespace QuantumProver.ControlledCliffordHierarchy

abbrev BitString (n : ℕ) := Fin n → ZMod 2

abbrev QuantumMatrix (n : ℕ) := Matrix (BitString n) (BitString n) ℂ

def PauliPhase (a : ℂ) : Prop :=
  a = 1 ∨ a = -1 ∨ a = Complex.I ∨ a = -Complex.I

@[simp] theorem pauliPhase_one : PauliPhase 1 := Or.inl rfl

@[simp] theorem pauliPhase_neg_one : PauliPhase (-1) := Or.inr (Or.inl rfl)

@[simp] theorem pauliPhase_I : PauliPhase Complex.I := Or.inr (Or.inr (Or.inl rfl))

@[simp] theorem pauliPhase_neg_I : PauliPhase (-Complex.I) :=
  Or.inr (Or.inr (Or.inr rfl))

theorem pauliPhase_mul {a b : ℂ} (ha : PauliPhase a) (hb : PauliPhase b) :
    PauliPhase (a * b) := by
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
    norm_num [PauliPhase, Complex.I_mul_I]

theorem pauliPhase_star {a : ℂ} (ha : PauliPhase a) : PauliPhase (star a) := by
  rcases ha with rfl | rfl | rfl | rfl <;> norm_num [PauliPhase]

theorem pauliPhase_star_mul {a : ℂ} (ha : PauliPhase a) : star a * a = 1 := by
  rcases ha with rfl | rfl | rfl | rfl <;> norm_num [Complex.I_mul_I]

theorem pauliPhase_mul_star {a : ℂ} (ha : PauliPhase a) : a * star a = 1 := by
  rw [mul_comm]
  exact pauliPhase_star_mul ha

def bitSign (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

@[simp] theorem bitSign_zero : bitSign 0 = 1 := by simp [bitSign]

@[simp] theorem bitSign_one : bitSign 1 = -1 := by norm_num [bitSign]

theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  fin_cases a <;> fin_cases b
  · change (1 : ℂ) = 1 * 1
    norm_num
  · change (-1 : ℂ) = 1 * (-1)
    norm_num
  · change (-1 : ℂ) = (-1) * 1
    norm_num
  · change (1 : ℂ) = (-1) * (-1)
    norm_num

@[simp] theorem bitSign_mul_self (a : ZMod 2) : bitSign a * bitSign a = 1 := by
  by_cases ha : a = 0 <;> simp [bitSign, ha]

@[simp] theorem bitSign_star (a : ZMod 2) : star (bitSign a) = bitSign a := by
  by_cases ha : a = 0 <;> simp [bitSign, ha]

theorem bitSign_phase (a : ZMod 2) : PauliPhase (bitSign a) := by
  by_cases ha : a = 0 <;> simp [bitSign, ha]

def dot {n : ℕ} (z b : BitString n) : ZMod 2 := ∑ i, z i * b i

theorem dot_add_right {n : ℕ} (z b c : BitString n) :
    dot z (b + c) = dot z b + dot z c := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_add_left {n : ℕ} (z w b : BitString n) :
    dot (z + w) b = dot z b + dot w b := by
  simp [dot, add_mul, Finset.sum_add_distrib]

@[simp] theorem dot_zero_right {n : ℕ} (z : BitString n) : dot z 0 = 0 := by
  simp [dot]

@[simp] theorem dot_zero_left {n : ℕ} (b : BitString n) : dot 0 b = 0 := by
  simp [dot]

theorem dot_comm {n : ℕ} (z b : BitString n) : dot z b = dot b z := by
  simp only [dot, mul_comm]

def character {n : ℕ} (z b : BitString n) : ℂ := bitSign (dot z b)

theorem character_add_basis {n : ℕ} (z b c : BitString n) :
    character z (b + c) = character z b * character z c := by
  rw [character, dot_add_right, bitSign_add]
  rfl

theorem character_add_label {n : ℕ} (z w b : BitString n) :
    character (z + w) b = character z b * character w b := by
  rw [character, dot_add_left, bitSign_add]
  rfl

@[simp] theorem character_mul_self {n : ℕ} (z b : BitString n) :
    character z b * character z b = 1 := bitSign_mul_self _

@[simp] theorem character_star {n : ℕ} (z b : BitString n) :
    star (character z b) = character z b := bitSign_star _

theorem character_phase {n : ℕ} (z b : BitString n) :
    PauliPhase (character z b) := bitSign_phase _

@[simp] theorem character_zero_basis {n : ℕ} (z : BitString n) :
    character z 0 = 1 := by simp [character]

@[simp] theorem character_zero_label {n : ℕ} (b : BitString n) :
    character 0 b = 1 := by simp [character]

theorem bitString_add_self {n : ℕ} (x : BitString n) : x + x = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (x i)

def shiftPerm {n : ℕ} (x : BitString n) : Equiv.Perm (BitString n) where
  toFun b := b + x
  invFun b := b + x
  left_inv b := by
    ext i
    exact CharTwo.add_cancel_right (b i) (x i)
  right_inv b := by
    ext i
    exact CharTwo.add_cancel_right (b i) (x i)

def xMatrix {n : ℕ} (x : BitString n) : QuantumMatrix n :=
  (shiftPerm x).permMatrix ℂ

def zMatrix {n : ℕ} (z : BitString n) : QuantumMatrix n :=
  Matrix.diagonal (character z)

def orderedPauli {n : ℕ} (x z : BitString n) : QuantumMatrix n :=
  xMatrix x * zMatrix z

def actualPauli {n : ℕ} (U : QuantumMatrix n) : Prop :=
  ∃ (a : ℂ) (x z : BitString n), PauliPhase a ∧ U = a • orderedPauli x z

def unitaryMatrix {n : ℕ} (U : QuantumMatrix n) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

theorem xMatrix_mulVec {n : ℕ} (x : BitString n) (ψ : BitString n → ℂ) :
    xMatrix x *ᵥ ψ = fun b => ψ (b + x) := by
  rw [xMatrix, Matrix.permMatrix_mulVec]
  rfl

theorem zMatrix_mulVec {n : ℕ} (z : BitString n) (ψ : BitString n → ℂ) :
    zMatrix z *ᵥ ψ = fun b => character z b * ψ b := by
  funext b
  exact Matrix.mulVec_diagonal _ _ _

theorem orderedPauli_mulVec {n : ℕ} (x z : BitString n) (ψ : BitString n → ℂ) :
    orderedPauli x z *ᵥ ψ = fun b => character z (b + x) * ψ (b + x) := by
  rw [orderedPauli, ← Matrix.mulVec_mulVec, xMatrix_mulVec, zMatrix_mulVec]

theorem character_cocycle {n : ℕ} (z w b x y : BitString n) :
    character z (b + x) * character w ((b + x) + y) =
      character z y * character (z + w) (b + (x + y)) := by
  rw [character_add_label, ← add_assoc, character_add_basis z (b + x) y]
  calc
    character z (b + x) * character w (b + x + y) =
        (character z y * character z y) *
          (character z (b + x) * character w (b + x + y)) := by
      rw [character_mul_self, one_mul]
    _ = character z y *
        (character z (b + x) * character z y * character w (b + x + y)) := by
      ring

theorem orderedPauli_mul {n : ℕ} (x z y w : BitString n) :
    orderedPauli x z * orderedPauli y w =
      character z y • orderedPauli (x + y) (z + w) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro ψ
  funext b
  simpa only [← Matrix.mulVec_mulVec, orderedPauli_mulVec, Matrix.smul_mulVec,
    Pi.smul_apply, smul_eq_mul, add_assoc, mul_assoc] using
    congrArg (fun a : ℂ => a * ψ (b + (x + y))) (character_cocycle z w b x y)

@[simp] theorem orderedPauli_zero {n : ℕ} :
    orderedPauli (0 : BitString n) 0 = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro ψ
  funext b
  simp [orderedPauli_mulVec]

theorem orderedPauli_actual {n : ℕ} (x z : BitString n) :
    actualPauli (orderedPauli x z) := by
  exact ⟨1, x, z, pauliPhase_one, by simp⟩

theorem actualPauli_one (n : ℕ) : actualPauli (1 : QuantumMatrix n) := by
  exact ⟨1, 0, 0, pauliPhase_one, by simp⟩

@[simp] theorem shiftPerm_inv {n : ℕ} (x : BitString n) :
    (shiftPerm x)⁻¹ = shiftPerm x := by
  ext b
  rfl

@[simp] theorem xMatrix_zero (n : ℕ) : xMatrix (0 : BitString n) = 1 := by
  have hs : shiftPerm (0 : BitString n) = 1 := by
    apply Equiv.ext
    intro b
    change b + 0 = b
    simp
  simp only [xMatrix, hs, Matrix.permMatrix_one]

@[simp] theorem zMatrix_zero (n : ℕ) : zMatrix (0 : BitString n) = 1 := by
  have hc : character (0 : BitString n) = fun _ => (1 : ℂ) := by
    funext b
    exact character_zero_label b
  simp only [zMatrix, hc, Matrix.diagonal_one]

@[simp] theorem orderedPauli_x {n : ℕ} (x : BitString n) :
    orderedPauli x 0 = xMatrix x := by simp [orderedPauli]

@[simp] theorem orderedPauli_z {n : ℕ} (z : BitString n) :
    orderedPauli 0 z = zMatrix z := by simp [orderedPauli]

@[simp] theorem xMatrix_conjTranspose {n : ℕ} (x : BitString n) :
    (xMatrix x).conjTranspose = xMatrix x := by
  simp only [xMatrix, Matrix.conjTranspose_permMatrix, shiftPerm_inv]

@[simp] theorem zMatrix_conjTranspose {n : ℕ} (z : BitString n) :
    (zMatrix z).conjTranspose = zMatrix z := by
  change (Matrix.diagonal (character z)).conjTranspose = Matrix.diagonal (character z)
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext b
  exact character_star z b

@[simp] theorem xMatrix_mul_self {n : ℕ} (x : BitString n) :
    xMatrix x * xMatrix x = 1 := by
  simpa [bitString_add_self] using orderedPauli_mul x (0 : BitString n) x 0

@[simp] theorem zMatrix_mul_self {n : ℕ} (z : BitString n) :
    zMatrix z * zMatrix z = 1 := by
  simpa [bitString_add_self] using orderedPauli_mul (0 : BitString n) z 0 z

theorem orderedPauli_conjTranspose {n : ℕ} (x z : BitString n) :
    (orderedPauli x z).conjTranspose = character z x • orderedPauli x z := by
  calc
    (orderedPauli x z).conjTranspose = zMatrix z * xMatrix x := by
      simp [orderedPauli, Matrix.conjTranspose_mul]
    _ = orderedPauli 0 z * orderedPauli x 0 := by simp
    _ = character z x • orderedPauli x z := by
      simpa using orderedPauli_mul (0 : BitString n) z x 0

theorem orderedPauli_unitary {n : ℕ} (x z : BitString n) :
    unitaryMatrix (orderedPauli x z) := by
  simp only [unitaryMatrix, orderedPauli, Matrix.conjTranspose_mul,
    xMatrix_conjTranspose, zMatrix_conjTranspose]
  constructor
  · calc
      (zMatrix z * xMatrix x) * (xMatrix x * zMatrix z) =
          zMatrix z * (xMatrix x * xMatrix x) * zMatrix z := by simp only [mul_assoc]
      _ = 1 := by rw [xMatrix_mul_self, mul_one, zMatrix_mul_self]
  · calc
      (xMatrix x * zMatrix z) * (zMatrix z * xMatrix x) =
          xMatrix x * (zMatrix z * zMatrix z) * xMatrix x := by simp only [mul_assoc]
      _ = 1 := by rw [zMatrix_mul_self, mul_one, xMatrix_mul_self]

theorem unitaryMatrix_one (n : ℕ) : unitaryMatrix (1 : QuantumMatrix n) := by
  simp [unitaryMatrix]

theorem unitaryMatrix_mul {n : ℕ} {U V : QuantumMatrix n}
    (hU : unitaryMatrix U) (hV : unitaryMatrix V) : unitaryMatrix (U * V) := by
  rcases hU with ⟨hU₁, hU₂⟩
  rcases hV with ⟨hV₁, hV₂⟩
  simp only [unitaryMatrix, Matrix.conjTranspose_mul]
  constructor
  · calc
      (V.conjTranspose * U.conjTranspose) * (U * V) =
          V.conjTranspose * (U.conjTranspose * U) * V := by simp only [mul_assoc]
      _ = 1 := by rw [hU₁, mul_one, hV₁]
  · calc
      (U * V) * (V.conjTranspose * U.conjTranspose) =
          U * (V * V.conjTranspose) * U.conjTranspose := by simp only [mul_assoc]
      _ = 1 := by rw [hV₂, mul_one, hU₂]

theorem unitaryMatrix_conjTranspose {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) : unitaryMatrix U.conjTranspose := by
  simpa [unitaryMatrix] using And.symm hU

theorem unitaryMatrix_smul {n : ℕ} {a : ℂ} {U : QuantumMatrix n}
    (ha : star a * a = 1) (hU : unitaryMatrix U) : unitaryMatrix (a • U) := by
  rcases hU with ⟨hU₁, hU₂⟩
  have ha' : a * star a = 1 := by simpa only [mul_comm] using ha
  simp only [unitaryMatrix, Matrix.conjTranspose_smul, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  constructor
  · rw [hU₁, ha', one_smul]
  · rw [hU₂, ha, one_smul]

theorem actualPauli_unitary {n : ℕ} {U : QuantumMatrix n}
    (hU : actualPauli U) : unitaryMatrix U := by
  rcases hU with ⟨a, x, z, ha, rfl⟩
  exact unitaryMatrix_smul (pauliPhase_star_mul ha) (orderedPauli_unitary x z)

theorem actualPauli_mul {n : ℕ} {U V : QuantumMatrix n}
    (hU : actualPauli U) (hV : actualPauli V) : actualPauli (U * V) := by
  rcases hU with ⟨a, x, z, ha, rfl⟩
  rcases hV with ⟨b, y, w, hb, rfl⟩
  refine ⟨a * b * character z y, x + y, z + w,
    pauliPhase_mul (pauliPhase_mul ha hb) (character_phase z y), ?_⟩
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, orderedPauli_mul]
  congr 1
  ring

theorem actualPauli_conjTranspose {n : ℕ} {U : QuantumMatrix n}
    (hU : actualPauli U) : actualPauli U.conjTranspose := by
  rcases hU with ⟨a, x, z, ha, rfl⟩
  refine ⟨star a * character z x, x, z,
    pauliPhase_mul (pauliPhase_star ha) (character_phase z x), ?_⟩
  rw [Matrix.conjTranspose_smul, orderedPauli_conjTranspose, smul_smul]

theorem actualPauli_smul {n : ℕ} {a : ℂ} {U : QuantumMatrix n}
    (ha : PauliPhase a) (hU : actualPauli U) : actualPauli (a • U) := by
  rcases hU with ⟨b, x, z, hb, rfl⟩
  exact ⟨a * b, x, z, pauliPhase_mul ha hb, by rw [smul_smul]⟩

theorem actualPauli_pow {n : ℕ} {U : QuantumMatrix n}
    (hU : actualPauli U) (k : ℕ) : actualPauli (U ^ k) := by
  induction k with
  | zero => simpa using actualPauli_one n
  | succ k ih => simpa only [pow_succ] using actualPauli_mul ih hU

theorem unitaryMatrix_pow {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (k : ℕ) : unitaryMatrix (U ^ k) := by
  induction k with
  | zero => simpa using unitaryMatrix_one n
  | succ k ih => simpa only [pow_succ] using unitaryMatrix_mul ih hU

theorem orderedPauli_sq {n : ℕ} (x z : BitString n) :
    orderedPauli x z ^ 2 = character z x • (1 : QuantumMatrix n) := by
  simpa [pow_two, bitString_add_self] using orderedPauli_mul x z x z

end QuantumProver.ControlledCliffordHierarchy
