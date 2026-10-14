import QuantumProver.QuantumGates.ControlledCliffordHierarchy.ControlledFamily

noncomputable section

open scoped BigOperators Matrix

namespace QuantumProver.ControlledCliffordHierarchy

attribute [-simp] Fin.natAdd_eq_addNat

def entrywiseReal {n : ℕ} (U : QuantumMatrix n) : Prop :=
  ∀ row col, star (U row col) = U row col

theorem entrywiseReal_one (n : ℕ) : entrywiseReal (1 : QuantumMatrix n) := by
  intro row col
  by_cases h : row = col <;> simp [Matrix.one_apply, h]

theorem entrywiseReal_mul {n : ℕ} {U V : QuantumMatrix n}
    (hU : entrywiseReal U) (hV : entrywiseReal V) : entrywiseReal (U * V) := by
  intro row col
  simp only [Matrix.mul_apply, star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [hU row i, hV i col] using mul_comm (V i col) (U row i)

theorem cnotBits_involutive {n : ℕ} (control target : Fin n)
    (hct : control ≠ target) : Function.Involutive (cnotBits control target) := by
  intro b
  funext i
  by_cases hit : i = target
  · subst i
    simp [cnotBits, hct, CharTwo.add_cancel_right]
  · simp [cnotBits, hit]

theorem cnotMatrix_eq_involution {n : ℕ} (control target : Fin n)
    (hct : control ≠ target) :
    cnotMatrix control target = PhysicalMatrix.involutionMatrix (cnotBits control target) := by
  ext row col
  by_cases h : row = cnotBits control target col <;>
    simp [cnotMatrix, hct, PhysicalMatrix.involutionMatrix, h]

theorem cnotMatrix_adjoint {n : ℕ} (control target : Fin n) :
    (cnotMatrix control target).conjTranspose = cnotMatrix control target := by
  by_cases hct : control = target
  · simp [cnotMatrix, hct]
  · rw [cnotMatrix_eq_involution control target hct]
    exact PhysicalMatrix.involutionMatrix_adjoint (cnotBits control target)
      (cnotBits_involutive control target hct)

theorem cnotMatrix_square {n : ℕ} (control target : Fin n) :
    cnotMatrix control target * cnotMatrix control target = 1 := by
  by_cases hct : control = target
  · simp [cnotMatrix, hct]
  · rw [cnotMatrix_eq_involution control target hct]
    exact PhysicalMatrix.involutionMatrix_square (cnotBits control target)
      (cnotBits_involutive control target hct)

theorem cnotMatrix_unitary {n : ℕ} (control target : Fin n) :
    unitaryMatrix (cnotMatrix control target) := by
  rw [unitaryMatrix, cnotMatrix_adjoint]
  exact ⟨cnotMatrix_square control target, cnotMatrix_square control target⟩

theorem cnotMatrix_real {n : ℕ} (control target : Fin n) :
    entrywiseReal (cnotMatrix control target) := by
  intro row col
  by_cases hct : control = target
  · simpa [cnotMatrix, hct] using entrywiseReal_one n row col
  · simp [cnotMatrix, hct]

theorem czMatrix_adjoint {n : ℕ} (left right : Fin n) :
    (czMatrix left right).conjTranspose = czMatrix left right := by
  exact PhysicalMatrix.diagonal_adjoint _ (fun _ => bitSign_star _)

theorem czMatrix_square {n : ℕ} (left right : Fin n) :
    czMatrix left right * czMatrix left right = 1 := by
  exact PhysicalMatrix.diagonal_square _ (fun _ => bitSign_mul_self _)

theorem czMatrix_unitary {n : ℕ} (left right : Fin n) :
    unitaryMatrix (czMatrix left right) := by
  rw [unitaryMatrix, czMatrix_adjoint]
  exact ⟨czMatrix_square left right, czMatrix_square left right⟩

theorem czMatrix_real {n : ℕ} (left right : Fin n) :
    entrywiseReal (czMatrix left right) := by
  intro row col
  by_cases h : row = col <;> simp [czMatrix, Matrix.diagonal_apply, h]

theorem hadamardMatrix_real {n : ℕ} (wire : Fin n) :
    entrywiseReal (hadamardMatrix wire) := by
  intro row col
  have hsqrt : star (((Real.sqrt 2 : ℝ) : ℂ)) = ((Real.sqrt 2 : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  unfold hadamardMatrix
  split_ifs with h
  · rw [star_mul, bitSign_star, star_inv₀, hsqrt]
    exact mul_comm _ _
  · exact star_zero _

theorem hadamardMatrix_adjoint {n : ℕ} (wire : Fin n) :
    (hadamardMatrix wire).conjTranspose = hadamardMatrix wire := by
  ext row col
  change star (hadamardMatrix wire col row) = hadamardMatrix wire row col
  rw [hadamardMatrix_real wire col row]
  have heq : (∀ i : Fin n, i ≠ wire → col i = row i) ↔
      (∀ i : Fin n, i ≠ wire → row i = col i) := by
    constructor <;> intro h i hi <;> exact (h i hi).symm
  simp [hadamardMatrix, heq, mul_comm]

theorem physical_dot_single_left {n : ℕ} (i : Fin n) (a : ZMod 2)
    (b : BitString n) : dot (Pi.single i a) b = a * b i := by
  simp [dot, Pi.single_apply, ite_mul]

theorem physical_dot_single_right {n : ℕ} (i : Fin n) (a : ZMod 2)
    (b : BitString n) : dot b (Pi.single i a) = b i * a := by
  rw [dot_comm, physical_dot_single_left, mul_comm]

theorem cnotBits_as_add_single {n : ℕ} (control target : Fin n)
    (b : BitString n) :
    cnotBits control target b = b + Pi.single target (b control) := by
  funext i
  by_cases hit : i = target <;> simp [cnotBits, Pi.single_apply, hit]

theorem cnotBits_add {n : ℕ} (control target : Fin n) (b x : BitString n) :
    cnotBits control target (b + x) =
      cnotBits control target b + cnotBits control target x := by
  funext i
  by_cases hit : i = target <;> simp [cnotBits, hit] <;> ring

theorem cnotBits_dot_dual {n : ℕ} (control target : Fin n)
    (z b : BitString n) :
    dot z (cnotBits control target b) = dot (cnotBits target control z) b := by
  rw [cnotBits_as_add_single, dot_add_right, physical_dot_single_right,
    cnotBits_as_add_single, dot_add_left, physical_dot_single_left]

theorem cnotMatrix_mulVec {n : ℕ} (control target : Fin n)
    (hct : control ≠ target) (ψ : BitString n → ℂ) :
    cnotMatrix control target *ᵥ ψ = fun b => ψ (cnotBits control target b) := by
  rw [cnotMatrix_eq_involution control target hct]
  exact PhysicalMatrix.involutionMatrix_mulVec (cnotBits control target)
    (cnotBits_involutive control target hct) ψ

theorem cnotMatrix_conjugate_orderedPauli {n : ℕ} (control target : Fin n)
    (hct : control ≠ target) (x z : BitString n) :
    conjugate (cnotMatrix control target) (orderedPauli x z) =
      orderedPauli (cnotBits control target x) (cnotBits target control z) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro ψ
  simp only [conjugate, cnotMatrix_adjoint, ← Matrix.mulVec_mulVec,
    cnotMatrix_mulVec control target hct, orderedPauli_mulVec]
  funext b
  have hinv := cnotBits_involutive control target hct
  have hstate : cnotBits control target (cnotBits control target b + x) =
      b + cnotBits control target x := by
    rw [cnotBits_add, hinv b]
  have harg : cnotBits control target b + x =
      cnotBits control target (b + cnotBits control target x) := by
    rw [cnotBits_add, hinv x]
  change character z (cnotBits control target b + x) *
      ψ (cnotBits control target (cnotBits control target b + x)) =
    character (cnotBits target control z) (b + cnotBits control target x) *
      ψ (b + cnotBits control target x)
  rw [hstate, harg]
  rw [character, cnotBits_dot_dual]
  rfl

def cnotLabel {n : ℕ} (control target : Fin n) (p : PauliLabel n) : PauliLabel n :=
  if control = target then p else
    (cnotBits control target p.1, cnotBits target control p.2)

theorem cnotMatrix_implementsPauliLabels {n : ℕ} (control target : Fin n) :
    implementsPauliLabels (cnotMatrix control target) (cnotLabel control target) := by
  intro x z
  refine ⟨1, pauliPhase_one, ?_⟩
  by_cases hct : control = target
  · simp [cnotMatrix, cnotLabel, hct, conjugate]
  · simpa only [cnotLabel, if_neg hct, one_smul] using
      cnotMatrix_conjugate_orderedPauli control target hct x z

def czLabel {n : ℕ} (left right : Fin n) (p : PauliLabel n) : PauliLabel n :=
  (p.1, p.2 + (Pi.single left (p.1 right) + Pi.single right (p.1 left)))

theorem czMatrix_mulVec {n : ℕ} (left right : Fin n) (ψ : BitString n → ℂ) :
    czMatrix left right *ᵥ ψ = fun b => bitSign (b left * b right) * ψ b := by
  funext b
  exact Matrix.mulVec_diagonal _ _ _

theorem czMatrix_conjugate_orderedPauli {n : ℕ} (left right : Fin n)
    (x z : BitString n) :
    conjugate (czMatrix left right) (orderedPauli x z) =
      bitSign (x left * x right) •
        orderedPauli x (z + (Pi.single left (x right) + Pi.single right (x left))) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro ψ
  simp only [conjugate, czMatrix_adjoint, ← Matrix.mulVec_mulVec,
    czMatrix_mulVec, orderedPauli_mulVec, Matrix.smul_mulVec,
    Pi.smul_apply, smul_eq_mul]
  funext b
  let δ : BitString n := Pi.single left (x right) + Pi.single right (x left)
  have hsign : bitSign (b left * b right) *
      bitSign ((b + x) left * (b + x) right) =
      bitSign (x left * x right) * character δ (b + x) := by
    rw [← bitSign_add]
    change bitSign (b left * b right + (b + x) left * (b + x) right) =
      bitSign (x left * x right) * bitSign (dot δ (b + x))
    rw [← bitSign_add]
    congr 1
    dsimp only [δ]
    rw [dot_add_left, physical_dot_single_left, physical_dot_single_left]
    simp only [Pi.add_apply]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, zero_add,
      show (3 : ZMod 2) = 1 by decide, mul_one]
  change bitSign (b left * b right) *
      (character z (b + x) * (bitSign ((b + x) left * (b + x) right) * ψ (b + x))) =
    bitSign (x left * x right) * (character (z + δ) (b + x) * ψ (b + x))
  calc
    _ = (bitSign (b left * b right) *
        bitSign ((b + x) left * (b + x) right)) * character z (b + x) * ψ (b + x) := by
      ring
    _ = (bitSign (x left * x right) * character δ (b + x)) *
        character z (b + x) * ψ (b + x) := by rw [hsign]
    _ = _ := by rw [character_add_label z δ]; ring

theorem czMatrix_implementsPauliLabels {n : ℕ} (left right : Fin n) :
    implementsPauliLabels (czMatrix left right) (czLabel left right) := by
  intro x z
  exact ⟨bitSign (x left * x right), bitSign_phase _,
    czMatrix_conjugate_orderedPauli left right x z⟩

theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem hadamardMatrix_apply_update {n : ℕ} (wire : Fin n)
    (row : BitString n) (a : ZMod 2) :
    hadamardMatrix wire row (Function.update row wire a) =
      (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * bitSign (row wire * a) := by
  have hoff : ∀ i : Fin n, i ≠ wire →
      row i = Function.update row wire a i := by
    intro i hi
    simp [Function.update_of_ne hi]
  unfold hadamardMatrix
  rw [ite_eq_left hoff]
  simp only [Function.update_self]

theorem hadamardMatrix_mulVec {n : ℕ} (wire : Fin n) (ψ : BitString n → ℂ) :
    hadamardMatrix wire *ᵥ ψ = fun row =>
      (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
        (ψ (Function.update row wire 0) +
          bitSign (row wire) * ψ (Function.update row wire 1)) := by
  funext row
  let b0 : BitString n := Function.update row wire 0
  let b1 : BitString n := Function.update row wire 1
  have h01 : b0 ≠ b1 := by
    intro h
    have hwire := congrFun h wire
    have : (0 : ZMod 2) = 1 := by simpa [b0, b1] using hwire
    exact zero_ne_one this
  change (∑ col : BitString n, hadamardMatrix wire row col * ψ col) = _
  have hsum : (∑ col : BitString n, hadamardMatrix wire row col * ψ col) =
      ∑ col ∈ ({b0, b1} : Finset (BitString n)), hadamardMatrix wire row col * ψ col := by
    symm
    apply Finset.sum_subset (by simp)
    intro col hcol hn
    by_cases hoff : ∀ i : Fin n, i ≠ wire → row i = col i
    · have hupdate : col = Function.update row wire (col wire) := by
        funext i
        by_cases hi : i = wire
        · subst i
          simp
        · rw [Function.update_of_ne hi]
          exact (hoff i hi).symm
      rcases zmod_two_eq_zero_or_one (col wire) with hz | ho
      · exact (hn (by rw [hupdate, hz]; simp [b0])).elim
      · exact (hn (by rw [hupdate, ho]; simp [b1])).elim
    · simp [hadamardMatrix, hoff]
  rw [hsum, Finset.sum_pair h01]
  dsimp only [b0, b1]
  rw [hadamardMatrix_apply_update, hadamardMatrix_apply_update]
  simp only [mul_zero, bitSign_zero, mul_one]
  ring

theorem hadamard_normalization :
    (2 : ℂ) * ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 2) = 1 := by
  have hs : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = (2 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [inv_pow, hs]
  norm_num

theorem hadamardMatrix_square {n : ℕ} (wire : Fin n) :
    hadamardMatrix wire * hadamardMatrix wire = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro ψ
  rw [← Matrix.mulVec_mulVec, hadamardMatrix_mulVec, hadamardMatrix_mulVec,
    Matrix.one_mulVec]
  funext row
  simp only [Function.update_self, Function.update_idem, bitSign_zero,
    bitSign_one, one_mul, neg_one_mul]
  rcases zmod_two_eq_zero_or_one (row wire) with hz | ho
  · have hrow : Function.update row wire (0 : ZMod 2) = row :=
      Function.update_eq_self_iff.mpr hz.symm
    rw [hz, bitSign_zero, one_mul, hrow]
    calc
      _ = ((2 : ℂ) * ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 2)) * ψ row := by ring
      _ = ψ row := by rw [hadamard_normalization, one_mul]
  · have hrow : Function.update row wire (1 : ZMod 2) = row :=
      Function.update_eq_self_iff.mpr ho.symm
    rw [ho, bitSign_one, neg_one_mul, hrow]
    calc
      _ = ((2 : ℂ) * ((((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 2)) * ψ row := by ring
      _ = ψ row := by rw [hadamard_normalization, one_mul]

theorem hadamardMatrix_unitary {n : ℕ} (wire : Fin n) :
    unitaryMatrix (hadamardMatrix wire) := by
  rw [unitaryMatrix, hadamardMatrix_adjoint]
  exact ⟨hadamardMatrix_square wire, hadamardMatrix_square wire⟩

theorem physical_update_as_add_single {n : ℕ} (b : BitString n) (wire : Fin n)
    (a : ZMod 2) :
    Function.update b wire a = b + Pi.single wire (a + b wire) := by
  funext i
  by_cases hi : i = wire
  · subst i
    simp only [Function.update_self, Pi.add_apply, Pi.single_eq_same]
    rw [add_comm a, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · simp [Function.update_of_ne hi, Pi.single_apply, hi]

theorem physical_label_split {n : ℕ} (z : BitString n) (wire : Fin n) :
    z = Function.update z wire 0 + Pi.single wire (z wire) := by
  funext i
  by_cases hi : i = wire <;> simp [Function.update_apply, Pi.single_apply, hi]

theorem physical_update_add {n : ℕ} (b x : BitString n) (wire : Fin n)
    (a : ZMod 2) :
    Function.update b wire a + x = Function.update (b + x) wire (a + x wire) := by
  funext i
  by_cases hi : i = wire <;> simp [Function.update_apply, hi]

theorem physical_update_add_update {n : ℕ} (b x : BitString n) (wire : Fin n)
    (a : ZMod 2) :
    Function.update b wire a + Function.update x wire 0 =
      Function.update (b + x) wire a := by
  funext i
  by_cases hi : i = wire <;> simp [Function.update_apply, hi]

theorem physical_character_split {n : ℕ} (z b : BitString n) (wire : Fin n) :
    character z b = character (Function.update z wire 0) b * bitSign (z wire * b wire) := by
  conv_lhs => rw [physical_label_split z wire]
  rw [character_add_label]
  congr 1
  exact congrArg bitSign (physical_dot_single_left wire (z wire) b)

theorem physical_character_offwire_update {n : ℕ} (z b : BitString n)
    (wire : Fin n) (a : ZMod 2) :
    character (Function.update z wire 0) (Function.update b wire a) =
      character (Function.update z wire 0) b := by
  rw [physical_update_as_add_single b wire a, character_add_basis]
  have hone : character (Function.update z wire 0) (Pi.single wire (a + b wire)) = 1 := by
    simp [character, physical_dot_single_right]
  rw [hone, mul_one]

def hadamardLabel {n : ℕ} (wire : Fin n) (p : PauliLabel n) : PauliLabel n :=
  (Function.update p.1 wire (p.2 wire), Function.update p.2 wire (p.1 wire))

theorem hadamardMatrix_orderedPauli_intertwine {n : ℕ} (wire : Fin n)
    (x z : BitString n) :
    hadamardMatrix wire * orderedPauli x z =
      bitSign (x wire * z wire) •
        (orderedPauli (Function.update x wire (z wire))
          (Function.update z wire (x wire)) * hadamardMatrix wire) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro ψ
  simp only [← Matrix.mulVec_mulVec, hadamardMatrix_mulVec, orderedPauli_mulVec,
    Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  funext b
  simp only [Pi.smul_apply, smul_eq_mul]
  have hx (a : ZMod 2) : Function.update b wire a + x =
      Function.update (b + Function.update x wire (z wire)) wire (a + x wire) := by
    funext i
    by_cases hi : i = wire <;> simp [Function.update_apply, hi]
  have hz (a : ZMod 2) :
      character z (Function.update b wire a + x) =
        character (Function.update z wire 0) (b + Function.update x wire (z wire)) *
          bitSign (z wire * (a + x wire)) := by
    rw [hx, physical_character_split z _ wire,
      physical_character_offwire_update, Function.update_self]
  have hzp : character (Function.update z wire (x wire))
      (b + Function.update x wire (z wire)) =
        character (Function.update z wire 0) (b + Function.update x wire (z wire)) *
          bitSign (x wire * (b wire + z wire)) := by
    rw [physical_character_split _ _ wire]
    simp only [Function.update_self, Function.update_idem, Pi.add_apply]
  rw [hz 0, hz 1, hx 0, hx 1, hzp]
  simp only [Pi.add_apply, Function.update_self, zero_add]
  rcases zmod_two_eq_zero_or_one (x wire) with hx0 | hx1 <;>
    rcases zmod_two_eq_zero_or_one (z wire) with hz0 | hz1 <;>
    rcases zmod_two_eq_zero_or_one (b wire) with hb0 | hb1 <;>
    simp_all [bitSign, CharTwo.two_eq_zero, CharTwo.add_self_eq_zero] <;> ring

theorem hadamardMatrix_conjugate_orderedPauli {n : ℕ} (wire : Fin n)
    (x z : BitString n) :
    conjugate (hadamardMatrix wire) (orderedPauli x z) =
      bitSign (x wire * z wire) •
        orderedPauli (Function.update x wire (z wire))
          (Function.update z wire (x wire)) := by
  rw [conjugate, hadamardMatrix_adjoint, hadamardMatrix_orderedPauli_intertwine,
    smul_mul_assoc, mul_assoc, hadamardMatrix_square, mul_one]

theorem hadamardMatrix_implementsPauliLabels {n : ℕ} (wire : Fin n) :
    implementsPauliLabels (hadamardMatrix wire) (hadamardLabel wire) := by
  intro x z
  exact ⟨bitSign (x wire * z wire), bitSign_phase _,
    hadamardMatrix_conjugate_orderedPauli wire x z⟩

def implementsRealPauliLabels {n : ℕ} (U : QuantumMatrix n)
    (F : PauliLabel n → PauliLabel n) : Prop :=
  ∀ x z : BitString n, ∃ a : ZMod 2,
    conjugate U (orderedPauli x z) = bitSign a • orderedPauli (F (x, z)).1 (F (x, z)).2

theorem realPauliLabels_one (n : ℕ) :
    implementsRealPauliLabels (1 : QuantumMatrix n) id := by
  intro x z
  exact ⟨0, by simp [conjugate]⟩

theorem realPauliLabels_mul {n : ℕ} {U V : QuantumMatrix n}
    {F G : PauliLabel n → PauliLabel n}
    (hU : implementsRealPauliLabels U F) (hV : implementsRealPauliLabels V G) :
    implementsRealPauliLabels (U * V) (F ∘ G) := by
  intro x z
  obtain ⟨b, hb⟩ := hV x z
  obtain ⟨a, ha⟩ := hU (G (x,z)).1 (G (x,z)).2
  refine ⟨b + a, ?_⟩
  have hcomp : conjugate (U * V) (orderedPauli x z) =
      conjugate U (conjugate V (orderedPauli x z)) := by
    simp only [conjugate, Matrix.conjTranspose_mul, mul_assoc]
  rw [hcomp, hb]
  simp only [conjugate, mul_smul_comm, smul_mul_assoc]
  change bitSign b • conjugate U (orderedPauli (G (x,z)).1 (G (x,z)).2) = _
  rw [ha, smul_smul, ← bitSign_add]
  rfl

theorem cnotMatrix_realPauliLabels {n : ℕ} (control target : Fin n) :
    implementsRealPauliLabels (cnotMatrix control target) (cnotLabel control target) := by
  intro x z
  refine ⟨0, ?_⟩
  by_cases hct : control = target
  · simp [cnotMatrix, cnotLabel, hct, conjugate]
  · simpa only [cnotLabel, if_neg hct, bitSign_zero, one_smul] using
      cnotMatrix_conjugate_orderedPauli control target hct x z

theorem czMatrix_realPauliLabels {n : ℕ} (left right : Fin n) :
    implementsRealPauliLabels (czMatrix left right) (czLabel left right) := by
  intro x z
  exact ⟨x left * x right, czMatrix_conjugate_orderedPauli left right x z⟩

theorem hadamardMatrix_realPauliLabels {n : ℕ} (wire : Fin n) :
    implementsRealPauliLabels (hadamardMatrix wire) (hadamardLabel wire) := by
  intro x z
  exact ⟨x wire * z wire, hadamardMatrix_conjugate_orderedPauli wire x z⟩

def tensorBasisEquiv (n m : ℕ) : BitString (n + m) ≃ BitString n × BitString m where
  toFun b := (fun i => b (Fin.castAdd m i), fun j => b (Fin.natAdd n j))
  invFun p := Fin.append p.1 p.2
  left_inv b := Fin.append_castAdd_natAdd
  right_inv p := by
    apply Prod.ext <;> funext i <;> simp

theorem tensorMatrix_apply_append {n m : ℕ} (U : QuantumMatrix n) (V : QuantumMatrix m)
    (r c : BitString n) (s t : BitString m) :
    tensorMatrix U V (Fin.append r s) (Fin.append c t) = U r c * V s t := by
  simp [tensorMatrix]

theorem tensorMatrix_one_one (n m : ℕ) :
    tensorMatrix (1 : QuantumMatrix n) (1 : QuantumMatrix m) = 1 := by
  ext row col
  let eqv := tensorBasisEquiv n m
  have heq : row = col ↔ (eqv row).1 = (eqv col).1 ∧ (eqv row).2 = (eqv col).2 := by
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨h1,h2⟩
      exact eqv.injective (Prod.ext h1 h2)
  change (1 : QuantumMatrix n) (eqv row).1 (eqv col).1 *
      (1 : QuantumMatrix m) (eqv row).2 (eqv col).2 = (1 : QuantumMatrix (n+m)) row col
  by_cases h1 : (eqv row).1 = (eqv col).1 <;>
    by_cases h2 : (eqv row).2 = (eqv col).2 <;>
    simp [Matrix.one_apply, h1, h2, heq]

theorem tensorMatrix_conjTranspose {n m : ℕ} (U : QuantumMatrix n) (V : QuantumMatrix m) :
    (tensorMatrix U V).conjTranspose = tensorMatrix U.conjTranspose V.conjTranspose := by
  ext row col
  simp [tensorMatrix, Matrix.conjTranspose_apply, mul_comm]

theorem tensorMatrix_mul {n m : ℕ} (U D : QuantumMatrix n) (V C : QuantumMatrix m) :
    tensorMatrix U V * tensorMatrix D C = tensorMatrix (U * D) (V * C) := by
  ext row col
  rw [Matrix.mul_apply, ← (tensorBasisEquiv n m).symm.sum_comp
    (fun k => tensorMatrix U V row k * tensorMatrix D C k col)]
  change (∑ p : BitString n × BitString m,
    tensorMatrix U V row (Fin.append p.1 p.2) *
      tensorMatrix D C (Fin.append p.1 p.2) col) = _
  simp only [tensorMatrix, Fin.append_left, Fin.append_right]
  rw [Fintype.sum_prod_type, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem tensorMatrix_unitary {n m : ℕ} {U : QuantumMatrix n} {V : QuantumMatrix m}
    (hU : unitaryMatrix U) (hV : unitaryMatrix V) : unitaryMatrix (tensorMatrix U V) := by
  constructor
  · rw [tensorMatrix_conjTranspose, tensorMatrix_mul, hU.1, hV.1, tensorMatrix_one_one]
  · rw [tensorMatrix_conjTranspose, tensorMatrix_mul, hU.2, hV.2, tensorMatrix_one_one]

theorem swapBlocksBits_involutive (s : ℕ) : Function.Involutive (swapBlocksBits s) := by
  intro b
  funext i
  simp [swapBlocksBits]

theorem swapBlocksMatrix_adjoint (s : ℕ) :
    (swapBlocksMatrix s).conjTranspose = swapBlocksMatrix s := by
  exact PhysicalMatrix.involutionMatrix_adjoint _ (swapBlocksBits_involutive s)

theorem swapBlocksMatrix_square (s : ℕ) :
    swapBlocksMatrix s * swapBlocksMatrix s = 1 := by
  exact PhysicalMatrix.involutionMatrix_square _ (swapBlocksBits_involutive s)

theorem swapBlocksMatrix_unitary (s : ℕ) : unitaryMatrix (swapBlocksMatrix s) := by
  exact PhysicalMatrix.involutionMatrix_unitary _ (swapBlocksBits_involutive s)

theorem swapBlocksMatrix_mulVec (s : ℕ) (ψ : BitString (s+s) → ℂ) :
    swapBlocksMatrix s *ᵥ ψ = fun b => ψ (swapBlocksBits s b) := by
  exact PhysicalMatrix.involutionMatrix_mulVec _ (swapBlocksBits_involutive s) ψ

theorem swapBlocksBits_append {s : ℕ} (a b : BitString s) :
    swapBlocksBits s (Fin.append a b) = Fin.append b a := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [swapBlocksBits, finSumFinEquiv]

theorem swapBlocksMatrix_tensor_intertwine {s : ℕ} (U V : QuantumMatrix s) :
    swapBlocksMatrix s * tensorMatrix U V = tensorMatrix V U * swapBlocksMatrix s := by
  ext row col
  have hf := swapBlocksBits_involutive s
  have hsumleft : (swapBlocksMatrix s * tensorMatrix U V) row col =
      tensorMatrix U V (swapBlocksBits s row) col := by
    have h := congrFun (swapBlocksMatrix_mulVec s (fun k => tensorMatrix U V k col)) row
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  have hsumright : (tensorMatrix V U * swapBlocksMatrix s) row col =
      tensorMatrix V U row (swapBlocksBits s col) := by
    simp only [Matrix.mul_apply, swapBlocksMatrix, mul_ite, mul_one, mul_zero]
    simp [hf col]
  rw [hsumleft, hsumright]
  obtain ⟨⟨a,b⟩, rfl⟩ := (tensorBasisEquiv s s).symm.surjective row
  obtain ⟨⟨c,d⟩, rfl⟩ := (tensorBasisEquiv s s).symm.surjective col
  change tensorMatrix U V (swapBlocksBits s (Fin.append a b)) (Fin.append c d) =
    tensorMatrix V U (Fin.append a b) (swapBlocksBits s (Fin.append c d))
  rw [swapBlocksBits_append, swapBlocksBits_append, tensorMatrix_apply_append,
    tensorMatrix_apply_append]
  exact mul_comm _ _

theorem swapBlocksMatrix_tensor_conjugate {s : ℕ} (U V : QuantumMatrix s) :
    conjugate (swapBlocksMatrix s) (tensorMatrix U V) = tensorMatrix V U := by
  rw [conjugate, swapBlocksMatrix_adjoint, swapBlocksMatrix_tensor_intertwine,
    mul_assoc, swapBlocksMatrix_square, mul_one]

theorem hadamardGate_unitary (n wire : ℕ) : unitaryMatrix (hadamardGate n wire) := by
  unfold hadamardGate
  split_ifs with h
  · exact hadamardMatrix_unitary _
  · exact unitaryMatrix_one n

theorem cnotGate_unitary (n control target : ℕ) : unitaryMatrix (cnotGate n control target) := by
  unfold cnotGate
  split_ifs with hc ht
  · exact cnotMatrix_unitary _ _
  · exact unitaryMatrix_one n
  · exact unitaryMatrix_one n

theorem czGate_unitary (n left right : ℕ) : unitaryMatrix (czGate n left right) := by
  unfold czGate
  split_ifs with hl hr
  · exact czMatrix_unitary _ _
  · exact unitaryMatrix_one n
  · exact unitaryMatrix_one n

theorem hadamardGate_real (n wire : ℕ) : entrywiseReal (hadamardGate n wire) := by
  unfold hadamardGate
  split_ifs with h
  · exact hadamardMatrix_real _
  · exact entrywiseReal_one n

theorem cnotGate_real (n control target : ℕ) : entrywiseReal (cnotGate n control target) := by
  unfold cnotGate
  split_ifs with hc ht
  · exact cnotMatrix_real _ _
  · exact entrywiseReal_one n
  · exact entrywiseReal_one n

theorem czGate_real (n left right : ℕ) : entrywiseReal (czGate n left right) := by
  unfold czGate
  split_ifs with hl hr
  · exact czMatrix_real _ _
  · exact entrywiseReal_one n
  · exact entrywiseReal_one n

theorem physical_unitary_list_prod {n : ℕ} (L : List (QuantumMatrix n))
    (hL : ∀ U ∈ L, unitaryMatrix U) : unitaryMatrix L.prod := by
  induction L with
  | nil => exact unitaryMatrix_one n
  | cons U L ih =>
      exact unitaryMatrix_mul (hL U (by simp)) (ih (fun V hV => hL V (by simp [hV])))

theorem physical_real_list_prod {n : ℕ} (L : List (QuantumMatrix n))
    (hL : ∀ U ∈ L, entrywiseReal U) : entrywiseReal L.prod := by
  induction L with
  | nil => exact entrywiseReal_one n
  | cons U L ih =>
      exact entrywiseReal_mul (hL U (by simp)) (ih (fun V hV => hL V (by simp [hV])))

theorem layerC1_unitary (s : ℕ) : unitaryMatrix (layerC1 s) := by
  apply unitaryMatrix_mul (hadamardGate_unitary s 0)
  apply physical_unitary_list_prod
  intro U hU
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hU
  exact cnotGate_unitary s (2*j+2) (2*j+1)

theorem layerC2_unitary (s : ℕ) : unitaryMatrix (layerC2 s) := by
  apply unitaryMatrix_mul (czGate_unitary s 0 1)
  apply physical_unitary_list_prod
  intro U hU
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hU
  exact cnotGate_unitary s (2*j+3) (2*j+2)

theorem regularClifford_unitary (s : ℕ) : unitaryMatrix (regularClifford s) :=
  unitaryMatrix_mul (layerC2_unitary s) (layerC1_unitary s)

theorem layerC1_real (s : ℕ) : entrywiseReal (layerC1 s) := by
  apply entrywiseReal_mul (hadamardGate_real s 0)
  apply physical_real_list_prod
  intro U hU
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hU
  exact cnotGate_real s (2*j+2) (2*j+1)

theorem layerC2_real (s : ℕ) : entrywiseReal (layerC2 s) := by
  apply entrywiseReal_mul (czGate_real s 0 1)
  apply physical_real_list_prod
  intro U hU
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hU
  exact cnotGate_real s (2*j+3) (2*j+2)

theorem regularClifford_real (s : ℕ) : entrywiseReal (regularClifford s) :=
  entrywiseReal_mul (layerC2_real s) (layerC1_real s)

theorem selectorB_unitary (s : ℕ) : unitaryMatrix (selectorB s) :=
  unitaryMatrix_mul (tensorMatrix_unitary (layerC1_unitary s) (unitaryMatrix_one s))
    (swapBlocksMatrix_unitary s)

theorem selectorD_unitary (s : ℕ) : unitaryMatrix (selectorD s) :=
  tensorMatrix_unitary (layerC2_unitary s) (layerC1_unitary s)

theorem selectorA_unitary (s : ℕ) : unitaryMatrix (selectorA s) :=
  unitaryMatrix_mul (selectorB_unitary s) (selectorD_unitary s)

theorem selectorTarget_unitary (s : ℕ) : unitaryMatrix (selectorTarget s) :=
  branchMatrix_unitary (selectorB_unitary s) (selectorA_unitary s)

def hadamardGateLabel (n wire : ℕ) : PauliLabel n → PauliLabel n :=
  if h : wire < n then hadamardLabel ⟨wire,h⟩ else id

def cnotGateLabel (n control target : ℕ) : PauliLabel n → PauliLabel n :=
  if hc : control < n then
    if ht : target < n then cnotLabel ⟨control,hc⟩ ⟨target,ht⟩ else id
  else id

def czGateLabel (n left right : ℕ) : PauliLabel n → PauliLabel n :=
  if hl : left < n then
    if hr : right < n then czLabel ⟨left,hl⟩ ⟨right,hr⟩ else id
  else id

theorem hadamardGate_realPauliLabels (n wire : ℕ) :
    implementsRealPauliLabels (hadamardGate n wire) (hadamardGateLabel n wire) := by
  unfold hadamardGate hadamardGateLabel
  split_ifs with h
  · exact hadamardMatrix_realPauliLabels _
  · exact realPauliLabels_one n

theorem cnotGate_realPauliLabels (n control target : ℕ) :
    implementsRealPauliLabels (cnotGate n control target) (cnotGateLabel n control target) := by
  unfold cnotGate cnotGateLabel
  split_ifs with hc ht
  · exact cnotMatrix_realPauliLabels _ _
  · exact realPauliLabels_one n
  · exact realPauliLabels_one n

theorem czGate_realPauliLabels (n left right : ℕ) :
    implementsRealPauliLabels (czGate n left right) (czGateLabel n left right) := by
  unfold czGate czGateLabel
  split_ifs with hl hr
  · exact czMatrix_realPauliLabels _ _
  · exact realPauliLabels_one n
  · exact realPauliLabels_one n

def physicalLayerLabel {n : ℕ} {ι : Type*} (L : List ι)
    (F : ι → PauliLabel n → PauliLabel n) : PauliLabel n → PauliLabel n :=
  L.foldr (fun i G => F i ∘ G) id

theorem physical_realPauliLabels_list {n : ℕ} {ι : Type*} (L : List ι)
    (U : ι → QuantumMatrix n) (F : ι → PauliLabel n → PauliLabel n)
    (hL : ∀ i ∈ L, implementsRealPauliLabels (U i) (F i)) :
    implementsRealPauliLabels (L.map U).prod (physicalLayerLabel L F) := by
  induction L with
  | nil => exact realPauliLabels_one n
  | cons i L ih =>
      change implementsRealPauliLabels (U i * (L.map U).prod)
        (F i ∘ physicalLayerLabel L F)
      exact realPauliLabels_mul (hL i (by simp))
        (ih (fun j hj => hL j (by simp [hj])))

def layerC1Label (s : ℕ) : PauliLabel s → PauliLabel s :=
  hadamardGateLabel s 0 ∘
    physicalLayerLabel (List.range s) (fun j => cnotGateLabel s (2*j+2) (2*j+1))

def layerC2Label (s : ℕ) : PauliLabel s → PauliLabel s :=
  czGateLabel s 0 1 ∘
    physicalLayerLabel (List.range s) (fun j => cnotGateLabel s (2*j+3) (2*j+2))

def regularCliffordLabel (s : ℕ) : PauliLabel s → PauliLabel s :=
  layerC2Label s ∘ layerC1Label s

theorem layerC1_realPauliLabels (s : ℕ) :
    implementsRealPauliLabels (layerC1 s) (layerC1Label s) := by
  exact realPauliLabels_mul (hadamardGate_realPauliLabels s 0)
    (physical_realPauliLabels_list (List.range s) _ _
      (fun j hj => cnotGate_realPauliLabels s (2*j+2) (2*j+1)))

theorem layerC2_realPauliLabels (s : ℕ) :
    implementsRealPauliLabels (layerC2 s) (layerC2Label s) := by
  exact realPauliLabels_mul (czGate_realPauliLabels s 0 1)
    (physical_realPauliLabels_list (List.range s) _ _
      (fun j hj => cnotGate_realPauliLabels s (2*j+3) (2*j+2)))

theorem regularClifford_realPauliLabels (s : ℕ) :
    implementsRealPauliLabels (regularClifford s) (regularCliffordLabel s) :=
  realPauliLabels_mul (layerC2_realPauliLabels s) (layerC1_realPauliLabels s)

def regularCliffordSign (s : ℕ) (p : PauliLabel s) : ZMod 2 :=
  Classical.choose (regularClifford_realPauliLabels s p.1 p.2)

theorem regularClifford_signed_action (s : ℕ) (x z : BitString s) :
    conjugate (regularClifford s) (orderedPauli x z) =
      bitSign (regularCliffordSign s (x,z)) •
        orderedPauli (regularCliffordLabel s (x,z)).1 (regularCliffordLabel s (x,z)).2 :=
  Classical.choose_spec (regularClifford_realPauliLabels s x z)

@[simp] theorem cnotBits_zero {n : ℕ} (control target : Fin n) :
    cnotBits control target (0 : BitString n) = 0 := by
  funext i
  simp [cnotBits]

theorem cnotMatrix_zero_basis {n : ℕ} (control target : Fin n) :
    cnotMatrix control target *ᵥ Pi.single (0 : BitString n) (1 : ℂ) =
      Pi.single (0 : BitString n) 1 := by
  by_cases hct : control = target
  · simpa [cnotMatrix, hct] using
      Matrix.one_mulVec (Pi.single (0 : BitString n) (1 : ℂ))
  · rw [cnotMatrix_mulVec control target hct]
    funext b
    have hinv := cnotBits_involutive control target hct
    have heq : cnotBits control target b = 0 ↔ b = 0 := by
      constructor
      · intro h
        have := congrArg (cnotBits control target) h
        simpa only [hinv b, cnotBits_zero] using this
      · rintro rfl
        exact cnotBits_zero control target
    simp only [Pi.single_apply, eq_comm, heq]

theorem cnotGate_zero_basis (n control target : ℕ) :
    cnotGate n control target *ᵥ Pi.single (0 : BitString n) (1 : ℂ) =
      Pi.single (0 : BitString n) 1 := by
  unfold cnotGate
  split_ifs with hc ht
  · exact cnotMatrix_zero_basis _ _
  · exact Matrix.one_mulVec _
  · exact Matrix.one_mulVec _

theorem physical_zero_basis_list_prod {n : ℕ} (L : List (QuantumMatrix n))
    (hL : ∀ U ∈ L, U *ᵥ Pi.single (0 : BitString n) (1 : ℂ) = Pi.single 0 1) :
    L.prod *ᵥ Pi.single (0 : BitString n) (1 : ℂ) = Pi.single 0 1 := by
  induction L with
  | nil => exact Matrix.one_mulVec _
  | cons U L ih =>
      rw [List.prod_cons, ← Matrix.mulVec_mulVec,
        ih (fun V hV => hL V (by simp [hV]))]
      exact hL U (by simp)

theorem layerC1_zero_column {s : ℕ} (hs : 0 < s) (row : BitString s) :
    layerC1 s row 0 = hadamardMatrix (⟨0,hs⟩ : Fin s) row 0 := by
  have hprod : (((List.range s).map (fun j => cnotGate s (2*j+2) (2*j+1))).prod) *ᵥ
      Pi.single (0 : BitString s) (1 : ℂ) = Pi.single 0 1 := by
    apply physical_zero_basis_list_prod
    intro U hU
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hU
    exact cnotGate_zero_basis s (2*j+2) (2*j+1)
  have hvec : layerC1 s *ᵥ Pi.single (0 : BitString s) (1 : ℂ) =
      hadamardMatrix (⟨0,hs⟩ : Fin s) *ᵥ Pi.single 0 1 := by
    rw [layerC1, ← Matrix.mulVec_mulVec, hprod]
    simp [hadamardGate, hs]
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hvec row

theorem layerC1_zero_zero {s : ℕ} (hs : 0 < s) :
    layerC1 s 0 0 = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by
  rw [layerC1_zero_column hs]
  simp [hadamardMatrix]

theorem layerC1_single_zero {s : ℕ} (hs : 0 < s) :
    layerC1 s (Pi.single (⟨0,hs⟩ : Fin s) (1 : ZMod 2)) 0 =
      (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by
  rw [layerC1_zero_column hs]
  have hoff : ∀ i : Fin s, i ≠ (⟨0,hs⟩ : Fin s) →
      (Pi.single (⟨0,hs⟩ : Fin s) (1 : ZMod 2) : BitString s) i = (0 : BitString s) i := by
    intro i hi
    simp [Pi.single_apply, hi, Ne.symm hi]
  unfold hadamardMatrix
  rw [ite_eq_left hoff]
  simp

theorem selectorB_square (s : ℕ) :
    selectorB s ^ 2 = tensorMatrix (layerC1 s) (layerC1 s) := by
  let M := tensorMatrix (layerC1 s) (1 : QuantumMatrix s)
  let S := swapBlocksMatrix s
  change (M*S)^2 = _
  rw [pow_two]
  calc
    (M*S)*(M*S) = M*(S*M)*S := by simp only [mul_assoc]
    _ = M*(tensorMatrix (1 : QuantumMatrix s) (layerC1 s)*S)*S := by
      rw [swapBlocksMatrix_tensor_intertwine]
    _ = (M*tensorMatrix (1 : QuantumMatrix s) (layerC1 s))*(S*S) := by
      simp only [mul_assoc]
    _ = tensorMatrix (layerC1 s) (layerC1 s) := by
      rw [swapBlocksMatrix_square, mul_one]
      dsimp only [M]
      rw [tensorMatrix_mul, mul_one, one_mul]

theorem cnotBits_commute {n : ℕ} (c t d u : Fin n)
    (hct : c ≠ t) (hdu : d ≠ u) (hcu : c ≠ u) (hdt : d ≠ t)
    (b : BitString n) :
    cnotBits c t (cnotBits d u b) = cnotBits d u (cnotBits c t b) := by
  funext i
  by_cases htu : t = u
  · subst u
    by_cases hit : i = t <;>
      simp [cnotBits, hit, hct, hdu, hcu, hdt] <;> ring
  · by_cases hit : i = t <;> by_cases hiu : i = u <;>
      simp [cnotBits, hit, hiu, hct, hdu, hcu, hdt, htu, Ne.symm htu] <;> ring

theorem cnotMatrix_commute {n : ℕ} (c t d u : Fin n)
    (hct : c ≠ t) (hdu : d ≠ u) (hcu : c ≠ u) (hdt : d ≠ t) :
    Commute (cnotMatrix c t) (cnotMatrix d u) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro ψ
  simp only [← Matrix.mulVec_mulVec, cnotMatrix_mulVec c t hct,
    cnotMatrix_mulVec d u hdu]
  funext b
  exact congrArg ψ (cnotBits_commute c t d u hct hdu hcu hdt b).symm

theorem cnotBits_update_disjoint {n : ℕ} (c t wire : Fin n)
    (hwc : wire ≠ c) (hwt : wire ≠ t) (b : BitString n) (a : ZMod 2) :
    cnotBits c t (Function.update b wire a) =
      Function.update (cnotBits c t b) wire a := by
  funext i
  by_cases hiw : i = wire <;> by_cases hit : i = t <;>
    simp [cnotBits, Function.update_apply, hiw, hit, hwc, hwt, Ne.symm hwc, Ne.symm hwt]

theorem hadamardMatrix_cnot_commute {n : ℕ} (wire c t : Fin n)
    (hct : c ≠ t) (hwc : wire ≠ c) (hwt : wire ≠ t) :
    Commute (hadamardMatrix wire) (cnotMatrix c t) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro ψ
  simp only [← Matrix.mulVec_mulVec, hadamardMatrix_mulVec, cnotMatrix_mulVec c t hct]
  funext b
  rw [cnotBits_update_disjoint c t wire hwc hwt b 0,
    cnotBits_update_disjoint c t wire hwc hwt b 1]
  simp [cnotBits, hwt]

theorem czMatrix_cnot_commute {n : ℕ} (left right c t : Fin n)
    (hct : c ≠ t) (hlt : left ≠ t) (hrt : right ≠ t) :
    Commute (czMatrix left right) (cnotMatrix c t) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro ψ
  simp only [← Matrix.mulVec_mulVec, czMatrix_mulVec, cnotMatrix_mulVec c t hct]
  funext b
  simp [cnotBits, hlt, hrt]

theorem cnotGate_square (n control target : ℕ) :
    cnotGate n control target * cnotGate n control target = 1 := by
  unfold cnotGate
  split_ifs with hc ht
  · exact cnotMatrix_square _ _
  · simp
  · simp

theorem hadamardGate_square (n wire : ℕ) :
    hadamardGate n wire * hadamardGate n wire = 1 := by
  unfold hadamardGate
  split_ifs with h
  · exact hadamardMatrix_square _
  · simp

theorem czGate_square (n left right : ℕ) :
    czGate n left right * czGate n left right = 1 := by
  unfold czGate
  split_ifs with hl hr
  · exact czMatrix_square _ _
  · simp
  · simp

theorem cnotGate_commute (n c t d u : ℕ)
    (hct : c ≠ t) (hdu : d ≠ u) (hcu : c ≠ u) (hdt : d ≠ t) :
    Commute (cnotGate n c t) (cnotGate n d u) := by
  unfold cnotGate
  split_ifs with hc ht hd hu <;> try simp [Commute]
  apply cnotMatrix_commute <;> intro h <;> apply_fun Fin.val at h <;>
    simp only [Fin.val_mk] at h <;> contradiction

theorem hadamardGate_cnot_commute (n wire c t : ℕ)
    (hct : c ≠ t) (hwc : wire ≠ c) (hwt : wire ≠ t) :
    Commute (hadamardGate n wire) (cnotGate n c t) := by
  unfold hadamardGate cnotGate
  split_ifs with hw hc ht <;> try simp [Commute]
  apply hadamardMatrix_cnot_commute <;> intro h <;> apply_fun Fin.val at h <;>
    simp only [Fin.val_mk] at h <;> contradiction

theorem czGate_cnot_commute (n left right c t : ℕ)
    (hct : c ≠ t) (hlt : left ≠ t) (hrt : right ≠ t) :
    Commute (czGate n left right) (cnotGate n c t) := by
  unfold czGate cnotGate
  split_ifs with hl hr hc ht <;> try simp [Commute]
  apply czMatrix_cnot_commute <;> intro h <;> apply_fun Fin.val at h <;>
    simp only [Fin.val_mk] at h <;> contradiction

theorem physical_involution_list_prod {n : ℕ} (L : List (QuantumMatrix n))
    (hL : ∀ U ∈ L, U*U=1) (hComm : L.Pairwise Commute) : L.prod * L.prod = 1 := by
  induction L with
  | nil => simp
  | cons U L ih =>
      have hpair := List.pairwise_cons.mp hComm
      have hUL := Commute.list_prod_right L U hpair.1
      have htail := ih (fun V hV => hL V (by simp [hV])) hpair.2
      change (U*L.prod)*(U*L.prod)=1
      calc
        _ = U*(L.prod*U)*L.prod := by simp only [mul_assoc]
        _ = U*(U*L.prod)*L.prod := by rw [hUL.eq.symm]
        _ = (U*U)*(L.prod*L.prod) := by simp only [mul_assoc]
        _ = 1 := by rw [hL U (by simp), htail, one_mul]

theorem layerC1_square (s : ℕ) : layerC1 s * layerC1 s = 1 := by
  let L := (List.range s).map (fun j => cnotGate s (2*j+2) (2*j+1))
  let H := hadamardGate s 0
  have hLs : ∀ U ∈ L, U*U=1 := by
    intro U hU
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hU
    exact cnotGate_square _ _ _
  have hLc : L.Pairwise Commute := by
    apply List.pairwise_of_forall_mem_list
    intro U hU V hV
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hU
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hV
    apply cnotGate_commute <;> omega
  have hLP := physical_involution_list_prod L hLs hLc
  have hHP : Commute H L.prod := by
    apply Commute.list_prod_right
    intro U hU
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hU
    apply hadamardGate_cnot_commute <;> omega
  change (H*L.prod)*(H*L.prod)=1
  calc
    _ = H*(L.prod*H)*L.prod := by simp only [mul_assoc]
    _ = H*(H*L.prod)*L.prod := by rw [hHP.eq.symm]
    _ = (H*H)*(L.prod*L.prod) := by simp only [mul_assoc]
    _ = 1 := by rw [hadamardGate_square, hLP, one_mul]

theorem layerC2_square (s : ℕ) : layerC2 s * layerC2 s = 1 := by
  let L := (List.range s).map (fun j => cnotGate s (2*j+3) (2*j+2))
  let C := czGate s 0 1
  have hLs : ∀ U ∈ L, U*U=1 := by
    intro U hU
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hU
    exact cnotGate_square _ _ _
  have hLc : L.Pairwise Commute := by
    apply List.pairwise_of_forall_mem_list
    intro U hU V hV
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hU
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hV
    apply cnotGate_commute <;> omega
  have hLP := physical_involution_list_prod L hLs hLc
  have hCP : Commute C L.prod := by
    apply Commute.list_prod_right
    intro U hU
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hU
    apply czGate_cnot_commute <;> omega
  change (C*L.prod)*(C*L.prod)=1
  calc
    _ = C*(L.prod*C)*L.prod := by simp only [mul_assoc]
    _ = C*(C*L.prod)*L.prod := by rw [hCP.eq.symm]
    _ = (C*C)*(L.prod*L.prod) := by simp only [mul_assoc]
    _ = 1 := by rw [czGate_square, hLP, one_mul]

theorem layerC1_adjoint (s : ℕ) : (layerC1 s).conjTranspose = layerC1 s := by
  calc
    _ = (layerC1 s).conjTranspose * ((layerC1 s)*(layerC1 s)) := by rw [layerC1_square, mul_one]
    _ = ((layerC1 s).conjTranspose * layerC1 s) * layerC1 s := by rw [mul_assoc]
    _ = layerC1 s := by rw [(layerC1_unitary s).1, one_mul]

theorem layerC2_adjoint (s : ℕ) : (layerC2 s).conjTranspose = layerC2 s := by
  calc
    _ = (layerC2 s).conjTranspose * ((layerC2 s)*(layerC2 s)) := by rw [layerC2_square, mul_one]
    _ = ((layerC2 s).conjTranspose * layerC2 s) * layerC2 s := by rw [mul_assoc]
    _ = layerC2 s := by rw [(layerC2_unitary s).1, one_mul]

theorem regularClifford_reverser (s : ℕ) :
    conjugate (layerC1 s) (regularClifford s) = (regularClifford s).conjTranspose := by
  simp only [conjugate, regularClifford, Matrix.conjTranspose_mul,
    layerC1_adjoint, layerC2_adjoint]
  calc
    (layerC1 s * (layerC2 s * layerC1 s))*layerC1 s =
        (layerC1 s * layerC2 s)*(layerC1 s*layerC1 s) := by simp only [mul_assoc]
    _ = layerC1 s * layerC2 s := by rw [layerC1_square, mul_one]

theorem selectorA_eq_swap (s : ℕ) :
    selectorA s = tensorMatrix (1 : QuantumMatrix s) (layerC2 s) * swapBlocksMatrix s := by
  rw [selectorA, selectorB, selectorD]
  calc
    (tensorMatrix (layerC1 s) 1 * swapBlocksMatrix s) *
        tensorMatrix (layerC2 s) (layerC1 s) =
      tensorMatrix (layerC1 s) 1 *
        (swapBlocksMatrix s * tensorMatrix (layerC2 s) (layerC1 s)) := by rw [mul_assoc]
    _ = tensorMatrix (layerC1 s) 1 *
        (tensorMatrix (layerC1 s) (layerC2 s)*swapBlocksMatrix s) := by
      rw [swapBlocksMatrix_tensor_intertwine]
    _ = (tensorMatrix (layerC1 s) 1 * tensorMatrix (layerC1 s) (layerC2 s)) *
        swapBlocksMatrix s := by rw [mul_assoc]
    _ = _ := by rw [tensorMatrix_mul, layerC1_square, one_mul]

theorem selectorA_square (s : ℕ) :
    selectorA s ^ 2 = tensorMatrix (layerC2 s) (layerC2 s) := by
  rw [selectorA_eq_swap, pow_two]
  calc
    (tensorMatrix 1 (layerC2 s)*swapBlocksMatrix s) *
        (tensorMatrix 1 (layerC2 s)*swapBlocksMatrix s) =
      tensorMatrix 1 (layerC2 s) *
        (swapBlocksMatrix s*tensorMatrix 1 (layerC2 s)) * swapBlocksMatrix s := by
      simp only [mul_assoc]
    _ = tensorMatrix 1 (layerC2 s) *
        (tensorMatrix (layerC2 s) 1*swapBlocksMatrix s) * swapBlocksMatrix s := by
      rw [swapBlocksMatrix_tensor_intertwine]
    _ = (tensorMatrix 1 (layerC2 s)*tensorMatrix (layerC2 s) 1) *
        (swapBlocksMatrix s*swapBlocksMatrix s) := by simp only [mul_assoc]
    _ = _ := by rw [swapBlocksMatrix_square, mul_one, tensorMatrix_mul, one_mul, mul_one]

theorem selectorB_fourth_power (s : ℕ) : selectorB s ^ 4 = 1 := by
  have hexp : (4 : ℕ) = 2*2 := rfl
  rw [hexp, pow_mul, selectorB_square, pow_two, tensorMatrix_mul,
    layerC1_square, tensorMatrix_one_one]

theorem selectorA_fourth_power (s : ℕ) : selectorA s ^ 4 = 1 := by
  have hexp : (4 : ℕ) = 2*2 := rfl
  rw [hexp, pow_mul, selectorA_square, pow_two, tensorMatrix_mul,
    layerC2_square, tensorMatrix_one_one]

theorem selectorTarget_fourth_power (s : ℕ) : selectorTarget s ^ 4 = 1 := by
  rw [selectorTarget, branchMatrix_pow, selectorB_fourth_power,
    selectorA_fourth_power, branchMatrix_one_one]

theorem orderedPauli_zero_column {n : ℕ} (x z row : BitString n) :
    orderedPauli x z row 0 = if row = x then 1 else 0 := by
  have hvec := congrFun (orderedPauli_mulVec x z (Pi.single (0 : BitString n) (1 : ℂ))) row
  simp only [Matrix.mulVec_single_one] at hvec
  by_cases hrx : row = x
  · subst row
    simpa [Pi.single_apply, bitString_add_self] using hvec
  · have hsum : row + x ≠ 0 := by
      intro h
      have hx := congrArg (fun b : BitString n => b + x) h
      rw [add_assoc, bitString_add_self, add_zero, zero_add] at hx
      exact hrx hx
    simpa [Pi.single_apply, hrx, Ne.symm hsum] using hvec

theorem selectorTarget_square_zeroHead (s : ℕ) (r c : BitString (s+s)) :
    (selectorTarget s ^ 2) (basisCons 0 r) (basisCons 0 c) =
      tensorMatrix (layerC1 s) (layerC1 s) r c := by
  rw [selectorTarget, branchMatrix_pow, branchMatrix_apply_cons]
  simp only [ite_true, selectorB_square]

theorem selectorTarget_square_not_projectivePauli {s : ℕ} (hs : 0 < s) (a : ℂ) :
    ¬actualPauli (a • (selectorTarget s ^ 2)) := by
  intro hP
  let c : ℂ := (((Real.sqrt 2 : ℝ) : ℂ)⁻¹)
  let r0 : BitString (s+s) := Fin.append (0 : BitString s) (0 : BitString s)
  let r1 : BitString (s+s) := Fin.append (Pi.single (⟨0,hs⟩ : Fin s) 1) (0 : BitString s)
  let t1 : BitString ((s+s)+1) := basisCons 0 r1
  have hr0 : r0 = 0 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [r0]
  have hcons0 : basisCons (0 : ZMod 2) (0 : BitString (s+s)) = 0 := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [basisCons]
  have ht1 : t1 ≠ 0 := by
    intro h
    have hwire := congrFun h ((Fin.castAdd s (⟨0,hs⟩ : Fin s)).succ)
    have : (1 : ZMod 2) = 0 := by
      simpa only [t1, r1, basisCons, Fin.cons_succ, Fin.append_left,
        Pi.single_eq_same, Pi.zero_apply] using hwire
    exact one_ne_zero this
  have hc : c ≠ 0 := by
    intro h
    have hn := hadamard_normalization
    change (2 : ℂ)*c^2=1 at hn
    rw [h] at hn
    norm_num at hn
  have ha : a ≠ 0 := by
    intro h
    subst a
    have hu := actualPauli_unitary hP
    have hz : (0 : QuantumMatrix ((s+s)+1)) = 1 := by simpa using hu.2
    exact zero_ne_one hz
  have he0 : (selectorTarget s ^ 2) 0 0 = c^2 := by
    have h := selectorTarget_square_zeroHead s r0 r0
    rw [hr0,hcons0] at h
    change (selectorTarget s ^ 2) 0 0 = layerC1 s 0 0 * layerC1 s 0 0 at h
    rw [layerC1_zero_zero hs] at h
    simpa only [c, pow_two] using h
  have he1 : (selectorTarget s ^ 2) t1 0 = c^2 := by
    have h := selectorTarget_square_zeroHead s r1 r0
    rw [hr0,hcons0] at h
    change (selectorTarget s ^ 2) t1 0 = _ at h
    change (selectorTarget s ^ 2) t1 0 =
      tensorMatrix (layerC1 s) (layerC1 s) r1 0 at h
    rw [← hr0] at h
    rw [tensorMatrix_apply_append, layerC1_single_zero hs, layerC1_zero_zero hs] at h
    simpa only [c, pow_two] using h
  have hnon0 : (a • selectorTarget s ^ 2) 0 0 ≠ 0 := by
    change a*((selectorTarget s ^ 2) 0 0) ≠ 0
    rw [he0]
    exact mul_ne_zero ha (pow_ne_zero 2 hc)
  have hnon1 : (a • selectorTarget s ^ 2) t1 0 ≠ 0 := by
    change a*((selectorTarget s ^ 2) t1 0) ≠ 0
    rw [he1]
    exact mul_ne_zero ha (pow_ne_zero 2 hc)
  rcases hP with ⟨p,x,z,hp,hmat⟩
  have hx0 : (0 : BitString ((s+s)+1)) = x := by
    by_contra hx
    apply hnon0
    rw [hmat]
    change p*(orderedPauli x z 0 0)=0
    rw [orderedPauli_zero_column, if_neg hx, mul_zero]
  have hx1 : t1 = x := by
    by_contra hx
    apply hnon1
    rw [hmat]
    change p*(orderedPauli x z t1 0)=0
    rw [orderedPauli_zero_column, if_neg hx, mul_zero]
  exact ht1 (hx1.trans hx0.symm)

def cnotBitsLinear {n : ℕ} (control target : Fin n) :
    BitString n →ₗ[ZMod 2] BitString n where
  toFun := cnotBits control target
  map_add' := cnotBits_add control target
  map_smul' a b := by
    funext i
    by_cases hi : i = target <;>
      simp [cnotBits, hi, Pi.smul_apply, smul_eq_mul, mul_add]

def cnotLabelLinear {n : ℕ} (control target : Fin n) :
    PauliLabel n →ₗ[ZMod 2] PauliLabel n :=
  if control = target then LinearMap.id else
    (cnotBitsLinear control target).prodMap (cnotBitsLinear target control)

def hadamardLabelLinear {n : ℕ} (wire : Fin n) :
    PauliLabel n →ₗ[ZMod 2] PauliLabel n where
  toFun := hadamardLabel wire
  map_add' p q := by
    apply Prod.ext <;> funext i <;> by_cases hi : i = wire <;>
      simp [hadamardLabel, Function.update_apply, hi]
  map_smul' a p := by
    apply Prod.ext <;> funext i <;> by_cases hi : i = wire <;>
      simp [hadamardLabel, Function.update_apply, hi,
        Pi.smul_apply, smul_eq_mul]

def czLabelLinear {n : ℕ} (left right : Fin n) :
    PauliLabel n →ₗ[ZMod 2] PauliLabel n where
  toFun := czLabel left right
  map_add' p q := by
    apply Prod.ext
    · rfl
    · funext i
      by_cases hlr : left = right
      · subst right
        by_cases hil : i = left <;> simp [czLabel,Pi.single_apply,hil] <;> ring
      · by_cases hil : i = left <;> by_cases hir : i = right <;>
          simp [czLabel,Pi.single_apply,hil,hir,hlr,Ne.symm hlr] <;> ring
  map_smul' a p := by
    apply Prod.ext
    · rfl
    · funext i
      simp [czLabel, Pi.single_apply, Pi.smul_apply, smul_eq_mul,
        mul_add, mul_ite]

def hadamardGateLinear (n wire : ℕ) : PauliLabel n →ₗ[ZMod 2] PauliLabel n :=
  if h : wire < n then hadamardLabelLinear ⟨wire,h⟩ else LinearMap.id

def cnotGateLinear (n control target : ℕ) :
    PauliLabel n →ₗ[ZMod 2] PauliLabel n :=
  if hc : control < n then
    if ht : target < n then cnotLabelLinear ⟨control,hc⟩ ⟨target,ht⟩
    else LinearMap.id
  else LinearMap.id

def czGateLinear (n left right : ℕ) : PauliLabel n →ₗ[ZMod 2] PauliLabel n :=
  if hl : left < n then
    if hr : right < n then czLabelLinear ⟨left,hl⟩ ⟨right,hr⟩
    else LinearMap.id
  else LinearMap.id

def physicalLayerLinear {n : ℕ} {ι : Type*} (L : List ι)
    (F : ι → PauliLabel n →ₗ[ZMod 2] PauliLabel n) :
    PauliLabel n →ₗ[ZMod 2] PauliLabel n :=
  L.foldr (fun i G => (F i).comp G) LinearMap.id

def layerC1Linear (s : ℕ) : PauliLabel s →ₗ[ZMod 2] PauliLabel s :=
  (hadamardGateLinear s 0).comp
    (physicalLayerLinear (List.range s) (fun j => cnotGateLinear s (2*j+2) (2*j+1)))

def layerC2Linear (s : ℕ) : PauliLabel s →ₗ[ZMod 2] PauliLabel s :=
  (czGateLinear s 0 1).comp
    (physicalLayerLinear (List.range s) (fun j => cnotGateLinear s (2*j+3) (2*j+2)))

def regularCliffordLinear (s : ℕ) : PauliLabel s →ₗ[ZMod 2] PauliLabel s :=
  (layerC2Linear s).comp (layerC1Linear s)

@[simp] theorem cnotLabelLinear_apply {n : ℕ} (control target : Fin n)
    (p : PauliLabel n) :
    cnotLabelLinear control target p = cnotLabel control target p := by
  unfold cnotLabelLinear cnotLabel
  split_ifs <;> rfl

@[simp] theorem hadamardLabelLinear_apply {n : ℕ} (wire : Fin n)
    (p : PauliLabel n) : hadamardLabelLinear wire p = hadamardLabel wire p := rfl

@[simp] theorem czLabelLinear_apply {n : ℕ} (left right : Fin n)
    (p : PauliLabel n) : czLabelLinear left right p = czLabel left right p := rfl

@[simp] theorem hadamardGateLinear_apply (n wire : ℕ) (p : PauliLabel n) :
    hadamardGateLinear n wire p = hadamardGateLabel n wire p := by
  unfold hadamardGateLinear hadamardGateLabel
  split_ifs <;> rfl

@[simp] theorem cnotGateLinear_apply (n control target : ℕ) (p : PauliLabel n) :
    cnotGateLinear n control target p = cnotGateLabel n control target p := by
  unfold cnotGateLinear cnotGateLabel
  split_ifs <;> simp only [cnotLabelLinear_apply,LinearMap.id_apply,id_eq]

@[simp] theorem czGateLinear_apply (n left right : ℕ) (p : PauliLabel n) :
    czGateLinear n left right p = czGateLabel n left right p := by
  unfold czGateLinear czGateLabel
  split_ifs <;> rfl

theorem physicalLayerLinear_apply {n : ℕ} {ι : Type*} (L : List ι)
    (F : ι → PauliLabel n →ₗ[ZMod 2] PauliLabel n) (p : PauliLabel n) :
    physicalLayerLinear L F p =
      physicalLayerLabel L (fun i => fun q => F i q) p := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    change F i (physicalLayerLinear L F p) =
      F i (physicalLayerLabel L (fun j => fun q => F j q) p)
    rw [ih]

@[simp] theorem layerC1Linear_apply (s : ℕ) (p : PauliLabel s) :
    layerC1Linear s p = layerC1Label s p := by
  simp only [layerC1Linear,layerC1Label,LinearMap.comp_apply,
    hadamardGateLinear_apply,physicalLayerLinear_apply,cnotGateLinear_apply,
    Function.comp_apply]

@[simp] theorem layerC2Linear_apply (s : ℕ) (p : PauliLabel s) :
    layerC2Linear s p = layerC2Label s p := by
  simp only [layerC2Linear,layerC2Label,LinearMap.comp_apply,
    czGateLinear_apply,physicalLayerLinear_apply,cnotGateLinear_apply,
    Function.comp_apply]

@[simp] theorem regularCliffordLinear_apply (s : ℕ) (p : PauliLabel s) :
    regularCliffordLinear s p = regularCliffordLabel s p := by
  simp only [regularCliffordLinear,regularCliffordLabel,LinearMap.comp_apply,
    layerC1Linear_apply,layerC2Linear_apply,Function.comp_apply]

theorem regularClifford_signed_linear (s : ℕ) (p : PauliLabel s) :
    conjugate (regularClifford s) (orderedPauli p.1 p.2) =
      bitSign (regularCliffordSign s p) •
        orderedPauli (regularCliffordLinear s p).1 (regularCliffordLinear s p).2 := by
  simpa only [regularCliffordLinear_apply,Prod.mk.eta] using
    regularClifford_signed_action s p.1 p.2

def regularCliffordPowerSign (s : ℕ) : ℕ → PauliLabel s → ZMod 2
  | 0, _ => 0
  | k+1, p => regularCliffordPowerSign s k p +
      regularCliffordSign s ((regularCliffordLinear s ^ k) p)

theorem regularClifford_pow_signed_action (s k : ℕ) (p : PauliLabel s) :
    conjugate (regularClifford s ^ k) (orderedPauli p.1 p.2) =
      bitSign (regularCliffordPowerSign s k p) •
        orderedPauli ((regularCliffordLinear s ^ k) p).1
          ((regularCliffordLinear s ^ k) p).2 := by
  induction k with
  | zero => simp [conjugate,regularCliffordPowerSign]
  | succ k ih =>
    have hcomp : conjugate (regularClifford s ^ (k+1)) (orderedPauli p.1 p.2) =
        conjugate (regularClifford s)
          (conjugate (regularClifford s ^ k) (orderedPauli p.1 p.2)) := by
      rw [pow_succ']
      simp only [conjugate,Matrix.conjTranspose_mul,mul_assoc]
    rw [hcomp,ih]
    simp only [conjugate,mul_smul_comm,smul_mul_assoc]
    change bitSign (regularCliffordPowerSign s k p) •
      conjugate (regularClifford s)
        (orderedPauli ((regularCliffordLinear s ^ k) p).1
          ((regularCliffordLinear s ^ k) p).2) = _
    rw [regularClifford_signed_linear,smul_smul,← bitSign_add]
    rw [pow_succ']
    rfl

theorem regular_triangular_last_mem_range {d : ℕ} (hd : 0 < d)
    (N : Matrix (Fin d) (Fin d) (ZMod 2))
    (htri : ∀ i j : Fin d, i.val ≤ j.val → N i j = 0)
    (hstep : ∀ i j : Fin d, i.val = j.val + 1 → N i j = 1)
    (a : ℕ) (ha : a < d) :
    (Pi.single (⟨d-1,by omega⟩ : Fin d) (1 : ZMod 2)) ∈
      LinearMap.range (Matrix.mulVecLin (N ^ a)) := by
  let last : Fin d := ⟨d-1,by omega⟩
  let chainStart : Fin d := ⟨d-1-a,by omega⟩
  refine ⟨Pi.single chainStart 1, ?_⟩
  funext i
  change ((N ^ a) *ᵥ Pi.single chainStart 1) i =
    (Pi.single last (1 : ZMod 2) : Fin d → ZMod 2) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  by_cases hi : i = last
  · subst i
    rw [Pi.single_eq_same]
    exact RegularChain.pow_entry_one_on_diagonal N htri hstep a last chainStart
      (by dsimp [last,chainStart]; omega)
  · have hval : i.val ≠ last.val := fun h => hi (Fin.ext h)
    have hlt : i.val < chainStart.val + a := by
      have hid := i.isLt
      dsimp [last,chainStart] at *
      omega
    simpa [Pi.single_apply, hi, Ne.symm hi] using
      RegularChain.pow_entry_zero_before_diagonal N htri a i chainStart hlt

theorem regular_triangular_kernel_last {d : ℕ} (hd : 0 < d)
    (N : Matrix (Fin d) (Fin d) (ZMod 2))
    (htri : ∀ i j : Fin d, i.val ≤ j.val → N i j = 0)
    (hstep : ∀ i j : Fin d, i.val = j.val + 1 → N i j = 1)
    (v : Fin d → ZMod 2) (hv : N *ᵥ v = 0) :
    v = v ⟨d-1,by omega⟩ •
      Pi.single (⟨d-1,by omega⟩ : Fin d) (1 : ZMod 2) := by
  let last : Fin d := ⟨d-1,by omega⟩
  have hcoords : ∀ k (hk : k < d-1), v ⟨k,by omega⟩ = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      let row : Fin d := ⟨k+1,by omega⟩
      let col : Fin d := ⟨k,by omega⟩
      have hsum : (N *ᵥ v) row = N row col * v col := by
        change (∑ j : Fin d, N row j * v j) = N row col * v col
        apply Finset.sum_eq_single col
        · intro j hj hjcol
          by_cases hjk : j.val < k
          · have hz : v j = 0 := by
              simpa only using ih j.val hjk (by omega)
            rw [hz,mul_zero]
          · have hjne : j.val ≠ k := fun he => hjcol (Fin.ext he)
            rw [htri row j (by dsimp [row]; omega),zero_mul]
        · intro hc
          exact (hc (Finset.mem_univ col)).elim
      have hzero : N row col * v col = 0 :=
        hsum.symm.trans (congrFun hv row)
      rw [hstep row col (by rfl),one_mul] at hzero
      exact hzero
  funext i
  by_cases hi : i = last
  · subst i
    simp [last,Pi.smul_apply,smul_eq_mul]
  · have hval : i.val ≠ d-1 := by
      intro he
      exact hi (Fin.ext he)
    have hz : v i = 0 := by
      have hid := i.isLt
      simpa only using hcoords i.val (by omega)
    simp [last,Pi.smul_apply,smul_eq_mul,Pi.single_apply,hi,Ne.symm hi,hz]

theorem regular_triangular_ker_le_range_power {d : ℕ} (hd : 0 < d)
    (N : Matrix (Fin d) (Fin d) (ZMod 2))
    (htri : ∀ i j : Fin d, i.val ≤ j.val → N i j = 0)
    (hstep : ∀ i j : Fin d, i.val = j.val + 1 → N i j = 1)
    (a : ℕ) (ha : a < d) :
    LinearMap.ker (Matrix.mulVecLin N) ≤
      LinearMap.range (Matrix.mulVecLin (N ^ a)) := by
  intro v hv
  have hz : N *ᵥ v = 0 := LinearMap.mem_ker.mp hv
  rw [regular_triangular_kernel_last hd N htri hstep v hz]
  exact Submodule.smul_mem _ _
    (regular_triangular_last_mem_range hd N htri hstep a ha)

def regularShiftT0 (s : ℕ) : QuantumMatrix (s+s) :=
  tensorMatrix (regularClifford s) (1 : QuantumMatrix s)

def regularShiftT1 (s : ℕ) : QuantumMatrix (s+s) :=
  tensorMatrix (1 : QuantumMatrix s) (regularClifford s)

theorem regularShiftT0_unitary (s : ℕ) : unitaryMatrix (regularShiftT0 s) :=
  tensorMatrix_unitary (regularClifford_unitary s) (unitaryMatrix_one s)

theorem regularShiftT1_unitary (s : ℕ) : unitaryMatrix (regularShiftT1 s) :=
  tensorMatrix_unitary (unitaryMatrix_one s) (regularClifford_unitary s)

theorem regularShiftT0_T1_commute (s : ℕ) :
    Commute (regularShiftT0 s) (regularShiftT1 s) := by
  change regularShiftT0 s * regularShiftT1 s = regularShiftT1 s * regularShiftT0 s
  simp only [regularShiftT0,regularShiftT1,tensorMatrix_mul,mul_one,one_mul]

theorem physical_conjugate_mul {n : ℕ} (U V P : QuantumMatrix n) :
    conjugate (U*V) P = conjugate U (conjugate V P) := by
  simp only [conjugate,Matrix.conjTranspose_mul,mul_assoc]

theorem physical_conjugate_tensor {n m : ℕ} (U P : QuantumMatrix n)
    (V Q : QuantumMatrix m) :
    conjugate (tensorMatrix U V) (tensorMatrix P Q) =
      tensorMatrix (conjugate U P) (conjugate V Q) := by
  rw [conjugate,tensorMatrix_conjTranspose,tensorMatrix_mul,tensorMatrix_mul]
  rfl

theorem selectorB_mul_shiftT0 (s : ℕ) :
    selectorB s * regularShiftT0 s = regularShiftT1 s * selectorB s := by
  unfold selectorB regularShiftT0 regularShiftT1
  rw [mul_assoc,swapBlocksMatrix_tensor_intertwine,← mul_assoc,tensorMatrix_mul]
  rw [← mul_assoc,tensorMatrix_mul]
  simp only [mul_one,one_mul]

theorem selectorB_conjugate_shiftT0 (s : ℕ) :
    conjugate (selectorB s) (regularShiftT0 s) = regularShiftT1 s := by
  rw [conjugate,selectorB_mul_shiftT0,mul_assoc,(selectorB_unitary s).2,mul_one]

theorem selectorB_conjugate_shiftT1 (s : ℕ) :
    conjugate (selectorB s) (regularShiftT1 s) = (regularShiftT0 s).conjTranspose := by
  have hswap : conjugate (swapBlocksMatrix s)
      (tensorMatrix (1 : QuantumMatrix s) (regularClifford s)) =
        tensorMatrix (regularClifford s) (1 : QuantumMatrix s) := by
    simpa only [conjugate,swapBlocksMatrix_adjoint] using
      swapBlocksMatrix_tensor_conjugate (s:=s) (1 : QuantumMatrix s) (regularClifford s)
  rw [selectorB,regularShiftT1,physical_conjugate_mul,hswap,
    physical_conjugate_tensor,regularClifford_reverser]
  simp [conjugate,regularShiftT0,tensorMatrix_conjTranspose]

theorem selectorD_eq_shiftT0_square (s : ℕ) :
    selectorD s = regularShiftT0 s * selectorB s ^ 2 := by
  rw [selectorB_square,regularShiftT0,tensorMatrix_mul,one_mul,
    regularClifford,mul_assoc,layerC1_square,mul_one]
  rfl

theorem selectorA_eq_shiftT1_cube (s : ℕ) :
    selectorA s = regularShiftT1 s * selectorB s ^ 3 := by
  rw [selectorA,selectorD_eq_shiftT0_square,← mul_assoc,selectorB_mul_shiftT0,
    mul_assoc,← pow_succ']

theorem selectorB_conjugate_D (s : ℕ) :
    conjugate (selectorB s) (selectorD s) =
      tensorMatrix (layerC1 s) (layerC2 s) := by
  have hswap : conjugate (swapBlocksMatrix s)
      (tensorMatrix (layerC2 s) (layerC1 s)) =
        tensorMatrix (layerC1 s) (layerC2 s) := by
    simpa only [conjugate,swapBlocksMatrix_adjoint] using
      swapBlocksMatrix_tensor_conjugate (s:=s) (layerC2 s) (layerC1 s)
  rw [selectorB,selectorD,physical_conjugate_mul,hswap,physical_conjugate_tensor]
  simp only [conjugate,layerC1_adjoint,Matrix.conjTranspose_one,one_mul,mul_one,
    layerC1_square]

theorem selectorD_mul_conjugate_D (s : ℕ) :
    selectorD s * conjugate (selectorB s) (selectorD s) =
      tensorMatrix (regularClifford s) (regularClifford s).conjTranspose := by
  rw [selectorB_conjugate_D,selectorD,tensorMatrix_mul]
  simp only [regularClifford,Matrix.conjTranspose_mul,layerC1_adjoint,layerC2_adjoint]

def tensorPauliLabelLinearEquiv (n m : ℕ) :
    PauliLabel (n+m) ≃ₗ[ZMod 2] PauliLabel n × PauliLabel m where
  toFun p :=
    ((fun i => p.1 (Fin.castAdd m i), fun i => p.2 (Fin.castAdd m i)),
     (fun j => p.1 (Fin.natAdd n j), fun j => p.2 (Fin.natAdd n j)))
  invFun p := (Fin.append p.1.1 p.2.1, Fin.append p.1.2 p.2.2)
  left_inv p := by
    apply Prod.ext <;> exact Fin.append_castAdd_natAdd
  right_inv p := by
    apply Prod.ext
    · apply Prod.ext <;> funext i <;> simp
    · apply Prod.ext <;> funext i <;> simp
  map_add' p q := rfl
  map_smul' a p := rfl

@[simp] theorem tensorPauliLabelLinearEquiv_apply (n m : ℕ)
    (p : PauliLabel (n+m)) :
    tensorPauliLabelLinearEquiv n m p =
      ((fun i => p.1 (Fin.castAdd m i), fun i => p.2 (Fin.castAdd m i)),
       (fun j => p.1 (Fin.natAdd n j), fun j => p.2 (Fin.natAdd n j))) := rfl

@[simp] theorem tensorPauliLabelLinearEquiv_symm_apply (n m : ℕ)
    (p : PauliLabel n × PauliLabel m) :
    (tensorPauliLabelLinearEquiv n m).symm p =
      (Fin.append p.1.1 p.2.1, Fin.append p.1.2 p.2.2) := rfl

@[simp] theorem tensorPauliLabelLinearEquiv_append (n m : ℕ)
    (p : PauliLabel n) (q : PauliLabel m) :
    tensorPauliLabelLinearEquiv n m
        (Fin.append p.1 q.1, Fin.append p.2 q.2) = (p,q) := by
  exact (tensorPauliLabelLinearEquiv n m).apply_symm_apply (p,q)

def regularOrderedCoordinates {s : ℕ} (hs : 0 < s) (p : PauliLabel s) :
    BitString (s+s) := fun i =>
  if hi : i.val < s-1 then p.1 ⟨s-1-i.val,by omega⟩
  else if hi0 : i.val = s-1 then p.2 ⟨0,hs⟩ + p.1 ⟨0,hs⟩
  else if hi1 : i.val = s then p.1 ⟨0,hs⟩
  else p.2 ⟨i.val-s,by have hid := i.isLt; omega⟩

def regularOrderedCoordinatesInv {s : ℕ} (hs : 0 < s) (a : BitString (s+s)) :
    PauliLabel s :=
  (fun j => if hj : j.val = 0 then a ⟨s,by omega⟩
      else a ⟨s-1-j.val,by omega⟩,
   fun j => if hj : j.val = 0 then a ⟨s-1,by omega⟩ + a ⟨s,by omega⟩
      else a ⟨s+j.val,by have hjlt := j.isLt; omega⟩)

theorem regularOrderedCoordinates_left_inv {s : ℕ} (hs : 0 < s)
    (p : PauliLabel s) :
    regularOrderedCoordinatesInv hs (regularOrderedCoordinates hs p) = p := by
  apply Prod.ext
  · funext i
    by_cases hi : i.val = 0
    · have hiz : i = (⟨0,hs⟩ : Fin s) := Fin.ext hi
      subst i
      simp [regularOrderedCoordinatesInv,regularOrderedCoordinates,
        show ¬ s < s-1 by omega,show s ≠ s-1 by omega]
    · have hilow : s-1-i.val < s-1 := by have hil := i.isLt; omega
      have hback : s-1-(s-1-i.val) = i.val := by have hil := i.isLt; omega
      simp only [regularOrderedCoordinatesInv,Prod.fst,dif_neg hi]
      rw [regularOrderedCoordinates,dif_pos hilow]
      have hidx : (⟨s-1-(s-1-i.val),by have hil:=i.isLt; omega⟩ : Fin s) = i := Fin.ext hback
      exact congrArg p.1 hidx
  · funext i
    by_cases hi : i.val = 0
    · have hiz : i = (⟨0,hs⟩ : Fin s) := Fin.ext hi
      subst i
      simp [regularOrderedCoordinatesInv,regularOrderedCoordinates,
        show ¬ s < s-1 by omega,show s ≠ s-1 by omega,
        CharTwo.add_cancel_right]
    · have hlow : ¬ s+i.val < s-1 := by omega
      have hmid : s+i.val ≠ s-1 := by omega
      have hhigh : s+i.val ≠ s := by omega
      simp [regularOrderedCoordinatesInv,regularOrderedCoordinates,hi,hlow,hmid,hhigh]

theorem regularOrderedCoordinates_right_inv {s : ℕ} (hs : 0 < s)
    (a : BitString (s+s)) :
    regularOrderedCoordinates hs (regularOrderedCoordinatesInv hs a) = a := by
  funext i
  by_cases hi : i.val < s-1
  · have hne : s-1-i.val ≠ 0 := by omega
    have hback : s-1-(s-1-i.val) = i.val := by omega
    simp [regularOrderedCoordinates,regularOrderedCoordinatesInv,hi,hne,hback]
  · by_cases hi0 : i.val = s-1
    · have hieq : i = (⟨s-1,by omega⟩ : Fin (s+s)) := Fin.ext hi0
      rw [hieq]
      simp [regularOrderedCoordinates,regularOrderedCoordinatesInv,
        CharTwo.add_cancel_right]
    · by_cases hi1 : i.val = s
      · have hieq : i = (⟨s,by omega⟩ : Fin (s+s)) := Fin.ext hi1
        rw [hieq]
        simp [regularOrderedCoordinates,regularOrderedCoordinatesInv,
          show ¬ s < s-1 by omega,show s ≠ s-1 by omega]
      · have hne : i.val-s ≠ 0 := by omega
        have hback : s+(i.val-s) = i.val := by omega
        simp [regularOrderedCoordinates,regularOrderedCoordinatesInv,hi,hi0,hi1,hne,hback]

def regularOrderedLinearEquiv {s : ℕ} (hs : 0 < s) :
    PauliLabel s ≃ₗ[ZMod 2] BitString (s+s) where
  toFun := regularOrderedCoordinates hs
  invFun := regularOrderedCoordinatesInv hs
  left_inv := regularOrderedCoordinates_left_inv hs
  right_inv := regularOrderedCoordinates_right_inv hs
  map_add' p q := by
    funext i
    change regularOrderedCoordinates hs (p+q) i =
      regularOrderedCoordinates hs p i + regularOrderedCoordinates hs q i
    unfold regularOrderedCoordinates
    split_ifs <;> simp_all [Pi.add_apply] <;> ring
  map_smul' a p := by
    funext i
    change regularOrderedCoordinates hs (a • p) i = a • regularOrderedCoordinates hs p i
    unfold regularOrderedCoordinates
    split_ifs <;> simp_all [Pi.smul_apply,smul_eq_mul,mul_add]

theorem cnotGateLabel_fst_of_ne (n control target : ℕ) (p : PauliLabel n)
    (i : Fin n) (hi : i.val ≠ target) :
    (cnotGateLabel n control target p).1 i = p.1 i := by
  unfold cnotGateLabel
  split_ifs with hc ht
  · unfold cnotLabel
    split_ifs with hct
    · rfl
    · have hit : i ≠ (⟨target,ht⟩ : Fin n) :=
        fun h => hi (congrArg Fin.val h)
      simp [cnotBits,hit]
  · rfl
  · rfl

theorem cnotGateLabel_snd_of_ne (n control target : ℕ) (p : PauliLabel n)
    (i : Fin n) (hi : i.val ≠ control) :
    (cnotGateLabel n control target p).2 i = p.2 i := by
  unfold cnotGateLabel
  split_ifs with hc ht
  · unfold cnotLabel
    split_ifs with hct
    · rfl
    · have hic : i ≠ (⟨control,hc⟩ : Fin n) :=
        fun h => hi (congrArg Fin.val h)
      simp [cnotBits,hic]
  · rfl
  · rfl

theorem physical_cnot_layer_fst_fixed {n : ℕ} {ι : Type*} (L : List ι)
    (control target : ι → ℕ) (p : PauliLabel n) (i : Fin n)
    (hL : ∀ j ∈ L, i.val ≠ target j) :
    (physicalLayerLabel L (fun j => cnotGateLabel n (control j) (target j)) p).1 i =
      p.1 i := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    change (cnotGateLabel n (control j) (target j)
      (physicalLayerLabel L (fun k => cnotGateLabel n (control k) (target k)) p)).1 i = _
    rw [cnotGateLabel_fst_of_ne n (control j) (target j) _ i (hL j (by simp))]
    exact ih (fun k hk => hL k (by simp [hk]))

theorem physical_cnot_layer_snd_fixed {n : ℕ} {ι : Type*} (L : List ι)
    (control target : ι → ℕ) (p : PauliLabel n) (i : Fin n)
    (hL : ∀ j ∈ L, i.val ≠ control j) :
    (physicalLayerLabel L (fun j => cnotGateLabel n (control j) (target j)) p).2 i =
      p.2 i := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    change (cnotGateLabel n (control j) (target j)
      (physicalLayerLabel L (fun k => cnotGateLabel n (control k) (target k)) p)).2 i = _
    rw [cnotGateLabel_snd_of_ne n (control j) (target j) _ i (hL j (by simp))]
    exact ih (fun k hk => hL k (by simp [hk]))

theorem cnotGateLabel_last_fst {n : ℕ} (hn : 0 < n) (control target : ℕ)
    (htc : target < control) (p : PauliLabel n) :
    (cnotGateLabel n control target p).1 ⟨n-1,by omega⟩ = p.1 ⟨n-1,by omega⟩ := by
  by_cases hc : control < n
  · exact cnotGateLabel_fst_of_ne n control target p ⟨n-1,by omega⟩ (by simp only [Fin.val_mk]; omega)
  · simp [cnotGateLabel,hc]

theorem physical_cnot_layer_last_fst {n : ℕ} {ι : Type*} (hn : 0 < n)
    (L : List ι) (control target : ι → ℕ) (p : PauliLabel n)
    (hL : ∀ j ∈ L, target j < control j) :
    (physicalLayerLabel L (fun j => cnotGateLabel n (control j) (target j)) p).1
        ⟨n-1,by omega⟩ = p.1 ⟨n-1,by omega⟩ := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    change (cnotGateLabel n (control j) (target j)
      (physicalLayerLabel L (fun k => cnotGateLabel n (control k) (target k)) p)).1
        ⟨n-1,by omega⟩ = _
    rw [cnotGateLabel_last_fst hn (control j) (target j) (hL j (by simp))]
    exact ih (fun k hk => hL k (by simp [hk]))

theorem czGateLabel_fst (n left right : ℕ) (p : PauliLabel n) :
    (czGateLabel n left right p).1 = p.1 := by
  unfold czGateLabel
  split_ifs <;> rfl

theorem layerC1Linear_top_X_fixed {s : ℕ} (hs2 : 1 < s) (p : PauliLabel s) :
    (layerC1Linear s p).1 ⟨s-1,by omega⟩ = p.1 ⟨s-1,by omega⟩ := by
  have hs : 0 < s := by omega
  rw [layerC1Linear_apply]
  unfold layerC1Label hadamardGateLabel
  rw [dif_pos hs]
  change Function.update
      (physicalLayerLabel (List.range s) (fun j => cnotGateLabel s (2*j+2) (2*j+1)) p).1
      (⟨0,hs⟩ : Fin s) _ (⟨s-1,by omega⟩ : Fin s) = _
  have hne : (⟨s-1,by omega⟩ : Fin s) ≠ (⟨0,hs⟩ : Fin s) := by
    intro h
    have he := congrArg Fin.val h
    simp only [Fin.val_mk] at he
    omega
  rw [Function.update_of_ne hne]
  exact physical_cnot_layer_last_fst hs (List.range s) (fun j => 2*j+2)
    (fun j => 2*j+1) p (fun j hj => by omega)

theorem layerC2Linear_top_X_fixed {s : ℕ} (hs : 0 < s) (p : PauliLabel s) :
    (layerC2Linear s p).1 ⟨s-1,by omega⟩ = p.1 ⟨s-1,by omega⟩ := by
  rw [layerC2Linear_apply]
  change (czGateLabel s 0 1
    (physicalLayerLabel (List.range s) (fun j => cnotGateLabel s (2*j+3) (2*j+2)) p)).1
      ⟨s-1,by omega⟩ = _
  rw [czGateLabel_fst]
  exact physical_cnot_layer_last_fst hs (List.range s) (fun j => 2*j+3)
    (fun j => 2*j+2) p (fun j hj => by omega)

theorem regularCliffordLinear_top_X_fixed {s : ℕ} (hs2 : 1 < s)
    (p : PauliLabel s) :
    (regularCliffordLinear s p).1 ⟨s-1,by omega⟩ = p.1 ⟨s-1,by omega⟩ := by
  change (layerC2Linear s (layerC1Linear s p)).1 ⟨s-1,by omega⟩ = _
  rw [layerC2Linear_top_X_fixed (by omega),layerC1Linear_top_X_fixed hs2]

theorem physical_unitary_pow {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (k : ℕ) : unitaryMatrix (U ^ k) := by
  exact unitaryMatrix_pow hU k

theorem physical_real_pow {n : ℕ} {U : QuantumMatrix n}
    (hU : entrywiseReal U) (k : ℕ) : entrywiseReal (U ^ k) := by
  induction k with
  | zero => exact entrywiseReal_one n
  | succ k ih =>
    simpa only [pow_succ] using entrywiseReal_mul ih hU

theorem physical_real_projectivePauli_sign {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (hR : entrywiseReal U)
    (a : ℂ) (x z : BitString n) (hP : U = a • orderedPauli x z) :
    ∃ e : ZMod 2, U = bitSign e • orderedPauli x z := by
  have haReal : star a = a := by
    simpa [hP,Matrix.smul_apply,smul_eq_mul,orderedPauli_zero_column] using hR x 0
  have hprod := hU.1
  rw [hP] at hprod
  simp only [Matrix.conjTranspose_smul,smul_mul_assoc,mul_smul_comm,smul_smul,
    (orderedPauli_unitary x z).1] at hprod
  have hentry := congrArg (fun M : QuantumMatrix n => M 0 0) hprod
  have haNorm : star a * a = 1 := by
    simpa [Matrix.smul_apply,smul_eq_mul,mul_comm] using hentry
  rw [haReal] at haNorm
  have hfactor : (a-1)*(a+1)=0 := by
    calc
      (a-1)*(a+1) = a*a-1 := by ring
      _ = 0 := by rw [haNorm]; ring
  rcases mul_eq_zero.mp hfactor with hm | hp
  · have ha : a = 1 := sub_eq_zero.mp hm
    refine ⟨0,?_⟩
    simpa only [ha,bitSign_zero] using hP
  · have ha : a = -1 := by
      have he := congrArg (fun v : ℂ => v-1) hp
      simpa using he
    refine ⟨1,?_⟩
    simpa only [ha,bitSign_one] using hP

theorem physical_real_projectivePauli_actual {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (hR : entrywiseReal U)
    (a : ℂ) (x z : BitString n) (hP : U = a • orderedPauli x z) :
    actualPauli U := by
  obtain ⟨e,he⟩ := physical_real_projectivePauli_sign hU hR a x z hP
  exact ⟨bitSign e,x,z,bitSign_phase e,he⟩

theorem physical_real_projectivePauli_square {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (hR : entrywiseReal U)
    (a : ℂ) (x z : BitString n) (hP : U = a • orderedPauli x z)
    (hHermitian : dot z x = 0) : U ^ 2 = 1 := by
  obtain ⟨e,he⟩ := physical_real_projectivePauli_sign hU hR a x z hP
  rw [he,pow_two,smul_mul_assoc,mul_smul_comm,smul_smul,bitSign_mul_self,one_smul]
  rw [← pow_two,orderedPauli_sq,character,hHermitian,bitSign_zero,one_smul]

theorem regularClifford_pow_signed_identity {s q : ℕ}
    (hF : regularCliffordLinear s ^ q = 1) :
    implementsRealPauliLabels (regularClifford s ^ q) id := by
  intro x z
  refine ⟨regularCliffordPowerSign s q (x,z),?_⟩
  have hp := regularClifford_pow_signed_action s q (x,z)
  rw [hF] at hp
  exact hp

theorem layerC1_one :
    layerC1 1 = hadamardMatrix (⟨0,by decide⟩ : Fin 1) := by
  simp [layerC1,hadamardGate,cnotGate,List.range_succ]

theorem layerC2_one : layerC2 1 = 1 := by
  simp [layerC2,czGate,cnotGate,List.range_succ]

theorem regularClifford_one :
    regularClifford 1 = hadamardMatrix (⟨0,by decide⟩ : Fin 1) := by
  rw [regularClifford,layerC2_one,layerC1_one,one_mul]

theorem regularClifford_one_square : regularClifford 1 ^ 2 = 1 := by
  rw [regularClifford_one,pow_two]
  exact hadamardMatrix_square _

theorem physical_binary_commutant_extend {n : ℕ} (U : QuantumMatrix n)
    (M : BitString n → QuantumMatrix n)
    (hzero : M 0 = 1) (hadd : ∀ x y, M (x+y) = M x * M y)
    (hgen : ∀ i : Fin n, Commute U (M (Pi.single i 1))) :
    ∀ x : BitString n, Commute U (M x) := by
  classical
  intro x
  have hs : ∀ S : Finset (Fin n),
      Commute U (M (∑ i ∈ S, Pi.single i (x i))) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, hzero]; exact Commute.one_right U
    | @insert i S hi ih =>
      rw [Finset.sum_insert hi, hadd]
      apply Commute.mul_right _ ih
      generalize hv : x i = v
      fin_cases v
      · change Commute U (M (Pi.single i (0 : ZMod 2)))
        simp only [Pi.single_zero,hzero]
        exact Commute.one_right U
      · change Commute U (M (Pi.single i (1 : ZMod 2)))
        exact hgen i
  simpa only [Finset.univ_sum_single] using hs Finset.univ

theorem physical_generator_commutant_scalar {n : ℕ} (U : QuantumMatrix n)
    (hZ : ∀ i : Fin n, Commute U (zMatrix (Pi.single i 1)))
    (hX : ∀ i : Fin n, Commute U (xMatrix (Pi.single i 1))) :
    U = U 0 0 • (1 : QuantumMatrix n) := by
  apply pauli_commutant_scalar U
  · intro z
    apply (physical_binary_commutant_extend U zMatrix (zMatrix_zero n) ?_ hZ z).eq
    intro x y
    simpa only [orderedPauli_z, zero_add, character_zero_basis, one_smul]
      using (orderedPauli_mul (0 : BitString n) x 0 y).symm
  · intro x
    apply (physical_binary_commutant_extend U xMatrix (xMatrix_zero n) ?_ hX x).eq
    intro x y
    simpa only [orderedPauli_x, zero_add, character_zero_label, one_smul]
      using (orderedPauli_mul x (0 : BitString n) y 0).symm

theorem physical_conjugate_orderedPauli {n : ℕ}
    (x z y w : BitString n) :
    conjugate (orderedPauli x z) (orderedPauli y w) =
      (character z y * character w x) • orderedPauli y w := by
  have hx : x+y+x = y := by
    calc x+y+x = x+x+y := by abel
         _ = y := by rw [bitString_add_self,zero_add]
  have hz : z+w+z = w := by
    calc z+w+z = z+z+w := by abel
         _ = w := by rw [bitString_add_self,zero_add]
  rw [conjugate,orderedPauli_conjTranspose,mul_smul_comm,
    orderedPauli_mul,smul_mul_assoc,orderedPauli_mul,smul_smul,smul_smul,
    hx,hz,character_add_label]
  congr 1
  calc
    (character z x * character z y) * (character z x * character w x) =
      (character z x * character z x) * (character z y * character w x) := by ring
    _ = character z y * character w x := by rw [character_mul_self,one_mul]

theorem physical_conjugate_adjoint_left_inverse {n : ℕ} {P : QuantumMatrix n}
    (hP : unitaryMatrix P) (Q : QuantumMatrix n) :
    conjugate P.conjTranspose (conjugate P Q) = Q := by
  rw [conjugate,conjugate,Matrix.conjTranspose_conjTranspose]
  calc
    P.conjTranspose * (P*Q*P.conjTranspose) * P =
      (P.conjTranspose*P)*Q*(P.conjTranspose*P) := by simp only [mul_assoc]
    _ = Q := by rw [hP.1]; simp

theorem physical_conjugate_fixed_commute {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (Q : QuantumMatrix n) (hQ : conjugate U Q = Q) :
    Commute U Q := by
  change U*Q=Q*U
  calc
    U*Q = conjugate U Q * U := by
      rw [conjugate]
      calc U*Q = U*Q*(U.conjTranspose*U) := by rw [hU.1,mul_one]
           _ = U*Q*U.conjTranspose*U := by simp only [mul_assoc]
    _ = Q*U := by rw [hQ]

set_option maxHeartbeats 800000 in
theorem physical_realPauliLabels_identity_projective {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (hF : implementsRealPauliLabels U id) :
    ∃ (a : ℂ) (x z : BitString n), U = a • orderedPauli x z := by
  let x : BitString n := fun i => Classical.choose (hF 0 (Pi.single i 1))
  let z : BitString n := fun i => Classical.choose (hF (Pi.single i 1) 0)
  let P : QuantumMatrix n := orderedPauli x z
  have hP : unitaryMatrix P := orderedPauli_unitary x z
  have hZ : ∀ i : Fin n, conjugate U (zMatrix (Pi.single i 1)) =
      conjugate P (zMatrix (Pi.single i 1)) := by
    intro i
    have hi := Classical.choose_spec (hF 0 (Pi.single i 1))
    simpa only [P,x,← orderedPauli_z,physical_conjugate_orderedPauli,
      character_zero_basis,one_mul,pauli_character_single_unit,
      id_eq,Prod.fst,Prod.snd] using hi
  have hX : ∀ i : Fin n, conjugate U (xMatrix (Pi.single i 1)) =
      conjugate P (xMatrix (Pi.single i 1)) := by
    intro i
    have hi := Classical.choose_spec (hF (Pi.single i 1) 0)
    simpa only [P,z,← orderedPauli_x,physical_conjugate_orderedPauli,
      character_zero_label,mul_one,character,physical_dot_single_right,
      dot_zero_left,bitSign_zero,id_eq,Prod.fst,Prod.snd] using hi
  let V : QuantumMatrix n := P.conjTranspose*U
  have hV : unitaryMatrix V := unitaryMatrix_mul (unitaryMatrix_conjTranspose hP) hU
  have hVZ : ∀ i : Fin n, Commute V (zMatrix (Pi.single i 1)) := by
    intro i
    apply physical_conjugate_fixed_commute hV
    dsimp only [V]
    rw [physical_conjugate_mul,hZ i]
    exact physical_conjugate_adjoint_left_inverse hP _
  have hVX : ∀ i : Fin n, Commute V (xMatrix (Pi.single i 1)) := by
    intro i
    apply physical_conjugate_fixed_commute hV
    dsimp only [V]
    rw [physical_conjugate_mul,hX i]
    exact physical_conjugate_adjoint_left_inverse hP _
  have hscalar := physical_generator_commutant_scalar V hVZ hVX
  refine ⟨V 0 0,x,z,?_⟩
  calc
    U = P*V := by
      dsimp [V]
      rw [← mul_assoc,hP.2,one_mul]
    _ = (V 0 0) • P := by
      calc
        P*V = P*((V 0 0) • (1 : QuantumMatrix n)) :=
          congrArg (fun M : QuantumMatrix n => P*M) hscalar
        _ = (V 0 0) • P := by rw [mul_smul_comm,mul_one]
    _ = (V 0 0) • orderedPauli x z := rfl

theorem physical_realPauliLabels_identity_sign {n : ℕ} {U : QuantumMatrix n}
    (hU : unitaryMatrix U) (hR : entrywiseReal U)
    (hF : implementsRealPauliLabels U id) :
    ∃ (e : ZMod 2) (x z : BitString n), U = bitSign e • orderedPauli x z := by
  obtain ⟨a,x,z,he⟩ := physical_realPauliLabels_identity_projective hU hF
  obtain ⟨e,he⟩ := physical_real_projectivePauli_sign hU hR a x z he
  exact ⟨e,x,z,he⟩

def cnotLayerDelta (n control target : ℕ) (p : PauliLabel n) : PauliLabel n :=
  if hc : control < n then
    if ht : target < n then
      (Pi.single (⟨target,ht⟩ : Fin n) (p.1 ⟨control,hc⟩),
       Pi.single (⟨control,hc⟩ : Fin n) (p.2 ⟨target,ht⟩))
    else 0
  else 0

theorem cnotGateLabel_eq_add_delta (n control target : ℕ)
    (htc : target < control) (p : PauliLabel n) :
    cnotGateLabel n control target p = p+cnotLayerDelta n control target p := by
  unfold cnotGateLabel cnotLayerDelta
  split_ifs with hc ht
  · have hct : (⟨control,hc⟩ : Fin n) ≠ (⟨target,ht⟩ : Fin n) := by
      intro h
      have he := congrArg Fin.val h
      simp only [Fin.val_mk] at he
      omega
    simp only [cnotLabel,if_neg hct,cnotBits_as_add_single]
    rfl
  · simp
  · simp

theorem physical_cnot_layer_flat {n : ℕ} {ι : Type*} (L : List ι)
    (control target : ι → ℕ) (p : PauliLabel n)
    (hlt : ∀ j ∈ L, target j < control j)
    (hcross : ∀ j ∈ L, ∀ k ∈ L, control j ≠ target k) :
    physicalLayerLabel L (fun j => cnotGateLabel n (control j) (target j)) p =
      p+(L.map (fun j => cnotLayerDelta n (control j) (target j) p)).sum := by
  induction L with
  | nil => simp [physicalLayerLabel]
  | cons j L ih =>
    have hdelta : cnotLayerDelta n (control j) (target j)
        (physicalLayerLabel L (fun k => cnotGateLabel n (control k) (target k)) p) =
        cnotLayerDelta n (control j) (target j) p := by
      unfold cnotLayerDelta
      split_ifs with hc ht
      · rw [physical_cnot_layer_fst_fixed L control target p ⟨control j,hc⟩
          (fun k hk => hcross j (by simp) k (by simp [hk]))]
        rw [physical_cnot_layer_snd_fixed L control target p ⟨target j,ht⟩
          (fun k hk => (hcross k (by simp [hk]) j (by simp)).symm)]
      · rfl
      · rfl
    change cnotGateLabel n (control j) (target j)
      (physicalLayerLabel L (fun k => cnotGateLabel n (control k) (target k)) p) = _
    rw [cnotGateLabel_eq_add_delta n (control j) (target j) (hlt j (by simp)),hdelta]
    rw [ih (fun k hk => hlt k (by simp [hk]))
      (fun k hk l hl => hcross k (by simp [hk]) l (by simp [hl]))]
    simp only [List.map_cons,List.sum_cons]
    abel

theorem regularOrderedCoordinates_X_single {s : ℕ} (hs : 0 < s)
    (j : Fin s) (hj : 0 < j.val) (a : ZMod 2) :
    regularOrderedCoordinates hs (Pi.single j a,0) =
      Pi.single (⟨s-1-j.val,by have hjs:=j.isLt; omega⟩ : Fin (s+s)) a := by
  funext i
  have hil:=i.isLt
  have hjl:=j.isLt
  simp only [regularOrderedCoordinates,Pi.single_apply,Pi.zero_apply,
    Fin.ext_iff,Fin.val_mk]
  split_ifs <;> simp_all <;> omega

theorem regularOrderedCoordinates_Z_single {s : ℕ} (hs : 0 < s)
    (j : Fin s) (hj : 0 < j.val) (a : ZMod 2) :
    regularOrderedCoordinates hs (0,Pi.single j a) =
      Pi.single (⟨s+j.val,by have hjs:=j.isLt; omega⟩ : Fin (s+s)) a := by
  funext i
  have hil:=i.isLt
  have hjl:=j.isLt
  simp only [regularOrderedCoordinates,Pi.single_apply,Pi.zero_apply,
    Fin.ext_iff,Fin.val_mk]
  split_ifs <;> simp_all <;> omega

theorem physical_conjugate_smul {n : ℕ} (U P : QuantumMatrix n) (a : ℂ) :
    conjugate U (a • P) = a • conjugate U P := by
  simp only [conjugate,mul_smul_comm,smul_mul_assoc]

theorem physical_conjugate_bitSign_left {n : ℕ}
    (U P : QuantumMatrix n) (e : ZMod 2) :
    conjugate (bitSign e • U) P = conjugate U P := by
  simp only [conjugate,Matrix.conjTranspose_smul,bitSign_star,
    smul_mul_assoc,mul_smul_comm,smul_smul,bitSign_mul_self,one_smul]

theorem regularClifford_power_label_fixed {s q : ℕ}
    (hfaith : ∀ (a : ℂ) (p r : PauliLabel s),
      orderedPauli p.1 p.2 = a • orderedPauli r.1 r.2 → p=r)
    (e : ZMod 2) (p : PauliLabel s)
    (he : regularClifford s ^ q = bitSign e • orderedPauli p.1 p.2) :
    regularCliffordLinear s p = p := by
  have hcomm : Commute (regularClifford s) (regularClifford s ^ q) :=
    (Commute.refl _).pow_right q
  have hinv : conjugate (regularClifford s) (regularClifford s ^ q) =
      regularClifford s ^ q := by
    rw [conjugate,hcomm.eq,mul_assoc,(regularClifford_unitary s).2,mul_one]
  rw [he,physical_conjugate_smul] at hinv
  have hbase := congrArg (fun M : QuantumMatrix s => bitSign e • M) hinv
  simp only [smul_smul,bitSign_mul_self,one_smul] at hbase
  rw [regularClifford_signed_linear] at hbase
  have hf := congrArg
    (fun M : QuantumMatrix s => bitSign (regularCliffordSign s p) • M) hbase
  simp only [smul_smul,bitSign_mul_self,one_smul] at hf
  exact hfaith (bitSign (regularCliffordSign s p)) (regularCliffordLinear s p) p hf

theorem regularClifford_pow_linear_identity_of_projective {s k : ℕ}
    (hfaith : ∀ (a : ℂ) (p r : PauliLabel s),
      orderedPauli p.1 p.2 = a • orderedPauli r.1 r.2 → p=r)
    (a : ℂ) (x z : BitString s)
    (he : regularClifford s ^ k = a • orderedPauli x z) :
    regularCliffordLinear s ^ k = 1 := by
  obtain ⟨e,he⟩ := physical_real_projectivePauli_sign
    (unitaryMatrix_pow (regularClifford_unitary s) k)
    (physical_real_pow (regularClifford_real s) k) a x z he
  apply LinearMap.ext
  intro p
  change (regularCliffordLinear s ^ k) p = p
  have hact := regularClifford_pow_signed_action s k p
  rw [he,physical_conjugate_bitSign_left,physical_conjugate_orderedPauli] at hact
  have hf := congrArg
    (fun M : QuantumMatrix s => bitSign (regularCliffordPowerSign s k p) • M) hact.symm
  simp only [smul_smul,bitSign_mul_self,one_smul] at hf
  exact hfaith
    (bitSign (regularCliffordPowerSign s k p) * (character z p.1 * character p.2 x))
    ((regularCliffordLinear s ^ k) p) p hf

theorem regularClifford_pow_not_projective {s k : ℕ}
    (hfaith : ∀ (a : ℂ) (p r : PauliLabel s),
      orderedPauli p.1 p.2 = a • orderedPauli r.1 r.2 → p=r)
    (hne : regularCliffordLinear s ^ k ≠ 1) :
    ∀ (a : ℂ) (x z : BitString s), regularClifford s ^ k ≠ a • orderedPauli x z := by
  intro a x z he
  exact hne (regularClifford_pow_linear_identity_of_projective hfaith a x z he)

theorem regularClifford_pow_sign_of_linear_identity {s q : ℕ}
    (hF : regularCliffordLinear s ^ q=1) :
    ∃ (e : ZMod 2) (p : PauliLabel s),
      regularClifford s ^ q=bitSign e • orderedPauli p.1 p.2 := by
  obtain ⟨e,x,z,he⟩:=physical_realPauliLabels_identity_sign
    (unitaryMatrix_pow (regularClifford_unitary s) q)
    (physical_real_pow (regularClifford_real s) q)
    (regularClifford_pow_signed_identity hF)
  exact ⟨e,(x,z),he⟩

theorem regularClifford_pow_sign_fixed_of_linear_identity {s q : ℕ}
    (hfaith : ∀ (a : ℂ) (p r : PauliLabel s),
      orderedPauli p.1 p.2=a • orderedPauli r.1 r.2 → p=r)
    (hF : regularCliffordLinear s ^ q=1) :
    ∃ (e : ZMod 2) (p : PauliLabel s),
      regularClifford s ^ q=bitSign e • orderedPauli p.1 p.2 ∧
        regularCliffordLinear s p=p := by
  obtain ⟨e,p,he⟩:=regularClifford_pow_sign_of_linear_identity hF
  exact ⟨e,p,he,regularClifford_power_label_fixed hfaith e p he⟩

theorem physical_list_range_sum {α : Type*} [AddCommMonoid α] (f : ℕ → α) (k : ℕ) :
    ((List.range k).map f).sum = ∑ j ∈ Finset.range k, f j := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.sum_range_succ,Finset.sum_range_succ,ih]

@[simp] theorem regularOrderedCoordinates_center {s : ℕ} (hs : 0 < s)
    (p : PauliLabel s) :
    regularOrderedCoordinates hs p (⟨s-1,by omega⟩ : Fin (s+s)) =
      p.2 ⟨0,hs⟩+p.1 ⟨0,hs⟩ := by
  rw [regularOrderedCoordinates,dif_neg (show ¬ s-1 < s-1 by omega),dif_pos rfl]

@[simp] theorem regularOrderedCoordinates_pivot {s : ℕ} (hs : 0 < s)
    (p : PauliLabel s) :
    regularOrderedCoordinates hs p (⟨s,by omega⟩ : Fin (s+s)) = p.1 ⟨0,hs⟩ := by
  rw [regularOrderedCoordinates,dif_neg (show ¬ s < s-1 by omega),
    dif_neg (show s ≠ s-1 by omega),dif_pos rfl]

theorem regularOrderedCoordinates_X_eval {s : ℕ} (hs : 0 < s)
    (p : PauliLabel s) (j : Fin s) (hj : 0 < j.val) :
    regularOrderedCoordinates hs p (⟨s-1-j.val,by have hjs:=j.isLt; omega⟩ : Fin (s+s)) =
      p.1 j := by
  have hjs:=j.isLt
  have hlow : s-1-j.val < s-1 := by omega
  have hback : s-1-(s-1-j.val) = j.val := by omega
  rw [regularOrderedCoordinates,dif_pos hlow]
  exact congrArg p.1 (Fin.ext hback)

theorem regularOrderedCoordinates_Z_eval {s : ℕ} (hs : 0 < s)
    (p : PauliLabel s) (j : Fin s) (hj : 0 < j.val) :
    regularOrderedCoordinates hs p (⟨s+j.val,by have hjs:=j.isLt; omega⟩ : Fin (s+s)) =
      p.2 j := by
  have hjs:=j.isLt
  rw [regularOrderedCoordinates,dif_neg (show ¬ s+j.val < s-1 by omega),
    dif_neg (show s+j.val ≠ s-1 by omega),dif_neg (show s+j.val ≠ s by omega)]
  simp only [Fin.val_mk,Nat.add_sub_cancel_left]

theorem regularOrderedCoordinates_Z0_single {s : ℕ} (hs : 0 < s) (a : ZMod 2) :
    regularOrderedCoordinates hs (0,Pi.single (⟨0,hs⟩ : Fin s) a) =
      Pi.single (⟨s-1,by omega⟩ : Fin (s+s)) a := by
  funext i
  have hil:=i.isLt
  simp only [regularOrderedCoordinates,Pi.single_apply,Pi.zero_apply,
    Fin.ext_iff,Fin.val_mk]
  split_ifs <;> simp_all <;> omega

theorem regularOrderedCoordinates_Y0_single {s : ℕ} (hs : 0 < s) (a : ZMod 2) :
    regularOrderedCoordinates hs
        (Pi.single (⟨0,hs⟩ : Fin s) a,Pi.single (⟨0,hs⟩ : Fin s) a) =
      Pi.single (⟨s,by omega⟩ : Fin (s+s)) a := by
  have hsp : s<s+s := by omega
  funext i
  have hil := i.isLt
  by_cases hpivot : i.val=s
  · have hi : i=(⟨s,hsp⟩ : Fin (s+s)) := Fin.ext hpivot
    rw [hi,regularOrderedCoordinates_pivot]
    simp only [Pi.single_eq_same]
  · have hine : i≠(⟨s,hsp⟩ : Fin (s+s)) := by
      intro he
      exact hpivot (congrArg Fin.val he)
    have hrhs : (Pi.single (⟨s,hsp⟩ : Fin (s+s)) a : BitString (s+s)) i=0 := by
      simp only [Pi.single_apply,hine,if_false]
    rw [hrhs]
    by_cases hlow : i.val<s-1
    · rw [regularOrderedCoordinates,dif_pos hlow]
      have hz : s-1-i.val≠0 := by omega
      have hn : (⟨s-1-i.val,by omega⟩ : Fin s)≠(⟨0,hs⟩ : Fin s) := by
        intro he
        exact hz (congrArg Fin.val he)
      simp only [Pi.single_apply,hn,if_false]
    · by_cases hcenter : i.val=s-1
      · rw [regularOrderedCoordinates,dif_neg hlow,dif_pos hcenter]
        simp only [Pi.single_eq_same]
        exact CharTwo.add_self_eq_zero a
      · rw [regularOrderedCoordinates,dif_neg hlow,dif_neg hcenter,dif_neg hpivot]
        have hz : i.val-s≠0 := by omega
        have hn : (⟨i.val-s,by omega⟩ : Fin s)≠(⟨0,hs⟩ : Fin s) := by
          intro he
          exact hz (congrArg Fin.val he)
        simp only [Pi.single_apply,hn,if_false]

theorem hadamardLabel_eq_add_selfPair_single {n : ℕ} (wire : Fin n)
    (p : PauliLabel n) :
    hadamardLabel wire p = p+
      (Pi.single wire (p.1 wire+p.2 wire),Pi.single wire (p.1 wire+p.2 wire)) := by
  apply Prod.ext
  · funext i
    by_cases hi : i=wire
    · subst i
      simp [hadamardLabel,Pi.add_apply,Pi.single_apply,CharTwo.add_cancel_left]
    · simp [hadamardLabel,Pi.add_apply,Pi.single_apply,hi]
  · funext i
    by_cases hi : i=wire
    · subst i
      simp [hadamardLabel,Pi.add_apply,Pi.single_apply,add_left_comm,
        CharTwo.add_cancel_left,CharTwo.add_self_eq_zero]
    · simp [hadamardLabel,Pi.add_apply,Pi.single_apply,hi]

theorem regularOrderedCoordinates_H0 {s : ℕ} (hs : 0 < s) (p : PauliLabel s) :
    regularOrderedCoordinates hs (hadamardLabel (⟨0,hs⟩ : Fin s) p) =
      regularOrderedCoordinates hs p+
        Pi.single (⟨s,by omega⟩ : Fin (s+s))
          (regularOrderedCoordinates hs p (⟨s-1,by omega⟩ : Fin (s+s))) := by
  rw [regularOrderedCoordinates_center]
  let E:=regularOrderedLinearEquiv hs
  change E (hadamardLabel (⟨0,hs⟩ : Fin s) p) = E p+
    Pi.single (⟨s,by omega⟩ : Fin (s+s)) (p.2 ⟨0,hs⟩+p.1 ⟨0,hs⟩)
  rw [hadamardLabel_eq_add_selfPair_single,map_add]
  have hY:=regularOrderedCoordinates_Y0_single hs (p.1 ⟨0,hs⟩+p.2 ⟨0,hs⟩)
  change E _ = _ at hY
  rw [hY,add_comm (p.1 ⟨0,hs⟩) (p.2 ⟨0,hs⟩)]

theorem regularOrderedCoordinates_CZ01 {s : ℕ} (hs2 : 1 < s) (p : PauliLabel s) :
    regularOrderedCoordinates (by omega : 0<s)
        (czLabel (⟨0,by omega⟩ : Fin s) (⟨1,hs2⟩ : Fin s) p) =
      regularOrderedCoordinates (by omega : 0<s) p+
        Pi.single (⟨s-1,by omega⟩ : Fin (s+s)) (p.1 ⟨1,hs2⟩)+
        Pi.single (⟨s+1,by omega⟩ : Fin (s+s)) (p.1 ⟨0,by omega⟩) := by
  have hs : 0<s := by omega
  let E:=regularOrderedLinearEquiv hs
  have hlabel : czLabel (⟨0,hs⟩ : Fin s) (⟨1,hs2⟩ : Fin s) p =
      p+(0,Pi.single (⟨0,hs⟩ : Fin s) (p.1 ⟨1,hs2⟩))+
        (0,Pi.single (⟨1,hs2⟩ : Fin s) (p.1 ⟨0,hs⟩)) := by
    apply Prod.ext <;> funext i <;> simp [czLabel,Pi.add_apply,add_assoc]
  change E _ = E p+_+_
  rw [hlabel,map_add,map_add]
  have hZ0:=regularOrderedCoordinates_Z0_single hs (p.1 ⟨1,hs2⟩)
  have hZ1:=regularOrderedCoordinates_Z_single hs (⟨1,hs2⟩ : Fin s)
    (by decide : 0<(1:ℕ)) (p.1 ⟨0,hs⟩)
  change E _ = _ at hZ0 hZ1
  rw [hZ0,hZ1]

def regularOrderedHead {d : ℕ} (hd : 0<d) : BitString d →ₗ[ZMod 2] ZMod 2 where
  toFun v := v ⟨0,hd⟩
  map_add' v w := rfl
  map_smul' a v := rfl

theorem regular_triangular_range_eq_head_kernel {d : ℕ} (hd : 0<d)
    (N : Matrix (Fin d) (Fin d) (ZMod 2))
    (htri : ∀ i j : Fin d, i.val ≤ j.val → N i j=0)
    (hstep : ∀ i j : Fin d, i.val=j.val+1 → N i j=1) :
    LinearMap.range (Matrix.mulVecLin N) = LinearMap.ker (regularOrderedHead hd) := by
  let first : Fin d := ⟨0,hd⟩
  let last : Fin d := ⟨d-1,by omega⟩
  let e : BitString d := Pi.single last 1
  have hezero : Matrix.mulVecLin N e=0 := by
    funext i
    have hz : N i last=0 := htri i last (by dsimp [last]; have hil:=i.isLt; omega)
    change (N *ᵥ Pi.single last (1 : ZMod 2)) i=0
    simp [Matrix.mulVec_single,hz]
  have hker : LinearMap.ker (Matrix.mulVecLin N)=Submodule.span (ZMod 2) {e} := by
    apply le_antisymm
    · intro v hv
      apply Submodule.mem_span_singleton.mpr
      refine ⟨v last,?_⟩
      exact (regular_triangular_kernel_last hd N htri hstep v
        (LinearMap.mem_ker.mp hv)).symm
    · apply Submodule.span_le.mpr
      intro v hv
      have hvEq : v=e := Set.mem_singleton_iff.mp hv
      rw [hvEq]
      exact LinearMap.mem_ker.mpr hezero
  have he : e≠0 := by
    intro h
    have hv:=congrFun h last
    simp [e] at hv
  have hkerdim : Module.finrank (ZMod 2) (LinearMap.ker (Matrix.mulVecLin N))=1 := by
    rw [hker]
    exact finrank_span_singleton he
  have hsurj : Function.Surjective (regularOrderedHead hd) := by
    intro a
    refine ⟨Pi.single first a,?_⟩
    simp [regularOrderedHead,first]
  have hrange : LinearMap.range (regularOrderedHead hd)=⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrangedim : Module.finrank (ZMod 2) (LinearMap.range (regularOrderedHead hd))=1 := by
    rw [hrange,finrank_top]
    exact Module.finrank_self (ZMod 2)
  have hle : LinearMap.range (Matrix.mulVecLin N) ≤ LinearMap.ker (regularOrderedHead hd) := by
    rintro w ⟨v,rfl⟩
    apply LinearMap.mem_ker.mpr
    change (∑ j : Fin d, N first j*v j)=0
    apply Finset.sum_eq_zero
    intro j hj
    rw [htri first j (by dsimp [first]; omega),zero_mul]
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hN:=(Matrix.mulVecLin N).finrank_range_add_finrank_ker
  have hH:=(regularOrderedHead hd).finrank_range_add_finrank_ker
  rw [hkerdim] at hN
  rw [hrangedim] at hH
  change Module.finrank (ZMod 2) (LinearMap.range (Matrix.mulVecLin N))+1=
    Module.finrank (ZMod 2) (BitString d) at hN
  exact Nat.add_right_cancel (hN.trans (hH.symm.trans (Nat.add_comm _ _)))

theorem regular_triangular_difference_mem_range {d : ℕ} (hd : 0<d)
    (N : Matrix (Fin d) (Fin d) (ZMod 2))
    (htri : ∀ i j : Fin d, i.val ≤ j.val → N i j=0)
    (hstep : ∀ i j : Fin d, i.val=j.val+1 → N i j=1)
    (C : BitString d →ₗ[ZMod 2] BitString d)
    (hC : ∀ v, regularOrderedHead hd (C v)=regularOrderedHead hd v) (v : BitString d) :
    C v-v ∈ LinearMap.range (Matrix.mulVecLin N) := by
  rw [regular_triangular_range_eq_head_kernel hd N htri hstep]
  apply LinearMap.mem_ker.mpr
  rw [map_sub,hC v,sub_self]

theorem regular_matrix_single_mulVec {d : ℕ} (i j : Fin d) (v : BitString d) :
    Matrix.single i j (1 : ZMod 2) *ᵥ v = Pi.single i (v j) := by
  funext k
  by_cases hk : k=i <;>
    simp [Matrix.single_mulVec,Function.update_apply,Pi.single_apply,hk]

def regularCnotStepMatrix (s control target : ℕ) :
    Matrix (Fin (s+s)) (Fin (s+s)) (ZMod 2) :=
  if h : 0<target ∧ target<control ∧ control<s then
    Matrix.single (⟨s-1-target,by omega⟩ : Fin (s+s))
        (⟨s-1-control,by omega⟩ : Fin (s+s)) 1+
      Matrix.single (⟨s+control,by omega⟩ : Fin (s+s))
        (⟨s+target,by omega⟩ : Fin (s+s)) 1
  else 0

theorem regularOrderedCoordinates_cnotDelta {s : ℕ} (hs : 0<s)
    (control target : ℕ) (ht : 0<target) (htc : target<control) (p : PauliLabel s) :
    regularOrderedCoordinates hs (cnotLayerDelta s control target p) =
      regularCnotStepMatrix s control target *ᵥ regularOrderedCoordinates hs p := by
  let E:=regularOrderedLinearEquiv hs
  by_cases hc : control<s
  · have hts : target<s := by omega
    have hcs : 0<control := by omega
    have hvalid : 0<target ∧ target<control ∧ control<s := ⟨ht,htc,hc⟩
    have hd : cnotLayerDelta s control target p =
        (Pi.single (⟨target,hts⟩ : Fin s) (p.1 ⟨control,hc⟩),0)+
        (0,Pi.single (⟨control,hc⟩ : Fin s) (p.2 ⟨target,hts⟩)) := by
      simp [cnotLayerDelta,hc,hts]
    change E _ = regularCnotStepMatrix s control target *ᵥ E p
    rw [hd,map_add,regularCnotStepMatrix,dif_pos hvalid,Matrix.add_mulVec,
      regular_matrix_single_mulVec,regular_matrix_single_mulVec]
    have hX:=regularOrderedCoordinates_X_single hs (⟨target,hts⟩ : Fin s)
      ht (p.1 ⟨control,hc⟩)
    have hZ:=regularOrderedCoordinates_Z_single hs (⟨control,hc⟩ : Fin s)
      hcs (p.2 ⟨target,hts⟩)
    have hXe:=regularOrderedCoordinates_X_eval hs p (⟨control,hc⟩ : Fin s) hcs
    have hZe:=regularOrderedCoordinates_Z_eval hs p (⟨target,hts⟩ : Fin s) ht
    change E _ = _ at hX hZ
    change E p _ = _ at hXe hZe
    rw [hX,hZ,hXe,hZe]
  · have hvalid : ¬(0<target ∧ target<control ∧ control<s) := fun h => hc h.2.2
    change E _ = _
    simp [cnotLayerDelta,hc,regularCnotStepMatrix,hvalid]

theorem regular_cnot_layer_ordered_matrix {s : ℕ} (hs : 0<s) (k : ℕ)
    (control target : ℕ → ℕ) (p : PauliLabel s)
    (hpos : ∀ j<k, 0<target j) (hlt : ∀ j<k, target j<control j)
    (hcross : ∀ j<k, ∀ l<k, control j ≠ target l) :
    regularOrderedCoordinates hs
        (physicalLayerLabel (List.range k)
          (fun j => cnotGateLabel s (control j) (target j)) p) =
      (1+∑ j ∈ Finset.range k, regularCnotStepMatrix s (control j) (target j)) *ᵥ
        regularOrderedCoordinates hs p := by
  let E:=regularOrderedLinearEquiv hs
  have hflat:=physical_cnot_layer_flat (List.range k) control target p
    (fun j hj => hlt j (List.mem_range.mp hj))
    (fun j hj l hl => hcross j (List.mem_range.mp hj) l (List.mem_range.mp hl))
  change E _ = _
  rw [hflat,map_add,physical_list_range_sum,map_sum,Matrix.add_mulVec,
    Matrix.one_mulVec,Matrix.sum_mulVec]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact regularOrderedCoordinates_cnotDelta hs (control j) (target j)
    (hpos j (Finset.mem_range.mp hj)) (hlt j (Finset.mem_range.mp hj)) p

def regularHStepMatrix {s : ℕ} (hs : 0<s) :
    Matrix (Fin (s+s)) (Fin (s+s)) (ZMod 2) :=
  Matrix.single (⟨s,by omega⟩ : Fin (s+s)) (⟨s-1,by omega⟩ : Fin (s+s)) 1

theorem regular_hadamard_ordered_matrix {s : ℕ} (hs : 0<s) (p : PauliLabel s) :
    regularOrderedCoordinates hs (hadamardLabel (⟨0,hs⟩ : Fin s) p) =
      (1+regularHStepMatrix hs) *ᵥ regularOrderedCoordinates hs p := by
  rw [regularOrderedCoordinates_H0,regularHStepMatrix,Matrix.add_mulVec,
    Matrix.one_mulVec,regular_matrix_single_mulVec]

def regularAdjacentStepMatrix (d parity : ℕ) : Matrix (Fin d) (Fin d) (ZMod 2) :=
  fun i j => if i.val=j.val+1 ∧ i.val%2=parity%2 then 1 else 0

theorem regularCnotStepMatrix_entry {s : ℕ} (control target : ℕ)
    (ht : 0<target) (htc : target<control) (hc : control<s)
    (i j : Fin (s+s)) :
    regularCnotStepMatrix s control target i j =
      (if s-1-target=i.val ∧ s-1-control=j.val then 1 else 0)+
      (if s+control=i.val ∧ s+target=j.val then 1 else 0) := by
  have hvalid : 0<target ∧ target<control ∧ control<s := ⟨ht,htc,hc⟩
  simp only [regularCnotStepMatrix,dif_pos hvalid,Matrix.add_apply,
    Matrix.single_apply,Fin.ext_iff,Fin.val_mk]

theorem regularHStepMatrix_entry {s : ℕ} (hs : 0<s) (i j : Fin (s+s)) :
    regularHStepMatrix hs i j = if s=i.val ∧ s-1=j.val then 1 else 0 := by
  simp only [regularHStepMatrix,Matrix.single_apply,Fin.ext_iff,Fin.val_mk]

theorem regularC1Cnot_entry_zero_unless {s : ℕ} (k : ℕ) (i j : Fin (s+s))
    (hbad : ¬(i.val=j.val+1 ∧ i.val%2=s%2)) :
    regularCnotStepMatrix s (2*k+2) (2*k+1) i j=0 := by
  by_cases hc : 2*k+2<s
  · rw [regularCnotStepMatrix_entry (2*k+2) (2*k+1) (by omega) (by omega) hc]
    have hx : ¬(s-1-(2*k+1)=i.val ∧ s-1-(2*k+2)=j.val) := by
      rintro ⟨hxi,hxj⟩
      apply hbad
      constructor <;> omega
    have hz : ¬(s+(2*k+2)=i.val ∧ s+(2*k+1)=j.val) := by
      rintro ⟨hzi,hzj⟩
      apply hbad
      constructor <;> omega
    simp only [if_neg hx,if_neg hz,add_zero]
  · have hv : ¬(0<2*k+1 ∧ 2*k+1<2*k+2 ∧ 2*k+2<s) := fun h => hc h.2.2
    simp only [regularCnotStepMatrix,dif_neg hv,Matrix.zero_apply]

theorem regularC1StepSum_eq_adjacent {s : ℕ} (hs : 0<s) :
    regularHStepMatrix hs+
        ∑ k ∈ Finset.range s, regularCnotStepMatrix s (2*k+2) (2*k+1) =
      regularAdjacentStepMatrix (s+s) s := by
  classical
  ext i j
  have hil:=i.isLt
  have hjl:=j.isLt
  simp only [Matrix.add_apply,Matrix.sum_apply,regularAdjacentStepMatrix]
  by_cases ha : i.val=j.val+1 ∧ i.val%2=s%2
  · rw [if_pos ha]
    have hstep:=ha.1
    have hpar:=ha.2
    have hip : 0 < i.val := by omega
    by_cases hmid : i.val=s
    · have hH : regularHStepMatrix hs i j=1 := by
        rw [regularHStepMatrix_entry]
        have hx : s=i.val ∧ s-1=j.val := by constructor <;> omega
        simp only [if_pos hx]
      rw [hH]
      have hzero : ∑ k ∈ Finset.range s,
          regularCnotStepMatrix s (2*k+2) (2*k+1) i j=0 := by
        apply Finset.sum_eq_zero
        intro k hk
        by_cases hc : 2*k+2<s
        · rw [regularCnotStepMatrix_entry (2*k+2) (2*k+1) (by omega) (by omega) hc]
          have hx : s-1-(2*k+1)≠i.val := by omega
          have hz : s+(2*k+2)≠i.val := by omega
          simp only [hx,hz,false_and,if_false,add_zero]
        · have hv : ¬(0<2*k+1 ∧ 2*k+1<2*k+2 ∧ 2*k+2<s) := fun h => hc h.2.2
          simp only [regularCnotStepMatrix,dif_neg hv,Matrix.zero_apply]
      rw [hzero,add_zero]
    · have hH : regularHStepMatrix hs i j=0 := by
        rw [regularHStepMatrix_entry]
        have hx : ¬(s=i.val ∧ s-1=j.val) := by omega
        simp only [if_neg hx]
      rw [hH,zero_add]
      by_cases hlo : i.val<s
      · let k : ℕ := (s-i.val)/2-1
        have hcontrol : 2*k+2=s-i.val := by dsimp [k]; omega
        have hc : 2*k+2<s := by omega
        have hk : k∈Finset.range s := Finset.mem_range.mpr (by omega)
        have hsum : ∑ l ∈ Finset.range s,
            regularCnotStepMatrix s (2*l+2) (2*l+1) i j =
            regularCnotStepMatrix s (2*k+2) (2*k+1) i j := by
          apply Finset.sum_eq_single k
          · intro l hl hlk
            by_cases hlc : 2*l+2<s
            · rw [regularCnotStepMatrix_entry (2*l+2) (2*l+1) (by omega) (by omega) hlc]
              have hx : s-1-(2*l+1)≠i.val := by
                intro h
                apply hlk
                omega
              have hz : s+(2*l+2)≠i.val := by omega
              simp only [hx,hz,false_and,if_false,add_zero]
            · have hv : ¬(0<2*l+1 ∧ 2*l+1<2*l+2 ∧ 2*l+2<s) := fun h => hlc h.2.2
              simp only [regularCnotStepMatrix,dif_neg hv,Matrix.zero_apply]
          · intro hkn
            exact (hkn hk).elim
        rw [hsum,regularCnotStepMatrix_entry (2*k+2) (2*k+1) (by omega) (by omega) hc]
        have hx : s-1-(2*k+1)=i.val ∧ s-1-(2*k+2)=j.val := by constructor <;> omega
        have hz : s+(2*k+2)≠i.val := by omega
        simp only [if_pos hx,hz,false_and,if_false,add_zero]
      · let k : ℕ := (i.val-s)/2-1
        have hhigh : s < i.val := by omega
        have hcontrol : 2*k+2=i.val-s := by dsimp [k]; omega
        have hc : 2*k+2<s := by omega
        have hk : k∈Finset.range s := Finset.mem_range.mpr (by omega)
        have hsum : ∑ l ∈ Finset.range s,
            regularCnotStepMatrix s (2*l+2) (2*l+1) i j =
            regularCnotStepMatrix s (2*k+2) (2*k+1) i j := by
          apply Finset.sum_eq_single k
          · intro l hl hlk
            by_cases hlc : 2*l+2<s
            · rw [regularCnotStepMatrix_entry (2*l+2) (2*l+1) (by omega) (by omega) hlc]
              have hx : s-1-(2*l+1)≠i.val := by omega
              have hz : s+(2*l+2)≠i.val := by
                intro h
                apply hlk
                omega
              simp only [hx,hz,false_and,if_false,add_zero]
            · have hv : ¬(0<2*l+1 ∧ 2*l+1<2*l+2 ∧ 2*l+2<s) := fun h => hlc h.2.2
              simp only [regularCnotStepMatrix,dif_neg hv,Matrix.zero_apply]
          · intro hkn
            exact (hkn hk).elim
        rw [hsum,regularCnotStepMatrix_entry (2*k+2) (2*k+1) (by omega) (by omega) hc]
        have hx : s-1-(2*k+1)≠i.val := by omega
        have hz : s+(2*k+2)=i.val ∧ s+(2*k+1)=j.val := by constructor <;> omega
        simp only [hx,false_and,if_false,if_pos hz,zero_add]
  · rw [if_neg ha]
    have hH : regularHStepMatrix hs i j=0 := by
      rw [regularHStepMatrix_entry]
      have hx : ¬(s=i.val ∧ s-1=j.val) := by
        rintro ⟨hi,hj⟩
        apply ha
        constructor <;> omega
      simp only [if_neg hx]
    rw [hH,zero_add]
    apply Finset.sum_eq_zero
    intro k hk
    exact regularC1Cnot_entry_zero_unless k i j ha

theorem layerC1Linear_ordered_matrix {s : ℕ} (hs : 0<s) (p : PauliLabel s) :
    regularOrderedCoordinates hs (layerC1Linear s p) =
      (1+regularAdjacentStepMatrix (s+s) s) *ᵥ regularOrderedCoordinates hs p := by
  let Q:=physicalLayerLabel (List.range s)
    (fun k => cnotGateLabel s (2*k+2) (2*k+1)) p
  have hlabel : layerC1Linear s p=hadamardLabel (⟨0,hs⟩ : Fin s) Q := by
    simp only [layerC1Linear_apply,layerC1Label,hadamardGateLabel,dif_pos hs,
      Function.comp_apply,Q]
  have hQx : Q.1 (⟨0,hs⟩ : Fin s)=p.1 ⟨0,hs⟩ := by
    exact physical_cnot_layer_fst_fixed (List.range s) (fun k => 2*k+2)
      (fun k => 2*k+1) p (⟨0,hs⟩ : Fin s) (fun k hk => by simp only [Fin.val_mk]; omega)
  have hQz : Q.2 (⟨0,hs⟩ : Fin s)=p.2 ⟨0,hs⟩ := by
    exact physical_cnot_layer_snd_fixed (List.range s) (fun k => 2*k+2)
      (fun k => 2*k+1) p (⟨0,hs⟩ : Fin s) (fun k hk => by simp only [Fin.val_mk]; omega)
  have hcenter : regularOrderedCoordinates hs Q (⟨s-1,by omega⟩ : Fin (s+s))=
      regularOrderedCoordinates hs p (⟨s-1,by omega⟩ : Fin (s+s)) := by
    simp only [regularOrderedCoordinates_center,hQx,hQz]
  have hlist:=regular_cnot_layer_ordered_matrix hs s (fun k => 2*k+2)
    (fun k => 2*k+1) p (fun k hk => by omega) (fun k hk => by omega)
    (fun k hk l hl => by omega)
  change regularOrderedCoordinates hs Q = _ at hlist
  rw [hlabel,regularOrderedCoordinates_H0,hcenter,hlist]
  calc
    (1+∑ k ∈ Finset.range s, regularCnotStepMatrix s (2*k+2) (2*k+1)) *ᵥ
        regularOrderedCoordinates hs p+
        Pi.single (⟨s,by omega⟩ : Fin (s+s))
          (regularOrderedCoordinates hs p (⟨s-1,by omega⟩ : Fin (s+s))) =
      (1+(regularHStepMatrix hs+
        ∑ k ∈ Finset.range s, regularCnotStepMatrix s (2*k+2) (2*k+1))) *ᵥ
          regularOrderedCoordinates hs p := by
      simp only [Matrix.add_mulVec,Matrix.one_mulVec,regularHStepMatrix,
        regular_matrix_single_mulVec]
      abel
    _ = (1+regularAdjacentStepMatrix (s+s) s) *ᵥ regularOrderedCoordinates hs p := by
      rw [regularC1StepSum_eq_adjacent hs]

def regularCZStepMatrix {s : ℕ} (hs2 : 1<s) :
    Matrix (Fin (s+s)) (Fin (s+s)) (ZMod 2) :=
  Matrix.single (⟨s-1,by omega⟩ : Fin (s+s)) (⟨s-2,by omega⟩ : Fin (s+s)) 1+
    Matrix.single (⟨s+1,by omega⟩ : Fin (s+s)) (⟨s,by omega⟩ : Fin (s+s)) 1

theorem regularCZStepMatrix_entry {s : ℕ} (hs2 : 1<s) (i j : Fin (s+s)) :
    regularCZStepMatrix hs2 i j =
      (if s-1=i.val ∧ s-2=j.val then 1 else 0)+
      (if s+1=i.val ∧ s=j.val then 1 else 0) := by
  simp only [regularCZStepMatrix,Matrix.add_apply,Matrix.single_apply,
    Fin.ext_iff,Fin.val_mk]

theorem regularC2Cnot_entry_zero_unless {s : ℕ} (k : ℕ) (i j : Fin (s+s))
    (hbad : ¬(i.val=j.val+1 ∧ i.val%2=(s+1)%2)) :
    regularCnotStepMatrix s (2*k+3) (2*k+2) i j=0 := by
  by_cases hc : 2*k+3<s
  · rw [regularCnotStepMatrix_entry (2*k+3) (2*k+2) (by omega) (by omega) hc]
    have hx : ¬(s-1-(2*k+2)=i.val ∧ s-1-(2*k+3)=j.val) := by
      rintro ⟨hxi,hxj⟩
      apply hbad
      constructor <;> omega
    have hz : ¬(s+(2*k+3)=i.val ∧ s+(2*k+2)=j.val) := by
      rintro ⟨hzi,hzj⟩
      apply hbad
      constructor <;> omega
    simp only [if_neg hx,if_neg hz,add_zero]
  · have hv : ¬(0<2*k+2 ∧ 2*k+2<2*k+3 ∧ 2*k+3<s) := fun h => hc h.2.2
    simp only [regularCnotStepMatrix,dif_neg hv,Matrix.zero_apply]

theorem regularC2Cnot_entry_zero_at_center {s : ℕ} (k : ℕ)
    (i j : Fin (s+s)) (hi : i.val=s-1 ∨ i.val=s+1) :
    regularCnotStepMatrix s (2*k+3) (2*k+2) i j=0 := by
  by_cases hc : 2*k+3<s
  · rw [regularCnotStepMatrix_entry (2*k+3) (2*k+2) (by omega) (by omega) hc]
    have hx : s-1-(2*k+2)≠i.val := by rcases hi with hi | hi <;> omega
    have hz : s+(2*k+3)≠i.val := by rcases hi with hi | hi <;> omega
    simp only [hx,hz,false_and,if_false,add_zero]
  · have hv : ¬(0<2*k+2 ∧ 2*k+2<2*k+3 ∧ 2*k+3<s) := fun h => hc h.2.2
    simp only [regularCnotStepMatrix,dif_neg hv,Matrix.zero_apply]

theorem regularC2StepSum_eq_adjacent {s : ℕ} (hs2 : 1<s) :
    regularCZStepMatrix hs2+
        ∑ k ∈ Finset.range s, regularCnotStepMatrix s (2*k+3) (2*k+2) =
      regularAdjacentStepMatrix (s+s) (s+1) := by
  classical
  ext i j
  have hil:=i.isLt
  have hjl:=j.isLt
  simp only [Matrix.add_apply,Matrix.sum_apply,regularAdjacentStepMatrix]
  by_cases ha : i.val=j.val+1 ∧ i.val%2=(s+1)%2
  · rw [if_pos ha]
    have hstep:=ha.1
    have hpar:=ha.2
    have hip : 0 < i.val := by omega
    by_cases hlowmid : i.val=s-1
    · have hCZ : regularCZStepMatrix hs2 i j=1 := by
        rw [regularCZStepMatrix_entry]
        have hx : s-1=i.val ∧ s-2=j.val := by constructor <;> omega
        have hz : s+1≠i.val := by omega
        simp only [if_pos hx,hz,false_and,if_false,add_zero]
      rw [hCZ]
      have hzero : ∑ k ∈ Finset.range s,
          regularCnotStepMatrix s (2*k+3) (2*k+2) i j=0 := by
        apply Finset.sum_eq_zero
        intro k hk
        exact regularC2Cnot_entry_zero_at_center k i j (Or.inl hlowmid)
      rw [hzero,add_zero]
    · by_cases hhighmid : i.val=s+1
      · have hCZ : regularCZStepMatrix hs2 i j=1 := by
          rw [regularCZStepMatrix_entry]
          have hx : s-1≠i.val := by omega
          have hz : s+1=i.val ∧ s=j.val := by constructor <;> omega
          simp only [hx,false_and,if_false,if_pos hz,zero_add]
        rw [hCZ]
        have hzero : ∑ k ∈ Finset.range s,
            regularCnotStepMatrix s (2*k+3) (2*k+2) i j=0 := by
          apply Finset.sum_eq_zero
          intro k hk
          exact regularC2Cnot_entry_zero_at_center k i j (Or.inr hhighmid)
        rw [hzero,add_zero]
      · have hCZ : regularCZStepMatrix hs2 i j=0 := by
          rw [regularCZStepMatrix_entry]
          have hx : s-1≠i.val := Ne.symm hlowmid
          have hz : s+1≠i.val := Ne.symm hhighmid
          simp only [hx,hz,false_and,if_false,add_zero]
        rw [hCZ,zero_add]
        by_cases hlo : i.val<s
        · let k : ℕ := (s-i.val-3)/2
          have hcontrol : 2*k+3=s-i.val := by dsimp [k]; omega
          have hc : 2*k+3<s := by omega
          have hk : k∈Finset.range s := Finset.mem_range.mpr (by omega)
          have hsum : ∑ l ∈ Finset.range s,
              regularCnotStepMatrix s (2*l+3) (2*l+2) i j =
              regularCnotStepMatrix s (2*k+3) (2*k+2) i j := by
            apply Finset.sum_eq_single k
            · intro l hl hlk
              by_cases hlc : 2*l+3<s
              · rw [regularCnotStepMatrix_entry (2*l+3) (2*l+2) (by omega) (by omega) hlc]
                have hx : s-1-(2*l+2)≠i.val := by intro h; apply hlk; omega
                have hz : s+(2*l+3)≠i.val := by omega
                simp only [hx,hz,false_and,if_false,add_zero]
              · have hv : ¬(0<2*l+2 ∧ 2*l+2<2*l+3 ∧ 2*l+3<s) := fun h => hlc h.2.2
                simp only [regularCnotStepMatrix,dif_neg hv,Matrix.zero_apply]
            · intro hkn
              exact (hkn hk).elim
          rw [hsum,regularCnotStepMatrix_entry (2*k+3) (2*k+2) (by omega) (by omega) hc]
          have hx : s-1-(2*k+2)=i.val ∧ s-1-(2*k+3)=j.val := by constructor <;> omega
          have hz : s+(2*k+3)≠i.val := by omega
          simp only [if_pos hx,hz,false_and,if_false,add_zero]
        · let k : ℕ := (i.val-s-3)/2
          have hhigh : s < i.val := by omega
          have hcontrol : 2*k+3=i.val-s := by dsimp [k]; omega
          have hc : 2*k+3<s := by omega
          have hk : k∈Finset.range s := Finset.mem_range.mpr (by omega)
          have hsum : ∑ l ∈ Finset.range s,
              regularCnotStepMatrix s (2*l+3) (2*l+2) i j =
              regularCnotStepMatrix s (2*k+3) (2*k+2) i j := by
            apply Finset.sum_eq_single k
            · intro l hl hlk
              by_cases hlc : 2*l+3<s
              · rw [regularCnotStepMatrix_entry (2*l+3) (2*l+2) (by omega) (by omega) hlc]
                have hx : s-1-(2*l+2)≠i.val := by omega
                have hz : s+(2*l+3)≠i.val := by intro h; apply hlk; omega
                simp only [hx,hz,false_and,if_false,add_zero]
              · have hv : ¬(0<2*l+2 ∧ 2*l+2<2*l+3 ∧ 2*l+3<s) := fun h => hlc h.2.2
                simp only [regularCnotStepMatrix,dif_neg hv,Matrix.zero_apply]
            · intro hkn
              exact (hkn hk).elim
          rw [hsum,regularCnotStepMatrix_entry (2*k+3) (2*k+2) (by omega) (by omega) hc]
          have hx : s-1-(2*k+2)≠i.val := by omega
          have hz : s+(2*k+3)=i.val ∧ s+(2*k+2)=j.val := by constructor <;> omega
          simp only [hx,false_and,if_false,if_pos hz,zero_add]
  · rw [if_neg ha]
    have hCZ : regularCZStepMatrix hs2 i j=0 := by
      rw [regularCZStepMatrix_entry]
      have hx : ¬(s-1=i.val ∧ s-2=j.val) := by
        rintro ⟨hi,hj⟩
        apply ha
        constructor <;> omega
      have hz : ¬(s+1=i.val ∧ s=j.val) := by
        rintro ⟨hi,hj⟩
        apply ha
        constructor <;> omega
      simp only [if_neg hx,if_neg hz,add_zero]
    rw [hCZ,zero_add]
    apply Finset.sum_eq_zero
    intro k hk
    exact regularC2Cnot_entry_zero_unless k i j ha

theorem layerC2Linear_one (p : PauliLabel 1) : layerC2Linear 1 p=p := by
  simp [layerC2Linear_apply,layerC2Label,czGateLabel,cnotGateLabel,
    physicalLayerLabel,List.range_succ]

theorem layerC2Linear_ordered_matrix_large {s : ℕ} (hs2 : 1<s) (p : PauliLabel s) :
    regularOrderedCoordinates (by omega : 0<s) (layerC2Linear s p) =
      (1+regularAdjacentStepMatrix (s+s) (s+1)) *ᵥ
        regularOrderedCoordinates (by omega : 0<s) p := by
  have hs : 0<s := by omega
  let Q:=physicalLayerLabel (List.range s)
    (fun k => cnotGateLabel s (2*k+3) (2*k+2)) p
  have hlabel : layerC2Linear s p=
      czLabel (⟨0,hs⟩ : Fin s) (⟨1,hs2⟩ : Fin s) Q := by
    simp only [layerC2Linear_apply,layerC2Label,czGateLabel,dif_pos hs,
      dif_pos hs2,Function.comp_apply,Q]
  have hQx0 : Q.1 (⟨0,hs⟩ : Fin s)=p.1 ⟨0,hs⟩ := by
    exact physical_cnot_layer_fst_fixed (List.range s) (fun k => 2*k+3)
      (fun k => 2*k+2) p (⟨0,hs⟩ : Fin s) (fun k hk => by simp only [Fin.val_mk]; omega)
  have hQx1 : Q.1 (⟨1,hs2⟩ : Fin s)=p.1 ⟨1,hs2⟩ := by
    exact physical_cnot_layer_fst_fixed (List.range s) (fun k => 2*k+3)
      (fun k => 2*k+2) p (⟨1,hs2⟩ : Fin s) (fun k hk => by simp only [Fin.val_mk]; omega)
  have hlist:=regular_cnot_layer_ordered_matrix hs s (fun k => 2*k+3)
    (fun k => 2*k+2) p (fun k hk => by omega) (fun k hk => by omega)
    (fun k hk l hl => by omega)
  change regularOrderedCoordinates hs Q = _ at hlist
  have hXe:=regularOrderedCoordinates_X_eval hs p (⟨1,hs2⟩ : Fin s)
    (by exact (show 0 < (1 : ℕ) by decide))
  have hindex : (⟨s-1-1,by omega⟩ : Fin (s+s))=(⟨s-2,by omega⟩ : Fin (s+s)) :=
    Fin.ext (by simp only [Fin.val_mk];omega)
  rw [hindex] at hXe
  rw [hlabel,regularOrderedCoordinates_CZ01,hQx0,hQx1,hlist]
  calc
    (1+∑ k ∈ Finset.range s, regularCnotStepMatrix s (2*k+3) (2*k+2)) *ᵥ
        regularOrderedCoordinates hs p+
        Pi.single (⟨s-1,by omega⟩ : Fin (s+s)) (p.1 ⟨1,hs2⟩)+
        Pi.single (⟨s+1,by omega⟩ : Fin (s+s)) (p.1 ⟨0,hs⟩) =
      (1+(regularCZStepMatrix hs2+
        ∑ k ∈ Finset.range s, regularCnotStepMatrix s (2*k+3) (2*k+2))) *ᵥ
          regularOrderedCoordinates hs p := by
      simp only [Matrix.add_mulVec,Matrix.one_mulVec,regularCZStepMatrix,
        regular_matrix_single_mulVec,hXe,regularOrderedCoordinates_pivot]
      abel
    _ = (1+regularAdjacentStepMatrix (s+s) (s+1)) *ᵥ regularOrderedCoordinates hs p := by
      rw [regularC2StepSum_eq_adjacent hs2]

theorem layerC2Linear_ordered_matrix {s : ℕ} (hs : 0<s) (p : PauliLabel s) :
    regularOrderedCoordinates hs (layerC2Linear s p) =
      (1+regularAdjacentStepMatrix (s+s) (s+1)) *ᵥ regularOrderedCoordinates hs p := by
  by_cases hs2 : 1<s
  · exact layerC2Linear_ordered_matrix_large hs2 p
  · have hs1 : s=1 := by omega
    subst s
    have hA : regularAdjacentStepMatrix (1+1) (1+1)=0 := by
      ext i j
      have hil:=i.isLt
      have hjl:=j.isLt
      have hbad : ¬(i.val=j.val+1 ∧ i.val%2=(1+1)%2) := by omega
      simp only [regularAdjacentStepMatrix,if_neg hbad,Matrix.zero_apply]
    rw [layerC2Linear_one,hA,add_zero,Matrix.one_mulVec]

def regularNilpotentMatrix (s : ℕ) : Matrix (Fin (s+s)) (Fin (s+s)) (ZMod 2) :=
  regularAdjacentStepMatrix (s+s) s+regularAdjacentStepMatrix (s+s) (s+1)+
    regularAdjacentStepMatrix (s+s) (s+1)*regularAdjacentStepMatrix (s+s) s

theorem regular_adjacent_product_eq_one_add (s : ℕ) :
    (1+regularAdjacentStepMatrix (s+s) (s+1))*
      (1+regularAdjacentStepMatrix (s+s) s)=1+regularNilpotentMatrix s := by
  simp only [regularNilpotentMatrix,mul_add,add_mul,one_mul,mul_one]
  abel

theorem regularAdjacentStepMatrix_triangular (d parity : ℕ) :
    ∀ i j : Fin d, i.val≤j.val → regularAdjacentStepMatrix d parity i j=0 := by
  intro i j hij
  have hbad : ¬(i.val=j.val+1 ∧ i.val%2=parity%2) := by omega
  simp only [regularAdjacentStepMatrix,if_neg hbad]

theorem regular_adjacent_product_entry_zero (s : ℕ) (i j : Fin (s+s))
    (hij : i.val≤j.val+1) :
    (regularAdjacentStepMatrix (s+s) (s+1)*regularAdjacentStepMatrix (s+s) s) i j=0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hkj : k.val≤j.val
  · rw [regularAdjacentStepMatrix_triangular _ _ k j hkj,mul_zero]
  · rw [regularAdjacentStepMatrix_triangular _ _ i k (by omega),zero_mul]

theorem regularNilpotentMatrix_triangular (s : ℕ) :
    ∀ i j : Fin (s+s), i.val≤j.val → regularNilpotentMatrix s i j=0 := by
  intro i j hij
  simp only [regularNilpotentMatrix,Matrix.add_apply]
  rw [regularAdjacentStepMatrix_triangular _ _ i j hij,
    regularAdjacentStepMatrix_triangular _ _ i j hij,
    regular_adjacent_product_entry_zero s i j (by omega),zero_add]
  exact zero_add _

theorem regularNilpotentMatrix_adjacent (s : ℕ) :
    ∀ i j : Fin (s+s), i.val=j.val+1 → regularNilpotentMatrix s i j=1 := by
  intro i j hij
  have hA : regularAdjacentStepMatrix (s+s) s i j=
      if i.val%2=s%2 then 1 else 0 := by
    simp only [regularAdjacentStepMatrix,hij,true_and]
  have hB : regularAdjacentStepMatrix (s+s) (s+1) i j=
      if i.val%2=(s+1)%2 then 1 else 0 := by
    simp only [regularAdjacentStepMatrix,hij,true_and]
  simp only [regularNilpotentMatrix,Matrix.add_apply]
  rw [regular_adjacent_product_entry_zero s i j (by omega),add_zero,hA,hB]
  by_cases hp : i.val%2=s%2
  · have hq : i.val%2≠(s+1)%2 := by omega
    rw [if_pos hp,if_neg hq,add_zero]
  · have hq : i.val%2=(s+1)%2 := by omega
    rw [if_neg hp,if_pos hq,zero_add]

theorem regularNilpotentMatrix_nilpotency {s : ℕ} (hs : 0<s) :
    regularNilpotentMatrix s ^ (s+s)=0 ∧ regularNilpotentMatrix s ^ (s+s-1)≠0 := by
  exact ⟨RegularChain.pow_dimension_eq_zero _ (regularNilpotentMatrix_triangular s),
    RegularChain.pow_dimension_sub_one_ne_zero (by omega) _
      (regularNilpotentMatrix_triangular s) (regularNilpotentMatrix_adjacent s)⟩

theorem regularCliffordLinear_ordered_matrix {s : ℕ} (hs : 0<s) (p : PauliLabel s) :
    regularOrderedCoordinates hs (regularCliffordLinear s p) =
      (1+regularNilpotentMatrix s) *ᵥ regularOrderedCoordinates hs p := by
  change regularOrderedCoordinates hs (layerC2Linear s (layerC1Linear s p)) = _
  rw [layerC2Linear_ordered_matrix hs,layerC1Linear_ordered_matrix hs,
    Matrix.mulVec_mulVec,regular_adjacent_product_eq_one_add]

def regularNilpotentLinear (s : ℕ) : Module.End (ZMod 2) (PauliLabel s) :=
  regularCliffordLinear s-1

theorem regularCliffordLinear_ordered_pow {s : ℕ} (hs : 0<s)
    (k : ℕ) (p : PauliLabel s) :
    regularOrderedCoordinates hs ((regularCliffordLinear s ^ k) p) =
      (1+regularNilpotentMatrix s)^k *ᵥ regularOrderedCoordinates hs p := by
  induction k with
  | zero => simp only [pow_zero,Module.End.one_apply,Matrix.one_mulVec]
  | succ k ih =>
    simp only [pow_succ',Module.End.mul_apply]
    rw [regularCliffordLinear_ordered_matrix hs,ih,Matrix.mulVec_mulVec]

theorem regularNilpotentLinear_ordered_matrix {s : ℕ} (hs : 0<s)
    (p : PauliLabel s) :
    regularOrderedCoordinates hs (regularNilpotentLinear s p) =
      regularNilpotentMatrix s *ᵥ regularOrderedCoordinates hs p := by
  change (regularOrderedLinearEquiv hs) (regularCliffordLinear s p-p) = _
  rw [map_sub]
  change regularOrderedCoordinates hs (regularCliffordLinear s p)-
    regularOrderedCoordinates hs p = _
  rw [regularCliffordLinear_ordered_matrix hs,Matrix.add_mulVec,Matrix.one_mulVec]
  abel

theorem regularNilpotentLinear_ordered_pow {s : ℕ} (hs : 0<s)
    (k : ℕ) (p : PauliLabel s) :
    regularOrderedCoordinates hs ((regularNilpotentLinear s ^ k) p) =
      regularNilpotentMatrix s ^ k *ᵥ regularOrderedCoordinates hs p := by
  induction k with
  | zero => simp only [pow_zero,Module.End.one_apply,Matrix.one_mulVec]
  | succ k ih =>
    simp only [pow_succ',Module.End.mul_apply]
    rw [regularNilpotentLinear_ordered_matrix hs,ih,Matrix.mulVec_mulVec]

theorem regularCliffordLinear_pow_eq_one_iff {s : ℕ} (hs : 0<s) (k : ℕ) :
    regularCliffordLinear s ^ k=1 ↔ (1+regularNilpotentMatrix s)^k=1 := by
  constructor
  · intro hF
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    obtain ⟨p,rfl⟩ := (regularOrderedLinearEquiv hs).surjective v
    change (1+regularNilpotentMatrix s)^k *ᵥ regularOrderedCoordinates hs p =
      1 *ᵥ regularOrderedCoordinates hs p
    rw [← regularCliffordLinear_ordered_pow hs k p,hF,
      Module.End.one_apply,Matrix.one_mulVec]
  · intro hM
    apply LinearMap.ext
    intro p
    apply (regularOrderedLinearEquiv hs).injective
    change regularOrderedCoordinates hs ((regularCliffordLinear s ^ k) p) =
      regularOrderedCoordinates hs p
    rw [regularCliffordLinear_ordered_pow hs,hM,Matrix.one_mulVec]

theorem regularNilpotentLinear_pow_eq_zero_iff {s : ℕ} (hs : 0<s) (k : ℕ) :
    regularNilpotentLinear s ^ k=0 ↔ regularNilpotentMatrix s ^ k=0 := by
  constructor
  · intro hF
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    obtain ⟨p,rfl⟩ := (regularOrderedLinearEquiv hs).surjective v
    change regularNilpotentMatrix s ^ k *ᵥ regularOrderedCoordinates hs p =
      0 *ᵥ regularOrderedCoordinates hs p
    rw [← regularNilpotentLinear_ordered_pow hs k p,hF,
      LinearMap.zero_apply,Matrix.zero_mulVec]
    exact (regularOrderedLinearEquiv hs).map_zero
  · intro hM
    apply LinearMap.ext
    intro p
    apply (regularOrderedLinearEquiv hs).injective
    change regularOrderedCoordinates hs ((regularNilpotentLinear s ^ k) p) =
      (regularOrderedLinearEquiv hs) 0
    rw [regularNilpotentLinear_ordered_pow hs,hM,Matrix.zero_mulVec,map_zero]

theorem regularNilpotentLinear_nilpotency {s : ℕ} (hs : 0<s) :
    regularNilpotentLinear s ^ (s+s)=0 ∧
      regularNilpotentLinear s ^ (s+s-1)≠0 := by
  obtain ⟨hz,hn⟩ := regularNilpotentMatrix_nilpotency hs
  exact ⟨(regularNilpotentLinear_pow_eq_zero_iff hs _).mpr hz,
    fun h => hn ((regularNilpotentLinear_pow_eq_zero_iff hs _).mp h)⟩

theorem regularCliffordLinear_pow_two_pow_eq_one {s : ℕ} (hs : 0<s)
    (h : ℕ) (hupper : s+s≤2^h) :
    regularCliffordLinear s ^ (2^h)=1 := by
  letI : Nonempty (Fin (s+s)) := ⟨⟨0,by omega⟩⟩
  apply (regularCliffordLinear_pow_eq_one_iff hs _).mpr
  exact BinaryUnipotent.one_add_pow_two_pow_eq_one_of_nilpotent_bound
    (regularNilpotentMatrix s) (s+s) h
    (regularNilpotentMatrix_nilpotency hs).1 hupper

theorem regularCliffordLinear_pow_two_pow_ne_one {s : ℕ} (hs : 0<s)
    (h : ℕ) (hlower : 2^h<s+s) :
    regularCliffordLinear s ^ (2^h)≠1 := by
  letI : Nonempty (Fin (s+s)) := ⟨⟨0,by omega⟩⟩
  have hN := BinaryUnipotent.pow_ne_zero_of_chain_endpoint
    (regularNilpotentMatrix s) (s+s) (2^h)
    (regularNilpotentMatrix_nilpotency hs).2 hlower
  have hM := BinaryUnipotent.one_add_pow_two_pow_ne_one
    (regularNilpotentMatrix s) h hN
  exact fun hF => hM ((regularCliffordLinear_pow_eq_one_iff hs _).mp hF)

theorem regularCliffordLinear_orderOf {s : ℕ} (hs : 0<s)
    (h : ℕ) (hlower : 2^h<s+s) (hupper : s+s≤2^(h+1)) :
    orderOf (regularCliffordLinear s)=2^(h+1) := by
  apply orderOf_eq_prime_pow (p:=2) (n:=h)
  · exact regularCliffordLinear_pow_two_pow_ne_one hs h hlower
  · exact regularCliffordLinear_pow_two_pow_eq_one hs (h+1) hupper

theorem regularNilpotentLinear_ker_le_range_power {s : ℕ} (hs : 0<s)
    (a : ℕ) (ha : a<s+s) :
    LinearMap.ker (regularNilpotentLinear s) ≤
      LinearMap.range (regularNilpotentLinear s ^ a) := by
  intro p hp
  have hnp : regularNilpotentLinear s p=0 := LinearMap.mem_ker.mp hp
  have hmatrix : regularNilpotentMatrix s *ᵥ regularOrderedCoordinates hs p=0 := by
    rw [← regularNilpotentLinear_ordered_matrix hs p,hnp]
    exact (regularOrderedLinearEquiv hs).map_zero
  have hmem : regularOrderedCoordinates hs p ∈
      LinearMap.ker (Matrix.mulVecLin (regularNilpotentMatrix s)) :=
    LinearMap.mem_ker.mpr hmatrix
  obtain ⟨v,hv⟩ := regular_triangular_ker_le_range_power (by omega)
    (regularNilpotentMatrix s) (regularNilpotentMatrix_triangular s)
    (regularNilpotentMatrix_adjacent s) a ha hmem
  refine ⟨(regularOrderedLinearEquiv hs).symm v,?_⟩
  apply (regularOrderedLinearEquiv hs).injective
  change regularOrderedCoordinates hs
      ((regularNilpotentLinear s ^ a) ((regularOrderedLinearEquiv hs).symm v)) =
    regularOrderedCoordinates hs p
  rw [regularNilpotentLinear_ordered_pow hs]
  change regularNilpotentMatrix s ^ a *ᵥ
      ((regularOrderedLinearEquiv hs) ((regularOrderedLinearEquiv hs).symm v)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact hv

theorem regularNilpotentLinear_fixed_label_form {s : ℕ} (hs2 : 1<s)
    (p : PauliLabel s) (hp : regularCliffordLinear s p=p) :
    ∃ a : ZMod 2, p=(0,Pi.single (⟨s-1,by omega⟩ : Fin s) a) := by
  have hs : 0<s := by omega
  let last : Fin (s+s) := ⟨s+s-1,by omega⟩
  let wire : Fin s := ⟨s-1,by omega⟩
  let a : ZMod 2 := regularOrderedCoordinates hs p last
  have hnp : regularNilpotentLinear s p=0 := by
    simp only [regularNilpotentLinear,LinearMap.sub_apply,Module.End.one_apply,hp,sub_self]
  have hmatrix : regularNilpotentMatrix s *ᵥ regularOrderedCoordinates hs p=0 := by
    rw [← regularNilpotentLinear_ordered_matrix hs p,hnp]
    exact (regularOrderedLinearEquiv hs).map_zero
  have hc := regular_triangular_kernel_last (by omega)
    (regularNilpotentMatrix s) (regularNilpotentMatrix_triangular s)
    (regularNilpotentMatrix_adjacent s) (regularOrderedCoordinates hs p) hmatrix
  change regularOrderedCoordinates hs p=a • Pi.single last 1 at hc
  refine ⟨a,?_⟩
  apply (regularOrderedLinearEquiv hs).injective
  change regularOrderedCoordinates hs p=regularOrderedCoordinates hs (0,Pi.single wire a)
  rw [regularOrderedCoordinates_Z_single hs wire (by dsimp [wire];omega)]
  have hl : (⟨s+wire.val,by have hw:=wire.isLt;omega⟩ : Fin (s+s))=last := by
    apply Fin.ext
    dsimp [wire,last]
    omega
  rw [hl,hc]
  funext i
  by_cases hi : i=last
  · subst i
    simp [Pi.smul_apply,smul_eq_mul]
  · simp [Pi.smul_apply,smul_eq_mul,Pi.single_apply,hi,Ne.symm hi]

theorem regularClifford_fixed_label_Hermitian {s : ℕ} (hs2 : 1<s)
    (p : PauliLabel s) (hp : regularCliffordLinear s p=p) : dot p.2 p.1=0 := by
  obtain ⟨a,ha⟩ := regularNilpotentLinear_fixed_label_form hs2 p hp
  rw [ha]
  exact dot_zero_right _

theorem regularClifford_pow_two_pow_signed_endpoint_large {s : ℕ} (hs2 : 1<s)
    (hfaith : ∀ (a : ℂ) (p r : PauliLabel s),
      orderedPauli p.1 p.2=a • orderedPauli r.1 r.2 → p=r)
    (h : ℕ) (hupper : s+s≤2^h) (a : ℕ) (ha : a<s+s) :
    ∃ (e : ZMod 2) (p : PauliLabel s),
      regularClifford s ^ (2^h)=bitSign e • orderedPauli p.1 p.2 ∧
      dot p.2 p.1=0 ∧ p ∈ LinearMap.range (regularNilpotentLinear s ^ a) ∧
      regularClifford s ^ (2*(2^h))=1 := by
  have hs : 0<s := by omega
  obtain ⟨e,p,he,hp⟩ := regularClifford_pow_sign_fixed_of_linear_identity hfaith
    (regularCliffordLinear_pow_two_pow_eq_one hs h hupper)
  have hHerm := regularClifford_fixed_label_Hermitian hs2 p hp
  have hker : p ∈ LinearMap.ker (regularNilpotentLinear s) := by
    apply LinearMap.mem_ker.mpr
    simp only [regularNilpotentLinear,LinearMap.sub_apply,Module.End.one_apply,hp,sub_self]
  have hrange := regularNilpotentLinear_ker_le_range_power hs a ha hker
  have hsquare : (regularClifford s ^ (2^h))^2=1 :=
    physical_real_projectivePauli_square
      (unitaryMatrix_pow (regularClifford_unitary s) (2^h))
      (physical_real_pow (regularClifford_real s) (2^h))
      (bitSign e) p.1 p.2 he hHerm
  refine ⟨e,p,he,hHerm,hrange,?_⟩
  rw [Nat.mul_comm 2 (2^h),pow_mul]
  exact hsquare

theorem regularClifford_one_pow_two_pow (h : ℕ) (hh : 1≤h) :
    regularClifford 1 ^ (2^h)=1 := by
  cases h with
  | zero => omega
  | succ h =>
    rw [Nat.pow_succ,Nat.mul_comm (2^h) 2,pow_mul,
      regularClifford_one_square,one_pow]

theorem regularClifford_pow_two_pow_signed_endpoint {s : ℕ} (hs : 0<s)
    (hfaith : ∀ (a : ℂ) (p r : PauliLabel s),
      orderedPauli p.1 p.2=a • orderedPauli r.1 r.2 → p=r)
    (h : ℕ) (hh : 1≤h) (hupper : s+s≤2^h) (a : ℕ) (ha : a<s+s) :
    ∃ (e : ZMod 2) (p : PauliLabel s),
      regularClifford s ^ (2^h)=bitSign e • orderedPauli p.1 p.2 ∧
      dot p.2 p.1=0 ∧ p ∈ LinearMap.range (regularNilpotentLinear s ^ a) ∧
      regularClifford s ^ (2*(2^h))=1 := by
  by_cases hs1 : s=1
  · subst s
    have hq := regularClifford_one_pow_two_pow h hh
    refine ⟨0,0,?_,dot_zero_right _,Submodule.zero_mem _,?_⟩
    · change regularClifford 1 ^ (2^h)=bitSign 0 • orderedPauli (0 : BitString 1) 0
      simpa only [bitSign_zero,one_smul,orderedPauli_zero] using hq
    · rw [Nat.mul_comm 2 (2^h),pow_mul,hq,one_pow]
  · exact regularClifford_pow_two_pow_signed_endpoint_large (by omega)
      hfaith h hupper a ha

theorem physical_projective_of_smul_actual {n : ℕ} {U : QuantumMatrix n}
    (b : ℂ) (h : actualPauli (b • U)) :
    ∃ (a : ℂ) (x z : BitString n), U=a • orderedPauli x z := by
  obtain ⟨a,x,z,ha,he⟩ := h
  have hane : a≠0 := by
    rcases ha with rfl | rfl | rfl | rfl <;> norm_num
  have hbne : b≠0 := by
    intro hb
    have hv := congrArg (fun M : QuantumMatrix n => M x 0) he
    simp [hb,orderedPauli_zero_column] at hv
    exact hane hv.symm
  refine ⟨b⁻¹*a,x,z,?_⟩
  have hc := congrArg (fun M : QuantumMatrix n => b⁻¹ • M) he
  simpa only [smul_smul,inv_mul_cancel₀ hbne,one_smul] using hc

theorem regularClifford_early_pow_not_projectivePauli {s : ℕ} (hs : 0<s)
    (hfaith : ∀ (a : ℂ) (p r : PauliLabel s),
      orderedPauli p.1 p.2=a • orderedPauli r.1 r.2 → p=r)
    (a : ℕ) (ha : 2^a<s+s) (b : ℂ) :
    ¬actualPauli (b • (regularClifford s ^ (2^a))) := by
  intro hP
  obtain ⟨c,x,z,hc⟩ := physical_projective_of_smul_actual b hP
  exact regularClifford_pow_not_projective hfaith
    (regularCliffordLinear_pow_two_pow_ne_one hs a ha) c x z hc

theorem regularClifford_actualPeriod {s : ℕ} (hs : 0<s)
    (hfaith : ∀ (a : ℂ) (p r : PauliLabel s),
      orderedPauli p.1 p.2=a • orderedPauli r.1 r.2 → p=r)
    (h : ℕ) (hh : 1≤h) (hlower : 2^(h-1)<s+s) (hupper : s+s≤2^h) :
    actualPauliPeriod h (regularClifford s) ∧
      ∀ a<h, ∀ b : ℂ, ¬actualPauli (b • (regularClifford s ^ (2^a))) := by
  obtain ⟨e,p,he⟩ := regularClifford_pow_sign_of_linear_identity
    (regularCliffordLinear_pow_two_pow_eq_one hs h hupper)
  have hearly : ∀ a<h, ∀ b : ℂ,
      ¬actualPauli (b • (regularClifford s ^ (2^a))) := by
    intro a ha b
    apply regularClifford_early_pow_not_projectivePauli hs hfaith a _ b
    have hle : a≤h-1 := by omega
    exact lt_of_le_of_lt (by gcongr) hlower
  refine ⟨⟨⟨bitSign e,p.1,p.2,bitSign_phase e,he⟩,?_⟩,hearly⟩
  intro a ha
  simpa only [one_smul] using hearly a ha 1

theorem regularNilpotentLinear_range_ordered_iff {s : ℕ} (hs : 0<s)
    (a : ℕ) (p : PauliLabel s) :
    p ∈ LinearMap.range (regularNilpotentLinear s ^ a) ↔
      regularOrderedCoordinates hs p ∈
        LinearMap.range (Matrix.mulVecLin (regularNilpotentMatrix s ^ a)) := by
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨regularOrderedCoordinates hs q,?_⟩
    change regularNilpotentMatrix s ^ a *ᵥ regularOrderedCoordinates hs q =
      regularOrderedCoordinates hs p
    rw [← regularNilpotentLinear_ordered_pow hs a q,hq]
  · rintro ⟨v,hv⟩
    refine ⟨(regularOrderedLinearEquiv hs).symm v,?_⟩
    apply (regularOrderedLinearEquiv hs).injective
    change regularOrderedCoordinates hs
        ((regularNilpotentLinear s ^ a) ((regularOrderedLinearEquiv hs).symm v)) =
      regularOrderedCoordinates hs p
    rw [regularNilpotentLinear_ordered_pow hs]
    change regularNilpotentMatrix s ^ a *ᵥ
      ((regularOrderedLinearEquiv hs) ((regularOrderedLinearEquiv hs).symm v)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hv

theorem layerC1Linear_ordered_head_fixed {s : ℕ} (hs : 0<s)
    (p : PauliLabel s) :
    regularOrderedCoordinates hs (layerC1Linear s p) (⟨0,by omega⟩ : Fin (s+s)) =
      regularOrderedCoordinates hs p (⟨0,by omega⟩ : Fin (s+s)) := by
  let first : Fin (s+s) := ⟨0,by omega⟩
  let v : BitString (s+s) := regularOrderedCoordinates hs p
  have hz : (regularAdjacentStepMatrix (s+s) s *ᵥ v) first=0 := by
    change (∑ j : Fin (s+s), regularAdjacentStepMatrix (s+s) s first j*v j)=0
    apply Finset.sum_eq_zero
    intro j hj
    rw [regularAdjacentStepMatrix_triangular _ _ first j (by dsimp [first];omega),zero_mul]
  rw [layerC1Linear_ordered_matrix hs,Matrix.add_mulVec,Matrix.one_mulVec]
  change (v+regularAdjacentStepMatrix (s+s) s *ᵥ v) first=v first
  rw [Pi.add_apply,hz,add_zero]

theorem layerC1Linear_difference_mem_range {s : ℕ} (hs : 0<s)
    (p : PauliLabel s) :
    layerC1Linear s p-p ∈ LinearMap.range (regularNilpotentLinear s) := by
  have hmem := (regularNilpotentLinear_range_ordered_iff hs 1
    (layerC1Linear s p-p))
  simp only [pow_one] at hmem
  apply hmem.mpr
  rw [regular_triangular_range_eq_head_kernel (by omega)
    (regularNilpotentMatrix s) (regularNilpotentMatrix_triangular s)
    (regularNilpotentMatrix_adjacent s)]
  apply LinearMap.mem_ker.mpr
  change regularOrderedHead (by omega)
    ((regularOrderedLinearEquiv hs) (layerC1Linear s p-p))=0
  rw [map_sub,map_sub]
  change regularOrderedCoordinates hs (layerC1Linear s p) (⟨0,by omega⟩ : Fin (s+s))-
    regularOrderedCoordinates hs p (⟨0,by omega⟩ : Fin (s+s))=0
  rw [layerC1Linear_ordered_head_fixed hs,sub_self]

theorem layerC1Linear_difference_range_subset {s : ℕ} (hs : 0<s) :
    LinearMap.range (layerC1Linear s-1) ≤ LinearMap.range (regularNilpotentLinear s) := by
  rintro q ⟨p,rfl⟩
  change layerC1Linear s p-p ∈ LinearMap.range (regularNilpotentLinear s)
  exact layerC1Linear_difference_mem_range hs p

theorem regularCliffordLinear_blockSize_orderOf {h : ℕ} (hh : 1≤h) :
    orderOf (regularCliffordLinear (blockSize h))=2^h := by
  obtain ⟨hlower,hupper⟩ := blockSize_cycle_bounds hh
  have hpred : h-1+1=h := Nat.sub_add_cancel hh
  simpa only [hpred] using regularCliffordLinear_orderOf (blockSize_pos h) (h-1)
    hlower (by simpa only [hpred] using hupper)

theorem regularClifford_blockSize_signed_endpoint {h : ℕ} (hh : 1≤h)
    (hfaith : ∀ (a : ℂ) (p r : PauliLabel (blockSize h)),
      orderedPauli p.1 p.2=a • orderedPauli r.1 r.2 → p=r) :
    ∃ (e : ZMod 2) (p : PauliLabel (blockSize h)),
      regularClifford (blockSize h) ^ (2^h)=bitSign e • orderedPauli p.1 p.2 ∧
      dot p.2 p.1=0 ∧
      p ∈ LinearMap.range (regularNilpotentLinear (blockSize h) ^ (2^(h-1))) ∧
      regularClifford (blockSize h) ^ (2^(h+1))=1 := by
  obtain ⟨hlower,hupper⟩ := blockSize_cycle_bounds hh
  obtain ⟨e,p,he,hHerm,hrange,hperiod⟩ :=
    regularClifford_pow_two_pow_signed_endpoint (blockSize_pos h) hfaith
      h hh hupper (2^(h-1)) hlower
  refine ⟨e,p,he,hHerm,hrange,?_⟩
  simpa only [Nat.pow_succ,Nat.mul_comm (2^h) 2] using hperiod

theorem regularClifford_blockSize_actualPeriod {h : ℕ} (hh : 1≤h)
    (hfaith : ∀ (a : ℂ) (p r : PauliLabel (blockSize h)),
      orderedPauli p.1 p.2=a • orderedPauli r.1 r.2 → p=r) :
    actualPauliPeriod h (regularClifford (blockSize h)) ∧
      ∀ a<h, ∀ b : ℂ,
        ¬actualPauli (b • (regularClifford (blockSize h) ^ (2^a))) := by
  obtain ⟨hlower,hupper⟩ := blockSize_cycle_bounds hh
  exact regularClifford_actualPeriod (blockSize_pos h) hfaith h hh hlower hupper

end QuantumProver.ControlledCliffordHierarchy

attribute [simp] Fin.natAdd_eq_addNat
