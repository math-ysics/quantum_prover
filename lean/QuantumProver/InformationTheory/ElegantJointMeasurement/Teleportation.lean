import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.MeasurementStates
import QuantumProver.InformationTheory.ElegantJointMeasurement.IConcurrence
import QuantumProver.InformationTheory.ElegantJointMeasurement.ProtocolEffects
import QuantumProver.InformationTheory.ElegantJointMeasurement.TailReferencePurity

open scoped BigOperators ComplexConjugate Kronecker

namespace QuantumProver.ElegantJointMeasurement.Teleportation

noncomputable section

abbrev Q := Fin 2
abbrev BellLabel := Q × Q
abbrev SystemIndex := Q × Q

def resourceScale : ℝ := 1 / Real.sqrt 2
def c : ℂ := (resourceScale : ℂ)

theorem resourceScale_pos : 0 < resourceScale := by
  unfold resourceScale
  positivity

theorem resourceScale_sq : resourceScale ^ 2 = (1 / 2 : ℝ) := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  unfold resourceScale
  field_simp [hn]
  nlinarith [hs]

@[simp] theorem conj_c : conj c = c := by simp [c]

theorem c_sq : c ^ 2 = (1 / 2 : ℂ) := by
  rw [c, ← Complex.ofReal_pow, resourceScale_sq]
  norm_num

@[simp] theorem conj_half : conj (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
  rw [← c_sq, map_pow, conj_c]

def pauli (m : BellLabel) : Matrix Q Q ℂ :=
  QuantumProver.ElegantJointMeasurement.States.pauliX ^ m.2.val * QuantumProver.ElegantJointMeasurement.States.pauliZ ^ m.1.val

theorem pauli_unitary (m : BellLabel) :
    pauli m * (pauli m).conjTranspose = 1 := by
  rcases m with ⟨m₁, m₂⟩
  fin_cases m₁ <;> fin_cases m₂ <;>
    ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [pauli, QuantumProver.ElegantJointMeasurement.States.pauliX, QuantumProver.ElegantJointMeasurement.States.pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem pauli_unitary_left (m : BellLabel) :
    (pauli m).conjTranspose * pauli m = 1 := by
  exact mul_eq_one_comm.mp (pauli_unitary m)

def resource : Matrix Q Q ℂ := c • (1 : Matrix Q Q ℂ)

def bellCoefficient (m : BellLabel) : Matrix Q Q ℂ := c • pauli m

def flatten (E : Matrix Q Q ℂ) : SystemIndex → ℂ := fun i => E i.1 i.2

def rankOneEffect (v : SystemIndex → ℂ) : Matrix SystemIndex SystemIndex ℂ :=
  fun i k => v i * conj (v k)

def aliceBellContraction (m : BellLabel) (ψ : Matrix Q Q ℂ) : Matrix Q Q ℂ :=
  fun r b => ∑ a : Q, ∑ s : Q,
    conj (bellCoefficient m a s) * ψ a b * resource s r

def corrected (m : BellLabel) (ψ : Matrix Q Q ℂ) : Matrix Q Q ℂ :=
  pauli m * aliceBellContraction m ψ

theorem aliceBellContraction_eq (m : BellLabel) (ψ : Matrix Q Q ℂ) :
    aliceBellContraction m ψ = (1 / 2 : ℂ) • ((pauli m).conjTranspose * ψ) := by
  ext r b
  simp only [aliceBellContraction, bellCoefficient, resource, Matrix.smul_apply,
    smul_eq_mul, map_mul, conj_c, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    c * conj (pauli m a r) * ψ a b * c =
        c ^ 2 * (conj (pauli m a r) * ψ a b) := by ring
    _ = (1 / 2 : ℂ) * (conj (pauli m a r) * ψ a b) := by rw [c_sq]

theorem corrected_eq_half (m : BellLabel) (ψ : Matrix Q Q ℂ) :
    corrected m ψ = (1 / 2 : ℂ) • ψ := by
  rw [corrected, aliceBellContraction_eq, Matrix.mul_smul,
    ← Matrix.mul_assoc, pauli_unitary, Matrix.one_mul]

theorem bell_orthonormal (m n : BellLabel) :
    QuantumProver.ElegantJointMeasurement.States.coefficientInner (bellCoefficient m) (bellCoefficient n) =
      if m = n then 1 else 0 := by
  rcases m with ⟨m₁, m₂⟩
  rcases n with ⟨n₁, n₂⟩
  fin_cases m₁ <;> fin_cases m₂ <;> fin_cases n₁ <;> fin_cases n₂ <;>
    norm_num [bellCoefficient, pauli,
      QuantumProver.ElegantJointMeasurement.States.coefficientInner, QuantumProver.ElegantJointMeasurement.States.pauliX, QuantumProver.ElegantJointMeasurement.States.pauliZ,
      Matrix.mul_apply, Fin.sum_univ_two, ← sq, c_sq]

theorem bell_complete :
    ∑ m : BellLabel, rankOneEffect (flatten (bellCoefficient m)) = 1 := by
  ext i k
  rcases i with ⟨a, s⟩
  rcases k with ⟨a', s'⟩
  fin_cases a <;> fin_cases s <;> fin_cases a' <;> fin_cases s' <;>
    norm_num [rankOneEffect, flatten, bellCoefficient, pauli,
      QuantumProver.ElegantJointMeasurement.States.pauliX, QuantumProver.ElegantJointMeasurement.States.pauliZ, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, ← sq, c_sq]

def tetrahedron : Fin 4 → Fin 3 → ℝ :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

def ejmCoefficient (j : Fin 4) : Matrix Q Q ℂ :=
  QuantumProver.ElegantJointMeasurement.States.ejmCoefficient (tetrahedron j 0) (tetrahedron j 1) (tetrahedron j 2)

theorem ejm_is_physical (j : Fin 4) :
    QuantumProver.ElegantJointMeasurement.States.ejmFromPauli (tetrahedron j 0) (tetrahedron j 1)
      (tetrahedron j 2) = ejmCoefficient j :=
  QuantumProver.ElegantJointMeasurement.States.ejmFromPauli_eq _ _ _

theorem ejm_orthonormal (j k : Fin 4) :
    QuantumProver.ElegantJointMeasurement.States.coefficientInner (ejmCoefficient j) (ejmCoefficient k) =
      if j = k then 1 else 0 := by
  rw [ejmCoefficient, ejmCoefficient, QuantumProver.ElegantJointMeasurement.States.ejmCoefficient_inner]
  fin_cases j <;> fin_cases k <;> norm_num [tetrahedron]

def ejmBraMatrix : Matrix (Fin 4) SystemIndex ℂ :=
  fun j i => conj (flatten (ejmCoefficient j) i)

theorem ejmBraMatrix_unitary : ejmBraMatrix * ejmBraMatrix.conjTranspose = 1 := by
  ext j k
  simpa [ejmBraMatrix, flatten, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, QuantumProver.ElegantJointMeasurement.States.coefficientInner, Matrix.one_apply] using
    ejm_orthonormal j k

def represented_physicalEffect (j : Fin 4) : Matrix SystemIndex SystemIndex ℂ :=
  rankOneEffect (flatten (ejmCoefficient j))

theorem ejm_complete : ∑ j : Fin 4, represented_physicalEffect j = 1 := by
  have hu : ejmBraMatrix.conjTranspose * ejmBraMatrix = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (Fin 4) SystemIndex ℂ
      (by simp [SystemIndex, Q])).mp
      ejmBraMatrix_unitary
  calc
    ∑ j : Fin 4, represented_physicalEffect j = ejmBraMatrix.conjTranspose * ejmBraMatrix := by
      ext i k
      simp [Matrix.sum_apply, represented_physicalEffect, rankOneEffect, ejmBraMatrix, Matrix.mul_apply,
        Matrix.conjTranspose_apply]
    _ = 1 := hu

def basisCoefficient (i : SystemIndex) : Matrix Q Q ℂ :=
  fun a b => if a = i.1 then if b = i.2 then 1 else 0 else 0

theorem coefficientInner_basis (E : Matrix Q Q ℂ) (i : SystemIndex) :
    QuantumProver.ElegantJointMeasurement.States.coefficientInner E (basisCoefficient i) = conj (flatten E i) := by
  simp [QuantumProver.ElegantJointMeasurement.States.coefficientInner, basisCoefficient, flatten]

theorem coefficientInner_right_smul (E F : Matrix Q Q ℂ) (z : ℂ) :
    QuantumProver.ElegantJointMeasurement.States.coefficientInner E (z • F) = z * QuantumProver.ElegantJointMeasurement.States.coefficientInner E F := by
  simpa using QuantumProver.ElegantJointMeasurement.States.coefficientInner_smul E F 1 z

def jointBranchAmplitude (m : BellLabel) (j : Fin 4) (ψ : Matrix Q Q ℂ) : ℂ :=
  QuantumProver.ElegantJointMeasurement.States.coefficientInner (ejmCoefficient j) (corrected m ψ)

theorem jointBranchAmplitude_eq_half (m : BellLabel) (j : Fin 4)
    (ψ : Matrix Q Q ℂ) :
    jointBranchAmplitude m j ψ =
      (1 / 2 : ℂ) * QuantumProver.ElegantJointMeasurement.States.coefficientInner (ejmCoefficient j) ψ := by
  rw [jointBranchAmplitude, corrected_eq_half, coefficientInner_right_smul]

def branchKet (m : BellLabel) (j : Fin 4) : SystemIndex → ℂ :=
  fun i => conj (jointBranchAmplitude m j (basisCoefficient i))

theorem branchKet_eq_half (m : BellLabel) (j : Fin 4) :
    branchKet m j = (1 / 2 : ℂ) • flatten (ejmCoefficient j) := by
  ext i
  simp only [branchKet, jointBranchAmplitude_eq_half, coefficientInner_basis,
    map_mul, conj_half, starRingEnd_self_apply, Pi.smul_apply, smul_eq_mul]

def branchEffect (m : BellLabel) (j : Fin 4) : Matrix SystemIndex SystemIndex ℂ :=
  rankOneEffect (branchKet m j)

theorem rankOneEffect_smul (z : ℂ) (v : SystemIndex → ℂ) :
    rankOneEffect (z • v) = (z * conj z) • rankOneEffect v := by
  ext i k
  simp only [rankOneEffect, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  ring

theorem branchEffect_eq_quarter (m : BellLabel) (j : Fin 4) :
    branchEffect m j = (1 / 4 : ℂ) • represented_physicalEffect j := by
  rw [branchEffect, branchKet_eq_half, rankOneEffect_smul, conj_half]
  norm_num [represented_physicalEffect]

theorem effective_effect_eq_physical (j : Fin 4) :
    ∑ m : BellLabel, branchEffect m j = represented_physicalEffect j := by
  simp_rw [branchEffect_eq_quarter]
  ext i k
  simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem all_branch_effects_complete :
    ∑ j : Fin 4, ∑ m : BellLabel, branchEffect m j = 1 := by
  simp_rw [effective_effect_eq_physical]
  exact ejm_complete

theorem all_mixed_state_probabilities (ρ : Matrix SystemIndex SystemIndex ℂ) (j : Fin 4) :
    ∑ m : BellLabel, Matrix.trace (branchEffect m j * ρ) =
      Matrix.trace (represented_physicalEffect j * ρ) := by
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, effective_effect_eq_physical]

theorem frobeniusNormSq_smul (z : ℂ) (ψ : Matrix Q Q ℂ) :
    QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq (z • ψ) =
      Complex.normSq z * QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq ψ := by
  simp [QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq, Complex.normSq_mul]
  ring

theorem pauli_preserves_mass (m : BellLabel) (ψ : Matrix Q Q ℂ) :
    QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq (pauli m * ψ) = QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq ψ := by
  rcases m with ⟨m₁, m₂⟩
  fin_cases m₁ <;> fin_cases m₂ <;>
    simp [QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq, pauli, QuantumProver.ElegantJointMeasurement.States.pauliX, QuantumProver.ElegantJointMeasurement.States.pauliZ,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem corrected_mass_quarter (m : BellLabel) (ψ : Matrix Q Q ℂ) :
    QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq (corrected m ψ) =
      (1 / 4 : ℝ) * QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq ψ := by
  rw [corrected_eq_half, frobeniusNormSq_smul]
  norm_num [Complex.normSq]

theorem alice_branch_mass_quarter (m : BellLabel) (ψ : Matrix Q Q ℂ) :
    QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq (aliceBellContraction m ψ) =
      (1 / 4 : ℝ) * QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq ψ := by
  calc
    QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq (aliceBellContraction m ψ) =
        QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq (corrected m ψ) :=
      (pauli_preserves_mass m (aliceBellContraction m ψ)).symm
    _ = _ := corrected_mass_quarter m ψ

theorem alice_all_branch_mass (ψ : Matrix Q Q ℂ) :
    ∑ m : BellLabel, QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq (aliceBellContraction m ψ) =
      QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq ψ := by
  simp_rw [alice_branch_mass_quarter]
  simp

def schmidtWeight (_ : Q) : ℝ := 1 / 2

theorem resource_diagonal :
    resource = Matrix.diagonal (fun _ : Q => (resourceScale : ℂ)) := by
  ext a b
  simp [resource, c, Matrix.one_apply, Matrix.diagonal_apply]

theorem resource_schmidt_weights (q : Q) : resourceScale ^ 2 = schmidtWeight q :=
  resourceScale_sq

theorem resource_gram :
    resource * resource.conjTranspose =
      Matrix.diagonal (fun q : Q => (schmidtWeight q : ℂ)) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [resource, schmidtWeight, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, ← sq, c_sq]

theorem resource_normalized : QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq resource = 1 := by
  norm_num [QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq, resource, c, Fin.sum_univ_two,
    Complex.normSq_ofReal, ← sq, resourceScale_sq]

theorem schmidt_weights_sum_one : ∑ q : Q, schmidtWeight q = 1 := by
  norm_num [schmidtWeight, Fin.sum_univ_two]

theorem schmidt_weights_positive (q : Q) : 0 < schmidtWeight q := by
  norm_num [schmidtWeight]

def resourceEntropyBits : ℝ :=
  (∑ q : Q, Real.negMulLog (schmidtWeight q)) / Real.log 2

theorem resource_entropy_one : resourceEntropyBits = 1 := by
  have hl : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hn : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold resourceEntropyBits
  simp only [schmidtWeight, Fin.sum_univ_two, Real.negMulLog, hl]
  field_simp [hn]
  ring

def aliceLocalBra (m : BellLabel) : Matrix Unit SystemIndex ℂ :=
  fun _ i => conj (flatten (bellCoefficient m) i)

theorem aliceLocalBra_effect (m : BellLabel) :
    (aliceLocalBra m).conjTranspose * aliceLocalBra m =
      rankOneEffect (flatten (bellCoefficient m)) := by
  ext i k
  simp [aliceLocalBra, Matrix.mul_apply, Matrix.conjTranspose_apply, rankOneEffect]

theorem alice_local_instrument_complete :
    ∑ m : BellLabel, (aliceLocalBra m).conjTranspose * aliceLocalBra m = 1 := by
  simp_rw [aliceLocalBra_effect]
  exact bell_complete

def bobCorrection (m : BellLabel) : Matrix SystemIndex SystemIndex ℂ :=
  pauli m ⊗ₖ (1 : Matrix Q Q ℂ)

theorem bobCorrection_unitary (m : BellLabel) :
    bobCorrection m * (bobCorrection m).conjTranspose = 1 := by
  simp only [bobCorrection, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, pauli_unitary, Matrix.one_mul, Matrix.one_kronecker_one]

theorem bobCorrection_unitary_left (m : BellLabel) :
    (bobCorrection m).conjTranspose * bobCorrection m = 1 :=
  mul_eq_one_comm.mp (bobCorrection_unitary m)

theorem bobCorrection_action (m : BellLabel) (ψ : Matrix Q Q ℂ) :
    Matrix.mulVec (bobCorrection m) (flatten (aliceBellContraction m ψ)) =
      flatten (corrected m ψ) := by
  ext i
  rcases i with ⟨r, b⟩
  simp [bobCorrection, Matrix.mulVec, dotProduct, Matrix.one_apply,
    Fintype.sum_prod_type, flatten, corrected, Matrix.mul_apply]

def bobLocalBra (j : Fin 4) : Matrix Unit SystemIndex ℂ :=
  fun _ i => conj (flatten (ejmCoefficient j) i)

theorem bobLocalBra_effect (j : Fin 4) :
    (bobLocalBra j).conjTranspose * bobLocalBra j = represented_physicalEffect j := by
  ext i k
  simp [bobLocalBra, Matrix.mul_apply, Matrix.conjTranspose_apply,
    represented_physicalEffect, rankOneEffect]

theorem bob_local_instrument_complete :
    ∑ j : Fin 4, (bobLocalBra j).conjTranspose * bobLocalBra j = 1 := by
  simp_rw [bobLocalBra_effect]
  exact ejm_complete

def sharedInput (ψ : Matrix Q Q ℂ) : Matrix SystemIndex SystemIndex ℂ :=
  fun as rb => ψ as.1 rb.2 * resource as.2 rb.1

theorem aliceLocalBra_action (m : BellLabel) (ψ : Matrix Q Q ℂ) (r b : Q) :
    (aliceLocalBra m * sharedInput ψ) () (r, b) = aliceBellContraction m ψ r b := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, aliceLocalBra,
    sharedInput, flatten, aliceBellContraction]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro s hs
  ring

def physicalBranchAmplitude (m : BellLabel) (j : Fin 4) (ψ : Matrix Q Q ℂ) : ℂ :=
  Matrix.mulVec (bobLocalBra j)
    (Matrix.mulVec (bobCorrection m) (flatten (aliceBellContraction m ψ))) ()

theorem physicalBranchAmplitude_eq (m : BellLabel) (j : Fin 4) (ψ : Matrix Q Q ℂ) :
    physicalBranchAmplitude m j ψ = jointBranchAmplitude m j ψ := by
  rw [physicalBranchAmplitude, bobCorrection_action]
  simp [Matrix.mulVec, dotProduct, bobLocalBra, jointBranchAmplitude, flatten,
    QuantumProver.ElegantJointMeasurement.States.coefficientInner, Fintype.sum_prod_type]

def terminalBobBra (m : BellLabel) (j : Fin 4) : Matrix Unit SystemIndex ℂ :=
  bobLocalBra j * bobCorrection m

theorem terminalBobBra_effect (m : BellLabel) (j : Fin 4) :
    (terminalBobBra m j).conjTranspose * terminalBobBra m j =
      (bobCorrection m).conjTranspose *
        ((bobLocalBra j).conjTranspose * bobLocalBra j) * bobCorrection m := by
  simp [terminalBobBra, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem terminal_bob_instrument_complete (m : BellLabel) :
    ∑ j : Fin 4, (terminalBobBra m j).conjTranspose * terminalBobBra m j = 1 := by
  simp_rw [terminalBobBra_effect]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, bob_local_instrument_complete,
    Matrix.mul_one, bobCorrection_unitary_left]

abbrev ExtendedIndex := SystemIndex × SystemIndex

def terminalProductBra (m : BellLabel) (j : Fin 4) : Matrix (Unit × Unit) ExtendedIndex ℂ :=
  aliceLocalBra m ⊗ₖ terminalBobBra m j

theorem terminal_product_instrument_complete :
    ∑ m : BellLabel, ∑ j : Fin 4,
      (terminalProductBra m j).conjTranspose * terminalProductBra m j = 1 := by
  simp_rw [terminalProductBra, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  calc
    ∑ m : BellLabel, ∑ j : Fin 4,
        ((aliceLocalBra m).conjTranspose * aliceLocalBra m) ⊗ₖ
          ((terminalBobBra m j).conjTranspose * terminalBobBra m j) =
        ∑ m : BellLabel, ((aliceLocalBra m).conjTranspose * aliceLocalBra m) ⊗ₖ
          (1 : Matrix SystemIndex SystemIndex ℂ) := by
      apply Finset.sum_congr rfl
      intro m hm
      calc
        ∑ j : Fin 4, ((aliceLocalBra m).conjTranspose * aliceLocalBra m) ⊗ₖ
            ((terminalBobBra m j).conjTranspose * terminalBobBra m j) =
          ((aliceLocalBra m).conjTranspose * aliceLocalBra m) ⊗ₖ
            (∑ j : Fin 4, (terminalBobBra m j).conjTranspose * terminalBobBra m j) := by
          ext i k
          simp [Matrix.sum_apply, Finset.mul_sum]
        _ = _ := by rw [terminal_bob_instrument_complete]
    _ = (∑ m : BellLabel, (aliceLocalBra m).conjTranspose * aliceLocalBra m) ⊗ₖ
        (1 : Matrix SystemIndex SystemIndex ℂ) := by
      ext i k
      simp [Matrix.sum_apply, Finset.sum_mul]
    _ = 1 := by rw [alice_local_instrument_complete, Matrix.one_kronecker_one]

def flattenSharedInput (ψ : Matrix Q Q ℂ) : ExtendedIndex → ℂ :=
  fun x => sharedInput ψ x.1 x.2

theorem terminalProductBra_action (m : BellLabel) (j : Fin 4) (ψ : Matrix Q Q ℂ) :
    Matrix.mulVec (terminalProductBra m j) (flattenSharedInput ψ) ((), ()) =
      physicalBranchAmplitude m j ψ := by
  calc
    Matrix.mulVec (terminalProductBra m j) (flattenSharedInput ψ) ((), ()) =
        ∑ rb : SystemIndex, terminalBobBra m j () rb *
          (∑ as : SystemIndex, aliceLocalBra m () as * sharedInput ψ as rb) := by
      rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
      simp only [terminalProductBra, Matrix.kroneckerMap_apply, flattenSharedInput]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro rb hrb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro as has
      ring
    _ = Matrix.mulVec (terminalBobBra m j) (flatten (aliceBellContraction m ψ)) () := by
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro rb hrb
      rw [← Matrix.mul_apply, aliceLocalBra_action]
      rfl
    _ = physicalBranchAmplitude m j ψ := by
      rw [physicalBranchAmplitude, Matrix.mulVec_mulVec]
      rfl

def resourceEmbedding : Matrix ExtendedIndex SystemIndex ℂ :=
  fun x i => flattenSharedInput (basisCoefficient i) x

theorem resourceEmbedding_action (ψ : Matrix Q Q ℂ) :
    Matrix.mulVec resourceEmbedding (flatten ψ) = flattenSharedInput ψ := by
  ext x
  simp [Matrix.mulVec, dotProduct, resourceEmbedding, flattenSharedInput, sharedInput,
    basisCoefficient, flatten, Fintype.sum_prod_type, mul_ite, mul_comm]

def actualEffectiveBra (m : BellLabel) (j : Fin 4) :
    Matrix (Unit × Unit) SystemIndex ℂ :=
  terminalProductBra m j * resourceEmbedding

theorem actualEffectiveBra_eq (m : BellLabel) (j : Fin 4) :
    actualEffectiveBra m j = fun _ i => conj (branchKet m j i) := by
  ext u i
  rcases u with ⟨⟨⟩, ⟨⟩⟩
  change Matrix.mulVec (terminalProductBra m j)
    (flattenSharedInput (basisCoefficient i)) ((), ()) = conj (branchKet m j i)
  rw [terminalProductBra_action, physicalBranchAmplitude_eq]
  simp [branchKet]

theorem actual_effect_eq_branchEffect (m : BellLabel) (j : Fin 4) :
    (actualEffectiveBra m j).conjTranspose * actualEffectiveBra m j = branchEffect m j := by
  rw [actualEffectiveBra_eq]
  ext i k
  change (∑ _u : Unit × Unit, conj (conj (branchKet m j i)) * conj (branchKet m j k)) = _
  simp [branchEffect, rankOneEffect]

def resourceEncodedDensity (ρ : Matrix SystemIndex SystemIndex ℂ) :
    Matrix ExtendedIndex ExtendedIndex ℂ :=
  resourceEmbedding * ρ * resourceEmbedding.conjTranspose

def literalBranchWeight (m : BellLabel) (j : Fin 4)
    (ρ : Matrix SystemIndex SystemIndex ℂ) : ℂ :=
  Matrix.trace (terminalProductBra m j * resourceEncodedDensity ρ *
    (terminalProductBra m j).conjTranspose)

theorem literalBranchWeight_eq_effect (m : BellLabel) (j : Fin 4)
    (ρ : Matrix SystemIndex SystemIndex ℂ) :
    literalBranchWeight m j ρ = Matrix.trace (branchEffect m j * ρ) := by
  have h : terminalProductBra m j * resourceEncodedDensity ρ *
      (terminalProductBra m j).conjTranspose =
      (actualEffectiveBra m j * ρ) * (actualEffectiveBra m j).conjTranspose := by
    simp [actualEffectiveBra, resourceEncodedDensity, Matrix.conjTranspose_mul,
      Matrix.mul_assoc]
  rw [literalBranchWeight, h, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    actual_effect_eq_branchEffect]

theorem literal_all_mixed_state_probabilities (ρ : Matrix SystemIndex SystemIndex ℂ)
    (j : Fin 4) :
    ∑ m : BellLabel, literalBranchWeight m j ρ = Matrix.trace (represented_physicalEffect j * ρ) := by
  simp_rw [literalBranchWeight_eq_effect]
  exact all_mixed_state_probabilities ρ j

theorem jointBranchAmplitude_eq_branchBra (m : BellLabel) (j : Fin 4)
    (ψ : Matrix Q Q ℂ) :
    jointBranchAmplitude m j ψ =
      ∑ i : SystemIndex, conj (branchKet m j i) * flatten ψ i := by
  rw [jointBranchAmplitude_eq_half, branchKet_eq_half]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, conj_half,
    Fintype.sum_prod_type, flatten, QuantumProver.ElegantJointMeasurement.States.coefficientInner, Finset.mul_sum,
    mul_assoc]

def sharedClassicalOutput (_ : BellLabel) (j : Fin 4) : Fin 4 × Fin 4 := (j, j)

abbrev ClassicalIndex := Fin 4 × Fin 4

def sharedLabelProjector (j : Fin 4) : Matrix ClassicalIndex ClassicalIndex ℂ :=
  Matrix.diagonal (fun x => if x = (j, j) then 1 else 0)

def physicalClassicalChannel (ρ : Matrix SystemIndex SystemIndex ℂ) :
    Matrix ClassicalIndex ClassicalIndex ℂ :=
  ∑ j : Fin 4, Matrix.trace (represented_physicalEffect j * ρ) • sharedLabelProjector j

def implementedClassicalChannel (ρ : Matrix SystemIndex SystemIndex ℂ) :
    Matrix ClassicalIndex ClassicalIndex ℂ :=
  ∑ j : Fin 4,
    (∑ m : BellLabel, Matrix.trace (branchEffect m j * ρ)) • sharedLabelProjector j

def literalClassicalChannel (ρ : Matrix SystemIndex SystemIndex ℂ) :
    Matrix ClassicalIndex ClassicalIndex ℂ :=
  ∑ j : Fin 4, (∑ m : BellLabel, literalBranchWeight m j ρ) • sharedLabelProjector j

theorem exactClassicalChannel (ρ : Matrix SystemIndex SystemIndex ℂ) :
    implementedClassicalChannel ρ = physicalClassicalChannel ρ := by
  simp only [implementedClassicalChannel, physicalClassicalChannel,
    all_mixed_state_probabilities]

theorem literalClassicalChannel_eq_physical (ρ : Matrix SystemIndex SystemIndex ℂ) :
    literalClassicalChannel ρ = physicalClassicalChannel ρ := by
  simp only [literalClassicalChannel, physicalClassicalChannel,
    literal_all_mixed_state_probabilities]

theorem protocol_total_probability (ρ : Matrix SystemIndex SystemIndex ℂ) :
    ∑ j : Fin 4, ∑ m : BellLabel, Matrix.trace (branchEffect m j * ρ) =
      Matrix.trace ρ := by
  simp_rw [all_mixed_state_probabilities]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, ejm_complete, Matrix.one_mul]

def systemFinEquiv : SystemIndex ≃ Fin 4 := finProdFinEquiv
def unitFinEquiv : Unit ≃ Fin 1 := Fintype.equivFinOfCardEq (by simp)

def aliceFinBra (m : Fin 4) : Matrix (Fin 1) (Fin 4) ℂ :=
  Matrix.reindex unitFinEquiv systemFinEquiv (aliceLocalBra (systemFinEquiv.symm m))

def bobFinCorrection (m : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex systemFinEquiv systemFinEquiv (bobCorrection (systemFinEquiv.symm m))

def bobFinBra (j : Fin 4) : Matrix (Fin 1) (Fin 4) ℂ :=
  Matrix.reindex unitFinEquiv systemFinEquiv (bobLocalBra j)

theorem finiteBra_effect_reindex (K : Matrix Unit SystemIndex ℂ) :
    (Matrix.reindex unitFinEquiv systemFinEquiv K).conjTranspose *
        Matrix.reindex unitFinEquiv systemFinEquiv K =
      Matrix.reindex systemFinEquiv systemFinEquiv (K.conjTranspose * K) := by
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]

theorem aliceFinBra_complete :
    ∑ m : Fin 4, (aliceFinBra m).conjTranspose * aliceFinBra m = 1 := by
  simp only [aliceFinBra, finiteBra_effect_reindex]
  have hs : (∑ m : Fin 4,
      (aliceLocalBra (systemFinEquiv.symm m)).conjTranspose *
        aliceLocalBra (systemFinEquiv.symm m)) = 1 :=
    (systemFinEquiv.symm.sum_comp (fun m : SystemIndex =>
      (aliceLocalBra m).conjTranspose * aliceLocalBra m)).trans
        alice_local_instrument_complete
  have ht := congrArg (Matrix.reindex systemFinEquiv systemFinEquiv) hs
  ext i k
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i k) ht
  simpa [Matrix.sum_apply, Matrix.reindex_apply, Matrix.one_apply] using h

theorem bobFinCorrection_unitary_left (m : Fin 4) :
    (bobFinCorrection m).conjTranspose * bobFinCorrection m = 1 := by
  simp only [bobFinCorrection, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, bobCorrection_unitary_left, Matrix.submatrix_one_equiv]

theorem bobFinBra_complete :
    ∑ j : Fin 4, (bobFinBra j).conjTranspose * bobFinBra j = 1 := by
  simp only [bobFinBra, finiteBra_effect_reindex]
  ext i k
  simp only [Matrix.sum_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  have h := congrArg (fun M : Matrix SystemIndex SystemIndex ℂ =>
    M (systemFinEquiv.symm i) (systemFinEquiv.symm k)) bob_local_instrument_complete
  simpa [Matrix.sum_apply, Matrix.one_apply] using h

def bobEjmFiniteTree : QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree 1 4 :=
  .bob 1 4 1 4 bobFinBra bobFinBra_complete (fun _ => .leaf 1 1)

def bobCorrectionFiniteTree (m : Fin 4) : QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree 1 4 :=
  .bob 1 4 4 1 (fun _ => bobFinCorrection m)
    (by simpa using bobFinCorrection_unitary_left m) (fun _ => bobEjmFiniteTree)

def oneEbitFiniteTree : QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree 4 4 :=
  .alice 4 4 1 4 aliceFinBra aliceFinBra_complete (fun m => bobCorrectionFiniteTree m)

def finiteBranchPair (m j : Fin 4) : QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair 4 4 :=
  ⟨fun a => aliceFinBra m 0 a, fun b => (bobFinBra j * bobFinCorrection m) 0 b⟩

theorem finite_one_basis_vecMul {n : ℕ} (K : Matrix (Fin 1) (Fin n) ℂ) :
    Matrix.vecMul (fun b : Fin 1 => if b = 0 then 1 else 0) K = fun a => K 0 a := by
  ext a
  simp [Matrix.vecMul, dotProduct]

theorem finite_row_vecMul {m n o : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (N : Matrix (Fin n) (Fin o) ℂ) (i : Fin m) :
    Matrix.vecMul (fun a => M i a) N = fun b => ∑ a, M i a * N a b := by
  ext b
  rfl

theorem oneEbitFiniteTree_terminal_records :
    oneEbitFiniteTree.terminalBraPairs =
      (List.ofFn fun m : Fin 4 => List.ofFn fun j : Fin 4 => finiteBranchPair m j).flatten := by
  simp [oneEbitFiniteTree, bobCorrectionFiniteTree, bobEjmFiniteTree,
    QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree.terminalBraPairs,
    QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair.precomposeLeft,
    QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair.precomposeRight, finiteBranchPair,
    List.ofFn_succ, finite_one_basis_vecMul, finite_row_vecMul, Matrix.mul_apply]

theorem aliceFinBra_row (m a : Fin 4) :
    aliceFinBra m 0 a = aliceLocalBra (systemFinEquiv.symm m) () (systemFinEquiv.symm a) := by
  simp [aliceFinBra, Matrix.reindex_apply]

theorem bobFinCompositeBra_row (m j b : Fin 4) :
    (bobFinBra j * bobFinCorrection m) 0 b =
      terminalBobBra (systemFinEquiv.symm m) j () (systemFinEquiv.symm b) := by
  have h : bobFinBra j * bobFinCorrection m =
      Matrix.reindex unitFinEquiv systemFinEquiv (terminalBobBra (systemFinEquiv.symm m) j) := by
    simp only [bobFinBra, bobFinCorrection, terminalBobBra, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv]
  simpa [Matrix.reindex_apply] using congrArg (fun M => M 0 b) h

def matrixExtendedEquiv : ExtendedIndex ≃ (Fin 4 × Fin 4) :=
  Equiv.prodCongr systemFinEquiv systemFinEquiv

theorem finiteBranchPair_productEffect (m j : Fin 4) :
    (finiteBranchPair m j).productEffect =
      ((terminalProductBra (systemFinEquiv.symm m) j).conjTranspose *
        terminalProductBra (systemFinEquiv.symm m) j).submatrix
          matrixExtendedEquiv.symm matrixExtendedEquiv.symm := by
  ext z w
  rcases z with ⟨a, b⟩
  rcases w with ⟨a', b'⟩
  simp only [QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair.productEffect_apply, finiteBranchPair,
    aliceFinBra_row, bobFinCompositeBra_row, Matrix.submatrix_apply]
  change conj (aliceLocalBra (systemFinEquiv.symm m) () (systemFinEquiv.symm a) *
        terminalBobBra (systemFinEquiv.symm m) j () (systemFinEquiv.symm b)) *
      (aliceLocalBra (systemFinEquiv.symm m) () (systemFinEquiv.symm a') *
        terminalBobBra (systemFinEquiv.symm m) j () (systemFinEquiv.symm b')) =
      ∑ u : Unit × Unit,
        conj (terminalProductBra (systemFinEquiv.symm m) j u
          (systemFinEquiv.symm a, systemFinEquiv.symm b)) *
        terminalProductBra (systemFinEquiv.symm m) j u
          (systemFinEquiv.symm a', systemFinEquiv.symm b')
  simp [terminalProductBra, Fintype.sum_prod_type]

def matrixResourceEmbedding : Matrix (Fin 4 × Fin 4) SystemIndex ℂ :=
  resourceEmbedding.submatrix matrixExtendedEquiv.symm id

theorem matrix_branch_compression (m j : Fin 4) :
    matrixResourceEmbedding.conjTranspose * (finiteBranchPair m j).productEffect *
        matrixResourceEmbedding = branchEffect (systemFinEquiv.symm m) j := by
  calc
    _ = (actualEffectiveBra (systemFinEquiv.symm m) j).conjTranspose *
        actualEffectiveBra (systemFinEquiv.symm m) j := by
      simp only [matrixResourceEmbedding, finiteBranchPair_productEffect,
        Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
        Matrix.submatrix_id_id, actualEffectiveBra, Matrix.conjTranspose_mul,
        Matrix.mul_assoc]
    _ = _ := actual_effect_eq_branchEffect _ _

def matrixCoarseEffect (j : Fin 4) : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  ∑ m : Fin 4, (finiteBranchPair m j).productEffect

theorem finite_tree_effect_eq_physical (j : Fin 4) :
    matrixResourceEmbedding.conjTranspose * matrixCoarseEffect j * matrixResourceEmbedding =
      represented_physicalEffect j := by
  rw [matrixCoarseEffect, Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [matrix_branch_compression]
  exact (systemFinEquiv.symm.sum_comp (fun m : SystemIndex => branchEffect m j)).trans
    (effective_effect_eq_physical j)

theorem oneEbitFiniteTree_complete : oneEbitFiniteTree.terminalProductEffect = 1 :=
  QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree.terminalProductEffect_eq_one oneEbitFiniteTree

theorem finite_tree_all_mixed_probabilities (ρ : Matrix SystemIndex SystemIndex ℂ) (j : Fin 4) :
    Matrix.trace (matrixCoarseEffect j *
      (matrixResourceEmbedding * ρ * matrixResourceEmbedding.conjTranspose)) =
      Matrix.trace (represented_physicalEffect j * ρ) := by
  calc
    _ = Matrix.trace ((matrixCoarseEffect j * matrixResourceEmbedding * ρ) *
        matrixResourceEmbedding.conjTranspose) := by simp [Matrix.mul_assoc]
    _ = Matrix.trace (matrixResourceEmbedding.conjTranspose *
        (matrixCoarseEffect j * matrixResourceEmbedding * ρ)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((matrixResourceEmbedding.conjTranspose * matrixCoarseEffect j *
        matrixResourceEmbedding) * ρ) := by simp [Matrix.mul_assoc]
    _ = _ := by rw [finite_tree_effect_eq_physical]

def finiteTreeClassicalChannel (ρ : Matrix SystemIndex SystemIndex ℂ) :
    Matrix ClassicalIndex ClassicalIndex ℂ :=
  ∑ j : Fin 4, Matrix.trace (matrixCoarseEffect j *
    (matrixResourceEmbedding * ρ * matrixResourceEmbedding.conjTranspose)) • sharedLabelProjector j

theorem finite_tree_exact_shared_classical_channel (ρ : Matrix SystemIndex SystemIndex ℂ) :
    finiteTreeClassicalChannel ρ = physicalClassicalChannel ρ := by
  simp only [finiteTreeClassicalChannel, physicalClassicalChannel, finite_tree_all_mixed_probabilities]

def bobInputResourceFinEquiv : (Q × Q) ≃ Fin 4 :=
  (Equiv.prodComm Q Q).trans systemFinEquiv

structure OneEbitProtocolCertificate : Prop where
  resource_normalized : QuantumProver.ElegantJointMeasurement.States.frobeniusNormSq resource = 1
  resource_diagonal : resource =
    Matrix.diagonal (fun _ : Q => (resourceScale : ℂ))
  schmidt_amplitude_positive : 0 < resourceScale
  schmidt_weights : ∀ q : Q, resourceScale ^ 2 = schmidtWeight q
  schmidt_weights_normalized : ∑ q : Q, schmidtWeight q = 1
  resource_gram : resource * resource.conjTranspose =
    Matrix.diagonal (fun q : Q => (schmidtWeight q : ℂ))
  resource_entropy : resourceEntropyBits = 1
  alice_complete :
    ∑ m : BellLabel, (aliceLocalBra m).conjTranspose * aliceLocalBra m = 1
  conditional_bob_unitary : ∀ m : BellLabel,
    bobCorrection m * (bobCorrection m).conjTranspose = 1
  bob_complete : ∑ j : Fin 4, (bobLocalBra j).conjTranspose * bobLocalBra j = 1
  conditional_bob_instrument_complete : ∀ m : BellLabel,
    ∑ j : Fin 4, (terminalBobBra m j).conjTranspose * terminalBobBra m j = 1
  global_instrument_complete :
    ∑ m : BellLabel, ∑ j : Fin 4,
      (terminalProductBra m j).conjTranspose * terminalProductBra m j = 1
  actual_product_branch_action : ∀ (m : BellLabel) (j : Fin 4) (ψ : Matrix Q Q ℂ),
    Matrix.mulVec (terminalProductBra m j) (flattenSharedInput ψ) ((), ()) =
      physicalBranchAmplitude m j ψ
  actual_resource_encoding : ∀ ψ : Matrix Q Q ℂ,
    Matrix.mulVec resourceEmbedding (flatten ψ) = flattenSharedInput ψ
  actual_compressed_effect : ∀ (m : BellLabel) (j : Fin 4),
    (actualEffectiveBra m j).conjTranspose * actualEffectiveBra m j = branchEffect m j
  literal_mixed_probabilities : ∀ (ρ : Matrix SystemIndex SystemIndex ℂ) (j : Fin 4),
    ∑ m : BellLabel, literalBranchWeight m j ρ = Matrix.trace (represented_physicalEffect j * ρ)
  literal_shared_classical_channel : ∀ ρ : Matrix SystemIndex SystemIndex ℂ,
    literalClassicalChannel ρ = physicalClassicalChannel ρ
  alice_local_action : ∀ (m : BellLabel) (ψ : Matrix Q Q ℂ) (r b : Q),
    (aliceLocalBra m * sharedInput ψ) () (r, b) = aliceBellContraction m ψ r b
  bob_local_action : ∀ (m : BellLabel) (j : Fin 4) (ψ : Matrix Q Q ℂ),
    physicalBranchAmplitude m j ψ = jointBranchAmplitude m j ψ
  effective_branch_bra : ∀ (m : BellLabel) (j : Fin 4) (ψ : Matrix Q Q ℂ),
    jointBranchAmplitude m j ψ =
      ∑ i : SystemIndex, conj (branchKet m j i) * flatten ψ i
  contraction : ∀ (m : BellLabel) (ψ : Matrix Q Q ℂ),
    corrected m ψ = (1 / 2 : ℂ) • ψ
  physical_ejm : ∀ j : Fin 4,
    QuantumProver.ElegantJointMeasurement.States.ejmFromPauli (tetrahedron j 0) (tetrahedron j 1)
      (tetrahedron j 2) = ejmCoefficient j
  effective_effects : ∀ j : Fin 4,
    ∑ m : BellLabel, branchEffect m j = represented_physicalEffect j
  every_input_probability : ∀ (ρ : Matrix SystemIndex SystemIndex ℂ) (j : Fin 4),
    ∑ m : BellLabel, Matrix.trace (branchEffect m j * ρ) =
      Matrix.trace (represented_physicalEffect j * ρ)
  exact_shared_classical_channel : ∀ ρ : Matrix SystemIndex SystemIndex ℂ,
    implementedClassicalChannel ρ = physicalClassicalChannel ρ
  normalized_total_probability : ∀ ρ : Matrix SystemIndex SystemIndex ℂ,
    ∑ j : Fin 4, ∑ m : BellLabel, Matrix.trace (branchEffect m j * ρ) =
      Matrix.trace ρ
  shared_classical_outcome : ∀ (m : BellLabel) (j : Fin 4),
    sharedClassicalOutput m j = (j, j)

theorem one_ebit_protocol_certificate : OneEbitProtocolCertificate where
  resource_normalized := resource_normalized
  resource_diagonal := resource_diagonal
  schmidt_amplitude_positive := resourceScale_pos
  schmidt_weights := resource_schmidt_weights
  schmidt_weights_normalized := schmidt_weights_sum_one
  resource_gram := resource_gram
  resource_entropy := resource_entropy_one
  alice_complete := alice_local_instrument_complete
  conditional_bob_unitary := bobCorrection_unitary
  bob_complete := bob_local_instrument_complete
  conditional_bob_instrument_complete := terminal_bob_instrument_complete
  global_instrument_complete := terminal_product_instrument_complete
  actual_product_branch_action := terminalProductBra_action
  actual_resource_encoding := resourceEmbedding_action
  actual_compressed_effect := actual_effect_eq_branchEffect
  literal_mixed_probabilities := literal_all_mixed_state_probabilities
  literal_shared_classical_channel := literalClassicalChannel_eq_physical
  alice_local_action := aliceLocalBra_action
  bob_local_action := physicalBranchAmplitude_eq
  effective_branch_bra := jointBranchAmplitude_eq_branchBra
  contraction := corrected_eq_half
  physical_ejm := ejm_is_physical
  effective_effects := effective_effect_eq_physical
  every_input_probability := all_mixed_state_probabilities
  exact_shared_classical_channel := exactClassicalChannel
  normalized_total_probability := protocol_total_probability
  shared_classical_outcome := fun _ _ => rfl

structure OneEbitFiniteProtocolCertificate : Prop where
  coefficient_protocol : OneEbitProtocolCertificate
  actual_terminal_records : oneEbitFiniteTree.terminalBraPairs =
    (List.ofFn fun m : Fin 4 => List.ofFn fun j : Fin 4 => finiteBranchPair m j).flatten
  complete_tree : oneEbitFiniteTree.terminalProductEffect = 1
  compressed_physical_effects : ∀ j : Fin 4,
    matrixResourceEmbedding.conjTranspose * matrixCoarseEffect j * matrixResourceEmbedding =
      represented_physicalEffect j
  all_mixed_probabilities : ∀ (ρ : Matrix SystemIndex SystemIndex ℂ) (j : Fin 4),
    Matrix.trace (matrixCoarseEffect j *
      (matrixResourceEmbedding * ρ * matrixResourceEmbedding.conjTranspose)) =
      Matrix.trace (represented_physicalEffect j * ρ)
  shared_classical_channel : ∀ ρ : Matrix SystemIndex SystemIndex ℂ,
    finiteTreeClassicalChannel ρ = physicalClassicalChannel ρ

theorem one_ebit_finite_locc_protocol_certificate : OneEbitFiniteProtocolCertificate where
  coefficient_protocol := one_ebit_protocol_certificate
  actual_terminal_records := oneEbitFiniteTree_terminal_records
  complete_tree := oneEbitFiniteTree_complete
  compressed_physical_effects := finite_tree_effect_eq_physical
  all_mixed_probabilities := finite_tree_all_mixed_probabilities
  shared_classical_channel := finite_tree_exact_shared_classical_channel

end

end QuantumProver.ElegantJointMeasurement.Teleportation

namespace QuantumProver.ElegantJointMeasurement.Teleportation.Tomography

open scoped BigOperators ComplexConjugate ComplexOrder Topology

noncomputable section

variable {ι κ Label α : Type*} [Fintype ι] [DecidableEq ι]

def basis (i : ι) : ι → ℂ := fun a => if a = i then 1 else 0

omit [Fintype ι] in
@[simp] theorem conj_basis (i a : ι) : conj (basis i a) = basis i a := by
  simp [basis]

def unitMatrix (i k : ι) : Matrix ι ι ℂ := Matrix.vecMulVec (basis i) (basis k)

omit [Fintype ι] in
theorem unitMatrix_eq_single (i k : ι) : unitMatrix i k = Matrix.single i k 1 := by
  ext a b
  by_cases ha : a = i <;> by_cases hb : b = k <;>
    simp [unitMatrix, Matrix.vecMulVec_apply, basis, Matrix.single_apply, ha, hb] <;> aesop

def basisDensity (i : ι) : Matrix ι ι ℂ :=
  Matrix.vecMulVec (basis i) (fun a => conj (basis i a))

omit [Fintype ι] in
theorem basisDensity_eq_single (i : ι) : basisDensity i = Matrix.single i i 1 := by
  simpa only [basisDensity, unitMatrix, conj_basis] using unitMatrix_eq_single i i

theorem basisDensity_positive (i : ι) : (basisDensity i).PosSemidef := by
  change (Matrix.vecMulVec (basis i) (star (basis i))).PosSemidef
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem basisDensity_normalized (i : ι) : Matrix.trace (basisDensity i) = 1 := by
  rw [basisDensity_eq_single]
  simp

theorem born_basisDensity (A : Matrix ι ι ℂ) (i : ι) :
    Matrix.trace (A * basisDensity i) = A i i := by
  rw [basisDensity_eq_single, Matrix.trace_mul_single]
  simp

def pairKet (i k : ι) (z : ℂ) : ι → ℂ :=
  fun a => c * (basis i a + z * basis k a)

def pairDensity (i k : ι) (z : ℂ) : Matrix ι ι ℂ :=
  Matrix.vecMulVec (pairKet i k z) (fun a => conj (pairKet i k z a))

theorem pairDensity_positive (i k : ι) (z : ℂ) : (pairDensity i k z).PosSemidef := by
  change (Matrix.vecMulVec (pairKet i k z) (star (pairKet i k z))).PosSemidef
  exact Matrix.posSemidef_vecMulVec_self_star _

omit [Fintype ι] in
theorem pairDensity_expansion (i k : ι) (z : ℂ) :
    pairDensity i k z = (1 / 2 : ℂ) •
      (unitMatrix i i + z • unitMatrix k i + conj z • unitMatrix i k +
        (z * conj z) • unitMatrix k k) := by
  ext a b
  simp only [pairDensity, pairKet, unitMatrix, Matrix.vecMulVec_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, map_mul, map_add,
    conj_c, conj_basis]
  ring_nf
  simp only [c_sq]
  ring

theorem born_unitMatrix (A : Matrix ι ι ℂ) (i k : ι) :
    Matrix.trace (A * unitMatrix i k) = A k i := by
  rw [unitMatrix_eq_single, Matrix.trace_mul_single]
  simp

theorem born_pairDensity (A : Matrix ι ι ℂ) (i k : ι) (z : ℂ) :
    Matrix.trace (A * pairDensity i k z) = (1 / 2 : ℂ) *
      (A i i + z * A i k + conj z * A k i + (z * conj z) * A k k) := by
  rw [pairDensity_expansion]
  simp [Matrix.mul_add, Matrix.trace_smul, born_unitMatrix, smul_eq_mul]
  ring

theorem pairDensity_normalized (i k : ι) (hik : i ≠ k) (z : ℂ)
    (hz : z * conj z = 1) : Matrix.trace (pairDensity i k z) = 1 := by
  have h := born_pairDensity (1 : Matrix ι ι ℂ) i k z
  norm_num [Matrix.one_apply, hik, Ne.symm hik, hz] at h
  exact h

def phase : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]

theorem phase_unit (s : Fin 4) : phase s * conj (phase s) = 1 := by
  fin_cases s <;> norm_num [phase, Complex.conj_I, map_neg, Complex.I_sq]

def probeDensity (i k : ι) (s : Fin 4) : Matrix ι ι ℂ := pairDensity i k (phase s)

theorem probeDensity_positive (i k : ι) (s : Fin 4) : (probeDensity i k s).PosSemidef :=
  pairDensity_positive i k (phase s)

theorem probeDensity_normalized (i k : ι) (hik : i ≠ k) (s : Fin 4) :
    Matrix.trace (probeDensity i k s) = 1 :=
  pairDensity_normalized i k hik (phase s) (phase_unit s)

theorem entry_reconstruction (A : Matrix ι ι ℂ) (i k : ι) :
    A i k = (1 / 2 : ℂ) *
      ((Matrix.trace (A * probeDensity i k 0) - Matrix.trace (A * probeDensity i k 1)) -
        Complex.I * (Matrix.trace (A * probeDensity i k 2) -
          Matrix.trace (A * probeDensity i k 3))) := by
  simp only [probeDensity, born_pairDensity]
  norm_num [phase, Complex.conj_I, map_neg]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem effect_tomography (A B : Matrix ι ι ℂ)
    (hBorn : ∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → Matrix.trace ρ = 1 →
      Matrix.trace (A * ρ) = Matrix.trace (B * ρ)) : A = B := by
  ext i k
  by_cases hik : i = k
  · subst k
    simpa only [born_basisDensity] using
      hBorn (basisDensity i) (basisDensity_positive i) (basisDensity_normalized i)
  · have hp (s : Fin 4) : Matrix.trace (A * probeDensity i k s) =
        Matrix.trace (B * probeDensity i k s) :=
      hBorn (probeDensity i k s) (probeDensity_positive i k s)
        (probeDensity_normalized i k hik s)
    rw [entry_reconstruction A i k, entry_reconstruction B i k]
    simp only [hp]

theorem hermitian_effect_tomography (A B : Matrix ι ι ℂ)
    (_hA : A.IsHermitian) (_hB : B.IsHermitian)
    (hBorn : ∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → Matrix.trace ρ = 1 →
      Matrix.trace (A * ρ) = Matrix.trace (B * ρ)) : A = B :=
  effect_tomography A B hBorn

variable [Fintype Label] [DecidableEq Label]

def sharedProjector (j : Label) : Matrix (Label × Label) (Label × Label) ℂ :=
  Matrix.diagonal (fun x => if x = (j, j) then 1 else 0)

def measurementChannel (E : Label → Matrix ι ι ℂ) (ρ : Matrix ι ι ℂ) :
    Matrix (Label × Label) (Label × Label) ℂ :=
  ∑ j : Label, Matrix.trace (E j * ρ) • sharedProjector j

omit [DecidableEq ι] in
theorem measurementChannel_entry (E : Label → Matrix ι ι ℂ) (ρ : Matrix ι ι ℂ) (j : Label) :
    measurementChannel E ρ (j, j) (j, j) = Matrix.trace (E j * ρ) := by
  simp [measurementChannel, sharedProjector, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, mul_ite]

theorem measurementChannel_exact_iff_effects (E F : Label → Matrix ι ι ℂ) :
    (∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → Matrix.trace ρ = 1 →
      measurementChannel E ρ = measurementChannel F ρ) ↔ E = F := by
  constructor
  · intro h
    funext j
    apply effect_tomography
    intro ρ hρ ht
    have he := congrArg (fun M : Matrix (Label × Label) (Label × Label) ℂ => M (j, j) (j, j)) (h ρ hρ ht)
    simpa only [measurementChannel_entry] using he
  · rintro rfl
    exact fun _ _ _ => rfl

omit [DecidableEq ι] in
theorem measurementChannel_continuous (ρ : Matrix ι ι ℂ) :
    Continuous (fun E : Label → Matrix ι ι ℂ => measurementChannel E ρ) := by
  unfold measurementChannel
  fun_prop

omit [DecidableEq ι] in
theorem effects_tendsto_implies_measurementChannel
    (l : Filter α) (E : α → Label → Matrix ι ι ℂ) (F : Label → Matrix ι ι ℂ)
    (hE : ∀ j, Filter.Tendsto (fun a => E a j) l (𝓝 (F j))) (ρ : Matrix ι ι ℂ) :
    Filter.Tendsto (fun a => measurementChannel (E a) ρ) l
      (𝓝 (measurementChannel F ρ)) := by
  exact (measurementChannel_continuous ρ).tendsto F |>.comp (tendsto_pi_nhds.mpr hE)

theorem measurementChannel_tendsto_implies_effects
    (l : Filter α) (E : α → Label → Matrix ι ι ℂ) (F : Label → Matrix ι ι ℂ)
    (hChannel : ∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → Matrix.trace ρ = 1 →
      Filter.Tendsto (fun a => measurementChannel (E a) ρ) l
        (𝓝 (measurementChannel F ρ))) :
    ∀ j, Filter.Tendsto (fun a => E a j) l (𝓝 (F j)) := by
  have hBorn (j : Label) (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef)
      (ht : Matrix.trace ρ = 1) :
      Filter.Tendsto (fun a => Matrix.trace (E a j * ρ)) l
        (𝓝 (Matrix.trace (F j * ρ))) := by
    have he := ((hChannel ρ hρ ht).apply_nhds (j, j)).apply_nhds (j, j)
    simpa only [measurementChannel_entry] using he
  intro j
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro k
  by_cases hik : i = k
  · subst k
    simpa only [born_basisDensity] using
      hBorn j (basisDensity i) (basisDensity_positive i) (basisDensity_normalized i)
  · have hp (s : Fin 4) := hBorn j (probeDensity i k s)
        (probeDensity_positive i k s) (probeDensity_normalized i k hik s)
    have hhalf : Filter.Tendsto (fun _ : α => (1 / 2 : ℂ)) l (𝓝 (1 / 2 : ℂ)) :=
      tendsto_const_nhds
    have hI : Filter.Tendsto (fun _ : α => Complex.I) l (𝓝 Complex.I) :=
      tendsto_const_nhds
    have he := hhalf.mul ((hp 0 |>.sub (hp 1)).sub (hI.mul (hp 2 |>.sub (hp 3))))
    simpa only [← entry_reconstruction] using he

theorem measurementChannel_tendsto_iff_effects
    (l : Filter α) (E : α → Label → Matrix ι ι ℂ) (F : Label → Matrix ι ι ℂ) :
    (∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → Matrix.trace ρ = 1 →
      Filter.Tendsto (fun a => measurementChannel (E a) ρ) l
        (𝓝 (measurementChannel F ρ))) ↔
    (∀ j, Filter.Tendsto (fun a => E a j) l (𝓝 (F j))) := by
  constructor
  · exact measurementChannel_tendsto_implies_effects l E F
  · intro h ρ _ _
    exact effects_tendsto_implies_measurementChannel l E F h ρ

variable [Fintype κ]

def compressedEffects (J : Matrix κ ι ℂ) (F : Label → Matrix κ κ ℂ) : Label → Matrix ι ι ℂ :=
  fun j => J.conjTranspose * F j * J

def resourceMeasurementChannel (J : Matrix κ ι ℂ) (F : Label → Matrix κ κ ℂ)
    (ρ : Matrix ι ι ℂ) : Matrix (Label × Label) (Label × Label) ℂ :=
  ∑ j : Label, Matrix.trace (F j * (J * ρ * J.conjTranspose)) • sharedProjector j

omit [DecidableEq ι] in
theorem trace_resource_compression (J : Matrix κ ι ℂ) (F : Matrix κ κ ℂ)
    (ρ : Matrix ι ι ℂ) :
    Matrix.trace (F * (J * ρ * J.conjTranspose)) =
      Matrix.trace ((J.conjTranspose * F * J) * ρ) := by
  calc
    _ = Matrix.trace ((F * J * ρ) * J.conjTranspose) := by simp [Matrix.mul_assoc]
    _ = Matrix.trace (J.conjTranspose * (F * J * ρ)) := Matrix.trace_mul_comm _ _
    _ = _ := by simp [Matrix.mul_assoc]

omit [DecidableEq ι] in
theorem resourceMeasurementChannel_eq_compressed (J : Matrix κ ι ℂ)
    (F : Label → Matrix κ κ ℂ) (ρ : Matrix ι ι ℂ) :
    resourceMeasurementChannel J F ρ = measurementChannel (compressedEffects J F) ρ := by
  simp only [resourceMeasurementChannel, measurementChannel, compressedEffects,
    trace_resource_compression]

theorem resourceChannel_exact_iff_compressed (J : Matrix κ ι ℂ)
    (F : Label → Matrix κ κ ℂ) (E : Label → Matrix ι ι ℂ) :
    (∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → Matrix.trace ρ = 1 →
      resourceMeasurementChannel J F ρ = measurementChannel E ρ) ↔
      compressedEffects J F = E := by
  simp only [resourceMeasurementChannel_eq_compressed]
  exact measurementChannel_exact_iff_effects _ _

theorem resourceChannel_tendsto_iff_compressed
    (l : Filter α) (J : Matrix κ ι ℂ) (F : α → Label → Matrix κ κ ℂ)
    (E : Label → Matrix ι ι ℂ) :
    (∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → Matrix.trace ρ = 1 →
      Filter.Tendsto (fun a => resourceMeasurementChannel J (F a) ρ) l
        (𝓝 (measurementChannel E ρ))) ↔
    (∀ j, Filter.Tendsto (fun a => J.conjTranspose * F a j * J) l (𝓝 (E j))) := by
  simpa only [resourceMeasurementChannel_eq_compressed, compressedEffects] using
    measurementChannel_tendsto_iff_effects l (fun a => compressedEffects J (F a)) E

theorem resourceChannel_tendsto_iff_varying_compressed
    (l : Filter α) (J : α → Matrix κ ι ℂ) (F : α → Label → Matrix κ κ ℂ)
    (E : Label → Matrix ι ι ℂ) :
    (∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → Matrix.trace ρ = 1 →
      Filter.Tendsto (fun a => resourceMeasurementChannel (J a) (F a) ρ) l
        (𝓝 (measurementChannel E ρ))) ↔
    (∀ j, Filter.Tendsto (fun a => (J a).conjTranspose * F a j * J a) l (𝓝 (E j))) := by
  simpa only [resourceMeasurementChannel_eq_compressed, compressedEffects] using
    measurementChannel_tendsto_iff_effects l (fun a => compressedEffects (J a) (F a)) E

theorem physicalClassicalChannel_eq_measurement
    (ρ : Matrix SystemIndex SystemIndex ℂ) :
    physicalClassicalChannel ρ = measurementChannel represented_physicalEffect ρ := rfl

theorem ejm_density_exactness_implies_compressed_effects
    (J : Matrix κ SystemIndex ℂ) (F : Fin 4 → Matrix κ κ ℂ)
    (hChannel : ∀ ρ : Matrix SystemIndex SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      resourceMeasurementChannel J F ρ = physicalClassicalChannel ρ) :
    ∀ j, J.conjTranspose * F j * J = represented_physicalEffect j := by
  have h := (resourceChannel_exact_iff_compressed J F represented_physicalEffect).mp
    (fun ρ hρ ht => by
      simpa only [← physicalClassicalChannel_eq_measurement] using hChannel ρ hρ ht)
  intro j
  exact congrFun h j

theorem ejm_density_channel_tendsto_implies_compressed_effects
    (l : Filter α) (J : Matrix κ SystemIndex ℂ) (F : α → Fin 4 → Matrix κ κ ℂ)
    (hChannel : ∀ ρ : Matrix SystemIndex SystemIndex ℂ,
      ρ.PosSemidef → Matrix.trace ρ = 1 →
      Filter.Tendsto (fun a => resourceMeasurementChannel J (F a) ρ) l
        (𝓝 (physicalClassicalChannel ρ))) :
    ∀ j, Filter.Tendsto (fun a => J.conjTranspose * F a j * J) l
      (𝓝 (represented_physicalEffect j)) := by
  exact (resourceChannel_tendsto_iff_compressed l J F represented_physicalEffect).mp
    (fun ρ hρ ht => by
      simpa only [← physicalClassicalChannel_eq_measurement] using hChannel ρ hρ ht)

end

end QuantumProver.ElegantJointMeasurement.Teleportation.Tomography

namespace QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper

open scoped BigOperators ComplexConjugate ComplexOrder Matrix
open InnerProductSpace

noncomputable section

set_option maxHeartbeats 600000

def oneEbitBeta : Q → ℝ := fun _ => resourceScale

theorem oneEbitBeta_positive (q : Q) : 0 < oneEbitBeta q := resourceScale_pos

theorem oneEbitBeta_normalized : ∑ q : Q, oneEbitBeta q ^ 2 = 1 := by
  norm_num [oneEbitBeta, resourceScale_sq, Fin.sum_univ_two]

theorem oneEbitBeta_resourceCoefficient :
    QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient oneEbitBeta = resource := by
  rw [QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient_eq_diagonal, resource_diagonal]
  rfl

theorem one_ebit_alice_reduced_density :
    QuantumProver.ElegantJointMeasurement.Concurrence.IsDensity (resource * resource.conjTranspose) := by
  rw [← oneEbitBeta_resourceCoefficient, QuantumProver.ElegantJointMeasurement.TailReference.resource_leftGram_eq_resourceGram]
  exact QuantumProver.ElegantJointMeasurement.TailReference.resourceGram_isDensity oneEbitBeta oneEbitBeta_normalized

theorem one_ebit_alice_reduced_entropy :
    QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (resource * resource.conjTranspose) = 1 := by
  rw [← oneEbitBeta_resourceCoefficient,
    QuantumProver.ElegantJointMeasurement.TailReference.resource_left_vonNeumannEntropy_eq_entropyBits]
  simpa only [QuantumProver.ElegantJointMeasurement.Entropy.entropyBits, oneEbitBeta, resourceScale_sq,
    resourceEntropyBits, schmidtWeight] using resource_entropy_one

def alicePhysicalEquiv : (Fin 2 × Q) ≃ Fin 4 := systemFinEquiv
def bobPhysicalEquiv : (Fin 2 × Q) ≃ Fin 4 := bobInputResourceFinEquiv

theorem oneEbitFiniteTree_length : oneEbitFiniteTree.terminalBraPairs.length = 16 := by
  rw [oneEbitFiniteTree_terminal_records]
  simp [List.ofFn_succ]

def branchLabelEquiv : (Fin 4 × Fin 4) ≃ Fin 16 := finProdFinEquiv

def occurrenceEquiv : Fin oneEbitFiniteTree.terminalBraPairs.length ≃ (Fin 4 × Fin 4) :=
  (finCongr oneEbitFiniteTree_length).trans branchLabelEquiv.symm

def occurrenceReport (i : Fin oneEbitFiniteTree.terminalBraPairs.length) : Fin 4 :=
  (occurrenceEquiv i).2

theorem oneEbitFiniteTree_terminal_ofFn :
    oneEbitFiniteTree.terminalBraPairs = List.ofFn (fun t : Fin 16 =>
      finiteBranchPair (branchLabelEquiv.symm t).1 (branchLabelEquiv.symm t).2) := by
  rw [oneEbitFiniteTree_terminal_records]
  symm
  rw [List.ofFn_mul (m := 4) (n := 4)]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext m
  apply congrArg List.ofFn
  funext j
  have hindex :
      (⟨m.val * 4 + j.val, by omega⟩ : Fin 16) = branchLabelEquiv (m, j) := by
    apply Fin.ext
    simp [branchLabelEquiv, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  simp only [hindex, Equiv.symm_apply_apply]

theorem occurrence_terminal_pair (i : Fin oneEbitFiniteTree.terminalBraPairs.length) :
    oneEbitFiniteTree.terminalBraPairs.get i =
      finiteBranchPair (occurrenceEquiv i).1 (occurrenceEquiv i).2 := by
  have h16 : i.val < 16 := by
    simpa only [oneEbitFiniteTree_length] using i.isLt
  change oneEbitFiniteTree.terminalBraPairs.get i =
    finiteBranchPair (branchLabelEquiv.symm ⟨i.val, h16⟩).1
      (branchLabelEquiv.symm ⟨i.val, h16⟩).2
  apply Option.some.inj
  have hget := congrArg (fun l : List (QuantumProver.ElegantJointMeasurement.Concurrence.SystemBraPair 4 4) => l[i.val]?)
    oneEbitFiniteTree_terminal_ofFn
  simpa only [List.getElem?_eq_getElem i.isLt, List.getElem?_ofFn, dite_eq_left h16,
    List.get_eq_getElem] using hget

theorem groupedEffect_eq_matrix_pullback (j : Fin 4) :
    QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect oneEbitFiniteTree alicePhysicalEquiv bobPhysicalEquiv
      occurrenceReport j =
      QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect alicePhysicalEquiv bobPhysicalEquiv (matrixCoarseEffect j) := by
  unfold QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect QuantumProver.ElegantJointMeasurement.ProtocolEffects.outcomeSum
  rw [← occurrenceEquiv.symm.sum_comp]
  simp only [occurrence_terminal_pair, occurrenceReport, Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  simp only [QuantumProver.ElegantJointMeasurement.ProtocolEffects.physicalEffect_eq_pullback]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← map_sum]
  rfl

def physicalEmbedding : Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index Q) SystemIndex ℂ :=
  matrixResourceEmbedding.submatrix (alicePhysicalEquiv.prodCongr bobPhysicalEquiv) id

theorem physicalEmbedding_entry (z : QuantumProver.ElegantJointMeasurement.Augmented.Index Q) (i : SystemIndex) :
    physicalEmbedding z i =
      if z.1.2 = z.2.2 then c * (if (z.1.1, z.2.1) = i then 1 else 0) else 0 := by
  rcases z with ⟨⟨a, s⟩, ⟨b, r⟩⟩
  rcases i with ⟨i, k⟩
  by_cases hs : s = r <;> by_cases ha : a = i <;> by_cases hb : b = k <;>
    simp [physicalEmbedding, matrixResourceEmbedding, alicePhysicalEquiv,
    bobPhysicalEquiv, bobInputResourceFinEquiv, matrixExtendedEquiv,
    resourceEmbedding, flattenSharedInput, sharedInput, basisCoefficient,
    resource, hs, ha, hb]

theorem physicalEmbedding_mulVec (E : QuantumProver.ElegantJointMeasurement.ResourceCode.InputSpace Q Q) :
    Matrix.mulVec physicalEmbedding E.ofLp =
      (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous oneEbitBeta E).ofLp := by
  ext z
  rcases z with ⟨⟨a, s⟩, ⟨b, r⟩⟩
  simp only [Matrix.mulVec, dotProduct, physicalEmbedding_entry,
    QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous_apply, QuantumProver.ElegantJointMeasurement.ResourceCode.codeLinear_apply, oneEbitBeta]
  by_cases h : s = r
  · simp [h, c, mul_ite]
  · simp [h]

theorem physical_codeContinuous_eq_matrix :
    QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous (a := Q) (b := Q) oneEbitBeta =
      (Matrix.toEuclideanLin physicalEmbedding).toContinuousLinearMap := by
  ext E z
  change (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous oneEbitBeta E) z =
    (Matrix.mulVec physicalEmbedding E.ofLp) z
  rw [physicalEmbedding_mulVec]

theorem physical_grouped_compression (j : Fin 4) :
    physicalEmbedding.conjTranspose *
      QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect oneEbitFiniteTree alicePhysicalEquiv bobPhysicalEquiv
        occurrenceReport j * physicalEmbedding = represented_physicalEffect j := by
  rw [groupedEffect_eq_matrix_pullback]
  change (matrixResourceEmbedding.submatrix (alicePhysicalEquiv.prodCongr bobPhysicalEquiv) id).conjTranspose *
      (matrixCoarseEffect j).submatrix (alicePhysicalEquiv.prodCongr bobPhysicalEquiv)
        (alicePhysicalEquiv.prodCongr bobPhysicalEquiv) *
      matrixResourceEmbedding.submatrix (alicePhysicalEquiv.prodCongr bobPhysicalEquiv) id = represented_physicalEffect j
  simp only [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  exact finite_tree_effect_eq_physical j

def unitDirection (j : Fin 4) (a : Fin 3) : ℝ := tetrahedron j a / Real.sqrt 3

theorem unitDirection_scaled (j : Fin 4) (a : Fin 3) :
    Real.sqrt 3 * unitDirection j a = tetrahedron j a := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  unfold unitDirection
  field_simp

theorem unitDirection_sphere (j : Fin 4) :
    unitDirection j 0 ^ 2 + unitDirection j 1 ^ 2 + unitDirection j 2 ^ 2 = 1 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases j <;> norm_num [unitDirection, tetrahedron, div_pow, hs]

theorem directionKet_eq_physical (j : Fin 4) :
    QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (unitDirection j 0) (unitDirection j 1) (unitDirection j 2) =
      QuantumProver.ElegantJointMeasurement.ResourceCode.ejmKet (tetrahedron j 0) (tetrahedron j 1) (tetrahedron j 2) := by
  rw [QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet_eq_scaled_ejmKet, unitDirection_scaled,
    unitDirection_scaled, unitDirection_scaled]

theorem physicalEffect_operator (j : Fin 4) :
    (Matrix.toEuclideanLin (represented_physicalEffect j)).toContinuousLinearMap =
      rankOne ℂ
        (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (unitDirection j 0) (unitDirection j 1) (unitDirection j 2))
        (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (unitDirection j 0) (unitDirection j 1) (unitDirection j 2)) := by
  rw [directionKet_eq_physical]
  have h : represented_physicalEffect j = Matrix.toEuclideanLin.symm
      (rankOne ℂ (QuantumProver.ElegantJointMeasurement.ResourceCode.ejmKet (tetrahedron j 0) (tetrahedron j 1) (tetrahedron j 2))
        (QuantumProver.ElegantJointMeasurement.ResourceCode.ejmKet (tetrahedron j 0) (tetrahedron j 1) (tetrahedron j 2))).toLinearMap := by
    rw [InnerProductSpace.symm_toEuclideanLin_rankOne]
    rfl
  rw [h, LinearEquiv.apply_symm_apply]
  apply ContinuousLinearMap.coe_injective
  rfl

theorem one_ebit_grouped_code_compression (j : Fin 4) :
    (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous oneEbitBeta).adjoint ∘L
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator
        (QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect oneEbitFiniteTree alicePhysicalEquiv bobPhysicalEquiv
          occurrenceReport j) ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous oneEbitBeta) =
      rankOne ℂ
        (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (unitDirection j 0) (unitDirection j 1) (unitDirection j 2))
        (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (unitDirection j 0) (unitDirection j 1) (unitDirection j 2)) := by
  have hmatrix : (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous oneEbitBeta).adjoint ∘L
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator
        (QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect oneEbitFiniteTree alicePhysicalEquiv bobPhysicalEquiv
          occurrenceReport j) ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous oneEbitBeta) =
      (Matrix.toEuclideanLin (physicalEmbedding.conjTranspose *
        QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect oneEbitFiniteTree alicePhysicalEquiv bobPhysicalEquiv
          occurrenceReport j * physicalEmbedding)).toContinuousLinearMap := by
    rw [physical_codeContinuous_eq_matrix, ← LinearMap.adjoint_toContinuousLinearMap,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    ext E z
    change (physicalEmbedding.conjTranspose *ᵥ
      ((QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect oneEbitFiniteTree alicePhysicalEquiv bobPhysicalEquiv
        occurrenceReport j) *ᵥ (physicalEmbedding *ᵥ E.ofLp))) z =
      ((physicalEmbedding.conjTranspose *
        QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect oneEbitFiniteTree alicePhysicalEquiv bobPhysicalEquiv
          occurrenceReport j * physicalEmbedding) *ᵥ E.ofLp) z
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hmatrix, physical_grouped_compression, physicalEffect_operator]

theorem one_ebit_physical_shared_channel (ρ : Matrix SystemIndex SystemIndex ℂ) :
    Tomography.resourceMeasurementChannel physicalEmbedding
      (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect oneEbitFiniteTree alicePhysicalEquiv bobPhysicalEquiv
        occurrenceReport j) ρ = Tomography.measurementChannel represented_physicalEffect ρ := by
  rw [Tomography.resourceMeasurementChannel_eq_compressed]
  have h : Tomography.compressedEffects physicalEmbedding
      (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect oneEbitFiniteTree alicePhysicalEquiv bobPhysicalEquiv
        occurrenceReport j) = represented_physicalEffect := by
    funext j
    exact physical_grouped_compression j
  rw [h]

structure OneEbitPhysicalUpperCertificate : Prop where
  actual_finite_protocol : OneEbitFiniteProtocolCertificate
  positive_amplitudes : ∀ q, 0 < oneEbitBeta q
  normalized_amplitudes : ∑ q, oneEbitBeta q ^ 2 = 1
  physical_resource : QuantumProver.ElegantJointMeasurement.TailReference.resourceCoefficient oneEbitBeta = resource
  alice_reduced_density : QuantumProver.ElegantJointMeasurement.Concurrence.IsDensity (resource * resource.conjTranspose)
  alice_reduced_entropy :
    QuantumProver.ElegantJointMeasurement.TailReference.vonNeumannEntropyBits (resource * resource.conjTranspose) = 1
  literal_occurrence_labels : ∀ i,
    oneEbitFiniteTree.terminalBraPairs.get i =
      finiteBranchPair (occurrenceEquiv i).1 (occurrenceEquiv i).2
  normalized_directions : ∀ j,
    unitDirection j 0 ^ 2 + unitDirection j 1 ^ 2 + unitDirection j 2 ^ 2 = 1
  complete_grouped_effects :
    ∑ j, QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect oneEbitFiniteTree alicePhysicalEquiv bobPhysicalEquiv
      occurrenceReport j = 1
  physical_resource_code : QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous (a := Q) (b := Q) oneEbitBeta =
    (Matrix.toEuclideanLin physicalEmbedding).toContinuousLinearMap
  code_isometry : ∀ E : QuantumProver.ElegantJointMeasurement.ResourceCode.InputSpace Q Q,
    ‖QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous oneEbitBeta E‖ = ‖E‖
  represented_physical_grouped_compression : ∀ j,
    (QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous oneEbitBeta).adjoint ∘L
      (QuantumProver.ElegantJointMeasurement.ClosureJoin.effectOperator
        (QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect oneEbitFiniteTree alicePhysicalEquiv bobPhysicalEquiv
          occurrenceReport j) ∘L QuantumProver.ElegantJointMeasurement.ResourceCode.codeContinuous oneEbitBeta) =
      rankOne ℂ
        (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (unitDirection j 0) (unitDirection j 1) (unitDirection j 2))
        (QuantumProver.ElegantJointMeasurement.ClosureJoin.directionKet (unitDirection j 0) (unitDirection j 1) (unitDirection j 2))
  density_shared_channel : ∀ ρ : Matrix SystemIndex SystemIndex ℂ,
    ρ.PosSemidef → Matrix.trace ρ = 1 →
      Tomography.resourceMeasurementChannel physicalEmbedding
        (fun j => QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect oneEbitFiniteTree alicePhysicalEquiv bobPhysicalEquiv
          occurrenceReport j) ρ = physicalClassicalChannel ρ

theorem one_ebit_physical_upper_certificate : OneEbitPhysicalUpperCertificate where
  actual_finite_protocol := one_ebit_finite_locc_protocol_certificate
  positive_amplitudes := oneEbitBeta_positive
  normalized_amplitudes := oneEbitBeta_normalized
  physical_resource := oneEbitBeta_resourceCoefficient
  alice_reduced_density := one_ebit_alice_reduced_density
  alice_reduced_entropy := one_ebit_alice_reduced_entropy
  literal_occurrence_labels := occurrence_terminal_pair
  normalized_directions := unitDirection_sphere
  complete_grouped_effects :=
    QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect_sum oneEbitFiniteTree alicePhysicalEquiv bobPhysicalEquiv occurrenceReport
  physical_resource_code := physical_codeContinuous_eq_matrix
  code_isometry := QuantumProver.ElegantJointMeasurement.ResourceCode.code_norm oneEbitBeta oneEbitBeta_normalized
  represented_physical_grouped_compression := one_ebit_grouped_code_compression
  density_shared_channel := fun ρ _ _ =>
    (one_ebit_physical_shared_channel ρ).trans
      (Tomography.physicalClassicalChannel_eq_measurement ρ).symm

end

end QuantumProver.ElegantJointMeasurement.Teleportation.PhysicalUpper

namespace QuantumProver.ElegantJointMeasurement.Teleportation.ClassicalOutputRepair

open scoped BigOperators ComplexConjugate ComplexOrder Kronecker Matrix Topology

noncomputable section

set_option maxHeartbeats 600000

abbrev Label := Fin 4
abbrev OutputIndex := Label × Label
abbrev OutputMatrix := Matrix OutputIndex OutputIndex ℂ

def aliceProjector (a : Label) : Matrix Label Label ℂ := Matrix.single a a 1
def bobReset (a b : Label) : Matrix Label Label ℂ := Matrix.single a b 1

theorem aliceProjector_complete :
    ∑ a, (aliceProjector a).conjTranspose * aliceProjector a = 1 := by
  simp [aliceProjector, Matrix.sum_single_one]

theorem bobReset_complete (a : Label) :
    ∑ b, (bobReset a b).conjTranspose * bobReset a b = 1 := by
  simp [bobReset, Matrix.sum_single_one]

def copyKraus (q : OutputIndex) : Matrix OutputIndex OutputIndex ℂ :=
  aliceProjector q.1 ⊗ₖ bobReset q.1 q.2

theorem copyKraus_eq_single (q : OutputIndex) :
    copyKraus q = Matrix.single (q.1, q.1) q 1 := by
  simp [copyKraus, aliceProjector, bobReset, Matrix.single_kronecker_single]

theorem copyKraus_complete : ∑ q, (copyKraus q).conjTranspose * copyKraus q = 1 := by
  simp [copyKraus_eq_single, Matrix.sum_single_one]

def repairKrausTree : QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree 4 4 :=
  .alice 4 4 4 4 aliceProjector aliceProjector_complete (fun a =>
    .bob 4 4 4 4 (bobReset a) (bobReset_complete a) (fun _ => .leaf 4 4))

def copyAlice : OutputMatrix →ₗ[ℂ] OutputMatrix := QuantumProver.ElegantJointMeasurement.CP.krausMap copyKraus

theorem copyAlice_completelyPositive : QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive copyAlice :=
  QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive copyKraus

theorem copyAlice_trace_preserving (X : OutputMatrix) :
    Matrix.trace (copyAlice X) = Matrix.trace X :=
  (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff copyKraus).mpr copyKraus_complete X

theorem copyAlice_positive (X : OutputMatrix) (hX : X.PosSemidef) :
    (copyAlice X).PosSemidef := by
  change (∑ q, copyKraus q * X * (copyKraus q).conjTranspose).PosSemidef
  apply Matrix.posSemidef_sum
  intro q _
  exact hX.mul_mul_conjTranspose_same (copyKraus q)

theorem single_sandwich {I O : Type*} [Fintype I] [DecidableEq I] [DecidableEq O]
    (o : O) (i : I) (X : Matrix I I ℂ) :
    Matrix.single o i (1 : ℂ) * X * (Matrix.single o i (1 : ℂ)).conjTranspose =
      X i i • Matrix.single o o 1 := by
  simp [Matrix.smul_single]

theorem sharedProjector_eq_single (a : Label) :
    Tomography.sharedProjector a = Matrix.single (a, a) (a, a) (1 : ℂ) := by
  unfold Tomography.sharedProjector
  rw [← Matrix.diagonal_single]
  congr 1
  ext x
  simp [Pi.single_apply]

theorem copyAlice_eq_marginal_diagonal (X : OutputMatrix) :
    copyAlice X = ∑ a : Label, (∑ b : Label, X (a, b) (a, b)) • Tomography.sharedProjector a := by
  change (∑ q, copyKraus q * X * (copyKraus q).conjTranspose) = _
  simp_rw [copyKraus_eq_single, single_sandwich, ← sharedProjector_eq_single]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_smul]

theorem copyAlice_born_trace (X : OutputMatrix) (a : Label) :
    copyAlice X (a, a) (a, a) = ∑ b : Label, X (a, b) (a, b) := by
  rw [copyAlice_eq_marginal_diagonal]
  simp [Tomography.sharedProjector, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, mul_ite]

theorem copyAlice_pairProjector (a b : Label) :
    copyAlice (Matrix.single (a, b) (a, b) (1 : ℂ)) = Tomography.sharedProjector a := by
  rw [copyAlice_eq_marginal_diagonal]
  have hweight (i : Label) :
      (∑ r : Label, Matrix.single (a, b) (a, b) (1 : ℂ) (i, r) (i, r)) =
        if i = a then 1 else 0 := by
    by_cases h : i = a
    · subst i
      simp [Matrix.single_apply]
    · simp [h, Ne.symm h]
  simp_rw [hweight]
  simp

theorem copyAlice_sharedProjector (a : Label) :
    copyAlice (Tomography.sharedProjector a) = Tomography.sharedProjector a := by
  exact (congrArg copyAlice (sharedProjector_eq_single a)).trans (copyAlice_pairProjector a a)

theorem copyAlice_fixed_measurementChannel {ι : Type*} [Fintype ι]
    (E : Label → Matrix ι ι ℂ) (ρ : Matrix ι ι ℂ) :
    copyAlice (Tomography.measurementChannel E ρ) = Tomography.measurementChannel E ρ := by
  simp only [Tomography.measurementChannel, map_sum, map_smul, copyAlice_sharedProjector]

theorem copyAlice_fixed_physicalClassicalChannel (ρ : Matrix SystemIndex SystemIndex ℂ) :
    copyAlice (physicalClassicalChannel ρ) = physicalClassicalChannel ρ := by
  rw [Tomography.physicalClassicalChannel_eq_measurement, copyAlice_fixed_measurementChannel]

theorem copyAlice_continuous : Continuous copyAlice := by
  change Continuous (fun X : OutputMatrix => ∑ q, copyKraus q * X * (copyKraus q).conjTranspose)
  fun_prop

def aliceCP (a : Label) : Matrix Label Label ℂ →ₗ[ℂ] Matrix Label Label ℂ :=
  QuantumProver.ElegantJointMeasurement.CP.sandwichMap (aliceProjector a)

def bobCP (a b : Label) : Matrix Label Label ℂ →ₗ[ℂ] Matrix Label Label ℂ :=
  QuantumProver.ElegantJointMeasurement.CP.sandwichMap (bobReset a b)

theorem aliceCP_completelyPositive (a : Label) : QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (aliceCP a) :=
  QuantumProver.ElegantJointMeasurement.CP.sandwichMap_completelyPositive _

theorem bobCP_completelyPositive (a b : Label) : QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (bobCP a b) :=
  QuantumProver.ElegantJointMeasurement.CP.sandwichMap_completelyPositive _

theorem aliceCP_trace (X : Matrix Label Label ℂ) : (∑ a, aliceCP a X).trace = X.trace := by
  have h : (∑ a, aliceCP a X) = QuantumProver.ElegantJointMeasurement.CP.krausMap aliceProjector X := by
    simp [aliceCP, QuantumProver.ElegantJointMeasurement.CP.sandwichMap_apply, QuantumProver.ElegantJointMeasurement.CP.krausMap]
  rw [h]
  exact (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff aliceProjector).mpr aliceProjector_complete X

theorem bobCP_trace (a : Label) (X : Matrix Label Label ℂ) :
    (∑ b, bobCP a b X).trace = X.trace := by
  have h : (∑ b, bobCP a b X) = QuantumProver.ElegantJointMeasurement.CP.krausMap (bobReset a) X := by
    simp [bobCP, QuantumProver.ElegantJointMeasurement.CP.sandwichMap_apply, QuantumProver.ElegantJointMeasurement.CP.krausMap]
  rw [h]
  exact (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff (bobReset a)).mpr (bobReset_complete a) X

def repairCPTree : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree 4 4 :=
  .alice 4 4 4 4 aliceCP aliceCP_completelyPositive aliceCP_trace (fun a =>
    .bob 4 4 4 4 (bobCP a) (bobCP_completelyPositive a) (bobCP_trace a) (fun _ => .leaf 4 4))

def repairLabels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels repairCPTree Label :=
  fun a _ => a

theorem aliceCP_apply (a : Label) (M : Matrix Label Label ℂ) :
    aliceCP a M = M a a • aliceProjector a :=
  (QuantumProver.ElegantJointMeasurement.CP.sandwichMap_apply (aliceProjector a) M).trans (single_sandwich a a M)

theorem bobCP_apply (a b : Label) (M : Matrix Label Label ℂ) :
    bobCP a b M = M b b • aliceProjector a :=
  (QuantumProver.ElegantJointMeasurement.CP.sandwichMap_apply (bobReset a b) M).trans (single_sandwich a b M)

set_option backward.isDefEq.respectTransparency false in
theorem matrix_repair_branch (a b : Label) (X : OutputMatrix) :
    QuantumProver.ElegantJointMeasurement.CP.rightApplication (bobCP a b) (QuantumProver.ElegantJointMeasurement.CP.leftApplication (aliceCP a) X) =
      X (a, b) (a, b) • Tomography.sharedProjector a := by
  rw [sharedProjector_eq_single]
  ext x y
  rcases x with ⟨i, r⟩
  rcases y with ⟨j, s⟩
  change bobCP a b (fun u v => aliceCP a (fun p q => X (p, u) (q, v)) i j) r s = _
  rw [bobCP_apply, aliceCP_apply]
  simp only [aliceProjector, Matrix.smul_apply, smul_eq_mul]
  by_cases hi : a = i <;> by_cases hj : a = j <;>
    by_cases hr : a = r <;> by_cases hs : a = s <;>
      simp_all

set_option backward.isDefEq.respectTransparency false in
theorem matrix_repair_born (a : Label) (X : OutputMatrix) :
    repairCPTree.matrixReportedEvaluation repairLabels a X = ∑ b : Label, X (a, b) (a, b) := by
  simp only [repairCPTree, repairLabels, QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.matrixReportedEvaluation,
    LinearMap.sum_apply, LinearMap.comp_apply]
  simp_rw [matrix_repair_branch]
  have htrace (s b : Label) :
      (if s = a then Matrix.traceLinearMap OutputIndex ℂ ℂ else 0)
        (X (s, b) (s, b) • Tomography.sharedProjector s) =
        if s = a then X (s, b) (s, b) else 0 := by
    by_cases h : s = a <;> simp [h, sharedProjector_eq_single]
  simp_rw [htrace]
  simp

theorem copyAlice_eq_matrix_tree (X : OutputMatrix) :
    copyAlice X = ∑ a : Label, repairCPTree.matrixReportedEvaluation repairLabels a X •
      Tomography.sharedProjector a := by
  simp_rw [matrix_repair_born]
  exact copyAlice_eq_marginal_diagonal X

def mapLeafLabels {L M : Type*} (f : L → M) : {m n : ℕ} →
    (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n) →
    QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T L →
    QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T M
  | _, _, .leaf _ _, labels => f labels
  | _, _, .alice _ _ _ _ _ _ _ next, labels =>
      fun s => mapLeafLabels f (next s) (labels s)
  | _, _, .bob _ _ _ _ _ _ _ next, labels =>
      fun s => mapLeafLabels f (next s) (labels s)

theorem matrixReportedEvaluation_map {L M : Type*} [Fintype L] [DecidableEq L] [DecidableEq M]
    (f : L → M) {m n : ℕ} (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n) :
    ∀ (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T L) (j : M)
      (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ),
      T.matrixReportedEvaluation (mapLeafLabels f T labels) j X =
        ∑ ell : L, if f ell = j then T.matrixReportedEvaluation labels ell X else 0 := by
  induction T with
  | leaf m n =>
    intro labels j X
    rw [Finset.sum_eq_single labels]
    · by_cases h : f labels = j <;>
        simp [mapLeafLabels, QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.matrixReportedEvaluation, h]
    · intro ell _ hne
      simp [QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.matrixReportedEvaluation, Ne.symm hne]
    · simp
  | alice m n out outcomes Φ positive trace next ih =>
    intro labels j X
    simp only [mapLeafLabels, QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.matrixReportedEvaluation,
      LinearMap.sum_apply, LinearMap.comp_apply]
    simp_rw [ih]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ell _
    by_cases h : f ell = j <;> simp [h]
  | bob m n out outcomes Φ positive trace next ih =>
    intro labels j X
    simp only [mapLeafLabels, QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.matrixReportedEvaluation,
      LinearMap.sum_apply, LinearMap.comp_apply]
    simp_rw [ih]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ell _
    by_cases h : f ell = j <;> simp [h]

theorem reportedTerminalBraPairs_map {L M : Type*} (f : L → M) {m n : ℕ}
    (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n) :
    ∀ (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T L),
      T.reportedTerminalBraPairs (mapLeafLabels f T labels) =
        (T.reportedTerminalBraPairs labels).map (fun p => (p.1, f p.2)) := by
  induction T with
  | leaf m n =>
    intro labels
    simp [mapLeafLabels, QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.reportedTerminalBraPairs,
      List.map_map, Function.comp_def]
  | alice m n out outcomes Φ positive trace next ih =>
    intro labels
    simp only [mapLeafLabels, QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.reportedTerminalBraPairs]
    simp_rw [ih]
    simp only [List.map_flatten, List.map_ofFn, List.map_map, Function.comp_def]
  | bob m n out outcomes Φ positive trace next ih =>
    intro labels
    simp only [mapLeafLabels, QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.reportedTerminalBraPairs]
    simp_rw [ih]
    simp only [List.map_flatten, List.map_ofFn, List.map_map, Function.comp_def]

theorem terminalReport_map {L M : Type*} [DecidableEq L] [DecidableEq M]
    (f : L → M) {m n : ℕ}
    (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T L)
    (i : Fin T.krausRefinement.terminalBraPairs.length) :
    T.terminalReport (mapLeafLabels f T labels) i = f (T.terminalReport labels i) := by
  have hiL : i.val < (T.reportedTerminalBraPairs labels).length := by
    rw [T.reportedTerminalBraPairs_length labels]
    exact i.isLt
  have hiM : i.val < (T.reportedTerminalBraPairs (mapLeafLabels f T labels)).length := by
    rw [T.reportedTerminalBraPairs_length (mapLeafLabels f T labels)]
    exact i.isLt
  have h := congrArg (fun l => l[i.val]?) (reportedTerminalBraPairs_map f T labels)
  rw [List.getElem?_map] at h
  simp only [List.getElem?_eq_getElem hiL, List.getElem?_eq_getElem hiM,
    Option.map_some, Option.some.injEq] at h
  have hsnd := congrArg Prod.snd h
  simpa only [QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.terminalReport, List.get_eq_getElem,
    QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.terminalOccurrence_val] using hsnd

theorem matrixReportedEvaluation_fst {m n : ℕ}
    (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T OutputIndex)
    (a : Label) (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    T.matrixReportedEvaluation (mapLeafLabels Prod.fst T labels) a X =
      ∑ b : Label, T.matrixReportedEvaluation labels (a, b) X := by
  rw [matrixReportedEvaluation_map]
  rw [Fintype.sum_prod_type]
  have hf (s : Label) :
      (∑ b : Label, if s = a then T.matrixReportedEvaluation labels (s, b) X else 0) =
        if s = a then ∑ b : Label, T.matrixReportedEvaluation labels (s, b) X else 0 := by
    by_cases h : s = a <;> simp [h]
  simp_rw [hf]
  simp

theorem matrixReportedEffect_fst {m n : ℕ}
    (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T OutputIndex) (a : Label) :
    T.matrixReportedEffect (mapLeafLabels Prod.fst T labels) a =
      ∑ b : Label, T.matrixReportedEffect labels (a, b) := by
  symm
  apply T.matrixReportedEffect_unique
  intro X
  rw [Matrix.sum_mul, Matrix.trace_sum]
  simp_rw [← T.matrixReportedEvaluation_eq_trace_effect labels]
  exact (matrixReportedEvaluation_fst T labels a X).symm

def matrixPairedChannel {m n : ℕ} (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T OutputIndex)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : OutputMatrix :=
  ∑ a : Label, ∑ b : Label,
    T.matrixReportedEvaluation labels (a, b) X • Matrix.single (a, b) (a, b) 1

def matrixSharedChannel {m n : ℕ} (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T Label)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) : OutputMatrix :=
  ∑ a : Label, T.matrixReportedEvaluation labels a X • Tomography.sharedProjector a

theorem matrixSharedChannel_eq_measurement {m n : ℕ}
    (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T Label)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    matrixSharedChannel T labels X =
      Tomography.measurementChannel (T.matrixReportedEffect labels) X := by
  simp only [matrixSharedChannel, Tomography.measurementChannel,
    T.matrixReportedEvaluation_eq_trace_effect labels]

theorem copy_matrixPairedChannel_eq_fst {m n : ℕ}
    (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T OutputIndex)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    copyAlice (matrixPairedChannel T labels X) =
      matrixSharedChannel T (mapLeafLabels Prod.fst T labels) X := by
  simp only [matrixPairedChannel, matrixSharedChannel, map_sum, map_smul,
    copyAlice_pairProjector, matrixReportedEvaluation_fst, Finset.sum_smul]

theorem copy_preserves_density_exactness {ι : Type*} [Fintype ι]
    (E : Label → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ → OutputMatrix)
    (h : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 → Γ ρ = Tomography.measurementChannel E ρ) :
    ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      copyAlice (Γ ρ) = Tomography.measurementChannel E ρ := by
  intro ρ hpos htrace
  rw [h ρ hpos htrace, copyAlice_fixed_measurementChannel]

theorem copy_preserves_density_convergence {α ι : Type*} [Fintype ι]
    (l : Filter α) (E : Label → Matrix ι ι ℂ)
    (Γ : α → Matrix ι ι ℂ → OutputMatrix)
    (h : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      Filter.Tendsto (fun t => Γ t ρ) l (nhds (Tomography.measurementChannel E ρ))) :
    ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      Filter.Tendsto (fun t => copyAlice (Γ t ρ)) l
        (nhds (Tomography.measurementChannel E ρ)) := by
  intro ρ hpos htrace
  have hc := copyAlice_continuous.tendsto (Tomography.measurementChannel E ρ)
  rw [copyAlice_fixed_measurementChannel] at hc
  exact hc.comp (h ρ hpos htrace)

theorem copy_preserves_coded_density_exactness {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Matrix κ ι ℂ) (E : Label → Matrix ι ι ℂ)
    (Λ : Matrix κ κ ℂ → OutputMatrix)
    (h : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      Λ (J * ρ * J.conjTranspose) = Tomography.measurementChannel E ρ) :
    ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      copyAlice (Λ (J * ρ * J.conjTranspose)) = Tomography.measurementChannel E ρ :=
  copy_preserves_density_exactness E (fun ρ => Λ (J * ρ * J.conjTranspose)) h

theorem copy_preserves_coded_density_convergence {α ι κ : Type*}
    [Fintype ι] [Fintype κ] (l : Filter α) (J : α → Matrix κ ι ℂ)
    (E : Label → Matrix ι ι ℂ) (Λ : α → Matrix κ κ ℂ → OutputMatrix)
    (h : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      Filter.Tendsto (fun t => Λ t (J t * ρ * (J t).conjTranspose)) l
        (nhds (Tomography.measurementChannel E ρ))) :
    ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      Filter.Tendsto (fun t => copyAlice (Λ t (J t * ρ * (J t).conjTranspose))) l
        (nhds (Tomography.measurementChannel E ρ)) :=
  copy_preserves_density_convergence l E
    (fun t ρ => Λ t (J t * ρ * (J t).conjTranspose)) h

theorem copy_postprocessing_completelyPositive {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Λ : Matrix κ κ ℂ →ₗ[ℂ] OutputMatrix) (hΛ : QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive Λ) :
    QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (copyAlice.comp Λ) :=
  copyAlice_completelyPositive.comp hΛ

theorem copy_postprocessing_trace_preserving {κ : Type*} [Fintype κ]
    (Λ : Matrix κ κ ℂ →ₗ[ℂ] OutputMatrix)
    (hΛ : ∀ X, (Λ X).trace = X.trace) (X : Matrix κ κ ℂ) :
    ((copyAlice.comp Λ) X).trace = X.trace := by
  rw [LinearMap.comp_apply, copyAlice_trace_preserving, hΛ]

theorem matrix_coded_exactness_implies_fst_compression {ι : Type*}
    [Fintype ι] [DecidableEq ι] {m n : ℕ}
    (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T OutputIndex)
    (J : Matrix (Fin m × Fin n) ι ℂ) (E : Label → Matrix ι ι ℂ)
    (h : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      matrixPairedChannel T labels (J * ρ * J.conjTranspose) =
        Tomography.measurementChannel E ρ) :
    ∀ a : Label,
      J.conjTranspose * T.matrixReportedEffect (mapLeafLabels Prod.fst T labels) a * J = E a := by
  have hc := copy_preserves_coded_density_exactness J E (matrixPairedChannel T labels) h
  simp only [copy_matrixPairedChannel_eq_fst, matrixSharedChannel_eq_measurement] at hc
  have he := (Tomography.resourceChannel_exact_iff_compressed J
    (T.matrixReportedEffect (mapLeafLabels Prod.fst T labels)) E).mp hc
  intro a
  exact congrFun he a

theorem matrix_coded_convergence_implies_fst_compression {α ι : Type*}
    [Fintype ι] [DecidableEq ι] {m n : ℕ} (l : Filter α)
    (T : α → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : ∀ t, QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels (T t) OutputIndex)
    (J : α → Matrix (Fin m × Fin n) ι ℂ) (E : Label → Matrix ι ι ℂ)
    (h : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      Filter.Tendsto (fun t => matrixPairedChannel (T t) (labels t)
        (J t * ρ * (J t).conjTranspose)) l (nhds (Tomography.measurementChannel E ρ))) :
    ∀ a : Label, Filter.Tendsto
      (fun t => (J t).conjTranspose *
        (T t).matrixReportedEffect (mapLeafLabels Prod.fst (T t) (labels t)) a * J t)
      l (nhds (E a)) := by
  have hc := copy_preserves_coded_density_convergence l J E
    (fun t => matrixPairedChannel (T t) (labels t)) h
  simp only [copy_matrixPairedChannel_eq_fst, matrixSharedChannel_eq_measurement] at hc
  exact (Tomography.resourceChannel_tendsto_iff_varying_compressed l J
    (fun t => (T t).matrixReportedEffect (mapLeafLabels Prod.fst (T t) (labels t))) E).mp hc

end

end QuantumProver.ElegantJointMeasurement.Teleportation.ClassicalOutputRepair

namespace QuantumProver.ElegantJointMeasurement.Teleportation.InitialBasisTransport

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Topology

noncomputable section

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

def matrixEmbedding (e : κ ≃ ν) (J : Matrix κ ι ℂ) : Matrix ν ι ℂ :=
  J.submatrix e.symm id

omit [Fintype ι] in
theorem compression_reindex (e : κ ≃ ν) (J : Matrix κ ι ℂ) (F : Matrix ν ν ℂ) :
    (J.submatrix e.symm id).conjTranspose * F * J.submatrix e.symm id =
      J.conjTranspose * F.submatrix e e * J := by
  calc
    _ = J.conjTranspose.submatrix id e.symm *
        (F.submatrix e e).submatrix e.symm e.symm * J.submatrix e.symm id := by
      simp [Matrix.conjTranspose_submatrix, Matrix.submatrix_submatrix]
    _ = _ := by
      simp only [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]

omit [Fintype κ] [Fintype ν] in
theorem encoded_density_reindex (e : κ ≃ ν) (J : Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) :
    matrixEmbedding e J * ρ * (matrixEmbedding e J).conjTranspose =
      (J * ρ * J.conjTranspose).submatrix e.symm e.symm := by
  calc
    _ = J.submatrix e.symm (Equiv.refl ι) *
        ρ.submatrix (Equiv.refl ι) (Equiv.refl ι) *
          J.conjTranspose.submatrix (Equiv.refl ι) e.symm := by
      simp [matrixEmbedding, Matrix.conjTranspose_submatrix]
    _ = _ := by
      rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

theorem trace_resource_reindex (e : κ ≃ ν) (J : Matrix κ ι ℂ)
    (F : Matrix ν ν ℂ) (ρ : Matrix ι ι ℂ) :
    (F * (matrixEmbedding e J * ρ * (matrixEmbedding e J).conjTranspose)).trace =
      (F.submatrix e e * (J * ρ * J.conjTranspose)).trace := by
  rw [Tomography.trace_resource_compression, Tomography.trace_resource_compression]
  rw [matrixEmbedding, compression_reindex]

theorem resourceChannel_reindex {L : Type*} [Fintype L] [DecidableEq L]
    (e : κ ≃ ν) (J : Matrix κ ι ℂ) (F : L → Matrix ν ν ℂ) (ρ : Matrix ι ι ℂ) :
    Tomography.resourceMeasurementChannel (matrixEmbedding e J) F ρ =
      Tomography.resourceMeasurementChannel J (fun a => (F a).submatrix e e) ρ := by
  simp only [Tomography.resourceMeasurementChannel, trace_resource_reindex]

theorem density_exactness_reindex_iff {L : Type*} [Fintype L] [DecidableEq L]
    [DecidableEq ι] (e : κ ≃ ν) (J : Matrix κ ι ℂ)
    (F : L → Matrix ν ν ℂ) (E : L → Matrix ι ι ℂ) :
    (∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      Tomography.resourceMeasurementChannel (matrixEmbedding e J) F ρ =
        Tomography.measurementChannel E ρ) ↔
      (∀ a, J.conjTranspose * (F a).submatrix e e * J = E a) := by
  simp only [resourceChannel_reindex]
  rw [Tomography.resourceChannel_exact_iff_compressed]
  exact funext_iff

theorem density_limit_reindex_iff {α L : Type*} [Fintype L] [DecidableEq L]
    [DecidableEq ι] (l : Filter α) (e : α → κ ≃ ν) (J : α → Matrix κ ι ℂ)
    (F : α → L → Matrix ν ν ℂ) (E : L → Matrix ι ι ℂ) :
    (∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      Filter.Tendsto (fun t => Tomography.resourceMeasurementChannel
        (matrixEmbedding (e t) (J t)) (F t) ρ) l (nhds (Tomography.measurementChannel E ρ))) ↔
      (∀ a, Filter.Tendsto (fun t => (J t).conjTranspose * (F t a).submatrix (e t) (e t) * J t)
        l (nhds (E a))) := by
  simp only [resourceChannel_reindex]
  exact Tomography.resourceChannel_tendsto_iff_varying_compressed l J
    (fun t a => (F t a).submatrix (e t) (e t)) E

theorem repaired_matrixPairedChannel_reindex {m n : ℕ}
    (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T ClassicalOutputRepair.OutputIndex)
    (e : κ ≃ Fin m × Fin n) (J : Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) :
    ClassicalOutputRepair.copyAlice (ClassicalOutputRepair.matrixPairedChannel T labels
      (matrixEmbedding e J * ρ * (matrixEmbedding e J).conjTranspose)) =
      Tomography.resourceMeasurementChannel J
        (fun a => (T.matrixReportedEffect (ClassicalOutputRepair.mapLeafLabels Prod.fst T labels) a).submatrix
          e e) ρ := by
  rw [ClassicalOutputRepair.copy_matrixPairedChannel_eq_fst,
    ClassicalOutputRepair.matrixSharedChannel_eq_measurement]
  change Tomography.resourceMeasurementChannel (matrixEmbedding e J)
    (T.matrixReportedEffect (ClassicalOutputRepair.mapLeafLabels Prod.fst T labels)) ρ = _
  exact resourceChannel_reindex e J _ ρ

theorem matrix_paired_exactness_implies_physical_compression {m n : ℕ} [DecidableEq ι]
    (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T ClassicalOutputRepair.OutputIndex)
    (e : κ ≃ Fin m × Fin n) (J : Matrix κ ι ℂ)
    (E : ClassicalOutputRepair.Label → Matrix ι ι ℂ)
    (h : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      ClassicalOutputRepair.matrixPairedChannel T labels
        (matrixEmbedding e J * ρ * (matrixEmbedding e J).conjTranspose) =
          Tomography.measurementChannel E ρ) :
    ∀ a, J.conjTranspose *
      (T.matrixReportedEffect (ClassicalOutputRepair.mapLeafLabels Prod.fst T labels) a).submatrix
        e e * J = E a := by
  have hc := ClassicalOutputRepair.matrix_coded_exactness_implies_fst_compression
    T labels (matrixEmbedding e J) E h
  simpa only [matrixEmbedding, compression_reindex] using hc

theorem matrix_paired_limit_implies_physical_compression {α : Type*} {m n : ℕ}
    [DecidableEq ι] (l : Filter α) (T : α → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : ∀ t, QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels (T t) ClassicalOutputRepair.OutputIndex)
    (e : α → κ ≃ Fin m × Fin n) (J : α → Matrix κ ι ℂ)
    (E : ClassicalOutputRepair.Label → Matrix ι ι ℂ)
    (h : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      Filter.Tendsto (fun t => ClassicalOutputRepair.matrixPairedChannel (T t) (labels t)
        (matrixEmbedding (e t) (J t) * ρ * (matrixEmbedding (e t) (J t)).conjTranspose))
        l (nhds (Tomography.measurementChannel E ρ))) :
    ∀ a, Filter.Tendsto (fun t => (J t).conjTranspose *
      ((T t).matrixReportedEffect
        (ClassicalOutputRepair.mapLeafLabels Prod.fst (T t) (labels t)) a).submatrix
          (e t) (e t) * J t) l (nhds (E a)) := by
  have hc := ClassicalOutputRepair.matrix_coded_convergence_implies_fst_compression
    l T labels (fun t => matrixEmbedding (e t) (J t)) E h
  simpa only [matrixEmbedding, compression_reindex] using hc

theorem terminalReport_fst {m n : ℕ} (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T ClassicalOutputRepair.OutputIndex) :
    T.terminalReport (ClassicalOutputRepair.mapLeafLabels Prod.fst T labels) =
      fun i => (T.terminalReport labels i).1 := by
  funext i
  exact ClassicalOutputRepair.terminalReport_map Prod.fst T labels i

theorem matrix_effect_pullback_eq_grouped {r : Type*} [Fintype r] [DecidableEq r]
    {m n : ℕ} (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T (Fin 4))
    (ea : (Fin 2 × r) ≃ Fin m) (eb : (Fin 2 × r) ≃ Fin n) (a : Fin 4) :
    (T.matrixReportedEffect labels a).submatrix (ea.prodCongr eb) (ea.prodCongr eb) =
      QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect T.krausRefinement ea eb (T.terminalReport labels) a := by
  change QuantumProver.ElegantJointMeasurement.ProtocolEffects.pullbackEffect ea eb (T.matrixReportedEffect labels a) = _
  rw [QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.matrixReportedEffect, map_sum]
  unfold QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect QuantumProver.ElegantJointMeasurement.ProtocolEffects.outcomeSum
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : T.terminalReport labels i = a <;>
    simp [h, QuantumProver.ElegantJointMeasurement.ProtocolEffects.physicalEffect_eq_pullback]

theorem repaired_matrix_channel_eq_physical_grouped {r : Type*} [Fintype r] [DecidableEq r]
    {m n : ℕ} (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T ClassicalOutputRepair.OutputIndex)
    (ea : (Fin 2 × r) ≃ Fin m) (eb : (Fin 2 × r) ≃ Fin n)
    (J : Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index r) ι ℂ) (ρ : Matrix ι ι ℂ) :
    ClassicalOutputRepair.copyAlice (ClassicalOutputRepair.matrixPairedChannel T labels
      (matrixEmbedding (ea.prodCongr eb) J * ρ *
        (matrixEmbedding (ea.prodCongr eb) J).conjTranspose)) =
      Tomography.resourceMeasurementChannel J
        (QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect T.krausRefinement ea eb
          (fun i => (T.terminalReport labels i).1)) ρ := by
  rw [repaired_matrixPairedChannel_reindex]
  simp_rw [matrix_effect_pullback_eq_grouped, terminalReport_fst]

theorem matrix_paired_exactness_implies_grouped_compression {r : Type*}
    [Fintype r] [DecidableEq r] [DecidableEq ι] {m n : ℕ}
    (T : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels T ClassicalOutputRepair.OutputIndex)
    (ea : (Fin 2 × r) ≃ Fin m) (eb : (Fin 2 × r) ≃ Fin n)
    (J : Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index r) ι ℂ)
    (E : ClassicalOutputRepair.Label → Matrix ι ι ℂ)
    (h : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      ClassicalOutputRepair.matrixPairedChannel T labels
        (matrixEmbedding (ea.prodCongr eb) J * ρ *
          (matrixEmbedding (ea.prodCongr eb) J).conjTranspose) =
            Tomography.measurementChannel E ρ) :
    ∀ a, J.conjTranspose * QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect T.krausRefinement ea eb
      (fun i => (T.terminalReport labels i).1) a * J = E a := by
  have hc := matrix_paired_exactness_implies_physical_compression T labels (ea.prodCongr eb) J E h
  simpa only [matrix_effect_pullback_eq_grouped, terminalReport_fst] using hc

theorem matrix_paired_limit_implies_grouped_compression {α r : Type*}
    [Fintype r] [DecidableEq r] [DecidableEq ι] {m n : ℕ} (l : Filter α)
    (T : α → QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree m n)
    (labels : ∀ t, QuantumProver.ElegantJointMeasurement.CP.FiniteLocalCPInstrumentTree.LeafLabels (T t) ClassicalOutputRepair.OutputIndex)
    (ea : α → (Fin 2 × r) ≃ Fin m) (eb : α → (Fin 2 × r) ≃ Fin n)
    (J : α → Matrix (QuantumProver.ElegantJointMeasurement.Augmented.Index r) ι ℂ)
    (E : ClassicalOutputRepair.Label → Matrix ι ι ℂ)
    (h : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      Filter.Tendsto (fun t => ClassicalOutputRepair.matrixPairedChannel (T t) (labels t)
        (matrixEmbedding ((ea t).prodCongr (eb t)) (J t) * ρ *
          (matrixEmbedding ((ea t).prodCongr (eb t)) (J t)).conjTranspose))
        l (nhds (Tomography.measurementChannel E ρ))) :
    ∀ a, Filter.Tendsto (fun t => (J t).conjTranspose *
      QuantumProver.ElegantJointMeasurement.ProtocolEffects.groupedEffect (T t).krausRefinement (ea t) (eb t)
        (fun i => ((T t).terminalReport (labels t) i).1) a * J t) l (nhds (E a)) := by
  have hc := matrix_paired_limit_implies_physical_compression l T labels
    (fun t => (ea t).prodCongr (eb t)) J E h
  simpa only [matrix_effect_pullback_eq_grouped, terminalReport_fst] using hc

end

end QuantumProver.ElegantJointMeasurement.Teleportation.InitialBasisTransport

namespace QuantumProver.ElegantJointMeasurement.Teleportation.ChannelFirstEffects

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Topology

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

abbrev OutputMatrix := ClassicalOutputRepair.OutputMatrix
abbrev Label := ClassicalOutputRepair.Label
abbrev Channel := Matrix κ κ ℂ →ₗ[ℂ] OutputMatrix

def firstEffect (Γ : Channel (κ := κ)) (a : Label) : Matrix κ κ ℂ :=
  fun i j => ∑ b : Label, Γ (Matrix.single j i 1) (a, b) (a, b)

theorem firstEffect_born (Γ : Channel (κ := κ)) (a : Label) (X : Matrix κ κ ℂ) :
    (firstEffect Γ a * X).trace = ∑ b : Label, Γ X (a, b) (a, b) := by
  refine Matrix.induction_on'
    (P := fun X => (firstEffect Γ a * X).trace = ∑ b : Label, Γ X (a, b) (a, b))
    X ?_ ?_ ?_
  · simp
  · intro A B hA hB
    simp only [Matrix.mul_add, Matrix.trace_add, map_add, Matrix.add_apply,
      Finset.sum_add_distrib]
    rw [hA, hB]
  · intro i j z
    have hsingle : Matrix.single i j z = z • Matrix.single i j (1 : ℂ) := by
      simp [Matrix.smul_single]
    rw [Matrix.trace_mul_single, hsingle, map_smul]
    simp [firstEffect, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_comm]

def PositiveChannel (Γ : Channel (κ := κ)) : Prop :=
  ∀ X, X.PosSemidef → (Γ X).PosSemidef

omit [Fintype κ] [DecidableEq κ] in
theorem completelyPositive_positive (Γ : Channel (κ := κ))
    (hΓ : QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive Γ) : PositiveChannel Γ := by
  intro X hX
  have h := (hΓ 1 (X.submatrix Prod.snd Prod.snd) (hX.submatrix Prod.snd)).submatrix
    (fun i : ClassicalOutputRepair.OutputIndex => ((0 : Fin 1), i))
  change (Γ X).PosSemidef at h
  exact h

theorem firstEffect_born_nonneg (Γ : Channel (κ := κ)) (hΓ : PositiveChannel Γ)
    (a : Label) (X : Matrix κ κ ℂ) (hX : X.PosSemidef) :
    0 ≤ (firstEffect Γ a * X).trace := by
  rw [firstEffect_born]
  apply Finset.sum_nonneg
  intro b _
  exact (hΓ X hX).diag_nonneg

theorem firstEffect_isHermitian (Γ : Channel (κ := κ)) (hΓ : PositiveChannel Γ) (a : Label) :
    (firstEffect Γ a).IsHermitian := by
  change (firstEffect Γ a).conjTranspose = firstEffect Γ a
  apply Tomography.effect_tomography
  intro ρ hρ _
  calc
    ((firstEffect Γ a).conjTranspose * ρ).trace =
        (ρ * (firstEffect Γ a).conjTranspose).trace := Matrix.trace_mul_comm _ _
    _ = (firstEffect Γ a * ρ).conjTranspose.trace := by
      rw [Matrix.conjTranspose_mul, hρ.isHermitian.eq]
    _ = conj ((firstEffect Γ a * ρ).trace) := Matrix.trace_conjTranspose _
    _ = (firstEffect Γ a * ρ).trace :=
      (IsSelfAdjoint.of_nonneg (firstEffect_born_nonneg Γ hΓ a ρ hρ)).star_eq

theorem firstEffect_posSemidef (Γ : Channel (κ := κ)) (hΓ : PositiveChannel Γ) (a : Label) :
    (firstEffect Γ a).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (firstEffect_isHermitian Γ hΓ a)
  intro x
  have h := firstEffect_born_nonneg Γ hΓ a (Matrix.vecMulVec x (star x))
    (Matrix.posSemidef_vecMulVec_self_star x)
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] at h
  exact h

theorem firstEffect_posSemidef_of_cp (Γ : Channel (κ := κ))
    (hΓ : QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive Γ) (a : Label) : (firstEffect Γ a).PosSemidef :=
  firstEffect_posSemidef Γ (completelyPositive_positive Γ hΓ) a

theorem sum_firstEffect_eq_one (Γ : Channel (κ := κ))
    (hΓ : ∀ X, (Γ X).trace = X.trace) : ∑ a, firstEffect Γ a = 1 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [Matrix.sum_mul, Matrix.trace_sum, Matrix.one_mul]
  simp_rw [firstEffect_born]
  calc
    _ = (Γ X).trace := by
      rw [Matrix.trace, Fintype.sum_prod_type]
      rfl
    _ = X.trace := hΓ X

theorem copy_channel_eq_measurement (Γ : Channel (κ := κ)) (X : Matrix κ κ ℂ) :
    ClassicalOutputRepair.copyAlice (Γ X) = Tomography.measurementChannel (firstEffect Γ) X := by
  rw [ClassicalOutputRepair.copyAlice_eq_marginal_diagonal]
  simp only [Tomography.measurementChannel, firstEffect_born]

theorem copy_coded_channel_eq_resourceMeasurement {ι : Type*} [Fintype ι]
    (Γ : Channel (κ := κ)) (J : Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) :
    ClassicalOutputRepair.copyAlice (Γ (J * ρ * J.conjTranspose)) =
      Tomography.resourceMeasurementChannel J (firstEffect Γ) ρ :=
  copy_channel_eq_measurement Γ (J * ρ * J.conjTranspose)

theorem coded_density_exactness_implies_firstEffect_compression {ι : Type*}
    [Fintype ι] [DecidableEq ι] (Γ : Channel (κ := κ)) (J : Matrix κ ι ℂ)
    (E : Label → Matrix ι ι ℂ)
    (h : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      Γ (J * ρ * J.conjTranspose) = Tomography.measurementChannel E ρ) :
    ∀ a, J.conjTranspose * firstEffect Γ a * J = E a := by
  have hc := ClassicalOutputRepair.copy_preserves_coded_density_exactness J E Γ h
  simp only [copy_coded_channel_eq_resourceMeasurement] at hc
  have he := (Tomography.resourceChannel_exact_iff_compressed J (firstEffect Γ) E).mp hc
  intro a
  exact congrFun he a

theorem coded_density_limit_implies_firstEffect_compression {α ι : Type*}
    [Fintype ι] [DecidableEq ι] (l : Filter α) (Γ : α → Channel (κ := κ))
    (J : α → Matrix κ ι ℂ) (E : Label → Matrix ι ι ℂ)
    (h : ∀ ρ, ρ.PosSemidef → ρ.trace = 1 →
      Filter.Tendsto (fun t => Γ t (J t * ρ * (J t).conjTranspose)) l
        (nhds (Tomography.measurementChannel E ρ))) :
    ∀ a, Filter.Tendsto (fun t => (J t).conjTranspose * firstEffect (Γ t) a * J t)
      l (nhds (E a)) := by
  have hc := ClassicalOutputRepair.copy_preserves_coded_density_convergence l J E (fun t X => Γ t X) h
  simp only [copy_coded_channel_eq_resourceMeasurement] at hc
  exact (Tomography.resourceChannel_tendsto_iff_varying_compressed l J
    (fun t => firstEffect (Γ t)) E).mp hc

end

end QuantumProver.ElegantJointMeasurement.Teleportation.ChannelFirstEffects

namespace QuantumProver.ElegantJointMeasurement.Teleportation.MixedLocalAncillas

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

noncomputable section

set_option maxHeartbeats 600000

variable {m n da db : ℕ}

def localBasisEquiv (m d : ℕ) : (Fin m × Fin d) ≃ Fin (m * d) := finProdFinEquiv

def ancillaFactor (α : Matrix (Fin da) (Fin da) ℂ) : Matrix (Fin da) (Fin da) ℂ :=
  CFC.sqrt α

theorem ancillaFactor_gram_matrix (α : Matrix (Fin da) (Fin da) ℂ) (hα : α.PosSemidef) :
    ancillaFactor α * (ancillaFactor α).conjTranspose = α := by
  have hs : (ancillaFactor α).conjTranspose = ancillaFactor α :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg α)).isHermitian
  rw [hs, ← pow_two]
  exact CFC.sq_sqrt α hα.nonneg

theorem ancillaFactor_gram (α : Matrix (Fin da) (Fin da) ℂ) (hα : α.PosSemidef)
    (a b : Fin da) :
    ∑ r, ancillaFactor α a r * conj (ancillaFactor α b r) = α a b := by
  change (ancillaFactor α * (ancillaFactor α).conjTranspose) a b = α a b
  rw [ancillaFactor_gram_matrix α hα]

def preparationKraus (α : Matrix (Fin da) (Fin da) ℂ) (r : Fin da) :
    Matrix (Fin m × Fin da) (Fin m) ℂ :=
  fun p i => if p.1 = i then ancillaFactor α p.2 r else 0

def tensorPreparationMap (α : Matrix (Fin da) (Fin da) ℂ) :
    Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m × Fin da) (Fin m × Fin da) ℂ where
  toFun X := X ⊗ₖ α
  map_add' X Y := Matrix.add_kronecker X Y α
  map_smul' z X := Matrix.smul_kronecker z X α

theorem tensorPreparationMap_eq_krausMap (α : Matrix (Fin da) (Fin da) ℂ)
    (hα : α.PosSemidef) :
    tensorPreparationMap (m := m) α = QuantumProver.ElegantJointMeasurement.CP.krausMap (preparationKraus (m := m) α) := by
  apply QuantumProver.ElegantJointMeasurement.CP.linearMap_eq_of_matrix_units
  intro i j
  ext p q
  change (Matrix.single i j (1 : ℂ) ⊗ₖ α) p q =
    (∑ r : Fin da, preparationKraus (m := m) α r * Matrix.single i j (1 : ℂ) *
      (preparationKraus (m := m) α r).conjTranspose) p q
  simp only [Matrix.sum_apply, QuantumProver.ElegantJointMeasurement.CP.kraus_matrix_unit]
  rcases p with ⟨u, a⟩
  rcases q with ⟨v, b⟩
  by_cases hu : u = i <;> by_cases hv : v = j
  · subst u
    subst v
    simpa [preparationKraus] using (ancillaFactor_gram α hα a b).symm
  · simp [preparationKraus, hu, hv, Ne.symm hv]
  · simp [preparationKraus, hu, hv, Ne.symm hu]
  · simp [preparationKraus, hu, hv, Ne.symm hu, Ne.symm hv]

def matrixPreparationKraus (α : Matrix (Fin da) (Fin da) ℂ) (r : Fin da) :
    Matrix (Fin (m * da)) (Fin m) ℂ :=
  InitialBasisTransport.matrixEmbedding (localBasisEquiv m da) (preparationKraus α r)

def prepareMap (α : Matrix (Fin da) (Fin da) ℂ) :
    Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin (m * da)) (Fin (m * da)) ℂ where
  toFun X := (X ⊗ₖ α).submatrix (localBasisEquiv m da).symm (localBasisEquiv m da).symm
  map_add' X Y := by
    rw [Matrix.add_kronecker]
    rfl
  map_smul' z X := by
    rw [Matrix.smul_kronecker]
    rfl

theorem prepareMap_apply (α : Matrix (Fin da) (Fin da) ℂ) (X : Matrix (Fin m) (Fin m) ℂ) :
    prepareMap α X = (X ⊗ₖ α).submatrix (localBasisEquiv m da).symm
      (localBasisEquiv m da).symm := rfl

theorem prepareMap_eq_krausMap (α : Matrix (Fin da) (Fin da) ℂ) (hα : α.PosSemidef) :
    prepareMap (m := m) α = QuantumProver.ElegantJointMeasurement.CP.krausMap (matrixPreparationKraus (m := m) α) := by
  apply LinearMap.ext
  intro X
  change (tensorPreparationMap α X).submatrix (localBasisEquiv m da).symm
    (localBasisEquiv m da).symm = _
  rw [tensorPreparationMap_eq_krausMap α hα]
  change (∑ r : Fin da, preparationKraus (m := m) α r * X *
      (preparationKraus (m := m) α r).conjTranspose).submatrix
    (localBasisEquiv m da).symm (localBasisEquiv m da).symm =
      ∑ r : Fin da, matrixPreparationKraus (m := m) α r * X *
        (matrixPreparationKraus (m := m) α r).conjTranspose
  ext p q
  simp only [Matrix.submatrix_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  exact congrFun (congrFun (InitialBasisTransport.encoded_density_reindex
    (localBasisEquiv m da) (preparationKraus (m := m) α r) X).symm p) q

theorem prepareMap_completelyPositive (α : Matrix (Fin da) (Fin da) ℂ) (hα : α.PosSemidef) :
    QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (prepareMap (m := m) α) := by
  rw [prepareMap_eq_krausMap α hα]
  exact QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive _

theorem trace_submatrix_equiv {I O : Type*} [Fintype I] [Fintype O]
    (e : O ≃ I) (X : Matrix I I ℂ) : (X.submatrix e e).trace = X.trace := by
  change (∑ o : O, X (e o) (e o)) = ∑ i : I, X i i
  exact e.sum_comp (fun i : I => X i i)

theorem prepareMap_trace (α : Matrix (Fin da) (Fin da) ℂ) (X : Matrix (Fin m) (Fin m) ℂ) :
    (prepareMap α X).trace = X.trace * α.trace := by
  rw [prepareMap_apply, trace_submatrix_equiv, Matrix.trace_kronecker]

theorem prepareMap_trace_preserving (α : Matrix (Fin da) (Fin da) ℂ) (hα : α.trace = 1)
    (X : Matrix (Fin m) (Fin m) ℂ) : (prepareMap α X).trace = X.trace := by
  rw [prepareMap_trace, hα, mul_one]

theorem matrixPreparationKraus_complete (α : Matrix (Fin da) (Fin da) ℂ)
    (hα : α.PosSemidef) (htrace : α.trace = 1) :
    ∑ r, (matrixPreparationKraus (m := m) α r).conjTranspose *
      matrixPreparationKraus (m := m) α r = 1 := by
  apply (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff (matrixPreparationKraus (m := m) α)).mp
  intro X
  rw [← prepareMap_eq_krausMap α hα]
  exact prepareMap_trace_preserving α htrace X

theorem ancilla_dimension_pos (α : Matrix (Fin da) (Fin da) ℂ) (htrace : α.trace = 1) :
    0 < da := by
  by_contra h
  have hd : da = 0 := Nat.eq_zero_of_not_pos h
  subst da
  simp at htrace

theorem initial_dimensions_pos (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (htrace : X.trace = 1) : 0 < m ∧ 0 < n := by
  constructor
  · by_contra h
    have hm : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    simp at htrace
  · by_contra h
    have hn : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    simp at htrace

def regroupEquiv (m n da db : ℕ) :
    ((Fin m × Fin n) × (Fin da × Fin db)) ≃ ((Fin m × Fin da) × (Fin n × Fin db)) where
  toFun z := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  invFun z := ((z.1.1, z.2.1), (z.1.2, z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def augmentedBasisEquiv (m n da db : ℕ) :
    ((Fin m × Fin n) × (Fin da × Fin db)) ≃ (Fin (m * da) × Fin (n * db)) :=
  (regroupEquiv m n da db).trans ((localBasisEquiv m da).prodCongr (localBasisEquiv n db))

def augmentedProductState (α : Matrix (Fin da) (Fin da) ℂ)
    (β : Matrix (Fin db) (Fin db) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    Matrix (Fin (m * da) × Fin (n * db)) (Fin (m * da) × Fin (n * db)) ℂ :=
  (X ⊗ₖ (α ⊗ₖ β)).submatrix (augmentedBasisEquiv m n da db).symm
    (augmentedBasisEquiv m n da db).symm

theorem augmentedProductState_apply (α : Matrix (Fin da) (Fin da) ℂ)
    (β : Matrix (Fin db) (Fin db) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (p q : Fin (m * da) × Fin (n * db)) :
    augmentedProductState α β X p q =
      X (((localBasisEquiv m da).symm p.1).1, ((localBasisEquiv n db).symm p.2).1)
        (((localBasisEquiv m da).symm q.1).1, ((localBasisEquiv n db).symm q.2).1) *
      (α ((localBasisEquiv m da).symm p.1).2 ((localBasisEquiv m da).symm q.1).2 *
        β ((localBasisEquiv n db).symm p.2).2 ((localBasisEquiv n db).symm q.2).2) := rfl

theorem augmentedProductState_posSemidef (α : Matrix (Fin da) (Fin da) ℂ)
    (hα : α.PosSemidef) (β : Matrix (Fin db) (Fin db) ℂ) (hβ : β.PosSemidef)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) (hX : X.PosSemidef) :
    (augmentedProductState α β X).PosSemidef :=
  (hX.kronecker (hα.kronecker hβ)).submatrix (augmentedBasisEquiv m n da db).symm

theorem augmentedProductState_trace (α : Matrix (Fin da) (Fin da) ℂ)
    (β : Matrix (Fin db) (Fin db) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (augmentedProductState α β X).trace = X.trace * (α.trace * β.trace) := by
  rw [augmentedProductState, trace_submatrix_equiv, Matrix.trace_kronecker, Matrix.trace_kronecker]

theorem augmentedProductState_trace_preserving (α : Matrix (Fin da) (Fin da) ℂ)
    (hα : α.trace = 1) (β : Matrix (Fin db) (Fin db) ℂ) (hβ : β.trace = 1)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (augmentedProductState α β X).trace = X.trace := by
  rw [augmentedProductState_trace, hα, hβ, mul_one, mul_one]

theorem left_prepare_apply (α : Matrix (Fin da) (Fin da) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (p q : Fin (m * da) × Fin n) :
    QuantumProver.ElegantJointMeasurement.CP.leftApplication (prepareMap α) X p q =
      X (((localBasisEquiv m da).symm p.1).1, p.2)
        (((localBasisEquiv m da).symm q.1).1, q.2) *
      α ((localBasisEquiv m da).symm p.1).2 ((localBasisEquiv m da).symm q.1).2 := rfl

theorem right_prepare_apply (β : Matrix (Fin db) (Fin db) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (p q : Fin m × Fin (n * db)) :
    QuantumProver.ElegantJointMeasurement.CP.rightApplication (prepareMap β) X p q =
      X (p.1, ((localBasisEquiv n db).symm p.2).1)
        (q.1, ((localBasisEquiv n db).symm q.2).1) *
      β ((localBasisEquiv n db).symm p.2).2 ((localBasisEquiv n db).symm q.2).2 := rfl

theorem local_preparations_eq_augmentedProductState (α : Matrix (Fin da) (Fin da) ℂ)
    (β : Matrix (Fin db) (Fin db) ℂ)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    QuantumProver.ElegantJointMeasurement.CP.rightApplication (prepareMap β) (QuantumProver.ElegantJointMeasurement.CP.leftApplication (prepareMap α) X) =
      augmentedProductState α β X := by
  ext p q
  rw [right_prepare_apply, left_prepare_apply, augmentedProductState_apply, mul_assoc]

def prependLocalAncillas (hm : 0 < m) (hn : 0 < n)
    (α : Matrix (Fin da) (Fin da) ℂ) (hα : α.PosSemidef) (tα : α.trace = 1)
    (β : Matrix (Fin db) (Fin db) ℂ) (hβ : β.PosSemidef) (tβ : β.trace = 1)
    (T : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree (m * da) (n * db)) :
    QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree m n :=
  .alice m n 1 (fun _ => m * da) (fun _ => Nat.mul_pos hm (ancilla_dimension_pos α tα))
    (fun _ => prepareMap α) (fun _ => prepareMap_completelyPositive α hα)
    (fun X => by simpa only [Fin.sum_univ_one] using prepareMap_trace_preserving α tα X)
    (fun _ => .bob (m * da) n 1 (fun _ => n * db)
      (fun _ => Nat.mul_pos hn (ancilla_dimension_pos β tβ))
      (fun _ => prepareMap β) (fun _ => prepareMap_completelyPositive β hβ)
      (fun X => by simpa only [Fin.sum_univ_one] using prepareMap_trace_preserving β tβ X)
      (fun _ => T))

def prependLabels {L : Type*} (hm : 0 < m) (hn : 0 < n)
    (α : Matrix (Fin da) (Fin da) ℂ) (hα : α.PosSemidef) (tα : α.trace = 1)
    (β : Matrix (Fin db) (Fin db) ℂ) (hβ : β.PosSemidef) (tβ : β.trace = 1)
    (T : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree (m * da) (n * db))
    (labels : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels T L) :
    QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels
      (prependLocalAncillas hm hn α hα tα β hβ tβ T) L := fun _ _ => labels

def physicalLeafLabelsEquiv {L : Type*} (hm : 0 < m) (hn : 0 < n)
    (α : Matrix (Fin da) (Fin da) ℂ) (hα : α.PosSemidef) (tα : α.trace = 1)
    (β : Matrix (Fin db) (Fin db) ℂ) (hβ : β.PosSemidef) (tβ : β.trace = 1)
    (T : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree (m * da) (n * db)) :
    QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels
      (prependLocalAncillas hm hn α hα tα β hβ tβ T) L ≃
        QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels T L where
  toFun labels := labels 0 0
  invFun labels := prependLabels hm hn α hα tα β hβ tβ T labels
  left_inv labels := by
    funext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst a
    subst b
    rfl
  right_inv _ := rfl

theorem prependLabels_preserve {L : Type*} (hm : 0 < m) (hn : 0 < n)
    (α : Matrix (Fin da) (Fin da) ℂ) (hα : α.PosSemidef) (tα : α.trace = 1)
    (β : Matrix (Fin db) (Fin db) ℂ) (hβ : β.PosSemidef) (tβ : β.trace = 1)
    (T : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree (m * da) (n * db))
    (labels : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels T L) (a b : Fin 1) :
    prependLabels hm hn α hα tα β hβ tβ T labels a b = labels := rfl

theorem prepend_matrixReportedEvaluation {L : Type*} [DecidableEq L]
    (hm : 0 < m) (hn : 0 < n)
    (α : Matrix (Fin da) (Fin da) ℂ) (hα : α.PosSemidef) (tα : α.trace = 1)
    (β : Matrix (Fin db) (Fin db) ℂ) (hβ : β.PosSemidef) (tβ : β.trace = 1)
    (T : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree (m * da) (n * db))
    (labels : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels T L) (ell : L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    (prependLocalAncillas hm hn α hα tα β hβ tβ T).matrixReportedEvaluation
      (prependLabels hm hn α hα tα β hβ tβ T labels) ell X =
        T.matrixReportedEvaluation labels ell (augmentedProductState α β X) := by
  simp only [prependLocalAncillas, prependLabels,
    QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.matrixReportedEvaluation,
    LinearMap.comp_apply, Fin.sum_univ_one]
  rw [local_preparations_eq_augmentedProductState]

theorem matrix_total_report_mass {L : Type*} [Fintype L] [DecidableEq L]
    (T : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree m n)
    (labels : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels T L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    ∑ ell, T.matrixReportedEvaluation labels ell X = X.trace := by
  simp_rw [T.matrixReportedEvaluation_eq_commonTree labels,
    T.commonTree.matrixReportedEvaluation_eq_trace_effect (T.commonLabels labels)]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul,
    T.commonTree.sum_matrixReportedEffect (T.commonLabels labels), Matrix.one_mul]

theorem prepend_total_report_mass {L : Type*} [Fintype L] [DecidableEq L]
    (hm : 0 < m) (hn : 0 < n)
    (α : Matrix (Fin da) (Fin da) ℂ) (hα : α.PosSemidef) (tα : α.trace = 1)
    (β : Matrix (Fin db) (Fin db) ℂ) (hβ : β.PosSemidef) (tβ : β.trace = 1)
    (T : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree (m * da) (n * db))
    (labels : QuantumProver.ElegantJointMeasurement.CP.DependentOutputCPInstrumentTree.LeafLabels T L)
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    ∑ ell, (prependLocalAncillas hm hn α hα tα β hβ tβ T).matrixReportedEvaluation
      (prependLabels hm hn α hα tα β hβ tβ T labels) ell X = X.trace := by
  simp_rw [prepend_matrixReportedEvaluation hm hn α hα tα β hβ tβ T labels]
  rw [matrix_total_report_mass, augmentedProductState_trace_preserving α tα β tβ]

end

end QuantumProver.ElegantJointMeasurement.Teleportation.MixedLocalAncillas

namespace QuantumProver.ElegantJointMeasurement.Teleportation.ReferenceStability

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix

noncomputable section
set_option maxHeartbeats 800000

variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

def traceNorm (A : Matrix R R ℂ) : ℝ := (CFC.abs A).trace.re

def referenceBlock (E : Matrix I I ℂ) (X : Matrix (I × R) (I × R) ℂ) : Matrix R R ℂ :=
  fun r s => ∑ i : I, ∑ k : I, E i k * X (k, r) (i, s)

def referenceBlockLinear (E : Matrix I I ℂ) :
    Matrix (I × R) (I × R) ℂ →ₗ[ℂ] Matrix R R ℂ where
  toFun := referenceBlock E
  map_add' X Y := by
    ext r s
    simp [referenceBlock, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' z X := by
    ext r s
    simp [referenceBlock, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_left_comm]

def referenceKraus (E : Matrix I I ℂ) (t : I) : Matrix R (I × R) ℂ :=
  fun r p => if r = p.2 then conj (CFC.sqrt E p.1 t) else 0

theorem effect_sqrt_gram (E : Matrix I I ℂ) (hE : E.PosSemidef) (i k : I) :
    ∑ t, CFC.sqrt E i t * conj (CFC.sqrt E k t) = E i k := by
  have hs : (CFC.sqrt E).conjTranspose = CFC.sqrt E :=
    (CFC.sqrt_nonneg E).posSemidef.isHermitian
  change (CFC.sqrt E * (CFC.sqrt E).conjTranspose) i k = E i k
  rw [hs, ← pow_two, CFC.sq_sqrt E hE.nonneg]

theorem referenceBlock_eq_krausMap (E : Matrix I I ℂ) (hE : E.PosSemidef) :
    referenceBlockLinear (R := R) E = QuantumProver.ElegantJointMeasurement.CP.krausMap (referenceKraus (R := R) E) := by
  apply QuantumProver.ElegantJointMeasurement.CP.linearMap_eq_of_matrix_units
  rintro ⟨i, a⟩ ⟨k, b⟩
  ext r s
  change referenceBlock E (Matrix.single (i, a) (k, b) (1 : ℂ)) r s =
    (∑ t : I, referenceKraus (R := R) E t * Matrix.single (i, a) (k, b) (1 : ℂ) *
      (referenceKraus (R := R) E t).conjTranspose) r s
  simp only [Matrix.sum_apply, QuantumProver.ElegantJointMeasurement.CP.kraus_matrix_unit]
  by_cases ha : r = a <;> by_cases hb : s = b
  · subst r
    subst s
    simpa [referenceBlock, referenceKraus, Matrix.single, ite_and, mul_comm] using
      (effect_sqrt_gram E hE k i).symm
  · simp [referenceBlock, referenceKraus, Matrix.single, ha, hb, Ne.symm hb]
  · simp [referenceBlock, referenceKraus, Matrix.single, ha, hb, Ne.symm ha]
  · simp [referenceBlock, referenceKraus, Matrix.single, ha, hb, Ne.symm ha, Ne.symm hb]

theorem referenceBlock_posSemidef (E : Matrix I I ℂ) (hE : E.PosSemidef)
    (X : Matrix (I × R) (I × R) ℂ) (hX : X.PosSemidef) :
    (referenceBlock E X).PosSemidef := by
  change (referenceBlockLinear E X).PosSemidef
  rw [referenceBlock_eq_krausMap E hE]
  exact Matrix.posSemidef_sum Finset.univ
    (fun t _ => hX.mul_mul_conjTranspose_same (referenceKraus E t))

omit [DecidableEq I] [Fintype R] [DecidableEq R] in
theorem referenceBlock_add (E F : Matrix I I ℂ) (X : Matrix (I × R) (I × R) ℂ) :
    referenceBlock (E + F) X = referenceBlock E X + referenceBlock F X := by
  ext r s
  simp [referenceBlock, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

omit [DecidableEq I] [Fintype R] [DecidableEq R] in
theorem referenceBlock_sub (E F : Matrix I I ℂ) (X : Matrix (I × R) (I × R) ℂ) :
    referenceBlock (E - F) X = referenceBlock E X - referenceBlock F X := by
  ext r s
  simp [referenceBlock, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq I] [Fintype R] [DecidableEq R] in
theorem referenceBlock_smul (c : ℝ) (E : Matrix I I ℂ)
    (X : Matrix (I × R) (I × R) ℂ) :
    referenceBlock (c • E) X = c • referenceBlock E X := by
  ext r s
  simp [referenceBlock, Matrix.smul_apply, Finset.smul_sum, mul_assoc]

def referenceMarginal (X : Matrix (I × R) (I × R) ℂ) : Matrix R R ℂ := referenceBlock 1 X

omit [Fintype R] [DecidableEq R] in
theorem referenceMarginal_apply (X : Matrix (I × R) (I × R) ℂ) (r s : R) :
    referenceMarginal X r s = ∑ i, X (i, r) (i, s) := by
  simp [referenceMarginal, referenceBlock, Matrix.one_apply]

omit [DecidableEq R] in
theorem referenceMarginal_trace (X : Matrix (I × R) (I × R) ℂ) :
    (referenceMarginal X).trace = X.trace := by
  change (∑ r : R, referenceMarginal X r r) = ∑ p : I × R, X p p
  simp only [referenceMarginal_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem referenceMarginal_posSemidef (X : Matrix (I × R) (I × R) ℂ) (hX : X.PosSemidef) :
    (referenceMarginal X).PosSemidef := referenceBlock_posSemidef 1 Matrix.PosSemidef.one X hX

theorem referenceBlock_isHermitian (E : Matrix I I ℂ) (hE : E.IsHermitian)
    (X : Matrix (I × R) (I × R) ℂ) (hX : X.PosSemidef) :
    (referenceBlock E X).IsHermitian := by
  rw [← CFC.posPart_sub_negPart E hE.isSelfAdjoint, referenceBlock_sub]
  exact (referenceBlock_posSemidef _ (CFC.posPart_nonneg E).posSemidef X hX).isHermitian.sub
    (referenceBlock_posSemidef _ (CFC.negPart_nonneg E).posSemidef X hX).isHermitian

theorem hermitian_norm_bounds (D : Matrix I I ℂ) (hD : D.IsHermitian)
    (ε : ℝ) (hε : ‖D‖ ≤ ε) : -(ε • (1 : Matrix I I ℂ)) ≤ D ∧ D ≤ ε • 1 := by
  have hs : (‖D‖ • (1 : Matrix I I ℂ)) ≤ ε • 1 := by
    rw [Matrix.le_iff, ← sub_smul]
    exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hε)
  have hu := IsSelfAdjoint.le_algebraMap_norm_self D hD.isSelfAdjoint
  have hl := IsSelfAdjoint.neg_algebraMap_norm_le_self D hD.isSelfAdjoint
  rw [Algebra.algebraMap_eq_smul_one] at hu hl
  exact ⟨(neg_le_neg hs).trans hl, hu.trans hs⟩

theorem referenceBlock_order_bounds (D : Matrix I I ℂ) (hD : D.IsHermitian)
    (ε : ℝ) (hε : ‖D‖ ≤ ε) (X : Matrix (I × R) (I × R) ℂ) (hX : X.PosSemidef) :
    -(ε • referenceMarginal X) ≤ referenceBlock D X ∧
      referenceBlock D X ≤ ε • referenceMarginal X := by
  obtain ⟨hl, hu⟩ := hermitian_norm_bounds D hD ε hε
  have hp := referenceBlock_posSemidef (ε • 1 + D) (by
    simpa only [sub_neg_eq_add, add_comm] using Matrix.le_iff.mp hl) X hX
  have hm := referenceBlock_posSemidef (ε • 1 - D) (Matrix.le_iff.mp hu) X hX
  rw [referenceBlock_add, referenceBlock_smul] at hp
  rw [referenceBlock_sub, referenceBlock_smul] at hm
  exact ⟨by
    rw [Matrix.le_iff, sub_neg_eq_add]
    simpa only [referenceMarginal, add_comm] using hp,
    by simpa only [referenceMarginal, Matrix.le_iff] using hm⟩

theorem trace_pair_nonneg {A B : Matrix R R ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  have hs : (CFC.sqrt A).conjTranspose = CFC.sqrt A := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hp : (CFC.sqrt A * B * CFC.sqrt A).PosSemidef := by
    simpa only [hs] using hB.mul_mul_conjTranspose_same (CFC.sqrt A)
  have ht : (CFC.sqrt A * B * CFC.sqrt A).trace = (A * B).trace := by
    rw [Matrix.trace_mul_cycle, ← pow_two, CFC.sq_sqrt A hA.nonneg]
  exact (Complex.nonneg_iff.mp (ht ▸ hp.trace_nonneg)).1

def positiveIndicator (x : ℝ) : ℝ := if 0 < x then 1 else 0

def positiveSupport (A : Matrix R R ℂ) : Matrix R R ℂ := cfc positiveIndicator A

theorem positiveSupport_bounds (A : Matrix R R ℂ) (hA : A.IsHermitian) :
    (positiveSupport A).PosSemidef ∧ (1 - positiveSupport A).PosSemidef := by
  have hp : (positiveSupport A).PosSemidef := by
    refine (show (0 : Matrix R R ℂ) ≤ cfc positiveIndicator A from ?_).posSemidef
    apply cfc_nonneg (p := IsSelfAdjoint)
    intro x hx
    simp only [positiveIndicator]
    split_ifs <;> norm_num
  have hc : 1 - positiveSupport A = cfc (fun x : ℝ => 1 - positiveIndicator x) A := by
    rw [cfc_sub (p := IsSelfAdjoint) (fun _ : ℝ => 1) positiveIndicator A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_const_one (p := IsSelfAdjoint) ℝ A hA.isSelfAdjoint]
    rfl
  refine ⟨hp, ?_⟩
  rw [hc]
  refine (show (0 : Matrix R R ℂ) ≤ cfc (fun x : ℝ => 1 - positiveIndicator x) A from ?_).posSemidef
  apply cfc_nonneg (p := IsSelfAdjoint)
  intro x hx
  simp only [positiveIndicator]
  split_ifs <;> norm_num

theorem positiveSupport_mul (A : Matrix R R ℂ) (hA : A.IsHermitian) :
    positiveSupport A * A = A⁺ := by
  have hf : (fun x : ℝ => positiveIndicator x * x) = (fun x : ℝ => x⁺) := by
    funext x
    by_cases hx : 0 < x
    · simp [positiveIndicator, hx, posPart_eq_self.mpr (le_of_lt hx)]
    · simp [positiveIndicator, hx, posPart_eq_zero.mpr (le_of_not_gt hx)]
  calc
    positiveSupport A * A = cfc positiveIndicator A * cfc (fun x : ℝ => x) A := by
      rw [cfc_id' (p := IsSelfAdjoint) ℝ A hA.isSelfAdjoint]
      rfl
    _ = cfc (fun x : ℝ => positiveIndicator x * x) A :=
      (cfc_mul (p := IsSelfAdjoint) positiveIndicator (fun x : ℝ => x) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)).symm
    _ = A⁺ := by rw [hf, CFC.posPart_def, cfcₙ_eq_cfc]

theorem traceNorm_eq_support (A : Matrix R R ℂ) (hA : A.IsHermitian) :
    traceNorm A = 2 * (positiveSupport A * A).trace.re - A.trace.re := by
  have hp : (positiveSupport A * A).trace.re = A⁺.trace.re := by rw [positiveSupport_mul A hA]
  have hn : traceNorm A = A⁺.trace.re + A⁻.trace.re := by
    rw [traceNorm, ← CFC.posPart_add_negPart A hA.isSelfAdjoint, Matrix.trace_add, Complex.add_re]
  have ht : A.trace.re = A⁺.trace.re - A⁻.trace.re := by
    have h := congrArg (fun M : Matrix R R ℂ => M.trace.re)
      (CFC.posPart_sub_negPart A hA.isSelfAdjoint)
    simpa only [Matrix.trace_sub, Complex.sub_re] using h.symm
  linarith

theorem traceNorm_le_of_order (A B : Matrix R R ℂ) (hA : A.IsHermitian)
    (hl : -B ≤ A) (hu : A ≤ B) : traceNorm A ≤ B.trace.re := by
  obtain ⟨hS, hSc⟩ := positiveSupport_bounds A hA
  have hp := trace_pair_nonneg hS (Matrix.le_iff.mp hu)
  have hn := trace_pair_nonneg hSc (show (B + A).PosSemidef from by
    simpa only [sub_neg_eq_add, add_comm] using Matrix.le_iff.mp hl)
  simp only [mul_sub, Matrix.trace_sub, Complex.sub_re] at hp
  simp only [sub_mul, one_mul, mul_add, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re] at hn
  rw [traceNorm_eq_support A hA]
  linarith

theorem referenceBlock_traceNorm_le (D : Matrix I I ℂ) (hD : D.IsHermitian)
    (ε : ℝ) (hε : ‖D‖ ≤ ε) (X : Matrix (I × R) (I × R) ℂ) (hX : X.PosSemidef) :
    traceNorm (referenceBlock D X) ≤ ε * X.trace.re := by
  obtain ⟨hl, hu⟩ := referenceBlock_order_bounds D hD ε hε X hX
  have hb := traceNorm_le_of_order _ _ (referenceBlock_isHermitian D hD X hX) hl hu
  simpa only [Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, referenceMarginal_trace] using hb

end
end QuantumProver.ElegantJointMeasurement.Teleportation.ReferenceStability

namespace QuantumProver.ElegantJointMeasurement.Teleportation.ReferenceStability
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix
noncomputable section
set_option maxHeartbeats 800000
variable {I R L : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
  [Fintype L] [DecidableEq L]

theorem referenceBlock_eq_partialTrace (E : Matrix I I ℂ)
    (X : Matrix (I × R) (I × R) ℂ) :
    referenceBlock E X = referenceMarginal ((E ⊗ₖ (1 : Matrix R R ℂ)) * X) := by
  ext r s
  rw [referenceMarginal_apply]
  simp [referenceBlock, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply]

theorem blockDiagonal_posSemidef (B : L → Matrix R R ℂ) (hB : ∀ j, (B j).PosSemidef) :
    (Matrix.blockDiagonal B).PosSemidef := by
  have hg : Matrix.blockDiagonal (fun j => CFC.sqrt (B j)) *
      (Matrix.blockDiagonal (fun j => CFC.sqrt (B j))).conjTranspose = Matrix.blockDiagonal B := by
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    congr 1
    funext j
    have hs : (CFC.sqrt (B j)).conjTranspose = CFC.sqrt (B j) :=
      (CFC.sqrt_nonneg (B j)).posSemidef.isHermitian
    rw [hs, ← pow_two, CFC.sq_sqrt (B j) (hB j).nonneg]
  exact hg ▸ Matrix.posSemidef_self_mul_conjTranspose _

theorem abs_blockDiagonal (B : L → Matrix R R ℂ) :
    CFC.abs (Matrix.blockDiagonal B) = Matrix.blockDiagonal (fun j => CFC.abs (B j)) := by
  have hm : Matrix.blockDiagonal (fun j => CFC.abs (B j)) *
      Matrix.blockDiagonal (fun j => CFC.abs (B j)) =
        (Matrix.blockDiagonal B).conjTranspose * Matrix.blockDiagonal B := by
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
    congr 1
    funext j
    simpa only [Matrix.star_eq_conjTranspose] using CFC.abs_mul_abs (B j)
  rw [CFC.abs, Matrix.star_eq_conjTranspose]
  exact CFC.sqrt_unique hm
    (blockDiagonal_posSemidef _ (fun j => (CFC.abs_nonneg (B j)).posSemidef)).nonneg

theorem traceNorm_blockDiagonal (B : L → Matrix R R ℂ) :
    traceNorm (Matrix.blockDiagonal B) = ∑ j, traceNorm (B j) := by
  simp [traceNorm, abs_blockDiagonal, Matrix.trace_blockDiagonal]

theorem abs_submatrix_equiv {O : Type*} [Fintype O] [DecidableEq O]
    (e : O ≃ R) (X : Matrix R R ℂ) :
    CFC.abs (X.submatrix e e) = (CFC.abs X).submatrix e e := by
  have hm : (CFC.abs X).submatrix e e * (CFC.abs X).submatrix e e =
      (X.submatrix e e).conjTranspose * X.submatrix e e := by
    rw [Matrix.submatrix_mul_equiv, CFC.abs_mul_abs, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [CFC.abs, Matrix.star_eq_conjTranspose]
  exact CFC.sqrt_unique hm ((CFC.abs_nonneg X).posSemidef.submatrix e).nonneg

theorem traceNorm_submatrix_equiv {O : Type*} [Fintype O] [DecidableEq O]
    (e : O ≃ R) (X : Matrix R R ℂ) : traceNorm (X.submatrix e e) = traceNorm X := by
  rw [traceNorm, abs_submatrix_equiv]
  exact congrArg Complex.re (MixedLocalAncillas.trace_submatrix_equiv e (CFC.abs X))

theorem traceNorm_zero : traceNorm (0 : Matrix R R ℂ) = 0 := by simp [traceNorm]

def sharedBlocks (B : L → Matrix R R ℂ) :
    Matrix ((L × L) × R) ((L × L) × R) ℂ :=
  ∑ j, Tomography.sharedProjector j ⊗ₖ B j

omit [Fintype R] [DecidableEq R] in
theorem sharedBlocks_eq_blockDiagonal (B : L → Matrix R R ℂ) :
    sharedBlocks B = (Matrix.blockDiagonal (fun p : L × L =>
      if p.1 = p.2 then B p.1 else 0)).submatrix
        (Equiv.prodComm (L × L) R) (Equiv.prodComm (L × L) R) := by
  ext ⟨⟨a, b⟩, r⟩ ⟨⟨c, d⟩, s⟩
  by_cases hp : (a, b) = (c, d)
  · obtain ⟨hc, hd⟩ := Prod.mk.inj hp
    subst c
    subst d
    by_cases hab : a = b
    · subst b
      simp [sharedBlocks, Tomography.sharedProjector, Matrix.sum_apply,
        Matrix.blockDiagonal_apply]
    · have hj : ∀ j : L, (a, b) ≠ (j, j) := by
        intro j h
        obtain ⟨ha, hb⟩ := Prod.mk.inj h
        exact hab (ha.trans hb.symm)
      simp [sharedBlocks, Tomography.sharedProjector, Matrix.sum_apply,
        Matrix.blockDiagonal_apply, hj, hab]
  · simp [sharedBlocks, Tomography.sharedProjector, Matrix.sum_apply,
      Matrix.blockDiagonal_apply, hp]

theorem sharedBlocks_posSemidef (B : L → Matrix R R ℂ) (hB : ∀ j, (B j).PosSemidef) :
    (sharedBlocks B).PosSemidef := by
  rw [sharedBlocks_eq_blockDiagonal]
  apply Matrix.PosSemidef.submatrix
  apply blockDiagonal_posSemidef
  intro p
  split_ifs
  · exact hB p.1
  · exact Matrix.PosSemidef.zero

theorem traceNorm_sharedBlocks (B : L → Matrix R R ℂ) :
    traceNorm (sharedBlocks B) = ∑ j, traceNorm (B j) := by
  rw [sharedBlocks_eq_blockDiagonal, traceNorm_submatrix_equiv, traceNorm_blockDiagonal]
  simp [Fintype.sum_prod_type, apply_ite, traceNorm_zero]

def referenceMeasurement (F : L → Matrix I I ℂ) (X : Matrix (I × R) (I × R) ℂ) :
    Matrix ((L × L) × R) ((L × L) × R) ℂ :=
  sharedBlocks (fun j => referenceBlock (F j) X)

theorem referenceMeasurement_posSemidef (F : L → Matrix I I ℂ)
    (hF : ∀ j, (F j).PosSemidef) (X : Matrix (I × R) (I × R) ℂ) (hX : X.PosSemidef) :
    (referenceMeasurement F X).PosSemidef :=
  sharedBlocks_posSemidef _ (fun j => referenceBlock_posSemidef (F j) (hF j) X hX)

omit [DecidableEq I] [Fintype R] [DecidableEq R] in
theorem referenceMeasurement_sub (F G : L → Matrix I I ℂ)
    (X : Matrix (I × R) (I × R) ℂ) :
    referenceMeasurement F X - referenceMeasurement G X =
      sharedBlocks (fun j => referenceBlock (F j - G j) X) := by
  ext p q
  simp [referenceMeasurement, sharedBlocks, referenceBlock_sub,
    Matrix.sum_apply, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem referenceMeasurement_traceNorm_le (F G : L → Matrix I I ℂ)
    (hF : ∀ j, (F j).IsHermitian) (hG : ∀ j, (G j).IsHermitian)
    (ε : ℝ) (hε : ∀ j, ‖F j - G j‖ ≤ ε)
    (X : Matrix (I × R) (I × R) ℂ) (hX : X.PosSemidef) :
    traceNorm (referenceMeasurement F X - referenceMeasurement G X) ≤
      (Fintype.card L : ℝ) * ε * X.trace.re := by
  rw [referenceMeasurement_sub, traceNorm_sharedBlocks]
  calc
    ∑ j, traceNorm (referenceBlock (F j - G j) X) ≤ ∑ _j : L, ε * X.trace.re :=
      Finset.sum_le_sum (fun j _ => referenceBlock_traceNorm_le _
        ((hF j).sub (hG j)) ε (hε j) X hX)
    _ = (Fintype.card L : ℝ) * ε * X.trace.re := by simp [mul_assoc]

def measurementLinear (F : L → Matrix I I ℂ) :
    Matrix I I ℂ →ₗ[ℂ] Matrix (L × L) (L × L) ℂ where
  toFun := Tomography.measurementChannel F
  map_add' X Y := by
    simp [Tomography.measurementChannel, Matrix.mul_add, Matrix.trace_add,
      add_smul, Finset.sum_add_distrib]
  map_smul' z X := by
    simp [Tomography.measurementChannel, Matrix.trace_smul,
      smul_smul, Finset.smul_sum]

@[simp] theorem measurementLinear_apply (F : L → Matrix I I ℂ) (X : Matrix I I ℂ) :
    measurementLinear F X = Tomography.measurementChannel F X := rfl

def referenceAmplification {O : Type*} (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (X : Matrix (I × R) (I × R) ℂ) : Matrix (O × R) (O × R) ℂ :=
  fun p q => Φ (fun i k => X (i, p.2) (k, q.2)) p.1 q.1

omit [Fintype R] [DecidableEq R] in
theorem referenceMeasurement_eq_amplification (F : L → Matrix I I ℂ)
    (X : Matrix (I × R) (I × R) ℂ) :
    referenceMeasurement F X = referenceAmplification (measurementLinear F) X := by
  ext ⟨u, r⟩ ⟨v, s⟩
  change referenceMeasurement F X (u, r) (v, s) =
    (measurementLinear F (fun i k => X (i, r) (k, s))) u v
  calc
    referenceMeasurement F X (u, r) (v, s) =
        Tomography.measurementChannel F (Matrix.of (fun i k => X (i, r) (k, s))) u v := by
      have hb (j : L) :
          (F j * Matrix.of (fun i k => X (i, r) (k, s))).trace = referenceBlock (F j) X r s := rfl
      simp only [referenceMeasurement, sharedBlocks, Tomography.measurementChannel,
        Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.kronecker_apply, hb]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    _ = _ := (congrArg (fun A : Matrix (L × L) (L × L) ℂ => A u v)
      (measurementLinear_apply F (fun i k => X (i, r) (k, s)))).symm

omit [Fintype I] [DecidableEq I] in
theorem referenceAmplification_eq_matrix {O : Type*} [Fintype O] [DecidableEq O]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (k : ℕ)
    (X : Matrix (I × Fin k) (I × Fin k) ℂ) :
    referenceAmplification Φ X =
      (QuantumProver.ElegantJointMeasurement.CP.amplification Φ k (X.submatrix (Equiv.prodComm (Fin k) I)
        (Equiv.prodComm (Fin k) I))).submatrix (Equiv.prodComm O (Fin k))
          (Equiv.prodComm O (Fin k)) := rfl

theorem four_effect_reference_traceNorm_le (F G : Fin 4 → Matrix I I ℂ)
    (hF : ∀ j, (F j).IsHermitian) (hG : ∀ j, (G j).IsHermitian)
    (ε : ℝ) (hε : ∀ j, ‖F j - G j‖ ≤ ε)
    (X : Matrix (I × R) (I × R) ℂ) (hX : X.PosSemidef) (ht : X.trace = 1) :
    traceNorm (referenceAmplification (measurementLinear F) X -
      referenceAmplification (measurementLinear G) X) ≤ 4 * ε := by
  rw [← referenceMeasurement_eq_amplification, ← referenceMeasurement_eq_amplification]
  simpa [ht] using referenceMeasurement_traceNorm_le F G hF hG ε hε X hX

end
end QuantumProver.ElegantJointMeasurement.Teleportation.ReferenceStability

namespace QuantumProver.ElegantJointMeasurement.Teleportation.ReferenceStability
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix
noncomputable section
variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

theorem true_l2_norm (D : Matrix I I ℂ) :
    ‖D‖ = ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) D‖ :=
  Matrix.cstar_norm_def D

def maximumEffectError (F G : Fin 4 → Matrix I I ℂ) : ℝ := ‖F - G‖

theorem maximumEffectError_le_iff (F G : Fin 4 → Matrix I I ℂ) (ε : ℝ) (hε : 0 ≤ ε) :
    maximumEffectError F G ≤ ε ↔
      ∀ j, ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (F j - G j)‖ ≤ ε := by
  rw [maximumEffectError, pi_norm_le_iff_of_nonneg hε]
  simp only [Pi.sub_apply, true_l2_norm]

theorem traceNorm_nonneg (A : Matrix R R ℂ) : 0 ≤ traceNorm A :=
  (Complex.nonneg_iff.mp (CFC.abs_nonneg A).posSemidef.trace_nonneg).1

theorem four_effect_reference_traceNorm_le_of_max (F G : Fin 4 → Matrix I I ℂ)
    (hF : ∀ j, (F j).IsHermitian) (hG : ∀ j, (G j).IsHermitian)
    (ε : ℝ) (hmax : ‖F - G‖ ≤ ε)
    (X : Matrix (I × R) (I × R) ℂ) (hX : X.PosSemidef) (ht : X.trace = 1) :
    traceNorm (referenceAmplification (measurementLinear F) X -
      referenceAmplification (measurementLinear G) X) ≤ 4 * ε := by
  apply four_effect_reference_traceNorm_le F G hF hG ε _ X hX ht
  intro j
  simpa only [Pi.sub_apply] using (norm_le_pi_norm (F - G) j).trans hmax

theorem four_effect_reference_traceNorm_le_euclidean (F G : Fin 4 → Matrix I I ℂ)
    (hF : ∀ j, (F j).IsHermitian) (hG : ∀ j, (G j).IsHermitian)
    (ε : ℝ) (hε : ∀ j, ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (F j - G j)‖ ≤ ε)
    (X : Matrix (I × R) (I × R) ℂ) (hX : X.PosSemidef) (ht : X.trace = 1) :
    traceNorm (referenceAmplification (measurementLinear F) X -
      referenceAmplification (measurementLinear G) X) ≤ 4 * ε := by
  apply four_effect_reference_traceNorm_le F G hF hG ε _ X hX ht
  intro j
  rw [true_l2_norm]
  exact hε j

theorem four_effect_reference_traceNorm_le_error (F G : Fin 4 → Matrix I I ℂ)
    (hF : ∀ j, (F j).IsHermitian) (hG : ∀ j, (G j).IsHermitian)
    (X : Matrix (I × R) (I × R) ℂ) (hX : X.PosSemidef) (ht : X.trace = 1) :
    traceNorm (referenceAmplification (measurementLinear F) X -
      referenceAmplification (measurementLinear G) X) ≤ 4 * maximumEffectError F G :=
  four_effect_reference_traceNorm_le_of_max F G hF hG _ (le_refl _) X hX ht

theorem four_effect_reference_difference_tendsto {T : Type*} (l : Filter T)
    (F : T → Fin 4 → Matrix I I ℂ) (G : Fin 4 → Matrix I I ℂ)
    (hF : ∀ t j, (F t j).IsHermitian) (hG : ∀ j, (G j).IsHermitian)
    (hnorm : Filter.Tendsto (fun t => ‖F t - G‖) l (nhds (0 : ℝ)))
    (X : Matrix (I × R) (I × R) ℂ) (hX : X.PosSemidef) (ht : X.trace = 1) :
    Filter.Tendsto (fun t => traceNorm (referenceAmplification (measurementLinear (F t)) X -
      referenceAmplification (measurementLinear G) X)) l (nhds (0 : ℝ)) := by
  have hb := fun t => four_effect_reference_traceNorm_le_of_max (F t) G (hF t) hG
    ‖F t - G‖ (le_refl _) X hX ht
  have hc : Filter.Tendsto (fun t => 4 * ‖F t - G‖) l (nhds (0 : ℝ)) := by
    simpa using hnorm.const_mul 4
  exact squeeze_zero' (Filter.Eventually.of_forall (fun t => traceNorm_nonneg _))
    (Filter.Eventually.of_forall hb) hc

end
end QuantumProver.ElegantJointMeasurement.Teleportation.ReferenceStability

namespace QuantumProver.ElegantJointMeasurement.Teleportation.ReferenceStability
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix
noncomputable section
variable {I R L : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
  [Fintype L] [DecidableEq L]

theorem measurementLinear_completelyPositive (F : L → Matrix I I ℂ)
    (hF : ∀ j, (F j).PosSemidef) : QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (measurementLinear F) := by
  intro k X hX
  have he : QuantumProver.ElegantJointMeasurement.CP.amplification (measurementLinear F) k X =
      (referenceMeasurement F (X.submatrix (Equiv.prodComm I (Fin k))
        (Equiv.prodComm I (Fin k)))).submatrix (Equiv.prodComm (Fin k) (L × L))
          (Equiv.prodComm (Fin k) (L × L)) := by
    rw [referenceMeasurement_eq_amplification]
    rfl
  rw [he]
  exact (referenceMeasurement_posSemidef F hF _
    (hX.submatrix (Equiv.prodComm I (Fin k)))).submatrix (Equiv.prodComm (Fin k) (L × L))

theorem trace_sharedProjector (j : L) : (Tomography.sharedProjector j).trace = 1 := by
  simp [Tomography.sharedProjector, Matrix.trace_diagonal]

theorem measurementLinear_trace (F : L → Matrix I I ℂ) (X : Matrix I I ℂ) :
    (measurementLinear F X).trace = ((∑ j, F j) * X).trace := by
  rw [measurementLinear_apply, Tomography.measurementChannel, Matrix.trace_sum,
    Matrix.sum_mul, Matrix.trace_sum]
  simp [Matrix.trace_smul, trace_sharedProjector]

theorem measurementLinear_trace_preserving (F : L → Matrix I I ℂ) (hF : ∑ j, F j = 1)
    (X : Matrix I I ℂ) : (measurementLinear F X).trace = X.trace := by
  rw [measurementLinear_trace, hF, Matrix.one_mul]

omit [DecidableEq I] [DecidableEq R] in

theorem referenceAmplification_trace {O : Type*} [Fintype O] [DecidableEq O]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hΦ : ∀ Y, (Φ Y).trace = Y.trace) (X : Matrix (I × R) (I × R) ℂ) :
    (referenceAmplification Φ X).trace = X.trace := by
  change (∑ p : O × R, Φ (Matrix.of (fun i k => X (i, p.2) (k, p.2))) p.1 p.1) =
    ∑ p : I × R, X p p
  simp only [Fintype.sum_prod_type]
  calc
    ∑ o : O, ∑ r : R, Φ (Matrix.of (fun i k => X (i, r) (k, r))) o o =
        ∑ r : R, ∑ o : O, Φ (Matrix.of (fun i k => X (i, r) (k, r))) o o := Finset.sum_comm
    _ = ∑ r : R, ∑ i : I, X (i, r) (i, r) := by
      apply Finset.sum_congr rfl
      intro r _
      exact hΦ (Matrix.of (fun i k => X (i, r) (k, r)))
    _ = ∑ i : I, ∑ r : R, X (i, r) (i, r) := Finset.sum_comm

omit [DecidableEq R] in
theorem referenceMeasurement_trace (F : L → Matrix I I ℂ) (hF : ∑ j, F j = 1)
    (X : Matrix (I × R) (I × R) ℂ) : (referenceMeasurement F X).trace = X.trace := by
  rw [referenceMeasurement_eq_amplification]
  exact referenceAmplification_trace _ (measurementLinear_trace_preserving F hF) X

end
end QuantumProver.ElegantJointMeasurement.Teleportation.ReferenceStability

namespace QuantumProver.ElegantJointMeasurement.Teleportation.ReferenceStability
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix
noncomputable section
variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

omit [Fintype R] [DecidableEq R] in

theorem copied_channel_reference_identity (Γ : ChannelFirstEffects.Channel (κ := I))
    (X : Matrix (I × R) (I × R) ℂ) :
    referenceAmplification (ClassicalOutputRepair.copyAlice.comp Γ) X =
      referenceMeasurement (ChannelFirstEffects.firstEffect Γ) X := by
  rw [referenceMeasurement_eq_amplification]
  ext ⟨u, r⟩ ⟨v, s⟩
  change ClassicalOutputRepair.copyAlice (Γ (Matrix.of (fun i k => X (i, r) (k, s)))) u v =
    (measurementLinear (ChannelFirstEffects.firstEffect Γ)
      (Matrix.of (fun i k => X (i, r) (k, s)))) u v
  exact congrArg (fun A : ClassicalOutputRepair.OutputMatrix => A u v)
    ((ChannelFirstEffects.copy_channel_eq_measurement Γ
      (Matrix.of (fun i k => X (i, r) (k, s)))).trans
        (measurementLinear_apply _ (Matrix.of (fun i k => X (i, r) (k, s)))).symm)

theorem copied_channel_reference_traceNorm_le
    (Γ Δ : ChannelFirstEffects.Channel (κ := I))
    (hΓ : ChannelFirstEffects.PositiveChannel Γ) (hΔ : ChannelFirstEffects.PositiveChannel Δ)
    (ε : ℝ) (hε : ∀ j, ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)
      (ChannelFirstEffects.firstEffect Γ j - ChannelFirstEffects.firstEffect Δ j)‖ ≤ ε)
    (X : Matrix (I × R) (I × R) ℂ) (hX : X.PosSemidef) (ht : X.trace = 1) :
    traceNorm (referenceAmplification (ClassicalOutputRepair.copyAlice.comp Γ) X -
      referenceAmplification (ClassicalOutputRepair.copyAlice.comp Δ) X) ≤ 4 * ε := by
  rw [copied_channel_reference_identity, copied_channel_reference_identity,
    referenceMeasurement_eq_amplification, referenceMeasurement_eq_amplification]
  exact four_effect_reference_traceNorm_le_euclidean _ _
    (ChannelFirstEffects.firstEffect_isHermitian Γ hΓ)
    (ChannelFirstEffects.firstEffect_isHermitian Δ hΔ) ε hε X hX ht

end
end QuantumProver.ElegantJointMeasurement.Teleportation.ReferenceStability
