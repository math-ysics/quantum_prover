import QuantumProver.InformationTheory.ElegantJointMeasurement.TailReferencePurity

open scoped BigOperators ComplexConjugate Matrix
open InnerProductSpace QuantumProver.ElegantJointMeasurement.TailReference

namespace QuantumProver.ElegantJointMeasurement.SchmidtResource

noncomputable section

set_option maxHeartbeats 600000

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def conjugateRow (M : Matrix κ κ ℂ) (i : κ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun j => conj (M i j))

theorem inner_conjugateRow (M : Matrix κ κ ℂ) (i j : κ) :
    ⟪conjugateRow M i, conjugateRow M j⟫_ℂ = (M * Mᴴ) i j := by
  simp [conjugateRow, EuclideanSpace.inner_toLp_toLp, dotProduct,
    Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]

def normalizedConjugateRow (M : Matrix κ κ ℂ) (β : κ → ℝ) (i : κ) :
    EuclideanSpace ℂ κ := (β i : ℂ)⁻¹ • conjugateRow M i

theorem normalizedConjugateRows_orthonormal (M : Matrix κ κ ℂ) (β : κ → ℝ)
    (hGram : M * Mᴴ = Matrix.diagonal (fun i => ((β i ^ 2 : ℝ) : ℂ))) :
    Orthonormal ℂ (({i | 0 < β i} : Set κ).domRestrict (normalizedConjugateRow M β)) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  have hi : (β i.1 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt i.2)
  have hj : (β j.1 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt j.2)
  change ⟪(β i.1 : ℂ)⁻¹ • conjugateRow M i.1,
    (β j.1 : ℂ)⁻¹ • conjugateRow M j.1⟫_ℂ = _
  rw [inner_smul_left, inner_smul_right, inner_conjugateRow, hGram]
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply, hi]
    field_simp
  · have hval : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    simp [Matrix.diagonal_apply, hval, hij]

theorem conjugateRow_eq_zero_of_amplitude_zero (M : Matrix κ κ ℂ) (β : κ → ℝ)
    (hGram : M * Mᴴ = Matrix.diagonal (fun i => ((β i ^ 2 : ℝ) : ℂ)))
    (i : κ) (hi : β i = 0) : conjugateRow M i = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [inner_conjugateRow, hGram]
  simp [hi]

def basisUnitary (b : OrthonormalBasis κ ℂ (EuclideanSpace ℂ κ)) :
    unitary (Matrix κ κ ℂ) :=
  ⟨(EuclideanSpace.basisFun κ ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun κ ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩

theorem basisUnitary_apply (b : OrthonormalBasis κ ℂ (EuclideanSpace ℂ κ)) (i j : κ) :
    (basisUnitary b : Matrix κ κ ℂ) i j = b j i := rfl

theorem exists_right_unitary_of_diagonal_leftGram
    (M : Matrix κ κ ℂ) (β : κ → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (hGram : M * Mᴴ = Matrix.diagonal (fun i => ((β i ^ 2 : ℝ) : ℂ))) :
    ∃ V : unitary (Matrix κ κ ℂ),
      M = Matrix.diagonal (fun i => (β i : ℂ)) * (V : Matrix κ κ ℂ)ᵀ := by
  have horth := normalizedConjugateRows_orthonormal M β hGram
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq finrank_euclideanSpace
  refine ⟨Matrix.UnitaryGroup.map_star (basisUnitary b), ?_⟩
  have htranspose : (Matrix.UnitaryGroup.map_star (basisUnitary b) : Matrix κ κ ℂ)ᵀ =
      (basisUnitary b : Matrix κ κ ℂ)ᴴ := rfl
  rw [htranspose]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.conjTranspose_apply, basisUnitary_apply]
  by_cases hi : β i = 0
  · have hz := conjugateRow_eq_zero_of_amplitude_zero M β hGram i hi
    have hentry := congrArg (fun z : EuclideanSpace ℂ κ => conj (z j)) hz
    have hzero : M i j = 0 := by simpa [conjugateRow] using hentry
    simp [hi, hzero]
  · have hpos : 0 < β i := lt_of_le_of_ne (hβ i) (Ne.symm hi)
    have hbi : conj (b i j) = (β i : ℂ)⁻¹ * M i j := by
      rw [hb i hpos]
      simp [normalizedConjugateRow, conjugateRow, map_mul]
    have hcomplex : (β i : ℂ) ≠ 0 := by exact_mod_cast hi
    have hscaled := congrArg (fun z : ℂ => (β i : ℂ) * z) hbi
    simpa only [← mul_assoc, mul_inv_cancel₀ hcomplex, one_mul, Complex.star_def] using hscaled.symm

def leftSchmidtCoordinates (Ψ : Matrix κ κ ℂ) : Matrix κ κ ℂ :=
  (reducedSchmidtUnitary Ψ : Matrix κ κ ℂ)ᴴ * Ψ

theorem leftSchmidtCoordinates_gram (Ψ : Matrix κ κ ℂ) :
    leftSchmidtCoordinates Ψ * (leftSchmidtCoordinates Ψ)ᴴ =
      resourceGram (reducedSchmidtAmplitude Ψ) := by
  let U : Matrix κ κ ℂ := reducedSchmidtUnitary Ψ
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self (reducedSchmidtUnitary Ψ)
  change (Uᴴ * Ψ) * (Uᴴ * Ψ)ᴴ = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    (Uᴴ * Ψ) * (Ψᴴ * U) = Uᴴ * (Ψ * Ψᴴ) * U := by simp only [Matrix.mul_assoc]
    _ = Uᴴ * (U * resourceGram (reducedSchmidtAmplitude Ψ) * Uᴴ) * U := by
      rw [leftGram_eq_reducedSchmidt_conjugate Ψ]
    _ = (Uᴴ * U) * resourceGram (reducedSchmidtAmplitude Ψ) * (Uᴴ * U) := by
      simp only [Matrix.mul_assoc]
    _ = resourceGram (reducedSchmidtAmplitude Ψ) := by rw [hU, Matrix.one_mul, Matrix.mul_one]

theorem square_coefficient_schmidt (Ψ : Matrix κ κ ℂ) :
    ∃ V : unitary (Matrix κ κ ℂ),
      Ψ = (reducedSchmidtUnitary Ψ : Matrix κ κ ℂ) *
        Matrix.diagonal (fun k => (reducedSchmidtAmplitude Ψ k : ℂ)) * (V : Matrix κ κ ℂ)ᵀ := by
  obtain ⟨V, hV⟩ := exists_right_unitary_of_diagonal_leftGram (leftSchmidtCoordinates Ψ)
    (reducedSchmidtAmplitude Ψ) (reducedSchmidtAmplitude_nonneg Ψ)
    (by rw [leftSchmidtCoordinates_gram, resourceGram_eq_diagonal])
  refine ⟨V, ?_⟩
  calc
    Ψ = (reducedSchmidtUnitary Ψ : Matrix κ κ ℂ) * leftSchmidtCoordinates Ψ := by
      unfold leftSchmidtCoordinates
      have hU : (reducedSchmidtUnitary Ψ : Matrix κ κ ℂ) *
          (reducedSchmidtUnitary Ψ : Matrix κ κ ℂ)ᴴ = 1 :=
        Unitary.coe_mul_star_self (reducedSchmidtUnitary Ψ)
      rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
    _ = (reducedSchmidtUnitary Ψ : Matrix κ κ ℂ) *
        (Matrix.diagonal (fun k => (reducedSchmidtAmplitude Ψ k : ℂ)) * (V : Matrix κ κ ℂ)ᵀ) := by
      rw [hV]
    _ = _ := by rw [Matrix.mul_assoc]

theorem exists_squareSchmidtRepresentation (Ψ : Matrix κ κ ℂ)
    (hΨ : Matrix.trace (Ψ * Ψᴴ) = 1) :
    ∃ (β : κ → ℝ) (U V : unitary (Matrix κ κ ℂ)),
      (∀ k, 0 ≤ β k) ∧ (∑ k, β k ^ 2 = 1) ∧
      Ψ = (U : Matrix κ κ ℂ) * Matrix.diagonal (fun k => (β k : ℂ)) * (V : Matrix κ κ ℂ)ᵀ := by
  obtain ⟨V, hV⟩ := square_coefficient_schmidt Ψ
  exact ⟨reducedSchmidtAmplitude Ψ, reducedSchmidtUnitary Ψ, V,
    reducedSchmidtAmplitude_nonneg Ψ, reducedSchmidtAmplitude_normalized Ψ hΨ, hV⟩

end

end QuantumProver.ElegantJointMeasurement.SchmidtResource

namespace QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding

noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
open QuantumProver.ElegantJointMeasurement.TailReference

variable {κ η : Type*} [Fintype κ] [DecidableEq κ] [Fintype η] [DecidableEq η]

def coefficient (Psi : Matrix κ η ℂ) : Matrix (κ ⊕ η) (κ ⊕ η) ℂ :=
  Matrix.fromBlocks 0 Psi 0 0

def leftMatrix (A : Matrix κ κ ℂ) : Matrix (κ ⊕ η) (κ ⊕ η) ℂ :=
  Matrix.fromBlocks A 0 0 0

theorem coefficient_leftGram (Psi : Matrix κ η ℂ) :
    coefficient Psi * (coefficient Psi)ᴴ = leftMatrix (η := η) (Psi * Psiᴴ) := by
  simp [coefficient, leftMatrix, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply]

theorem leftMatrix_trace (A : Matrix κ κ ℂ) :
    (leftMatrix (η := η) A).trace = A.trace := by
  simp [leftMatrix, Matrix.trace, Fintype.sum_sum_type, Matrix.fromBlocks]

theorem coefficient_mass (Psi : Matrix κ η ℂ) :
    (coefficient Psi * (coefficient Psi)ᴴ).trace = (Psi * Psiᴴ).trace := by
  rw [coefficient_leftGram, leftMatrix_trace]

def leftUnitary (U : unitary (Matrix κ κ ℂ)) : unitary (Matrix (κ ⊕ η) (κ ⊕ η) ℂ) :=
  ⟨Matrix.fromBlocks (U : Matrix κ κ ℂ) 0 0 (1 : Matrix η η ℂ), by
    have hU : (U : Matrix κ κ ℂ) * (U : Matrix κ κ ℂ)ᴴ = 1 :=
      Unitary.coe_mul_star_self U
    apply Matrix.mem_unitaryGroup_iff.mpr
    simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add, Matrix.conjTranspose_zero, Matrix.conjTranspose_one,
      hU, Matrix.one_mul, Matrix.fromBlocks_one]⟩

theorem leftMatrix_unitary_conjugate (U : unitary (Matrix κ κ ℂ))
    (A : Matrix κ κ ℂ) :
    leftMatrix (η := η) ((U : Matrix κ κ ℂ) * A * (U : Matrix κ κ ℂ)ᴴ) =
      (leftUnitary (η := η) U : Matrix (κ ⊕ η) (κ ⊕ η) ℂ) * leftMatrix (η := η) A *
        (leftUnitary (η := η) U : Matrix (κ ⊕ η) (κ ⊕ η) ℂ)ᴴ := by
  simp [leftUnitary, leftMatrix, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply]

def amplitudes (beta : κ → ℝ) : κ ⊕ η → ℝ := Sum.elim beta (fun _ => 0)

theorem leftMatrix_resourceGram (beta : κ → ℝ) :
    leftMatrix (η := η) (resourceGram beta) = resourceGram (amplitudes (η := η) beta) := by
  rw [leftMatrix, resourceGram_eq_diagonal, resourceGram_eq_diagonal]
  rw [← Matrix.diagonal_zero (n := η), Matrix.fromBlocks_diagonal]
  congr 1
  funext i
  cases i <;> simp [amplitudes]

theorem amplitudes_entropy (beta : κ → ℝ) :
    QuantumProver.ElegantJointMeasurement.Entropy.entropyBits (fun i => (amplitudes (η := η) beta i) ^ 2) =
      QuantumProver.ElegantJointMeasurement.Entropy.entropyBits (fun i => (beta i) ^ 2) := by
  simp [QuantumProver.ElegantJointMeasurement.Entropy.entropyBits, amplitudes, Fintype.sum_sum_type]

theorem coefficient_entropy (Psi : Matrix κ η ℂ) :
    vonNeumannEntropyBits (coefficient Psi * (coefficient Psi)ᴴ) =
      vonNeumannEntropyBits (Psi * Psiᴴ) := by
  have hGram : coefficient Psi * (coefficient Psi)ᴴ =
      (leftUnitary (η := η) (reducedSchmidtUnitary Psi) :
        Matrix (κ ⊕ η) (κ ⊕ η) ℂ) *
      resourceGram (amplitudes (η := η) (reducedSchmidtAmplitude Psi)) *
      (leftUnitary (η := η) (reducedSchmidtUnitary Psi) :
        Matrix (κ ⊕ η) (κ ⊕ η) ℂ)ᴴ := by
    rw [coefficient_leftGram, leftGram_eq_reducedSchmidt_conjugate,
      leftMatrix_unitary_conjugate, leftMatrix_resourceGram]
  rw [hGram, vonNeumannEntropy_unitary_conjugate _ _
    (resourceGram_posSemidef _).isHermitian.isSelfAdjoint,
    resource_vonNeumannEntropy_eq_entropyBits, amplitudes_entropy,
    rectangular_resource_entropy]

def aliceEmbedding : Matrix (κ ⊕ η) κ ℂ :=
  fun i k => if i = Sum.inl k then 1 else 0

def bobEmbedding : Matrix (κ ⊕ η) η ℂ :=
  fun i k => if i = Sum.inr k then 1 else 0

theorem aliceEmbedding_gram : (aliceEmbedding (κ := κ) (η := η))ᴴ *
    aliceEmbedding (κ := κ) (η := η) = 1 := by
  ext i j
  simp [aliceEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type, Matrix.one_apply, eq_comm]

theorem bobEmbedding_gram : (bobEmbedding (κ := κ) (η := η))ᴴ *
    bobEmbedding (κ := κ) (η := η) = 1 := by
  ext i j
  simp [bobEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sum_type, Matrix.one_apply, eq_comm]

theorem coefficient_eq_local_embeddings (Psi : Matrix κ η ℂ) :
    coefficient Psi = aliceEmbedding (κ := κ) (η := η) * Psi *
      (bobEmbedding (κ := κ) (η := η))ᵀ := by
  ext i j
  cases i <;> cases j <;>
    simp [coefficient, aliceEmbedding, bobEmbedding, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.fromBlocks]

theorem normalized_coefficient (Psi : Matrix κ η ℂ) (hPsi : (Psi * Psiᴴ).trace = 1) :
    (coefficient Psi * (coefficient Psi)ᴴ).trace = 1 :=
  (coefficient_mass Psi).trans hPsi

end
end QuantumProver.ElegantJointMeasurement.SchmidtResource.SquarePadding
