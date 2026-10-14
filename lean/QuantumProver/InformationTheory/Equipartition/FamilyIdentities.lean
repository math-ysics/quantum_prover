import QuantumProver.InformationTheory.Equipartition.PolarBounds
import QuantumProver.InformationTheory.Equipartition.TestingBounds

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace QuantumProver.Equipartition.FiniteModel.Testing

section UnitaryPartitionOrthogonality
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem diagonalSelector_orthogonal (label : ι → κ) {k l : κ} (hkl : k ≠ l) :
    diagonalSelector label k * diagonalSelector label l = 0 := by
  rw [diagonalSelector, diagonalSelector, Matrix.diagonal_mul_diagonal]
  ext r s
  by_cases hrs : r = s
  · subst s
    simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply]
    by_cases hkr : label r = k
    · have hlr : label r ≠ l := fun hlr => hkl (hkr.symm.trans hlr)
      simp [hkr, hkl]
    · simp [hkr]
  · simp [Matrix.diagonal_apply_ne _ hrs]

theorem unitaryPartitionProjection_orthogonal (U : Matrix.unitaryGroup ι ℂ)
    (label : ι → κ) {k l : κ} (hkl : k ≠ l) :
    unitaryPartitionProjection U label k * unitaryPartitionProjection U label l = 0 := by
  have hu : (U : CMat ι)ᴴ * (U : CMat ι) = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  let V : CMat ι := U
  let D : CMat ι := diagonalSelector label k
  let E : CMat ι := diagonalSelector label l
  change (V * D * Vᴴ) * (V * E * Vᴴ) = 0
  calc
    (V * D * Vᴴ) * (V * E * Vᴴ) = (V * D) * (Vᴴ * V) * (E * Vᴴ) := by
      noncomm_ring
    _ = (V * D) * (E * Vᴴ) := by rw [hu, Matrix.mul_one]
    _ = V * (D * E) * Vᴴ := by noncomm_ring
    _ = 0 := by rw [diagonalSelector_orthogonal label hkl, Matrix.mul_zero, Matrix.zero_mul]

theorem unitaryPartitionProjection_mul (U : Matrix.unitaryGroup ι ℂ)
    (label : ι → κ) (k l : κ) :
    unitaryPartitionProjection U label k * unitaryPartitionProjection U label l =
      if k = l then unitaryPartitionProjection U label k else 0 := by
  by_cases hkl : k = l
  · subst l
    simp only [if_pos rfl]
    exact unitaryPartitionProjection_idempotent U label k
  · rw [if_neg hkl]
    exact unitaryPartitionProjection_orthogonal U label hkl

end UnitaryPartitionOrthogonality

section SpectralPinchingCommutation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem spectralPinchingProjection_orthogonal {σ : CMat ι} (hσ : σ.IsHermitian)
    {k l : SpectralLabels hσ} (hkl : k ≠ l) :
    spectralPinchingProjection hσ k * spectralPinchingProjection hσ l = 0 := by
  classical
  exact unitaryPartitionProjection_orthogonal _ _ hkl

theorem spectralPinchingProjection_mul {σ : CMat ι} (hσ : σ.IsHermitian)
    (k l : SpectralLabels hσ) :
    spectralPinchingProjection hσ k * spectralPinchingProjection hσ l =
      if k = l then spectralPinchingProjection hσ k else 0 := by
  classical
  exact unitaryPartitionProjection_mul _ _ k l

theorem spectralBlockCount_pos [Nonempty ι] {σ : CMat ι} (hσ : σ.IsHermitian) :
    0 < spectralBlockCount hσ := by
  have : Nonempty (SpectralLabels hσ) := ⟨spectralLabel hσ (Classical.choice inferInstance)⟩
  exact Fintype.card_pos

theorem spectralPinchingProjection_mul_left {σ : CMat ι} (hσ : σ.IsHermitian)
    (k : SpectralLabels hσ) :
    σ * spectralPinchingProjection hσ k =
      ((k : ℝ) : ℂ) • spectralPinchingProjection hσ k := by
  classical
  let φ := Unitary.conjStarAlgAut ℂ (CMat ι) hσ.eigenvectorUnitary
  let E : CMat ι := Matrix.diagonal (fun j => (hσ.eigenvalues j : ℂ))
  let D : CMat ι := diagonalSelector (spectralLabel hσ) k
  have hσrep : σ = φ E := by
    simpa only [RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using hσ.spectral_theorem
  have hPrep : spectralPinchingProjection hσ k = φ D := by rfl
  have he (j : ι) (hj : spectralLabel hσ j = k) : hσ.eigenvalues j = (k : ℝ) :=
    congrArg Subtype.val hj
  have heD : E * D = ((k : ℝ) : ℂ) • D := by
    change Matrix.diagonal (fun j => (hσ.eigenvalues j : ℂ)) *
      Matrix.diagonal (fun j => if spectralLabel hσ j = k then 1 else 0) = _
    change Matrix.diagonal (fun j => (hσ.eigenvalues j : ℂ)) *
      Matrix.diagonal (fun j => if spectralLabel hσ j = k then 1 else 0) =
        ((k : ℝ) : ℂ) •
          Matrix.diagonal (fun j => if spectralLabel hσ j = k then 1 else 0)
    rw [Matrix.diagonal_mul_diagonal]
    ext r s
    by_cases hrs : r = s
    · subst s
      by_cases hr : spectralLabel hσ r = k
      · simp [Matrix.smul_apply, hr, he r hr]
      · simp [Matrix.smul_apply, hr]
    · simp [Matrix.diagonal_apply_ne _ hrs, Matrix.smul_apply]
  calc
    σ * spectralPinchingProjection hσ k = φ E * φ D :=
      congrArg₂ (fun X Y : CMat ι => X * Y) hσrep hPrep
    _ = φ (E * D) := (map_mul φ E D).symm
    _ = φ (((k : ℝ) : ℂ) • D) := congrArg φ heD
    _ = ((k : ℝ) : ℂ) • spectralPinchingProjection hσ k := by
      rw [map_smul, ← hPrep]

theorem spectralPinchingProjection_mul_right {σ : CMat ι} (hσ : σ.IsHermitian)
    (k : SpectralLabels hσ) :
    spectralPinchingProjection hσ k * σ =
      ((k : ℝ) : ℂ) • spectralPinchingProjection hσ k := by
  have h := congrArg Matrix.conjTranspose (spectralPinchingProjection_mul_left hσ k)
  have hs : star (((k : ℝ) : ℂ)) = ((k : ℝ) : ℂ) := by simp
  simpa only [Matrix.conjTranspose_mul, hσ.eq,
    (spectralPinchingProjection_posSemidef hσ k).isHermitian.eq,
    Matrix.conjTranspose_smul, hs] using h

theorem spectralPinchingProjection_commutes {σ : CMat ι} (hσ : σ.IsHermitian)
    (k : SpectralLabels hσ) :
    σ * spectralPinchingProjection hσ k = spectralPinchingProjection hσ k * σ := by
  rw [spectralPinchingProjection_mul_left, spectralPinchingProjection_mul_right]

theorem spectralPinching_commutes {σ : CMat ι} (hσ : σ.IsHermitian) (A : CMat ι) :
    σ * spectralPinching hσ A = spectralPinching hσ A * σ := by
  classical
  simp only [spectralPinching, pinchingSandwich, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  let P := spectralPinchingProjection hσ k
  calc
    σ * (P * A * P) = (σ * P) * A * P := by noncomm_ring
    _ = ((k : ℝ) : ℂ) • (P * A * P) := by
      rw [spectralPinchingProjection_mul_left, Matrix.smul_mul, Matrix.smul_mul]
    _ = (P * A) * (((k : ℝ) : ℂ) • P) := by rw [Matrix.mul_smul]
    _ = (P * A) * (P * σ) := by rw [spectralPinchingProjection_mul_right]
    _ = (P * A * P) * σ := by noncomm_ring

theorem spectralPinching_fixed {σ : CMat ι} (hσ : σ.IsHermitian) :
    spectralPinching hσ σ = σ := by
  classical
  have hterm (k : SpectralLabels hσ) :
      spectralPinchingProjection hσ k * σ * spectralPinchingProjection hσ k =
        σ * spectralPinchingProjection hσ k := by
    rw [← spectralPinchingProjection_commutes, Matrix.mul_assoc,
      spectralPinchingProjection_idempotent]
  simp only [spectralPinching, pinchingSandwich, hterm]
  rw [← Finset.mul_sum, sum_spectralPinchingProjection, Matrix.mul_one]

end SpectralPinchingCommutation

section PinchingTracePair
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem tracePair_pinchingSandwich (P : κ → CMat ι) (A B : CMat ι) :
    tracePair B (pinchingSandwich P A) = tracePair (pinchingSandwich P B) A := by
  have ht (k : κ) : Matrix.trace (B * (P k * A * P k)) =
      Matrix.trace ((P k * B * P k) * A) := by
    calc
      Matrix.trace (B * (P k * A * P k)) = Matrix.trace ((B * P k * A) * P k) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace (P k * (B * P k * A)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((P k * B * P k) * A) := by
        congr 1
        noncomm_ring
  simp only [tracePair, pinchingSandwich, Finset.mul_sum, Finset.sum_mul,
    Matrix.trace_sum, ht]

theorem tracePair_spectralPinching {σ : CMat ι} (hσ : σ.IsHermitian) (A : CMat ι) :
    tracePair σ (spectralPinching hσ A) = tracePair σ A := by
  rw [spectralPinching, tracePair_pinchingSandwich]
  change tracePair (spectralPinching hσ σ) A = _
  rw [spectralPinching_fixed]

end PinchingTracePair

section CompressedProjectionPOVM
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def compressionOutcome (P : κ → CMat ι) (U : Matrix.unitaryGroup ι ℂ)
    (z : κ × ι) : CMat ι :=
  P z.1 * unitaryPartitionProjection U id z.2 * P z.1

theorem compressionOutcome_posSemidef (P : κ → CMat ι)
    (U : Matrix.unitaryGroup ι ℂ) (hP : ∀ k, (P k).IsHermitian) (z : κ × ι) :
    (compressionOutcome P U z).PosSemidef := by
  simpa only [compressionOutcome, (hP z.1).eq] using
    (unitaryPartitionProjection_posSemidef U id z.2).mul_mul_conjTranspose_same (P z.1)

theorem sum_compressionOutcome (P : κ → CMat ι) (U : Matrix.unitaryGroup ι ℂ)
    (hsum : ∑ k, P k = 1) (hidem : ∀ k, P k * P k = P k) :
    ∑ z, compressionOutcome P U z = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [compressionOutcome]
  calc
    (∑ k, ∑ j, P k * unitaryPartitionProjection U id j * P k) =
        ∑ k, P k * (∑ j, unitaryPartitionProjection U id j) * P k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = ∑ k, P k := by
      simp only [sum_unitaryPartitionProjection, Matrix.mul_one, hidem]
    _ = 1 := hsum

def compressedProjectionPOVM (P : κ → CMat ι) (U : Matrix.unitaryGroup ι ℂ)
    (hP : ∀ k, (P k).IsHermitian) (hsum : ∑ k, P k = 1)
    (hidem : ∀ k, P k * P k = P k) : FinitePOVM ι (Fintype.card (κ × ι)) where
  outcome := fun i => compressionOutcome P U ((Fintype.equivFin (κ × ι)).symm i)
  positive := fun i => compressionOutcome_posSemidef P U hP _
  sum_outcome := by
    calc
      (∑ i, compressionOutcome P U ((Fintype.equivFin (κ × ι)).symm i)) =
          ∑ z, compressionOutcome P U z :=
        (Fintype.equivFin (κ × ι)).symm.sum_comp _
      _ = 1 := sum_compressionOutcome P U hsum hidem

end CompressedProjectionPOVM

section PartitionCompression
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem projection_mul_pinchingSandwich (P : κ → CMat ι)
    (hmul : ∀ k l, P k * P l = if k = l then P k else 0)
    (A : CMat ι) (l : κ) :
    P l * pinchingSandwich P A = P l * A * P l := by
  calc
    _ = ∑ k, (P l * P k) * A * P k := by
      rw [pinchingSandwich, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      noncomm_ring
    _ = ∑ k, if l = k then P l * A * P l else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hlk : l = k
      · subst k
        simp [hmul]
      · simp [hmul, hlk]
    _ = _ := by simp

theorem pinchingSandwich_mul_projection (P : κ → CMat ι)
    (hmul : ∀ k l, P k * P l = if k = l then P k else 0)
    (A : CMat ι) (l : κ) :
    pinchingSandwich P A * P l = P l * A * P l := by
  calc
    _ = ∑ k, P k * A * (P k * P l) := by
      rw [pinchingSandwich, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      noncomm_ring
    _ = ∑ k, if k = l then P l * A * P l else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hkl : k = l
      · subst k
        simp [hmul]
      · simp [hmul, hkl]
    _ = _ := by simp

theorem pinchingSandwich_commutes_projection (P : κ → CMat ι)
    (hmul : ∀ k l, P k * P l = if k = l then P k else 0)
    (A : CMat ι) (l : κ) :
    pinchingSandwich P A * P l = P l * pinchingSandwich P A := by
  rw [pinchingSandwich_mul_projection P hmul,
    projection_mul_pinchingSandwich P hmul]

theorem pinchingSandwich_compression_fixed (P : κ → CMat ι)
    (hmul : ∀ k l, P k * P l = if k = l then P k else 0)
    (E : CMat ι) (l : κ) :
    pinchingSandwich P (P l * E * P l) = P l * E * P l := by
  unfold pinchingSandwich
  calc
    _ = ∑ k, (P k * P l) * E * (P l * P k) := by
      apply Finset.sum_congr rfl
      intro k _
      noncomm_ring
    _ = ∑ k, if k = l then P l * E * P l else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hkl : k = l
      · subst k
        simp [hmul]
      · simp [hmul, hkl]
    _ = _ := by simp

theorem tracePair_compressionOutcome_eq_pinched (P : κ → CMat ι)
    (hmul : ∀ k l, P k * P l = if k = l then P k else 0)
    (U : Matrix.unitaryGroup ι ℂ) (A : CMat ι) (z : κ × ι) :
    tracePair A (compressionOutcome P U z) =
      tracePair (pinchingSandwich P A) (compressionOutcome P U z) := by
  have hf : pinchingSandwich P (compressionOutcome P U z) =
      compressionOutcome P U z :=
    pinchingSandwich_compression_fixed P hmul _ z.1
  calc
    _ = tracePair A (pinchingSandwich P (compressionOutcome P U z)) := by rw [hf]
    _ = _ := tracePair_pinchingSandwich P _ A

theorem compressedProjectionPOVM_mass (P : κ → CMat ι)
    (U : Matrix.unitaryGroup ι ℂ) (hP : ∀ k, (P k).IsHermitian)
    (hsum : ∑ k, P k = 1) (hidem : ∀ k, P k * P k = P k)
    (A : CMat ι) (z : κ × ι) :
    measurementMass (compressedProjectionPOVM P U hP hsum hidem) A
      ((Fintype.equivFin (κ × ι)) z) = tracePair A (compressionOutcome P U z) := by
  simp [measurementMass, compressedProjectionPOVM]

end PartitionCompression

section SpectralCompressionMass
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unitary_partition_diagonal_sum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : Matrix.unitaryGroup ι ℂ) (label : ι → κ) (b : κ → ℝ) :
    (U : CMat ι) * Matrix.diagonal (fun j => (b (label j) : ℂ)) * (U : CMat ι)ᴴ =
      ∑ k, (b k : ℂ) • unitaryPartitionProjection U label k := by
  have hd : Matrix.diagonal (fun j => (b (label j) : ℂ)) =
      ∑ k, (b k : ℂ) • diagonalSelector label k := by
    ext r s
    by_cases hrs : r = s
    · subst s
      simp [diagonalSelector, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.diagonal_apply, smul_eq_mul]
    · simp [diagonalSelector, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.diagonal_apply, smul_eq_mul, hrs]
  rw [hd, Finset.mul_sum, Finset.sum_mul]
  simp only [unitaryPartitionProjection, Matrix.mul_smul, Matrix.smul_mul]

theorem matrixRpow_eq_sum_singleton (A : CMat ι) (hA : A.IsHermitian) (t : ℝ) :
    matrixRpow A t = ∑ j, (Real.rpow (hA.eigenvalues j) t : ℂ) •
      unitaryPartitionProjection hA.eigenvectorUnitary id j := by
  rw [matrixRpow, Spectral.cfc_eq_conjugate _ hA]
  change (hA.eigenvectorUnitary : CMat ι) *
      Matrix.diagonal (fun j => (Real.rpow (hA.eigenvalues j) t : ℂ)) *
        (hA.eigenvectorUnitary : CMat ι)ᴴ = _
  exact unitary_partition_diagonal_sum hA.eigenvectorUnitary (id : ι → ι)
    (fun j => Real.rpow (hA.eigenvalues j) t)

theorem matrixRpow_eq_sum_spectralPinchingProjection {σ : CMat ι}
    (hσ : σ.IsHermitian) (t : ℝ) :
    matrixRpow σ t = ∑ k : SpectralLabels hσ,
      (Real.rpow (k : ℝ) t : ℂ) • spectralPinchingProjection hσ k := by
  classical
  rw [matrixRpow, Spectral.cfc_eq_conjugate _ hσ]
  change (hσ.eigenvectorUnitary : CMat ι) *
      Matrix.diagonal (fun j => (Real.rpow (hσ.eigenvalues j) t : ℂ)) *
        (hσ.eigenvectorUnitary : CMat ι)ᴴ =
    ∑ k : SpectralLabels hσ, (Real.rpow (k : ℝ) t : ℂ) •
      unitaryPartitionProjection hσ.eigenvectorUnitary (spectralLabel hσ) k
  exact unitary_partition_diagonal_sum hσ.eigenvectorUnitary (spectralLabel hσ)
    (fun k : SpectralLabels hσ => Real.rpow (k : ℝ) t)

theorem singletonEigenProjection_mul_left {A : CMat ι} (hA : A.IsHermitian) (j : ι) :
    A * unitaryPartitionProjection hA.eigenvectorUnitary id j =
      (hA.eigenvalues j : ℂ) • unitaryPartitionProjection hA.eigenvectorUnitary id j := by
  let φ := Unitary.conjStarAlgAut ℂ (CMat ι) hA.eigenvectorUnitary
  let E : CMat ι := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  let D : CMat ι := diagonalSelector id j
  have hArep : A = φ E := by
    simpa only [RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using hA.spectral_theorem
  have hPrep : unitaryPartitionProjection hA.eigenvectorUnitary id j = φ D := rfl
  have heD : E * D = (hA.eigenvalues j : ℂ) • D := by
    change Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
      Matrix.diagonal (fun i => if i = j then 1 else 0) =
        (hA.eigenvalues j : ℂ) • Matrix.diagonal (fun i => if i = j then 1 else 0)
    rw [Matrix.diagonal_mul_diagonal]
    ext r s
    by_cases hrs : r = s
    · subst s
      by_cases hrj : r = j
      · subst r
        simp [Matrix.smul_apply]
      · simp [Matrix.smul_apply, hrj]
    · simp [Matrix.diagonal_apply_ne _ hrs, Matrix.smul_apply]
  calc
    _ = φ E * φ D := congrArg₂ (fun X Y : CMat ι => X * Y) hArep hPrep
    _ = φ (E * D) := (map_mul φ E D).symm
    _ = φ ((hA.eigenvalues j : ℂ) • D) := congrArg φ heD
    _ = _ := by rw [map_smul, ← hPrep]

theorem singletonEigenProjection_mul_right {A : CMat ι} (hA : A.IsHermitian) (j : ι) :
    unitaryPartitionProjection hA.eigenvectorUnitary id j * A =
      (hA.eigenvalues j : ℂ) • unitaryPartitionProjection hA.eigenvectorUnitary id j := by
  have h := congrArg Matrix.conjTranspose (singletonEigenProjection_mul_left hA j)
  have hs : star (hA.eigenvalues j : ℂ) = (hA.eigenvalues j : ℂ) := by simp
  simpa only [Matrix.conjTranspose_mul, hA.eq,
    (unitaryPartitionProjection_posSemidef hA.eigenvectorUnitary id j).isHermitian.eq,
    Matrix.conjTranspose_smul, hs] using h

theorem tracePair_compression_cyclic (A P E : CMat ι) :
    tracePair A (P * E * P) = tracePair E (P * A * P) := by
  unfold tracePair
  apply congrArg Complex.re
  calc
    Matrix.trace (A * (P * E * P)) = Matrix.trace ((A * P * E) * P) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (P * (A * P * E)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((P * A * P) * E) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (E * (P * A * P)) := Matrix.trace_mul_comm _ _

theorem compressionOutcome_null_mass {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P : κ → CMat ι)
    (hmul : ∀ k l, P k * P l = if k = l then P k else 0)
    (ρ : CMat ι) (hA : (pinchingSandwich P ρ).IsHermitian) (z : κ × ι) :
    tracePair ρ (compressionOutcome P hA.eigenvectorUnitary z) =
      hA.eigenvalues z.2 *
        tracePair (unitaryPartitionProjection hA.eigenvectorUnitary id z.2) (P z.1) := by
  rw [tracePair_compressionOutcome_eq_pinched P hmul]
  let B := pinchingSandwich P ρ
  let E := unitaryPartitionProjection hA.eigenvectorUnitary id z.2
  have hPP : P z.1 * B * P z.1 = B * P z.1 := by
    calc
      _ = (B * P z.1) * P z.1 := by
        rw [← pinchingSandwich_commutes_projection P hmul ρ z.1]
      _ = B * (P z.1 * P z.1) := Matrix.mul_assoc _ _ _
      _ = B * P z.1 := by simp [hmul]
  change tracePair B (P z.1 * E * P z.1) = _
  calc
    _ = tracePair E (P z.1 * B * P z.1) := tracePair_compression_cyclic _ _ _
    _ = tracePair E (B * P z.1) := congrArg (tracePair E) hPP
    _ = tracePair (E * B) (P z.1) := by simp only [tracePair, Matrix.mul_assoc]
    _ = tracePair ((hA.eigenvalues z.2 : ℂ) • E) (P z.1) := by
      rw [singletonEigenProjection_mul_right hA]
    _ = _ := tracePair_smul_left _ _ _

theorem compressionOutcome_alternative_mass {σ : CMat ι} (hσ : σ.IsHermitian)
    (U : Matrix.unitaryGroup ι ℂ) (z : SpectralLabels hσ × ι) :
    tracePair σ (compressionOutcome (spectralPinchingProjection hσ) U z) =
      (z.1 : ℝ) *
        tracePair (unitaryPartitionProjection U id z.2) (spectralPinchingProjection hσ z.1) := by
  classical
  rw [compressionOutcome, tracePair_compression_cyclic]
  have hPP : spectralPinchingProjection hσ z.1 * σ * spectralPinchingProjection hσ z.1 =
      ((z.1 : ℝ) : ℂ) • spectralPinchingProjection hσ z.1 := by
    rw [spectralPinchingProjection_mul_right, Matrix.smul_mul,
      spectralPinchingProjection_idempotent]
  rw [hPP, tracePair_comm, tracePair_smul_left]
  exact congrArg (fun x : ℝ => (z.1 : ℝ) * x)
    (tracePair_comm (spectralPinchingProjection hσ z.1)
      (unitaryPartitionProjection U id z.2))

end SpectralCompressionMass

section SpectralCompressedWitness
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def compressedSpectralPOVM {ρ σ : CMat ι} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    FinitePOVM ι (Fintype.card (SpectralLabels hσ.1 × ι)) := by
  classical
  exact compressedProjectionPOVM (spectralPinchingProjection hσ.1)
    (spectralPinching_posSemidef hσ.1 hρ).1.eigenvectorUnitary
    (fun k => (spectralPinchingProjection_posSemidef hσ.1 k).1)
    (sum_spectralPinchingProjection hσ.1) (spectralPinchingProjection_idempotent hσ.1)

def compressedSpectralOverlap {ρ σ : CMat ι} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (z : SpectralLabels hσ.1 × ι) : ℝ :=
  tracePair
    (unitaryPartitionProjection (spectralPinching_posSemidef hσ.1 hρ).1.eigenvectorUnitary id z.2)
    (spectralPinchingProjection hσ.1 z.1)

theorem compressedSpectralOverlap_nonneg {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (z : SpectralLabels hσ.1 × ι) :
    0 ≤ compressedSpectralOverlap hρ hσ z :=
  tracePair_nonneg (unitaryPartitionProjection_posSemidef _ _ _)
    (spectralPinchingProjection_posSemidef hσ.1 z.1)

theorem spectralLabel_value_nonneg {σ : CMat ι} (hσ : σ.PosSemidef)
    (k : SpectralLabels hσ.1) : 0 ≤ (k : ℝ) := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp k.property
  rw [← hj]
  exact hσ.eigenvalues_nonneg j

theorem compressedSpectralPOVM_null_mass {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (z : SpectralLabels hσ.1 × ι) :
    measurementMass (compressedSpectralPOVM hρ hσ) ρ
        ((Fintype.equivFin (SpectralLabels hσ.1 × ι)) z) =
      (spectralPinching_posSemidef hσ.1 hρ).1.eigenvalues z.2 *
        compressedSpectralOverlap hρ hσ z := by
  classical
  rw [compressedSpectralPOVM, compressedProjectionPOVM_mass]
  exact compressionOutcome_null_mass (spectralPinchingProjection hσ.1)
    (spectralPinchingProjection_mul hσ.1) ρ (spectralPinching_posSemidef hσ.1 hρ).1 z

theorem compressedSpectralPOVM_alternative_mass {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (z : SpectralLabels hσ.1 × ι) :
    measurementMass (compressedSpectralPOVM hρ hσ) σ
        ((Fintype.equivFin (SpectralLabels hσ.1 × ι)) z) =
      (z.1 : ℝ) * compressedSpectralOverlap hρ hσ z := by
  classical
  rw [compressedSpectralPOVM, compressedProjectionPOVM_mass]
  exact compressionOutcome_alternative_mass hσ.1 _ z

theorem tracePair_smul_right (c : ℝ) (A Q : CMat ι) :
    tracePair A ((c : ℂ) • Q) = c * tracePair A Q := by
  rw [tracePair_comm, tracePair_smul_left]
  exact congrArg (fun x : ℝ => c * x) (tracePair_comm Q A)

theorem scaled_renyi_term {p q a α : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a)
    (hα : 0 < α) (hα1 : α < 1) :
    Real.rpow (p * a) α * Real.rpow (q * a) (1 - α) =
      Real.rpow p α * Real.rpow q (1 - α) * a := by
  simp only [Real.rpow_eq_pow]
  by_cases ha0 : a = 0
  · simp [ha0, Real.zero_rpow hα.ne', Real.zero_rpow (sub_pos.mpr hα1).ne']
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rw [Real.mul_rpow hp ha, Real.mul_rpow hq ha]
    calc
      p ^ α * a ^ α * (q ^ (1 - α) * a ^ (1 - α)) =
          p ^ α * q ^ (1 - α) * (a ^ α * a ^ (1 - α)) := by ring
      _ = p ^ α * q ^ (1 - α) * a := by
        rw [← Real.rpow_add hap α (1 - α)]
        simp

theorem petzTrace_spectralPinching_eq_sum {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (α : ℝ) :
    petzTrace (spectralPinching hσ.1 ρ) σ α =
      ∑ z : SpectralLabels hσ.1 × ι,
        Real.rpow ((spectralPinching_posSemidef hσ.1 hρ).1.eigenvalues z.2) α *
          Real.rpow (z.1 : ℝ) (1 - α) * compressedSpectralOverlap hρ hσ z := by
  classical
  unfold petzTrace
  rw [matrixRpow_eq_sum_singleton _ (spectralPinching_posSemidef hσ.1 hρ).1,
    matrixRpow_eq_sum_spectralPinchingProjection hσ.1]
  simp only [tracePair_sum_left, tracePair_smul_left, tracePair_sum_right,
    tracePair_smul_right, Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [compressedSpectralOverlap]
  ring

theorem classicalRenyiTrace_compressedSpectralPOVM {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    classicalRenyiTrace (measurementMass (compressedSpectralPOVM hρ hσ) ρ)
        (measurementMass (compressedSpectralPOVM hρ hσ) σ) α =
      petzTrace (spectralPinching hσ.1 ρ) σ α := by
  classical
  rw [petzTrace_spectralPinching_eq_sum hρ hσ α]
  unfold classicalRenyiTrace
  calc
    _ = ∑ z : SpectralLabels hσ.1 × ι,
        Real.rpow (measurementMass (compressedSpectralPOVM hρ hσ) ρ
          ((Fintype.equivFin (SpectralLabels hσ.1 × ι)) z)) α *
        Real.rpow (measurementMass (compressedSpectralPOVM hρ hσ) σ
          ((Fintype.equivFin (SpectralLabels hσ.1 × ι)) z)) (1 - α) :=
      ((Fintype.equivFin (SpectralLabels hσ.1 × ι)).sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      rw [compressedSpectralPOVM_null_mass, compressedSpectralPOVM_alternative_mass]
      exact scaled_renyi_term ((spectralPinching_posSemidef hσ.1 hρ).eigenvalues_nonneg z.2)
        (spectralLabel_value_nonneg hσ z.1) (compressedSpectralOverlap_nonneg hρ hσ z) hα hα1

theorem classicalRenyiDivergence_compressedSpectralPOVM {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    classicalRenyiDivergence (measurementMass (compressedSpectralPOVM hρ hσ) ρ)
        (measurementMass (compressedSpectralPOVM hρ hσ) σ) α =
      petzDivergence (spectralPinching hσ.1 ρ) σ α := by
  simp only [classicalRenyiDivergence, petzDivergence, ne_of_lt hα1,
    if_false, not_lt_of_ge hα1.le, false_and,
    classicalRenyiTrace_compressedSpectralPOVM hρ hσ hα hα1]

theorem petzDivergence_spectralPinching_le_measured {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    petzDivergence (spectralPinching hσ.1 ρ) σ α ≤ measuredDivergence ρ σ α := by
  rw [← classicalRenyiDivergence_compressedSpectralPOVM hρ hσ hα hα1]
  exact le_sSup ⟨_, compressedSpectralPOVM hρ hσ, rfl⟩

end SpectralCompressedWitness

section MeasuredDomination
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem renyi_mass_ge_scaled_mass {p q a α : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 < a) (hdom : p ≤ a * q)
    (hα : 0 < α) (hα1 : α < 1) :
    p / Real.rpow a (1 - α) ≤ Real.rpow p α * Real.rpow q (1 - α) := by
  have hβ : 0 < 1 - α := sub_pos.mpr hα1
  have hpow : p ^ (1 - α) ≤ a ^ (1 - α) * q ^ (1 - α) := by
    simpa only [Real.mul_rpow ha.le hq] using
      Real.rpow_le_rpow hp hdom hβ.le
  have hpowers : p = p ^ α * p ^ (1 - α) := by
    rw [← Real.rpow_add' hp (by norm_num : α + (1 - α) ≠ 0)]
    simp
  apply (div_le_iff₀ (Real.rpow_pos_of_pos ha (1 - α))).mpr
  simp only [Real.rpow_eq_pow]
  calc
    p = p ^ α * p ^ (1 - α) := hpowers
    _ ≤ p ^ α * (a ^ (1 - α) * q ^ (1 - α)) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hp α)
    _ = _ := by ring

theorem measurementRenyiTrace_ge_of_domination {L : ℕ} (M : FinitePOVM ι L)
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {a α : ℝ} (ha : 0 < a) (hdom : LoewnerLE ρ ((a : ℂ) • σ))
    (hα : 0 < α) (hα1 : α < 1) :
    Real.rpow a (α - 1) ≤
      classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α := by
  have he : Real.rpow a (α - 1) = 1 / Real.rpow a (1 - α) := by
    simp only [Real.rpow_eq_pow]
    rw [show α - 1 = -(1 - α) by ring, Real.rpow_neg ha.le, one_div]
  rw [he]
  have hs : ∑ i, measurementMass M ρ i / Real.rpow a (1 - α) =
      1 / Real.rpow a (1 - α) := by
    rw [← Finset.sum_div, measurementMass_sum M hρ]
  rw [← hs, classicalRenyiTrace]
  apply Finset.sum_le_sum
  intro i _
  exact renyi_mass_ge_scaled_mass (measurementMass_nonneg M hρ.1 i)
    (measurementMass_nonneg M hσ i) ha (measurementMass_domination M hdom i) hα hα1

theorem classicalRenyiDivergence_le_log_of_domination {L : ℕ} (M : FinitePOVM ι L)
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {a α : ℝ} (ha : 0 < a) (hdom : LoewnerLE ρ ((a : ℂ) • σ))
    (hα : 0 < α) (hα1 : α < 1) :
    classicalRenyiDivergence (measurementMass M ρ) (measurementMass M σ) α ≤
      (logTwo a : EReal) := by
  have ht := measurementRenyiTrace_ge_of_domination M hρ hσ ha hdom hα hα1
  have hpos : 0 < classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α :=
    (Real.rpow_pos_of_pos ha (α - 1)).trans_le ht
  have hl := logTwo_mono_pos (Real.rpow_pos_of_pos ha (α - 1)) ht
  rw [logTwo_rpow_pos ha] at hl
  have hquot : logTwo (classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α) /
      (α - 1) ≤ logTwo a :=
    (div_le_iff_of_neg (sub_neg.mpr hα1)).mpr (by simpa only [mul_comm] using hl)
  have hd : classicalRenyiDivergence (measurementMass M ρ) (measurementMass M σ) α =
      ((logTwo (classicalRenyiTrace (measurementMass M ρ) (measurementMass M σ) α) /
        (α - 1) : ℝ) : EReal) := by
    simp only [classicalRenyiDivergence, ne_of_lt hα1, if_false,
      not_lt_of_ge hα1.le, false_and, hpos.ne']
    rw [← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_div]
  rw [hd]
  exact EReal.coe_le_coe hquot

theorem measuredDivergence_le_log_of_domination {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {a α : ℝ}
    (ha : 0 < a) (hdom : LoewnerLE ρ ((a : ℂ) • σ))
    (hα : 0 < α) (hα1 : α < 1) :
    measuredDivergence ρ σ α ≤ (logTwo a : EReal) := by
  unfold measuredDivergence
  apply sSup_le
  rintro z ⟨L, M, rfl⟩
  exact classicalRenyiDivergence_le_log_of_domination M hρ hσ ha hdom hα hα1

theorem measuredDivergence_finite_of_domination {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {a α : ℝ}
    (ha : 0 < a) (hdom : LoewnerLE ρ ((a : ℂ) • σ))
    (hα : 0 < α) (hα1 : α < 1) :
    measuredDivergence ρ σ α ≠ ⊤ ∧ measuredDivergence ρ σ α ≠ ⊥ := by
  have hu := measuredDivergence_le_log_of_domination hρ hσ ha hdom hα hα1
  have hl := measuredDivergence_ge_neg_log_trace_of_domination hρ ha hdom α
  constructor
  · intro htop
    have he : (logTwo a : EReal) = ⊤ := le_antisymm le_top (by simpa only [htop] using hu)
    exact EReal.coe_ne_top _ he
  · intro hbot
    have he : (-logTwo (Matrix.trace σ).re : EReal) = ⊥ :=
      le_antisymm (by simpa only [hbot] using hl) bot_le
    exact EReal.coe_ne_bot _ he

end MeasuredDomination

section MatrixSpectralSandwich
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem cfc_mul_of_eigenmatrix {A B : CMat ι} (hA : A.IsHermitian)
    {a : ℝ} (hAB : A * B = (a : ℂ) • B) (f : ℝ → ℝ) :
    cfc f A * B = (f a : ℂ) • B := by
  let U : CMat ι := hA.eigenvectorUnitary
  let D : CMat ι := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  let V : CMat ι := Uᴴ * B
  have hu : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hdiag : Uᴴ * A * U = D := by
    simpa only [Unitary.conjStarAlgAut_star_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, RCLike.ofReal_eq_complex_ofReal,
      Function.comp_def] using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hleft : D * Uᴴ = Uᴴ * A := by
    rw [← hdiag]
    calc
      (Uᴴ * A * U) * Uᴴ = (Uᴴ * A) * (U * Uᴴ) := by noncomm_ring
      _ = Uᴴ * A := by rw [hu, Matrix.mul_one]
  have hDV : D * V = (a : ℂ) • V := by
    change D * (Uᴴ * B) = (a : ℂ) • (Uᴴ * B)
    rw [← Matrix.mul_assoc, hleft, Matrix.mul_assoc, hAB, Matrix.mul_smul]
  have hfV : Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * V =
      (f a : ℂ) • V := by
    ext i j
    have he : (hA.eigenvalues i : ℂ) * V i j = (a : ℂ) * V i j := by
      simpa only [D, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul] using
        congrArg (fun X : CMat ι => X i j) hDV
    simp only [Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    by_cases hi : hA.eigenvalues i = a
    · rw [hi]
    · have hiC : (hA.eigenvalues i : ℂ) ≠ (a : ℂ) := by exact_mod_cast hi
      have hV0 : V i j = 0 := (mul_eq_mul_right_iff.mp he).resolve_left hiC
      rw [hV0, mul_zero, mul_zero]
  rw [Spectral.cfc_eq_conjugate f hA]
  change (U * Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * Uᴴ) * B = _
  calc
    _ = U * (Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) * V) := by
      dsimp only [V]
      noncomm_ring
    _ = U * ((f a : ℂ) • V) := congrArg (fun X : CMat ι => U * X) hfV
    _ = (f a : ℂ) • B := by
      rw [Matrix.mul_smul]
      congr 1
      change U * (Uᴴ * B) = B
      rw [← Matrix.mul_assoc, hu, Matrix.one_mul]

theorem cfc_mul_spectralPinchingProjection {σ : CMat ι} (hσ : σ.IsHermitian)
    (f : ℝ → ℝ) (k : SpectralLabels hσ) :
    cfc f σ * spectralPinchingProjection hσ k =
      (f (k : ℝ) : ℂ) • spectralPinchingProjection hσ k :=
  cfc_mul_of_eigenmatrix hσ (spectralPinchingProjection_mul_left hσ k) f

theorem matrixRpow_commutes_spectralPinchingProjection {σ : CMat ι}
    (hσ : σ.IsHermitian) (t : ℝ) (k : SpectralLabels hσ) :
    Commute (matrixRpow σ t) (spectralPinchingProjection hσ k) :=
  (show Commute σ (spectralPinchingProjection hσ k) from
    spectralPinchingProjection_commutes hσ k).cfc_real (fun x => Real.rpow x t)

theorem sandwichedTrace_spectralPinching_le [Nonempty ι] {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    sandwichedTrace (spectralPinching hσ.1 ρ) σ α ≤
      Real.rpow (spectralBlockCount hσ.1 : ℝ) (1 - α) * sandwichedTrace ρ σ α := by
  classical
  letI : Nonempty (SpectralLabels hσ.1) :=
    ⟨spectralLabel hσ.1 (Classical.choice inferInstance)⟩
  exact sandwichedTrace_pinching_le (spectralPinchingProjection hσ.1)
    (fun k => (spectralPinchingProjection_posSemidef hσ.1 k).1.eq)
    (spectralPinchingProjection_mul hσ.1) (sum_spectralPinchingProjection hσ.1)
    hρ hα hα1 (matrixRpow_commutes_spectralPinchingProjection hσ.1 _)

theorem cfc_eq_sum_of_eigenmatrix_resolution {κ : Type*} [Fintype κ]
    {A : CMat ι} (hA : A.IsHermitian) (P : κ → CMat ι) (a : κ → ℝ)
    (hsum : ∑ k, P k = 1) (hAP : ∀ k, A * P k = (a k : ℂ) • P k)
    (f : ℝ → ℝ) : cfc f A = ∑ k, (f (a k) : ℂ) • P k := by
  calc
    cfc f A = cfc f A * (∑ k, P k) := by rw [hsum, Matrix.mul_one]
    _ = ∑ k, cfc f A * P k := Finset.mul_sum _ _ _
    _ = _ := Finset.sum_congr rfl fun k _ => cfc_mul_of_eigenmatrix hA (hAP k) f

theorem spectralPinchingProjection_eq_cfc {σ : CMat ι} (hσ : σ.IsHermitian)
    (k : SpectralLabels hσ) :
    spectralPinchingProjection hσ k =
      cfc (fun x : ℝ => if x = (k : ℝ) then 1 else 0) σ := by
  classical
  rw [Spectral.cfc_eq_conjugate _ hσ]
  change (hσ.eigenvectorUnitary : CMat ι) *
      Matrix.diagonal (fun i => if spectralLabel hσ i = k then 1 else 0) *
        (hσ.eigenvectorUnitary : CMat ι)ᴴ =
    (hσ.eigenvectorUnitary : CMat ι) *
      Matrix.diagonal (fun i => ((if hσ.eigenvalues i = (k : ℝ) then 1 else 0 : ℝ) : ℂ)) *
        (hσ.eigenvectorUnitary : CMat ι)ᴴ
  apply congrArg (fun D : CMat ι => (hσ.eigenvectorUnitary : CMat ι) * D *
    (hσ.eigenvectorUnitary : CMat ι)ᴴ)
  apply congrArg Matrix.diagonal
  funext i
  by_cases hi : spectralLabel hσ i = k
  · have hi' : hσ.eigenvalues i = (k : ℝ) := congrArg Subtype.val hi
    simp [hi, hi']
  · have hi' : hσ.eigenvalues i ≠ (k : ℝ) := fun h => hi (Subtype.ext h)
    simp [hi, hi']

def jointSpectralProjection {A σ : CMat ι} (hA : A.IsHermitian)
    (hσ : σ.IsHermitian) (z : SpectralLabels hσ × SpectralLabels hA) : CMat ι :=
  spectralPinchingProjection hσ z.1 * spectralPinchingProjection hA z.2

theorem sum_jointSpectralProjection {A σ : CMat ι} (hA : A.IsHermitian)
    (hσ : σ.IsHermitian) : ∑ z, jointSpectralProjection hA hσ z = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [jointSpectralProjection, ← Finset.mul_sum, sum_spectralPinchingProjection,
    Matrix.mul_one]

theorem jointSpectralProjection_null_action {A σ : CMat ι} (hA : A.IsHermitian)
    (hσ : σ.IsHermitian) (hcomm : Commute A σ)
    (z : SpectralLabels hσ × SpectralLabels hA) :
    A * jointSpectralProjection hA hσ z =
      ((z.2 : ℝ) : ℂ) • jointSpectralProjection hA hσ z := by
  have hc := hcomm.symm.cfc_real (fun x : ℝ => if x = (z.1 : ℝ) then 1 else 0)
  rw [← spectralPinchingProjection_eq_cfc] at hc
  unfold jointSpectralProjection
  rw [← Matrix.mul_assoc, hc.symm.eq, Matrix.mul_assoc,
    spectralPinchingProjection_mul_left hA, Matrix.mul_smul]

theorem jointSpectralProjection_power_action {A σ : CMat ι} (hA : A.IsHermitian)
    (hσ : σ.IsHermitian) (t : ℝ) (z : SpectralLabels hσ × SpectralLabels hA) :
    matrixRpow σ t * jointSpectralProjection hA hσ z =
      (Real.rpow (z.1 : ℝ) t : ℂ) • jointSpectralProjection hA hσ z := by
  unfold jointSpectralProjection matrixRpow
  rw [← Matrix.mul_assoc, cfc_mul_spectralPinchingProjection, Matrix.smul_mul]

theorem petzTrace_eq_joint_spectral_sum {A σ : CMat ι}
    (hA : A.IsHermitian) (hσ : σ.IsHermitian) (hcomm : Commute A σ) (α : ℝ) :
    petzTrace A σ α = ∑ z : SpectralLabels hσ × SpectralLabels hA,
      Real.rpow (z.2 : ℝ) α * Real.rpow (z.1 : ℝ) (1 - α) *
        (Matrix.trace (jointSpectralProjection hA hσ z)).re := by
  classical
  unfold petzTrace
  rw [matrixRpow, cfc_eq_sum_of_eigenmatrix_resolution hA
    (jointSpectralProjection hA hσ) (fun z => (z.2 : ℝ))
    (sum_jointSpectralProjection hA hσ) (jointSpectralProjection_null_action hA hσ hcomm)]
  rw [tracePair_comm]
  simp only [tracePair_sum_right, tracePair_smul_right]
  apply Finset.sum_congr rfl
  intro z _
  have ht : tracePair (matrixRpow σ (1 - α)) (jointSpectralProjection hA hσ z) =
      Real.rpow (z.1 : ℝ) (1 - α) *
        (Matrix.trace (jointSpectralProjection hA hσ z)).re := by
    rw [tracePair, jointSpectralProjection_power_action, Matrix.trace_smul]
    simp
  rw [ht]
  ring

theorem sandwich_mul_of_eigenmatrix (S A B : CMat ι) {s a : ℝ}
    (hSB : S * B = (s : ℂ) • B) (hAB : A * B = (a : ℂ) • B) :
    (S * A * S) * B = ((s ^ 2 * a : ℝ) : ℂ) • B := by
  calc
    _ = S * (A * (S * B)) := by noncomm_ring
    _ = S * (A * ((s : ℂ) • B)) := by rw [hSB]
    _ = ((s ^ 2 * a : ℝ) : ℂ) • B := by
      rw [Matrix.mul_smul, hAB, Matrix.mul_smul, Matrix.mul_smul, hSB,
        smul_smul, smul_smul]
      congr 1
      push_cast
      ring

theorem sandwich_scalar_rpow {p q α : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hα : 0 < α) :
    Real.rpow ((Real.rpow q ((1 - α) / (2 * α))) ^ 2 * p) α =
      Real.rpow p α * Real.rpow q (1 - α) := by
  simp only [Real.rpow_eq_pow]
  let β : ℝ := (1 - α) / (2 * α)
  have hs : (q ^ β) ^ 2 = q ^ (β * 2) := by
    simpa only [Real.rpow_two] using (Real.rpow_mul hq β 2).symm
  change ((q ^ β) ^ 2 * p) ^ α = p ^ α * q ^ (1 - α)
  rw [hs, Real.mul_rpow (Real.rpow_nonneg hq _) hp, ← Real.rpow_mul hq]
  have he : β * 2 * α = 1 - α := by
    dsimp [β]
    field_simp [hα.ne']
    <;> ring
  rw [he, mul_comm]

theorem sandwichedTrace_eq_petzTrace_of_commute {A σ : CMat ι}
    (hA : A.PosSemidef) (hσ : σ.PosSemidef) (hcomm : Commute A σ)
    {α : ℝ} (hα : 0 < α) : sandwichedTrace A σ α = petzTrace A σ α := by
  classical
  let β : ℝ := (1 - α) / (2 * α)
  let S := matrixRpow σ β
  let H := S * A * S
  let R := jointSpectralProjection hA.1 hσ.1
  let b : SpectralLabels hσ.1 × SpectralLabels hA.1 → ℝ :=
    fun z => (Real.rpow (z.1 : ℝ) β) ^ 2 * (z.2 : ℝ)
  have hS : S.IsHermitian := cfc_predicate (p := IsSelfAdjoint) _ σ
  have hH : H.PosSemidef := by
    simpa only [H, hS.eq] using hA.mul_mul_conjTranspose_same S
  have hHR (z : SpectralLabels hσ.1 × SpectralLabels hA.1) :
      H * R z = (b z : ℂ) • R z :=
    sandwich_mul_of_eigenmatrix S A (R z)
      (jointSpectralProjection_power_action hA.1 hσ.1 β z)
      (jointSpectralProjection_null_action hA.1 hσ.1 hcomm z)
  have hpow : matrixRpow H α = ∑ z, (Real.rpow (b z) α : ℂ) • R z :=
    cfc_eq_sum_of_eigenmatrix_resolution hH.1 R b
      (sum_jointSpectralProjection hA.1 hσ.1) hHR _
  change (Matrix.trace (matrixRpow H α)).re = petzTrace A σ α
  rw [hpow, petzTrace_eq_joint_spectral_sum hA.1 hσ.1 hcomm,
    Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Matrix.trace_smul]
  have hb : Real.rpow (b z) α = Real.rpow (z.2 : ℝ) α *
      Real.rpow (z.1 : ℝ) (1 - α) :=
    sandwich_scalar_rpow (spectralLabel_value_nonneg hA z.2)
      (spectralLabel_value_nonneg hσ z.1) hα
  simp only [Complex.smul_re, smul_eq_mul, hb, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rfl

theorem sandwichedTrace_spectralPinching_eq_petz {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {α : ℝ} (hα : 0 < α) :
    sandwichedTrace (spectralPinching hσ.1 ρ) σ α =
      petzTrace (spectralPinching hσ.1 ρ) σ α :=
  sandwichedTrace_eq_petzTrace_of_commute (spectralPinching_posSemidef hσ.1 hρ) hσ
    (show Commute (spectralPinching hσ.1 ρ) σ from
      (spectralPinching_commutes hσ.1 ρ).symm) hα

theorem isState_nonempty_index {ρ : CMat ι} (hρ : IsState ρ) : Nonempty ι := by
  classical
  by_contra he
  haveI : IsEmpty ι := not_nonempty_iff.mp he
  have ht : Matrix.trace ρ = 0 := by simp [Matrix.trace]
  have htr := hρ.2
  rw [ht] at htr
  exact zero_ne_one htr

theorem petzTrace_spectralPinching_pos_of_domination {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {a α : ℝ} (ha : 0 < a)
    (hdom : LoewnerLE ρ ((a : ℂ) • σ)) (hα : 0 < α) (hα1 : α < 1) :
    0 < petzTrace (spectralPinching hσ.1 ρ) σ α := by
  have ht := classicalRenyiTrace_pos_of_domination (compressedSpectralPOVM hρ.1 hσ)
    ha hρ hσ hdom (α := α)
  rw [classicalRenyiTrace_compressedSpectralPOVM hρ.1 hσ hα hα1] at ht
  exact ht

theorem sandwichedTrace_spectralPinching_pos_of_domination {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {a α : ℝ} (ha : 0 < a)
    (hdom : LoewnerLE ρ ((a : ℂ) • σ)) (hα : 0 < α) (hα1 : α < 1) :
    0 < sandwichedTrace (spectralPinching hσ.1 ρ) σ α := by
  rw [sandwichedTrace_spectralPinching_eq_petz hρ.1 hσ hα]
  exact petzTrace_spectralPinching_pos_of_domination hρ hσ ha hdom hα hα1

theorem sandwichedTrace_pos_of_domination {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {a α : ℝ} (ha : 0 < a)
    (hdom : LoewnerLE ρ ((a : ℂ) • σ)) (hα : 0 < α) (hα1 : α < 1) :
    0 < sandwichedTrace ρ σ α := by
  letI := isState_nonempty_index hρ
  have hp := sandwichedTrace_spectralPinching_pos_of_domination hρ hσ ha hdom hα hα1
  have hb := sandwichedTrace_spectralPinching_le hρ.1 hσ hα hα1
  have hv : 0 < Real.rpow (spectralBlockCount hσ.1 : ℝ) (1 - α) :=
    Real.rpow_pos_of_pos (by exact_mod_cast spectralBlockCount_pos hσ.1) _
  by_contra hn
  have hz := mul_nonpos_of_nonneg_of_nonpos hv.le (le_of_not_gt hn)
  linarith

theorem sandwichedDivergence_spectralPinching_eq_petz {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    sandwichedDivergence (spectralPinching hσ.1 ρ) σ α =
      petzDivergence (spectralPinching hσ.1 ρ) σ α := by
  simp only [sandwichedDivergence, petzDivergence, ne_of_lt hα1, if_false,
    not_lt_of_ge hα1.le, false_and, sandwichedTrace_spectralPinching_eq_petz hρ hσ hα]

theorem sandwichedDivergence_spectralPinching_le_measured {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    sandwichedDivergence (spectralPinching hσ.1 ρ) σ α ≤ measuredDivergence ρ σ α := by
  rw [sandwichedDivergence_spectralPinching_eq_petz hρ hσ hα hα1]
  exact petzDivergence_spectralPinching_le_measured hρ hσ hα hα1

theorem sandwichedDivergence_sub_log_spectralCount_le_measured {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {a α : ℝ} (ha : 0 < a)
    (hdom : LoewnerLE ρ ((a : ℂ) • σ)) (hα : 0 < α) (hα1 : α < 1) :
    sandwichedDivergence ρ σ α - (logTwo (spectralBlockCount hσ.1 : ℝ) : EReal) ≤
      measuredDivergence ρ σ α := by
  classical
  letI := isState_nonempty_index hρ
  letI : Nonempty (SpectralLabels hσ.1) :=
    ⟨spectralLabel hσ.1 (Classical.choice inferInstance)⟩
  have hb := sandwichedDivergence_pinching_lower (spectralPinchingProjection hσ.1)
    (fun k => (spectralPinchingProjection_posSemidef hσ.1 k).1.eq)
    (spectralPinchingProjection_mul hσ.1) (sum_spectralPinchingProjection hσ.1)
    hρ.1 hα hα1 (matrixRpow_commutes_spectralPinchingProjection hσ.1 _)
    (sandwichedTrace_pos_of_domination hρ hσ ha hdom hα hα1)
    (sandwichedTrace_spectralPinching_pos_of_domination hρ hσ ha hdom hα hα1)
  exact hb.trans (sandwichedDivergence_spectralPinching_le_measured hρ.1 hσ hα hα1)

theorem testingDivergence_lower_of_sandwich_spectralCount {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {a ε α : ℝ}
    (ha : 0 < a) (hdom : LoewnerLE ρ ((a : ℂ) • σ))
    (hε : 0 < ε) (hε1 : ε < 1) (hα : 0 < α) (hα1 : α < 1) :
    sandwichedDivergence ρ σ α - (logTwo (spectralBlockCount hσ.1 : ℝ) : EReal) +
        (((α / (1 - α)) * logTwo ε : ℝ) : EReal) ≤ testingDivergence ε ρ σ := by
  have hl := sandwichedDivergence_sub_log_spectralCount_le_measured
    hρ hσ ha hdom hα hα1
  have hu := measuredDivergence_le_testing_corrected hε hε1 hρ hσ hα hα1 ha hdom
  have h := add_le_add (hl.trans hu)
    (le_refl (((α / (1 - α)) * logTwo ε : ℝ) : EReal))
  rw [← EReal.coe_add, sub_add_cancel] at h
  rw [testingDivergence_eq_of_domination hε.le hε1 ha hρ hdom]
  exact h

end MatrixSpectralSandwich

end QuantumProver.Equipartition.FiniteModel.Testing
