import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Kronecker
open RCLike
open Matrix

namespace QuantumProver.AmplitudeDamping.SecretKey.Phase

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev PhaseWord (ι : Type*) := ι → ZMod 3

def wordCharacter (signature : PhaseWord ι) : AddChar (PhaseWord ι) ℂ where
  toFun z := ZMod.stdAddChar (∑ i, signature i * z i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact AddChar.map_add_eq_mul _ _ _

@[simp] theorem wordCharacter_apply (signature z : PhaseWord ι) :
    wordCharacter signature z = ZMod.stdAddChar (∑ i, signature i * z i) := rfl

@[simp] theorem wordCharacter_single (signature : PhaseWord ι) (i : ι) :
    wordCharacter signature (Pi.single i 1) = ZMod.stdAddChar (signature i) := by
  simp [wordCharacter, Pi.single_apply, mul_ite]

theorem wordCharacter_injective : Function.Injective (wordCharacter (ι := ι)) := by
  classical
  intro a b hab
  funext i
  apply ZMod.injective_stdAddChar
  have h := congrArg (fun χ : AddChar (PhaseWord ι) ℂ => χ (Pi.single i 1)) hab
  simpa only [wordCharacter_single] using h

theorem wordCharacter_orthogonality (a b : PhaseWord ι) :
    (𝔼 z : PhaseWord ι, conj (wordCharacter a z) * wordCharacter b z) =
      if a = b then 1 else 0 := by
  classical
  have h := AddChar.wInner_cWeight_eq_boole (wordCharacter a) (wordCharacter b)
  simpa only [wInner_cWeight_eq_expect, RCLike.inner_apply,
    wordCharacter_injective.eq_iff, mul_comm] using h

theorem wordCharacter_sum_orthogonality (a b : PhaseWord ι) :
    (∑ z : PhaseWord ι, conj (wordCharacter a z) * wordCharacter b z) =
      if a = b then (Fintype.card (PhaseWord ι) : ℂ) else 0 := by
  classical
  have h := wordCharacter_orthogonality a b
  rw [Fintype.expect_eq_sum_div_card] at h
  have hn : (Fintype.card (PhaseWord ι) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h' := (div_eq_iff hn).mp h
  simpa only [ite_mul, one_mul, zero_mul] using h'

theorem phaseVectors_gram {I : Type*} [Fintype I] [DecidableEq I]
    (signature : I → PhaseWord ι) (hinj : Function.Injective signature) :
    (∑ z : PhaseWord ι,
      Matrix.vecMulVec (fun i => wordCharacter (signature i) z)
        (star (fun i => wordCharacter (signature i) z))) =
      (Fintype.card (PhaseWord ι) : ℂ) • (1 : Matrix I I ℂ) := by
  ext i j
  have h := wordCharacter_sum_orthogonality (signature j) (signature i)
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simpa [RCLike.star_def, mul_comm] using h
  · have hsig : signature j ≠ signature i := fun heq => hij (hinj heq).symm
    simpa [hij, hsig, RCLike.star_def, mul_comm] using h

theorem sum_scaled_outer {I J : Type*} [Fintype J] (a : ℂ) (v : J → I → ℂ) :
    (∑ j, Matrix.vecMulVec (fun i => a * v j i) (star (fun i => a * v j i))) =
      (a * star a) • (∑ j, Matrix.vecMulVec (v j) (star (v j))) := by
  ext i k
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply, star_mul,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def phaseNormalization : ℂ :=
  ((Real.sqrt (Fintype.card (PhaseWord ι) : ℝ))⁻¹ : ℝ)

theorem phaseNormalization_identity :
    phaseNormalization (ι := ι) * star (phaseNormalization (ι := ι)) *
      (Fintype.card (PhaseWord ι) : ℂ) = 1 := by
  have hn : 0 < (Fintype.card (PhaseWord ι) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card (PhaseWord ι) : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hn)
  have hr : (Real.sqrt (Fintype.card (PhaseWord ι) : ℝ))⁻¹ *
      (Real.sqrt (Fintype.card (PhaseWord ι) : ℝ))⁻¹ *
        (Fintype.card (PhaseWord ι) : ℝ) = 1 := by
    field_simp [hs]
    nlinarith [Real.mul_self_sqrt hn.le]
  simpa [phaseNormalization] using congrArg (fun x : ℝ => (x : ℂ)) hr

theorem normalizedPhaseVectors_complete {I : Type*} [Fintype I] [DecidableEq I]
    (signature : I → PhaseWord ι) (hinj : Function.Injective signature) :
    (∑ z : PhaseWord ι,
      Matrix.vecMulVec (fun i => phaseNormalization (ι := ι) * wordCharacter (signature i) z)
        (star (fun i => phaseNormalization (ι := ι) * wordCharacter (signature i) z))) =
      (1 : Matrix I I ℂ) := by
  rw [sum_scaled_outer, phaseVectors_gram signature hinj, smul_smul,
    phaseNormalization_identity, one_smul]

def averagedPhaseGram {κ : Type*} (signature : κ → PhaseWord ι) : Matrix κ κ ℂ :=
  fun i j => 𝔼 z : PhaseWord ι, conj (wordCharacter (signature i) z) *
    wordCharacter (signature j) z

@[simp] theorem averagedPhaseGram_apply {κ : Type*}
    (signature : κ → PhaseWord ι) (i j : κ) :
    averagedPhaseGram signature i j = if signature i = signature j then 1 else 0 := by
  exact wordCharacter_orthogonality _ _

section SignatureClasses

variable {κ η : Type*} [Fintype κ] [Fintype η] [DecidableEq η]

def classVector (signature : κ → η) (a : η) : κ → ℂ :=
  fun i => if signature i = a then 1 else 0

def classBlock (signature : κ → η) (a : η) : Matrix κ κ ℂ :=
  Matrix.vecMulVec (classVector signature a) (star (classVector signature a))

theorem classBlock_posSemidef (signature : κ → η) (a : η) :
    (classBlock signature a).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

def classGram (signature : κ → η) : Matrix κ κ ℂ :=
  ∑ a, classBlock signature a

@[simp] theorem classGram_apply (signature : κ → η) (i j : κ) :
    classGram signature i j = if signature i = signature j then 1 else 0 := by
  classical
  simp only [classGram, Matrix.sum_apply, classBlock, Matrix.vecMulVec_apply,
    classVector, Pi.star_apply]
  rw [Finset.sum_eq_single (signature i)]
  · by_cases h : signature i = signature j
    · simp [h]
    · simp [h, Ne.symm h]
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

theorem classGram_posSemidef (signature : κ → η) :
    (classGram signature).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro a _
  exact classBlock_posSemidef _ _

theorem classBlocks_posSemidef (signature : κ → η) (classes : Finset η) :
    (∑ a ∈ classes, classBlock signature a).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro a _
  exact classBlock_posSemidef _ _

theorem classGram_sub_blocks_posSemidef (signature : κ → η) (classes : Finset η) :
    (classGram signature - ∑ a ∈ classes, classBlock signature a).PosSemidef := by
  rw [classGram, ← Finset.sum_sdiff_eq_sub (Finset.subset_univ classes)]
  exact classBlocks_posSemidef signature (Finset.univ \ classes)

end SignatureClasses

theorem averagedPhaseGram_eq_classGram {κ : Type*} [Fintype κ]
    (signature : κ → PhaseWord ι) :
    averagedPhaseGram signature = classGram signature := by
  ext i j
  simp

theorem averagedPhaseGram_posSemidef {κ : Type*} [Fintype κ]
    (signature : κ → PhaseWord ι) : (averagedPhaseGram signature).PosSemidef := by
  rw [averagedPhaseGram_eq_classGram]
  exact classGram_posSemidef _

theorem averagedPhaseGram_sub_blocks_posSemidef {κ : Type*} [Fintype κ]
    (signature : κ → PhaseWord ι) (classes : Finset (PhaseWord ι)) :
    (averagedPhaseGram signature - ∑ a ∈ classes, classBlock signature a).PosSemidef := by
  rw [averagedPhaseGram_eq_classGram]
  exact classGram_sub_blocks_posSemidef _ _

end QuantumProver.AmplitudeDamping.SecretKey.Phase

namespace QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra

variable {I O J : Type*} [Fintype I] [Fintype O] [Fintype J]

def rankOneKraus (v : I → ℂ) (b : O → ℂ) : Matrix O I ℂ :=
  Matrix.vecMulVec b (star v)

theorem rankOneKraus_gram (v : I → ℂ) (b : O → ℂ) :
    (rankOneKraus v b)ᴴ * rankOneKraus v b =
      (∑ o, star (b o) * b o) • Matrix.vecMulVec v (star v) := by
  ext i j
  simp only [rankOneKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, star_mul, star_star,
    Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro o _
  ring

theorem rankOneKraus_complete [DecidableEq I] (v : J → I → ℂ) (b : J → O → ℂ)
    (hv : ∑ j, Matrix.vecMulVec (v j) (star (v j)) = 1)
    (hb : ∀ j, ∑ o, star (b j o) * b j o = 1) :
    ∑ j, (rankOneKraus (v j) (b j))ᴴ * rankOneKraus (v j) (b j) = 1 := by
  calc
    _ = ∑ j, Matrix.vecMulVec (v j) (star (v j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [rankOneKraus_gram, hb j, one_smul]
    _ = 1 := hv

def outcomeWeight (v : I → ℂ) (ρ : Matrix I I ℂ) : ℂ :=
  ∑ j, ∑ i, star (v i) * ρ i j * v j

theorem outcomeWeight_eq_dotProduct (v : I → ℂ) (ρ : Matrix I I ℂ) :
    outcomeWeight v ρ = star v ⬝ᵥ (ρ *ᵥ v) := by
  simp only [outcomeWeight, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem outcomeWeight_nonnegative (v : I → ℂ) {ρ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) : 0 ≤ outcomeWeight v ρ := by
  rw [outcomeWeight_eq_dotProduct]
  exact hρ.dotProduct_mulVec_nonneg v

theorem rankOneKraus_eval (v : I → ℂ) (b : O → ℂ) (ρ : Matrix I I ℂ) :
    rankOneKraus v b * ρ * (rankOneKraus v b)ᴴ =
      outcomeWeight v ρ • Matrix.vecMulVec b (star b) := by
  ext o p
  simp only [rankOneKraus, outcomeWeight, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, star_mul, star_star,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

section Memory

variable {A : Type*} [Fintype A] [DecidableEq A]

def memoryCompression (v : I → ℂ) : Matrix A (A × I) ℂ :=
  fun a ai => if a = ai.1 then star (v ai.2) else 0

def memoryPreparation (b : O → ℂ) : Matrix (A × O) A ℂ :=
  fun ao a => if ao.1 = a then b ao.2 else 0

theorem memoryPreparation_mul_compression (v : I → ℂ) (b : O → ℂ) :
    memoryPreparation (A := A) b * memoryCompression v =
      (1 : Matrix A A ℂ) ⊗ₖ rankOneKraus v b := by
  ext ao ai
  simp only [Matrix.mul_apply, memoryPreparation, memoryCompression,
    Matrix.kroneckerMap_apply, Matrix.one_apply, rankOneKraus,
    Matrix.vecMulVec_apply, Pi.star_apply]
  rw [Finset.sum_eq_single ai.1]
  · by_cases h : ao.1 = ai.1 <;> simp [h]
  · intro a _ ha
    simp [ha, Ne.symm ha]
  · simp

theorem memoryPreparation_sandwich (b : O → ℂ) (σ : Matrix A A ℂ) :
    memoryPreparation b * σ * (memoryPreparation b)ᴴ =
      σ ⊗ₖ Matrix.vecMulVec b (star b) := by
  ext ao ap
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, memoryPreparation,
    Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  rw [Finset.sum_eq_single ap.1]
  · rw [Finset.sum_eq_single ao.1]
    · simp
      ring
    · intro a _ ha
      simp [ha, Ne.symm ha]
    · simp
  · intro a _ ha
    simp [ha, Ne.symm ha]
  · simp

theorem memoryCompression_posSemidef (v : I → ℂ) {ρ : Matrix (A × I) (A × I) ℂ}
    (hρ : ρ.PosSemidef) :
    (memoryCompression v * ρ * (memoryCompression v)ᴴ).PosSemidef :=
  hρ.mul_mul_conjTranspose_same _

theorem rankOneKraus_withMemory_eval (v : I → ℂ) (b : O → ℂ)
    (ρ : Matrix (A × I) (A × I) ℂ) :
    ((1 : Matrix A A ℂ) ⊗ₖ rankOneKraus v b) * ρ *
      ((1 : Matrix A A ℂ) ⊗ₖ rankOneKraus v b)ᴴ =
      (memoryCompression v * ρ * (memoryCompression v)ᴴ) ⊗ₖ
        Matrix.vecMulVec b (star b) := by
  calc
    _ = memoryPreparation b *
        (memoryCompression v * ρ * (memoryCompression v)ᴴ) *
          (memoryPreparation b)ᴴ := by
      simp only [← memoryPreparation_mul_compression, Matrix.conjTranspose_mul,
        Matrix.mul_assoc]
    _ = _ := memoryPreparation_sandwich _ _

end Memory

end QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra
