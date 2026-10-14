import Mathlib

noncomputable section
namespace QuantumProver.DepolarizingPrivateInformation

open scoped BigOperators ComplexOrder
open Matrix

abbrev CMat (ι : Type*) := Matrix ι ι ℂ
abbrev Qubit := Fin 2
abbrev PauliIndex := Fin 4
abbrev QubitMatrix := CMat Qubit
abbrev EnvironmentMatrix := CMat PauliIndex

def IsDensity {ι : Type*} [Fintype ι] (ρ : CMat ι) : Prop :=
  ρ.PosSemidef ∧ Matrix.trace ρ = 1

structure Density (ι : Type*) [Fintype ι] where
  mat : CMat ι
  psd : mat.PosSemidef
  trace_one : Matrix.trace mat = 1

namespace Density
variable {ι : Type*} [Fintype ι]
theorem isDensity (ρ : Density ι) : IsDensity ρ.mat := ⟨ρ.psd, ρ.trace_one⟩
end Density

def realTrace {ι : Type*} [Fintype ι] (A : CMat ι) : ℝ := (Matrix.trace A).re

def pauli (e : PauliIndex) : QubitMatrix :=
  ![!![1, 0; 0, 1], !![0, 1; 1, 0],
    !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]] e

def sourceToCanonical : PauliIndex ≃ PauliIndex where
  toFun := ![0, 3, 1, 2]
  invFun := ![0, 2, 3, 1]
  left_inv := by intro i; fin_cases i <;> decide
  right_inv := by intro i; fin_cases i <;> decide

@[simp] theorem pauli_conjTranspose (e : PauliIndex) : (pauli e)ᴴ = pauli e := by
  fin_cases e <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.conjTranspose_apply]

@[simp] theorem pauli_conjTranspose_mul (e : PauliIndex) :
    (pauli e)ᴴ * pauli e = 1 := by
  fin_cases e <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauli, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.I_mul_I]

@[simp] theorem pauli_mul_self (e : PauliIndex) : pauli e * pauli e = 1 := by
  simpa only [pauli_conjTranspose] using pauli_conjTranspose_mul e

def krausWeight (p : ℝ) (e : PauliIndex) : ℝ :=
  if e = 0 then 1 - 3 * p / 4 else p / 4

noncomputable def kraus (p : ℝ) (e : PauliIndex) : QubitMatrix :=
  (Real.sqrt (krausWeight p e) : ℂ) • pauli e

theorem krausWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (e : PauliIndex) : 0 ≤ krausWeight p e := by
  unfold krausWeight
  split_ifs <;> nlinarith

@[simp] theorem krausWeight_sum (p : ℝ) : ∑ e, krausWeight p e = 1 := by
  simp [krausWeight, Fin.sum_univ_succ]
  ring

def stinespring (p : ℝ) : Matrix (Qubit × PauliIndex) Qubit ℂ :=
  fun be a => kraus p be.2 be.1 a

def partialTraceRight {ι κ : Type*} [Fintype κ]
    (X : CMat (ι × κ)) : CMat ι := fun i j => ∑ e, X (i,e) (j,e)

def partialTraceLeft {ι κ : Type*} [Fintype ι]
    (X : CMat (ι × κ)) : CMat κ := fun e f => ∑ i, X (i,e) (i,f)

def jointChannel (p : ℝ) (ρ : QubitMatrix) : CMat (Qubit × PauliIndex) :=
  stinespring p * ρ * (stinespring p)ᴴ

def bobChannel (p : ℝ) (ρ : QubitMatrix) : QubitMatrix :=
  ∑ e, kraus p e * ρ * (kraus p e)ᴴ

def eveChannel (p : ℝ) (ρ : QubitMatrix) : EnvironmentMatrix :=
  fun e f => Matrix.trace (kraus p e * ρ * (kraus p f)ᴴ)

@[simp] theorem trace_partialTraceRight {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : CMat (ι × κ)) : Matrix.trace (partialTraceRight X) = Matrix.trace X := by
  simp [partialTraceRight, Matrix.trace, Fintype.sum_prod_type]

@[simp] theorem trace_partialTraceLeft {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : CMat (ι × κ)) : Matrix.trace (partialTraceLeft X) = Matrix.trace X := by
  change (∑ e, ∑ i, X (i,e) (i,e)) = ∑ be, X be be
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem partialTraceRight_posSemidef {ι κ : Type*} [Fintype κ]
    {X : CMat (ι × κ)} (hX : X.PosSemidef) : (partialTraceRight X).PosSemidef := by
  have h := Matrix.posSemidef_sum Finset.univ
    (fun e (_ : e ∈ Finset.univ) => hX.submatrix (fun i => (i,e)))
  convert h using 1
  ext i j
  simp [partialTraceRight, Matrix.sum_apply]

theorem partialTraceLeft_posSemidef {ι κ : Type*} [Fintype ι]
    {X : CMat (ι × κ)} (hX : X.PosSemidef) : (partialTraceLeft X).PosSemidef := by
  have h := Matrix.posSemidef_sum Finset.univ
    (fun i (_ : i ∈ Finset.univ) => hX.submatrix (fun e => (i,e)))
  convert h using 1
  ext e f
  simp [partialTraceLeft, Matrix.sum_apply]

theorem partialTraceRight_joint (p : ℝ) (ρ : QubitMatrix) :
    partialTraceRight (jointChannel p ρ) = bobChannel p ρ := by
  ext i j
  simp [partialTraceRight, jointChannel, stinespring, bobChannel,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply]

theorem partialTraceLeft_joint (p : ℝ) (ρ : QubitMatrix) :
    partialTraceLeft (jointChannel p ρ) = eveChannel p ρ := by
  ext e f
  simp [partialTraceLeft, jointChannel, stinespring, eveChannel, Matrix.trace,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]

theorem jointChannel_posSemidef (p : ℝ) {ρ : QubitMatrix} (hρ : ρ.PosSemidef) :
    (jointChannel p ρ).PosSemidef := hρ.mul_mul_conjTranspose_same (stinespring p)

theorem scaled_pauli_norm (e : PauliIndex) (r : ℝ) :
    ((r : ℂ) • pauli e)ᴴ * ((r : ℂ) • pauli e) =
      ((r * r : ℝ) : ℂ) • (1 : QubitMatrix) := by
  simp [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Complex.ofReal_mul]

theorem kraus_conjTranspose_mul {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (e : PauliIndex) : (kraus p e)ᴴ * kraus p e =
      (krausWeight p e : ℂ) • (1 : QubitMatrix) := by
  unfold kraus
  rw [scaled_pauli_norm]
  congr 2
  exact_mod_cast Real.mul_self_sqrt (krausWeight_nonneg hp0 hp1 e)

theorem kraus_complete {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ e, (kraus p e)ᴴ * kraus p e = (1 : QubitMatrix) := by
  have hw : (∑ e, (krausWeight p e : ℂ)) = 1 := by
    exact_mod_cast krausWeight_sum p
  simp_rw [kraus_conjTranspose_mul hp0 hp1]
  rw [← Finset.sum_smul, hw, one_smul]

theorem stinespring_complete {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (stinespring p)ᴴ * stinespring p = (1 : QubitMatrix) := by
  calc
    _ = ∑ e, (kraus p e)ᴴ * kraus p e := by
      ext i j
      simp [stinespring, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type, Matrix.sum_apply, Finset.sum_comm]
    _ = 1 := kraus_complete hp0 hp1

theorem trace_jointChannel {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : QubitMatrix) : Matrix.trace (jointChannel p ρ) = Matrix.trace ρ := by
  rw [jointChannel, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    stinespring_complete hp0 hp1, Matrix.one_mul]

theorem bobChannel_isDensity {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ : QubitMatrix} (hρ : IsDensity ρ) : IsDensity (bobChannel p ρ) := by
  rw [← partialTraceRight_joint]
  exact ⟨partialTraceRight_posSemidef (jointChannel_posSemidef p hρ.1), by
    rw [trace_partialTraceRight, trace_jointChannel hp0 hp1, hρ.2]⟩

theorem eveChannel_isDensity {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ : QubitMatrix} (hρ : IsDensity ρ) : IsDensity (eveChannel p ρ) := by
  rw [← partialTraceLeft_joint]
  exact ⟨partialTraceLeft_posSemidef (jointChannel_posSemidef p hρ.1), by
    rw [trace_partialTraceLeft, trace_jointChannel hp0 hp1, hρ.2]⟩

theorem scaled_pauli_sandwich (e : PauliIndex) (r : ℝ) (ρ : QubitMatrix) :
    ((r : ℂ) • pauli e) * ρ * ((r : ℂ) • pauli e)ᴴ =
      ((r * r : ℝ) : ℂ) • (pauli e * ρ * (pauli e)ᴴ) := by
  simp [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Complex.ofReal_mul]

theorem kraus_sandwich {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (e : PauliIndex) (ρ : QubitMatrix) :
    kraus p e * ρ * (kraus p e)ᴴ =
      (krausWeight p e : ℂ) • (pauli e * ρ * (pauli e)ᴴ) := by
  unfold kraus
  rw [scaled_pauli_sandwich]
  congr 2
  exact_mod_cast Real.mul_self_sqrt (krausWeight_nonneg hp0 hp1 e)

theorem bobChannel_eq_depolarizing {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : QubitMatrix) :
    bobChannel p ρ = ((1-p : ℝ) : ℂ) • ρ +
      (((p/2 : ℝ) : ℂ) * Matrix.trace ρ) • (1 : QubitMatrix) := by
  unfold bobChannel
  simp_rw [kraus_sandwich hp0 hp1]
  ext i j
  simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [krausWeight, pauli, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;> ring

end QuantumProver.DepolarizingPrivateInformation
