import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.BinaryTesting

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.SuperchannelDiscrimination.FlaggedStates

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def flagBlock (A : Matrix n n ℂ) (B : Matrix m m ℂ) : Matrix (n ⊕ m) (n ⊕ m) ℂ :=
  Matrix.fromBlocks A 0 0 B

@[simp] theorem flagBlock_trace (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    (flagBlock A B).trace = A.trace + B.trace := by
  simp [flagBlock, Matrix.trace, Fintype.sum_sum_type]

theorem flagBlock_isHermitian {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (flagBlock A B).IsHermitian := by
  exact Matrix.IsHermitian.fromBlocks hA (by simp) hB

theorem flagBlock_posSemidef {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (flagBlock A B).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (flagBlock_isHermitian hA.1 hB.1)
  intro x
  simpa [flagBlock, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
    Function.comp_def] using
    add_nonneg (hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl))
      (hB.dotProduct_mulVec_nonneg (x ∘ Sum.inr))

theorem flagBlock_posSemidef_iff (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    (flagBlock A B).PosSemidef ↔ A.PosSemidef ∧ B.PosSemidef := by
  constructor
  · intro h
    constructor
    · have hleft : (flagBlock A B).submatrix Sum.inl Sum.inl = A := by
        ext i j
        rfl
      simpa only [hleft] using h.submatrix Sum.inl
    · have hright : (flagBlock A B).submatrix Sum.inr Sum.inr = B := by
        ext i j
        rfl
      simpa only [hright] using h.submatrix Sum.inr
  · rintro ⟨hA, hB⟩
    exact flagBlock_posSemidef hA hB

def IsDensity (A : Matrix n n ℂ) : Prop := A.PosSemidef ∧ A.trace = 1

theorem flagBlock_isDensity {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (htrace : A.trace + B.trace = 1) :
    IsDensity (flagBlock A B) :=
  ⟨flagBlock_posSemidef hA hB, by simpa using htrace⟩

def IsEffect (E : Matrix n n ℂ) : Prop := E.PosSemidef ∧ (1 - E).PosSemidef

def successfulEffect (E : Matrix n n ℂ) : Matrix (n ⊕ m) (n ⊕ m) ℂ :=
  flagBlock E 0

theorem successfulEffect_isEffect {E : Matrix n n ℂ} (hE : IsEffect E) :
    IsEffect (successfulEffect (m := m) E) := by
  constructor
  · exact flagBlock_posSemidef hE.1 Matrix.PosSemidef.zero
  · have hcomp : 1 - successfulEffect (m := m) E = flagBlock (1 - E) 1 := by
      ext i j
      cases i <;> cases j <;> simp [successfulEffect, flagBlock, Matrix.one_apply]
    rw [hcomp]
    exact flagBlock_posSemidef hE.2 Matrix.PosSemidef.one

@[simp] theorem flagBlock_mul (A C : Matrix n n ℂ) (B D : Matrix m m ℂ) :
    flagBlock A B * flagBlock C D = flagBlock (A * C) (B * D) := by
  simp [flagBlock, Matrix.fromBlocks_multiply]

theorem successfulEffect_trace (A E : Matrix n n ℂ) (B : Matrix m m ℂ) :
    (flagBlock A B * successfulEffect E).trace = (A * E).trace := by
  simp [successfulEffect]

theorem successfulEffect_repair_zero (B : Matrix m m ℂ) (E : Matrix n n ℂ) :
    (flagBlock 0 B * successfulEffect E).trace = 0 := by
  simp [successfulEffect_trace]

theorem trace_mul_re_nonneg {A E : Matrix n n ℂ}
    (hA : A.PosSemidef) (hE : E.PosSemidef) : 0 ≤ (A * E).trace.re := by
  have hs : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).posSemidef.1
  have hpos : (CFC.sqrt A * E * CFC.sqrt A).PosSemidef := by
    simpa only [hs] using hE.mul_mul_conjTranspose_same (CFC.sqrt A)
  have htrace : (CFC.sqrt A * E * CFC.sqrt A).trace = (A * E).trace := by
    rw [Matrix.trace_mul_cycle, ← pow_two, CFC.sq_sqrt A hA.nonneg]
  exact (Complex.nonneg_iff.mp (htrace ▸ hpos.trace_nonneg)).1

def acceptanceProbability (A E : Matrix n n ℂ) : ℝ := (A * E).trace.re

theorem acceptanceProbability_bounds {A E : Matrix n n ℂ}
    (hA : IsDensity A) (hE : IsEffect E) :
    0 ≤ acceptanceProbability A E ∧ acceptanceProbability A E ≤ 1 := by
  constructor
  · exact trace_mul_re_nonneg hA.1 hE.1
  · have hcomp := trace_mul_re_nonneg hA.1 hE.2
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re,
      hA.2, Complex.one_re] at hcomp
    dsimp [acceptanceProbability]
    linarith

theorem acceptanceProbability_success (A E : Matrix n n ℂ) (B : Matrix m m ℂ) :
    acceptanceProbability (flagBlock A B) (successfulEffect E) =
      acceptanceProbability A E := by
  simp only [acceptanceProbability, successfulEffect_trace]

theorem acceptanceProbability_weighted_success (p : ℝ) (A E : Matrix n n ℂ)
    (B : Matrix m m ℂ) :
    acceptanceProbability (flagBlock (p • A) ((1 - p) • B)) (successfulEffect E) =
      p * acceptanceProbability A E := by
  simp only [acceptanceProbability, successfulEffect_trace, Matrix.smul_mul,
    Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

def flagBlockHom : (Matrix n n ℂ × Matrix m m ℂ) →⋆ₐ[ℝ]
    Matrix (n ⊕ m) (n ⊕ m) ℂ where
  toFun p := flagBlock p.1 p.2
  map_zero' := by ext i j; cases i <;> cases j <;> simp [flagBlock]
  map_one' := Matrix.fromBlocks_one
  map_add' p q := by simp [flagBlock, Matrix.fromBlocks_add]
  map_mul' p q := by simp [flagBlock, Matrix.fromBlocks_multiply]
  commutes' r := by
    ext i j
    cases i <;> cases j <;> simp [flagBlock, Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
  map_star' p := by
    simp [flagBlock, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]

theorem flagBlockHom_continuous : Continuous (flagBlockHom (n := n) (m := m)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases i <;> cases j <;> simp [flagBlockHom, flagBlock, Matrix.fromBlocks] <;> fun_prop

theorem cfc_flagBlock (f : ℝ → ℝ) {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    cfc f (flagBlock A B) = flagBlock (cfc f A) (cfc f B) := by
  letI : IsometricContinuousFunctionalCalculus ℝ
      (Matrix n n ℂ × Matrix m m ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  have hf : ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ B) :=
    (A.finite_real_spectrum.union B.finite_real_spectrum).continuousOn f
  have hab : IsSelfAdjoint (A, B) := by
    exact Prod.ext hA hB
  have hmap := (flagBlockHom (n := n) (m := m)).map_cfc f (A, B)
    (by simpa only [Prod.spectrum_eq] using hf) flagBlockHom_continuous hab
    (flagBlock_isHermitian hA hB)
  rw [cfc_map_prod (S := ℝ) f A B hf hab hA hB] at hmap
  exact hmap.symm

def entropyBits (A : Matrix n n ℂ) : ℝ :=
  -(cfc (fun x : ℝ => x * Real.log x) A).trace.re / Real.log 2

theorem entropyBits_flagBlock {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    entropyBits (flagBlock A B) = entropyBits A + entropyBits B := by
  simp only [entropyBits, cfc_flagBlock _ hA.1 hB.1, flagBlock_trace, Complex.add_re]
  ring

theorem weighted_mul_log (p x : ℝ) :
    (p * x) * Real.log (p * x) =
      p * (x * Real.log x) + (p * Real.log p) * x := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hx : x = 0
  · simp [hx]
  rw [Real.log_mul hp hx]
  ring

theorem cfc_mul_log_smul (p : ℝ) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc (fun x : ℝ => x * Real.log x) (p • A) =
      p • cfc (fun x : ℝ => x * Real.log x) A + (p * Real.log p) • A := by
  have hcomp := cfc_comp_const_mul (p := IsSelfAdjoint) p
    (fun x : ℝ => x * Real.log x) A
    ((A.finite_real_spectrum.image (fun x : ℝ => p * x)).continuousOn _) hA
  trans cfc (fun x : ℝ => (p * x) * Real.log (p * x)) A
  · exact hcomp.symm
  have hfun : (fun x : ℝ => (p * x) * Real.log (p * x)) =
      (fun x : ℝ => p * (x * Real.log x) + (p * Real.log p) * x) :=
    funext (weighted_mul_log p)
  rw [hfun]
  rw [cfc_add A (fun x : ℝ => p * (x * Real.log x))
      (fun x : ℝ => (p * Real.log p) * x) (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _)]
  rw [cfc_const_mul p _ A (A.finite_real_spectrum.continuousOn _),
    cfc_const_mul_id (p := IsSelfAdjoint) (p * Real.log p) A hA]

theorem entropyBits_smul (p : ℝ) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    entropyBits (p • A) = p * entropyBits A -
      (p * Real.log p / Real.log 2) * A.trace.re := by
  simp only [entropyBits, cfc_mul_log_smul p hA.1, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re]
  ring

def flagEntropyBits (p : ℝ) : ℝ :=
  -(p * Real.log p + (1 - p) * Real.log (1 - p)) / Real.log 2

theorem entropyBits_flagged_density {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : IsDensity A) (hB : IsDensity B) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entropyBits (flagBlock (p • A) ((1 - p) • B)) = flagEntropyBits p +
      p * entropyBits A + (1 - p) * entropyBits B := by
  rw [entropyBits_flagBlock (hA.1.smul hp0) (hB.1.smul (sub_nonneg.mpr hp1)),
    entropyBits_smul p hA.1, entropyBits_smul (1 - p) hB.1, hA.2, hB.2]
  simp only [Complex.one_re, mul_one, flagEntropyBits]
  ring

theorem weighted_flagBlock_isDensity {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : IsDensity A) (hB : IsDensity B) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsDensity (flagBlock (p • A) ((1 - p) • B)) := by
  apply flagBlock_isDensity (hA.1.smul hp0) (hB.1.smul (sub_nonneg.mpr hp1))
  simp only [Matrix.trace_smul, hA.2, hB.2, ← add_smul, add_sub_cancel,
    one_smul]

def finiteRelativeEntropyBits (A B : Matrix n n ℂ) : ℝ :=
  (A * (cfc Real.log A - cfc Real.log B)).trace.re / Real.log 2

theorem finiteRelativeEntropyBits_eq_spectral {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    finiteRelativeEntropyBits A B = ((cfc (fun x : ℝ => x * Real.log x) A).trace.re -
      (A * cfc Real.log B).trace.re) / Real.log 2 := by
  have hprod : cfc (fun x : ℝ => x * Real.log x) A = A * cfc Real.log A := by
    rw [cfc_mul (p := IsSelfAdjoint) (fun x : ℝ => x) Real.log A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_id' (p := IsSelfAdjoint) ℝ A hA]
  simp only [finiteRelativeEntropyBits, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re, hprod]

theorem finiteRelativeEntropyBits_smul {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    finiteRelativeEntropyBits (p • A) (q • B) =
      p * finiteRelativeEntropyBits A B +
        (p * Real.log (p / q) / Real.log 2) * A.trace.re := by
  have hlog : cfc Real.log (q • B) =
      algebraMap ℝ (Matrix n n ℂ) (Real.log q) + cfc Real.log B := by
    simpa only [CFC.log] using CFC.log_smul' B hq hB.isStrictlyPositive
  rw [finiteRelativeEntropyBits_eq_spectral (hA.smul hp).1,
    finiteRelativeEntropyBits_eq_spectral hA.1, cfc_mul_log_smul p hA.1, hlog]
  simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re]
  rw [weighted_log_quotient p (ne_of_gt hq)]
  ring

theorem finiteRelativeEntropyBits_flagBlock_of_hermitian {A B : Matrix n n ℂ}
    {C D : Matrix m m ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian) (hD : D.IsHermitian) :
    finiteRelativeEntropyBits (flagBlock A C) (flagBlock B D) =
      finiteRelativeEntropyBits A B + finiteRelativeEntropyBits C D := by
  have hsub : flagBlock (cfc Real.log A) (cfc Real.log C) -
      flagBlock (cfc Real.log B) (cfc Real.log D) =
      flagBlock (cfc Real.log A - cfc Real.log B) (cfc Real.log C - cfc Real.log D) := by
    ext i j
    cases i <;> cases j <;> simp [flagBlock]
  simp only [finiteRelativeEntropyBits, cfc_flagBlock _ hA hC,
    cfc_flagBlock _ hB hD, hsub, flagBlock_mul, flagBlock_trace, Complex.add_re]
  ring

theorem finiteRelativeEntropyBits_flagBlock {A B : Matrix n n ℂ}
    {C D : Matrix m m ℂ} (hA : A.PosSemidef) (hB : B.PosDef)
    (hC : C.PosSemidef) (hD : D.PosDef) :
    finiteRelativeEntropyBits (flagBlock A C) (flagBlock B D) =
      finiteRelativeEntropyBits A B + finiteRelativeEntropyBits C D :=
  finiteRelativeEntropyBits_flagBlock_of_hermitian hA.1 hB.1 hC.1 hD.1

theorem finiteRelativeEntropyBits_weighted_flag {A B : Matrix n n ℂ}
    {C D : Matrix m m ℂ} (hA : IsDensity A) (hB : B.PosDef)
    (hC : IsDensity C) (hD : D.PosDef) {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    finiteRelativeEntropyBits (flagBlock (p • A) ((1 - p) • C))
      (flagBlock (q • B) ((1 - q) • D)) =
      binaryRelativeEntropyBits p q + p * finiteRelativeEntropyBits A B +
        (1 - p) * finiteRelativeEntropyBits C D := by
  rw [finiteRelativeEntropyBits_flagBlock (hA.1.smul hp0) (hB.smul hq0)
    (hC.1.smul (sub_nonneg.mpr hp1)) (hD.smul (sub_pos.mpr hq1)),
    finiteRelativeEntropyBits_smul hA.1 hB hp0 hq0,
    finiteRelativeEntropyBits_smul hC.1 hD (sub_nonneg.mpr hp1) (sub_pos.mpr hq1),
    hA.2, hC.2]
  simp only [Complex.one_re, mul_one, binaryRelativeEntropyBits]
  ring

def HasSupportIn (A B : Matrix n n ℂ) : Prop :=
  ∀ v : n → ℂ, B *ᵥ v = 0 → A *ᵥ v = 0

theorem hasSupportIn_self (A : Matrix n n ℂ) : HasSupportIn A A := by
  intro v hv
  exact hv

theorem hasSupportIn_zero (B : Matrix n n ℂ) : HasSupportIn 0 B := by
  intro v _
  simp

theorem hasSupportIn_of_posDef (A : Matrix n n ℂ) {B : Matrix n n ℂ}
    (hB : B.PosDef) : HasSupportIn A B := by
  intro v hv
  have hv0 : v = 0 := (Matrix.mulVec_injective_iff_isUnit.mpr hB.isUnit) (by simpa using hv)
  simp [hv0]

theorem hasSupportIn_flagBlock_iff (A B : Matrix n n ℂ) (C D : Matrix m m ℂ) :
    HasSupportIn (flagBlock A C) (flagBlock B D) ↔
      HasSupportIn A B ∧ HasSupportIn C D := by
  constructor
  · intro h
    constructor
    · intro v hv
      have hvflag : flagBlock B D *ᵥ Sum.elim v 0 = 0 := by
        ext i
        cases i <;> simp [flagBlock, Matrix.fromBlocks_mulVec, hv]
      have hflag := h (Sum.elim v 0) hvflag
      ext i
      simpa [flagBlock, Matrix.fromBlocks_mulVec] using congrFun hflag (Sum.inl i)
    · intro v hv
      have hvflag : flagBlock B D *ᵥ Sum.elim 0 v = 0 := by
        ext i
        cases i <;> simp [flagBlock, Matrix.fromBlocks_mulVec, hv]
      have hflag := h (Sum.elim 0 v) hvflag
      ext i
      simpa [flagBlock, Matrix.fromBlocks_mulVec] using congrFun hflag (Sum.inr i)
  · rintro ⟨hAB, hCD⟩ v hv
    have hvL : B *ᵥ (v ∘ Sum.inl) = 0 := by
      ext i
      simpa [flagBlock, Matrix.fromBlocks_mulVec] using congrFun hv (Sum.inl i)
    have hvR : D *ᵥ (v ∘ Sum.inr) = 0 := by
      ext i
      simpa [flagBlock, Matrix.fromBlocks_mulVec] using congrFun hv (Sum.inr i)
    ext i
    cases i <;> simp [flagBlock, Matrix.fromBlocks_mulVec, hAB _ hvL, hCD _ hvR]

def relativeEntropyBits (A B : Matrix n n ℂ) : EReal := by
  classical
  exact if HasSupportIn A B then (finiteRelativeEntropyBits A B : EReal) else ⊤

theorem relativeEntropyBits_zero_left (B : Matrix n n ℂ) :
    relativeEntropyBits 0 B = 0 := by
  simp [relativeEntropyBits, hasSupportIn_zero, finiteRelativeEntropyBits]

theorem relativeEntropyBits_ne_bot (A B : Matrix n n ℂ) : relativeEntropyBits A B ≠ ⊥ := by
  classical
  unfold relativeEntropyBits
  split_ifs <;> simp

theorem relativeEntropyBits_eq_top_iff (A B : Matrix n n ℂ) :
    relativeEntropyBits A B = ⊤ ↔ ¬ HasSupportIn A B := by
  classical
  simp [relativeEntropyBits]

theorem relativeEntropyBits_of_posDef (A : Matrix n n ℂ) {B : Matrix n n ℂ}
    (hB : B.PosDef) : relativeEntropyBits A B = (finiteRelativeEntropyBits A B : EReal) := by
  simp [relativeEntropyBits, hasSupportIn_of_posDef A hB]

theorem relativeEntropyBits_flagBlock {A B : Matrix n n ℂ} {C D : Matrix m m ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) (hD : D.PosSemidef) :
    relativeEntropyBits (flagBlock A C) (flagBlock B D) =
      relativeEntropyBits A B + relativeEntropyBits C D := by
  by_cases hAB : HasSupportIn A B <;> by_cases hCD : HasSupportIn C D <;>
    simp [relativeEntropyBits, hasSupportIn_flagBlock_iff, hAB, hCD,
      finiteRelativeEntropyBits_flagBlock_of_hermitian hA.1 hB.1 hC.1 hD.1,
      EReal.coe_add]

theorem weighted_flagged_density_relativeEntropy {A B : Matrix n n ℂ}
    {C D : Matrix m m ℂ} (hA : IsDensity A) (hB : IsDensity B) (hBdef : B.PosDef)
    (hC : IsDensity C) (hD : IsDensity D) (hDdef : D.PosDef) {p q : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 < q) (hq1 : q < 1) :
    IsDensity (flagBlock (p • A) ((1 - p) • C)) ∧
      IsDensity (flagBlock (q • B) ((1 - q) • D)) ∧
      relativeEntropyBits (flagBlock (p • A) ((1 - p) • C))
        (flagBlock (q • B) ((1 - q) • D)) =
        ((binaryRelativeEntropyBits p q + p * finiteRelativeEntropyBits A B +
          (1 - p) * finiteRelativeEntropyBits C D : ℝ) : EReal) := by
  refine ⟨weighted_flagBlock_isDensity hA hC hp0 hp1,
    weighted_flagBlock_isDensity hB hD hq0.le hq1.le, ?_⟩
  have hs : HasSupportIn (flagBlock (p • A) ((1 - p) • C))
      (flagBlock (q • B) ((1 - q) • D)) :=
    (hasSupportIn_flagBlock_iff _ _ _ _).mpr
      ⟨hasSupportIn_of_posDef _ (hBdef.smul hq0),
        hasSupportIn_of_posDef _ (hDdef.smul (sub_pos.mpr hq1))⟩
  rw [relativeEntropyBits, if_pos hs,
    finiteRelativeEntropyBits_weighted_flag hA hBdef hC hDdef hp0 hp1 hq0 hq1]

end QuantumProver.SuperchannelDiscrimination.FlaggedStates
