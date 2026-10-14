import QuantumProver.InformationTheory.ConditionalEntropy.Definitions
import QuantumProver.InformationTheory.ConditionalEntropy.ConditionalRange
import Mathlib.Analysis.Convex.Jensen
import QuantumProver.InformationTheory.QuantumEntropy.PartialTraceKraus
import QuantumProver.InformationTheory.QuantumEntropy.StrongSubadditivity
import QuantumProver.InformationTheory.SuperchannelDiscrimination.FlaggedStates

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.ConditionalEntropy.MixtureEntropy

open QuantumProver.SuperchannelDiscrimination.FlaggedStates

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def reindexStarAlgHom (e : I ≃ J) : Matrix I I ℂ →⋆ₐ[ℝ] Matrix J J ℂ :=
  { (Matrix.reindexAlgEquiv ℝ ℂ e).toAlgHom with
    map_star' := by
      intro X
      ext i j
      rfl }

theorem reindexStarAlgHom_continuous (e : I ≃ J) :
    Continuous (reindexStarAlgHom e) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun X : Matrix I I ℂ => X (e.symm i) (e.symm j))
  fun_prop

theorem cfc_reindex (e : I ≃ J) (f : ℝ → ℝ) {X : Matrix I I ℂ}
    (hX : X.IsHermitian) :
    cfc f (Matrix.reindex e e X) = Matrix.reindex e e (cfc f X) := by
  exact ((reindexStarAlgHom e).map_cfc f X (X.finite_real_spectrum.continuousOn _)
    (reindexStarAlgHom_continuous e) hX (hX.submatrix e.symm)).symm

omit [DecidableEq I] [DecidableEq J] in
theorem trace_reindex (e : I ≃ J) (X : Matrix I I ℂ) :
    (Matrix.reindex e e X).trace = X.trace := by
  change (∑ j : J, X (e.symm j) (e.symm j)) = ∑ i : I, X i i
  exact Equiv.sum_comp e.symm (fun i => X i i)

theorem entropyBits_reindex (e : I ≃ J) {X : Matrix I I ℂ}
    (hX : X.IsHermitian) :
    entropyBits (Matrix.reindex e e X) = entropyBits X := by
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
      (Matrix.reindex e e X) =
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits X
  rw [QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits,
    cfc_reindex e _ hX, trace_reindex]
  rfl

theorem isDensity_reindex (e : I ≃ J) {X : Matrix I I ℂ}
    (hX : IsDensity X) : IsDensity (Matrix.reindex e e X) :=
  ⟨hX.1.submatrix e.symm, (trace_reindex e X).trans hX.2⟩

@[simp] theorem entropyBits_zero : entropyBits (0 : Matrix I I ℂ) = 0 := by
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
    (0 : Matrix I I ℂ) = 0
  simp [QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits]

def flagEquiv (I : Type*) : I ⊕ I ≃ I × Bool where
  toFun := Sum.elim (fun i => (i, false)) (fun i => (i, true))
  invFun := fun ib => if ib.2 then Sum.inr ib.1 else Sum.inl ib.1
  left_inv := by intro i; cases i <;> rfl
  right_inv := by rintro ⟨i, b⟩; cases b <;> rfl

def binaryFlagged (p : ℝ) (X Y : Matrix I I ℂ) :
    Matrix (I × Bool) (I × Bool) ℂ :=
  Matrix.reindex (flagEquiv I) (flagEquiv I)
    (flagBlock ((1-p) • X) (p • Y))

omit [Fintype I] [DecidableEq I] in
@[simp] theorem binaryFlagged_false_false (p : ℝ) (X Y : Matrix I I ℂ) (i j : I) :
    binaryFlagged p X Y (i, false) (j, false) = ((1-p) • X) i j := rfl

omit [Fintype I] [DecidableEq I] in
@[simp] theorem binaryFlagged_true_true (p : ℝ) (X Y : Matrix I I ℂ) (i j : I) :
    binaryFlagged p X Y (i, true) (j, true) = (p • Y) i j := rfl

omit [Fintype I] [DecidableEq I] in
@[simp] theorem binaryFlagged_false_true (p : ℝ) (X Y : Matrix I I ℂ) (i j : I) :
    binaryFlagged p X Y (i, false) (j, true) = 0 := rfl

omit [Fintype I] [DecidableEq I] in
@[simp] theorem binaryFlagged_true_false (p : ℝ) (X Y : Matrix I I ℂ) (i j : I) :
    binaryFlagged p X Y (i, true) (j, false) = 0 := rfl

theorem binaryFlagged_posSemidef {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {X Y : Matrix I I ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    (binaryFlagged p X Y).PosSemidef :=
  (flagBlock_posSemidef (hX.smul (sub_nonneg.mpr hp1)) (hY.smul hp0)).submatrix
    (flagEquiv I).symm

theorem binaryFlagged_isDensity {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {X Y : Matrix I I ℂ} (hX : IsDensity X) (hY : IsDensity Y) :
    IsDensity (binaryFlagged p X Y) := by
  apply isDensity_reindex
  simpa only [sub_sub_cancel] using
    weighted_flagBlock_isDensity hX hY (sub_nonneg.mpr hp1) (by linarith)

theorem entropyBits_binaryFlagged {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {X Y : Matrix I I ℂ} (hX : IsDensity X) (hY : IsDensity Y) :
    entropyBits (binaryFlagged p X Y) = flagEntropyBits p +
      (1-p) * entropyBits X + p * entropyBits Y := by
  rw [binaryFlagged, entropyBits_reindex _
    (flagBlock_posSemidef (hX.1.smul (sub_nonneg.mpr hp1)) (hY.1.smul hp0)).1]
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
      (flagBlock ((1-p) • X) (p • Y)) = flagEntropyBits p +
    (1-p) * QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits X +
    p * QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits Y
  rw [entropyBits_flagBlock (hX.1.smul (sub_nonneg.mpr hp1)) (hY.1.smul hp0),
    entropyBits_smul (1-p) hX.1, entropyBits_smul p hY.1, hX.2, hY.2]
  simp only [Complex.one_re, mul_one, flagEntropyBits]
  ring

theorem binaryFlagged_quantumMarginal (p : ℝ) (X Y : Matrix I I ℂ) :
    (fun i j => ∑ b : Bool, binaryFlagged p X Y (i,b) (j,b)) =
      (1-p) • X + p • Y := by
  ext i j
  simp [Matrix.add_apply, add_comm]

theorem binaryFlagged_flagMarginal {X Y : Matrix I I ℂ}
    (hX : X.trace = 1) (hY : Y.trace = 1) (p : ℝ) :
    (fun b b' => ∑ i, binaryFlagged p X Y (i,b) (i,b')) =
      Matrix.diagonal (fun b : Bool => if b then (p : ℂ) else ((1-p : ℝ) : ℂ)) := by
  have hsumX : (∑ i, ((1-p) • X) i i) = ((1-p : ℝ) : ℂ) := by
    change (((1-p) • X).trace) = _
    rw [Matrix.trace_smul, hX]
    simp
  have hsumY : (∑ i, (p • Y) i i) = (p : ℂ) := by
    change ((p • Y).trace) = _
    rw [Matrix.trace_smul, hY]
    simp
  ext b b'
  cases b <;> cases b' <;>
    simp only [binaryFlagged_false_false, binaryFlagged_false_true,
      binaryFlagged_true_false, binaryFlagged_true_true, hsumX, hsumY,
      Finset.sum_const_zero] <;> rfl

end QuantumProver.ConditionalEntropy.MixtureEntropy

namespace QuantumProver.ConditionalEntropy.MixtureEntropy

open QuantumProver.SuperchannelDiscrimination.FlaggedStates

variable {I J A B : Type*} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
  [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]

def unitRightEquiv (I : Type*) : I × Unit ≃ I where
  toFun := Prod.fst
  invFun := fun i => (i, ())
  left_inv := by rintro ⟨i,u⟩; cases u; rfl
  right_inv := by intro i; rfl

def unitLeftEquiv (I : Type*) : Unit × I ≃ I where
  toFun := Prod.snd
  invFun := fun i => ((),i)
  left_inv := by rintro ⟨u,i⟩; cases u; rfl
  right_inv := by intro i; rfl

def singletonMiddleEquiv (A B : Type*) : A × B ≃ A × (Unit × B) where
  toFun := fun ab => (ab.1, ((), ab.2))
  invFun := fun aub => (aub.1, aub.2.2)
  left_inv := by intro ab; rfl
  right_inv := by rintro ⟨a,u,b⟩; cases u; rfl

theorem entropyBits_unit_of_trace_one {R : Matrix Unit Unit ℂ}
    (htrace : R.trace = 1) : entropyBits R = 0 := by
  have hR : R = 1 := by
    ext i j
    cases i
    cases j
    simpa [Matrix.trace, Matrix.diag] using htrace
  rw [hR]
  change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
    (1 : Matrix Unit Unit ℂ) = 0
  simp [QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits]

def singletonMiddle (R : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × (Unit × B)) (A × (Unit × B)) ℂ :=
  Matrix.reindex (singletonMiddleEquiv A B) (singletonMiddleEquiv A B) R

theorem singletonMiddle_marginalAB (R : Matrix (A × B) (A × B) ℂ) :
    QuantumProver.QuantumEntropy.marginalAB (singletonMiddle R) =
      Matrix.reindex (unitRightEquiv A).symm (unitRightEquiv A).symm
        (QuantumProver.QuantumEntropy.partialTrace_right R) := by
  ext ⟨a,u⟩ ⟨a',u'⟩
  cases u
  cases u'
  rfl

theorem singletonMiddle_marginalBC (R : Matrix (A × B) (A × B) ℂ) :
    QuantumProver.QuantumEntropy.marginalBC (singletonMiddle R) =
      Matrix.reindex (unitLeftEquiv B).symm (unitLeftEquiv B).symm
        (QuantumProver.QuantumEntropy.partialTrace_left R) := by
  ext ⟨u,b⟩ ⟨u',b'⟩
  cases u
  cases u'
  rfl

theorem partialTraceLeft_mix (p : ℝ) (R S : Matrix (A × B) (A × B) ℂ) :
    QuantumProver.QuantumEntropy.partialTrace_left (mix p R S) =
      mix p (QuantumProver.QuantumEntropy.partialTrace_left R)
        (QuantumProver.QuantumEntropy.partialTrace_left S) := by
  ext b b'
  simp [QuantumProver.QuantumEntropy.partialTrace_left, mix, Matrix.add_apply,
    Matrix.smul_apply, Finset.sum_add_distrib, Finset.mul_sum]

def conditionalFlagged (p : ℝ) (R S : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × (B × Bool)) (A × (B × Bool)) ℂ :=
  Matrix.reindex (Equiv.prodAssoc A B Bool) (Equiv.prodAssoc A B Bool)
    (binaryFlagged p R S)

theorem conditionalFlagged_isDensity {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {R S : Matrix (A × B) (A × B) ℂ} (hR : IsDensity R) (hS : IsDensity S) :
    IsDensity (conditionalFlagged p R S) :=
  isDensity_reindex _ (binaryFlagged_isDensity hp0 hp1 hR hS)

theorem conditionalFlagged_marginalAB (p : ℝ)
    (R S : Matrix (A × B) (A × B) ℂ) :
    QuantumProver.QuantumEntropy.marginalAB (conditionalFlagged p R S) = mix p R S := by
  exact binaryFlagged_quantumMarginal p R S

theorem conditionalFlagged_marginalBC (p : ℝ)
    (R S : Matrix (A × B) (A × B) ℂ) :
    QuantumProver.QuantumEntropy.marginalBC (conditionalFlagged p R S) =
      binaryFlagged p (QuantumProver.QuantumEntropy.partialTrace_left R)
        (QuantumProver.QuantumEntropy.partialTrace_left S) := by
  ext ⟨b,c⟩ ⟨b',c'⟩
  cases c <;> cases c' <;>
    simp [QuantumProver.QuantumEntropy.marginalBC, QuantumProver.QuantumEntropy.partialTrace_left,
      conditionalFlagged, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.smul_apply, Finset.mul_sum]

theorem conditionalFlagged_marginalB (p : ℝ)
    (R S : Matrix (A × B) (A × B) ℂ) :
    QuantumProver.QuantumEntropy.marginalB (conditionalFlagged p R S) =
      mix p (QuantumProver.QuantumEntropy.partialTrace_left R)
        (QuantumProver.QuantumEntropy.partialTrace_left S) := by
  rw [QuantumProver.QuantumEntropy.marginalB, conditionalFlagged_marginalAB,
    partialTraceLeft_mix]

theorem entropyBits_conditionalFlagged {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {R S : Matrix (A × B) (A × B) ℂ} (hR : IsDensity R) (hS : IsDensity S) :
    entropyBits (conditionalFlagged p R S) = binaryEntropy p +
      (1-p) * entropyBits R + p * entropyBits S := by
  rw [conditionalFlagged,
    entropyBits_reindex _ (binaryFlagged_posSemidef hp0 hp1 hR.1 hS.1).1]
  exact entropyBits_binaryFlagged hp0 hp1 hR hS

theorem conditionalEntropy_conditionalFlagged {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {R S : Matrix (A × B) (A × B) ℂ} (hR : IsDensity R) (hS : IsDensity S) :
    conditionalEntropyBits (conditionalFlagged p R S) =
      (1-p) * conditionalEntropyBits R + p * conditionalEntropyBits S := by
  rw [conditionalEntropyBits, entropyBits_conditionalFlagged hp0 hp1 hR hS]
  change _ - entropyBits (QuantumProver.QuantumEntropy.marginalBC (conditionalFlagged p R S)) = _
  rw [conditionalFlagged_marginalBC,
    entropyBits_binaryFlagged hp0 hp1
      (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR)
      (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hS)]
  simp only [conditionalEntropyBits, binaryEntropy]
  ring

def firstFlagged (p : ℝ) (R S : Matrix I I ℂ) :
    Matrix (Bool × I) (Bool × I) ℂ :=
  Matrix.reindex (Equiv.prodComm I Bool) (Equiv.prodComm I Bool) (binaryFlagged p R S)

theorem firstFlagged_isDensity {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {R S : Matrix I I ℂ} (hR : IsDensity R) (hS : IsDensity S) :
    IsDensity (firstFlagged p R S) :=
  isDensity_reindex _ (binaryFlagged_isDensity hp0 hp1 hR hS)

theorem firstFlagged_quantumMarginal (p : ℝ) (R S : Matrix I I ℂ) :
    QuantumProver.QuantumEntropy.partialTrace_left (firstFlagged p R S) = mix p R S := by
  exact binaryFlagged_quantumMarginal p R S

theorem conditionalEntropy_firstFlagged {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {R S : Matrix I I ℂ} (hR : IsDensity R) (hS : IsDensity S) :
    conditionalEntropyBits (firstFlagged p R S) = binaryEntropy p +
      (1-p) * entropyBits R + p * entropyBits S - entropyBits (mix p R S) := by
  rw [conditionalEntropyBits, firstFlagged_quantumMarginal, firstFlagged,
    entropyBits_reindex _ (binaryFlagged_posSemidef hp0 hp1 hR.1 hS.1).1,
    entropyBits_binaryFlagged hp0 hp1 hR hS]

theorem firstFlagged_endpoint_mix (p : ℝ) (R S : Matrix I I ℂ) :
    mix p (firstFlagged 0 R R) (firstFlagged 1 S S) = firstFlagged p R S := by
  ext ⟨b,i⟩ ⟨b',j⟩
  cases b <;> cases b' <;>
    simp [mix, firstFlagged, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.add_apply, Matrix.smul_apply]

theorem entropyBits_binaryDiagonal {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entropyBits (Matrix.diagonal (fun b : Bool =>
      if b then (p : ℂ) else ((1-p : ℝ) : ℂ))) = binaryEntropy p := by
  have hU : IsDensity (1 : Matrix Unit Unit ℂ) := ⟨Matrix.PosSemidef.one, by simp⟩
  have hD : Matrix.diagonal (fun b : Bool =>
        if b then (p : ℂ) else ((1-p : ℝ) : ℂ)) =
      Matrix.reindex (unitLeftEquiv Bool) (unitLeftEquiv Bool)
        (binaryFlagged p (1 : Matrix Unit Unit ℂ) 1) := by
    ext b b'
    cases b <;> cases b' <;>
      simp [Matrix.diagonal, Matrix.reindex_apply, Matrix.submatrix_apply,
        unitLeftEquiv, Matrix.one_apply, Matrix.smul_apply]
  rw [hD, entropyBits_reindex _ (binaryFlagged_posSemidef hp0 hp1 hU.1 hU.1).1,
    entropyBits_binaryFlagged hp0 hp1 hU hU, entropyBits_unit_of_trace_one hU.2]
  simp only [mul_zero, add_zero]

end QuantumProver.ConditionalEntropy.MixtureEntropy

namespace QuantumProver.ConditionalEntropy.MixtureEntropy

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem matrix_subadditivity {R : Matrix (A × B) (A × B) ℂ}
    (hR : IsDensity R) :
    entropyBits R ≤ entropyBits (QuantumProver.QuantumEntropy.partialTrace_right R) +
      entropyBits (QuantumProver.QuantumEntropy.partialTrace_left R) := by
  have hT : IsDensity (singletonMiddle R) := isDensity_reindex _ hR
  have hssa := QuantumProver.QuantumEntropy.strongSubadditivity hT
  change entropyBits (QuantumProver.QuantumEntropy.marginalB (singletonMiddle R)) +
      entropyBits (singletonMiddle R) ≤
    entropyBits (QuantumProver.QuantumEntropy.marginalAB (singletonMiddle R)) +
      entropyBits (QuantumProver.QuantumEntropy.marginalBC (singletonMiddle R)) at hssa
  have hmid : entropyBits (QuantumProver.QuantumEntropy.marginalB (singletonMiddle R)) = 0 :=
    entropyBits_unit_of_trace_one (QuantumProver.QuantumEntropy.marginalB_isDensity hT).2
  have hEnt : entropyBits (singletonMiddle R) = entropyBits R := by
    change entropyBits (Matrix.reindex (singletonMiddleEquiv A B)
      (singletonMiddleEquiv A B) R) = entropyBits R
    exact entropyBits_reindex _ hR.1.1
  rw [hmid, hEnt, singletonMiddle_marginalAB, singletonMiddle_marginalBC,
    entropyBits_reindex _ (QuantumProver.QuantumEntropy.partialTraceRight_posSemidef hR.1).1,
    entropyBits_reindex _ (QuantumProver.QuantumEntropy.partialTraceLeft_posSemidef hR.1).1]
    at hssa
  simpa only [zero_add] using hssa

end QuantumProver.ConditionalEntropy.MixtureEntropy

namespace QuantumProver.ConditionalEntropy

open MixtureEntropy

variable {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]
  [DecidableEq I] [DecidableEq A] [DecidableEq B]

theorem entropyBits_subadditivity {R : Matrix (A × B) (A × B) ℂ}
    (hR : IsDensity R) :
    entropyBits R ≤ entropyBits (QuantumProver.QuantumEntropy.partialTrace_right R) +
      entropyBits (QuantumProver.QuantumEntropy.partialTrace_left R) :=
  matrix_subadditivity hR

theorem conditionalEntropy_mix_lower {R S : Matrix (A × B) (A × B) ℂ}
    (hR : IsDensity R) (hS : IsDensity S) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1-p) * conditionalEntropyBits R + p * conditionalEntropyBits S ≤
      conditionalEntropyBits (mix p R S) := by
  have hT := conditionalFlagged_isDensity hp0 hp1 hR hS
  have hssa := QuantumProver.QuantumEntropy.strongSubadditivity hT
  change entropyBits (QuantumProver.QuantumEntropy.marginalB (conditionalFlagged p R S)) +
      entropyBits (conditionalFlagged p R S) ≤
    entropyBits (QuantumProver.QuantumEntropy.marginalAB (conditionalFlagged p R S)) +
      entropyBits (QuantumProver.QuantumEntropy.marginalBC (conditionalFlagged p R S)) at hssa
  rw [conditionalFlagged_marginalAB, conditionalFlagged_marginalB,
    conditionalFlagged_marginalBC, entropyBits_conditionalFlagged hp0 hp1 hR hS,
    entropyBits_binaryFlagged hp0 hp1
      (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR)
      (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hS),
    ← partialTraceLeft_mix] at hssa
  simp only [conditionalEntropyBits, binaryEntropy] at *
  nlinarith only [hssa]

theorem entropyBits_mix_lower {R S : Matrix I I ℂ}
    (hR : IsDensity R) (hS : IsDensity S) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1-p) * entropyBits R + p * entropyBits S ≤ entropyBits (mix p R S) := by
  have hF := binaryFlagged_isDensity hp0 hp1 hR hS
  have hsub := matrix_subadditivity hF
  change _ ≤ entropyBits ((fun i j => ∑ b : Bool, binaryFlagged p R S (i,b) (j,b))) +
    entropyBits ((fun b b' => ∑ i, binaryFlagged p R S (i,b) (i,b'))) at hsub
  rw [binaryFlagged_quantumMarginal, binaryFlagged_flagMarginal hR.2 hS.2 p,
    entropyBits_binaryDiagonal hp0 hp1, entropyBits_binaryFlagged hp0 hp1 hR hS] at hsub
  change _ ≤ entropyBits ((1-p) • R + p • S)
  change _ + _ ≤ _ + binaryEntropy p at hsub
  linarith only [hsub]

theorem entropyBits_mix_upper {R S : Matrix I I ℂ}
    (hR : IsDensity R) (hS : IsDensity S) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entropyBits (mix p R S) ≤ (1-p) * entropyBits R + p * entropyBits S + binaryEntropy p := by
  have h0 := firstFlagged_isDensity (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 1) hR hR
  have h1 := firstFlagged_isDensity (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (1 : ℝ) ≤ 1) hS hS
  have e0 : conditionalEntropyBits (firstFlagged 0 R R) = 0 := by
    rw [conditionalEntropy_firstFlagged (by norm_num) (by norm_num) hR hR]
    simp
  have e1 : conditionalEntropyBits (firstFlagged 1 S S) = 0 := by
    rw [conditionalEntropy_firstFlagged (by norm_num) (by norm_num) hS hS]
    simp
  have hconc := conditionalEntropy_mix_lower h0 h1 hp0 hp1
  rw [e0, e1, firstFlagged_endpoint_mix,
    conditionalEntropy_firstFlagged hp0 hp1 hR hS] at hconc
  linarith only [hconc]

theorem conditionalEntropy_mix_upper {R S : Matrix (A × B) (A × B) ℂ}
    (hR : IsDensity R) (hS : IsDensity S) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    conditionalEntropyBits (mix p R S) ≤
      (1-p) * conditionalEntropyBits R + p * conditionalEntropyBits S + binaryEntropy p := by
  have hupper := entropyBits_mix_upper hR hS hp0 hp1
  have hlower := entropyBits_mix_lower
    (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR)
    (QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hS) hp0 hp1
  rw [← partialTraceLeft_mix] at hlower
  simp only [conditionalEntropyBits] at *
  nlinarith only [hupper, hlower]

end QuantumProver.ConditionalEntropy

namespace QuantumProver.ConditionalEntropy

variable {I H A B : Type*} [Fintype I] [Fintype H] [Fintype A] [Fintype B]
  [DecidableEq I] [DecidableEq A] [DecidableEq B]

theorem convex_isDensity : Convex ℝ {R : Matrix I I ℂ | IsDensity R} := by
  intro R hR S hS a b ha hb hab
  change IsDensity (a • R + b • S)
  have haeq : 1 - b = a := by linarith only [hab]
  have hb1 : b ≤ 1 := by linarith only [ha, hab]
  simpa only [mix, haeq] using mix_isDensity hR hS hb hb1

theorem entropyBits_concaveOn :
    ConcaveOn ℝ {R : Matrix I I ℂ | IsDensity R} entropyBits := by
  refine ⟨convex_isDensity, ?_⟩
  intro R hR S hS a b ha hb hab
  have haeq : 1 - b = a := by linarith only [hab]
  have hb1 : b ≤ 1 := by linarith only [ha, hab]
  simpa only [mix, haeq, smul_eq_mul] using entropyBits_mix_lower hR hS hb hb1

theorem weightedSum_isDensity (w : H → ℝ) (R : H → Matrix I I ℂ)
    (hw : ∀ h, 0 ≤ w h) (hs : ∑ h, w h = 1) (hR : ∀ h, IsDensity (R h)) :
    IsDensity (∑ h, w h • R h) :=
  convex_isDensity.sum_mem (fun h _ => hw h) hs (fun h _ => hR h)

theorem entropyBits_weightedSum_lower (w : H → ℝ) (R : H → Matrix I I ℂ)
    (hw : ∀ h, 0 ≤ w h) (hs : ∑ h, w h = 1) (hR : ∀ h, IsDensity (R h)) :
    ∑ h, w h * entropyBits (R h) ≤ entropyBits (∑ h, w h • R h) := by
  simpa only [smul_eq_mul] using
    entropyBits_concaveOn.le_map_sum (fun h _ => hw h) hs (fun h _ => hR h)

theorem conditionalEntropy_concaveOn :
    ConcaveOn ℝ {R : Matrix (A × B) (A × B) ℂ | IsDensity R}
      conditionalEntropyBits := by
  refine ⟨convex_isDensity, ?_⟩
  intro R hR S hS a b ha hb hab
  have haeq : 1 - b = a := by linarith only [hab]
  have hb1 : b ≤ 1 := by linarith only [ha, hab]
  simpa only [mix, haeq, smul_eq_mul] using conditionalEntropy_mix_lower hR hS hb hb1

theorem conditionalEntropy_weightedSum_lower (w : H → ℝ)
    (R : H → Matrix (A × B) (A × B) ℂ)
    (hw : ∀ h, 0 ≤ w h) (hs : ∑ h, w h = 1) (hR : ∀ h, IsDensity (R h)) :
    ∑ h, w h * conditionalEntropyBits (R h) ≤
      conditionalEntropyBits (∑ h, w h • R h) := by
  simpa only [smul_eq_mul] using
    conditionalEntropy_concaveOn.le_map_sum (fun h _ => hw h) hs (fun h _ => hR h)

end QuantumProver.ConditionalEntropy

namespace QuantumProver.ConditionalEntropy

open ConditionalRange

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem conditionalEntropy_bounds {R : Matrix (A × B) (A × B) ℂ}
    (hR : IsDensity R) :
    -logDimA A ≤ conditionalEntropyBits R ∧ conditionalEntropyBits R ≤ logDimA A := by
  have hA := QuantumProver.QuantumEntropy.partialTraceRight_isDensity hR
  have hB := QuantumProver.QuantumEntropy.partialTraceLeft_isDensity hR
  have hdim := (ConditionalRange.entropyBits_bounds hA).2
  have hsub := entropyBits_subadditivity hR
  let V := CFC.sqrt R
  have hVV : V * Vᴴ = R := (sqrt_grams hR.1).1
  have hC : IsDensity (complementaryState V) := complementaryState_sqrt_isDensity hR
  have hComplement := entropyBits_subadditivity hC
  have hMarginalB :
      ((fun b b' => ∑ a, (V * Vᴴ) (a,b) (a,b')) : Matrix B B ℂ) =
        QuantumProver.QuantumEntropy.partialTrace_left R := by
    ext b b'
    change (∑ a, (V * Vᴴ) (a,b) (a,b')) = ∑ a, R (a,b) (a,b')
    rw [hVV]
  have hBherm : Matrix.IsHermitian
      ((fun b b' => ∑ a, (V * Vᴴ) (a,b) (a,b')) : Matrix B B ℂ) := by
    rw [hMarginalB]
    exact hB.1.1
  have hCompEntropy : entropyBits (complementaryState V) =
      entropyBits (QuantumProver.QuantumEntropy.partialTrace_left R) := by
    change QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
        (complementaryState V) =
      QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits
        (QuantumProver.QuantumEntropy.partialTrace_left R)
    exact (entropyBits_complementaryState V hBherm).trans
      (congrArg QuantumProver.SuperchannelDiscrimination.FlaggedStates.entropyBits hMarginalB)
  have hCompA : QuantumProver.QuantumEntropy.partialTrace_right (complementaryState V) =
      QuantumProver.QuantumEntropy.partialTrace_right R :=
    complementaryState_sqrt_marginalA hR.1
  have hCompC : QuantumProver.QuantumEntropy.partialTrace_left (complementaryState V) = Rᵀ :=
    complementaryState_sqrt_marginalC hR.1
  have hTranspose : entropyBits Rᵀ = entropyBits R := entropyBits_transpose hR.1.1
  rw [hCompEntropy, hCompA, hCompC, hTranspose] at hComplement
  change entropyBits (QuantumProver.QuantumEntropy.partialTrace_right R) ≤ logDimA A at hdim
  simp only [conditionalEntropyBits]
  constructor <;> linarith only [hdim, hsub, hComplement]

theorem abs_conditionalEntropy_le_logDim {R : Matrix (A × B) (A × B) ℂ}
    (hR : IsDensity R) : |conditionalEntropyBits R| ≤ logDimA A :=
  abs_le.mpr (conditionalEntropy_bounds hR)

theorem conditionalEntropy_difference_le_two_logDim
    {R S : Matrix (A × B) (A × B) ℂ} (hR : IsDensity R) (hS : IsDensity S) :
    conditionalEntropyBits R - conditionalEntropyBits S ≤ 2 * logDimA A := by
  have hRbound := (conditionalEntropy_bounds hR).2
  have hSbound := (conditionalEntropy_bounds hS).1
  linarith only [hRbound, hSbound]

end QuantumProver.ConditionalEntropy
