import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.EffectPerturbation
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.SuperchannelDiscrimination.DiamondControl

variable {n m I O C D R : Type*}
  [Fintype n] [Fintype m] [Fintype I] [Fintype O]
  [Fintype C] [Fintype D] [Fintype R]
  [DecidableEq n] [DecidableEq m] [DecidableEq I] [DecidableEq O]
  [DecidableEq C] [DecidableEq D] [DecidableEq R]

def nuclearNorm (X : Matrix n n ℂ) : ℝ := (CFC.sqrt (Xᴴ * X)).trace.re

theorem nuclearNorm_eq_traceNorm (X : Matrix n n ℂ) :
    nuclearNorm X = EffectPerturbation.traceNorm X := rfl

theorem nuclearNorm_nonneg (X : Matrix n n ℂ) : 0 ≤ nuclearNorm X :=
  EffectPerturbation.traceNorm_nonneg X

theorem nuclearNorm_of_posSemidef {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    nuclearNorm X = X.trace.re :=
  EffectPerturbation.traceNorm_of_posSemidef hX

theorem nuclearNorm_of_density {X : Matrix n n ℂ} (hX : FlaggedStates.IsDensity X) :
    nuclearNorm X = 1 := by
  rw [nuclearNorm_of_posSemidef hX.1, hX.2]
  rfl

theorem nuclearNorm_zero : nuclearNorm (0 : Matrix n n ℂ) = 0 := by
  simp [nuclearNorm]

theorem nuclearNorm_neg (X : Matrix n n ℂ) : nuclearNorm (-X) = nuclearNorm X := by
  simp only [nuclearNorm_eq_traceNorm, EffectPerturbation.traceNorm, CFC.abs_neg]

theorem nuclearNorm_smul (z : ℂ) (X : Matrix n n ℂ) :
    nuclearNorm (z • X) = ‖z‖ * nuclearNorm X := by
  simp only [nuclearNorm_eq_traceNorm, EffectPerturbation.traceNorm, CFC.abs_smul,
    Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

theorem posSemidef_trace_re_eq_zero_iff {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    X.trace.re = 0 ↔ X = 0 := by
  constructor
  · intro ht
    have htc : X.trace = 0 := by
      apply Complex.ext
      · simpa using ht
      · simpa using (Complex.nonneg_iff.mp hX.trace_nonneg).2.symm
    have hs : (CFC.sqrt X)ᴴ * CFC.sqrt X = X := by
      rw [← Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg X).star_eq,
        CFC.sqrt_mul_sqrt_self X hX.nonneg]
    have hs0 : CFC.sqrt X = 0 :=
      Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ((congrArg Matrix.trace hs).trans htc)
    rw [← hs, hs0]
    simp
  · intro h
    simp [h]

theorem nuclearNorm_eq_zero_iff (X : Matrix n n ℂ) : nuclearNorm X = 0 ↔ X = 0 := by
  rw [nuclearNorm_eq_traceNorm]
  change (CFC.abs X).trace.re = 0 ↔ X = 0
  rw [posSemidef_trace_re_eq_zero_iff (CFC.abs_nonneg X).posSemidef,
    CFC.abs_eq_zero_iff]

theorem nuclearNorm_pos_iff (X : Matrix n n ℂ) : 0 < nuclearNorm X ↔ X ≠ 0 := by
  rw [lt_iff_le_and_ne]
  simp only [nuclearNorm_nonneg X, true_and, ne_eq]
  rw [eq_comm, nuclearNorm_eq_zero_iff]

theorem abs_submatrix_equiv (e : m ≃ n) (X : Matrix n n ℂ) :
    CFC.abs (X.submatrix e e) = (CFC.abs X).submatrix e e := by
  have hmul :
      (CFC.abs X).submatrix e e * (CFC.abs X).submatrix e e =
        (X.submatrix e e)ᴴ * X.submatrix e e := by
    rw [Matrix.submatrix_mul_equiv, CFC.abs_mul_abs, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [CFC.abs, Matrix.star_eq_conjTranspose]
  exact CFC.sqrt_unique hmul ((CFC.abs_nonneg X).posSemidef.submatrix e).nonneg

theorem nuclearNorm_submatrix_equiv (e : m ≃ n) (X : Matrix n n ℂ) :
    nuclearNorm (X.submatrix e e) = nuclearNorm X := by
  simp only [nuclearNorm_eq_traceNorm, EffectPerturbation.traceNorm, abs_submatrix_equiv]
  exact congrArg Complex.re (e.sum_comp (fun i => (CFC.abs X) i i))

def amplifyMap (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] :
    Matrix (I × R) (I × R) ℂ →ₗ[ℂ] Matrix (O × R) (O × R) ℂ where
  toFun X := fun x y => Δ (fun i j => X (i, x.2) (j, y.2)) x.1 y.1
  map_add' X Y := by
    ext x y
    exact congrArg (fun M : Matrix O O ℂ => M x.1 y.1)
      (Δ.map_add (fun i j => X (i, x.2) (j, y.2))
        (fun i j => Y (i, x.2) (j, y.2)))
  map_smul' z X := by
    ext x y
    exact congrArg (fun M : Matrix O O ℂ => M x.1 y.1)
      (Δ.map_smul z (fun i j => X (i, x.2) (j, y.2)))

omit [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O] in
theorem amplifyMap_sub (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] :
    amplifyMap (Φ - Ψ) R = amplifyMap Φ R - amplifyMap Ψ R := by
  ext X x y
  rfl

omit [Fintype I] [Fintype O] [Fintype D]
  [DecidableEq I] [DecidableEq O] [DecidableEq D] in
theorem amplifyMap_comp (Φ : Matrix O O ℂ →ₗ[ℂ] Matrix D D ℂ)
    (Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (R : Type*) [Fintype R] :
    amplifyMap (Φ.comp Ψ) R = (amplifyMap Φ R).comp (amplifyMap Ψ R) := by
  ext X x y
  rfl

omit [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O] in
theorem amplifyMap_neg (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] : amplifyMap (-Δ) R = -amplifyMap Δ R := by
  ext X x y
  rfl

omit [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O] in

theorem amplifyMap_assoc
    (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (S R : Type*) [Fintype S] [Fintype R]
    (X : Matrix ((I × S) × R) ((I × S) × R) ℂ) :
    amplifyMap Δ (S × R)
      (X.submatrix (Equiv.prodAssoc I S R).symm (Equiv.prodAssoc I S R).symm) =
      (amplifyMap (amplifyMap Δ S) R X).submatrix
        (Equiv.prodAssoc O S R).symm (Equiv.prodAssoc O S R).symm := by
  ext x y
  rfl

omit [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O] [DecidableEq R] in
theorem amplifyMap_submatrix_reference
    (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    {S : Type*} [Fintype S] (e : S ≃ R)
    (X : Matrix (I × R) (I × R) ℂ) :
    amplifyMap Δ S
      (X.submatrix (Equiv.prodCongr (Equiv.refl I) e)
        (Equiv.prodCongr (Equiv.refl I) e)) =
      (amplifyMap Δ R X).submatrix (Equiv.prodCongr (Equiv.refl O) e)
        (Equiv.prodCongr (Equiv.refl O) e) := by
  ext x y
  rfl

def diamondBudget (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : EReal :=
  ⨆ (k : ℕ) (X : Matrix (I × Fin k) (I × Fin k) ℂ)
    (_hX : nuclearNorm X ≤ 1), (nuclearNorm (amplifyMap Δ (Fin k) X) : EReal)

theorem unitBall_output_le_diamondBudget
    (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (k : ℕ)
    {X : Matrix (I × Fin k) (I × Fin k) ℂ} (hX : nuclearNorm X ≤ 1) :
    (nuclearNorm (amplifyMap Δ (Fin k) X) : EReal) ≤ diamondBudget Δ := by
  exact le_iSup_of_le k (le_iSup_of_le X (le_iSup_of_le hX le_rfl))

theorem diamondBudget_le_iff
    (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (δ : EReal) :
    diamondBudget Δ ≤ δ ↔
      ∀ (k : ℕ) (X : Matrix (I × Fin k) (I × Fin k) ℂ),
        nuclearNorm X ≤ 1 → (nuclearNorm (amplifyMap Δ (Fin k) X) : EReal) ≤ δ := by
  simp only [diamondBudget, iSup_le_iff]

theorem diamondBudget_nonneg
    (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : 0 ≤ diamondBudget Δ := by
  have hz : nuclearNorm (0 : Matrix (I × Fin 0) (I × Fin 0) ℂ) ≤ 1 := by
    simp [nuclearNorm]
  have hout := unitBall_output_le_diamondBudget Δ 0 hz
  simpa [amplifyMap, nuclearNorm] using hout

theorem diamondBudget_zero :
    diamondBudget (0 : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) = 0 := by
  apply le_antisymm _ (diamondBudget_nonneg _)
  rw [diamondBudget_le_iff]
  intro k X hX
  change (nuclearNorm (0 : Matrix (O × Fin k) (O × Fin k) ℂ) : EReal) ≤ 0
  simp only [nuclearNorm_zero, EReal.coe_zero, le_refl]

theorem diamondBudget_neg
    (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : diamondBudget (-Δ) = diamondBudget Δ := by
  simp only [diamondBudget, amplifyMap_neg, LinearMap.neg_apply, nuclearNorm_neg]

theorem diamondBudget_difference_symm
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    diamondBudget (Φ - Ψ) = diamondBudget (Ψ - Φ) := by
  have he : Ψ - Φ = -(Φ - Ψ) := by abel
  rw [he, diamondBudget_neg]

theorem unitBall_output_le_diamondBudget_allReferences
    (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix (I × R) (I × R) ℂ} (hX : nuclearNorm X ≤ 1) :
    (nuclearNorm (amplifyMap Δ R X) : EReal) ≤ diamondBudget Δ := by
  let e : Fin (Fintype.card R) ≃ R := (Fintype.equivFin R).symm
  let ei := Equiv.prodCongr (Equiv.refl I) e
  let eo := Equiv.prodCongr (Equiv.refl O) e
  have hXi : nuclearNorm (X.submatrix ei ei) ≤ 1 := by
    rw [nuclearNorm_submatrix_equiv ei]
    exact hX
  have h := unitBall_output_le_diamondBudget Δ (Fintype.card R) hXi
  rw [amplifyMap_submatrix_reference Δ e, nuclearNorm_submatrix_equiv eo] at h
  exact h

theorem diamondBudget_amplifyMap_le
    (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (S : Type*) [Fintype S] [DecidableEq S] :
    diamondBudget (amplifyMap Δ S) ≤ diamondBudget Δ := by
  rw [diamondBudget_le_iff]
  intro k X hX
  let ei := (Equiv.prodAssoc I S (Fin k)).symm
  let eo := (Equiv.prodAssoc O S (Fin k)).symm
  have hXi : nuclearNorm (X.submatrix ei ei) ≤ 1 := by
    rw [nuclearNorm_submatrix_equiv ei]
    exact hX
  have h := unitBall_output_le_diamondBudget_allReferences Δ (S × Fin k) hXi
  rw [amplifyMap_assoc Δ S (Fin k), nuclearNorm_submatrix_equiv eo] at h
  exact h

theorem diamondBudget_amplify_difference_le
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (S : Type*) [Fintype S] [DecidableEq S] {δ : EReal}
    (hδ : diamondBudget (Φ - Ψ) ≤ δ) :
    diamondBudget (amplifyMap Φ S - amplifyMap Ψ S) ≤ δ := by
  rw [← amplifyMap_sub]
  exact (diamondBudget_amplifyMap_le (Φ - Ψ) S).trans hδ

theorem unitBall_output_le_of_diamondBudget
    (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] {δ : ℝ}
    (hδ : diamondBudget Δ ≤ (δ : EReal))
    {X : Matrix (I × R) (I × R) ℂ} (hX : nuclearNorm X ≤ 1) :
    nuclearNorm (amplifyMap Δ R X) ≤ δ := by
  exact EReal.coe_le_coe_iff.mp
    ((unitBall_output_le_diamondBudget_allReferences Δ R hX).trans hδ)

theorem bound_nonneg_of_diamondBudget
    (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) {δ : ℝ}
    (hδ : diamondBudget Δ ≤ (δ : EReal)) : 0 ≤ δ := by
  exact EReal.coe_le_coe_iff.mp ((diamondBudget_nonneg Δ).trans hδ)

theorem output_le_scaled_of_diamondBudget
    (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] {δ : ℝ}
    (hδ : diamondBudget Δ ≤ (δ : EReal)) (X : Matrix (I × R) (I × R) ℂ) :
    nuclearNorm (amplifyMap Δ R X) ≤ δ * nuclearNorm X := by
  by_cases hX : X = 0
  · simp [hX, nuclearNorm_zero]
  · have hN : 0 < nuclearNorm X := (nuclearNorm_pos_iff X).mpr hX
    let z : ℂ := (nuclearNorm X)⁻¹
    have hz : ‖z‖ = (nuclearNorm X)⁻¹ := by
      simp [z, Complex.norm_real, abs_of_pos hN, norm_inv]
    have hunit : nuclearNorm (z • X) ≤ 1 := by
      rw [nuclearNorm_smul, hz, inv_mul_cancel₀ (ne_of_gt hN)]
    have hb := unitBall_output_le_of_diamondBudget Δ R hδ hunit
    rw [map_smul, nuclearNorm_smul, hz] at hb
    have hmul := mul_le_mul_of_nonneg_left hb (le_of_lt hN)
    calc
      nuclearNorm (amplifyMap Δ R X) =
          nuclearNorm X * ((nuclearNorm X)⁻¹ * nuclearNorm (amplifyMap Δ R X)) := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hN), one_mul]
      _ ≤ nuclearNorm X * δ := hmul
      _ = δ * nuclearNorm X := mul_comm _ _

theorem density_output_le_of_diamondBudget
    (Δ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] {δ : ℝ}
    (hδ : diamondBudget Δ ≤ (δ : EReal))
    {ρ : Matrix (I × R) (I × R) ℂ} (hρ : FlaggedStates.IsDensity ρ) :
    nuclearNorm (amplifyMap Δ R ρ) ≤ δ := by
  apply unitBall_output_le_of_diamondBudget Δ R hδ
  exact le_of_eq (nuclearNorm_of_density hρ)

def CompletelyPositive (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Prop :=
  ∀ (k : ℕ) (X : Matrix (I × Fin k) (I × Fin k) ℂ),
    X.PosSemidef → (amplifyMap Φ (Fin k) X).PosSemidef

omit [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O] in

theorem completelyPositive_allReferences
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : CompletelyPositive Φ)
    (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix (I × R) (I × R) ℂ} (hX : X.PosSemidef) :
    (amplifyMap Φ R X).PosSemidef := by
  let e : Fin (Fintype.card R) ≃ R := (Fintype.equivFin R).symm
  let ei := Equiv.prodCongr (Equiv.refl I) e
  let eo := Equiv.prodCongr (Equiv.refl O) e
  have h := hΦ (Fintype.card R) (X.submatrix ei ei) (hX.submatrix ei)
  rw [amplifyMap_submatrix_reference Φ e] at h
  exact (Matrix.posSemidef_submatrix_equiv eo).mp h

omit [Fintype m] [DecidableEq m] in

theorem positive_map_isHermitian
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (hpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    {X : Matrix n n ℂ} (hX : X.IsHermitian) : (Φ X).IsHermitian := by
  have he : Φ X = Φ X⁺ - Φ X⁻ := by
    rw [← map_sub, CFC.posPart_sub_negPart X hX.isSelfAdjoint]
  rw [he]
  exact (hpos X⁺ (CFC.posPart_nonneg X).posSemidef).isHermitian.sub
    (hpos X⁻ (CFC.negPart_nonneg X).posSemidef).isHermitian

theorem nuclearNorm_contracts_positive_tracePreserving
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (hpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (htrace : ∀ X, (Φ X).trace = X.trace)
    {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    nuclearNorm (Φ X) ≤ nuclearNorm X :=
  EffectPerturbation.traceNorm_contracts_positive_tracePreserving Φ hpos htrace hX

theorem density_difference_output_le_of_diamondBudget
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] [DecidableEq R] {δ : ℝ}
    (hδ : diamondBudget (Φ - Ψ) ≤ (δ : EReal))
    {ρ : Matrix (I × R) (I × R) ℂ} (hρ : FlaggedStates.IsDensity ρ) :
    EffectPerturbation.traceNorm (amplifyMap Φ R ρ - amplifyMap Ψ R ρ) ≤ δ := by
  have h := density_output_le_of_diamondBudget (Φ - Ψ) R hδ hρ
  rw [amplifyMap_sub, LinearMap.sub_apply, nuclearNorm_eq_traceNorm] at h
  exact h

theorem common_wrapper_output_error_le
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (pre : Matrix C C ℂ →ₗ[ℂ] Matrix (I × R) (I × R) ℂ)
    (post : Matrix (O × R) (O × R) ℂ →ₗ[ℂ] Matrix D D ℂ)
    (hΦ : CompletelyPositive Φ) (hΨ : CompletelyPositive Ψ)
    (hprepos : ∀ X, X.PosSemidef → (pre X).PosSemidef)
    (hpretrace : ∀ X, (pre X).trace = X.trace)
    (hpostpos : ∀ X, X.PosSemidef → (post X).PosSemidef)
    (hposttrace : ∀ X, (post X).trace = X.trace) {δ : ℝ}
    (hδ : diamondBudget (Φ - Ψ) ≤ (δ : EReal))
    {ρ : Matrix C C ℂ} (hρ : FlaggedStates.IsDensity ρ) :
    EffectPerturbation.traceNorm
      (post (amplifyMap Φ R (pre ρ)) - post (amplifyMap Ψ R (pre ρ))) ≤ δ := by
  have hpreρ := EffectPerturbation.isDensity_map_positive_tracePreserving
    pre hprepos hpretrace hρ
  have hA := completelyPositive_allReferences hΦ R hpreρ.1
  have hB := completelyPositive_allReferences hΨ R hpreρ.1
  have hc := EffectPerturbation.traceNorm_difference_contracts
    post hpostpos hposttrace hA.isHermitian hB.isHermitian
  exact hc.trans (density_difference_output_le_of_diamondBudget Φ Ψ R hδ hpreρ)

omit [DecidableEq I] [DecidableEq O] in

theorem amplifyMap_tracePreserving
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hΦ : ∀ X, (Φ X).trace = X.trace)
    (R : Type*) [Fintype R] (X : Matrix (I × R) (I × R) ℂ) :
    (amplifyMap Φ R X).trace = X.trace := by
  calc
    (amplifyMap Φ R X).trace =
        ∑ r : R, (Φ (fun i j => X (i, r) (j, r))).trace := by
      simp only [amplifyMap, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ = ∑ r : R, Matrix.trace ((fun i j => X (i, r) (j, r)) : Matrix I I ℂ) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hΦ _
    _ = X.trace := by
      simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
      exact Finset.sum_comm

omit [DecidableEq I] [DecidableEq O] in

theorem amplifyMap_traceNonincreasing
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hΦ : ∀ X, X.PosSemidef → (Φ X).trace.re ≤ X.trace.re)
    (R : Type*) [Fintype R] {X : Matrix (I × R) (I × R) ℂ}
    (hX : X.PosSemidef) : (amplifyMap Φ R X).trace.re ≤ X.trace.re := by
  calc
    (amplifyMap Φ R X).trace.re =
        ∑ r : R, (Φ (fun i j => X (i, r) (j, r))).trace.re := by
      simp only [amplifyMap, Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
        Complex.re_sum]
      exact Finset.sum_comm
    _ ≤ ∑ r : R, (Matrix.trace ((fun i j => X (i, r) (j, r)) : Matrix I I ℂ)).re := by
      apply Finset.sum_le_sum
      intro r hr
      exact hΦ _ (hX.submatrix (fun i => (i, r)))
    _ = X.trace.re := by
      simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Complex.re_sum]
      exact Finset.sum_comm

def wrappedMap (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (pre : Matrix C C ℂ →ₗ[ℂ] Matrix (I × R) (I × R) ℂ)
    (post : Matrix (O × R) (O × R) ℂ →ₗ[ℂ] Matrix D D ℂ) :
    Matrix C C ℂ →ₗ[ℂ] Matrix D D ℂ :=
  post.comp ((amplifyMap Φ R).comp pre)

omit [Fintype I] [Fintype O] [Fintype C] [Fintype D]
  [DecidableEq I] [DecidableEq O] [DecidableEq C] [DecidableEq D] [DecidableEq R] in
theorem wrappedMap_apply (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (pre : Matrix C C ℂ →ₗ[ℂ] Matrix (I × R) (I × R) ℂ)
    (post : Matrix (O × R) (O × R) ℂ →ₗ[ℂ] Matrix D D ℂ) (X : Matrix C C ℂ) :
    wrappedMap Φ pre post X = post (amplifyMap Φ R (pre X)) := rfl

omit [Fintype I] [Fintype O] [Fintype C] [Fintype D]
  [DecidableEq I] [DecidableEq O] [DecidableEq C] [DecidableEq D] in
theorem wrappedMap_positive
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : CompletelyPositive Φ)
    (pre : Matrix C C ℂ →ₗ[ℂ] Matrix (I × R) (I × R) ℂ)
    (post : Matrix (O × R) (O × R) ℂ →ₗ[ℂ] Matrix D D ℂ)
    (hpre : ∀ X, X.PosSemidef → (pre X).PosSemidef)
    (hpost : ∀ X, X.PosSemidef → (post X).PosSemidef)
    {X : Matrix C C ℂ} (hX : X.PosSemidef) :
    (wrappedMap Φ pre post X).PosSemidef :=
  hpost _ (completelyPositive_allReferences hΦ R (hpre X hX))

omit [DecidableEq I] [DecidableEq O] [DecidableEq C] [DecidableEq D] [DecidableEq R] in
theorem wrappedMap_tracePreserving
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (pre : Matrix C C ℂ →ₗ[ℂ] Matrix (I × R) (I × R) ℂ)
    (post : Matrix (O × R) (O × R) ℂ →ₗ[ℂ] Matrix D D ℂ)
    (hΦ : ∀ X, (Φ X).trace = X.trace)
    (hpre : ∀ X, (pre X).trace = X.trace)
    (hpost : ∀ X, (post X).trace = X.trace) (X : Matrix C C ℂ) :
    (wrappedMap Φ pre post X).trace = X.trace := by
  rw [wrappedMap_apply, hpost, amplifyMap_tracePreserving Φ hΦ R, hpre]

omit [DecidableEq I] [DecidableEq O] [DecidableEq C] [DecidableEq D] in
theorem wrappedMap_density
    {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ} (hΦ : CompletelyPositive Φ)
    (pre : Matrix C C ℂ →ₗ[ℂ] Matrix (I × R) (I × R) ℂ)
    (post : Matrix (O × R) (O × R) ℂ →ₗ[ℂ] Matrix D D ℂ)
    (hprepos : ∀ X, X.PosSemidef → (pre X).PosSemidef)
    (hpretrace : ∀ X, (pre X).trace = X.trace)
    (hpostpos : ∀ X, X.PosSemidef → (post X).PosSemidef)
    (hposttrace : ∀ X, (post X).trace = X.trace)
    (hΦtrace : ∀ X, (Φ X).trace = X.trace)
    {ρ : Matrix C C ℂ} (hρ : FlaggedStates.IsDensity ρ) :
    FlaggedStates.IsDensity (wrappedMap Φ pre post ρ) :=
  ⟨wrappedMap_positive hΦ pre post hprepos hpostpos hρ.1,
    (wrappedMap_tracePreserving Φ pre post hΦtrace hpretrace hposttrace ρ).trans hρ.2⟩

theorem hermitian_abs_trace_le_nuclearNorm {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    |X.trace.re| ≤ nuclearNorm X := by
  have hid : FlaggedStates.IsEffect (1 : Matrix n n ℂ) :=
    ⟨Matrix.PosSemidef.one, by simpa using (Matrix.PosSemidef.zero (n := n) (R := ℂ))⟩
  simpa [EffectPerturbation.effectValue, nuclearNorm_eq_traceNorm] using
    (EffectPerturbation.effectValue_abs_le_traceNorm hid hX)

theorem density_success_trace_ge_of_diamondBudget
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hΦ : CompletelyPositive Φ) (hΨ : CompletelyPositive Ψ)
    (hΨtrace : ∀ X, (Ψ X).trace = X.trace)
    (R : Type*) [Fintype R] [DecidableEq R] {δ : ℝ}
    (hδ : diamondBudget (Φ - Ψ) ≤ (δ : EReal))
    {ρ : Matrix (I × R) (I × R) ℂ} (hρ : FlaggedStates.IsDensity ρ) :
    1 - δ ≤ (amplifyMap Φ R ρ).trace.re := by
  have hA := completelyPositive_allReferences hΦ R hρ.1
  have hB := completelyPositive_allReferences hΨ R hρ.1
  have hb := hermitian_abs_trace_le_nuclearNorm (hA.isHermitian.sub hB.isHermitian)
  have hd := density_difference_output_le_of_diamondBudget Φ Ψ R hδ hρ
  have ht : (amplifyMap Ψ R ρ).trace = 1 :=
    (amplifyMap_tracePreserving Ψ hΨtrace R ρ).trans hρ.2
  rw [Matrix.trace_sub, Complex.sub_re, ht] at hb
  rw [nuclearNorm_eq_traceNorm] at hb
  have hh := (abs_le.mp (hb.trans hd)).1
  norm_num at hh
  linarith

theorem wrapped_success_acceptance_lower_bound
    {k : Type*} [Fintype k] [DecidableEq k]
    (Φ Ψ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (pre : Matrix C C ℂ →ₗ[ℂ] Matrix (I × R) (I × R) ℂ)
    (post : Matrix (O × R) (O × R) ℂ →ₗ[ℂ] Matrix D D ℂ)
    (hΦ : CompletelyPositive Φ) (hΨ : CompletelyPositive Ψ)
    (hΨtrace : ∀ X, (Ψ X).trace = X.trace)
    (hprepos : ∀ X, X.PosSemidef → (pre X).PosSemidef)
    (hpretrace : ∀ X, (pre X).trace = X.trace)
    (hpostpos : ∀ X, X.PosSemidef → (post X).PosSemidef)
    (hposttrace : ∀ X, (post X).trace = X.trace)
    {δ η : ℝ} (hδ : diamondBudget (Φ - Ψ) ≤ (δ : EReal))
    {ν ρ : Matrix C C ℂ} (hν : FlaggedStates.IsDensity ν)
    (hρ : FlaggedStates.IsDensity ρ)
    (hη : EffectPerturbation.traceNorm (ν - ρ) ≤ η)
    {E : Matrix D D ℂ} (hE : FlaggedStates.IsEffect E)
    (repair : Matrix k k ℂ) :
    FlaggedStates.acceptanceProbability (wrappedMap Ψ pre post ρ) E - δ - (1 / 2) * η ≤
      FlaggedStates.acceptanceProbability
        (FlaggedStates.flagBlock (wrappedMap Φ pre post ν) repair)
        (FlaggedStates.successfulEffect E) := by
  apply EffectPerturbation.successful_acceptance_lower_bound_of_input_and_output_errors
    (wrappedMap Ψ pre post)
    (fun X hX => wrappedMap_positive hΨ pre post hprepos hpostpos hX)
    (wrappedMap_tracePreserving Ψ pre post hΨtrace hpretrace hposttrace) repair hE
    (wrappedMap_positive hΦ pre post hprepos hpostpos hν.1).isHermitian hν hρ _ hη
  exact common_wrapper_output_error_le Φ Ψ R pre post hΦ hΨ
    hprepos hpretrace hpostpos hposttrace hδ hν

end QuantumProver.SuperchannelDiscrimination.DiamondControl

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace QuantumProver.SuperchannelDiscrimination.ChannelRegularization

open Matrix KrausCompletion CPWrappers FlaggedStates TensorEntropy
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker Topology

section TensorChannels

variable {I O J P κ ν : Type*}
  [Fintype I] [Fintype O] [Fintype J] [Fintype P]
  [Fintype κ] [Fintype ν]
  [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq P]

def tensorKraus (K : κ → Matrix O I ℂ) (L : ν → Matrix P J ℂ) :
    κ × ν → Matrix (O × P) (I × J) ℂ := fun k => K k.1 ⊗ₖ L k.2

theorem tensorKraus_gram (K : κ → Matrix O I ℂ) (L : ν → Matrix P J ℂ) :
    krausGram (tensorKraus K L) = krausGram K ⊗ₖ krausGram L := by
  simp only [krausGram, tensorKraus, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Fintype.sum_prod_type]
  ext a b
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem tensorKraus_action_product (K : κ → Matrix O I ℂ)
    (L : ν → Matrix P J ℂ) (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    krausAction (tensorKraus K L) (A ⊗ₖ B) =
      krausAction K A ⊗ₖ krausAction L B := by
  simp only [krausAction, tensorKraus, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Fintype.sum_prod_type]
  ext a b
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

def tensorChannel (Φ : FiniteCPTP I O) (Ψ : FiniteCPTP J P) :
    FiniteCPTP (I × J) (O × P) where
  map := krausMap (tensorKraus (CPTPKraus.canonicalKraus Φ.map)
    (CPTPKraus.canonicalKraus Ψ.map))
  completelyPositive r A hA := krausMap_completelyPositive _ (Fin r) hA
  tracePreserving A := by
    apply krausAction_tracePreserving
    rw [tensorKraus_gram,
      AbstractDPI.canonicalKraus_complete Φ.map Φ.completelyPositive Φ.tracePreserving,
      AbstractDPI.canonicalKraus_complete Ψ.map Ψ.completelyPositive Ψ.tracePreserving,
      Matrix.one_kronecker_one]

theorem tensorChannel_map_product (Φ : FiniteCPTP I O) (Ψ : FiniteCPTP J P)
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    (tensorChannel Φ Ψ).map (A ⊗ₖ B) = Φ.map A ⊗ₖ Ψ.map B := by
  change krausAction _ (A ⊗ₖ B) = _
  rw [tensorKraus_action_product,
    ← AbstractDPI.canonicalKraus_reconstruct Φ.map Φ.completelyPositive A,
    ← AbstractDPI.canonicalKraus_reconstruct Ψ.map Ψ.completelyPositive B]

end TensorChannels

section References

variable {I O R S : Type*} [Fintype I] [Fintype O]
  [Fintype R] [Fintype S] [DecidableEq I] [DecidableEq O]
  [DecidableEq R] [DecidableEq S]

theorem relativeEntropyBits_reindex (e : I ≃ O) {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    relativeEntropyBits (Matrix.reindex e e A) (Matrix.reindex e e B) =
      relativeEntropyBits A B := by
  have inv (X : Matrix I I ℂ) :
      (reindexChannel e.symm).map ((reindexChannel e).map X) = X := by
    ext i j
    change X (e.symm (e i)) (e.symm (e j)) = X i j
    simp only [Equiv.symm_apply_apply]
  apply le_antisymm
  · exact AbstractDPI.relativeEntropyBits_cptp_dpi (reindexChannel e) hA hB
  · have h := AbstractDPI.relativeEntropyBits_cptp_dpi (reindexChannel e.symm)
      (hA.submatrix e.symm) (hB.submatrix e.symm)
    change relativeEntropyBits
        ((reindexChannel e.symm).map ((reindexChannel e).map A))
        ((reindexChannel e.symm).map ((reindexChannel e).map B)) ≤
      relativeEntropyBits ((reindexChannel e).map A) ((reindexChannel e).map B) at h
    rw [inv, inv] at h
    change relativeEntropyBits A B ≤
      relativeEntropyBits ((reindexChannel e).map A) ((reindexChannel e).map B)
    exact h

theorem amplify_reindex_reference (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (e : R ≃ S) (A : Matrix (I × R) (I × R) ℂ) :
    amplify Φ S
        (Matrix.reindex (Equiv.prodCongr (Equiv.refl I) e)
          (Equiv.prodCongr (Equiv.refl I) e) A) =
      Matrix.reindex (Equiv.prodCongr (Equiv.refl O) e)
        (Equiv.prodCongr (Equiv.refl O) e) (amplify Φ R A) := by
  ext x y
  rfl

end References

section Stabilized

variable {I O : Type*} [Fintype I] [Fintype O]
  [DecidableEq I] [DecidableEq O]

def stabilizedRelativeEntropyBits (Φ Ψ : FiniteCPTP I O) : EReal :=
  ⨆ (r : ℕ) (ρ : Matrix (I × Fin r) (I × Fin r) ℂ) (_hρ : IsDensity ρ),
    relativeEntropyBits (amplify Φ.map (Fin r) ρ) (amplify Ψ.map (Fin r) ρ)

theorem stabilizedRelativeEntropyBits_witness_fin_le (Φ Ψ : FiniteCPTP I O)
    (r : ℕ) {ρ : Matrix (I × Fin r) (I × Fin r) ℂ} (hρ : IsDensity ρ) :
    relativeEntropyBits (amplify Φ.map (Fin r) ρ) (amplify Ψ.map (Fin r) ρ) ≤
      stabilizedRelativeEntropyBits Φ Ψ :=
  le_iSup_of_le r (le_iSup_of_le ρ (le_iSup_of_le hρ le_rfl))

theorem stabilizedRelativeEntropyBits_witness_le (Φ Ψ : FiniteCPTP I O)
    (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (I × R) (I × R) ℂ} (hρ : IsDensity ρ) :
    relativeEntropyBits (amplify Φ.map R ρ) (amplify Ψ.map R ρ) ≤
      stabilizedRelativeEntropyBits Φ Ψ := by
  let e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  let eI := Equiv.prodCongr (Equiv.refl I) e
  let eO := Equiv.prodCongr (Equiv.refl O) e
  let ρ' := Matrix.reindex eI eI ρ
  have hρ' : IsDensity ρ' := channel_density (reindexChannel eI) hρ.1 hρ.2
  have hΦρ := channel_density (amplifiedChannel Φ R) hρ.1 hρ.2
  have hΨρ := channel_density (amplifiedChannel Ψ R) hρ.1 hρ.2
  have heq :
      relativeEntropyBits (amplify Φ.map (Fin (Fintype.card R)) ρ')
          (amplify Ψ.map (Fin (Fintype.card R)) ρ') =
        relativeEntropyBits (amplify Φ.map R ρ) (amplify Ψ.map R ρ) := by
    change relativeEntropyBits
        (amplify Φ.map (Fin (Fintype.card R))
          (Matrix.reindex (Equiv.prodCongr (Equiv.refl I) e)
            (Equiv.prodCongr (Equiv.refl I) e) ρ))
        (amplify Ψ.map (Fin (Fintype.card R))
          (Matrix.reindex (Equiv.prodCongr (Equiv.refl I) e)
            (Equiv.prodCongr (Equiv.refl I) e) ρ)) = _
    rw [amplify_reindex_reference, amplify_reindex_reference]
    exact relativeEntropyBits_reindex eO hΦρ.1 hΨρ.1
  rw [← heq]
  exact stabilizedRelativeEntropyBits_witness_fin_le Φ Ψ _ hρ'

theorem single_isDensity (i : I) : IsDensity (Matrix.single i i (1 : ℂ)) := by
  constructor
  · have h := Matrix.posSemidef_conjTranspose_mul_self (Matrix.single i i (1 : ℂ))
    simpa [Matrix.conjTranspose_single] using h
  · simp [Matrix.trace, Matrix.diag, Matrix.single_apply]

theorem stabilizedRelativeEntropyBits_nonneg (Φ Ψ : FiniteCPTP I O)
    [Nonempty I] : 0 ≤ stabilizedRelativeEntropyBits Φ Ψ := by
  classical
  let i : I := Classical.choice inferInstance
  let ρ := Matrix.single (i, (0 : Fin 1)) (i, (0 : Fin 1)) (1 : ℂ)
  have hρ : IsDensity ρ := single_isDensity _
  have hΦρ := channel_density (amplifiedChannel Φ (Fin 1)) hρ.1 hρ.2
  have hΨρ := channel_density (amplifiedChannel Ψ (Fin 1)) hρ.1 hρ.2
  exact (Klein.relativeEntropyBits_nonneg hΦρ hΨρ).trans
    (stabilizedRelativeEntropyBits_witness_fin_le Φ Ψ 1 hρ)

theorem relativeEntropyBits_self (A : Matrix I I ℂ) : relativeEntropyBits A A = 0 := by
  have hs : HasSupportIn A A := fun _ hv => hv
  simp [relativeEntropyBits, hs, finiteRelativeEntropyBits]

end Stabilized

section TensorWitnesses

variable {I O J P R S : Type*}
  [Fintype I] [Fintype O] [Fintype J] [Fintype P] [Fintype R] [Fintype S]
  [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq P]
  [DecidableEq R] [DecidableEq S]

def groupReference (I J R S : Type*) : (I × R) × (J × S) ≃ (I × J) × (R × S) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem tensorChannel_amplify_product (Φ : FiniteCPTP I O) (Ψ : FiniteCPTP J P)
    (ρ : Matrix (I × R) (I × R) ℂ) (τ : Matrix (J × S) (J × S) ℂ) :
    amplify (tensorChannel Φ Ψ).map (R × S)
        (Matrix.reindex (groupReference I J R S) (groupReference I J R S) (ρ ⊗ₖ τ)) =
      Matrix.reindex (groupReference O P R S) (groupReference O P R S)
        (amplify Φ.map R ρ ⊗ₖ amplify Ψ.map S τ) := by
  ext x y
  exact congrArg (fun Z : Matrix (O × P) (O × P) ℂ => Z x.1 y.1)
    (tensorChannel_map_product Φ Ψ
      (fun i j => ρ (i, x.2.1) (j, y.2.1))
      (fun i j => τ (i, x.2.2) (j, y.2.2)))

theorem tensor_witness_lower (Φ Ψ : FiniteCPTP I O) (Φ' Ψ' : FiniteCPTP J P)
    {ρ : Matrix (I × R) (I × R) ℂ} {τ : Matrix (J × S) (J × S) ℂ}
    (hρ : IsDensity ρ) (hτ : IsDensity τ) :
    relativeEntropyBits (amplify Φ.map R ρ) (amplify Ψ.map R ρ) +
        relativeEntropyBits (amplify Φ'.map S τ) (amplify Ψ'.map S τ) ≤
      stabilizedRelativeEntropyBits (tensorChannel Φ Φ') (tensorChannel Ψ Ψ') := by
  let eI := groupReference I J R S
  let eO := groupReference O P R S
  let ω := Matrix.reindex eI eI (ρ ⊗ₖ τ)
  have hρτ := isDensity_kronecker hρ hτ
  have hω : IsDensity ω := channel_density (reindexChannel eI) hρτ.1 hρτ.2
  have hΦρ : IsDensity (amplify Φ.map R ρ) :=
    channel_density (amplifiedChannel Φ R) hρ.1 hρ.2
  have hΨρ : IsDensity (amplify Ψ.map R ρ) :=
    channel_density (amplifiedChannel Ψ R) hρ.1 hρ.2
  have hΦτ : IsDensity (amplify Φ'.map S τ) :=
    channel_density (amplifiedChannel Φ' S) hτ.1 hτ.2
  have hΨτ : IsDensity (amplify Ψ'.map S τ) :=
    channel_density (amplifiedChannel Ψ' S) hτ.1 hτ.2
  have heq :
      relativeEntropyBits (amplify (tensorChannel Φ Φ').map (R × S) ω)
          (amplify (tensorChannel Ψ Ψ').map (R × S) ω) =
        relativeEntropyBits (amplify Φ.map R ρ) (amplify Ψ.map R ρ) +
          relativeEntropyBits (amplify Φ'.map S τ) (amplify Ψ'.map S τ) := by
    change relativeEntropyBits
        (amplify (tensorChannel Φ Φ').map (R × S)
          (Matrix.reindex (groupReference I J R S) (groupReference I J R S) (ρ ⊗ₖ τ)))
        (amplify (tensorChannel Ψ Ψ').map (R × S)
          (Matrix.reindex (groupReference I J R S) (groupReference I J R S) (ρ ⊗ₖ τ))) = _
    rw [tensorChannel_amplify_product, tensorChannel_amplify_product,
      relativeEntropyBits_reindex eO (hΦρ.1.kronecker hΦτ.1) (hΨρ.1.kronecker hΨτ.1),
      TensorEntropy.relativeEntropyBits_kronecker hΦρ hΨρ.1 hΦτ hΨτ.1]
  rw [← heq]
  exact stabilizedRelativeEntropyBits_witness_le _ _ (R × S) hω

theorem stabilizedRelativeEntropyBits_tensor_lower
    (Φ Ψ : FiniteCPTP I O) (Φ' Ψ' : FiniteCPTP J P) :
    stabilizedRelativeEntropyBits Φ Ψ + stabilizedRelativeEntropyBits Φ' Ψ' ≤
      stabilizedRelativeEntropyBits (tensorChannel Φ Φ') (tensorChannel Ψ Ψ') := by
  apply EReal.add_le_of_forall_lt
  intro a ha b hb
  obtain ⟨r, hr⟩ := lt_iSup_iff.mp ha
  obtain ⟨ρ, hrρ⟩ := lt_iSup_iff.mp hr
  obtain ⟨hρ, haρ⟩ := lt_iSup_iff.mp hrρ
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp hb
  obtain ⟨τ, hsτ⟩ := lt_iSup_iff.mp hs
  obtain ⟨hτ, hbτ⟩ := lt_iSup_iff.mp hsτ
  exact (add_le_add haρ.le hbτ.le).trans (tensor_witness_lower Φ Ψ Φ' Ψ' hρ hτ)

end TensorWitnesses

end QuantumProver.SuperchannelDiscrimination.ChannelRegularization

namespace QuantumProver.SuperchannelDiscrimination.ExtendedFekete

open Filter
open scoped Topology

def normalized (a : ℕ → EReal) (n : ℕ) : EReal := (((n : ℝ)⁻¹ : ℝ) : EReal) * a n

def upperRate (a : ℕ → EReal) : EReal := ⨆ n : ℕ, normalized a (n + 1)

theorem normalized_nonneg {a : ℕ → EReal} (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    0 ≤ normalized a n := by
  apply EReal.mul_nonneg
  · exact EReal.coe_nonneg.mpr (inv_nonneg.mpr (show (0 : ℝ) ≤ n by positivity))
  · exact ha n

theorem normalized_le_upperRate {a : ℕ → EReal} {n : ℕ} (hn : 0 < n) :
    normalized a n ≤ upperRate a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact le_iSup (fun k => normalized a (k + 1)) k

theorem tendsto_normalized {a : ℕ → EReal} (ha : ∀ n, 0 ≤ a n)
    (hzero : a 0 = 0) (hsuper : ∀ m n, a m + a n ≤ a (m + n)) :
    Tendsto (normalized a) atTop (𝓝 (upperRate a)) := by
  have hbot (n : ℕ) : a n ≠ ⊥ := ne_of_gt (EReal.bot_lt_zero.trans_le (ha n))
  by_cases htop : ∃ n, a n = ⊤
  · obtain ⟨k, hk⟩ := htop
    have hk0 : k ≠ 0 := by
      intro h
      simpa [h, hzero] using hk
    have hpos : 0 < k := Nat.pos_of_ne_zero hk0
    have habove (p : ℕ) (hp : k ≤ p) : a p = ⊤ := by
      have h := hsuper k (p - k)
      rw [Nat.add_sub_of_le hp, hk, EReal.top_add_of_ne_bot (hbot (p - k))] at h
      exact top_le_iff.mp h
    have hnormtop (p : ℕ) (hp : 0 < p) (h : a p = ⊤) : normalized a p = ⊤ := by
      rw [normalized, h]
      exact EReal.coe_mul_top_of_pos (inv_pos.mpr (Nat.cast_pos.mpr hp))
    have hL : upperRate a = ⊤ := by
      apply top_le_iff.mp
      rw [← hnormtop k hpos hk]
      exact normalized_le_upperRate hpos
    rw [hL]
    have he : normalized a =ᶠ[atTop] (fun _ : ℕ => (⊤ : EReal)) := by
      filter_upwards [eventually_ge_atTop k] with p hp
      exact hnormtop p (hpos.trans_le hp) (habove p hp)
    exact (tendsto_congr' he).2 tendsto_const_nhds
  · have hfinite (n : ℕ) : a n ≠ ⊤ := fun hn => htop ⟨n, hn⟩
    let x : ℕ → ℝ := fun n => (a n).toReal
    have hcoe (n : ℕ) : (x n : EReal) = a n :=
      EReal.coe_toReal (hfinite n) (hbot n)
    have hsub : Subadditive (fun n => -x n) := by
      intro m n
      have h := hsuper m n
      rw [← hcoe m, ← hcoe n, ← hcoe (m + n), ← EReal.coe_add] at h
      have hr : x m + x n ≤ x (m + n) := by exact_mod_cast h
      linarith
    have hnorm (n : ℕ) : normalized a n = ((x n / n : ℝ) : EReal) := by
      rw [normalized, ← hcoe n, ← EReal.coe_mul]
      congr 1
      simp [div_eq_mul_inv, mul_comm]
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro l hl
      induction l using EReal.rec with
      | bot =>
          exact Eventually.of_forall fun n =>
            EReal.bot_lt_zero.trans_le (normalized_nonneg ha n)
      | coe c =>
          obtain ⟨k, hk⟩ := lt_iSup_iff.mp hl
          rw [hnorm] at hk
          have hc : c < x (k + 1) / (k + 1) := by exact_mod_cast hk
          have hu : (-x (k + 1)) / (k + 1 : ℕ) < -c := by
            simpa only [neg_div, Nat.cast_add, Nat.cast_one] using neg_lt_neg hc
          have he := hsub.eventually_div_lt_of_div_lt (Nat.succ_ne_zero k) hu
          filter_upwards [he] with p hp
          rw [hnorm]
          have hc' : c < x p / p := by
            rw [neg_div] at hp
            exact neg_lt_neg_iff.mp hp
          exact_mod_cast hc'
      | top => exact False.elim (not_top_lt hl)
    · intro U hU
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact (normalized_le_upperRate (lt_of_lt_of_le Nat.zero_lt_one hn)).trans_lt hU

end QuantumProver.SuperchannelDiscrimination.ExtendedFekete

namespace QuantumProver.SuperchannelDiscrimination.ChannelRegularization

open Matrix KrausCompletion CPWrappers FlaggedStates TensorEntropy
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker Topology

section ChannelBasisChanges

variable {I O J P : Type*} [Fintype I] [Fintype O] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq P]

theorem reindex_roundtrip (e : I ≃ J) (X : Matrix I I ℂ) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e X) = X := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

theorem reindex_single (e : I ≃ J) (i j : I) :
    Matrix.reindex e e (Matrix.single i j (1 : ℂ)) =
      Matrix.single (e i) (e j) (1 : ℂ) := by
  ext a b
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.single_apply,
    Equiv.eq_symm_apply]

theorem matrixMap_ext_units (F G : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (h : ∀ i j, F (Matrix.single i j 1) = G (Matrix.single i j 1)) : F = G := by
  apply LinearMap.ext
  intro X
  have hX : X = ∑ i : I, ∑ j : I, X i j • Matrix.single i j (1 : ℂ) := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single X
  calc
    F X = ∑ i : I, ∑ j : I, X i j • F (Matrix.single i j 1) := by
      conv_lhs => rw [hX]
      simp only [map_sum, map_smul]
    _ = ∑ i : I, ∑ j : I, X i j • G (Matrix.single i j 1) := by simp only [h]
    _ = G X := by
      conv_rhs => rw [hX]
      simp only [map_sum, map_smul]

theorem amplify_intertwine_reindex (eI : I ≃ J) (eO : O ≃ P)
    (Φ : FiniteCPTP I O) (Φ' : FiniteCPTP J P)
    (hΦ : ∀ X, Φ'.map (Matrix.reindex eI eI X) = Matrix.reindex eO eO (Φ.map X))
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (I × R) (I × R) ℂ) :
    amplify Φ'.map R
        (Matrix.reindex (Equiv.prodCongr eI (Equiv.refl R))
          (Equiv.prodCongr eI (Equiv.refl R)) ρ) =
      Matrix.reindex (Equiv.prodCongr eO (Equiv.refl R))
        (Equiv.prodCongr eO (Equiv.refl R)) (amplify Φ.map R ρ) := by
  ext x y
  exact congrArg (fun Z : Matrix P P ℂ => Z x.1 y.1)
    (hΦ (fun i j => ρ (i, x.2) (j, y.2)))

theorem stabilizedRelativeEntropyBits_le_of_intertwine
    (eI : I ≃ J) (eO : O ≃ P) (Φ Ψ : FiniteCPTP I O) (Φ' Ψ' : FiniteCPTP J P)
    (hΦ : ∀ X, Φ'.map (Matrix.reindex eI eI X) = Matrix.reindex eO eO (Φ.map X))
    (hΨ : ∀ X, Ψ'.map (Matrix.reindex eI eI X) = Matrix.reindex eO eO (Ψ.map X)) :
    stabilizedRelativeEntropyBits Φ Ψ ≤ stabilizedRelativeEntropyBits Φ' Ψ' := by
  refine iSup_le fun r => iSup_le fun ρ => iSup_le fun hρ => ?_
  let ei := Equiv.prodCongr eI (Equiv.refl (Fin r))
  let eo := Equiv.prodCongr eO (Equiv.refl (Fin r))
  let ρ' := Matrix.reindex ei ei ρ
  have hρ' : IsDensity ρ' := channel_density (reindexChannel ei) hρ.1 hρ.2
  have hΦρ := channel_density (amplifiedChannel Φ (Fin r)) hρ.1 hρ.2
  have hΨρ := channel_density (amplifiedChannel Ψ (Fin r)) hρ.1 hρ.2
  have heq : relativeEntropyBits (amplify Φ'.map (Fin r) ρ')
          (amplify Ψ'.map (Fin r) ρ') =
        relativeEntropyBits (amplify Φ.map (Fin r) ρ) (amplify Ψ.map (Fin r) ρ) := by
    change relativeEntropyBits
        (amplify Φ'.map (Fin r)
          (Matrix.reindex (Equiv.prodCongr eI (Equiv.refl (Fin r)))
            (Equiv.prodCongr eI (Equiv.refl (Fin r))) ρ))
        (amplify Ψ'.map (Fin r)
          (Matrix.reindex (Equiv.prodCongr eI (Equiv.refl (Fin r)))
            (Equiv.prodCongr eI (Equiv.refl (Fin r))) ρ)) = _
    rw [amplify_intertwine_reindex eI eO Φ Φ' hΦ,
      amplify_intertwine_reindex eI eO Ψ Ψ' hΨ]
    exact relativeEntropyBits_reindex eo hΦρ.1 hΨρ.1
  have h := stabilizedRelativeEntropyBits_witness_fin_le Φ' Ψ' r hρ'
  rwa [heq] at h

theorem stabilizedRelativeEntropyBits_eq_of_intertwine
    (eI : I ≃ J) (eO : O ≃ P) (Φ Ψ : FiniteCPTP I O) (Φ' Ψ' : FiniteCPTP J P)
    (hΦ : ∀ X, Φ'.map (Matrix.reindex eI eI X) = Matrix.reindex eO eO (Φ.map X))
    (hΨ : ∀ X, Ψ'.map (Matrix.reindex eI eI X) = Matrix.reindex eO eO (Ψ.map X)) :
    stabilizedRelativeEntropyBits Φ Ψ = stabilizedRelativeEntropyBits Φ' Ψ' := by
  apply le_antisymm
  · exact stabilizedRelativeEntropyBits_le_of_intertwine eI eO Φ Ψ Φ' Ψ' hΦ hΨ
  · apply stabilizedRelativeEntropyBits_le_of_intertwine eI.symm eO.symm Φ' Ψ' Φ Ψ
    · intro X
      have h := congrArg (Matrix.reindex eO.symm eO.symm)
        (hΦ (Matrix.reindex eI.symm eI.symm X))
      simpa [reindex_roundtrip] using h.symm
    · intro X
      have h := congrArg (Matrix.reindex eO.symm eO.symm)
        (hΨ (Matrix.reindex eI.symm eI.symm X))
      simpa [reindex_roundtrip] using h.symm

end ChannelBasisChanges

section Powers

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

instance tensorIndexZeroUnique (I : Type*) : Unique (TensorIndex I 0) :=
  inferInstanceAs (Unique PUnit)

def channelPower (Φ : FiniteCPTP I O) : (n : ℕ) →
    FiniteCPTP (TensorIndex I n) (TensorIndex O n)
  | 0 => reindexChannel (Equiv.ofUnique _ _)
  | n + 1 => tensorChannel (channelPower Φ n) Φ

def splitTensorIndex (I : Type*) (m : ℕ) : (n : ℕ) →
    TensorIndex I (m + n) ≃ TensorIndex I m × TensorIndex I n
  | 0 => (Equiv.prodPUnit (TensorIndex I m)).symm
  | n + 1 =>
      (Equiv.prodCongr (splitTensorIndex I m n) (Equiv.refl I)).trans
        (Equiv.prodAssoc (TensorIndex I m) (TensorIndex I n) I)

def tensorUnitOutput (Φ : FiniteCPTP I O) : (n : ℕ) →
    TensorIndex I n → TensorIndex I n → Matrix (TensorIndex O n) (TensorIndex O n) ℂ
  | 0, _, _ => 1
  | n + 1, i, j => tensorUnitOutput Φ n i.1 j.1 ⊗ₖ Φ.map (Matrix.single i.2 j.2 1)

theorem channelPower_map_single (Φ : FiniteCPTP I O) (n : ℕ)
    (i j : TensorIndex I n) :
    (channelPower Φ n).map (Matrix.single i j 1) = tensorUnitOutput Φ n i j := by
  induction n with
  | zero =>
      ext x y
      cases i
      cases j
      cases x
      cases y
      have hinv : (Equiv.ofUnique (TensorIndex I 0) (TensorIndex O 0)).symm PUnit.unit =
          PUnit.unit := Subsingleton.elim _ _
      change (Matrix.single PUnit.unit PUnit.unit (1 : ℂ))
        ((Equiv.ofUnique (TensorIndex I 0) (TensorIndex O 0)).symm PUnit.unit)
        ((Equiv.ofUnique (TensorIndex I 0) (TensorIndex O 0)).symm PUnit.unit) = (1 : ℂ)
      rw [hinv]
      simp [Matrix.single_apply]
  | succ n ih =>
      rcases i with ⟨i₀, i₁⟩
      rcases j with ⟨j₀, j₁⟩
      have hunit : Matrix.single i₀ j₀ (1 : ℂ) ⊗ₖ Matrix.single i₁ j₁ 1 =
          Matrix.single (i₀, i₁) (j₀, j₁) 1 := by
        simpa only [mul_one] using Matrix.single_kronecker_single i₀ j₀ i₁ j₁ (1 : ℂ) 1
      change (tensorChannel (channelPower Φ n) Φ).map
        (Matrix.single (i₀, i₁) (j₀, j₁) 1) = _
      rw [← hunit, tensorChannel_map_product, ih]
      rfl

theorem tensorUnitOutput_split (Φ : FiniteCPTP I O) (m n : ℕ)
    (i j : TensorIndex I (m + n)) :
    Matrix.reindex (splitTensorIndex O m n) (splitTensorIndex O m n)
        (tensorUnitOutput Φ (m + n) i j) =
      tensorUnitOutput Φ m ((splitTensorIndex I m n) i).1
          ((splitTensorIndex I m n) j).1 ⊗ₖ
        tensorUnitOutput Φ n ((splitTensorIndex I m n) i).2
          ((splitTensorIndex I m n) j).2 := by
  induction n with
  | zero =>
      ext ⟨a, b⟩ ⟨a', b'⟩
      cases b
      cases b'
      change tensorUnitOutput Φ m i j a a' = tensorUnitOutput Φ m i j a a' *
        (1 : Matrix PUnit PUnit ℂ) PUnit.unit PUnit.unit
      simp only [Matrix.one_apply, ite_true, mul_one]
  | succ n ih =>
      ext ⟨a, ⟨b, c⟩⟩ ⟨a', ⟨b', c'⟩⟩
      have h : tensorUnitOutput Φ (m + n) i.1 j.1
            ((splitTensorIndex O m n).symm (a, b))
            ((splitTensorIndex O m n).symm (a', b')) =
          tensorUnitOutput Φ m ((splitTensorIndex I m n) i.1).1
              ((splitTensorIndex I m n) j.1).1 a a' *
            tensorUnitOutput Φ n ((splitTensorIndex I m n) i.1).2
              ((splitTensorIndex I m n) j.1).2 b b' :=
        congrArg (fun X => X (a, b) (a', b')) (ih i.1 j.1)
      change tensorUnitOutput Φ (m + n) i.1 j.1
            ((splitTensorIndex O m n).symm (a, b))
            ((splitTensorIndex O m n).symm (a', b')) *
          Φ.map (Matrix.single i.2 j.2 1) c c' =
        tensorUnitOutput Φ m ((splitTensorIndex I m n) i.1).1
            ((splitTensorIndex I m n) j.1).1 a a' *
          (tensorUnitOutput Φ n ((splitTensorIndex I m n) i.1).2
              ((splitTensorIndex I m n) j.1).2 b b' *
            Φ.map (Matrix.single i.2 j.2 1) c c')
      rw [h, mul_assoc]

theorem channelPower_split_map (Φ : FiniteCPTP I O) (m n : ℕ)
    (X : Matrix (TensorIndex I (m + n)) (TensorIndex I (m + n)) ℂ) :
    Matrix.reindex (splitTensorIndex O m n) (splitTensorIndex O m n)
        ((channelPower Φ (m + n)).map X) =
      (tensorChannel (channelPower Φ m) (channelPower Φ n)).map
        (Matrix.reindex (splitTensorIndex I m n) (splitTensorIndex I m n) X) := by
  let ei := splitTensorIndex I m n
  let eo := splitTensorIndex O m n
  let F := (reindexMap eo).comp (channelPower Φ (m + n)).map
  let G := (tensorChannel (channelPower Φ m) (channelPower Φ n)).map.comp (reindexMap ei)
  have hFG : F = G := by
    apply matrixMap_ext_units
    intro i j
    change Matrix.reindex eo eo ((channelPower Φ (m + n)).map (Matrix.single i j 1)) =
      (tensorChannel (channelPower Φ m) (channelPower Φ n)).map
        (Matrix.reindex ei ei (Matrix.single i j 1))
    rw [channelPower_map_single, tensorUnitOutput_split, reindex_single]
    have hunit : Matrix.single (ei i).1 (ei j).1 (1 : ℂ) ⊗ₖ
          Matrix.single (ei i).2 (ei j).2 1 = Matrix.single (ei i) (ei j) 1 := by
      simpa using Matrix.single_kronecker_single (ei i).1 (ei j).1
        (ei i).2 (ei j).2 (1 : ℂ) 1
    rw [← hunit, tensorChannel_map_product, channelPower_map_single, channelPower_map_single]
  exact congrArg (fun H => H X) hFG

theorem channelPower_split_product (Φ : FiniteCPTP I O) (m n : ℕ)
    (A : Matrix (TensorIndex I m) (TensorIndex I m) ℂ)
    (B : Matrix (TensorIndex I n) (TensorIndex I n) ℂ) :
    (channelPower Φ (m + n)).map
        (Matrix.reindex (splitTensorIndex I m n).symm
          (splitTensorIndex I m n).symm (A ⊗ₖ B)) =
      Matrix.reindex (splitTensorIndex O m n).symm (splitTensorIndex O m n).symm
        ((channelPower Φ m).map A ⊗ₖ (channelPower Φ n).map B) := by
  have h := congrArg
    (Matrix.reindex (splitTensorIndex O m n).symm (splitTensorIndex O m n).symm)
    (channelPower_split_map Φ m n
      (Matrix.reindex (splitTensorIndex I m n).symm (splitTensorIndex I m n).symm (A ⊗ₖ B)))
  simpa [reindex_roundtrip, tensorChannel_map_product] using h

instance tensorIndexNonempty (I : Type*) [Nonempty I] (n : ℕ) : Nonempty (TensorIndex I n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty PUnit)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (Nonempty (TensorIndex I n × I))

def powerValue (Φ Ψ : FiniteCPTP I O) (n : ℕ) : EReal :=
  stabilizedRelativeEntropyBits (channelPower Φ n) (channelPower Ψ n)

def normalizedPowerValue (Φ Ψ : FiniteCPTP I O) : ℕ → EReal :=
  ExtendedFekete.normalized (powerValue Φ Ψ)

def regularizedRelativeEntropyBits (Φ Ψ : FiniteCPTP I O) : EReal :=
  ExtendedFekete.upperRate (powerValue Φ Ψ)

theorem stabilizedRelativeEntropyBits_self (Φ : FiniteCPTP I O) [Nonempty I] :
    stabilizedRelativeEntropyBits Φ Φ = 0 := by
  apply le_antisymm
  · refine iSup_le fun r => iSup_le fun ρ => iSup_le fun _hρ => ?_
    simp only [relativeEntropyBits_self, le_refl]
  · exact stabilizedRelativeEntropyBits_nonneg Φ Φ

theorem powerValue_zero (Φ Ψ : FiniteCPTP I O) : powerValue Φ Ψ 0 = 0 := by
  change stabilizedRelativeEntropyBits (reindexChannel (Equiv.ofUnique _ _))
    (reindexChannel (Equiv.ofUnique _ _)) = 0
  exact stabilizedRelativeEntropyBits_self _

theorem powerValue_nonneg (Φ Ψ : FiniteCPTP I O) [Nonempty I] (n : ℕ) :
    0 ≤ powerValue Φ Ψ n := stabilizedRelativeEntropyBits_nonneg _ _

theorem powerValue_split (Φ Ψ : FiniteCPTP I O) (m n : ℕ) :
    powerValue Φ Ψ (m + n) =
      stabilizedRelativeEntropyBits (tensorChannel (channelPower Φ m) (channelPower Φ n))
        (tensorChannel (channelPower Ψ m) (channelPower Ψ n)) :=
  stabilizedRelativeEntropyBits_eq_of_intertwine (splitTensorIndex I m n)
    (splitTensorIndex O m n) _ _ _ _
    (fun X => (channelPower_split_map Φ m n X).symm)
    (fun X => (channelPower_split_map Ψ m n X).symm)

theorem powerValue_superadditive (Φ Ψ : FiniteCPTP I O) (m n : ℕ) :
    powerValue Φ Ψ m + powerValue Φ Ψ n ≤ powerValue Φ Ψ (m + n) := by
  rw [powerValue_split]
  exact stabilizedRelativeEntropyBits_tensor_lower _ _ _ _

theorem powerValue_multiple_lower (Φ Ψ : FiniteCPTP I O) (k n : ℕ) :
    (k : EReal) * powerValue Φ Ψ n ≤ powerValue Φ Ψ (k * n) := by
  induction k with
  | zero => simp [powerValue_zero]
  | succ k ih =>
      calc
        ((k + 1 : ℕ) : EReal) * powerValue Φ Ψ n =
            (k : EReal) * powerValue Φ Ψ n + powerValue Φ Ψ n := by
          rw [Nat.cast_succ, EReal.right_distrib_of_nonneg (by positivity) (by positivity), one_mul]
        _ ≤ powerValue Φ Ψ (k * n) + powerValue Φ Ψ n := add_le_add ih le_rfl
        _ ≤ powerValue Φ Ψ (k * n + n) := powerValue_superadditive Φ Ψ _ _
        _ = powerValue Φ Ψ ((k + 1) * n) := by congr 1; ring

theorem tensor_input_test_lower (Φ Ψ : FiniteCPTP I O) (n : ℕ)
    (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (TensorIndex I n × R) (TensorIndex I n × R) ℂ} (hρ : IsDensity ρ) :
    relativeEntropyBits (amplify (channelPower Φ n).map R ρ)
        (amplify (channelPower Ψ n).map R ρ) ≤ powerValue Φ Ψ n :=
  stabilizedRelativeEntropyBits_witness_le _ _ R hρ

theorem normalizedPowerValue_zero (Φ Ψ : FiniteCPTP I O) :
    normalizedPowerValue Φ Ψ 0 = 0 := by
  simp [normalizedPowerValue, ExtendedFekete.normalized]

theorem normalizedPowerValue_tendsto (Φ Ψ : FiniteCPTP I O) [Nonempty I] :
    Filter.Tendsto (normalizedPowerValue Φ Ψ) Filter.atTop
      (𝓝 (regularizedRelativeEntropyBits Φ Ψ)) :=
  ExtendedFekete.tendsto_normalized (powerValue_nonneg Φ Ψ)
    (powerValue_zero Φ Ψ) (powerValue_superadditive Φ Ψ)

end Powers

end QuantumProver.SuperchannelDiscrimination.ChannelRegularization

noncomputable section

namespace QuantumProver.SuperchannelDiscrimination.ChannelRegularization

open Matrix KrausCompletion CPWrappers FlaggedStates TensorEntropy
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker Topology

variable {I O : Type*} [Fintype I] [Fintype O]
  [DecidableEq I] [DecidableEq O]

theorem normalizedPowerValue_le_regularized (Φ Ψ : FiniteCPTP I O)
    {n : ℕ} (hn : 0 < n) :
    normalizedPowerValue Φ Ψ n ≤ regularizedRelativeEntropyBits Φ Ψ :=
  ExtendedFekete.normalized_le_upperRate hn

theorem regularizedRelativeEntropyBits_nonneg (Φ Ψ : FiniteCPTP I O)
    [Nonempty I] : 0 ≤ regularizedRelativeEntropyBits Φ Ψ :=
  (ExtendedFekete.normalized_nonneg (powerValue_nonneg Φ Ψ) 1).trans
    (normalizedPowerValue_le_regularized Φ Ψ Nat.zero_lt_one)

theorem regularizedRelativeEntropyBits_ne_bot (Φ Ψ : FiniteCPTP I O)
    [Nonempty I] : regularizedRelativeEntropyBits Φ Ψ ≠ ⊥ :=
  ne_of_gt (EReal.bot_lt_zero.trans_le (regularizedRelativeEntropyBits_nonneg Φ Ψ))

theorem powerValue_le_regularized (Φ Ψ : FiniteCPTP I O) (n : ℕ) :
    powerValue Φ Ψ n ≤ ((n : ℝ) : EReal) * regularizedRelativeEntropyBits Φ Ψ := by
  by_cases hn : n = 0
  · subst n
    simp [powerValue_zero]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have h := normalizedPowerValue_le_regularized Φ Ψ (Nat.pos_of_ne_zero hn)
    have hm := mul_le_mul_of_nonneg_left h
      (EReal.coe_nonneg.mpr (show (0 : ℝ) ≤ n by positivity))
    change ((n : ℝ) : EReal) *
      ((((n : ℝ)⁻¹ : ℝ) : EReal) * powerValue Φ Ψ n) ≤ _ at hm
    rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hnR, EReal.coe_one, one_mul] at hm
    exact hm

theorem powerValue_le_real_bound (Φ Ψ : FiniteCPTP I O) (n : ℕ) {B : ℝ}
    (hB : regularizedRelativeEntropyBits Φ Ψ ≤ (B : EReal)) :
    powerValue Φ Ψ n ≤ (((n : ℝ) * B : ℝ) : EReal) := by
  calc
    powerValue Φ Ψ n ≤ ((n : ℝ) : EReal) * regularizedRelativeEntropyBits Φ Ψ :=
      powerValue_le_regularized Φ Ψ n
    _ ≤ ((n : ℝ) : EReal) * (B : EReal) := mul_le_mul_of_nonneg_left hB (by positivity)
    _ = _ := (EReal.coe_mul _ _).symm

theorem channelPower_reference_isDensity (Φ : FiniteCPTP I O) (n : ℕ)
    (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (TensorIndex I n × R) (TensorIndex I n × R) ℂ}
    (hρ : IsDensity ρ) : IsDensity (amplify (channelPower Φ n).map R ρ) :=
  channel_density (amplifiedChannel (channelPower Φ n) R) hρ.1 hρ.2

theorem channelPower_reference_entropy_le_regularized (Φ Ψ : FiniteCPTP I O)
    (n : ℕ) (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (TensorIndex I n × R) (TensorIndex I n × R) ℂ}
    (hρ : IsDensity ρ) :
    relativeEntropyBits (amplify (channelPower Φ n).map R ρ)
      (amplify (channelPower Ψ n).map R ρ) ≤
      ((n : ℝ) : EReal) * regularizedRelativeEntropyBits Φ Ψ :=
  (tensor_input_test_lower Φ Ψ n R hρ).trans (powerValue_le_regularized Φ Ψ n)

theorem channelPower_reference_entropy_le_real_bound (Φ Ψ : FiniteCPTP I O)
    (n : ℕ) (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (TensorIndex I n × R) (TensorIndex I n × R) ℂ}
    (hρ : IsDensity ρ) {B : ℝ}
    (hB : regularizedRelativeEntropyBits Φ Ψ ≤ (B : EReal)) :
    relativeEntropyBits (amplify (channelPower Φ n).map R ρ)
      (amplify (channelPower Ψ n).map R ρ) ≤ (((n : ℝ) * B : ℝ) : EReal) :=
  (tensor_input_test_lower Φ Ψ n R hρ).trans (powerValue_le_real_bound Φ Ψ n hB)

theorem hasSupportIn_of_relativeEntropyBits_le_real {J : Type*}
    [Fintype J] [DecidableEq J] {A H : Matrix J J ℂ} {b : ℝ}
    (h : relativeEntropyBits A H ≤ (b : EReal)) : HasSupportIn A H := by
  by_contra hsupport
  rw [relativeEntropyBits, if_neg hsupport] at h
  exact (not_le_of_gt (EReal.coe_lt_top b) h).elim

theorem channelPower_reference_support_of_real_bound (Φ Ψ : FiniteCPTP I O)
    (n : ℕ) (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (TensorIndex I n × R) (TensorIndex I n × R) ℂ}
    (hρ : IsDensity ρ) {B : ℝ}
    (hB : regularizedRelativeEntropyBits Φ Ψ ≤ (B : EReal)) :
    HasSupportIn (amplify (channelPower Φ n).map R ρ)
      (amplify (channelPower Ψ n).map R ρ) :=
  hasSupportIn_of_relativeEntropyBits_le_real
    (channelPower_reference_entropy_le_real_bound Φ Ψ n R hρ hB)

section Postprocessing

variable {J R : Type*} [Fintype J] [DecidableEq J]
  [Fintype R] [DecidableEq R]

theorem postprocessed_power_reference_entropy_le_power (Φ Ψ : FiniteCPTP I O)
    (n : ℕ) (M : FiniteCPTP (TensorIndex O n × R) J)
    {ρ : Matrix (TensorIndex I n × R) (TensorIndex I n × R) ℂ}
    (hρ : IsDensity ρ) :
    relativeEntropyBits (M.map (amplify (channelPower Φ n).map R ρ))
      (M.map (amplify (channelPower Ψ n).map R ρ)) ≤ powerValue Φ Ψ n := by
  exact (AbstractDPI.relativeEntropyBits_cptp_dpi M
    (channelPower_reference_isDensity Φ n R hρ).1
    (channelPower_reference_isDensity Ψ n R hρ).1).trans
      (tensor_input_test_lower Φ Ψ n R hρ)

theorem postprocessed_power_reference_entropy_le_regularized (Φ Ψ : FiniteCPTP I O)
    (n : ℕ) (M : FiniteCPTP (TensorIndex O n × R) J)
    {ρ : Matrix (TensorIndex I n × R) (TensorIndex I n × R) ℂ}
    (hρ : IsDensity ρ) :
    relativeEntropyBits (M.map (amplify (channelPower Φ n).map R ρ))
      (M.map (amplify (channelPower Ψ n).map R ρ)) ≤
        ((n : ℝ) : EReal) * regularizedRelativeEntropyBits Φ Ψ :=
  (postprocessed_power_reference_entropy_le_power Φ Ψ n M hρ).trans
    (powerValue_le_regularized Φ Ψ n)

theorem postprocessed_power_reference_entropy_le_real_bound (Φ Ψ : FiniteCPTP I O)
    (n : ℕ) (M : FiniteCPTP (TensorIndex O n × R) J)
    {ρ : Matrix (TensorIndex I n × R) (TensorIndex I n × R) ℂ}
    (hρ : IsDensity ρ) {B : ℝ}
    (hB : regularizedRelativeEntropyBits Φ Ψ ≤ (B : EReal)) :
    relativeEntropyBits (M.map (amplify (channelPower Φ n).map R ρ))
      (M.map (amplify (channelPower Ψ n).map R ρ)) ≤ (((n : ℝ) * B : ℝ) : EReal) :=
  (postprocessed_power_reference_entropy_le_power Φ Ψ n M hρ).trans
    (powerValue_le_real_bound Φ Ψ n hB)

theorem wrapped_power_entropy_le_real_bound (Φ Ψ : FiniteCPTP I O)
    (n : ℕ) {C : Type*} [Fintype C] [DecidableEq C]
    (P : FiniteCPTP C (TensorIndex I n × R))
    (M : FiniteCPTP (TensorIndex O n × R) J)
    {ρ : Matrix C C ℂ} (hρ : IsDensity ρ) {B : ℝ}
    (hB : regularizedRelativeEntropyBits Φ Ψ ≤ (B : EReal)) :
    relativeEntropyBits (M.map (amplify (channelPower Φ n).map R (P.map ρ)))
      (M.map (amplify (channelPower Ψ n).map R (P.map ρ))) ≤
        (((n : ℝ) * B : ℝ) : EReal) :=
  postprocessed_power_reference_entropy_le_real_bound Φ Ψ n M
    (channel_density P hρ.1 hρ.2) hB

theorem normalized_reference_entropy_le_regularized (Φ Ψ : FiniteCPTP I O)
    {n : ℕ} (hn : 0 < n)
    {ρ : Matrix (TensorIndex I n × R) (TensorIndex I n × R) ℂ}
    (hρ : IsDensity ρ) :
    (((n : ℝ)⁻¹ : ℝ) : EReal) *
      relativeEntropyBits (amplify (channelPower Φ n).map R ρ)
        (amplify (channelPower Ψ n).map R ρ) ≤ regularizedRelativeEntropyBits Φ Ψ := by
  have h := mul_le_mul_of_nonneg_left (tensor_input_test_lower Φ Ψ n R hρ)
    (EReal.coe_nonneg.mpr (inv_nonneg.mpr (show (0 : ℝ) ≤ n by positivity)))
  exact h.trans (normalizedPowerValue_le_regularized Φ Ψ hn)

theorem normalized_postprocessed_entropy_le_regularized (Φ Ψ : FiniteCPTP I O)
    {n : ℕ} (hn : 0 < n) (M : FiniteCPTP (TensorIndex O n × R) J)
    {ρ : Matrix (TensorIndex I n × R) (TensorIndex I n × R) ℂ}
    (hρ : IsDensity ρ) :
    (((n : ℝ)⁻¹ : ℝ) : EReal) *
      relativeEntropyBits (M.map (amplify (channelPower Φ n).map R ρ))
        (M.map (amplify (channelPower Ψ n).map R ρ)) ≤ regularizedRelativeEntropyBits Φ Ψ := by
  have h := mul_le_mul_of_nonneg_left
    (postprocessed_power_reference_entropy_le_power Φ Ψ n M hρ)
    (EReal.coe_nonneg.mpr (inv_nonneg.mpr (show (0 : ℝ) ≤ n by positivity)))
  exact h.trans (normalizedPowerValue_le_regularized Φ Ψ hn)

end Postprocessing
end QuantumProver.SuperchannelDiscrimination.ChannelRegularization
