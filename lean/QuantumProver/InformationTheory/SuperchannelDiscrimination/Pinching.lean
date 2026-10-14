import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.DiamondControl

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.SuperchannelDiscrimination.Pinching

variable {n κ R : Type*} [Fintype n] [Fintype κ] [Fintype R]
  [DecidableEq n] [DecidableEq R]

structure IsProjectionFamily (P : κ → Matrix n n ℂ) : Prop where
  selfAdjoint : ∀ i, (P i).IsHermitian
  idempotent : ∀ i, P i * P i = P i
  orthogonal : ∀ i j, i ≠ j → P i * P j = 0
  complete : ∑ i, P i = 1

def pinchingMap (P : κ → Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := ∑ i, P i * X * (P i)ᴴ
  map_add' X Y := by
    simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' z X := by
    simp [Finset.smul_sum]

theorem pinchingMap_apply (P : κ → Matrix n n ℂ)
    (hP : ∀ i, (P i).IsHermitian) (X : Matrix n n ℂ) :
    pinchingMap P X = ∑ i, P i * X * P i := by
  change (∑ i, P i * X * (P i)ᴴ) = _
  exact Finset.sum_congr rfl (fun i _ => by rw [(hP i).eq])

theorem pinchingMap_posSemidef (P : κ → Matrix n n ℂ)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) : (pinchingMap P X).PosSemidef := by
  simpa [pinchingMap] using Matrix.posSemidef_sum Finset.univ
    (fun i _ => hX.mul_mul_conjTranspose_same (P i))

theorem amplifyMap_pinching (P : κ → Matrix n n ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (X : Matrix (n × R) (n × R) ℂ) :
    DiamondControl.amplifyMap (pinchingMap P) R X =
      ∑ i, (P i ⊗ₖ (1 : Matrix R R ℂ)) * X * (P i ⊗ₖ (1 : Matrix R R ℂ))ᴴ := by
  ext x y
  simp [DiamondControl.amplifyMap, pinchingMap, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.one_apply, Finset.sum_mul]
  simp [apply_ite]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change (∑ a : n, P i x.1 a * X (a, x.2) (j, y.2)) * star (P i y.1 j) =
    ∑ a : n, P i x.1 a * X (a, x.2) (j, y.2) * star (P i y.1 j)
  rw [Finset.sum_mul]

theorem pinchingMap_completelyPositive (P : κ → Matrix n n ℂ) :
    DiamondControl.CompletelyPositive (pinchingMap P) := by
  intro k X hX
  rw [amplifyMap_pinching]
  simpa using Matrix.posSemidef_sum Finset.univ
    (fun i _ => hX.mul_mul_conjTranspose_same (P i ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℂ)))

theorem pinchingMap_completelyPositive_allReferences (P : κ → Matrix n n ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix (n × R) (n × R) ℂ} (hX : X.PosSemidef) :
    (DiamondControl.amplifyMap (pinchingMap P) R X).PosSemidef :=
  DiamondControl.completelyPositive_allReferences (pinchingMap_completelyPositive P) R hX

theorem trace_pinchingMap (P : κ → Matrix n n ℂ) (X : Matrix n n ℂ) :
    (pinchingMap P X).trace = ((∑ i, (P i)ᴴ * P i) * X).trace := by
  change (∑ i, P i * X * (P i)ᴴ).trace = _
  rw [Matrix.trace_sum, Matrix.sum_mul, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun i _ => Matrix.trace_mul_cycle (P i) X (P i)ᴴ

theorem projection_gram_eq_one {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P) :
    (∑ i, (P i)ᴴ * P i) = 1 := by
  calc
    (∑ i, (P i)ᴴ * P i) = ∑ i, P i := by
      exact Finset.sum_congr rfl (fun i _ => by rw [(hP.selfAdjoint i).eq, hP.idempotent i])
    _ = 1 := hP.complete

theorem pinchingMap_tracePreserving {P : κ → Matrix n n ℂ}
    (hP : IsProjectionFamily P) (X : Matrix n n ℂ) :
    (pinchingMap P X).trace = X.trace := by
  rw [trace_pinchingMap, projection_gram_eq_one hP, Matrix.one_mul]

theorem pinchingMap_tracePreserving_allReferences {P : κ → Matrix n n ℂ}
    (hP : IsProjectionFamily P) (R : Type*) [Fintype R] [DecidableEq R]
    (X : Matrix (n × R) (n × R) ℂ) :
    (DiamondControl.amplifyMap (pinchingMap P) R X).trace = X.trace :=
  DiamondControl.amplifyMap_tracePreserving (pinchingMap P) (pinchingMap_tracePreserving hP) R X

theorem pinchingMap_density {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P)
    {ρ : Matrix n n ℂ} (hρ : FlaggedStates.IsDensity ρ) :
    FlaggedStates.IsDensity (pinchingMap P ρ) :=
  ⟨pinchingMap_posSemidef P hρ.1, (pinchingMap_tracePreserving hP ρ).trans hρ.2⟩

theorem pinching_defect_sum_identity (P : κ → Matrix n n ℂ)
    (hP : ∀ i, (P i).IsHermitian) (hsum : ∑ i, P i = 1) (X : Matrix n n ℂ) :
    (∑ i, ∑ j, (P i - P j) * X * (P i - P j)) =
      (2 : ℝ) • ((Fintype.card κ : ℝ) • pinchingMap P X - X) := by
  have hd1 : (∑ i, ∑ _j : κ, P i * X * P i) =
      (Fintype.card κ : ℝ) • (∑ i, P i * X * P i) := by
    simp only [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [Finset.smul_sum]
  have hd2 : (∑ _i : κ, ∑ j, P j * X * P j) =
      (Fintype.card κ : ℝ) • (∑ j, P j * X * P j) := by
    simp only [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hc1 : (∑ i, ∑ j, P i * X * P j) = X := by
    calc
      (∑ i, ∑ j, P i * X * P j) = (∑ i, P i) * X * (∑ j, P j) := by
        simp only [Matrix.sum_mul, Matrix.mul_sum]
        rw [Finset.sum_comm]
      _ = X := by rw [hsum, Matrix.one_mul, Matrix.mul_one]
  have hc2 : (∑ i, ∑ j, P j * X * P i) = X := by
    rw [Finset.sum_comm]
    exact hc1
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [hd1, hd2, hc1, hc2, pinchingMap_apply P hP]
  module

theorem pinching_domination {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    ((Fintype.card κ : ℝ) • pinchingMap P X - X).PosSemidef := by
  have hpairs : (∑ i, ∑ j, (P i - P j) * X * (P i - P j)).PosSemidef := by
    apply Matrix.posSemidef_sum Finset.univ
    intro i hi
    apply Matrix.posSemidef_sum Finset.univ
    intro j hj
    have he := (hP.selfAdjoint i).sub (hP.selfAdjoint j)
    simpa only [he.eq] using hX.mul_mul_conjTranspose_same (P i - P j)
  have hs := hpairs.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [pinching_defect_sum_identity P hP.selfAdjoint hP.complete X, smul_smul] at hs
  norm_num at hs
  exact hs

theorem le_card_smul_pinching {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P)
    {X : Matrix n n ℂ} (hX : X.PosSemidef) :
    X ≤ (Fintype.card κ : ℝ) • pinchingMap P X :=
  sub_nonneg.mp (pinching_domination hP hX).nonneg

theorem projections_commute {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P)
    (i j : κ) : Commute (P i) (P j) := by
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  · show P i * P j = P j * P i
    rw [hP.orthogonal i j hij, hP.orthogonal j i (Ne.symm hij)]

theorem projector_mul_pinching {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P)
    (i : κ) (X : Matrix n n ℂ) : P i * pinchingMap P X = P i * X * P i := by
  classical
  rw [pinchingMap_apply P hP.selfAdjoint, Matrix.mul_sum]
  calc
    (∑ j, P i * (P j * X * P j)) = P i * (P i * X * P i) := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.orthogonal i j hji.symm,
          Matrix.zero_mul, Matrix.zero_mul]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    _ = P i * X * P i := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.idempotent]

theorem pinching_mul_projector {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P)
    (i : κ) (X : Matrix n n ℂ) : pinchingMap P X * P i = P i * X * P i := by
  classical
  rw [pinchingMap_apply P hP.selfAdjoint, Matrix.sum_mul]
  calc
    (∑ j, (P j * X * P j) * P i) = (P i * X * P i) * P i := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        rw [Matrix.mul_assoc, hP.orthogonal j i hji, Matrix.mul_zero]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    _ = P i * X * P i := by rw [Matrix.mul_assoc, hP.idempotent]

theorem pinching_commutes_projector {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P)
    (i : κ) (X : Matrix n n ℂ) : Commute (P i) (pinchingMap P X) := by
  show P i * pinchingMap P X = pinchingMap P X * P i
  rw [projector_mul_pinching hP, pinching_mul_projector hP]

theorem pinchingMap_idempotent {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P)
    (X : Matrix n n ℂ) : pinchingMap P (pinchingMap P X) = pinchingMap P X := by
  calc
    pinchingMap P (pinchingMap P X) = ∑ i, P i * pinchingMap P X * P i :=
      pinchingMap_apply P hP.selfAdjoint _
    _ = ∑ i, P i * X * P i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [projector_mul_pinching hP, Matrix.mul_assoc, hP.idempotent]
    _ = pinchingMap P X := (pinchingMap_apply P hP.selfAdjoint X).symm

theorem pinchingMap_fixes_commutant {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P)
    (X : Matrix n n ℂ) (hX : ∀ i, Commute (P i) X) : pinchingMap P X = X := by
  calc
    pinchingMap P X = ∑ i, P i * X * P i := pinchingMap_apply P hP.selfAdjoint X
    _ = ∑ i, X * P i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(hX i).eq, Matrix.mul_assoc, hP.idempotent]
    _ = X := by rw [← Matrix.mul_sum, hP.complete, Matrix.mul_one]

theorem pinchingMap_fixes_projection {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P)
    (i : κ) : pinchingMap P (P i) = P i :=
  pinchingMap_fixes_commutant hP (P i) (fun j => projections_commute hP j i)

def spectralCombination (P : κ → Matrix n n ℂ) (a : κ → ℂ) : Matrix n n ℂ :=
  ∑ i, a i • P i

theorem pinchingMap_fixes_spectralCombination {P : κ → Matrix n n ℂ}
    (hP : IsProjectionFamily P) (a : κ → ℂ) :
    pinchingMap P (spectralCombination P a) = spectralCombination P a := by
  change pinchingMap P (∑ i, a i • P i) = ∑ i, a i • P i
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, pinchingMap_fixes_projection hP]

theorem pinching_commutes_spectralCombination {P : κ → Matrix n n ℂ}
    (hP : IsProjectionFamily P) (a : κ → ℂ) (X : Matrix n n ℂ) :
    Commute (pinchingMap P X) (spectralCombination P a) := by
  show pinchingMap P X * (∑ i, a i • P i) = (∑ i, a i • P i) * pinchingMap P X
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  exact congrArg (fun M : Matrix n n ℂ => a i • M) (pinching_commutes_projector hP i X).eq.symm

def liftedProjections (P : κ → Matrix n n ℂ) (R : Type*) [Fintype R] [DecidableEq R] :
    κ → Matrix (n × R) (n × R) ℂ := fun i => P i ⊗ₖ (1 : Matrix R R ℂ)

theorem liftedProjections_family {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P)
    (R : Type*) [Fintype R] [DecidableEq R] :
    IsProjectionFamily (liftedProjections P R) := by
  constructor
  · intro i
    show (P i ⊗ₖ (1 : Matrix R R ℂ))ᴴ = P i ⊗ₖ (1 : Matrix R R ℂ)
    rw [Matrix.conjTranspose_kronecker, (hP.selfAdjoint i).eq, Matrix.conjTranspose_one]
  · intro i
    change (P i ⊗ₖ (1 : Matrix R R ℂ)) * (P i ⊗ₖ (1 : Matrix R R ℂ)) = _
    rw [← Matrix.mul_kronecker_mul, hP.idempotent, Matrix.one_mul]
    rfl
  · intro i j hij
    change (P i ⊗ₖ (1 : Matrix R R ℂ)) * (P j ⊗ₖ (1 : Matrix R R ℂ)) = 0
    rw [← Matrix.mul_kronecker_mul, hP.orthogonal i j hij, Matrix.zero_kronecker]
  · have hs : (∑ i, P i ⊗ₖ (1 : Matrix R R ℂ)) =
        (∑ i, P i) ⊗ₖ (1 : Matrix R R ℂ) := by
      ext x y
      simp [Matrix.sum_apply, Finset.sum_mul]
    change (∑ i, P i ⊗ₖ (1 : Matrix R R ℂ)) = 1
    rw [hs, hP.complete, Matrix.one_kronecker_one]

theorem amplifyMap_pinching_eq_lifted (P : κ → Matrix n n ℂ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (X : Matrix (n × R) (n × R) ℂ) :
    DiamondControl.amplifyMap (pinchingMap P) R X =
      pinchingMap (liftedProjections P R) X :=
  amplifyMap_pinching P R X

theorem pinching_domination_allReferences {P : κ → Matrix n n ℂ}
    (hP : IsProjectionFamily P) (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix (n × R) (n × R) ℂ} (hX : X.PosSemidef) :
    ((Fintype.card κ : ℝ) • DiamondControl.amplifyMap (pinchingMap P) R X - X).PosSemidef := by
  rw [amplifyMap_pinching_eq_lifted]
  exact pinching_domination (liftedProjections_family hP R) hX

theorem le_card_smul_pinching_allReferences {P : κ → Matrix n n ℂ}
    (hP : IsProjectionFamily P) (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix (n × R) (n × R) ℂ} (hX : X.PosSemidef) :
    X ≤ (Fintype.card κ : ℝ) • DiamondControl.amplifyMap (pinchingMap P) R X :=
  sub_nonneg.mp (pinching_domination_allReferences hP R hX).nonneg

theorem projection_posSemidef {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P)
    (i : κ) : (P i).PosSemidef := by
  simpa only [(hP.selfAdjoint i).eq, hP.idempotent i] using
    Matrix.posSemidef_conjTranspose_mul_self (P i)

theorem projection_isEffect {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P)
    (i : κ) : FlaggedStates.IsEffect (P i) := by
  have hi : (1 - P i) * (1 - P i) = 1 - P i := by
    simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hP.idempotent]
    abel
  have hz := Matrix.posSemidef_conjTranspose_mul_self (1 - P i)
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, (hP.selfAdjoint i).eq, hi] at hz
  exact ⟨projection_posSemidef hP i, hz⟩

theorem projection_branch_trace {P : κ → Matrix n n ℂ} (hP : IsProjectionFamily P)
    (i : κ) (X : Matrix n n ℂ) : (P i * X * P i).trace = (X * P i).trace := by
  rw [Matrix.trace_mul_cycle, hP.idempotent, Matrix.trace_mul_comm]

theorem projection_branch_probability_bounds {P : κ → Matrix n n ℂ}
    (hP : IsProjectionFamily P) (i : κ) {ρ : Matrix n n ℂ}
    (hρ : FlaggedStates.IsDensity ρ) :
    0 ≤ (P i * ρ * P i).trace.re ∧ (P i * ρ * P i).trace.re ≤ 1 := by
  rw [projection_branch_trace hP i]
  exact FlaggedStates.acceptanceProbability_bounds hρ (projection_isEffect hP i)

theorem sum_projection_branch_probabilities {P : κ → Matrix n n ℂ}
    (hP : IsProjectionFamily P) {ρ : Matrix n n ℂ}
    (hρ : FlaggedStates.IsDensity ρ) : (∑ i, (P i * ρ * P i).trace.re) = 1 := by
  have ht := congrArg Complex.re ((pinchingMap_tracePreserving hP ρ).trans hρ.2)
  rw [pinchingMap_apply P hP.selfAdjoint, Matrix.trace_sum, Complex.re_sum] at ht
  exact ht

theorem pinching_traceNorm_contracts {P : κ → Matrix n n ℂ}
    (hP : IsProjectionFamily P) {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    EffectPerturbation.traceNorm (pinchingMap P X) ≤ EffectPerturbation.traceNorm X :=
  EffectPerturbation.traceNorm_contracts_positive_tracePreserving (pinchingMap P)
    (fun _ h => pinchingMap_posSemidef P h) (pinchingMap_tracePreserving hP) hX

theorem pinching_traceNorm_contracts_allReferences {P : κ → Matrix n n ℂ}
    (hP : IsProjectionFamily P) (R : Type*) [Fintype R] [DecidableEq R]
    {X : Matrix (n × R) (n × R) ℂ} (hX : X.IsHermitian) :
    EffectPerturbation.traceNorm (DiamondControl.amplifyMap (pinchingMap P) R X) ≤
      EffectPerturbation.traceNorm X :=
  EffectPerturbation.traceNorm_contracts_positive_tracePreserving
    (DiamondControl.amplifyMap (pinchingMap P) R)
    (fun _ h => pinchingMap_completelyPositive_allReferences P R h)
    (pinchingMap_tracePreserving_allReferences hP R) hX

end QuantumProver.SuperchannelDiscrimination.Pinching
