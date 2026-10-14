import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QuantumProver.SandwichedDPI

open QuantumProver.SuperchannelDiscrimination
open KrausCompletion CPWrappers CPJensen CPSchwarz

variable {I O Z : Type*} [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O]

private theorem bottomBlock_posSemidef {D : Matrix O O ℂ} (hD : D.PosSemidef) :
    (Matrix.fromBlocks (0 : Matrix O O ℂ) 0 0 D).PosSemidef := by
  let J : Matrix O (O ⊕ O) ℂ := fun i s =>
    Sum.elim (fun _ => 0) (fun j => if i = j then 1 else 0) s
  have h := hD.conjTranspose_mul_mul_same J
  have heq : Jᴴ * D * J = Matrix.fromBlocks (0 : Matrix O O ℂ) 0 0 D := by
    ext u v
    change (∑ k, (∑ l, star (J l u) * D l k) * J k v) = _
    cases u <;> cases v <;> simp [J, Matrix.fromBlocks, mul_ite, ite_mul]
  rwa [heq] at h

theorem subunital_kadison_schwarz {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) (hsub : Φ 1 ≤ 1) (X : Matrix I I ℂ) :
    (Φ (Xᴴ * X) - (Φ X)ᴴ * Φ X).PosSemidef := by
  let : Invertible (1 : Matrix O O ℂ) := invertibleOne
  have hblock := completelyPositive_positive (completelyPositive_flagLiftMap hΦ)
    (gramBlock_posSemidef X)
  rw [flagLiftMap_fromBlocks, map_conjTranspose hΦ X] at hblock
  have hdeficit := bottomBlock_posSemidef (Matrix.le_iff.mp hsub)
  have hblock' : (Matrix.fromBlocks (Φ (Xᴴ * X)) (Φ X)ᴴ (Φ X)
      (1 : Matrix O O ℂ)).PosSemidef := by
    convert hblock.add hdeficit using 1
    rw [Matrix.fromBlocks_add]
    simp
  have h := (Matrix.PosDef.fromBlocks₂₂ (Φ (Xᴴ * X)) ((Φ X)ᴴ)
    (Matrix.PosDef.one : (1 : Matrix O O ℂ).PosDef)).mp (by simpa using hblock')
  simpa using h

private def cpPositiveMap (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (hΦ : CompletelyPositive Φ) : Matrix I I ℂ →ₚ[ℂ] Matrix O O ℂ where
  toLinearMap := Φ
  monotone' := by
    intro A B hAB
    have h := completelyPositive_positive hΦ (Matrix.le_iff.mp hAB)
    change Φ A ≤ Φ B
    apply Matrix.le_iff.mpr
    rw [map_sub] at h
    exact h

theorem norm_map_le_of_subunital_cp {Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ}
    (hΦ : CompletelyPositive Φ) (hsub : Φ 1 ≤ 1) (X : Matrix I I ℂ) :
    ‖Φ X‖ ≤ ‖X‖ := by
  have hΦ1 := completelyPositive_positive hΦ
    (Matrix.PosSemidef.one : (1 : Matrix I I ℂ).PosSemidef)
  have hn1 : ‖Φ 1‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (Φ 1) hΦ1.nonneg).mpr hsub
  have hnorm : ‖(Φ X)ᴴ * Φ X‖ ≤ ‖Xᴴ * X‖ := by
    calc
      ‖(Φ X)ᴴ * Φ X‖ ≤ ‖Φ (Xᴴ * X)‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg
          (Matrix.le_iff.mpr (subunital_kadison_schwarz hΦ hsub X))
          (Matrix.posSemidef_conjTranspose_mul_self (Φ X)).nonneg
      _ ≤ ‖Φ 1‖ * ‖Xᴴ * X‖ :=
        PositiveLinearMap.norm_apply_le_of_nonneg (cpPositiveMap Φ hΦ) _
          (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
      _ ≤ 1 * ‖Xᴴ * X‖ := mul_le_mul_of_nonneg_right hn1 (norm_nonneg _)
      _ = ‖Xᴴ * X‖ := one_mul _
  have hsq : ‖Φ X‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    simpa only [← Matrix.star_eq_conjTranspose, CStarRing.norm_star_mul_self,
      ← pow_two] using hnorm
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem inverse_sqrt_sandwich_le_one {A : Matrix O O ℂ} (hA : A.PosSemidef) :
    CFC.rpow A (-1 / 2 : ℝ) * A * CFC.rpow A (-1 / 2 : ℝ) ≤ 1 := by
  let g : ℝ → ℝ := fun x => x ^ (-1 / 2 : ℝ)
  have hg : ContinuousOn g (spectrum ℝ A) := A.finite_real_spectrum.continuousOn _
  have hgi : ContinuousOn (fun x : ℝ => g x * x) (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn _
  have hi : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA.1
  have hp1 : cfc (fun x : ℝ => g x * x) A = cfc g A * A := by
    calc
      cfc (fun x : ℝ => g x * x) A = cfc g A * cfc (fun x : ℝ => x) A :=
        cfc_mul g (fun x : ℝ => x) A hg continuousOn_id
      _ = cfc g A * A := congrArg (fun B : Matrix O O ℂ => cfc g A * B) hi
  have hp2 : cfc (fun x : ℝ => g x * x * g x) A =
      cfc (fun x : ℝ => g x * x) A * cfc g A :=
    cfc_mul (fun x : ℝ => g x * x) g A hgi hg
  have hpow : CFC.rpow A (-1 / 2 : ℝ) = cfc g A :=
    CFC.rpow_eq_cfc_real (A := Matrix O O ℂ) (a := A) (y := (-1 / 2 : ℝ)) hA.nonneg
  rw [hpow, ← hp1, ← hp2]
  apply cfc_le_one
  intro x hx
  have hx0 : 0 ≤ x := by
    obtain ⟨i, rfl⟩ := hA.1.spectrum_real_eq_range_eigenvalues ▸ hx
    exact hA.eigenvalues_nonneg i
  by_cases hxzero : x = 0
  · simp [g, hxzero]
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hxzero)
    have hscalar : g x * x * g x = 1 := by
      change x ^ (-1 / 2 : ℝ) * x * x ^ (-1 / 2 : ℝ) = 1
      calc
        x ^ (-1 / 2 : ℝ) * x * x ^ (-1 / 2 : ℝ) =
            x ^ (-1 / 2 : ℝ) * x ^ (1 : ℝ) * x ^ (-1 / 2 : ℝ) := by
          rw [Real.rpow_one]
        _ = x ^ ((-1 / 2 : ℝ) + 1 + (-1 / 2 : ℝ)) := by
          rw [Real.rpow_add hxpos, Real.rpow_add hxpos]
        _ = 1 := by norm_num
    exact hscalar.le

variable [Fintype Z]

def normalizedKraus (K : Z → Matrix O I ℂ) (σ : Matrix I I ℂ) :
    Z → Matrix O I ℂ := fun z =>
  CFC.rpow (krausAction K σ) (-1 / 2 : ℝ) * K z * CFC.sqrt σ

theorem normalizedKraus_action (K : Z → Matrix O I ℂ) (σ X : Matrix I I ℂ) :
    krausAction (normalizedKraus K σ) X =
      CFC.rpow (krausAction K σ) (-1 / 2 : ℝ) *
        krausAction K (CFC.sqrt σ * X * CFC.sqrt σ) *
        CFC.rpow (krausAction K σ) (-1 / 2 : ℝ) := by
  have hV : (CFC.sqrt σ).IsHermitian := (CFC.sqrt_nonneg σ).posSemidef.1
  have hS : (CFC.rpow (krausAction K σ) (-1 / 2 : ℝ)).IsHermitian :=
    (CFC.rpow_nonneg : 0 ≤ CFC.rpow (krausAction K σ) (-1 / 2 : ℝ)).posSemidef.1
  change (∑ z, (CFC.rpow (krausAction K σ) (-1 / 2 : ℝ) * K z * CFC.sqrt σ) * X *
      (CFC.rpow (krausAction K σ) (-1 / 2 : ℝ) * K z * CFC.sqrt σ)ᴴ) =
    CFC.rpow (krausAction K σ) (-1 / 2 : ℝ) *
      (∑ z, K z * (CFC.sqrt σ * X * CFC.sqrt σ) * (K z)ᴴ) *
      CFC.rpow (krausAction K σ) (-1 / 2 : ℝ)
  simp only [Matrix.conjTranspose_mul, hV.eq, hS.eq,
    Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [Matrix.mul_assoc]

theorem normalizedKraus_subunital (K : Z → Matrix O I ℂ) {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) : krausAction (normalizedKraus K σ) 1 ≤ 1 := by
  rw [normalizedKraus_action, Matrix.mul_one, CFC.sqrt_mul_sqrt_self σ hσ.nonneg]
  exact inverse_sqrt_sandwich_le_one (krausAction_posSemidef K hσ)

theorem normalizedKraus_gram_le_one (K : Z → Matrix O I ℂ) {σ : Matrix I I ℂ}
    (hσ : σ.PosSemidef) :
    (∑ z, normalizedKraus K σ z * (normalizedKraus K σ z)ᴴ) ≤ 1 := by
  simpa only [krausAction, Matrix.mul_one] using normalizedKraus_subunital K hσ

theorem norm_normalizedKraus_action_le (K : Z → Matrix O I ℂ)
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) (X : Matrix I I ℂ) :
    ‖krausAction (normalizedKraus K σ) X‖ ≤ ‖X‖ := by
  apply norm_map_le_of_subunital_cp
    (Φ := krausMap (normalizedKraus K σ))
  · intro r A hA
    exact krausMap_completelyPositive (normalizedKraus K σ) (Fin r) hA
  · exact normalizedKraus_subunital K hσ

theorem norm_inverse_sqrt_kraus_conjugation_le (K : Z → Matrix O I ℂ)
    {σ : Matrix I I ℂ} (hσ : σ.PosSemidef) (X : Matrix I I ℂ) :
    ‖CFC.rpow (krausAction K σ) (-1 / 2 : ℝ) *
        krausAction K (CFC.sqrt σ * X * CFC.sqrt σ) *
        CFC.rpow (krausAction K σ) (-1 / 2 : ℝ)‖ ≤ ‖X‖ := by
  rw [← normalizedKraus_action]
  exact norm_normalizedKraus_action_le K hσ X

end QuantumProver.SandwichedDPI
