import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.BlockIncrement

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator

namespace QuantumProver.AmplitudeDamping.FiniteModel

theorem sandwichedTrace_unequal_flag_scalars_nonneg {I : Type*}
    [Fintype I] [DecidableEq I] {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α u v : ℝ} (hα : 1 ≤ α) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hzero : v = 0 → u = 0) :
    sandwichedTrace α (u • ρ) (v • σ) =
      u ^ α * v ^ (1 - α) * sandwichedTrace α ρ σ := by
  by_cases hvzero : v = 0
  · rw [hzero hvzero, hvzero]
    simp [sandwichedTrace_zero_input _ (by linarith : 0 < α),
      Real.zero_rpow (by linarith : α ≠ 0)]
  · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hvzero)
    rw [sandwichedTrace_smul_input hρ (v • σ) hu hα,
      sandwichedTrace_smul_comparison hρ hσ hvpos hα, ← mul_assoc]

theorem labFlagComparator_sandwichedTrace_unequal {f g a b : ℕ}
    (u v : Fin f × Fin g → ℝ) (ρ σ : Fin f × Fin g → BipartiteMatrix a b)
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (hzero : ∀ j, v j = 0 → u j = 0)
    (hρ : ∀ j, (ρ j).PosSemidef) (hσ : ∀ j, (σ j).PosSemidef)
    {α : ℝ} (hα : 1 ≤ α) :
    sandwichedTrace α (labFlagComparator u ρ) (labFlagComparator v σ) =
      ∑ j, (u j) ^ α * (v j) ^ (1 - α) * sandwichedTrace α (ρ j) (σ j) := by
  rw [labFlagComparator_sandwichedTrace_sum u v ρ σ hu hv hρ hσ]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.coe_smul, Complex.coe_smul]
  exact sandwichedTrace_unequal_flag_scalars_nonneg (hρ j) (hσ j) hα
    (hu j) (hv j) (hzero j)

theorem optimizedPhaseLawB_renyi_factor (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (α z : ℝ)
    (hα : 1 < α) (hαz : α * z = α - 1) :
    (∑ r : Fin (w + 1), (physicalPhaseLawB p w r) ^ α *
      (optimizedPhaseLawB n w p z r) ^ (1 - α) *
      (phaseComparisonConstantB n w r.val) ^ (α - 1)) =
        (Scalar.survivorMoment n w p z) ^ α := by
  have hfactor := QuantumProver.AmplitudeDamping.SecretKey.Scalar.optimized_renyi_flag_factor
    (physicalPhaseLawB p w) (fun r => phaseComparisonConstantB n w r.val) α z
    (physicalPhaseLawB_nonneg p hp0 hp1 w) (physicalPhaseLawB_sum p w)
    (fun r => phaseComparisonConstantB_pos n w r.val (Nat.le_of_lt_succ r.isLt)
      ((Nat.le_of_lt_succ r.isLt).trans hwn)) hα hαz
  rw [physical_phase_moment_eq_survivorMoment] at hfactor
  have hnum : optimizedPhaseNumeratorB n w p z =
      (fun r => physicalPhaseLawB p w r * (phaseComparisonConstantB n w r.val) ^ z) := by
    funext r
    rfl
  simpa only [optimizedPhaseLawB, hnum] using hfactor

section MatrixSector

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem fixedWeight_optimized_flagged_sandwichedTrace_le_of_order
    (n w : ℕ) (hwn : w ≤ n) (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    {ρ σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {p α z : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hα : 1 < α) (hαz : α * z = α - 1) :
    sandwichedTrace α
      (labFlagComparator (fun j : Fin 1 × Fin (w + 1) => physicalPhaseLawB p w j.2)
        (fun j => labTransferOutput (lossKrausB n w j.2.val) ρ))
      (labFlagComparator (fun j : Fin 1 × Fin (w + 1) => optimizedPhaseLawB n w p z j.2)
        (fun j => labTransferOutput (measurePhaseKrausB n w j.2.val) σ)) ≤
      (Scalar.survivorMoment n w p z) ^ α * sandwichedTrace α ρ σ := by
  rw [labFlagComparator_sandwichedTrace_unequal
    (fun j : Fin 1 × Fin (w + 1) => physicalPhaseLawB p w j.2)
    (fun j : Fin 1 × Fin (w + 1) => optimizedPhaseLawB n w p z j.2)
    (fun j => labTransferOutput (lossKrausB n w j.2.val) ρ)
    (fun j => labTransferOutput (measurePhaseKrausB n w j.2.val) σ)
    (fun j => physicalPhaseLawB_nonneg p hp0 hp1 w j.2)
    (fun j => optimizedPhaseLawB_nonneg n w hwn p hp0 hp1 z j.2)
    (fun j => optimizedPhaseLawB_support n w hwn p hp0 hp1 z j.2)
    (fun j => krausSumB_posSemidef _ hρ) (fun j => krausSumB_posSemidef _ hσ) hα.le]
  calc
    _ ≤ ∑ j : Fin 1 × Fin (w + 1), (physicalPhaseLawB p w j.2) ^ α *
        (optimizedPhaseLawB n w p z j.2) ^ (1 - α) *
        ((phaseComparisonConstantB n w j.2.val) ^ (α - 1) * sandwichedTrace α ρ σ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hrw : j.2.val ≤ w := Nat.le_of_lt_succ j.2.isLt
      exact mul_le_mul_of_nonneg_left
        (fixedWeight_sandwichedTrace_phase_le_input_of_posSemidef n w j.2.val
          hrw (hrw.trans hwn) hA hB hρ hσ hs hα)
        (mul_nonneg
          (Real.rpow_nonneg (physicalPhaseLawB_nonneg p hp0 hp1 w j.2) α)
          (Real.rpow_nonneg (optimizedPhaseLawB_nonneg n w hwn p hp0 hp1 z j.2) (1 - α)))
    _ = _ := by
      simp only [Fintype.sum_prod_type, Fin.sum_univ_one, ← mul_assoc, ← Finset.sum_mul]
      rw [optimizedPhaseLawB_renyi_factor n w hwn p hp0 hp1 α z hα hαz]

theorem fixedWeight_optimized_flagged_sandwichedTrace_le
    (n w : ℕ) (hwn : w ≤ n) (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    {ρ σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {p z : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hz0 : 0 < z) (hz1 : z < 1) :
    sandwichedTrace (1 / (1 - z))
      (labFlagComparator (fun j : Fin 1 × Fin (w + 1) => physicalPhaseLawB p w j.2)
        (fun j => labTransferOutput (lossKrausB n w j.2.val) ρ))
      (labFlagComparator (fun j : Fin 1 × Fin (w + 1) => optimizedPhaseLawB n w p z j.2)
        (fun j => labTransferOutput (measurePhaseKrausB n w j.2.val) σ)) ≤
      (Scalar.survivorMoment n w p z) ^ (1 / (1 - z)) *
        sandwichedTrace (1 / (1 - z)) ρ σ := by
  have hd : 0 < 1 - z := sub_pos.mpr hz1
  have hα : 1 < 1 / (1 - z) := (lt_div_iff₀ hd).mpr (by linarith)
  have hαz : (1 / (1 - z)) * z = 1 / (1 - z) - 1 := by
    field_simp [hd.ne']
    ring
  exact fixedWeight_optimized_flagged_sandwichedTrace_le_of_order
    n w hwn hA hB hρ hσ hs hp0 hp1 hα hαz

end MatrixSector
end QuantumProver.AmplitudeDamping.FiniteModel
