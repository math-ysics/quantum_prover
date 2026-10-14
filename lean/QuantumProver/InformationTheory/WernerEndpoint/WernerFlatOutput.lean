import QuantumProver.InformationTheory.WernerEndpoint.PurityTheorems

noncomputable section

namespace QuantumProver.WernerEndpoint.WernerFlatOutput

open scoped BigOperators ComplexOrder Matrix Kronecker

def diagonalVector (d : ℕ) : Fin d × Fin d → ℂ :=
  fun ac => if ac.1 = ac.2 then 1 else 0

def diagonalKernel (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun ac be =>
    (if ac.1 = ac.2 then 1 else 0) * (if be.1 = be.2 then 1 else 0) -
    (if ac.1 = be.2 then 1 else 0) * (if be.1 = ac.2 then 1 else 0)

theorem wedgeInclusion_star (d : ℕ) (ab : Fin d × Fin d) (x : Edge d) :
    star (wedgeInclusion d ab x) = wedgeInclusion d ab x := by
  simp [wedgeInclusion]

theorem equalLabel_amplitudes_projector (d : ℕ) (c : ℂ)
    (ac be : Fin d × Fin d) :
    ((antisymmetricStinespring d).tensor (antisymmetricStinespring d)).amplitudes
      (fun xy : Edge d × Edge d => c * (if xy.1 = xy.2 then 1 else 0)) ac be =
      c * wedgeProjector d (ac.1, be.1) (ac.2, be.2) := by
  rw [Stinespring.tensor_amplitudes]
  simp only [antisymmetricStinespring]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp only [wedgeProjector, Matrix.mul_apply, Matrix.conjTranspose_apply,
    wedgeInclusion_star, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem equalLabel_amplitudes (d : ℕ) (c : ℂ) :
    ((antisymmetricStinespring d).tensor (antisymmetricStinespring d)).amplitudes
      (fun xy : Edge d × Edge d => c * (if xy.1 = xy.2 then 1 else 0)) =
      (c / 2) • diagonalKernel d := by
  ext ⟨a, k⟩ ⟨b, e⟩
  rw [equalLabel_amplitudes_projector, wedgeProjector_eq_antisymmetrizer]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    physicalSwap, diagonalKernel, smul_eq_mul, Prod.mk.injEq]
  by_cases hak : a = k <;> by_cases hbe : b = e <;>
    by_cases hae : a = e <;> by_cases hbk : b = k
  all_goals simp [hak, hbe, hae, hbk, and_comm, eq_comm] <;> simp_all <;> ring

theorem diagonalKernel_reducedLeft (d : ℕ) :
    reducedLeft (diagonalKernel d) =
      1 + ((d : ℂ) - 2) • pureDensity (diagonalVector d) := by
  ext ⟨a, k⟩ ⟨p, l⟩
  by_cases hak : a = k <;> by_cases hpl : p = l <;>
    by_cases hap : a = p <;> by_cases hkl : k = l
  all_goals
    simp [reducedLeft, crossLeft, diagonalKernel, diagonalVector, pureDensity,
      crossDensity, Fintype.sum_prod_type, endpointConj_ite, mul_sub, sub_mul,
      Finset.sum_sub_distrib, mul_ite, ite_mul, ite_and, Matrix.one_apply,
      Prod.mk.injEq, hak, hpl, hap, hkl, eq_comm, Matrix.smul_apply,
      smul_eq_mul, Matrix.add_apply] <;> simp_all <;> ring

theorem equalLabel_joint_output (d : ℕ) (c : ℂ) :
    ((antisymmetricStinespring d).tensor (antisymmetricStinespring d)).apply
      (pureDensity (fun xy : Edge d × Edge d =>
        c * (if xy.1 = xy.2 then 1 else 0))) =
      ((c * star c) / 4) •
        (1 + ((d : ℂ) - 2) • pureDensity (diagonalVector d)) := by
  rw [Stinespring.apply_pureDensity, equalLabel_amplitudes]
  simp only [reducedLeft, crossLeft_smul_left, crossLeft_smul_right, smul_smul]
  change (star (c / 2) * (c / 2)) • reducedLeft (diagonalKernel d) = _
  rw [diagonalKernel_reducedLeft]
  congr 1
  simp only [star_div₀, star_ofNat]
  ring

end QuantumProver.WernerEndpoint.WernerFlatOutput
