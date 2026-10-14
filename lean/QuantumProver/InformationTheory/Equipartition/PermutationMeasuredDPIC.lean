import QuantumProver.InformationTheory.Equipartition.PermutationSpectrum

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace QuantumProver.Equipartition.FiniteModel.PermutationMeasured
open Testing PermutationSpectrum

theorem tracePair_sitePermute_both {d n : ℕ} (p : Equiv.Perm (Fin n))
    (A B : QMat d n) : tracePair (sitePermute p A) (sitePermute p B) = tracePair A B := by
  let e := wordSitePermEquiv (d := d) p
  change (Matrix.trace (A.submatrix e e * B.submatrix e e)).re = _
  rw [Matrix.submatrix_mul_equiv]
  have ht : Matrix.trace ((A * B).submatrix e e) = Matrix.trace (A * B) :=
    Equiv.sum_comp e (fun i => (A * B) i i)
  exact congrArg Complex.re ht

theorem tracePair_sitePermute_left {d n : ℕ} (p : Equiv.Perm (Fin n))
    (A B : QMat d n) : tracePair (sitePermute p A) B = tracePair A (sitePermute p.symm B) := by
  have h := tracePair_sitePermute_both p A (sitePermute p.symm B)
  have hc : sitePermute p (sitePermute p.symm B) = B := by
    ext x y
    simp [sitePermute]
  rw [hc] at h
  exact h

theorem tracePair_real_smul_left {ι : Type*} [Fintype ι]
    (a : ℝ) (A B : CMat ι) : tracePair (a • A) B = a * tracePair A B := by
  simp only [tracePair, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

theorem tracePair_real_smul_right {ι : Type*} [Fintype ι]
    (a : ℝ) (A B : CMat ι) : tracePair A (a • B) = a * tracePair A B := by
  simp only [tracePair, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

theorem tracePair_siteAverage_left {d n : ℕ} (A B : QMat d n) :
    tracePair (siteAverage A) B = tracePair A (siteAverage B) := by
  rw [siteAverage, tracePair_real_smul_left, tracePair_sum_left]
  simp only [tracePair_sitePermute_left]
  have hi : (∑ p : Equiv.Perm (Fin n), tracePair A (sitePermute p.symm B)) =
      ∑ p : Equiv.Perm (Fin n), tracePair A (sitePermute p B) :=
    Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n))) (fun p => tracePair A (sitePermute p B))
  rw [hi, siteAverage, tracePair_real_smul_right, tracePair_sum_right]

theorem siteAverage_posSemidef {d n : ℕ} {A : QMat d n} (hA : A.PosSemidef) :
    (siteAverage A).PosSemidef := by
  have hs : (∑ p : Equiv.Perm (Fin n), sitePermute p A).PosSemidef :=
    Matrix.posSemidef_sum _ (fun p _ => hA.submatrix (wordSitePermEquiv p))
  exact Matrix.nonneg_iff_posSemidef.mp
    (smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hs.nonneg)

theorem siteAverage_one (d n : ℕ) : siteAverage (1 : QMat d n) = 1 := by
  have h1 (p : Equiv.Perm (Fin n)) : sitePermute p (1 : QMat d n) = 1 :=
    (reindexStarAlgHom (wordSitePermEquiv p)).map_one
  have hv : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [siteAverage]
  simp only [h1, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hv, one_smul]

theorem siteAverage_sum {d n : ℕ} {κ : Type*} [Fintype κ] (A : κ → QMat d n) :
    siteAverage (∑ k, A k) = ∑ k, siteAverage (A k) := by
  simp only [siteAverage, sitePermute_sum, Finset.smul_sum]
  rw [Finset.sum_comm]

def siteAveragePOVM {d n L : ℕ} (M : FinitePOVM (Word d n) L) :
    FinitePOVM (Word d n) L where
  outcome i := siteAverage (M.outcome i)
  positive i := siteAverage_posSemidef (M.positive i)
  sum_outcome := by rw [← siteAverage_sum, M.sum_outcome, siteAverage_one]

theorem measurementMass_siteAveragePOVM {d n L : ℕ}
    (M : FinitePOVM (Word d n) L) (A : QMat d n) :
    measurementMass (siteAveragePOVM M) A = measurementMass M (siteAverage A) := by
  funext i
  change tracePair A (siteAverage (M.outcome i)) = tracePair (siteAverage A) (M.outcome i)
  exact (tracePair_siteAverage_left A (M.outcome i)).symm

theorem measuredDivergence_siteAverage_le {d n : ℕ} (ρ σ : QMat d n) (α : ℝ) :
    measuredDivergence (siteAverage ρ) (siteAverage σ) α ≤ measuredDivergence ρ σ α := by
  unfold measuredDivergence
  apply sSup_le
  rintro z ⟨L, M, rfl⟩
  rw [← measurementMass_siteAveragePOVM M ρ, ← measurementMass_siteAveragePOVM M σ]
  exact le_sSup ⟨L, siteAveragePOVM M, rfl⟩

theorem physical_dimension_pos {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) : 0 < d := by
  obtain ⟨ρ, hρ⟩ := hF.null_nonempty n hn
  let x : Word d n := Classical.choice (isState_nonempty_index (hF.null_states n hn ρ hρ))
  exact (Nat.zero_le (x ⟨0, hn⟩).val).trans_lt (x ⟨0, hn⟩).isLt

theorem physical_set_sandwich_sub_pinchingOverhead_le_measured {d n : ℕ}
    {F : QuantumFamilies d} (hF : PhysicalAssumptions F) (hn : 0 < n)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    setSandwichedDivergence F n α - (pinchingOverhead d n : EReal) ≤
      setMeasuredDivergence F n α := by
  unfold setMeasuredDivergence
  apply le_sInf
  rintro z ⟨ρ, hρ, σ, hσ, rfl⟩
  have hr := siteAverage_mem_null hF hn hρ
  have hs := siteAverage_mem_alternative hF hn hσ
  have hi : setSandwichedDivergence F n α ≤
      sandwichedDivergence (siteAverage ρ) (siteAverage σ) α :=
    sInf_le ⟨siteAverage ρ, hr, siteAverage σ, hs, rfl⟩
  have hp := physical_pair_sandwich_sub_polynomialLog_le_measured
    hF hn hr hs (siteAverage_invariant σ) hα hα1
  have hg : (((d : ℝ) ^ 2 * blockLog n : ℝ) : EReal) ≤
      (pinchingOverhead d n : EReal) :=
    EReal.coe_le_coe (polynomialLog_le_pinchingOverhead (physical_dimension_pos hF hn))
  exact (EReal.sub_le_sub hi hg).trans (hp.trans (measuredDivergence_siteAverage_le ρ σ α))

end QuantumProver.Equipartition.FiniteModel.PermutationMeasured
