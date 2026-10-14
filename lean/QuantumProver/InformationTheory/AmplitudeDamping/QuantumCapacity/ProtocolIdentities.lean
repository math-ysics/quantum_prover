import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.Definitions

set_option autoImplicit false

namespace QuantumProver.AmplitudeDamping.Identities

open QuantumProver.AmplitudeDamping.FiniteModel

open scoped BigOperators ComplexConjugate Matrix

theorem bellProjector_trace (d : ℕ) (hd : 0 < d) :
    (bellProjector d).trace = 1 := by
  classical
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  simp [Matrix.trace, bellProjector, Fintype.sum_prod_type, hdc]

theorem bellProjector_isHermitian (d : ℕ) : (bellProjector d).IsHermitian := by
  ext x y
  by_cases hx : x.1 = x.2 <;> by_cases hy : y.1 = y.2 <;>
    simp [Matrix.conjTranspose_apply, bellProjector, hx, hy, and_comm]

theorem bellOverlap_zero (d : ℕ) : bellOverlap d 0 = 0 := by
  simp [bellOverlap]

theorem done_bellOverlap (p : ℝ) (d : ℕ) (ρ : BipartiteMatrix d d) :
    bellOverlap d ((FiniteProtocol.done (p := p) d d).output ρ) = bellOverlap d ρ := rfl

end QuantumProver.AmplitudeDamping.Identities

noncomputable section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

namespace QuantumProver.AmplitudeDamping.TracePower

variable {I : Type*} [Fintype I] [DecidableEq I]

def entryWeight (M : Matrix I I ℂ) (i j : I) : ℝ := Complex.normSq (M i j)

omit [Fintype I] [DecidableEq I] in
theorem entryWeight_nonneg (M : Matrix I I ℂ) (i j : I) :
    0 ≤ entryWeight M i j := Complex.normSq_nonneg _

theorem entryWeight_row_le (M : Matrix I I ℂ) (hM : M * Mᴴ ≤ 1) (i : I) :
    ∑ j, entryWeight M i j ≤ 1 := by
  have hd := (Complex.nonneg_iff.mp
    ((Matrix.le_iff.mp hM).diag_nonneg (i := i))).1
  have h : 0 ≤ 1 - ∑ j, entryWeight M i j := by
    simpa [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.mul_conj, Complex.re_sum, entryWeight] using hd
  linarith

theorem entryWeight_col_le (M : Matrix I I ℂ) (hM : Mᴴ * M ≤ 1) (j : I) :
    ∑ i, entryWeight M i j ≤ 1 := by
  have hd := (Complex.nonneg_iff.mp
    ((Matrix.le_iff.mp hM).diag_nonneg (i := j))).1
  have h : 0 ≤ 1 - ∑ i, entryWeight M i j := by
    simpa [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, ← Complex.normSq_eq_conj_mul_self,
      Complex.re_sum, entryWeight] using hd
  linarith

omit [DecidableEq I] in
theorem substochastic_rpow_sum_le (W : I → I → ℝ) (x : I → ℝ) {α : ℝ}
    (hα : 1 ≤ α) (hW : ∀ i j, 0 ≤ W i j) (hx : ∀ j, 0 ≤ x j)
    (hrow : ∀ i, ∑ j, W i j ≤ 1) (hcol : ∀ j, ∑ i, W i j ≤ 1) :
    ∑ i, (∑ j, W i j * x j) ^ α ≤ ∑ j, (x j) ^ α := by
  have hzero : (0 : ℝ) ^ α = 0 := Real.zero_rpow (by linarith)
  have hJ (i : I) : (∑ j, W i j * x j) ^ α ≤ ∑ j, W i j * (x j) ^ α := by
    have hh := (convexOn_rpow hα).map_add_sum_le
      (t := Finset.univ) (w := fun j => W i j) (p := x)
      (v := 1 - ∑ j, W i j) (q := 0)
      (fun j _ => hW i j) (by ring) (fun j _ => hx j)
      (sub_nonneg.mpr (hrow i)) (by simp only [Set.mem_Ici]; exact le_rfl)
    simpa only [smul_eq_mul, mul_zero, zero_add, hzero] using hh
  calc
    _ ≤ ∑ i, ∑ j, W i j * (x j) ^ α := Finset.sum_le_sum fun i _ => hJ i
    _ = ∑ j, (∑ i, W i j) * (x j) ^ α := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ ∑ j, 1 * (x j) ^ α := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hcol j) (Real.rpow_nonneg (hx j) α)
    _ = _ := by simp only [one_mul]

theorem cfc_spectral (f : ℝ → ℝ) {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    cfc f X = Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) hX.eigenvectorUnitary
      (Matrix.diagonal (fun i => (f (hX.eigenvalues i) : ℂ))) := by
  rw [hX.cfc_eq f]
  rfl

theorem trace_unitary_conjugate (U : Matrix.unitaryGroup I ℂ) (X : Matrix I I ℂ) :
    (Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) U X).trace = X.trace := by
  change ((U : Matrix I I ℂ) * X * (U : Matrix I I ℂ)ᴴ).trace = X.trace
  rw [Matrix.trace_mul_cycle]
  have hU : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  rw [hU, Matrix.one_mul]

theorem trace_rpow_eq_sum {X : Matrix I I ℂ} (hX : X.PosSemidef) (α : ℝ) :
    (CFC.rpow X α).trace.re = ∑ i, (hX.1.eigenvalues i) ^ α := by
  have heq : CFC.rpow X α = cfc (fun x : ℝ => x ^ α) X :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := X) (y := α) hX.nonneg
  rw [heq, cfc_spectral _ hX.1,
    trace_unitary_conjugate, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re]

theorem sandwich_diagonal_re (M : Matrix I I ℂ) (x : I → ℝ) (i : I) :
    ((M * Matrix.diagonal (fun j => (x j : ℂ)) * Mᴴ) i i).re =
      ∑ j, entryWeight M i j * x j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [entryWeight, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem trace_rpow_contraction {X C : Matrix I I ℂ} (hX : X.PosSemidef)
    (hleft : Cᴴ * C ≤ 1) (hright : C * Cᴴ ≤ 1) {α : ℝ} (hα : 1 ≤ α) :
    (CFC.rpow (C * X * Cᴴ) α).trace.re ≤ (CFC.rpow X α).trace.re := by
  let Y := C * X * Cᴴ
  have hY : Y.PosSemidef := hX.mul_mul_conjTranspose_same C
  let UX : Matrix.unitaryGroup I ℂ := hX.1.eigenvectorUnitary
  let UY : Matrix.unitaryGroup I ℂ := hY.1.eigenvectorUnitary
  let M : Matrix I I ℂ := (UY : Matrix I I ℂ)ᴴ * C * (UX : Matrix I I ℂ)
  have hUX : (UX : Matrix I I ℂ) * (UX : Matrix I I ℂ)ᴴ = 1 :=
    Unitary.coe_mul_star_self UX
  have hUY : (UY : Matrix I I ℂ) * (UY : Matrix I I ℂ)ᴴ = 1 :=
    Unitary.coe_mul_star_self UY
  have hMleft : Mᴴ * M ≤ 1 := by
    have hgram : Mᴴ * M = (UX : Matrix I I ℂ)ᴴ * (Cᴴ * C) *
        (UX : Matrix I I ℂ) := by
      dsimp only [M]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc
        _ = (UX : Matrix I I ℂ)ᴴ * Cᴴ *
            ((UY : Matrix I I ℂ) * (UY : Matrix I I ℂ)ᴴ) * C *
              (UX : Matrix I I ℂ) := by noncomm_ring
        _ = _ := by rw [hUY]; noncomm_ring
    rw [hgram]
    calc
      _ ≤ (UX : Matrix I I ℂ)ᴴ * 1 * (UX : Matrix I I ℂ) :=
        star_left_conjugate_le_conjugate hleft (UX : Matrix I I ℂ)
      _ = 1 := by rw [Matrix.mul_one]; exact Unitary.coe_star_mul_self UX
  have hMright : M * Mᴴ ≤ 1 := by
    have hgram : M * Mᴴ = (UY : Matrix I I ℂ)ᴴ * (C * Cᴴ) *
        (UY : Matrix I I ℂ) := by
      dsimp only [M]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc
        _ = (UY : Matrix I I ℂ)ᴴ * C *
            ((UX : Matrix I I ℂ) * (UX : Matrix I I ℂ)ᴴ) * Cᴴ *
              (UY : Matrix I I ℂ) := by noncomm_ring
        _ = _ := by rw [hUX]; noncomm_ring
    rw [hgram]
    calc
      _ ≤ (UY : Matrix I I ℂ)ᴴ * 1 * (UY : Matrix I I ℂ) :=
        star_left_conjugate_le_conjugate hright (UY : Matrix I I ℂ)
      _ = 1 := by rw [Matrix.mul_one]; exact Unitary.coe_star_mul_self UY
  have hsX : X = (UX : Matrix I I ℂ) *
      Matrix.diagonal (fun j => (hX.1.eigenvalues j : ℂ)) *
        (UX : Matrix I I ℂ)ᴴ := hX.1.spectral_theorem
  have hsY : (UY : Matrix I I ℂ)ᴴ * Y * (UY : Matrix I I ℂ) =
      Matrix.diagonal (fun i => (hY.1.eigenvalues i : ℂ)) :=
    by simpa [UY, Unitary.conjStarAlgAut_star_apply, Function.comp_def,
      Matrix.star_eq_conjTranspose] using
      hY.1.conjStarAlgAut_star_eigenvectorUnitary
  have hdiag : M * Matrix.diagonal (fun j => (hX.1.eigenvalues j : ℂ)) * Mᴴ =
      Matrix.diagonal (fun i => (hY.1.eigenvalues i : ℂ)) := by
    calc
      _ = (UY : Matrix I I ℂ)ᴴ *
          (C * ((UX : Matrix I I ℂ) *
            Matrix.diagonal (fun j => (hX.1.eigenvalues j : ℂ)) *
              (UX : Matrix I I ℂ)ᴴ) * Cᴴ) * (UY : Matrix I I ℂ) := by
        dsimp only [M]
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        noncomm_ring
      _ = (UY : Matrix I I ℂ)ᴴ * Y * (UY : Matrix I I ℂ) := by rw [← hsX]
      _ = _ := hsY
  have heigen (i : I) : hY.1.eigenvalues i =
      ∑ j, entryWeight M i j * hX.1.eigenvalues j := by
    have hi := congrArg (fun A : Matrix I I ℂ => (A i i).re) hdiag
    simpa only [sandwich_diagonal_re, Matrix.diagonal_apply_eq, Complex.ofReal_re]
      using hi.symm
  change (CFC.rpow Y α).trace.re ≤ _
  rw [trace_rpow_eq_sum hY, trace_rpow_eq_sum hX]
  simp_rw [heigen]
  exact substochastic_rpow_sum_le (entryWeight M) hX.1.eigenvalues hα
    (entryWeight_nonneg M) (hX.eigenvalues_nonneg)
    (entryWeight_row_le M hMright) (entryWeight_col_le M hMleft)

end QuantumProver.AmplitudeDamping.TracePower
