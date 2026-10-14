import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.FlaggedStates

set_option autoImplicit false

noncomputable section
open Matrix Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

namespace QuantumProver.SuperchannelDiscrimination.PetzMoments

variable {I : Type*} [Fintype I] [DecidableEq I]

def overlapWeight (U : Matrix.unitaryGroup I ℂ) (i j : I) : ℝ :=
  Complex.normSq ((U : Matrix I I ℂ) i j)

def overlapUnitary {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Matrix.unitaryGroup I ℂ := star hA.eigenvectorUnitary * hB.eigenvectorUnitary

theorem overlapWeight_nonneg (U : Matrix.unitaryGroup I ℂ) (i j : I) :
    0 ≤ overlapWeight U i j := Complex.normSq_nonneg _

theorem overlapWeight_sum_row (U : Matrix.unitaryGroup I ℂ) (i : I) :
    ∑ j, overlapWeight U i j = 1 := by
  have hu : (U : Matrix I I ℂ) * (U : Matrix I I ℂ)ᴴ = 1 :=
    Unitary.coe_mul_star_self U
  have hi := congrArg (fun M : Matrix I I ℂ => (M i i).re) hu
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj,
    Complex.re_sum, overlapWeight] using hi

theorem overlapWeight_sum_col (U : Matrix.unitaryGroup I ℂ) (j : I) :
    ∑ i, overlapWeight U i j = 1 := by
  have hu : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  have hj := congrArg (fun M : Matrix I I ℂ => (M j j).re) hu
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_sum, overlapWeight] using hj

theorem overlap_sum_rows (U : Matrix.unitaryGroup I ℂ) (a : I → ℝ) :
    ∑ i, ∑ j, a i * overlapWeight U i j = ∑ i, a i := by
  simp_rw [← Finset.mul_sum, overlapWeight_sum_row, mul_one]

theorem overlap_sum_cols (U : Matrix.unitaryGroup I ℂ) (b : I → ℝ) :
    ∑ i, ∑ j, b j * overlapWeight U i j = ∑ j, b j := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, overlapWeight_sum_col, mul_one]

theorem cfc_spectral (f : ℝ → ℝ) {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    cfc f A = Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) hA.eigenvectorUnitary
      (Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ))) := by
  rw [hA.cfc_eq f]
  rfl

theorem trace_unitary_conjugate (U : Matrix.unitaryGroup I ℂ) (X : Matrix I I ℂ) :
    (Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) U X).trace = X.trace := by
  change ((U : Matrix I I ℂ) * X * (U : Matrix I I ℂ)ᴴ).trace = X.trace
  rw [Matrix.trace_mul_cycle]
  have hu : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  rw [hu, Matrix.one_mul]

theorem trace_cfc_eq_sum (f : ℝ → ℝ) {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    (cfc f A).trace.re = ∑ i, f (hA.eigenvalues i) := by
  rw [cfc_spectral f hA, trace_unitary_conjugate, Matrix.trace_diagonal]
  simp [Complex.re_sum]

theorem trace_eq_sum_eigenvalues_re {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    A.trace.re = ∑ i, hA.eigenvalues i := by
  rw [hA.trace_eq_sum_eigenvalues]
  simp [Complex.re_sum]

theorem trace_diagonal_overlap (U : Matrix.unitaryGroup I ℂ) (a b : I → ℝ) :
    (Matrix.diagonal (fun i => (a i : ℂ)) *
      Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) U
        (Matrix.diagonal (fun j => (b j : ℂ)))).trace.re =
      ∑ i, ∑ j, a i * b j * overlapWeight U i j := by
  change (Matrix.diagonal (fun i => (a i : ℂ)) *
    ((U : Matrix I I ℂ) * Matrix.diagonal (fun j => (b j : ℂ)) *
      (U : Matrix I I ℂ)ᴴ)).trace.re = _
  have hentry (i : I) : (Matrix.diagonal (fun i => (a i : ℂ)) *
      ((U : Matrix I I ℂ) * Matrix.diagonal (fun j => (b j : ℂ)) *
        (U : Matrix I I ℂ)ᴴ)) i i =
      ∑ j, (a i : ℂ) * (((U : Matrix I I ℂ) i j * (b j : ℂ)) *
        starRingEnd ℂ ((U : Matrix I I ℂ) i j)) := by
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Finset.mul_sum,
      Complex.star_def]
  simp only [Matrix.trace, Matrix.diag, hentry, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have h : (a i : ℂ) * (((U : Matrix I I ℂ) i j * (b j : ℂ)) *
      starRingEnd ℂ ((U : Matrix I I ℂ) i j)) =
      ((a i * b j : ℝ) : ℂ) *
        ((U : Matrix I I ℂ) i j * starRingEnd ℂ ((U : Matrix I I ℂ) i j)) := by
    push_cast
    ring
  rw [h, Complex.mul_conj, Complex.re_ofReal_mul]
  rfl

theorem trace_cfc_mul_cfc_eq_overlap (f g : ℝ → ℝ) {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (cfc f A * cfc g B).trace.re =
      ∑ i, ∑ j, f (hA.eigenvalues i) * g (hB.eigenvalues j) *
        overlapWeight (overlapUnitary hA hB) i j := by
  have hu : hA.eigenvectorUnitary * overlapUnitary hA hB = hB.eigenvectorUnitary := by
    simp [overlapUnitary, ← mul_assoc]
  have hp : cfc f A * cfc g B =
      Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *
          Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) (overlapUnitary hA hB)
            (Matrix.diagonal (fun j => (g (hB.eigenvalues j) : ℂ)))) := by
    rw [map_mul, ← Unitary.conjStarAlgAut_mul_apply, hu,
      ← cfc_spectral f hA, ← cfc_spectral g hB]
  rw [hp, trace_unitary_conjugate, trace_diagonal_overlap]

theorem trace_mul_cfc_eq_overlap (f : ℝ → ℝ) {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * cfc f B).trace.re =
      ∑ i, ∑ j, hA.eigenvalues i * f (hB.eigenvalues j) *
        overlapWeight (overlapUnitary hA hB) i j := by
  simpa only [cfc_id' (p := IsSelfAdjoint) ℝ A hA] using
    trace_cfc_mul_cfc_eq_overlap (fun x : ℝ => x) f hA hB

theorem trace_cfc_mul_cfc_real (f g : ℝ → ℝ) (A B : Matrix I I ℂ) :
    (cfc f A * cfc g B).trace = (((cfc f A * cfc g B).trace.re : ℝ) : ℂ) := by
  have hf : (cfc f A).IsHermitian := cfc_predicate (p := IsSelfAdjoint) f A
  have hg : (cfc g B).IsHermitian := cfc_predicate (p := IsSelfAdjoint) g B
  have hs : star (cfc f A * cfc g B).trace = (cfc f A * cfc g B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hf.eq, hg.eq,
      Matrix.trace_mul_comm]
  have him : (cfc f A * cfc g B).trace.im = 0 := by
    have h := congrArg Complex.im hs
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  apply Complex.ext <;> simp [him]

def petzMoment (ρ σ : Matrix I I ℂ) (s : ℝ) : ℝ :=
  (cfc (fun x : ℝ => x ^ (1 + s)) ρ *
    cfc (fun x : ℝ => x ^ (-s)) σ).trace.re

def relativeEntropyNats (ρ σ : Matrix I I ℂ) : ℝ :=
  (ρ * (cfc Real.log ρ - cfc Real.log σ)).trace.re

theorem petzMoment_eq_complexTrace (ρ σ : Matrix I I ℂ) (s : ℝ) :
    (cfc (fun x : ℝ => x ^ (1 + s)) ρ *
      cfc (fun x : ℝ => x ^ (-s)) σ).trace = (petzMoment ρ σ s : ℂ) :=
  trace_cfc_mul_cfc_real _ _ ρ σ

theorem petzMoment_eq_overlap {ρ σ : Matrix I I ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (s : ℝ) :
    petzMoment ρ σ s =
      ∑ i, ∑ j, (hρ.eigenvalues i) ^ (1 + s) * (hσ.eigenvalues j) ^ (-s) *
        overlapWeight (overlapUnitary hρ hσ) i j :=
  trace_cfc_mul_cfc_eq_overlap _ _ hρ hσ

theorem petzMoment_zero {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.IsHermitian) :
    petzMoment ρ σ 0 = 1 := by
  rw [petzMoment_eq_overlap hρ.1.1 hσ]
  simp only [add_zero, neg_zero, Real.rpow_one, Real.rpow_zero, mul_one]
  rw [overlap_sum_rows, ← trace_eq_sum_eigenvalues_re hρ.1.1, hρ.2]
  rfl

theorem petzMoment_nonneg {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (s : ℝ) :
    0 ≤ petzMoment ρ σ s := by
  rw [petzMoment_eq_overlap hρ.1 hσ.1]
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg
    (mul_nonneg (Real.rpow_nonneg (hρ.eigenvalues_nonneg i) _)
      (Real.rpow_nonneg (hσ.eigenvalues_nonneg j) _))
    (overlapWeight_nonneg _ i j)

theorem relativeEntropyNats_eq_spectral {ρ σ : Matrix I I ℂ} (hρ : ρ.IsHermitian) :
    relativeEntropyNats ρ σ = (cfc (fun x : ℝ => x * Real.log x) ρ).trace.re -
      (ρ * cfc Real.log σ).trace.re := by
  have hprod : cfc (fun x : ℝ => x * Real.log x) ρ = ρ * cfc Real.log ρ := by
    rw [cfc_mul (p := IsSelfAdjoint) (fun x : ℝ => x) Real.log ρ
      (ρ.finite_real_spectrum.continuousOn _) (ρ.finite_real_spectrum.continuousOn _),
      cfc_id' (p := IsSelfAdjoint) ℝ ρ hρ]
  simp only [relativeEntropyNats, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hprod]

theorem relativeEntropyNats_eq_overlap {ρ σ : Matrix I I ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relativeEntropyNats ρ σ =
      ∑ i, ∑ j, hρ.eigenvalues i * (Real.log (hρ.eigenvalues i) -
        Real.log (hσ.eigenvalues j)) * overlapWeight (overlapUnitary hρ hσ) i j := by
  rw [relativeEntropyNats_eq_spectral hρ, trace_cfc_eq_sum _ hρ,
    trace_mul_cfc_eq_overlap _ hρ hσ,
    ← overlap_sum_rows (overlapUnitary hρ hσ) (fun i => hρ.eigenvalues i * Real.log (hρ.eigenvalues i))]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem relativeEntropyNats_eq_bits (ρ σ : Matrix I I ℂ) :
    relativeEntropyNats ρ σ = Real.log 2 * FlaggedStates.finiteRelativeEntropyBits ρ σ := by
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold relativeEntropyNats FlaggedStates.finiteRelativeEntropyBits
  field_simp

theorem zero_rpow_one_add_eventually :
    (fun s : ℝ => (0 : ℝ) ^ (1 + s)) =ᶠ[𝓝 0] fun _ => 0 := by
  filter_upwards [eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)] with s hs
  exact Real.zero_rpow (by linarith : 1 + s ≠ 0)

theorem hasDerivAt_nonneg_rpow_one_add {a : ℝ} (ha : 0 ≤ a) :
    HasDerivAt (fun s : ℝ => a ^ (1 + s)) (a * Real.log a) 0 := by
  by_cases ha0 : a = 0
  · subst a
    simpa using (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
      zero_rpow_one_add_eventually
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    simpa [mul_comm] using
      ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id (0 : ℝ))).const_rpow hapos

theorem hasDerivAt_pos_rpow_neg {b : ℝ} (hb : 0 < b) :
    HasDerivAt (fun s : ℝ => b ^ (-s)) (-Real.log b) 0 := by
  simpa using (hasDerivAt_id (0 : ℝ)).neg.const_rpow hb

theorem scalarMoment_hasDerivAt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (w : ℝ) :
    HasDerivAt (fun s : ℝ => a ^ (1 + s) * b ^ (-s) * w)
      (a * (Real.log a - Real.log b) * w) 0 := by
  convert ((hasDerivAt_nonneg_rpow_one_add ha).mul (hasDerivAt_pos_rpow_neg hb)).mul_const w using 1
  simp only [add_zero, neg_zero, Real.rpow_one, Real.rpow_zero, mul_one]
  ring

theorem petzMoment_hasDerivAt_zero {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosDef) :
    HasDerivAt (petzMoment ρ σ) (relativeEntropyNats ρ σ) 0 := by
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ i, ∑ j, (hρ.1.eigenvalues i) ^ (1 + s) *
        (hσ.1.eigenvalues j) ^ (-s) * overlapWeight (overlapUnitary hρ.1 hσ.1) i j)
      (∑ i, ∑ j, hρ.1.eigenvalues i * (Real.log (hρ.1.eigenvalues i) -
        Real.log (hσ.1.eigenvalues j)) * overlapWeight (overlapUnitary hρ.1 hσ.1) i j) 0 :=
    HasDerivAt.fun_sum fun i hi => HasDerivAt.fun_sum fun j hj =>
      scalarMoment_hasDerivAt (hρ.eigenvalues_nonneg i) (hσ.eigenvalues_pos j) _
  rw [← relativeEntropyNats_eq_overlap hρ.1 hσ.1] at hsum
  exact hsum.congr_of_eventuallyEq (Eventually.of_forall fun s => petzMoment_eq_overlap hρ.1 hσ.1 s)

theorem petzMoment_deriv_zero {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosDef) :
    deriv (petzMoment ρ σ) 0 = relativeEntropyNats ρ σ :=
  (petzMoment_hasDerivAt_zero hρ hσ).deriv

theorem log_petzMoment_hasDerivAt_zero {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) :
    HasDerivAt (fun s : ℝ => Real.log (petzMoment ρ σ s)) (relativeEntropyNats ρ σ) 0 := by
  have h0 := petzMoment_zero hρ hσ.1
  have hd := (petzMoment_hasDerivAt_zero hρ.1 hσ).log (by rw [h0]; norm_num)
  simpa only [h0, div_one] using hd

theorem log_petzMoment_div_tendsto {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) :
    Tendsto (fun s : ℝ => Real.log (petzMoment ρ σ s) / s)
      (𝓝[≠] 0) (𝓝 (relativeEntropyNats ρ σ)) := by
  have h := (log_petzMoment_hasDerivAt_zero hρ hσ).tendsto_slope_zero
  simpa only [zero_add, petzMoment_zero hρ hσ.1, Real.log_one, sub_zero,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using h

theorem log_petzMoment_div_tendsto_right {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) :
    Tendsto (fun s : ℝ => Real.log (petzMoment ρ σ s) / s)
      (𝓝[>] 0) (𝓝 (relativeEntropyNats ρ σ)) :=
  (log_petzMoment_div_tendsto hρ hσ).mono_left (nhdsGT_le_nhdsNE 0)

theorem petzMoment_eventually_pos {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) :
    ∀ᶠ s : ℝ in 𝓝 0, 0 < petzMoment ρ σ s := by
  have h0 : 0 < petzMoment ρ σ 0 := by rw [petzMoment_zero hρ hσ.1]; norm_num
  exact (petzMoment_hasDerivAt_zero hρ.1 hσ).continuousAt.eventually (eventually_gt_nhds h0)

theorem relativeEntropyBits_eq_nats_of_posDef {ρ σ : Matrix I I ℂ}
    (hσ : σ.PosDef) :
    FlaggedStates.relativeEntropyBits ρ σ = ((relativeEntropyNats ρ σ / Real.log 2 : ℝ) : EReal) := by
  rw [FlaggedStates.relativeEntropyBits,
    ite_eq_left (FlaggedStates.hasSupportIn_of_posDef ρ hσ)]
  rfl

theorem log_petzMoment_div_tendsto_bits {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : σ.PosDef) :
    Tendsto (fun s : ℝ => (Real.log (petzMoment ρ σ s) / s) / Real.log 2)
      (𝓝[≠] 0) (𝓝 (FlaggedStates.finiteRelativeEntropyBits ρ σ)) := by
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h := (log_petzMoment_div_tendsto hρ hσ).div_const (Real.log 2)
  rw [relativeEntropyNats_eq_bits] at h
  simpa only [mul_div_cancel_left₀ _ hl] using h

end QuantumProver.SuperchannelDiscrimination.PetzMoments
