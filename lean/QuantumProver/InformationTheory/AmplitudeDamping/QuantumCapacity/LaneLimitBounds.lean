import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.TracePowerBounds
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.Definitions
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.ProtocolIdentities

set_option autoImplicit false

namespace QuantumProver.AmplitudeDamping.FiniteModel

open Filter Topology

theorem converseBudget_eq_scalarBudget_interior {p s : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hs1 : s < 1) :
    converseBudget p s = Scalar.scalarBudget p s := by
  simpa only [converseBudget, ite_eq_right hp0.ne', ite_eq_right hp1.ne, ite_eq_right hs1.ne,
    logTwo, Scalar.log2, Scalar.optimizingSurvivor] using
    (Scalar.scalarBudget_eq_closed hp0 hp1 hs1).symm

theorem converseBudget_eq_scalarBudget_one {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    converseBudget p 1 = Scalar.scalarBudget p 1 := by
  rw [Scalar.scalarBudget_one hp1]
  simp [converseBudget, hp0.ne', hp1.ne, logTwo, Scalar.log2]
  congr 2
  ring

theorem finiteTypeIncrement_matrix (n w : ℕ) {p s : ℝ}
    (hn : 0 < n) (hwn : w ≤ n) (hp0 : 0 < p) (hp1 : p < 1)
    (hs0 : 0 < s) (hs1 : s < 1) :
    ((1 + s) / s) * logTwo ((n : ℝ) + 1) +
      logTwo (Scalar.survivorMoment n w p s) / s ≤
        (n : ℝ) * converseBudget p s +
          ((2 + s) / s) * logTwo ((n : ℝ) + 1) := by
  rw [converseBudget_eq_scalarBudget_interior hp0 hp1 hs1]
  exact Scalar.finiteTypeIncrement_le n w hn hwn hp0 hp1 hs0 hs1

theorem finiteTypeIncrement_matrix_one (n w : ℕ) {p : ℝ}
    (hwn : w ≤ n) (hp0 : 0 < p) (hp1 : p < 1) :
    2 * logTwo ((n : ℝ) + 1) + logTwo (Scalar.survivorMoment n w p 1) ≤
      (n : ℝ) * converseBudget p 1 + 2 * logTwo ((n : ℝ) + 1) := by
  have hm := Scalar.survivorMoment_pos n w hp0 hp1 (s := 1)
  have hl := Real.log_le_log hm (Scalar.survivorMoment_one_le n w hwn hp0 hp1)
  rw [Real.log_pow] at hl
  rw [converseBudget_eq_scalarBudget_one hp0 hp1, Scalar.scalarBudget_one hp1]
  have hb : logTwo (Scalar.survivorMoment n w p 1) ≤
      (n : ℝ) * Scalar.log2 (1 + (1 - p)) := by
    unfold logTwo Scalar.log2
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact (div_le_div_of_nonneg_right hl h2.le).trans_eq (by ring)
  linarith

theorem finiteTypeIncrement_matrix_full_s (n w : ℕ) {p s : ℝ}
    (hn : 0 < n) (hwn : w ≤ n) (hp0 : 0 < p) (hp1 : p < 1)
    (hs0 : 0 < s) (hs1 : s ≤ 1) :
    ((1 + s) / s) * logTwo ((n : ℝ) + 1) +
      logTwo (Scalar.survivorMoment n w p s) / s ≤
        (n : ℝ) * converseBudget p s +
          ((2 + s) / s) * logTwo ((n : ℝ) + 1) := by
  rcases lt_or_eq_of_le hs1 with hslt | rfl
  · exact finiteTypeIncrement_matrix n w hn hwn hp0 hp1 hs0 hslt
  · have h := finiteTypeIncrement_matrix_one n w hwn hp0 hp1
    have hnlog : 0 ≤ logTwo ((n : ℝ) + 1) := by
      unfold logTwo
      have hnreal : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      exact div_nonneg (Real.log_nonneg (by linarith)) (Real.log_pos (by norm_num)).le
    norm_num at h ⊢
    linarith

theorem converseBudget_limit_zero_right {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Tendsto (converseBudget p) (𝓝[>] (0 : ℝ)) (𝓝 (Scalar.zCapacityBound p)) := by
  apply (Scalar.tendsto_scalarBudget_zero_right hp0 hp1).congr'
  have hs : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hs] with s hs1
  exact (converseBudget_eq_scalarBudget_interior hp0 hp1 hs1).symm

end QuantumProver.AmplitudeDamping.FiniteModel

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix

namespace QuantumProver.AmplitudeDamping.Testing

variable {I : Type*} [Fintype I] [DecidableEq I]

def vectorMass (x : I → ℂ) : ℝ := ∑ i, Complex.normSq (x i)

def expectation (A : Matrix I I ℂ) (x : I → ℂ) : ℝ :=
  (star x ⬝ᵥ (A *ᵥ x)).re

omit [DecidableEq I] in
theorem vectorMass_nonneg (x : I → ℂ) : 0 ≤ vectorMass x :=
  Finset.sum_nonneg (fun _i _ => Complex.normSq_nonneg _)

omit [DecidableEq I] in
theorem vectorMass_eq_dot (x : I → ℂ) : vectorMass x = (star x ⬝ᵥ x).re := by
  simp [vectorMass, dotProduct, Pi.star_apply, Complex.re_sum,
    ← Complex.normSq_eq_conj_mul_self]

omit [DecidableEq I] in
theorem vectorMass_mulVec (C : Matrix I I ℂ) (x : I → ℂ) :
    vectorMass (C *ᵥ x) = expectation (Cᴴ * C) x := by
  rw [vectorMass_eq_dot]
  unfold expectation
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

theorem vectorMass_mulVec_of_gram (C : Matrix I I ℂ) (hC : Cᴴ * C = 1)
    (x : I → ℂ) : vectorMass (C *ᵥ x) = vectorMass x := by
  rw [vectorMass_mulVec, hC]
  simp only [expectation, Matrix.one_mulVec, vectorMass_eq_dot]

omit [DecidableEq I] in
theorem expectation_nonneg {A : Matrix I I ℂ} (hA : A.PosSemidef) (x : I → ℂ) :
    0 ≤ expectation A x := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg x)).1

omit [DecidableEq I] in
theorem expectation_conjugate (C A : Matrix I I ℂ) (x : I → ℂ) :
    expectation (C * A * Cᴴ) x = expectation A (Cᴴ *ᵥ x) := by
  unfold expectation
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
    ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem expectation_diagonal (d : I → ℝ) (x : I → ℂ) :
    expectation (Matrix.diagonal (fun i => (d i : ℂ))) x =
      ∑ i, Complex.normSq (x i) * d i := by
  simp only [expectation, dotProduct, Pi.star_apply,
    Matrix.mulVec_diagonal, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem expectation_spectral {A : Matrix I I ℂ} (hA : A.IsHermitian) (x : I → ℂ) :
    expectation A x = ∑ i,
      Complex.normSq (((hA.eigenvectorUnitary : Matrix I I ℂ)ᴴ *ᵥ x) i) *
        hA.eigenvalues i := by
  conv_lhs =>
    rw [hA.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal]
  rw [expectation_conjugate, expectation_diagonal]

theorem expectation_rpow_spectral {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (α : ℝ) (x : I → ℂ) :
    expectation (CFC.rpow A α) x = ∑ i,
      Complex.normSq (((hA.1.eigenvectorUnitary : Matrix I I ℂ)ᴴ *ᵥ x) i) *
        (hA.1.eigenvalues i) ^ α := by
  have heq : CFC.rpow A α = cfc (fun t : ℝ => t ^ α) A :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := A) (y := α) hA.nonneg
  rw [heq, TracePower.cfc_spectral _ hA.1]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rw [expectation_conjugate, expectation_diagonal]

theorem spectral_vectorMass {A : Matrix I I ℂ} (hA : A.IsHermitian) (x : I → ℂ) :
    ∑ i, Complex.normSq (((hA.eigenvectorUnitary : Matrix I I ℂ)ᴴ *ᵥ x) i) =
      vectorMass x := by
  apply vectorMass_mulVec_of_gram
  simpa only [Matrix.conjTranspose_conjTranspose, Unitary.coe_star,
    Matrix.star_eq_conjTranspose] using
    Unitary.coe_mul_star_self hA.eigenvectorUnitary

omit [DecidableEq I] in
theorem weighted_rpow_le_mass_rpow_sum (W t : I → ℝ)
    (hW : ∀ i, 0 ≤ W i) (ht : ∀ i, 0 ≤ t i) {α : ℝ} (hα : 1 ≤ α) :
    (∑ i, W i * t i) ^ α ≤ (∑ i, W i) ^ α * ∑ i, (t i) ^ α := by
  let N := ∑ i, W i
  have hN0 : 0 ≤ N := Finset.sum_nonneg (fun i _ => hW i)
  rcases eq_or_lt_of_le hN0 with hN | hN
  · have hW0 (i : I) : W i = 0 := by
      have hi : W i ≤ N := Finset.single_le_sum (fun j _ => hW j) (Finset.mem_univ i)
      exact le_antisymm (by simpa only [← hN] using hi) (hW i)
    simp [hW0, Real.zero_rpow (by linarith : α ≠ 0)]
  · let ν := fun i => W i / N
    have hν0 (i : I) : 0 ≤ ν i := div_nonneg (hW i) hN.le
    have hν1 (i : I) : ν i ≤ 1 := (div_le_one hN).mpr
      (Finset.single_le_sum (fun j _ => hW j) (Finset.mem_univ i))
    have hνsum : ∑ i, ν i = 1 := by
      dsimp only [ν]
      rw [← Finset.sum_div]
      exact div_self hN.ne'
    have hinput : (∑ i, ν i * t i) = (∑ i, W i * t i) / N := by
      calc
        _ = ∑ i, (W i * t i) / N := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [ν]
          ring
        _ = _ := (Finset.sum_div _ _ _).symm
    have hJ := (convexOn_rpow hα).map_sum_le
      (t := Finset.univ) (w := ν) (p := t)
      (fun i _ => hν0 i) hνsum (fun i _ => ht i)
    have hbound : ((∑ i, W i * t i) / N) ^ α ≤ ∑ i, (t i) ^ α := by
      calc
        _ ≤ ∑ i, ν i * (t i) ^ α := by
          simpa only [smul_eq_mul, hinput] using hJ
        _ ≤ ∑ i, 1 * (t i) ^ α := Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_right (hν1 i) (Real.rpow_nonneg (ht i) α))
        _ = _ := by simp only [one_mul]
    have hnum : 0 ≤ ∑ i, W i * t i := Finset.sum_nonneg
      (fun i _ => mul_nonneg (hW i) (ht i))
    rw [Real.div_rpow hnum hN.le] at hbound
    have h := (div_le_iff₀ (Real.rpow_pos_of_pos hN α)).mp hbound
    simpa only [N, mul_comm] using h

theorem expectation_rpow_le_mass_trace {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (x : I → ℂ) {α : ℝ} (hα : 1 ≤ α) :
    (expectation A x) ^ α ≤ (vectorMass x) ^ α * (CFC.rpow A α).trace.re := by
  rw [expectation_spectral hA.1, TracePower.trace_rpow_eq_sum hA,
    ← spectral_vectorMass hA.1 x]
  exact weighted_rpow_le_mass_rpow_sum _ _ (fun i => Complex.normSq_nonneg _)
    hA.eigenvalues_nonneg hα

theorem expectation_rpow_concave {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (x : I → ℂ) (hx : vectorMass x = 1) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    expectation (CFC.rpow A β) x ≤ (expectation A x) ^ β := by
  have hw : ∑ i,
      Complex.normSq (((hA.1.eigenvectorUnitary : Matrix I I ℂ)ᴴ *ᵥ x) i) = 1 :=
    (spectral_vectorMass hA.1 x).trans hx
  have hJ := (Real.concaveOn_rpow hβ0 hβ1).le_map_sum
    (t := Finset.univ)
    (w := fun i => Complex.normSq (((hA.1.eigenvectorUnitary : Matrix I I ℂ)ᴴ *ᵥ x) i))
    (p := hA.1.eigenvalues) (fun i _ => Complex.normSq_nonneg _) hw
    (fun i _ => hA.eigenvalues_nonneg i)
  rw [expectation_rpow_spectral hA, expectation_spectral hA.1]
  simpa only [smul_eq_mul] using hJ

theorem fullRank_pureProbe {ρ σ : Matrix I I ℂ} (hρ : ρ.PosSemidef)
    (hσ : σ.PosDef) (φ : I → ℂ) (hφ : vectorMass φ = 1)
    {α : ℝ} (hα : 1 < α) :
    (expectation ρ φ) ^ α ≤ (expectation σ φ) ^ (α - 1) *
      FiniteModel.sandwichedTrace α ρ σ := by
  let β := (α - 1) / α
  have hα0 : 0 < α := by linarith
  have hαne : α ≠ 0 := hα0.ne'
  have hβ0 : 0 ≤ β := div_nonneg (by linarith) hα0.le
  have hβ1 : β ≤ 1 := (div_le_one hα0).mpr (by linarith)
  have hβα : β * α = α - 1 := div_mul_cancel₀ _ hαne
  let W := CFC.rpow σ (-(β / 2))
  let S := CFC.rpow σ (β / 2)
  let X := W * ρ * W
  let x := S *ᵥ φ
  have hW : Wᴴ = W :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := σ) (y := -(β / 2)))).1
  have hS : Sᴴ = S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := σ) (y := β / 2))).1
  have hX : X.PosSemidef := by
    change (W * ρ * W).PosSemidef
    simpa only [hW] using hρ.mul_mul_conjTranspose_same W
  have hSW : S * W = 1 := CFC.rpow_mul_rpow_neg (β / 2) hσ.isStrictlyPositive
  have hWS : W * S = 1 := CFC.rpow_neg_mul_rpow (β / 2) hσ.isStrictlyPositive
  have hSS : S * S = CFC.rpow σ β := by
    calc
      _ = CFC.rpow σ (β / 2 + β / 2) :=
        (CFC.rpow_add (a := σ) (x := β / 2) (y := β / 2) hσ.isUnit).symm
      _ = _ := by congr 1; ring
  have hcancel : S * X * Sᴴ = ρ := by
    change S * (W * ρ * W) * Sᴴ = ρ
    rw [hS]
    calc
      _ = (S * W) * ρ * (W * S) := by noncomm_ring
      _ = ρ := by rw [hSW, hWS]; simp
  have hE : expectation X x = expectation ρ φ := by
    calc
      _ = expectation (S * X * Sᴴ) φ := by
        rw [expectation_conjugate, hS]
      _ = _ := by rw [hcancel]
  have hmass : vectorMass x = expectation (CFC.rpow σ β) φ := by
    calc
      _ = expectation (Sᴴ * S) φ := vectorMass_mulVec S φ
      _ = _ := by rw [hS, hSS]
  have hconc : vectorMass x ≤ (expectation σ φ) ^ β := by
    rw [hmass]
    exact expectation_rpow_concave hσ.posSemidef φ hφ hβ0 hβ1
  have ha0 : 0 ≤ expectation σ φ := expectation_nonneg hσ.posSemidef φ
  have hp : (vectorMass x) ^ α ≤ (expectation σ φ) ^ (α - 1) := by
    calc
      _ ≤ ((expectation σ φ) ^ β) ^ α :=
        Real.rpow_le_rpow (vectorMass_nonneg x) hconc hα0.le
      _ = _ := by rw [← Real.rpow_mul ha0, hβα]
  have hQ0 : 0 ≤ (CFC.rpow X α).trace.re := by
    rw [TracePower.trace_rpow_eq_sum hX]
    exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hX.eigenvalues_nonneg i) α)
  have hw : (1 - α) / (2 * α) = -(β / 2) := by
    dsimp only [β]
    field_simp [hαne] <;> ring
  have hQ : FiniteModel.sandwichedTrace α ρ σ = (CFC.rpow X α).trace.re := by
    unfold FiniteModel.sandwichedTrace
    rw [hw]
  rw [hQ]
  calc
    _ ≤ (vectorMass x) ^ α * (CFC.rpow X α).trace.re := by
      simpa only [hE] using expectation_rpow_le_mass_trace hX x hα.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hp hQ0

end QuantumProver.AmplitudeDamping.Testing

namespace QuantumProver.AmplitudeDamping.PositiveTrace

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem density_weighted_rpow_le (weights x : I → ℝ) (hweights : ∀ i, 0 ≤ weights i)
    (hweightssum : ∑ i, weights i = 1) (hx : ∀ i, 0 ≤ x i) {α : ℝ} (hα : 1 < α) :
    (∑ i, (weights i) ^ ((α - 1) / α) * x i) ^ α ≤ ∑ i, (x i) ^ α := by
  have hα0 : 0 < α := by linarith
  have hαne : α ≠ 0 := hα0.ne'
  let δ := 1 / α
  let β := (α - 1) / α
  let y := fun i => x i / (weights i) ^ δ
  have hδ0 : 0 < δ := one_div_pos.mpr hα0
  have hβ0 : 0 < β := div_pos (by linarith) hα0
  have hβ : β = 1 - δ := by
    dsimp only [β, δ]
    field_simp [hαne]
  have hδα : δ * α = 1 := div_mul_cancel₀ _ hαne
  have hy (i : I) : 0 ≤ y i := div_nonneg (hx i) (Real.rpow_nonneg (hweights i) δ)
  have hterm (i : I) : weights i * y i = (weights i) ^ β * x i := by
    rcases eq_or_lt_of_le (hweights i) with hi | hi
    · simp [y, ← hi, Real.zero_rpow hβ0.ne']
    · have hp : (weights i) ^ β = weights i / (weights i) ^ δ := by
        rw [hβ, Real.rpow_sub hi, Real.rpow_one]
      rw [hp]
      dsimp only [y]
      ring
  have hpower (i : I) : weights i * (y i) ^ α ≤ (x i) ^ α := by
    rcases eq_or_lt_of_le (hweights i) with hi | hi
    · simp only [← hi, zero_mul]
      exact Real.rpow_nonneg (hx i) α
    · have hp : ((weights i) ^ δ) ^ α = weights i := by
        rw [← Real.rpow_mul (hweights i), hδα, Real.rpow_one]
      dsimp only [y]
      rw [Real.div_rpow (hx i) (Real.rpow_nonneg (hweights i) δ), hp]
      exact le_of_eq (by field_simp [hi.ne'])
  have hJ := (convexOn_rpow hα.le).map_sum_le
    (t := Finset.univ) (w := weights) (p := y)
    (fun i _ => hweights i) hweightssum (fun i _ => hy i)
  calc
    _ = (∑ i, weights i * y i) ^ α := by simp_rw [hterm]; rfl
    _ ≤ ∑ i, weights i * (y i) ^ α := by simpa only [smul_eq_mul] using hJ
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hpower i)

theorem diagonal_rpow_sum_le_trace {X : Matrix I I ℂ} (hX : X.PosSemidef)
    {α : ℝ} (hα : 1 ≤ α) :
    ∑ i, (X i i).re ^ α ≤ (CFC.rpow X α).trace.re := by
  let U := hX.1.eigenvectorUnitary
  have hs : X = (U : Matrix I I ℂ) *
      Matrix.diagonal (fun i => (hX.1.eigenvalues i : ℂ)) *
        (U : Matrix I I ℂ)ᴴ := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hX.1.spectral_theorem
  have hdiag (i : I) : (X i i).re =
      ∑ j, TracePower.entryWeight (U : Matrix I I ℂ) i j * hX.1.eigenvalues j := by
    conv_lhs => rw [hs]
    exact TracePower.sandwich_diagonal_re _ _ i
  have hleft : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) ≤ 1 :=
    le_of_eq (Unitary.coe_star_mul_self U)
  have hright : (U : Matrix I I ℂ) * (U : Matrix I I ℂ)ᴴ ≤ 1 :=
    le_of_eq (Unitary.coe_mul_star_self U)
  rw [TracePower.trace_rpow_eq_sum hX]
  simp_rw [hdiag]
  exact TracePower.substochastic_rpow_sum_le
    (TracePower.entryWeight (U : Matrix I I ℂ)) hX.1.eigenvalues hα
    (TracePower.entryWeight_nonneg _) hX.eigenvalues_nonneg
    (TracePower.entryWeight_row_le _ hright) (TracePower.entryWeight_col_le _ hleft)

theorem trace_rpow_mul_spectral {σ X : Matrix I I ℂ} (hσ : σ.PosSemidef) (β : ℝ) :
    (CFC.rpow σ β * X).trace.re = ∑ i, (hσ.1.eigenvalues i) ^ β *
      (((hσ.1.eigenvectorUnitary : Matrix I I ℂ)ᴴ * X *
        (hσ.1.eigenvectorUnitary : Matrix I I ℂ)) i i).re := by
  let U := hσ.1.eigenvectorUnitary
  let D : Matrix I I ℂ := Matrix.diagonal (fun i => (((hσ.1.eigenvalues i) ^ β : ℝ) : ℂ))
  let Y : Matrix I I ℂ := (U : Matrix I I ℂ)ᴴ * X * (U : Matrix I I ℂ)
  have hp : CFC.rpow σ β = (U : Matrix I I ℂ) * D * (U : Matrix I I ℂ)ᴴ := by
    have heq : CFC.rpow σ β = cfc (fun t : ℝ => t ^ β) σ :=
      CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := σ) (y := β) hσ.nonneg
    rw [heq, TracePower.cfc_spectral _ hσ.1]
    simp only [U, D, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  have ht : (CFC.rpow σ β * X).trace = (D * Y).trace := by
    rw [hp]
    calc
      _ = ((U : Matrix I I ℂ) * (D * (U : Matrix I I ℂ)ᴴ * X)).trace := by
        congr 1
        noncomm_ring
      _ = ((D * (U : Matrix I I ℂ)ᴴ * X) * (U : Matrix I I ℂ)).trace :=
        Matrix.trace_mul_comm _ _
      _ = (D * Y).trace := by
        congr 1
        dsimp only [Y]
        noncomm_ring
  rw [ht]
  change (D * Y).trace.re = ∑ i, (hσ.1.eigenvalues i) ^ β * (Y i i).re
  simp only [D, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem density_weighted_trace_rpow_le {σ X : Matrix I I ℂ}
    (hσ : FiniteModel.IsDensity σ) (hX : X.PosSemidef) {α : ℝ} (hα : 1 < α) :
    ((CFC.rpow σ ((α - 1) / α) * X).trace.re) ^ α ≤
      (CFC.rpow X α).trace.re := by
  let U := hσ.1.1.eigenvectorUnitary
  let Y : Matrix I I ℂ := (U : Matrix I I ℂ)ᴴ * X * (U : Matrix I I ℂ)
  have hY : Y.PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      hX.mul_mul_conjTranspose_same (U : Matrix I I ℂ)ᴴ
  have hweightssum : ∑ i, hσ.1.1.eigenvalues i = 1 := by
    have ht := congrArg Complex.re hσ.1.1.trace_eq_sum_eigenvalues
    calc
      _ = σ.trace.re := by
        simpa only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal,
          Complex.ofReal_re] using ht.symm
      _ = 1 := by simpa only [Complex.one_re] using congrArg Complex.re hσ.2
  have hx (i : I) : 0 ≤ (Y i i).re :=
    (Complex.nonneg_iff.mp (hY.diag_nonneg (i := i))).1
  have hleft : (U : Matrix I I ℂ) * (U : Matrix I I ℂ)ᴴ ≤ 1 :=
    le_of_eq (Unitary.coe_mul_star_self U)
  have hright : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) ≤ 1 :=
    le_of_eq (Unitary.coe_star_mul_self U)
  calc
    _ = (∑ i, (hσ.1.1.eigenvalues i) ^ ((α - 1) / α) * (Y i i).re) ^ α := by
      rw [trace_rpow_mul_spectral hσ.1]
    _ ≤ ∑ i, (Y i i).re ^ α :=
      density_weighted_rpow_le _ _ hσ.1.eigenvalues_nonneg hweightssum hx hα
    _ ≤ (CFC.rpow Y α).trace.re := diagonal_rpow_sum_le_trace hY hα.le
    _ ≤ (CFC.rpow X α).trace.re := by
      simpa only [Y, Matrix.conjTranspose_conjTranspose] using
        TracePower.trace_rpow_contraction hX
          (C := (U : Matrix I I ℂ)ᴴ)
          (by simpa only [Matrix.conjTranspose_conjTranspose] using hleft)
          (by simpa only [Matrix.conjTranspose_conjTranspose] using hright) hα.le

end QuantumProver.AmplitudeDamping.PositiveTrace

namespace QuantumProver.AmplitudeDamping.PowerContinuity

open Filter Topology

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem continuousOn_rpow_posSemidef {α : ℝ} (hα : 0 < α) :
    ContinuousOn (fun A : Matrix I I ℂ => CFC.rpow A α)
      {A : Matrix I I ℂ | A.PosSemidef} := by
  have hc : ContinuousOn (fun A : Matrix I I ℂ => cfc (fun x : ℝ => x ^ α) A)
      {A : Matrix I I ℂ | A.PosSemidef} :=
    ContinuousOn.cfc_of_mem_nhdsSet (p := IsSelfAdjoint) (s := Set.univ)
      (fun x : ℝ => x ^ α) (by exact Filter.univ_mem) continuous_id.continuousOn
      (fun A hA => hA.1.isSelfAdjoint)
      (Real.continuous_rpow_const hα.le).continuousOn
  refine hc.congr ?_
  intro A hA
  exact CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := A) (y := α) hA.nonneg

theorem tendsto_rpow_of_posSemidef {T : Type*} {l : Filter T}
    {Aε : T → Matrix I I ℂ} {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (hε : ∀ᶠ ε in l, (Aε ε).PosSemidef) (hT : Tendsto Aε l (𝓝 A))
    {α : ℝ} (hα : 0 < α) :
    Tendsto (fun ε => CFC.rpow (Aε ε) α) l (𝓝 (CFC.rpow A α)) := by
  apply (continuousOn_rpow_posSemidef hα).continuousWithinAt hA |>.tendsto.comp
  rw [tendsto_nhdsWithin_iff]
  exact ⟨hT, hε⟩

theorem continuous_real_trace :
    Continuous (fun A : Matrix I I ℂ => A.trace.re) := by
  simp only [Matrix.trace, Matrix.diag]
  fun_prop

theorem tendsto_real_trace_rpow_of_posSemidef {T : Type*} {l : Filter T}
    {Aε : T → Matrix I I ℂ} {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (hε : ∀ᶠ ε in l, (Aε ε).PosSemidef) (hT : Tendsto Aε l (𝓝 A))
    {α : ℝ} (hα : 0 < α) :
    Tendsto (fun ε => (CFC.rpow (Aε ε) α).trace.re) l
      (𝓝 ((CFC.rpow A α).trace.re)) :=
  continuous_real_trace.tendsto (CFC.rpow A α) |>.comp
    (tendsto_rpow_of_posSemidef hA hε hT hα)

end QuantumProver.AmplitudeDamping.PowerContinuity

namespace QuantumProver.AmplitudeDamping.TensorPower

open Filter Topology
open scoped Kronecker

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def diagonalStarAlgHom : (I → ℂ) →⋆ₐ[ℝ] Matrix I I ℂ :=
  { Matrix.diagonalAlgHom (n := I) (α := ℂ) ℝ with
    map_star' v := by
      change Matrix.diagonal (star v) = star (Matrix.diagonal v)
      rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose] }

theorem diagonalStarAlgHom_apply (v : I → ℂ) :
    diagonalStarAlgHom v = Matrix.diagonal v := rfl

theorem cfc_diagonal_real (f : ℝ → ℝ) (d : I → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) =
      Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  letI : IsometricContinuousFunctionalCalculus ℝ (I → ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  let a : I → ℂ := fun i => (d i : ℂ)
  have ha : IsSelfAdjoint a := by ext i; simp [a, IsSelfAdjoint]
  have hdiag : (Matrix.diagonal a).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.diagonal_conjTranspose, a]
  have hf : ContinuousOn f (spectrum ℝ a) := by
    apply Set.Finite.continuousOn
    rw [Pi.spectrum_eq]
    apply Set.finite_iUnion
    intro i
    exact (Set.finite_singleton (d i)).subset (CFC.spectrum_algebraMap_subset (A := ℂ) (d i))
  have hcont : Continuous (diagonalStarAlgHom (I := I)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [diagonalStarAlgHom_apply, Matrix.diagonal_apply]
    split_ifs <;> fun_prop
  have hmap := (diagonalStarAlgHom (I := I)).map_cfc f a hf hcont ha hdiag
  rw [cfc_map_pi (S := ℝ) f a (by simpa only [← Pi.spectrum_eq] using hf) ha
    (fun i => by simp [a, IsSelfAdjoint])] at hmap
  have hscalar : (fun i => cfc f (a i)) = fun i => (f (d i) : ℂ) := by
    funext i
    exact cfc_algebraMap (R := ℝ) (A := ℂ) (d i) f
  rw [hscalar, diagonalStarAlgHom_apply, diagonalStarAlgHom_apply] at hmap
  exact hmap.symm

def unitaryKronecker (U : Matrix.unitaryGroup I ℂ) (V : Matrix.unitaryGroup J ℂ) :
    Matrix.unitaryGroup (I × J) ℂ :=
  ⟨(U : Matrix I I ℂ) ⊗ₖ (V : Matrix J J ℂ), by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul]
    have hU : (U : Matrix I I ℂ) * (U : Matrix I I ℂ)ᴴ = 1 :=
      Unitary.coe_mul_star_self U
    have hV : (V : Matrix J J ℂ) * (V : Matrix J J ℂ)ᴴ = 1 :=
      Unitary.coe_mul_star_self V
    rw [hU, hV, Matrix.one_kronecker_one]⟩

theorem unitaryKronecker_conjugate (U : Matrix.unitaryGroup I ℂ)
    (V : Matrix.unitaryGroup J ℂ) (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    Unitary.conjStarAlgAut ℝ (Matrix (I × J) (I × J) ℂ) (unitaryKronecker U V) (A ⊗ₖ B) =
      (Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) U A) ⊗ₖ
        (Unitary.conjStarAlgAut ℝ (Matrix J J ℂ) V B) := by
  change ((U : Matrix I I ℂ) ⊗ₖ (V : Matrix J J ℂ)) * (A ⊗ₖ B) *
    ((U : Matrix I I ℂ) ⊗ₖ (V : Matrix J J ℂ))ᴴ =
      ((U : Matrix I I ℂ) * A * (U : Matrix I I ℂ)ᴴ) ⊗ₖ
        ((V : Matrix J J ℂ) * B * (V : Matrix J J ℂ)ᴴ)
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]

theorem cfc_unitary_conjugate (f : ℝ → ℝ) (U : Matrix.unitaryGroup I ℂ)
    {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    cfc f (Unitary.conjStarAlgAut ℝ _ U A) =
      Unitary.conjStarAlgAut ℝ _ U (cfc f A) := by
  have hout : IsSelfAdjoint (Unitary.conjStarAlgAut ℝ _ U A) := by
    change star (Unitary.conjStarAlgAut ℝ _ U A) = Unitary.conjStarAlgAut ℝ _ U A
    rw [← map_star]
    exact congrArg (Unitary.conjStarAlgAut ℝ _ U) hA
  exact (StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℝ _ U) f A
    (A.finite_real_spectrum.continuousOn _) (by
      change Continuous (fun X : Matrix I I ℂ =>
        (U : Matrix I I ℂ) * X * (U : Matrix I I ℂ)ᴴ)
      fun_prop) hA hout).symm

theorem cfc_kronecker_spectral (f : ℝ → ℝ) {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    cfc f (A ⊗ₖ B) =
      Unitary.conjStarAlgAut ℝ (Matrix (I × J) (I × J) ℂ)
        (unitaryKronecker hA.eigenvectorUnitary hB.eigenvectorUnitary)
        (Matrix.diagonal (fun x : I × J =>
          (f (hA.eigenvalues x.1 * hB.eigenvalues x.2) : ℂ))) := by
  have hd : Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) ⊗ₖ
      Matrix.diagonal (fun j => (hB.eigenvalues j : ℂ)) =
      Matrix.diagonal (fun x : I × J => ((hA.eigenvalues x.1 * hB.eigenvalues x.2 : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal]
    simp only [Complex.ofReal_mul]
  have heq : A ⊗ₖ B =
      Unitary.conjStarAlgAut ℝ (Matrix (I × J) (I × J) ℂ)
        (unitaryKronecker hA.eigenvectorUnitary hB.eigenvectorUnitary)
        (Matrix.diagonal (fun x : I × J => ((hA.eigenvalues x.1 * hB.eigenvalues x.2 : ℝ) : ℂ))) := by
    rw [← hd, unitaryKronecker_conjugate]
    exact congrArg₂ Matrix.kronecker hA.spectral_theorem hB.spectral_theorem
  have hdiag : (Matrix.diagonal (fun x : I × J =>
      ((hA.eigenvalues x.1 * hB.eigenvalues x.2 : ℝ) : ℂ))).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  rw [heq, cfc_unitary_conjugate f _ hdiag, cfc_diagonal_real]

theorem rpow_kronecker {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t : ℝ) :
    CFC.rpow (A ⊗ₖ B) t = CFC.rpow A t ⊗ₖ CFC.rpow B t := by
  have hAB : CFC.rpow (A ⊗ₖ B) t = cfc (fun x : ℝ => x ^ t) (A ⊗ₖ B) :=
    CFC.rpow_eq_cfc_real (A := Matrix (I × J) (I × J) ℂ)
      (a := A ⊗ₖ B) (y := t) (hA.kronecker hB).nonneg
  have hAA : CFC.rpow A t = cfc (fun x : ℝ => x ^ t) A :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := A) (y := t) hA.nonneg
  have hBB : CFC.rpow B t = cfc (fun x : ℝ => x ^ t) B :=
    CFC.rpow_eq_cfc_real (A := Matrix J J ℂ) (a := B) (y := t) hB.nonneg
  rw [hAB, hAA, hBB, cfc_kronecker_spectral _ hA.1 hB.1,
    TracePower.cfc_spectral _ hA.1, TracePower.cfc_spectral _ hB.1,
    ← unitaryKronecker_conjugate]
  congr 1
  rw [Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext x
  rw [Real.mul_rpow (hA.eigenvalues_nonneg x.1) (hB.eigenvalues_nonneg x.2),
    Complex.ofReal_mul]

theorem trace_kronecker_re_of_posSemidef {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊗ₖ B).trace.re = A.trace.re * B.trace.re := by
  rw [Matrix.trace_kronecker, Complex.mul_re,
    (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm,
    (Complex.nonneg_iff.mp hB.trace_nonneg).2.symm, zero_mul, sub_zero]

theorem sandwichedTrace_kronecker {ρ σ : Matrix I I ℂ} {τ υ : Matrix J J ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hτ : τ.PosSemidef) (hυ : υ.PosSemidef) (α : ℝ) :
    FiniteModel.sandwichedTrace α (ρ ⊗ₖ τ) (σ ⊗ₖ υ) =
      FiniteModel.sandwichedTrace α ρ σ * FiniteModel.sandwichedTrace α τ υ := by
  let t := (1 - α) / (2 * α)
  let W := CFC.rpow σ t
  let V := CFC.rpow υ t
  have hW : W.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := σ) (y := t))
  have hV : V.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := υ) (y := t))
  have hWs : Wᴴ = W := hW.1
  have hVs : Vᴴ = V := hV.1
  have hX : (W * ρ * W).PosSemidef := by
    simpa only [hWs] using hρ.mul_mul_conjTranspose_same W
  have hY : (V * τ * V).PosSemidef := by
    simpa only [hVs] using hτ.mul_mul_conjTranspose_same V
  have hRX : (CFC.rpow (W * ρ * W) α).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := W * ρ * W) (y := α))
  have hRY : (CFC.rpow (V * τ * V) α).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := V * τ * V) (y := α))
  change (CFC.rpow (CFC.rpow (σ ⊗ₖ υ) t * (ρ ⊗ₖ τ) * CFC.rpow (σ ⊗ₖ υ) t) α).trace.re =
    (CFC.rpow (W * ρ * W) α).trace.re * (CFC.rpow (V * τ * V) α).trace.re
  rw [rpow_kronecker hσ hυ, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    rpow_kronecker hX hY]
  exact trace_kronecker_re_of_posSemidef hRX hRY

end QuantumProver.AmplitudeDamping.TensorPower

namespace QuantumProver.AmplitudeDamping.FiniteModel

open scoped Kronecker

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem SupportLE.exists_right_factor {ρ σ : Matrix I I ℂ} (h : SupportLE ρ σ) :
    ∃ F : Matrix I I ℂ, ρ = σ * F := by
  classical
  change LinearMap.range ρ.mulVecLin ≤ LinearMap.range σ.mulVecLin at h
  have hc : ∀ j : I, ∃ x : I → ℂ, σ.mulVecLin x = ρ.mulVecLin (Pi.single j 1) := by
    intro j
    exact h ⟨Pi.single j 1, rfl⟩
  choose f hf using hc
  let F : Matrix I I ℂ := fun i j => f j i
  refine ⟨F, ?_⟩
  ext i j
  have hj : σ *ᵥ f j = ρ *ᵥ Pi.single j 1 := hf j
  calc
    ρ i j = (ρ *ᵥ Pi.single j 1) i := by simp [Matrix.mulVec_single_one, Matrix.col_apply]
    _ = (σ *ᵥ f j) i := congrFun hj.symm i
    _ = (σ * F) i j := rfl

theorem supportLE_of_eq_mul {ρ σ F : Matrix I I ℂ} (hρ : ρ = σ * F) :
    SupportLE ρ σ := by
  change LinearMap.range ρ.mulVecLin ≤ LinearMap.range σ.mulVecLin
  rintro v ⟨x, rfl⟩
  refine ⟨F *ᵥ x, ?_⟩
  change σ *ᵥ (F *ᵥ x) = ρ *ᵥ x
  rw [hρ, Matrix.mulVec_mulVec]

theorem SupportLE.kronecker {ρ σ : Matrix I I ℂ} {τ υ : Matrix J J ℂ}
    (h : SupportLE ρ σ) (k : SupportLE τ υ) :
    SupportLE (ρ ⊗ₖ τ) (σ ⊗ₖ υ) := by
  obtain ⟨F, hF⟩ := h.exists_right_factor
  obtain ⟨G, hG⟩ := k.exists_right_factor
  apply supportLE_of_eq_mul (F := F ⊗ₖ G)
  rw [hF, hG, Matrix.mul_kronecker_mul]

theorem IsDensity.kronecker {ρ : Matrix I I ℂ} {τ : Matrix J J ℂ}
    (hρ : IsDensity ρ) (hτ : IsDensity τ) : IsDensity (ρ ⊗ₖ τ) := by
  refine ⟨hρ.1.kronecker hτ.1, ?_⟩
  rw [Matrix.trace_kronecker, hρ.2, hτ.2, one_mul]

end QuantumProver.AmplitudeDamping.FiniteModel

namespace QuantumProver.AmplitudeDamping.FiniteModel
open scoped Kronecker

theorem IsDensity.submatrix_equiv {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] {ρ : Matrix I I ℂ} (hρ : IsDensity ρ) (e : K ≃ I) :
    IsDensity (ρ.submatrix e e) := by
  refine ⟨hρ.1.submatrix e, ?_⟩
  change (∑ k, ρ (e k) (e k)) = 1
  calc
    _ = ∑ i, ρ i i := e.sum_comp (fun i => ρ i i)
    _ = 1 := hρ.2

theorem SupportLE.submatrix_equiv {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] {ρ σ : Matrix I I ℂ} (h : SupportLE ρ σ) (e : K ≃ I) :
    SupportLE (ρ.submatrix e e) (σ.submatrix e e) := by
  obtain ⟨F, hF⟩ := h.exists_right_factor
  apply supportLE_of_eq_mul (F := F.submatrix e e)
  rw [hF, Matrix.submatrix_mul_equiv]

def tensorLabEquiv (a b c d : ℕ) :
    (Fin (a * c) × Fin (b * d)) ≃ ((Fin a × Fin b) × (Fin c × Fin d)) :=
  (((finProdFinEquiv : (Fin a × Fin c) ≃ Fin (a * c)).symm).prodCongr
    ((finProdFinEquiv : (Fin b × Fin d) ≃ Fin (b * d)).symm)).trans
    (Equiv.prodProdProdComm (Fin a) (Fin c) (Fin b) (Fin d))

def tensorOnLabCut {a b c d : ℕ} (ρ : BipartiteMatrix a b) (τ : BipartiteMatrix c d) :
    BipartiteMatrix (a * c) (b * d) :=
  (ρ ⊗ₖ τ).submatrix (tensorLabEquiv a b c d) (tensorLabEquiv a b c d)

theorem tensorOnLabCut_product {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ)
    (C : Matrix (Fin c) (Fin c) ℂ) (D : Matrix (Fin d) (Fin d) ℂ) :
    tensorOnLabCut (A ⊗ₖ B) (C ⊗ₖ D) =
      (A ⊗ₖ C).submatrix (finProdFinEquiv.symm) (finProdFinEquiv.symm) ⊗ₖ
        (B ⊗ₖ D).submatrix (finProdFinEquiv.symm) (finProdFinEquiv.symm) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [tensorOnLabCut, tensorLabEquiv, Matrix.submatrix_apply, Matrix.kronecker_apply,
    Equiv.prodProdProdComm, mul_assoc, mul_left_comm, mul_comm]

theorem tensorOnLabCut_sum {a b c d : ℕ} {K L : Type*} [Fintype K] [Fintype L]
    (ρ : K → BipartiteMatrix a b) (τ : L → BipartiteMatrix c d) :
    tensorOnLabCut (∑ k, ρ k) (∑ l, τ l) = ∑ k, ∑ l, tensorOnLabCut (ρ k) (τ l) := by
  ext i j
  simp [tensorOnLabCut, Matrix.submatrix_apply, Matrix.kronecker_apply, Matrix.sum_apply,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem tensorOnLabCut_smul {a b c d : ℕ}
    (ρ : BipartiteMatrix a b) (τ : BipartiteMatrix c d) (u v : ℂ) :
    tensorOnLabCut (u • ρ) (v • τ) = (u * v) • tensorOnLabCut ρ τ := by
  ext i j
  simp [tensorOnLabCut, Matrix.submatrix_apply, Matrix.kronecker_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem IsDensity.tensorOnLabCut {a b c d : ℕ}
    {ρ : BipartiteMatrix a b} {τ : BipartiteMatrix c d}
    (hρ : IsDensity ρ) (hτ : IsDensity τ) : IsDensity (tensorOnLabCut ρ τ) :=
  (hρ.kronecker hτ).submatrix_equiv (tensorLabEquiv a b c d)

theorem SupportLE.tensorOnLabCut {a b c d : ℕ}
    {ρ σ : BipartiteMatrix a b} {τ υ : BipartiteMatrix c d}
    (h : SupportLE ρ σ) (k : SupportLE τ υ) :
    SupportLE (tensorOnLabCut ρ τ) (tensorOnLabCut σ υ) :=
  (h.kronecker k).submatrix_equiv (tensorLabEquiv a b c d)

theorem IsSeparable.tensorOnLabCut {a b c d : ℕ}
    {ρ : BipartiteMatrix a b} {τ : BipartiteMatrix c d}
    (hρ : IsSeparable a b ρ) (hτ : IsSeparable c d τ) :
    IsSeparable (a * c) (b * d) (tensorOnLabCut ρ τ) := by
  classical
  rcases hρ with ⟨k, t, A, B, ht, htsum, hAB, hρ⟩
  rcases hτ with ⟨l, s, C, D, hs, hssum, hCD, hτ⟩
  let e : Fin (k * l) ≃ (Fin k × Fin l) := finProdFinEquiv.symm
  let weights : Fin (k * l) → ℝ := fun z => t (e z).1 * s (e z).2
  let AA : Fin (k * l) → Matrix (Fin (a * c)) (Fin (a * c)) ℂ := fun z =>
    (A (e z).1 ⊗ₖ C (e z).2).submatrix finProdFinEquiv.symm finProdFinEquiv.symm
  let BB : Fin (k * l) → Matrix (Fin (b * d)) (Fin (b * d)) ℂ := fun z =>
    (B (e z).1 ⊗ₖ D (e z).2).submatrix finProdFinEquiv.symm finProdFinEquiv.symm
  refine ⟨k * l, weights, AA, BB, ?_, ?_, ?_, ?_⟩
  · intro z
    exact mul_nonneg (ht (e z).1) (hs (e z).2)
  · change (∑ z, t (e z).1 * s (e z).2) = 1
    calc
      _ = (∑ i, t i) * (∑ j, s j) := by
        rw [e.sum_comp (fun ij => t ij.1 * s ij.2)]
        simp [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
      _ = 1 := by rw [htsum, hssum, one_mul]
  · intro z
    exact ⟨((hAB (e z).1).1.kronecker (hCD (e z).2).1).submatrix_equiv
        finProdFinEquiv.symm,
      ((hAB (e z).1).2.kronecker (hCD (e z).2).2).submatrix_equiv
        finProdFinEquiv.symm⟩
  · rw [hρ, hτ, tensorOnLabCut_sum]
    simp_rw [tensorOnLabCut_smul, tensorOnLabCut_product]
    let g : (Fin k × Fin l) → BipartiteMatrix (a * c) (b * d) := fun ij =>
      ((t ij.1 : ℂ) * (s ij.2 : ℂ)) •
        ((A ij.1 ⊗ₖ C ij.2).submatrix finProdFinEquiv.symm finProdFinEquiv.symm ⊗ₖ
          (B ij.1 ⊗ₖ D ij.2).submatrix finProdFinEquiv.symm finProdFinEquiv.symm)
    simpa only [g, weights, AA, BB, Fintype.sum_prod_type, Complex.ofReal_mul] using
      (e.sum_comp g).symm

end QuantumProver.AmplitudeDamping.FiniteModel

namespace QuantumProver.AmplitudeDamping.TensorPower
variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

def submatrixStarAlgEquiv (e : K ≃ I) :
    Matrix I I ℂ ≃⋆ₐ[ℝ] Matrix K K ℂ :=
  { Matrix.reindexAlgEquiv ℝ ℂ e.symm with
    map_smul' r A := by
      change (r • A).submatrix e e = r • A.submatrix e e
      rfl
    map_star' A := by
      change (star A).submatrix e e = star (A.submatrix e e)
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix] }

theorem submatrixStarAlgEquiv_apply (e : K ≃ I) (A : Matrix I I ℂ) :
    submatrixStarAlgEquiv e A = A.submatrix e e := rfl

theorem rpow_submatrix_equiv {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (e : K ≃ I) (t : ℝ) :
    CFC.rpow (A.submatrix e e) t = (CFC.rpow A t).submatrix e e := by
  have hc : Continuous (submatrixStarAlgEquiv e) := by
    change Continuous (fun M : Matrix I I ℂ => M.submatrix e e)
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [Matrix.submatrix_apply]
    fun_prop
  have hm := StarAlgHomClass.map_cfc (R := ℝ) (S := ℝ)
    (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (submatrixStarAlgEquiv e) (fun x : ℝ => x ^ t) A
    (A.finite_real_spectrum.continuousOn _) hc hA.1 (hA.submatrix e).1
  have hAK : CFC.rpow (A.submatrix e e) t = cfc (fun x : ℝ => x ^ t) (A.submatrix e e) :=
    CFC.rpow_eq_cfc_real (A := Matrix K K ℂ) (a := A.submatrix e e) (y := t)
      (hA.submatrix e).nonneg
  have hAI : CFC.rpow A t = cfc (fun x : ℝ => x ^ t) A :=
    CFC.rpow_eq_cfc_real (A := Matrix I I ℂ) (a := A) (y := t) hA.nonneg
  rw [hAK, hAI]
  simpa only [submatrixStarAlgEquiv_apply] using hm.symm

theorem trace_submatrix_equiv (A : Matrix I I ℂ) (e : K ≃ I) :
    (A.submatrix e e).trace = A.trace := by
  exact e.sum_comp (fun i => A i i)

theorem sandwichedTrace_submatrix_equiv {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (e : K ≃ I) (α : ℝ) :
    FiniteModel.sandwichedTrace α (ρ.submatrix e e) (σ.submatrix e e) =
      FiniteModel.sandwichedTrace α ρ σ := by
  let t := (1 - α) / (2 * α)
  let W := CFC.rpow σ t
  have hW : W.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := σ) (y := t))
  have hWs : Wᴴ = W := hW.1
  have hX : (W * ρ * W).PosSemidef := by
    simpa only [hWs] using hρ.mul_mul_conjTranspose_same W
  change (CFC.rpow (CFC.rpow (σ.submatrix e e) t * ρ.submatrix e e *
    CFC.rpow (σ.submatrix e e) t) α).trace.re = (CFC.rpow (W * ρ * W) α).trace.re
  rw [rpow_submatrix_equiv hσ e, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, rpow_submatrix_equiv hX e, trace_submatrix_equiv]
end QuantumProver.AmplitudeDamping.TensorPower

namespace QuantumProver.AmplitudeDamping.TensorPower
open scoped Kronecker

theorem sandwichedTrace_tensorOnLabCut {a b c d : ℕ}
    {ρ σ : FiniteModel.BipartiteMatrix a b} {τ υ : FiniteModel.BipartiteMatrix c d}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hτ : τ.PosSemidef) (hυ : υ.PosSemidef) (α : ℝ) :
    FiniteModel.sandwichedTrace α (FiniteModel.tensorOnLabCut ρ τ) (FiniteModel.tensorOnLabCut σ υ) =
      FiniteModel.sandwichedTrace α ρ σ * FiniteModel.sandwichedTrace α τ υ := by
  unfold FiniteModel.tensorOnLabCut
  rw [sandwichedTrace_submatrix_equiv (hρ.kronecker hτ) (hσ.kronecker hυ),
    sandwichedTrace_kronecker hρ hσ hτ hυ]
end QuantumProver.AmplitudeDamping.TensorPower

namespace QuantumProver.AmplitudeDamping.FiniteModel

theorem SupportLE.submatrix_equiv_iff {I K : Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K] {ρ σ : Matrix I I ℂ} (e : K ≃ I) :
    SupportLE (ρ.submatrix e e) (σ.submatrix e e) ↔ SupportLE ρ σ := by
  constructor
  · intro h
    simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
      using h.submatrix_equiv e.symm
  · exact fun h => h.submatrix_equiv e

end QuantumProver.AmplitudeDamping.FiniteModel

namespace QuantumProver.AmplitudeDamping.TensorPower
open scoped Kronecker
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

theorem sandwichedDivergence_submatrix_equiv {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (e : K ≃ I) (α : ℝ) :
    FiniteModel.sandwichedDivergence α (ρ.submatrix e e) (σ.submatrix e e) =
      FiniteModel.sandwichedDivergence α ρ σ := by
  classical
  simp only [FiniteModel.sandwichedDivergence, FiniteModel.SupportLE.submatrix_equiv_iff e,
    sandwichedTrace_submatrix_equiv hρ hσ e α]

theorem sandwichedDivergence_kronecker_of_support {ρ σ : Matrix I I ℂ}
    {τ υ : Matrix J J ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hτ : τ.PosSemidef) (hυ : υ.PosSemidef)
    (hSupport : FiniteModel.SupportLE ρ σ) (kSupport : FiniteModel.SupportLE τ υ)
    (α : ℝ) (hQρ : 0 < FiniteModel.sandwichedTrace α ρ σ)
    (hQτ : 0 < FiniteModel.sandwichedTrace α τ υ) :
    FiniteModel.sandwichedDivergence α (ρ ⊗ₖ τ) (σ ⊗ₖ υ) =
      FiniteModel.sandwichedDivergence α ρ σ + FiniteModel.sandwichedDivergence α τ υ := by
  classical
  have hTensorSupport := hSupport.kronecker kSupport
  simp only [FiniteModel.sandwichedDivergence, if_pos hSupport, if_pos kSupport,
    if_pos hTensorSupport]
  rw [sandwichedTrace_kronecker hρ hσ hτ hυ α, Real.log_mul hQρ.ne' hQτ.ne',
    ← EReal.coe_add]
  congr 1
  ring

theorem sandwichedDivergence_tensorOnLabCut_of_support {a b c d : ℕ}
    {ρ σ : FiniteModel.BipartiteMatrix a b} {τ υ : FiniteModel.BipartiteMatrix c d}
    (hρ : FiniteModel.IsDensity ρ) (hσ : FiniteModel.IsDensity σ)
    (hτ : FiniteModel.IsDensity τ) (hυ : FiniteModel.IsDensity υ)
    (hSupport : FiniteModel.SupportLE ρ σ) (kSupport : FiniteModel.SupportLE τ υ)
    (α : ℝ) (hQρ : 0 < FiniteModel.sandwichedTrace α ρ σ)
    (hQτ : 0 < FiniteModel.sandwichedTrace α τ υ) :
    FiniteModel.sandwichedDivergence α (FiniteModel.tensorOnLabCut ρ τ)
      (FiniteModel.tensorOnLabCut σ υ) =
      FiniteModel.sandwichedDivergence α ρ σ + FiniteModel.sandwichedDivergence α τ υ := by
  unfold FiniteModel.tensorOnLabCut
  rw [sandwichedDivergence_submatrix_equiv (hρ.1.kronecker hτ.1)
    (hσ.1.kronecker hυ.1)]
  exact sandwichedDivergence_kronecker_of_support hρ.1 hσ.1 hτ.1 hυ.1
    hSupport kSupport α hQρ hQτ

end QuantumProver.AmplitudeDamping.TensorPower

namespace QuantumProver.AmplitudeDamping.TensorPower
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem trace_mul_im_eq_zero {A B : Matrix I I ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A * B).trace.im = 0 := by
  have h : star (A * B).trace = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA, hB,
      Matrix.trace_mul_comm]
  have hi := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

end QuantumProver.AmplitudeDamping.TensorPower

namespace QuantumProver.AmplitudeDamping.FiniteModel
open scoped Kronecker

theorem tensorOnLabCut_mul {a b c d : ℕ}
    (ρ σ : BipartiteMatrix a b) (τ υ : BipartiteMatrix c d) :
    tensorOnLabCut ρ τ * tensorOnLabCut σ υ =
      tensorOnLabCut (ρ * σ) (τ * υ) := by
  unfold tensorOnLabCut
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]

theorem trace_tensorOnLabCut {a b c d : ℕ}
    (ρ : BipartiteMatrix a b) (τ : BipartiteMatrix c d) :
    (tensorOnLabCut ρ τ).trace = ρ.trace * τ.trace := by
  unfold tensorOnLabCut
  rw [TensorPower.trace_submatrix_equiv, Matrix.trace_kronecker]

theorem bellProjector_tensorOnLabCut (a c : ℕ) :
    tensorOnLabCut (bellProjector a) (bellProjector c) = bellProjector (a * c) := by
  let e : Fin (a * c) ≃ (Fin a × Fin c) := finProdFinEquiv.symm
  have he (x y : Fin (a * c)) :
      ((e x).1 = (e y).1 ∧ (e x).2 = (e y).2) ↔ x = y := by
    rw [← Prod.ext_iff, e.injective.eq_iff]
  ext ⟨i, j⟩ ⟨k, l⟩
  change
    (if (e i).1 = (e j).1 ∧ (e k).1 = (e l).1 then 1 / (a : ℂ) else 0) *
      (if (e i).2 = (e j).2 ∧ (e k).2 = (e l).2 then 1 / (c : ℂ) else 0) =
        if i = j ∧ k = l then 1 / ((a * c : ℕ) : ℂ) else 0
  by_cases hij : i = j
  · subst j
    by_cases hkl : k = l
    · subst l
      simp [Nat.cast_mul, one_div, _root_.mul_inv_rev, mul_comm]
    · have hparts : (e k).1 ≠ (e l).1 ∨ (e k).2 ≠ (e l).2 := by
        rw [← not_and_or]
        exact (he k l).not.mpr hkl
      rcases hparts with hfirst | hsecond
      · simp [hkl, hfirst]
      · simp [hkl, hsecond]
  · have hparts : (e i).1 ≠ (e j).1 ∨ (e i).2 ≠ (e j).2 := by
      rw [← not_and_or]
      exact (he i j).not.mpr hij
    rcases hparts with hfirst | hsecond
    · simp [hij, hfirst]
    · simp [hij, hsecond]

theorem bellOverlap_tensorOnLabCut {a c : ℕ}
    {ρ : BipartiteMatrix a a} {τ : BipartiteMatrix c c}
    (hρ : ρ.PosSemidef) (hτ : τ.PosSemidef) :
    bellOverlap (a * c) (tensorOnLabCut ρ τ) = bellOverlap a ρ * bellOverlap c τ := by
  unfold bellOverlap
  rw [← bellProjector_tensorOnLabCut a c, tensorOnLabCut_mul, trace_tensorOnLabCut,
    Complex.mul_re, TensorPower.trace_mul_im_eq_zero
      (Identities.bellProjector_isHermitian a) hρ.1,
    TensorPower.trace_mul_im_eq_zero (Identities.bellProjector_isHermitian c) hτ.1,
    zero_mul, sub_zero]

end QuantumProver.AmplitudeDamping.FiniteModel

namespace QuantumProver.AmplitudeDamping.FlagPower

variable {K : Type*} [Fintype K] [DecidableEq K]
variable {H : K → Type*} [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]

def blockDiagonalStarAlgHom :
    (∀ i, Matrix (H i) (H i) ℂ) →⋆ₐ[ℝ] Matrix (Sigma H) (Sigma H) ℂ :=
  { Matrix.blockDiagonal'RingHom H ℂ with
    commutes' r := by
      change Matrix.blockDiagonal' (algebraMap ℝ (∀ i, Matrix (H i) (H i) ℂ) r) =
        algebraMap ℝ (Matrix (Sigma H) (Sigma H) ℂ) r
      rw [Algebra.algebraMap_eq_smul_one, Matrix.blockDiagonal'_smul,
        Matrix.blockDiagonal'_one, Algebra.algebraMap_eq_smul_one]
    map_star' A := by
      change Matrix.blockDiagonal' (fun i => star (A i)) = star (Matrix.blockDiagonal' A)
      simp only [Matrix.star_eq_conjTranspose, Matrix.blockDiagonal'_conjTranspose] }

theorem blockDiagonalStarAlgHom_apply (A : ∀ i, Matrix (H i) (H i) ℂ) :
    blockDiagonalStarAlgHom A = Matrix.blockDiagonal' A := rfl

theorem posSemidef_blockDiagonal' {A : ∀ i, Matrix (H i) (H i) ℂ}
    (hA : ∀ i, (A i).PosSemidef) : (Matrix.blockDiagonal' A).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact map_nonneg (blockDiagonalStarAlgHom (H := H)) (fun i => (hA i).nonneg)

def unitaryBlockDiagonal (U : ∀ i, Matrix.unitaryGroup (H i) ℂ) :
    Matrix.unitaryGroup (Sigma H) ℂ :=
  ⟨Matrix.blockDiagonal' (fun i => (U i : Matrix (H i) (H i) ℂ)), by
    apply Matrix.mem_unitaryGroup_iff.mpr
    rw [Matrix.star_eq_conjTranspose, Matrix.blockDiagonal'_conjTranspose,
      ← Matrix.blockDiagonal'_mul]
    have hU : (fun i => (U i : Matrix (H i) (H i) ℂ) *
        (U i : Matrix (H i) (H i) ℂ)ᴴ) = (1 : ∀ i, Matrix (H i) (H i) ℂ) := by
      funext i
      exact Unitary.coe_mul_star_self (U i)
    rw [hU, Matrix.blockDiagonal'_one]⟩

theorem unitaryBlockDiagonal_conjugate (U : ∀ i, Matrix.unitaryGroup (H i) ℂ)
    (A : ∀ i, Matrix (H i) (H i) ℂ) :
    Unitary.conjStarAlgAut ℝ (Matrix (Sigma H) (Sigma H) ℂ) (unitaryBlockDiagonal U)
      (Matrix.blockDiagonal' A) =
      Matrix.blockDiagonal' (fun i => Unitary.conjStarAlgAut ℝ
        (Matrix (H i) (H i) ℂ) (U i) (A i)) := by
  change Matrix.blockDiagonal' (fun i => (U i : Matrix (H i) (H i) ℂ)) *
      Matrix.blockDiagonal' A *
      (Matrix.blockDiagonal' (fun i => (U i : Matrix (H i) (H i) ℂ)))ᴴ =
    Matrix.blockDiagonal' (fun i => (U i : Matrix (H i) (H i) ℂ) * A i *
      (U i : Matrix (H i) (H i) ℂ)ᴴ)
  rw [Matrix.blockDiagonal'_conjTranspose, ← Matrix.blockDiagonal'_mul,
    ← Matrix.blockDiagonal'_mul]

theorem cfc_blockDiagonal' (f : ℝ → ℝ) {A : ∀ i, Matrix (H i) (H i) ℂ}
    (hA : ∀ i, (A i).IsHermitian) :
    cfc f (Matrix.blockDiagonal' A) =
      Matrix.blockDiagonal' (fun i => cfc f (A i)) := by
  let U : ∀ i, Matrix.unitaryGroup (H i) ℂ := fun i => (hA i).eigenvectorUnitary
  let d : Sigma H → ℝ := fun x => (hA x.1).eigenvalues x.2
  have heq : Matrix.blockDiagonal' A =
      Unitary.conjStarAlgAut ℝ (Matrix (Sigma H) (Sigma H) ℂ) (unitaryBlockDiagonal U)
        (Matrix.diagonal (fun x => (d x : ℂ))) := by
    change Matrix.blockDiagonal' A =
      Unitary.conjStarAlgAut ℝ (Matrix (Sigma H) (Sigma H) ℂ) (unitaryBlockDiagonal U)
        (Matrix.diagonal (fun x : Sigma H => ((hA x.1).eigenvalues x.2 : ℂ)))
    rw [← Matrix.blockDiagonal'_diagonal (fun i j => ((hA i).eigenvalues j : ℂ)),
      unitaryBlockDiagonal_conjugate]
    apply congrArg Matrix.blockDiagonal'
    funext i
    exact (hA i).spectral_theorem
  have hdiag : (Matrix.diagonal (fun x => (d x : ℂ))).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  calc
    cfc f (Matrix.blockDiagonal' A) =
        Unitary.conjStarAlgAut ℝ (Matrix (Sigma H) (Sigma H) ℂ) (unitaryBlockDiagonal U)
          (Matrix.diagonal (fun x => (f (d x) : ℂ))) := by
      rw [heq, TensorPower.cfc_unitary_conjugate f _ hdiag, TensorPower.cfc_diagonal_real]
    _ = Matrix.blockDiagonal' (fun i => cfc f (A i)) := by
      change Unitary.conjStarAlgAut ℝ (Matrix (Sigma H) (Sigma H) ℂ)
        (unitaryBlockDiagonal U)
        (Matrix.diagonal (fun x : Sigma H => (f ((hA x.1).eigenvalues x.2) : ℂ))) = _
      rw [← Matrix.blockDiagonal'_diagonal (fun i j => (f ((hA i).eigenvalues j) : ℂ)),
        unitaryBlockDiagonal_conjugate]
      apply congrArg Matrix.blockDiagonal'
      funext i
      exact (TracePower.cfc_spectral f (hA i)).symm

theorem rpow_blockDiagonal' {A : ∀ i, Matrix (H i) (H i) ℂ}
    (hA : ∀ i, (A i).PosSemidef) (t : ℝ) :
    CFC.rpow (Matrix.blockDiagonal' A) t =
      Matrix.blockDiagonal' (fun i => CFC.rpow (A i) t) := by
  calc
    CFC.rpow (Matrix.blockDiagonal' A) t =
        cfc (fun x : ℝ => x ^ t) (Matrix.blockDiagonal' A) :=
      CFC.rpow_eq_cfc_real (A := Matrix (Sigma H) (Sigma H) ℂ)
        (a := Matrix.blockDiagonal' A) (y := t) (posSemidef_blockDiagonal' hA).nonneg
    _ = Matrix.blockDiagonal' (fun i => cfc (fun x : ℝ => x ^ t) (A i)) :=
      cfc_blockDiagonal' _ (fun i => (hA i).1)
    _ = Matrix.blockDiagonal' (fun i => CFC.rpow (A i) t) := by
      apply congrArg Matrix.blockDiagonal'
      funext i
      exact (CFC.rpow_eq_cfc_real (A := Matrix (H i) (H i) ℂ)
        (a := A i) (y := t) (hA i).nonneg).symm

theorem trace_rpow_blockDiagonal' {A : ∀ i, Matrix (H i) (H i) ℂ}
    (hA : ∀ i, (A i).PosSemidef) (t : ℝ) :
    (CFC.rpow (Matrix.blockDiagonal' A) t).trace =
      ∑ i, (CFC.rpow (A i) t).trace := by
  rw [rpow_blockDiagonal' hA t, Matrix.trace_blockDiagonal']

theorem real_trace_rpow_blockDiagonal' {A : ∀ i, Matrix (H i) (H i) ℂ}
    (hA : ∀ i, (A i).PosSemidef) (t : ℝ) :
    (CFC.rpow (Matrix.blockDiagonal' A) t).trace.re =
      ∑ i, (CFC.rpow (A i) t).trace.re := by
  rw [trace_rpow_blockDiagonal' hA t, Complex.re_sum]

theorem sandwichedTrace_blockDiagonal' {ρ σ : ∀ i, Matrix (H i) (H i) ℂ}
    (hρ : ∀ i, (ρ i).PosSemidef) (hσ : ∀ i, (σ i).PosSemidef) (α : ℝ) :
    FiniteModel.sandwichedTrace α (Matrix.blockDiagonal' ρ) (Matrix.blockDiagonal' σ) =
      ∑ i, FiniteModel.sandwichedTrace α (ρ i) (σ i) := by
  let t := (1 - α) / (2 * α)
  let W : ∀ i, Matrix (H i) (H i) ℂ := fun i => CFC.rpow (σ i) t
  have hW : ∀ i, (W i).PosSemidef := fun i =>
    Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := σ i) (y := t))
  have hX : ∀ i, (W i * ρ i * W i).PosSemidef := by
    intro i
    have hWs : (W i)ᴴ = W i := (hW i).1
    simpa only [hWs] using (hρ i).mul_mul_conjTranspose_same (W i)
  change (CFC.rpow (CFC.rpow (Matrix.blockDiagonal' σ) t * Matrix.blockDiagonal' ρ *
      CFC.rpow (Matrix.blockDiagonal' σ) t) α).trace.re =
    ∑ i, (CFC.rpow (W i * ρ i * W i) α).trace.re
  rw [rpow_blockDiagonal' hσ t, ← Matrix.blockDiagonal'_mul,
    ← Matrix.blockDiagonal'_mul, real_trace_rpow_blockDiagonal' hX α]

end QuantumProver.AmplitudeDamping.FlagPower

namespace QuantumProver.AmplitudeDamping.FiniteModel

theorem SupportLE.blockDiagonal' {K : Type*} [Fintype K] [DecidableEq K]
    {H : K → Type*} [∀ i, Fintype (H i)] [∀ i, DecidableEq (H i)]
    {ρ σ : ∀ i, Matrix (H i) (H i) ℂ} (h : ∀ i, SupportLE (ρ i) (σ i)) :
    SupportLE (Matrix.blockDiagonal' ρ) (Matrix.blockDiagonal' σ) := by
  classical
  choose F hF using fun i => (h i).exists_right_factor
  apply supportLE_of_eq_mul
  rw [← Matrix.blockDiagonal'_mul]
  exact congrArg Matrix.blockDiagonal' (funext hF)

end QuantumProver.AmplitudeDamping.FiniteModel
