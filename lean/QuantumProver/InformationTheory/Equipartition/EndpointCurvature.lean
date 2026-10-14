import QuantumProver.InformationTheory.Equipartition.FixedOrderInduction

noncomputable section
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace QuantumProver.Equipartition.FiniteModel.EndpointCurvature
open FixedMInduction

def narrowScale (zeta : ℝ) (n : ℕ) : ℝ := zeta / ((n : ℝ) * blockLog n)

def narrowBlockBudget (G : ℝ) (M : ℕ) (zeta : ℝ) (n : ℕ) : ℝ :=
  narrowScale zeta n * (n : ℝ) *
    (G * blockLog (n / 16) / ((n / 16 : ℕ) : ℝ) +
      (M : ℝ) * curvatureOrder zeta n * (blockLog (n / 16)) ^ 3)

def narrowMomentBudget (G : ℝ) (M : ℕ) (zeta : ℝ) (n : ℕ) : ℝ :=
  (M : ℝ) / Real.log 2 * (n : ℝ) * (blockLog (n / 16)) ^ 3 +
    (32 * G / zeta) * (n : ℝ) * (blockLog n) ^ 2

def narrowFactor (C G : ℝ) (M : ℕ) (zeta : ℝ) (n : ℕ) : ℝ :=
  Real.exp (8 * zeta * (C + 1) / (3 * blockLog n)) *
    (1 + 2 * narrowBlockBudget G M zeta n)

def matrixTailBudget (n : ℕ) : ℝ :=
  (128 / (Real.log 2 / 2) ^ 2) * Real.rpow 2 (-(n : ℝ))

theorem narrowScale_pos {n : ℕ} (hn : 1 ≤ n) {zeta : ℝ} (hzeta : 0 < zeta) :
    0 < narrowScale zeta n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < blockLog n := lt_of_lt_of_le zero_lt_one (blockLog_ge_one hn)
  unfold narrowScale
  positivity

theorem narrowBlockBudget_nonneg {G zeta : ℝ} (hG : 0 ≤ G) (hzeta : 0 < zeta)
    (M n : ℕ) (hn : 32 ≤ n) : 0 ≤ narrowBlockBudget G M zeta n := by
  have hscale := (narrowScale_pos (by omega : 1 ≤ n) hzeta).le
  have hLm := blockLog_nonneg (n / 16)
  have horder := (curvatureOrder_in_smaller_window hn hzeta).1.le
  unfold narrowBlockBudget
  positivity

theorem narrowBlockBudget_div_scale_sq {G zeta : ℝ} (hG : 0 ≤ G)
    (hzeta : 0 < zeta) (M : ℕ) {n : ℕ} (hn : 32 ≤ n) :
    narrowBlockBudget G M zeta n / (narrowScale zeta n) ^ 2 ≤
      narrowMomentBudget G M zeta n := by
  have hs := shrunk_block_bounds hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmpos : 0 < ((n / 16 : ℕ) : ℝ) := by exact_mod_cast hs.1
  have hLpos : 0 < blockLog n := lt_of_lt_of_le zero_lt_one (blockLog_ge_one (by omega))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : (n : ℝ) / ((n / 16 : ℕ) : ℝ) ≤ 32 := by
    apply (div_le_iff₀ hmpos).mpr
    nlinarith [hs.2.2.1]
  have hlogs : blockLog (n / 16) ≤ blockLog n := blockLog_mono hs.2.1.le
  have hprod : ((n : ℝ) / ((n / 16 : ℕ) : ℝ)) * blockLog (n / 16) ≤
      32 * blockLog n :=
    mul_le_mul hratio hlogs (blockLog_nonneg _) (by norm_num)
  have hGterm : (G / zeta) * (n : ℝ) ^ 2 * blockLog n * blockLog (n / 16) /
      ((n / 16 : ℕ) : ℝ) ≤ (32 * G / zeta) * (n : ℝ) * (blockLog n) ^ 2 := by
    calc
      _ = ((G / zeta) * (n : ℝ) * blockLog n) *
          (((n : ℝ) / ((n / 16 : ℕ) : ℝ)) * blockLog (n / 16)) := by ring
      _ ≤ ((G / zeta) * (n : ℝ) * blockLog n) * (32 * blockLog n) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by ring
  calc
    _ = (M : ℝ) / Real.log 2 * (n : ℝ) * (blockLog (n / 16)) ^ 3 +
        (G / zeta) * (n : ℝ) ^ 2 * blockLog n * blockLog (n / 16) /
          ((n / 16 : ℕ) : ℝ) := by
      unfold narrowBlockBudget narrowScale curvatureOrder
      field_simp [hnpos.ne', hmpos.ne', hLpos.ne', hlog2.ne', hzeta.ne']
      ring
    _ ≤ _ := add_le_add le_rfl hGterm

theorem narrowBlockBudget_le_uniform {G zeta : ℝ} (hG : 0 ≤ G)
    (hzeta : 0 < zeta) (M : ℕ) {n : ℕ} (hn : 32 ≤ n) :
    narrowBlockBudget G M zeta n ≤
      laplaceBudget (32 * zeta * G) (zeta ^ 2 / Real.log 2) M n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < blockLog n := lt_of_lt_of_le zero_lt_one (blockLog_ge_one (by omega))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscale := narrowScale_pos (by omega : 1 ≤ n) hzeta
  have hbudget := narrowBlockBudget_div_scale_sq hG hzeta M hn
  have hlogs : (blockLog (n / 16)) ^ 3 ≤ (blockLog n) ^ 3 :=
    pow_le_pow_left₀ (blockLog_nonneg _) (blockLog_mono (Nat.div_le_self _ _)) 3
  have hbig : narrowMomentBudget G M zeta n ≤
      (M : ℝ) / Real.log 2 * (n : ℝ) * (blockLog n) ^ 3 +
        (32 * G / zeta) * (n : ℝ) * (blockLog n) ^ 2 := by
    exact add_le_add (mul_le_mul_of_nonneg_left hlogs (by positivity)) le_rfl
  calc
    _ = (narrowBlockBudget G M zeta n / (narrowScale zeta n) ^ 2) *
        (narrowScale zeta n) ^ 2 := by field_simp [hscale.ne']
    _ ≤ ((M : ℝ) / Real.log 2 * (n : ℝ) * (blockLog n) ^ 3 +
        (32 * G / zeta) * (n : ℝ) * (blockLog n) ^ 2) *
          (narrowScale zeta n) ^ 2 :=
      mul_le_mul_of_nonneg_right (hbudget.trans hbig) (sq_nonneg _)
    _ = _ := by
      unfold narrowScale laplaceBudget
      field_simp [hnpos.ne', hLpos.ne', hlog2.ne', hzeta.ne']
      ring

theorem uniform_narrowFactor {C G zeta : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hzeta : 0 < zeta) (hsmall : 8 * zeta * (C + 1) / 3 ≤ 2 / 75) :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → ∀ n : ℕ, M ^ 2 ≤ n → 32 ≤ n →
      0 ≤ narrowBlockBudget G M zeta n ∧
      narrowBlockBudget G M zeta n ≤ 1 / (100 * blockLog n) ∧
      narrowFactor C G M zeta n ≤ 1 + 1 / (4 * blockLog n) := by
  have hA : 0 ≤ 32 * zeta * G := by positivity
  have hD : 0 ≤ zeta ^ 2 / Real.log 2 := by positivity
  have hgamma : 0 ≤ 8 * zeta * (C + 1) / 3 := by positivity
  obtain ⟨M0, hfactor⟩ := uniform_curvature_factor hA hD hgamma hsmall
  refine ⟨M0, ?_⟩
  intro M hM n hn hn32
  have hf := hfactor M hM n hn (by omega)
  have hb0 := narrowBlockBudget_nonneg hG hzeta M n hn32
  have hb := narrowBlockBudget_le_uniform hG hzeta M hn32
  refine ⟨hb0, hb.trans hf.2.1, ?_⟩
  have hprod := mul_le_mul_of_nonneg_left
    (show 1 + 2 * narrowBlockBudget G M zeta n ≤
      1 + 2 * laplaceBudget (32 * zeta * G) (zeta ^ 2 / Real.log 2) M n by linarith)
    (Real.exp_pos (8 * zeta * (C + 1) / (3 * blockLog n))).le
  have he : (8 * zeta * (C + 1) / 3) / blockLog n =
      8 * zeta * (C + 1) / (3 * blockLog n) := by ring
  have hh : narrowFactor C G M zeta n ≤
      curvatureFactor (32 * zeta * G) (zeta ^ 2 / Real.log 2)
        (8 * zeta * (C + 1) / 3) M n := by
    simpa only [narrowFactor, curvatureFactor, he] using hprod
  exact hh.trans hf.2.2

theorem matrix_ns_narrow_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {C G zeta center t : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hzeta : 0 < zeta) (hzetaSmall : zeta ≤ Real.log 2 / 8)
    (M : ℕ) {n : ℕ} (hn : 32 ≤ n)
    (hdom : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ))
    (hcenter : -(C * (n : ℝ)) ≤ center)
    (hmean : 0 ≤ umegakiReal ρ σ - center)
    (ht : 0 ≤ t) (ht3 : t ≤ narrowScale zeta n / 3)
    (ha1 : narrowBlockBudget G M zeta n ≤ 1)
    (hLap : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-narrowScale zeta n * (nsLikelihood ρ σ z - center))) ≤
        Real.exp (narrowBlockBudget G M zeta n)) :
    nsWeightedMoment ρ σ center t ≤
      2 * narrowFactor C G M zeta n *
        (narrowMomentBudget G M zeta n +
          ((n : ℝ) * blockLog n / zeta) * (umegakiReal ρ σ - center)) +
        matrixTailBudget n := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL := blockLog_ge_one hn1
  have hLpos : 0 < blockLog n := by linarith
  have ht0 := narrowScale_pos hn1 hzeta
  have ht0small : narrowScale zeta n ≤ zeta := by
    unfold narrowScale
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) * blockLog n)).mpr
    have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
    nlinarith [mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ zeta * (n : ℝ))]
  have htBeta : t ≤ Real.log 2 / 16 := by linarith
  have ha0 := narrowBlockBudget_nonneg hG hzeta M n hn
  have hnativ := nsWeightedMoment_le_laplace_budget hρ hσ hC n hdom hcenter
    ht ht0 ht3 htBeta ha0 ha1 hLap
  have he : 8 * narrowScale zeta n * (C + 1) * (n : ℝ) / 3 =
      8 * zeta * (C + 1) / (3 * blockLog n) := by
    unfold narrowScale
    field_simp [hnpos.ne', hLpos.ne'] <;> ring
  rw [he] at hnativ
  let E := Real.exp (8 * zeta * (C + 1) / (3 * blockLog n))
  let a := narrowBlockBudget G M zeta n
  let s := umegakiReal ρ σ - center
  let u := narrowScale zeta n
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hH : E ≤ narrowFactor C G M zeta n := by
    unfold narrowFactor
    dsimp [E]
    nlinarith [mul_nonneg hE ha0]
  have hcoef : (2 * E / u ^ 2) * (a * (1 + 2 * a) + u * s) ≤
      2 * narrowFactor C G M zeta n * (a / u ^ 2 + s / u) := by
    calc
      _ = 2 * narrowFactor C G M zeta n * (a / u ^ 2) + 2 * E * (s / u) := by
        dsimp [E, a, s, u]
        unfold narrowFactor
        field_simp [ht0.ne'] <;> ring
      _ ≤ 2 * narrowFactor C G M zeta n * (a / u ^ 2) +
          2 * narrowFactor C G M zeta n * (s / u) := by
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hmean ht0.le)
      _ = _ := by ring
  have hratio := narrowBlockBudget_div_scale_sq hG hzeta M hn
  have hsid : s / u = ((n : ℝ) * blockLog n / zeta) * s := by
    dsimp [u, narrowScale]
    field_simp [hzeta.ne', hnpos.ne', hLpos.ne'] <;> ring
  have hbudget : a / u ^ 2 + s / u ≤ narrowMomentBudget G M zeta n +
      ((n : ℝ) * blockLog n / zeta) * s := by
    rw [hsid]
    exact add_le_add hratio le_rfl
  have hfactor0 : 0 ≤ 2 * narrowFactor C G M zeta n := by
    unfold narrowFactor
    positivity
  have htotal := hcoef.trans (mul_le_mul_of_nonneg_left hbudget hfactor0)
  exact hnativ.trans (add_le_add htotal le_rfl)

private theorem ns_weighted_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef) (center t : ℝ) :
    (nsLaw ρ σ hρ hσ).weightedSecondMoment
      (fun z => nsLikelihood ρ σ z - center) 0 t = nsWeightedMoment ρ σ center t := by
  simp only [nsWeightedMoment, nsExpectation, FiniteLaw.weightedSecondMoment,
    FiniteLaw.expect, nsLaw, sub_zero]

theorem matrix_ns_narrow_negative_laplace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {C G zeta center t : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hzeta : 0 < zeta) (hzetaSmall : zeta ≤ Real.log 2 / 8)
    (M : ℕ) {n : ℕ} (hn : 32 ≤ n)
    (hdom : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ))
    (hcenter : -(C * (n : ℝ)) ≤ center)
    (hmean : 0 ≤ umegakiReal ρ σ - center)
    (ht : 0 ≤ t) (ht8 : t ≤ narrowScale zeta n / 8)
    (ha1 : narrowBlockBudget G M zeta n ≤ 1)
    (hH : narrowFactor C G M zeta n ≤ 2)
    (hLap : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-narrowScale zeta n * (nsLikelihood ρ σ z - center))) ≤
        Real.exp (narrowBlockBudget G M zeta n)) :
    (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-t * (nsLikelihood ρ σ z - center))) ≤
        Real.exp (t ^ 2 *
          (narrowFactor C G M zeta n * narrowMomentBudget G M zeta n +
            matrixTailBudget n / 2)) := by
  let P := nsLaw ρ σ hρ hσ
  let X := fun z => nsLikelihood ρ σ z - center
  have ht0 := narrowScale_pos (by omega : 1 ≤ n) hzeta
  have ht3 : t ≤ narrowScale zeta n / 3 := by linarith
  have hw := matrix_ns_narrow_moment hρ hσ hC hG hzeta hzetaSmall M hn
    hdom hcenter hmean ht ht3 ha1 hLap
  have hmu : P.mean X = umegakiReal ρ σ - center := by
    change P.expect (fun z => nsLikelihood ρ σ z - center) = _
    rw [P.expect_sub, P.expect_const]
    exact congrArg (fun x : ℝ => x - center) (nsLaw_mean_eq_umegakiReal ρ σ hρ hσ)
  have hs : 0 ≤ P.mean X := by rw [hmu]; exact hmean
  have hsid : (umegakiReal ρ σ - center) / narrowScale zeta n =
      ((n : ℝ) * blockLog n / zeta) * (umegakiReal ρ σ - center) := by
    unfold narrowScale
    field_simp [hzeta.ne'] <;> ring
  have hw' : P.weightedSecondMoment X 0 t ≤
      2 * narrowFactor C G M zeta n *
        (narrowMomentBudget G M zeta n + P.mean X / narrowScale zeta n) +
          matrixTailBudget n := by
    rw [hmu, hsid]
    rw [ns_weighted_eq hρ hσ]
    exact hw
  have hc := P.laplace_of_mean_dependent_curvature X ht ht0 ht8 hH hs hw'
  exact hc.trans (by simpa only [add_comm] using
    Real.add_one_le_exp (t ^ 2 *
      (narrowFactor C G M zeta n * narrowMomentBudget G M zeta n + matrixTailBudget n / 2)))

theorem matrix_ns_narrow_positive_laplace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {C G zeta center t : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hzeta : 0 < zeta) (hzetaSmall : zeta ≤ Real.log 2 / 8)
    (M : ℕ) {n : ℕ} (hn : 32 ≤ n)
    (hdom : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ))
    (hcenter : -(C * (n : ℝ)) ≤ center)
    (hmean : 0 ≤ umegakiReal ρ σ - center)
    (ht : 0 ≤ t) (ht3 : t ≤ narrowScale zeta n / 3)
    (ha1 : narrowBlockBudget G M zeta n ≤ 1)
    (hLap : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-narrowScale zeta n * (nsLikelihood ρ σ z - center))) ≤
        Real.exp (narrowBlockBudget G M zeta n)) :
    (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (t * (nsLikelihood ρ σ z - center))) ≤
        Real.exp (t * (umegakiReal ρ σ - center) + t ^ 2 *
          (narrowFactor C G M zeta n *
            (narrowMomentBudget G M zeta n +
              ((n : ℝ) * blockLog n / zeta) * (umegakiReal ρ σ - center)) +
            matrixTailBudget n / 2)) := by
  let P := nsLaw ρ σ hρ hσ
  let X := fun z => nsLikelihood ρ σ z - center
  have hw := matrix_ns_narrow_moment hρ hσ hC hG hzeta hzetaSmall M hn
    hdom hcenter hmean ht ht3 ha1 hLap
  have hmu : P.mean X = umegakiReal ρ σ - center := by
    change P.expect (fun z => nsLikelihood ρ σ z - center) = _
    rw [P.expect_sub, P.expect_const]
    exact congrArg (fun x : ℝ => x - center) (nsLaw_mean_eq_umegakiReal ρ σ hρ hσ)
  have hTaylor := P.positive_laplace_taylor_upper X ht
  rw [hmu, ns_weighted_eq hρ hσ] at hTaylor
  have hwmul := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ t ^ 2 / 2)
  have hexact : t ^ 2 / 2 *
      (2 * narrowFactor C G M zeta n *
        (narrowMomentBudget G M zeta n +
          ((n : ℝ) * blockLog n / zeta) * (umegakiReal ρ σ - center)) + matrixTailBudget n) =
      t ^ 2 * (narrowFactor C G M zeta n *
        (narrowMomentBudget G M zeta n +
          ((n : ℝ) * blockLog n / zeta) * (umegakiReal ρ σ - center)) + matrixTailBudget n / 2) := by ring
  rw [hexact] at hwmul
  have hb := hTaylor.trans (add_le_add le_rfl hwmul)
  exact hb.trans (by simpa only [add_assoc, add_comm] using
    Real.add_one_le_exp (t * (umegakiReal ρ σ - center) + t ^ 2 *
      (narrowFactor C G M zeta n *
        (narrowMomentBudget G M zeta n +
          ((n : ℝ) * blockLog n / zeta) * (umegakiReal ρ σ - center)) + matrixTailBudget n / 2)))

theorem petz_lower_of_negative_laplace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    (center : ℝ) {t exponent : ℝ} (ht : 0 < t)
    (hα : 0 < 1 - t / Real.log 2)
    (hLap : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-t * (nsLikelihood ρ σ z - center))) ≤ Real.exp exponent) :
    ((center - exponent / t : ℝ) : EReal) ≤
      petzDivergence ρ σ (1 - t / Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hα1 : 1 - t / Real.log 2 ≠ 1 := by
    have h := div_pos ht hlog2
    linarith
  have hp := petzTrace_pos_of_support ρ σ hρ hσ hs hα
  rw [nsLaw_laplace_centered ρ σ hρ hσ hs center t hα] at hLap
  have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) hp) hLap
  rw [Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp, Real.log_exp] at hlog
  let D := logTwo (petzTrace ρ σ (1 - t / Real.log 2)) /
    ((1 - t / Real.log 2) - 1)
  have hid : Real.log (petzTrace ρ σ (1 - t / Real.log 2)) = -t * D := by
    dsimp [D, logTwo]
    field_simp [hlog2.ne', ht.ne'] <;> ring
  rw [hid] at hlog
  have hb : center - D ≤ exponent / t :=
    (le_div_iff₀ ht).mpr (by nlinarith)
  rw [petzDivergence_of_support ρ σ hρ hσ hs hα hα1]
  apply EReal.coe_le_coe
  change center - exponent / t ≤ D
  linarith

theorem petz_upper_of_positive_laplace {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    (center : ℝ) {t exponent : ℝ} (ht : 0 < t)
    (hLap : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (t * (nsLikelihood ρ σ z - center))) ≤ Real.exp exponent) :
    petzDivergence ρ σ (1 + t / Real.log 2) ≤
      ((center + exponent / t : ℝ) : EReal) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htdiv := div_pos ht hlog2
  have hα : 0 < 1 + t / Real.log 2 := by linarith
  have hα1 : 1 + t / Real.log 2 ≠ 1 := by linarith
  have hp := petzTrace_pos_of_support ρ σ hρ hσ hs hα
  have he := nsLaw_laplace_centered ρ σ hρ hσ hs center (-t)
    (by simpa only [neg_div, sub_neg_eq_add] using hα)
  simp only [neg_neg, neg_div, sub_neg_eq_add] at he
  rw [he] at hLap
  have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) hp) hLap
  rw [Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp, Real.log_exp] at hlog
  let D := logTwo (petzTrace ρ σ (1 + t / Real.log 2)) /
    ((1 + t / Real.log 2) - 1)
  have hid : Real.log (petzTrace ρ σ (1 + t / Real.log 2)) = t * D := by
    dsimp [D, logTwo]
    field_simp [hlog2.ne', ht.ne'] <;> ring
  rw [hid] at hlog
  have hb : D - center ≤ exponent / t := (le_div_iff₀ ht).mpr (by nlinarith)
  rw [petzDivergence_of_support ρ σ hρ hσ hs hα hα1]
  apply EReal.coe_le_coe
  change D ≤ center + exponent / t
  linarith

theorem matrix_petz_narrow_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {C G zeta center t : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hzeta : 0 < zeta) (hzetaSmall : zeta ≤ Real.log 2 / 8)
    (M : ℕ) {n : ℕ} (hn : 32 ≤ n)
    (hdom : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ))
    (hcenter : -(C * (n : ℝ)) ≤ center)
    (hmean : 0 ≤ umegakiReal ρ σ - center)
    (ht : 0 < t) (ht8 : t ≤ narrowScale zeta n / 8)
    (hα : 0 < 1 - t / Real.log 2)
    (ha1 : narrowBlockBudget G M zeta n ≤ 1)
    (hH : narrowFactor C G M zeta n ≤ 2)
    (hLap : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-narrowScale zeta n * (nsLikelihood ρ σ z - center))) ≤
        Real.exp (narrowBlockBudget G M zeta n)) :
    ((center - t * (narrowFactor C G M zeta n * narrowMomentBudget G M zeta n +
      matrixTailBudget n / 2) : ℝ) : EReal) ≤
        petzDivergence ρ σ (1 - t / Real.log 2) := by
  have hs := supportLE_of_real_psd_domination hρ.1 hdom
  have hneg := matrix_ns_narrow_negative_laplace hρ hσ hC hG hzeta hzetaSmall M hn
    hdom hcenter hmean ht.le ht8 ha1 hH hLap
  have hp := petz_lower_of_negative_laplace hρ hσ hs center ht hα hneg
  have hid : t ^ 2 *
      (narrowFactor C G M zeta n * narrowMomentBudget G M zeta n + matrixTailBudget n / 2) / t =
      t * (narrowFactor C G M zeta n * narrowMomentBudget G M zeta n + matrixTailBudget n / 2) := by
    field_simp [ht.ne'] <;> ring
  simpa only [hid] using hp

theorem matrix_petz_narrow_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ρ σ : CMat ι} (hρ : IsState ρ) (hσ : σ.PosSemidef)
    {C G zeta center t : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hzeta : 0 < zeta) (hzetaSmall : zeta ≤ Real.log 2 / 8)
    (M : ℕ) {n : ℕ} (hn : 32 ≤ n)
    (hdom : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ))
    (hcenter : -(C * (n : ℝ)) ≤ center)
    (hmean : 0 ≤ umegakiReal ρ σ - center)
    (ht : 0 < t) (ht3 : t ≤ narrowScale zeta n / 3)
    (ha1 : narrowBlockBudget G M zeta n ≤ 1)
    (hLap : (nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-narrowScale zeta n * (nsLikelihood ρ σ z - center))) ≤
        Real.exp (narrowBlockBudget G M zeta n)) :
    petzDivergence ρ σ (1 + t / Real.log 2) ≤
      ((umegakiReal ρ σ + t *
        (narrowFactor C G M zeta n *
          (narrowMomentBudget G M zeta n +
            ((n : ℝ) * blockLog n / zeta) * (umegakiReal ρ σ - center)) +
          matrixTailBudget n / 2) : ℝ) : EReal) := by
  have hs := supportLE_of_real_psd_domination hρ.1 hdom
  have hpos := matrix_ns_narrow_positive_laplace hρ hσ hC hG hzeta hzetaSmall M hn
    hdom hcenter hmean ht.le ht3 ha1 hLap
  have hp := petz_upper_of_positive_laplace hρ hσ hs center ht hpos
  let B := narrowFactor C G M zeta n *
    (narrowMomentBudget G M zeta n +
      ((n : ℝ) * blockLog n / zeta) * (umegakiReal ρ σ - center)) + matrixTailBudget n / 2
  have hid : (t * (umegakiReal ρ σ - center) + t ^ 2 * B) / t =
      (umegakiReal ρ σ - center) + t * B := by field_simp [ht.ne'] <;> ring
  change petzDivergence ρ σ (1 + t / Real.log 2) ≤
    ((center + (t * (umegakiReal ρ σ - center) + t ^ 2 * B) / t : ℝ) : EReal) at hp
  rw [hid] at hp
  have hcenterId : center + ((umegakiReal ρ σ - center) + t * B) =
      umegakiReal ρ σ + t * B := by ring
  simpa only [hcenterId] using hp

end QuantumProver.Equipartition.FiniteModel.EndpointCurvature
