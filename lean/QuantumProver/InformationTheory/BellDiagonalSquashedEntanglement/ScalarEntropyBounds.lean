import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

noncomputable section

open scoped BigOperators

namespace QuantumProver.BellDiagonalSquashedEntanglement.Scalar

def binaryEntropyBits (p : ℝ) : ℝ :=
  -(p * Real.log p + (1 - p) * Real.log (1 - p)) / Real.log 2

def formationPhi (v : ℝ) : ℝ :=
  binaryEntropyBits ((1 + Real.sqrt (1 - v)) / 2)

def jointDeficit (b u : ℝ) : ℝ :=
  formationPhi (b ^ 2) - formationPhi (b ^ 2 - u ^ 2)

theorem log_two_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

theorem binaryEntropyBits_zero : binaryEntropyBits 0 = 0 := by
  simp [binaryEntropyBits]

theorem binaryEntropyBits_one : binaryEntropyBits 1 = 0 := by
  simp [binaryEntropyBits]

theorem binaryEntropyBits_symm (p : ℝ) :
    binaryEntropyBits (1 - p) = binaryEntropyBits p := by
  have h : 1 - (1 - p) = p := by ring
  unfold binaryEntropyBits
  rw [h]
  congr 1
  ring

theorem log_le_half (r : ℝ) (hr : 0 < r) : Real.log r ≤ r / 2 := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hlog : Real.log r / 2 ≤ Real.sqrt r - 1 := by
    simpa only [Real.log_sqrt (le_of_lt hr)] using
      Real.log_le_sub_one_of_pos hs
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt (le_of_lt hr)
  nlinarith [sq_nonneg (Real.sqrt r - 2)]

theorem square_log_residual (r : ℝ) (hr : 4 ≤ r) :
    0 ≤ r ^ 2 / 8 - Real.log r := by
  have hrpos : 0 < r := by linarith
  have hlog := log_le_half r hrpos
  have hmul : 0 ≤ r * (r - 4) :=
    mul_nonneg (le_of_lt hrpos) (by linarith)
  nlinarith

theorem high_branch_residual (c L r V : ℝ) (hr : 4 ≤ r)
    (hV : c ^ 2 / (2 * Real.log 2) *
      (L - Real.log r + r ^ 2 / 8) ≤ V) :
    c ^ 2 / (2 * Real.log 2) * L ≤ V := by
  have hcoef : 0 ≤ c ^ 2 / (2 * Real.log 2) :=
    div_nonneg (sq_nonneg c) (le_of_lt (mul_pos (by norm_num) log_two_pos))
  have hres := square_log_residual r hr
  have hprod := mul_nonneg hcoef hres
  nlinarith

theorem two_bures_gain_bound (x b₀ b₁ g₀ g₁ loss : ℝ)
    (hx : 0 ≤ x) (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁)
    (hxb : x ≤ b₀ + b₁)
    (hg₀ : b₀ ^ 2 ≤ Real.log 2 * g₀)
    (hg₁ : b₁ ^ 2 ≤ Real.log 2 * g₁)
    (havg : g₀ + g₁ = 2 * loss) :
    x ^ 2 ≤ 4 * Real.log 2 * loss := by
  have hprod : 0 ≤ (b₀ + b₁ - x) * (b₀ + b₁ + x) :=
    mul_nonneg (by linarith) (by linarith)
  have hscaled : Real.log 2 * g₀ + Real.log 2 * g₁ =
      2 * Real.log 2 * loss := by
    rw [← mul_add, havg]
    ring
  nlinarith [sq_nonneg (b₀ - b₁)]

theorem weighted_column_cauchy {ι : Type*} (s : Finset ι)
    (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * x i) ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * x i ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * x i)
  have hprod : (∑ i ∈ s, Real.sqrt (w i) * (Real.sqrt (w i) * x i)) =
      ∑ i ∈ s, w i * x i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have hleft : (∑ i ∈ s, Real.sqrt (w i) ^ 2) = ∑ i ∈ s, w i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (hw i hi)
  have hright : (∑ i ∈ s, (Real.sqrt (w i) * x i) ^ 2) =
      ∑ i ∈ s, w i * x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  simpa only [hprod, hleft, hright] using hcs

theorem flag_gain_replacement (c F Fhat loss : ℝ)
    (hc : 0 ≤ c) (hcF : c ≤ F) (hh : 0 ≤ Fhat)
    (hmoment : Fhat ^ 2 ≤ F * c)
    (hloss : (F - Fhat) ^ 2 ≤ 4 * Real.log 2 * loss) :
    (F - Real.sqrt (F * c)) ^ 2 ≤ 4 * Real.log 2 * loss := by
  have hF : 0 ≤ F := le_trans hc hcF
  have hFc : 0 ≤ F * c := mul_nonneg hF hc
  have hs : 0 ≤ Real.sqrt (F * c) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (F * c) ^ 2 = F * c := Real.sq_sqrt hFc
  have hhat : Fhat ≤ Real.sqrt (F * c) := by nlinarith
  have hmul : 0 ≤ F * (F - c) := mul_nonneg hF (by linarith)
  have hsF : Real.sqrt (F * c) ≤ F := by nlinarith
  have hprod : 0 ≤
      ((F - Fhat) - (F - Real.sqrt (F * c))) *
      ((F - Fhat) + (F - Real.sqrt (F * c))) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem sqrt_product_le_half (c F : ℝ) (hc : 0 ≤ c) (hfour : 4 * c ≤ F) :
    Real.sqrt (F * c) ≤ F / 2 := by
  have hF : 0 ≤ F := by linarith
  have hFc : 0 ≤ F * c := mul_nonneg hF hc
  have hs := Real.sqrt_nonneg (F * c)
  have hsq := Real.sq_sqrt hFc
  have hmul : 0 ≤ F * (F - 4 * c) := mul_nonneg hF (by linarith)
  nlinarith

theorem high_fidelity_flag_loss (c F loss : ℝ) (hc : 0 ≤ c)
    (hfour : 4 * c ≤ F)
    (hloss : (F - Real.sqrt (F * c)) ^ 2 ≤ 4 * Real.log 2 * loss) :
    F ^ 2 / (16 * Real.log 2) ≤ loss := by
  have hF : 0 ≤ F := by linarith
  have hs := sqrt_product_le_half c F hc hfour
  have hroot := Real.sqrt_nonneg (F * c)
  have hprod : 0 ≤ (F / 2 - Real.sqrt (F * c)) *
      (3 * F / 2 - Real.sqrt (F * c)) :=
    mul_nonneg (by linarith) (by linarith)
  have hdenom : 0 < 16 * Real.log (2 : ℝ) := mul_pos (by norm_num) log_two_pos
  apply (div_le_iff₀ hdenom).mpr
  nlinarith

end QuantumProver.BellDiagonalSquashedEntanglement.Scalar

namespace QuantumProver.BellDiagonalSquashedEntanglement.Scalar

theorem binaryEntropyBits_eq_binEntropy (p : ℝ) :
    binaryEntropyBits p = Real.binEntropy p / Real.log 2 := by
  unfold binaryEntropyBits Real.binEntropy
  simp only [Real.log_inv]
  ring

theorem binaryEntropyBits_continuous : Continuous binaryEntropyBits := by
  have h : binaryEntropyBits = fun p => Real.binEntropy p / Real.log 2 :=
    funext binaryEntropyBits_eq_binEntropy
  rw [h]
  exact Real.binEntropy_continuous.div_const _

theorem formationPhi_continuous : Continuous formationPhi := by
  unfold formationPhi
  exact binaryEntropyBits_continuous.comp
    ((continuous_const.add (Real.continuous_sqrt.comp
      (continuous_const.sub continuous_id))).div_const 2)

theorem jointDeficit_continuous :
    Continuous (fun x : ℝ × ℝ => jointDeficit x.1 x.2) := by
  unfold jointDeficit
  exact (formationPhi_continuous.comp (continuous_fst.pow 2)).sub
    (formationPhi_continuous.comp
      ((continuous_fst.pow 2).sub (continuous_snd.pow 2)))

theorem binaryEntropyBits_hasDerivAt (p : ℝ) (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    HasDerivAt binaryEntropyBits
      ((Real.log (1 - p) - Real.log p) / Real.log 2) p := by
  have h : binaryEntropyBits = fun p => Real.binEntropy p / Real.log 2 :=
    funext binaryEntropyBits_eq_binEntropy
  rw [h]
  exact (Real.hasDerivAt_binEntropy hp0 hp1).div_const _

theorem formationPhi_hasDerivAt (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    HasDerivAt formationPhi
      ((Real.log ((1 + Real.sqrt (1 - v)) / 2) -
          Real.log ((1 - Real.sqrt (1 - v)) / 2)) /
        (4 * Real.sqrt (1 - v) * Real.log 2)) v := by
  have harg : 0 < 1 - v := by linarith
  have hs : 0 < Real.sqrt (1 - v) := Real.sqrt_pos.mpr harg
  have hsq : Real.sqrt (1 - v) ^ 2 = 1 - v :=
    Real.sq_sqrt harg.le
  have hs1 : Real.sqrt (1 - v) < 1 := by nlinarith
  have hp0 : (1 + Real.sqrt (1 - v)) / 2 ≠ 0 := by linarith
  have hp1 : (1 + Real.sqrt (1 - v)) / 2 ≠ 1 := by linarith
  have hinner : HasDerivAt (fun t : ℝ => (1 + Real.sqrt (1 - t)) / 2)
      ((-1 / (2 * Real.sqrt (1 - v))) / 2) v := by
    simpa using ((((hasDerivAt_id v).const_sub 1).sqrt harg.ne').const_add 1).div_const 2
  have houter := (binaryEntropyBits_hasDerivAt _ hp0 hp1).comp v hinner
  have hsub : 1 - (1 + Real.sqrt (1 - v)) / 2 =
      (1 - Real.sqrt (1 - v)) / 2 := by ring
  unfold formationPhi
  convert houter using 1
  · rfl
  · rw [hsub]
    field_simp <;> ring

theorem formationPhi_deriv_lower (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    -Real.log v / (4 * Real.log 2) ≤ deriv formationPhi v := by
  rw [(formationPhi_hasDerivAt v hv0 hv1).deriv]
  have harg : 0 < 1 - v := by linarith
  have hs : 0 < Real.sqrt (1 - v) := Real.sqrt_pos.mpr harg
  have hsq := Real.sq_sqrt harg.le
  have hs1 : Real.sqrt (1 - v) < 1 := by nlinarith
  have hplus : 0 < 1 + Real.sqrt (1 - v) := by linarith
  have hminus : 0 < 1 - Real.sqrt (1 - v) := by linarith
  have hmul : (1 + Real.sqrt (1 - v)) * (1 - Real.sqrt (1 - v)) = v :=
    by nlinarith
  have hlog := Real.log_mul hplus.ne' hminus.ne'
  rw [hmul] at hlog
  have hnum : Real.log ((1 + Real.sqrt (1 - v)) / 2) -
      Real.log ((1 - Real.sqrt (1 - v)) / 2) =
      2 * Real.log (1 + Real.sqrt (1 - v)) - Real.log v := by
    rw [Real.log_div hplus.ne' (by norm_num),
      Real.log_div hminus.ne' (by norm_num), hlog]
    ring
  rw [hnum]
  have hp : 0 ≤ Real.log (1 + Real.sqrt (1 - v)) :=
    Real.log_nonneg (by linarith)
  have hvlog : 0 ≤ -Real.log v :=
    neg_nonneg.mpr (Real.log_nonpos hv0.le hv1.le)
  have hprod : 0 ≤ (-Real.log v) * (1 - Real.sqrt (1 - v)) :=
    mul_nonneg hvlog hminus.le
  have hdenom : 0 < 4 * Real.sqrt (1 - v) * Real.log 2 := by
    exact mul_pos (mul_pos (by norm_num) hs) log_two_pos
  apply (le_div_iff₀ hdenom).mpr
  have hcancel : (-Real.log v / (4 * Real.log 2)) *
      (4 * Real.sqrt (1 - v) * Real.log 2) =
      (-Real.log v) * Real.sqrt (1 - v) := by
    field_simp [ne_of_gt log_two_pos]
  rw [hcancel]
  nlinarith

theorem formationPhi_difference_lower (a b : ℝ) (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) :
    (b - a) * (-Real.log b) / (4 * Real.log 2) ≤
      formationPhi b - formationPhi a := by
  have hdiff : DifferentiableOn ℝ formationPhi (Set.Ioo a b) := by
    intro v hv
    exact (formationPhi_hasDerivAt v (by linarith [hv.1])
      (by linarith [hv.2])).differentiableAt.differentiableWithinAt
  obtain ⟨v, hv, heq⟩ := exists_deriv_eq_slope formationPhi hab
    formationPhi_continuous.continuousOn hdiff
  have hv0 : 0 < v := by linarith [hv.1]
  have hv1 : v < 1 := by linarith [hv.2]
  have hderiv := formationPhi_deriv_lower v hv0 hv1
  have hlog : Real.log v ≤ Real.log b := Real.log_le_log hv0 hv.2.le
  have hdenom : 0 < 4 * Real.log (2 : ℝ) :=
    mul_pos (by norm_num) log_two_pos
  have hbound : -Real.log b / (4 * Real.log 2) ≤ deriv formationPhi v :=
    le_trans (div_le_div_of_nonneg_right (by linarith) hdenom.le) hderiv
  rw [heq] at hbound
  have hresult := (le_div_iff₀ (sub_pos.mpr hab)).mp hbound
  convert hresult using 1 <;> ring

theorem jointDeficit_log_lower (c F : ℝ) (hc : 0 < c)
    (hcF : c ≤ F) (hF1 : F ≤ 1) :
    c ^ 2 * Real.log (1 / F) / (2 * Real.log 2) ≤ jointDeficit F c := by
  have hF : 0 < F := lt_of_lt_of_le hc hcF
  have ha : 0 ≤ F ^ 2 - c ^ 2 := by nlinarith
  have hab : F ^ 2 - c ^ 2 < F ^ 2 := by nlinarith
  have hb : F ^ 2 ≤ 1 := by nlinarith
  have hbound := formationPhi_difference_lower (F ^ 2 - c ^ 2) (F ^ 2) ha hab hb
  unfold jointDeficit
  convert hbound using 1
  rw [Real.log_pow, Real.log_div one_ne_zero hF.ne', Real.log_one]
  ring

theorem small_coherence_scalar_reduction (c F V loss : ℝ)
    (hc : 0 < c) (hcF : c ≤ F) (hF1 : F ≤ 1)
    (hadd : jointDeficit F c + loss ≤ V)
    (hloss : (F - Real.sqrt (F * c)) ^ 2 ≤ 4 * Real.log 2 * loss) :
    c ^ 2 * Real.log (1 / (4 * c)) / (2 * Real.log 2) ≤ V := by
  have hF : 0 < F := lt_of_lt_of_le hc hcF
  have hlog2 : 0 < Real.log (2 : ℝ) := log_two_pos
  have hloss0 : 0 ≤ loss := by
    have hdenom : 0 < 4 * Real.log (2 : ℝ) := mul_pos (by norm_num) hlog2
    have hnonneg : 0 ≤ 4 * Real.log 2 * loss :=
      le_trans (sq_nonneg _) hloss
    exact (mul_nonneg_iff_of_pos_left hdenom).mp hnonneg
  have hdeficit := jointDeficit_log_lower c F hc hcF hF1
  have hcoef : 0 ≤ c ^ 2 / (2 * Real.log 2) :=
    div_nonneg (sq_nonneg c) (le_of_lt (mul_pos (by norm_num) hlog2))
  by_cases hlow : F ≤ 4 * c
  · have hlog : Real.log (1 / (4 * c)) ≤ Real.log (1 / F) := by
      apply Real.log_le_log (by positivity)
      exact one_div_le_one_div_of_le hF hlow
    have hscaled := mul_le_mul_of_nonneg_left hlog hcoef
    have hdeficit' : c ^ 2 / (2 * Real.log 2) * Real.log (1 / F) ≤
        jointDeficit F c := by
      convert hdeficit using 1 <;> ring
    have hfinal := le_trans hscaled (le_trans hdeficit' (by linarith :
      jointDeficit F c ≤ V))
    convert hfinal using 1 <;> ring
  · have hfour : 4 * c ≤ F := le_of_lt (lt_of_not_ge hlow)
    have hflag := high_fidelity_flag_loss c F loss hc.le hfour hloss
    have hr : 4 ≤ F / c := (le_div_iff₀ hc).mpr (by linarith)
    have hlog : Real.log (1 / F) = Real.log (1 / c) - Real.log (F / c) := by
      rw [Real.log_div one_ne_zero hF.ne', Real.log_div one_ne_zero hc.ne',
        Real.log_div hF.ne' hc.ne', Real.log_one]
      ring
    have hhigh : c ^ 2 / (2 * Real.log 2) *
        (Real.log (1 / c) - Real.log (F / c) + (F / c) ^ 2 / 8) ≤ V := by
      rw [hlog] at hdeficit
      have hcombined : c ^ 2 *
          (Real.log (1 / c) - Real.log (F / c)) / (2 * Real.log 2) +
          F ^ 2 / (16 * Real.log 2) ≤ V := by linarith
      convert hcombined using 1
      field_simp [hc.ne', hlog2.ne']
      ring
    have hres := high_branch_residual c (Real.log (1 / c)) (F / c) V hr hhigh
    have hlog4 : Real.log (1 / (4 * c)) ≤ Real.log (1 / c) := by
      apply Real.log_le_log (by positivity)
      exact one_div_le_one_div_of_le hc (by linarith)
    have hfinal := le_trans (mul_le_mul_of_nonneg_left hlog4 hcoef) hres
    convert hfinal using 1 <;> ring

end QuantumProver.BellDiagonalSquashedEntanglement.Scalar

namespace QuantumProver.BellDiagonalSquashedEntanglement.DJointSeries

def partialSum (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), 1 / (2 * (j : ℝ) + 3)

def numerator (n : ℕ) : ℝ :=
  2 * ((n : ℝ) + 4) * partialSum n - (2 * (n : ℝ) + 3) +
    3 / (2 * (n : ℝ) + 5)

def coefficient (n : ℕ) : ℝ := numerator n / (4 * ((n : ℝ) + 3))

theorem partialSum_succ (n : ℕ) :
    partialSum (n + 1) = partialSum n + 1 / (2 * (n : ℝ) + 5) := by
  simp only [partialSum, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  congr 1
  congr 1
  ring

theorem partialSum_lower (n : ℕ) :
    ((n : ℝ) + 1) / (2 * (n : ℝ) + 3) ≤ partialSum n := by
  have hterm : ∀ j ∈ Finset.range (n + 1),
      1 / (2 * (n : ℝ) + 3) ≤ 1 / (2 * (j : ℝ) + 3) := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjreal : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hsum := Finset.sum_le_sum hterm
  simpa only [partialSum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul] using hsum

theorem numerator_zero : numerator 0 = 4 / 15 := by
  norm_num [numerator, partialSum]

theorem numerator_succ_sub (n : ℕ) :
    numerator (n + 1) - numerator n =
      2 * partialSum n - 2 * (n : ℝ) / (2 * (n : ℝ) + 5) -
        6 / ((2 * (n : ℝ) + 5) * (2 * (n : ℝ) + 7)) := by
  have h5 : 2 * (n : ℝ) + 5 ≠ 0 := by positivity
  have h7 : 2 * (n : ℝ) + 7 ≠ 0 := by positivity
  simp only [numerator, partialSum_succ, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem numerator_step_identity (n : ℕ) :
    numerator (n + 1) - numerator n =
      2 * (partialSum n - ((n : ℝ) + 1) / (2 * (n : ℝ) + 3)) +
      (16 * (n : ℝ) ^ 2 + 64 * (n : ℝ) + 52) /
        ((2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 5) * (2 * (n : ℝ) + 7)) := by
  rw [numerator_succ_sub]
  have h3 : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  have h5 : 2 * (n : ℝ) + 5 ≠ 0 := by positivity
  have h7 : 2 * (n : ℝ) + 7 ≠ 0 := by positivity
  field_simp
  ring

theorem numerator_step_pos (n : ℕ) : 0 < numerator (n + 1) - numerator n := by
  rw [numerator_step_identity]
  have hfirst : 0 ≤ 2 *
      (partialSum n - ((n : ℝ) + 1) / (2 * (n : ℝ) + 3)) := by
    have h := partialSum_lower n
    linarith
  have hsecond : 0 < (16 * (n : ℝ) ^ 2 + 64 * (n : ℝ) + 52) /
      ((2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 5) * (2 * (n : ℝ) + 7)) := by
    positivity
  exact add_pos_of_nonneg_of_pos hfirst hsecond

theorem numerator_pos (n : ℕ) : 0 < numerator n := by
  induction n with
  | zero => rw [numerator_zero]; norm_num
  | succ n ih =>
      have h := numerator_step_pos n
      linarith

theorem coefficient_pos (n : ℕ) : 0 < coefficient n := by
  exact div_pos (numerator_pos n) (by positivity)

end QuantumProver.BellDiagonalSquashedEntanglement.DJointSeries

namespace QuantumProver.BellDiagonalSquashedEntanglement.DJointSeries

def analyticA (q : ℝ) : ℝ :=
  (Real.log (1 + Real.sqrt q) - Real.log (1 - Real.sqrt q)) /
    (2 * Real.sqrt q)

def analyticK (q : ℝ) : ℝ := (analyticA q - 1) / q

def analyticL (q : ℝ) : ℝ := (analyticK q - 1 / 3) / q

def analyticA1 (q : ℝ) : ℝ := (1 / (1 - q) - analyticK q) / 2

def analyticK1 (q : ℝ) : ℝ := (1 / (1 - q) - 3 * analyticL q) / 2

theorem analyticA_hasSum (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => q ^ n / (2 * (n : ℝ) + 1)) (analyticA q) := by
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
  have hs1 : |Real.sqrt q| < 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg q)]
    nlinarith
  have h : HasSum
      (fun n : ℕ =>
        (2 * (1 / (2 * (n : ℝ) + 1)) * Real.sqrt q ^ (2 * n + 1)) /
          (2 * Real.sqrt q)) (analyticA q) := by
    simpa only [analyticA] using
      (Real.hasSum_log_sub_log_of_abs_lt_one hs1).div_const (2 * Real.sqrt q)
  refine h.congr_fun ?_
  intro n
  rw [pow_add, pow_mul, hsq, pow_one]
  have hn : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hs0.ne', hn]
  <;> ring

theorem analyticK_hasSum (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => q ^ n / (2 * (n : ℝ) + 3)) (analyticK q) := by
  have ht : HasSum
      (fun n : ℕ => q ^ (n + 1) / (2 * ((n + 1 : ℕ) : ℝ) + 1))
        (analyticA q - 1) := by
    simpa using (hasSum_nat_add_iff' 1).mpr (analyticA_hasSum q hq0 hq1)
  have h : HasSum
      (fun n : ℕ => (q ^ (n + 1) / (2 * ((n + 1 : ℕ) : ℝ) + 1)) / q)
        (analyticK q) := by
    simpa only [analyticK] using ht.div_const q
  refine h.congr_fun ?_
  intro n
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hq0.ne', hn]
  <;> ring

theorem analyticL_hasSum (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => q ^ n / (2 * (n : ℝ) + 5)) (analyticL q) := by
  have ht : HasSum
      (fun n : ℕ => q ^ (n + 1) / (2 * ((n + 1 : ℕ) : ℝ) + 3))
        (analyticK q - 1 / 3) := by
    simpa using (hasSum_nat_add_iff' 1).mpr (analyticK_hasSum q hq0 hq1)
  have h : HasSum
      (fun n : ℕ => (q ^ (n + 1) / (2 * ((n + 1 : ℕ) : ℝ) + 3)) / q)
        (analyticL q) := by
    simpa only [analyticL] using ht.div_const q
  refine h.congr_fun ?_
  intro n
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : 2 * (n : ℝ) + 5 ≠ 0 := by positivity
  field_simp [hq0.ne', hn]
  <;> ring

theorem analyticA1_hasSum (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * q ^ n / (2 * (n : ℝ) + 3))
      (analyticA1 q) := by
  have hg : HasSum (fun n : ℕ => q ^ n) (1 / (1 - q)) := by
    simpa only [one_div] using hasSum_geometric_of_lt_one hq0.le hq1
  have h : HasSum
      (fun n : ℕ => (q ^ n - q ^ n / (2 * (n : ℝ) + 3)) / 2)
        (analyticA1 q) := by
    simpa only [analyticA1] using (hg.sub (analyticK_hasSum q hq0 hq1)).div_const 2
  refine h.congr_fun ?_
  intro n
  have hn : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hn]
  <;> ring

theorem analyticK1_hasSum (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * q ^ n / (2 * (n : ℝ) + 5))
      (analyticK1 q) := by
  have hg : HasSum (fun n : ℕ => q ^ n) (1 / (1 - q)) := by
    simpa only [one_div] using hasSum_geometric_of_lt_one hq0.le hq1
  have h : HasSum
      (fun n : ℕ => (q ^ n - 3 * (q ^ n / (2 * (n : ℝ) + 5))) / 2)
        (analyticK1 q) := by
    simpa only [analyticK1] using
      (hg.sub ((analyticL_hasSum q hq0 hq1).mul_left 3)).div_const 2
  refine h.congr_fun ?_
  intro n
  have hn : 2 * (n : ℝ) + 5 ≠ 0 := by positivity
  field_simp [hn]
  <;> ring

theorem analyticK_positive (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    0 < analyticK q := by
  have h := sum_le_hasSum ({0} : Finset ℕ)
    (fun n _ => div_nonneg (pow_nonneg hq0.le n) (by positivity))
    (analyticK_hasSum q hq0 hq1)
  norm_num at h
  linarith

theorem analyticA_hasDerivAt (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt analyticA (analyticA1 q) q := by
  let s := Real.sqrt q
  have hs0 : 0 < s := Real.sqrt_pos.mpr hq0
  have hsq : s ^ 2 = q := Real.sq_sqrt hq0.le
  have hs1 : s < 1 := by nlinarith
  have hplus : 1 + s ≠ 0 := by linarith
  have hminus : 1 - s ≠ 0 := by linarith
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt t) (1 / (2 * s)) q :=
    Real.hasDerivAt_sqrt hq0.ne'
  have hn := ((hs.const_add 1).log hplus).sub ((hs.const_sub 1).log hminus)
  have hd := hs.const_mul 2
  have hratio := hn.div hd (show 2 * Real.sqrt q ≠ 0 by positivity)
  change HasDerivAt (fun t : ℝ =>
    (Real.log (1 + Real.sqrt t) - Real.log (1 - Real.sqrt t)) /
      (2 * Real.sqrt t)) (analyticA1 q) q
  refine hratio.congr_deriv ?_
  change
    (((1 / (2 * s) / (1 + s) - (- (1 / (2 * s))) / (1 - s))) *
      (2 * s) - (Real.log (1 + s) - Real.log (1 - s)) *
      (2 * (1 / (2 * s)))) / (2 * s) ^ 2 = analyticA1 q
  unfold analyticA1 analyticK analyticA
  change
    (((1 / (2 * s) / (1 + s) - (- (1 / (2 * s))) / (1 - s))) *
      (2 * s) - (Real.log (1 + s) - Real.log (1 - s)) *
      (2 * (1 / (2 * s)))) / (2 * s) ^ 2 =
      (1 / (1 - q) - ((Real.log (1 + s) - Real.log (1 - s)) / (2 * s) - 1) / q) / 2
  rw [← hsq]
  have hsne : 1 - s ^ 2 ≠ 0 := by nlinarith
  field_simp [hs0.ne', hplus, hminus, hsne]
  <;> ring

theorem analyticK_hasDerivAt (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt analyticK (analyticK1 q) q := by
  have h := ((analyticA_hasDerivAt q hq0 hq1).sub_const 1).div
    (hasDerivAt_id q) hq0.ne'
  change HasDerivAt (fun t : ℝ => (analyticA t - 1) / t) (analyticK1 q) q
  refine h.congr_deriv ?_
  dsimp only [id, analyticA1, analyticK1, analyticL, analyticK]
  have hne : 1 - q ≠ 0 := by linarith
  field_simp [hq0.ne', hne]
  <;> ring

end QuantumProver.BellDiagonalSquashedEntanglement.DJointSeries

noncomputable section
open scoped BigOperators
namespace QuantumProver.BellDiagonalSquashedEntanglement.DJointSeries

def harmonicA (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), 1 / (2 * (i : ℝ) + 1)

def harmonicL (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), 1 / (2 * (i : ℝ) + 5)

theorem harmonicA_succ (n : ℕ) :
    harmonicA (n + 1) = harmonicA n + 1 / (2 * (n : ℝ) + 3) := by
  simp only [harmonicA, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  congr 1
  congr 1
  ring

theorem harmonicL_succ (n : ℕ) :
    harmonicL (n + 1) = harmonicL n + 1 / (2 * (n : ℝ) + 7) := by
  simp only [harmonicL, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  congr 1
  congr 1
  ring

theorem harmonicA_rewrite (n : ℕ) :
    harmonicA n = 1 + partialSum n - 1 / (2 * (n : ℝ) + 3) := by
  induction n with
  | zero => norm_num [harmonicA, partialSum]
  | succ n ih =>
      rw [harmonicA_succ, partialSum_succ, ih]
      push_cast
      have hden : 2 * ((n : ℝ) + 1) + 3 = 2 * (n : ℝ) + 5 := by ring
      rw [hden]
      ring

theorem harmonicL_rewrite (n : ℕ) :
    harmonicL n = partialSum n - 1 / 3 + 1 / (2 * (n : ℝ) + 5) := by
  induction n with
  | zero => norm_num [harmonicL, partialSum]
  | succ n ih =>
      rw [harmonicL_succ, partialSum_succ, ih]
      push_cast
      have hden : 2 * ((n : ℝ) + 1) + 5 = 2 * (n : ℝ) + 7 := by ring
      rw [hden]
      ring

theorem reciprocal_reflect (n : ℕ) (d : ℝ) :
    (∑ i ∈ Finset.range (n + 1), 1 / (2 * ((n - i : ℕ) : ℝ) + d)) =
      ∑ i ∈ Finset.range (n + 1), 1 / (2 * (i : ℝ) + d) := by
  simpa only [Nat.add_sub_cancel] using
    Finset.sum_range_reflect (fun i : ℕ => (1 : ℝ) / (2 * (i : ℝ) + d)) (n + 1)

theorem symmetric_reciprocal_identity (n i : ℕ) (hi : i ≤ n) :
    1 / ((2 * (i : ℝ) + 3) * (2 * ((n - i : ℕ) : ℝ) + 3)) =
      (1 / (2 * (i : ℝ) + 3) + 1 / (2 * ((n - i : ℕ) : ℝ) + 3)) /
        (2 * ((n : ℝ) + 3)) := by
  have hsum : (i : ℝ) + ((n - i : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.add_sub_of_le hi
  have hi3 : 2 * (i : ℝ) + 3 ≠ 0 := by positivity
  have hj3 : 2 * ((n - i : ℕ) : ℝ) + 3 ≠ 0 := by positivity
  have hn3 : (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hi3, hj3, hn3]
  <;> nlinarith

theorem asymmetric_reciprocal_identity (n i : ℕ) (hi : i ≤ n) :
    1 / ((2 * (i : ℝ) + 1) * (2 * ((n - i : ℕ) : ℝ) + 5)) =
      (1 / (2 * (i : ℝ) + 1) + 1 / (2 * ((n - i : ℕ) : ℝ) + 5)) /
        (2 * ((n : ℝ) + 3)) := by
  have hsum : (i : ℝ) + ((n - i : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.add_sub_of_le hi
  have hi1 : 2 * (i : ℝ) + 1 ≠ 0 := by positivity
  have hj5 : 2 * ((n - i : ℕ) : ℝ) + 5 ≠ 0 := by positivity
  have hn3 : (n : ℝ) + 3 ≠ 0 := by positivity
  field_simp [hi1, hj5, hn3]
  <;> nlinarith

theorem symmetric_reciprocal_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      1 / ((2 * (i : ℝ) + 3) * (2 * ((n - i : ℕ) : ℝ) + 3))) =
      partialSum n / ((n : ℝ) + 3) := by
  calc
    _ = ∑ i ∈ Finset.range (n + 1),
        (1 / (2 * (i : ℝ) + 3) + 1 / (2 * ((n - i : ℕ) : ℝ) + 3)) /
          (2 * ((n : ℝ) + 3)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact symmetric_reciprocal_identity n i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    _ = (partialSum n + partialSum n) / (2 * ((n : ℝ) + 3)) := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, reciprocal_reflect]
      rfl
    _ = _ := by
      have hn3 : (n : ℝ) + 3 ≠ 0 := by positivity
      field_simp [hn3] <;> ring

theorem asymmetric_reciprocal_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      1 / ((2 * (i : ℝ) + 1) * (2 * ((n - i : ℕ) : ℝ) + 5))) =
      (harmonicA n + harmonicL n) / (2 * ((n : ℝ) + 3)) := by
  calc
    _ = ∑ i ∈ Finset.range (n + 1),
        (1 / (2 * (i : ℝ) + 1) + 1 / (2 * ((n - i : ℕ) : ℝ) + 5)) /
          (2 * ((n : ℝ) + 3)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact asymmetric_reciprocal_identity n i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, reciprocal_reflect]
      rfl

theorem first_convolution (n : ℕ) :
    2 * (∑ i ∈ Finset.range (n + 1),
      (((i : ℝ) + 1) / (2 * (i : ℝ) + 3)) *
        (1 / (2 * ((n - i : ℕ) : ℝ) + 3))) =
      ((n : ℝ) + 2) * partialSum n / ((n : ℝ) + 3) := by
  have hsplit (i : ℕ) :
      2 * ((((i : ℝ) + 1) / (2 * (i : ℝ) + 3)) *
        (1 / (2 * ((n - i : ℕ) : ℝ) + 3))) =
      1 / (2 * ((n - i : ℕ) : ℝ) + 3) -
        1 / ((2 * (i : ℝ) + 3) * (2 * ((n - i : ℕ) : ℝ) + 3)) := by
    have hi3 : 2 * (i : ℝ) + 3 ≠ 0 := by positivity
    have hj3 : 2 * ((n - i : ℕ) : ℝ) + 3 ≠ 0 := by positivity
    field_simp [hi3, hj3] <;> ring
  calc
    _ = ∑ i ∈ Finset.range (n + 1),
        (1 / (2 * ((n - i : ℕ) : ℝ) + 3) -
          1 / ((2 * (i : ℝ) + 3) * (2 * ((n - i : ℕ) : ℝ) + 3))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => hsplit i)
    _ = partialSum n - partialSum n / ((n : ℝ) + 3) := by
      rw [Finset.sum_sub_distrib, reciprocal_reflect, symmetric_reciprocal_sum]
      rfl
    _ = _ := by
      have hn3 : (n : ℝ) + 3 ≠ 0 := by positivity
      field_simp [hn3] <;> ring

theorem second_convolution (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      (1 / (2 * (i : ℝ) + 1)) *
        ((((n - i : ℕ) : ℝ) + 1) / (2 * ((n - i : ℕ) : ℝ) + 5))) =
      harmonicA n / 2 -
        3 * (harmonicA n + harmonicL n) / (4 * ((n : ℝ) + 3)) := by
  have hsplit (i : ℕ) :
      (1 / (2 * (i : ℝ) + 1)) *
        ((((n - i : ℕ) : ℝ) + 1) / (2 * ((n - i : ℕ) : ℝ) + 5)) =
      (1 / 2 : ℝ) * (1 / (2 * (i : ℝ) + 1)) -
        (3 / 2 : ℝ) *
          (1 / ((2 * (i : ℝ) + 1) * (2 * ((n - i : ℕ) : ℝ) + 5))) := by
    have hi1 : 2 * (i : ℝ) + 1 ≠ 0 := by positivity
    have hj5 : 2 * ((n - i : ℕ) : ℝ) + 5 ≠ 0 := by positivity
    field_simp [hi1, hj5] <;> ring
  calc
    _ = ∑ i ∈ Finset.range (n + 1),
        ((1 / 2 : ℝ) * (1 / (2 * (i : ℝ) + 1)) -
          (3 / 2 : ℝ) *
            (1 / ((2 * (i : ℝ) + 1) * (2 * ((n - i : ℕ) : ℝ) + 5)))) :=
      Finset.sum_congr rfl (fun i _ => hsplit i)
    _ = (1 / 2 : ℝ) * harmonicA n -
        (3 / 2 : ℝ) *
          ((harmonicA n + harmonicL n) / (2 * ((n : ℝ) + 3))) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        asymmetric_reciprocal_sum]
      rfl
    _ = _ := by
      have hn3 : (n : ℝ) + 3 ≠ 0 := by positivity
      field_simp [hn3] <;> ring

theorem joint_convolution_coefficient (n : ℕ) :
    2 * (∑ i ∈ Finset.range (n + 1),
      (((i : ℝ) + 1) / (2 * (i : ℝ) + 3)) *
        (1 / (2 * ((n - i : ℕ) : ℝ) + 3))) -
      (∑ i ∈ Finset.range (n + 1),
        (1 / (2 * (i : ℝ) + 1)) *
          ((((n - i : ℕ) : ℝ) + 1) / (2 * ((n - i : ℕ) : ℝ) + 5))) =
        coefficient n := by
  rw [first_convolution, second_convolution, harmonicA_rewrite, harmonicL_rewrite]
  unfold coefficient numerator
  have hn3 : (n : ℝ) + 3 ≠ 0 := by positivity
  have hd3 : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  have hd5 : 2 * (n : ℝ) + 5 ≠ 0 := by positivity
  field_simp [hn3, hd3, hd5] <;> ring

theorem norm_summable_of_hasSum_nonneg {f : ℕ → ℝ} {a : ℝ}
    (hf : HasSum f a) (hn : ∀ n, 0 ≤ f n) : Summable (fun n => ‖f n‖) := by
  exact hf.summable.congr (fun n => (Real.norm_of_nonneg (hn n)).symm)

theorem joint_convolution_hasSum (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => coefficient n * q ^ n)
      (2 * analyticA1 q * analyticK q - analyticA q * analyticK1 q) := by
  have hA := analyticA_hasSum q hq0 hq1
  have hK := analyticK_hasSum q hq0 hq1
  have hA1 := analyticA1_hasSum q hq0 hq1
  have hK1 := analyticK1_hasSum q hq0 hq1
  have hAn := norm_summable_of_hasSum_nonneg hA (fun n => by positivity)
  have hKn := norm_summable_of_hasSum_nonneg hK (fun n => by positivity)
  have hA1n := norm_summable_of_hasSum_nonneg hA1 (fun n => by positivity)
  have hK1n := norm_summable_of_hasSum_nonneg hK1 (fun n => by positivity)
  have hp1 : HasSum
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        (((i : ℝ) + 1) * q ^ i / (2 * (i : ℝ) + 3)) *
          (q ^ (n - i) / (2 * ((n - i : ℕ) : ℝ) + 3)))
      (analyticA1 q * analyticK q) := by
    simpa only [hA1.tsum_eq, hK.tsum_eq] using
      hasSum_sum_range_mul_of_summable_norm hA1n hKn
  have hp2 : HasSum
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        (q ^ i / (2 * (i : ℝ) + 1)) *
          ((((n - i : ℕ) : ℝ) + 1) * q ^ (n - i) /
            (2 * ((n - i : ℕ) : ℝ) + 5)))
      (analyticA q * analyticK1 q) := by
    simpa only [hA.tsum_eq, hK1.tsum_eq] using
      hasSum_sum_range_mul_of_summable_norm hAn hK1n
  have h : HasSum
      (fun n : ℕ =>
        2 * (∑ i ∈ Finset.range (n + 1),
          (((i : ℝ) + 1) * q ^ i / (2 * (i : ℝ) + 3)) *
            (q ^ (n - i) / (2 * ((n - i : ℕ) : ℝ) + 3))) -
        (∑ i ∈ Finset.range (n + 1),
          (q ^ i / (2 * (i : ℝ) + 1)) *
            ((((n - i : ℕ) : ℝ) + 1) * q ^ (n - i) /
              (2 * ((n - i : ℕ) : ℝ) + 5))))
      (2 * analyticA1 q * analyticK q - analyticA q * analyticK1 q) := by
    convert (hp1.mul_left 2).sub hp2 using 1 <;> ring
  refine h.congr_fun ?_
  intro n
  symm
  have hpow (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      q ^ i * q ^ (n - i) = q ^ n := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  have hf :
      (∑ i ∈ Finset.range (n + 1),
        (((i : ℝ) + 1) * q ^ i / (2 * (i : ℝ) + 3)) *
          (q ^ (n - i) / (2 * ((n - i : ℕ) : ℝ) + 3))) =
      (∑ i ∈ Finset.range (n + 1),
        (((i : ℝ) + 1) / (2 * (i : ℝ) + 3)) *
          (1 / (2 * ((n - i : ℕ) : ℝ) + 3))) * q ^ n := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = ((((i : ℝ) + 1) / (2 * (i : ℝ) + 3)) *
        (1 / (2 * ((n - i : ℕ) : ℝ) + 3))) * (q ^ i * q ^ (n - i)) := by ring
      _ = _ := by rw [hpow i hi]
  have hg :
      (∑ i ∈ Finset.range (n + 1),
        (q ^ i / (2 * (i : ℝ) + 1)) *
          ((((n - i : ℕ) : ℝ) + 1) * q ^ (n - i) /
            (2 * ((n - i : ℕ) : ℝ) + 5))) =
      (∑ i ∈ Finset.range (n + 1),
        (1 / (2 * (i : ℝ) + 1)) *
          ((((n - i : ℕ) : ℝ) + 1) / (2 * ((n - i : ℕ) : ℝ) + 5))) * q ^ n := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = ((1 / (2 * (i : ℝ) + 1)) *
        ((((n - i : ℕ) : ℝ) + 1) / (2 * ((n - i : ℕ) : ℝ) + 5))) *
          (q ^ i * q ^ (n - i)) := by ring
      _ = _ := by rw [hpow i hi]
  rw [hf, hg]
  calc
    _ = (2 * (∑ i ∈ Finset.range (n + 1),
        (((i : ℝ) + 1) / (2 * (i : ℝ) + 3)) *
          (1 / (2 * ((n - i : ℕ) : ℝ) + 3))) -
      (∑ i ∈ Finset.range (n + 1),
        (1 / (2 * (i : ℝ) + 1)) *
          ((((n - i : ℕ) : ℝ) + 1) / (2 * ((n - i : ℕ) : ℝ) + 5)))) * q ^ n := by ring
    _ = _ := by rw [joint_convolution_coefficient]

theorem analytic_joint_derivative_positive (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    0 < 2 * analyticA1 q * analyticK q - analyticA q * analyticK1 q := by
  have h := sum_le_hasSum ({0} : Finset ℕ)
    (fun n _ => mul_nonneg (coefficient_pos n).le (pow_nonneg hq0.le n))
    (joint_convolution_hasSum q hq0 hq1)
  have h0 : coefficient 0 ≤
      2 * analyticA1 q * analyticK q - analyticA q * analyticK1 q := by
    simpa only [Finset.sum_singleton, pow_zero, mul_one] using h
  exact lt_of_lt_of_le (coefficient_pos 0) h0

end QuantumProver.BellDiagonalSquashedEntanglement.DJointSeries

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace QuantumProver.BellDiagonalSquashedEntanglement.DJointSeries

theorem unit_denominator_positive (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < 1 - q * t ^ 2 := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hmul := mul_le_mul_of_nonneg_left ht2 hq0
  nlinarith

theorem unit_fraction_continuousOn (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (a b : ℕ) :
    ContinuousOn (fun t : ℝ => t ^ a / (1 - q * t ^ 2) ^ b) (Icc (0 : ℝ) 1) := by
  apply (continuousOn_id.pow a).div
    ((continuousOn_const.sub (continuousOn_const.mul (continuousOn_id.pow 2))).pow b)
  intro t ht
  exact pow_ne_zero b (unit_denominator_positive q hq0 hq1 t ht).ne'

def integralPrimitiveK (q t : ℝ) : ℝ :=
  ((Real.log (1 + Real.sqrt q * t) - Real.log (1 - Real.sqrt q * t)) /
    (2 * Real.sqrt q) - t) / q

theorem integralPrimitiveK_hasDerivAt (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (integralPrimitiveK q) (t ^ 2 / (1 - q * t ^ 2)) t := by
  let s := Real.sqrt q
  have hs0 : 0 < s := Real.sqrt_pos.mpr hq0
  have hsq : s ^ 2 = q := Real.sq_sqrt hq0.le
  have hs1 : s < 1 := by nlinarith
  have ht0 : 0 ≤ t := ht.1
  have hplus : 0 < 1 + s * t := by positivity
  have hminus : 0 < 1 - s * t := by
    have hm := mul_le_mul_of_nonneg_left ht.2 hs0.le
    nlinarith
  have hden : 1 - s ^ 2 * t ^ 2 ≠ 0 := by
    simpa only [hsq] using (unit_denominator_positive q hq0.le hq1 t ht).ne'
  have hs := (hasDerivAt_id t).const_mul s
  have hlog := ((hs.const_add 1).log hplus.ne').sub ((hs.const_sub 1).log hminus.ne')
  have h := ((hlog.div_const (2 * s)).sub (hasDerivAt_id t)).div_const q
  dsimp only [id] at h
  change HasDerivAt (fun x : ℝ =>
    ((Real.log (1 + s * x) - Real.log (1 - s * x)) / (2 * s) - x) / q) _ t
  refine h.congr_deriv ?_
  rw [← hsq]
  field_simp [hs0.ne', hplus.ne', hminus.ne', hden] <;> ring

theorem integralPrimitiveK_zero (q : ℝ) : integralPrimitiveK q 0 = 0 := by
  simp [integralPrimitiveK]

theorem integralPrimitiveK_one (q : ℝ) : integralPrimitiveK q 1 = analyticK q := by
  simp [integralPrimitiveK, analyticK, analyticA]

theorem analyticK_eq_integral (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (∫ t in (0 : ℝ)..1, t ^ 2 / (1 - q * t ^ 2)) = analyticK q := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ 2 / (1 - q * t ^ 2)) volume 0 1 := by
    simpa only [pow_one] using
      (unit_fraction_continuousOn q hq0.le hq1 2 1).intervalIntegrable_of_Icc
        (show (0 : ℝ) ≤ 1 by norm_num)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => integralPrimitiveK_hasDerivAt q hq0 hq1 t
      (by simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)) hint
  simpa only [integralPrimitiveK_one, integralPrimitiveK_zero, sub_zero] using h

theorem analyticK1_quotient (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    analyticK1 q = (1 / (1 - q) - 3 * analyticK q) / (2 * q) := by
  have hd : 1 - q ≠ 0 := by linarith
  unfold analyticK1 analyticL
  field_simp [hq0.ne', hd] <;> ring

def integralPrimitiveK1 (q t : ℝ) : ℝ :=
  (t ^ 3 / (1 - q * t ^ 2) - 3 * integralPrimitiveK q t) / (2 * q)

theorem integralPrimitiveK1_hasDerivAt (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (integralPrimitiveK1 q) (t ^ 4 / (1 - q * t ^ 2) ^ 2) t := by
  have hd0 := (unit_denominator_positive q hq0.le hq1 t ht).ne'
  have hid := hasDerivAt_id t
  have hd := ((hid.pow 2).const_mul q).const_sub 1
  have hfirst := (hid.pow 3).div hd hd0
  have h := (hfirst.sub ((integralPrimitiveK_hasDerivAt q hq0 hq1 t ht).const_mul 3)).div_const (2 * q)
  dsimp only [id] at h
  unfold integralPrimitiveK1
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.div_apply, Pi.sub_apply, Pi.neg_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp [hq0.ne', hd0] <;> ring

theorem integralPrimitiveK1_zero (q : ℝ) : integralPrimitiveK1 q 0 = 0 := by
  simp [integralPrimitiveK1, integralPrimitiveK_zero]

theorem integralPrimitiveK1_one (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    integralPrimitiveK1 q 1 = analyticK1 q := by
  simp only [integralPrimitiveK1, one_pow, mul_one, integralPrimitiveK_one]
  exact (analyticK1_quotient q hq0 hq1).symm

theorem analyticK1_eq_integral (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (∫ t in (0 : ℝ)..1, t ^ 4 / (1 - q * t ^ 2) ^ 2) = analyticK1 q := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ 4 / (1 - q * t ^ 2) ^ 2) volume 0 1 :=
    (unit_fraction_continuousOn q hq0.le hq1 4 2).intervalIntegrable_of_Icc
    (show (0 : ℝ) ≤ 1 by norm_num)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => integralPrimitiveK1_hasDerivAt q hq0 hq1 t
      (by simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)) hint
  simpa only [integralPrimitiveK1_one q hq0 hq1, integralPrimitiveK1_zero, sub_zero] using h

def analyticK2 (q : ℝ) : ℝ := (1 / (1 - q) ^ 2 - 5 * analyticK1 q) / (2 * q)

def integralPrimitiveK2Half (q t : ℝ) : ℝ :=
  (t ^ 5 / (1 - q * t ^ 2) ^ 2 - 5 * integralPrimitiveK1 q t) / (4 * q)

theorem integralPrimitiveK2Half_hasDerivAt (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (integralPrimitiveK2Half q) (t ^ 6 / (1 - q * t ^ 2) ^ 3) t := by
  have hd0 := (unit_denominator_positive q hq0.le hq1 t ht).ne'
  have hid := hasDerivAt_id t
  have hd := ((hid.pow 2).const_mul q).const_sub 1
  have hfirst := (hid.pow 5).div (hd.pow 2) (pow_ne_zero 2 hd0)
  have h := (hfirst.sub ((integralPrimitiveK1_hasDerivAt q hq0 hq1 t ht).const_mul 5)).div_const (4 * q)
  dsimp only [id] at h
  unfold integralPrimitiveK2Half
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.div_apply, Pi.sub_apply, Pi.neg_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp [hq0.ne', hd0] <;> ring

theorem integralPrimitiveK2Half_zero (q : ℝ) : integralPrimitiveK2Half q 0 = 0 := by
  simp [integralPrimitiveK2Half, integralPrimitiveK1_zero]

theorem integralPrimitiveK2Half_one (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    integralPrimitiveK2Half q 1 = analyticK2 q / 2 := by
  simp only [integralPrimitiveK2Half, one_pow, mul_one, integralPrimitiveK1_one q hq0 hq1]
  unfold analyticK2
  ring

theorem analyticK2_half_eq_integral (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (∫ t in (0 : ℝ)..1, t ^ 6 / (1 - q * t ^ 2) ^ 3) = analyticK2 q / 2 := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ 6 / (1 - q * t ^ 2) ^ 3) volume 0 1 :=
    (unit_fraction_continuousOn q hq0.le hq1 6 3).intervalIntegrable_of_Icc
    (show (0 : ℝ) ≤ 1 by norm_num)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => integralPrimitiveK2Half_hasDerivAt q hq0 hq1 t
      (by simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)) hint
  simpa only [integralPrimitiveK2Half_one q hq0 hq1, integralPrimitiveK2Half_zero, sub_zero] using h

theorem analyticK1_hasDerivAt (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt analyticK1 (analyticK2 q) q := by
  have hd : 1 - q ≠ 0 := by linarith
  have h2q : 2 * q ≠ 0 := by positivity
  have hInv : HasDerivAt (fun x : ℝ => 1 / (1 - x)) (1 / (1 - q) ^ 2) q := by
    convert ((hasDerivAt_id q).const_sub 1).inv hd using 1
    · funext x
      simp
    · simp
  have hnum := hInv.sub ((analyticK_hasDerivAt q hq0 hq1).const_mul 3)
  have hquot := hnum.div ((hasDerivAt_id q).const_mul 2) h2q
  have hrel := (eq_div_iff h2q).mp (analyticK1_quotient q hq0 hq1)
  have hg : HasDerivAt
      (fun x : ℝ => (1 / (1 - x) - 3 * analyticK x) / (2 * x))
        (analyticK2 q) q := by
    dsimp only [id] at hquot
    refine hquot.congr_deriv ?_
    simp only [Pi.sub_apply, Pi.div_apply, mul_one]
    rw [← hrel]
    unfold analyticK2
    field_simp [hq0.ne', hd] <;> ring
  have he : analyticK1 =ᶠ[𝓝 q]
      (fun x : ℝ => (1 / (1 - x) - 3 * analyticK x) / (2 * x)) := by
    filter_upwards [Ioo_mem_nhds hq0 hq1] with x hx
    exact analyticK1_quotient x hx.1 hx.2
  exact hg.congr_of_eventuallyEq he

theorem analytic_K_second_derivative_inequality (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    2 * analyticK1 q ^ 2 ≤ analyticK q * analyticK2 q := by
  let r := analyticK1 q / analyticK q
  have hK0 := analyticK_positive q hq0 hq1
  have h0 : IntervalIntegrable (fun t : ℝ => t ^ 2 / (1 - q * t ^ 2)) volume 0 1 := by
    simpa only [pow_one] using
      (unit_fraction_continuousOn q hq0.le hq1 2 1).intervalIntegrable_of_Icc
        (show (0 : ℝ) ≤ 1 by norm_num)
  have h1 : IntervalIntegrable (fun t : ℝ => t ^ 4 / (1 - q * t ^ 2) ^ 2) volume 0 1 :=
    (unit_fraction_continuousOn q hq0.le hq1 4 2).intervalIntegrable_of_Icc
    (show (0 : ℝ) ≤ 1 by norm_num)
  have h2 : IntervalIntegrable (fun t : ℝ => t ^ 6 / (1 - q * t ^ 2) ^ 3) volume 0 1 :=
    (unit_fraction_continuousOn q hq0.le hq1 6 3).intervalIntegrable_of_Icc
    (show (0 : ℝ) ≤ 1 by norm_num)
  have hm : IntervalIntegrable
      (fun t : ℝ => (2 * r) * (t ^ 4 / (1 - q * t ^ 2) ^ 2)) volume 0 1 := by
    exact h1.const_mul (2 * r)
  have hz : IntervalIntegrable
      (fun t : ℝ => r ^ 2 * (t ^ 2 / (1 - q * t ^ 2))) volume 0 1 := by
    exact h0.const_mul (r ^ 2)
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (t ^ 2 / (1 - q * t ^ 2)) * (t ^ 2 / (1 - q * t ^ 2) - r) ^ 2 =
        t ^ 6 / (1 - q * t ^ 2) ^ 3 -
          (2 * r) * (t ^ 4 / (1 - q * t ^ 2) ^ 2) +
          r ^ 2 * (t ^ 2 / (1 - q * t ^ 2)) := by
    have hd := (unit_denominator_positive q hq0.le hq1 t ht).ne'
    generalize 1 - q * t ^ 2 = d at hd ⊢
    field_simp [hd] <;> ring
  have hv := intervalIntegral.integral_nonneg (μ := volume) (show (0 : ℝ) ≤ 1 by norm_num)
    (fun t ht => mul_nonneg
      (div_nonneg (sq_nonneg t) (unit_denominator_positive q hq0.le hq1 t ht).le)
      (sq_nonneg (t ^ 2 / (1 - q * t ^ 2) - r)))
  have he :
      (∫ t in (0 : ℝ)..1,
        (t ^ 2 / (1 - q * t ^ 2)) * (t ^ 2 / (1 - q * t ^ 2) - r) ^ 2) =
      (∫ t in (0 : ℝ)..1,
        (t ^ 6 / (1 - q * t ^ 2) ^ 3 -
          (2 * r) * (t ^ 4 / (1 - q * t ^ 2) ^ 2)) +
          r ^ 2 * (t ^ 2 / (1 - q * t ^ 2))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hp t (by simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)
  rw [he, intervalIntegral.integral_add (h2.sub hm) hz,
    intervalIntegral.integral_sub h2 hm, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, analyticK_eq_integral q hq0 hq1,
    analyticK1_eq_integral q hq0 hq1, analyticK2_half_eq_integral q hq0 hq1] at hv
  have hscale := mul_nonneg (show 0 ≤ 2 * analyticK q by positivity) hv
  have hcancel :
      2 * analyticK q * (analyticK2 q / 2 - (2 * r) * analyticK1 q + r ^ 2 * analyticK q) =
        analyticK q * analyticK2 q - 2 * analyticK1 q ^ 2 := by
    dsimp only [r]
    field_simp [hK0.ne'] <;> ring
  rw [hcancel] at hscale
  linarith

def reciprocalK (q : ℝ) : ℝ := (analyticK q)⁻¹

def reciprocalK1 (q : ℝ) : ℝ := -analyticK1 q / analyticK q ^ 2

def reciprocalK2 (q : ℝ) : ℝ :=
  (2 * analyticK1 q ^ 2 - analyticK q * analyticK2 q) / analyticK q ^ 3

theorem reciprocalK_hasDerivAt (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt reciprocalK (reciprocalK1 q) q := by
  have hK0 := analyticK_positive q hq0 hq1
  exact (analyticK_hasDerivAt q hq0 hq1).inv hK0.ne'

theorem reciprocalK1_hasDerivAt (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt reciprocalK1 (reciprocalK2 q) q := by
  have hK0 := analyticK_positive q hq0 hq1
  have h := ((analyticK1_hasDerivAt q hq0 hq1).neg).div
    ((analyticK_hasDerivAt q hq0 hq1).pow 2) (pow_ne_zero 2 hK0.ne')
  unfold reciprocalK1 reciprocalK2
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.neg_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [hK0.ne'] <;> ring

theorem reciprocalK2_nonpositive (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    reciprocalK2 q ≤ 0 := by
  have h := analytic_K_second_derivative_inequality q hq0 hq1
  have hK0 := analyticK_positive q hq0 hq1
  unfold reciprocalK2
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (by positivity)

theorem reciprocalK_concaveOn : ConcaveOn ℝ (Ioo (0 : ℝ) 1) reciprocalK := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos
    (f' := reciprocalK1) (f'' := reciprocalK2) (convex_Ioo 0 1)
  · intro q hq
    exact (reciprocalK_hasDerivAt q hq.1 hq.2).continuousAt.continuousWithinAt
  · intro q hq
    have hqi : q ∈ Ioo (0 : ℝ) 1 := interior_subset hq
    exact (reciprocalK_hasDerivAt q hqi.1 hqi.2).hasDerivWithinAt
  · intro q hq
    have hqi : q ∈ Ioo (0 : ℝ) 1 := interior_subset hq
    exact (reciprocalK1_hasDerivAt q hqi.1 hqi.2).hasDerivWithinAt
  · intro q hq
    have hqi : q ∈ Ioo (0 : ℝ) 1 := interior_subset hq
    exact reciprocalK2_nonpositive q hqi.1 hqi.2

end QuantumProver.BellDiagonalSquashedEntanglement.DJointSeries

noncomputable section
open Set
open scoped BigOperators Topology
namespace QuantumProver.BellDiagonalSquashedEntanglement.DJointSeries

theorem analyticA_positive (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    0 < analyticA q := by
  have h := sum_le_hasSum ({0} : Finset ℕ)
    (fun n _ => div_nonneg (pow_nonneg hq0.le n) (by positivity))
    (analyticA_hasSum q hq0 hq1)
  norm_num at h
  linarith

theorem analyticA1_positive (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    0 < analyticA1 q := by
  have h := sum_le_hasSum ({0} : Finset ℕ)
    (fun n _ => div_nonneg (mul_nonneg (by positivity) (pow_nonneg hq0.le n))
      (by positivity)) (analyticA1_hasSum q hq0 hq1)
  norm_num at h
  linarith

theorem analytic_A_K_identity (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    analyticA q - 2 * (1 - q) * analyticA1 q = analyticK q := by
  unfold analyticA1 analyticK
  field_simp [hq0.ne', (show 1 - q ≠ 0 by linarith)]
  ring

theorem reciprocalK_tangent (q Q : ℝ) (hq0 : 0 < q) (hqQ : q ≤ Q) (hQ1 : Q < 1) :
    reciprocalK q - reciprocalK Q ≤
      (Q - q) * analyticK1 Q / analyticK Q ^ 2 := by
  by_cases h : q = Q
  · subst Q
    simp
  · have hlt : q < Q := lt_of_le_of_ne hqQ h
    have h := reciprocalK_concaveOn.le_slope_of_hasDerivAt
      (show q ∈ Ioo (0 : ℝ) 1 from ⟨hq0, hqQ.trans_lt hQ1⟩)
      (show Q ∈ Ioo (0 : ℝ) 1 from ⟨hq0.trans_le hqQ, hQ1⟩)
      hlt (reciprocalK_hasDerivAt Q (hq0.trans_le hqQ) hQ1)
    rw [slope_def_field] at h
    have h := (le_div_iff₀ (sub_pos.mpr hlt)).mp h
    unfold reciprocalK1 at h
    have heq : -analyticK1 Q / analyticK Q ^ 2 * (Q - q) =
      -((Q - q) * analyticK1 Q / analyticK Q ^ 2) := by ring
    rw [heq] at h
    linarith

theorem reciprocalK_tangent_cross (q Q : ℝ) (hq0 : 0 < q)
    (hqQ : q ≤ Q) (hQ1 : Q < 1) :
    analyticK Q ^ 2 - analyticK q * analyticK Q ≤
      (Q - q) * analyticK q * analyticK1 Q := by
  have ht := reciprocalK_tangent q Q hq0 hqQ hQ1
  have hqK := analyticK_positive q hq0 (hqQ.trans_lt hQ1)
  have hQK := analyticK_positive Q (hq0.trans_le hqQ) hQ1
  have hs := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ analyticK q * analyticK Q ^ 2 by positivity)
  have hleft : analyticK q * analyticK Q ^ 2 * (reciprocalK q - reciprocalK Q) =
      analyticK Q ^ 2 - analyticK q * analyticK Q := by
    unfold reciprocalK
    field_simp [hqK.ne', hQK.ne'] <;> ring
  have hright : analyticK q * analyticK Q ^ 2 *
      ((Q - q) * analyticK1 Q / analyticK Q ^ 2) =
      (Q - q) * analyticK q * analyticK1 Q := by
    field_simp [hQK.ne']
  rwa [hleft, hright] at hs

theorem analytic_hessian_determinant_nonnegative (q Q : ℝ)
    (hq0 : 0 < q) (hqQ : q ≤ Q) (hQ1 : Q < 1) :
    0 ≤ analyticK q * (analyticA Q + 2 * (Q - q) * analyticA1 Q) -
      analyticA Q * analyticK Q := by
  have hQ0 := hq0.trans_le hqQ
  have hA := analyticA_positive Q hQ0 hQ1
  have hK := analyticK_positive Q hQ0 hQ1
  have hKq := analyticK_positive q hq0 (hqQ.trans_lt hQ1)
  have ht := mul_le_mul_of_nonneg_left
    (reciprocalK_tangent_cross q Q hq0 hqQ hQ1) hA.le
  have hB := mul_nonneg
    (show 0 ≤ (Q - q) * analyticK q by positivity)
    (analytic_joint_derivative_positive Q hQ0 hQ1).le
  have hdet : 0 ≤ (analyticK q * (analyticA Q + 2 * (Q - q) * analyticA1 Q) -
      analyticA Q * analyticK Q) * analyticK Q := by
    nlinarith
  exact (mul_nonneg_iff_of_pos_right hK).mp hdet

def hessianBB (b u : ℝ) : ℝ :=
  analyticK (1 - b ^ 2) - analyticA (1 - b ^ 2 + u ^ 2) +
    2 * b ^ 2 * analyticA1 (1 - b ^ 2 + u ^ 2)

def hessianBU (b u : ℝ) : ℝ := -2 * b * u * analyticA1 (1 - b ^ 2 + u ^ 2)

def hessianUU (b u : ℝ) : ℝ :=
  analyticA (1 - b ^ 2 + u ^ 2) + 2 * u ^ 2 * analyticA1 (1 - b ^ 2 + u ^ 2)

theorem hessianUU_positive (b u : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hu : |u| < b) : 0 < hessianUU b u := by
  have hq0 : 0 < 1 - b ^ 2 + u ^ 2 := by nlinarith [sq_nonneg u]
  have hq1 : 1 - b ^ 2 + u ^ 2 < 1 := by
    have hs := (sq_lt_sq₀ (abs_nonneg u) hb0.le).mpr hu
    nlinarith [sq_abs u]
  unfold hessianUU
  exact add_pos_of_pos_of_nonneg (analyticA_positive _ hq0 hq1)
    (mul_nonneg (by positivity) (analyticA1_positive _ hq0 hq1).le)

theorem hessian_determinant_identity (b u : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hu : |u| < b) :
    hessianBB b u * hessianUU b u - hessianBU b u ^ 2 =
      analyticK (1 - b ^ 2) *
        (analyticA (1 - b ^ 2 + u ^ 2) + 2 * u ^ 2 * analyticA1 (1 - b ^ 2 + u ^ 2)) -
      analyticA (1 - b ^ 2 + u ^ 2) * analyticK (1 - b ^ 2 + u ^ 2) := by
  have hq0 : 0 < 1 - b ^ 2 + u ^ 2 := by nlinarith [sq_nonneg u]
  have hq1 : 1 - b ^ 2 + u ^ 2 < 1 := by
    have hs := (sq_lt_sq₀ (abs_nonneg u) hb0.le).mpr hu
    nlinarith [sq_abs u]
  have hrel := analytic_A_K_identity (1 - b ^ 2 + u ^ 2) hq0 hq1
  rw [← hrel]
  unfold hessianBB hessianUU hessianBU
  ring

theorem hessian_determinant_nonnegative (b u : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (hu : |u| < b) :
    0 ≤ hessianBB b u * hessianUU b u - hessianBU b u ^ 2 := by
  have hq0 : 0 < 1 - b ^ 2 := by nlinarith
  have hqQ : 1 - b ^ 2 ≤ 1 - b ^ 2 + u ^ 2 := by nlinarith [sq_nonneg u]
  have hQ1 : 1 - b ^ 2 + u ^ 2 < 1 := by
    have hs := (sq_lt_sq₀ (abs_nonneg u) hb0.le).mpr hu
    nlinarith [sq_abs u]
  rw [hessian_determinant_identity b u hb0 hb1 hu]
  simpa only [add_sub_cancel_left] using
    analytic_hessian_determinant_nonnegative (1 - b ^ 2) (1 - b ^ 2 + u ^ 2)
      hq0 hqQ hQ1

theorem hessian_quadratic_nonnegative (b u x y : ℝ)
    (hb0 : 0 < b) (hb1 : b < 1) (hu : |u| < b) :
    0 ≤ hessianBB b u * x ^ 2 + 2 * hessianBU b u * x * y + hessianUU b u * y ^ 2 := by
  have hd := hessianUU_positive b u hb0 hb1 hu
  have hdet := hessian_determinant_nonnegative b u hb0 hb1 hu
  have hnum := add_nonneg (sq_nonneg (hessianUU b u * y + hessianBU b u * x))
    (mul_nonneg hdet (sq_nonneg x))
  have heq : (hessianUU b u * y + hessianBU b u * x) ^ 2 +
      (hessianBB b u * hessianUU b u - hessianBU b u ^ 2) * x ^ 2 =
      hessianUU b u *
        (hessianBB b u * x ^ 2 + 2 * hessianBU b u * x * y + hessianUU b u * y ^ 2) := by ring
  rw [heq] at hnum
  exact (mul_nonneg_iff_of_pos_left hd).mp hnum

end QuantumProver.BellDiagonalSquashedEntanglement.DJointSeries

noncomputable section
open Set
open scoped Topology
namespace QuantumProver.BellDiagonalSquashedEntanglement.DJointSeries

theorem formationPhi_hasDerivAt_analyticA (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    HasDerivAt Scalar.formationPhi (analyticA (1 - v) / (2 * Real.log 2)) v := by
  have h := Scalar.formationPhi_hasDerivAt v hv0 hv1
  have hs0 : 0 < Real.sqrt (1 - v) := Real.sqrt_pos.mpr (by linarith)
  have hs1 : Real.sqrt (1 - v) < 1 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 - v by linarith)]
  have hp : 1 + Real.sqrt (1 - v) ≠ 0 := by positivity
  have hm : 1 - Real.sqrt (1 - v) ≠ 0 := by linarith
  refine h.congr_deriv ?_
  rw [Real.log_div hp (by norm_num), Real.log_div hm (by norm_num)]
  unfold analyticA
  field_simp [hs0.ne', Scalar.log_two_pos.ne']
  ring

def jointLine (b u x y t : ℝ) : ℝ :=
  Real.log 2 * Scalar.jointDeficit (b + t * x) (u + t * y)

def jointLine1 (b u x y t : ℝ) : ℝ :=
  x * (b + t * x) * (analyticA (1 - (b + t * x) ^ 2) -
    analyticA (1 - (b + t * x) ^ 2 + (u + t * y) ^ 2)) +
  y * (u + t * y) * analyticA (1 - (b + t * x) ^ 2 + (u + t * y) ^ 2)

def jointLine2 (b u x y t : ℝ) : ℝ :=
  hessianBB (b + t * x) (u + t * y) * x ^ 2 +
    2 * hessianBU (b + t * x) (u + t * y) * x * y +
      hessianUU (b + t * x) (u + t * y) * y ^ 2

theorem jointLine_hasDerivAt (b u x y t : ℝ)
    (hb0 : 0 < b + t * x) (hb1 : b + t * x < 1)
    (hu : |u + t * y| < b + t * x) :
    HasDerivAt (jointLine b u x y) (jointLine1 b u x y t) t := by
  have hsq : (u + t * y) ^ 2 < (b + t * x) ^ 2 := by
    nlinarith [(sq_lt_sq₀ (abs_nonneg (u + t * y)) hb0.le).mpr hu, sq_abs (u + t * y)]
  have hv0 : 0 < (b + t * x) ^ 2 := sq_pos_of_pos hb0
  have hv1 : (b + t * x) ^ 2 < 1 := by nlinarith
  have hw0 : 0 < (b + t * x) ^ 2 - (u + t * y) ^ 2 := by linarith
  have hw1 : (b + t * x) ^ 2 - (u + t * y) ^ 2 < 1 := by nlinarith [sq_nonneg (u + t * y)]
  have hb := ((hasDerivAt_id t).mul_const x).const_add b
  have hu' := ((hasDerivAt_id t).mul_const y).const_add u
  have hfirst := (formationPhi_hasDerivAt_analyticA _ hv0 hv1).comp t (hb.pow 2)
  have hsecond := (formationPhi_hasDerivAt_analyticA _ hw0 hw1).comp t
    ((hb.pow 2).sub (hu'.pow 2))
  have h := (hfirst.sub hsecond).const_mul (Real.log 2)
  unfold jointLine Scalar.jointDeficit jointLine1
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.sub_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul]
  rw [show 1 - ((b + t * x) ^ 2 - (u + t * y) ^ 2) =
    1 - (b + t * x) ^ 2 + (u + t * y) ^ 2 by ring]
  field_simp [Scalar.log_two_pos.ne']
  ring

theorem jointLine1_hasDerivAt (b u x y t : ℝ)
    (hb0 : 0 < b + t * x) (hb1 : b + t * x < 1)
    (hu : |u + t * y| < b + t * x) :
    HasDerivAt (jointLine1 b u x y) (jointLine2 b u x y t) t := by
  have hq0 : 0 < 1 - (b + t * x) ^ 2 := by nlinarith
  have hq1 : 1 - (b + t * x) ^ 2 < 1 := by nlinarith
  have hQ0 : 0 < 1 - (b + t * x) ^ 2 + (u + t * y) ^ 2 := by nlinarith [sq_nonneg (u + t * y)]
  have hQ1 : 1 - (b + t * x) ^ 2 + (u + t * y) ^ 2 < 1 := by
    nlinarith [(sq_lt_sq₀ (abs_nonneg (u + t * y)) hb0.le).mpr hu, sq_abs (u + t * y)]
  have hb := ((hasDerivAt_id t).mul_const x).const_add b
  have hu' := ((hasDerivAt_id t).mul_const y).const_add u
  have hq := (hb.pow 2).const_sub 1
  have hQ := hq.add (hu'.pow 2)
  have hA := (analyticA_hasDerivAt _ hq0 hq1).comp t hq
  have hAQ := (analyticA_hasDerivAt _ hQ0 hQ1).comp t hQ
  have h := ((hb.mul (hA.sub hAQ)).const_mul x).add ((hu'.mul hAQ).const_mul y)
  have hK := analytic_A_K_identity (1 - (b + t * x) ^ 2) hq0 hq1
  rw [show 1 - (1 - (b + t * x) ^ 2) = (b + t * x) ^ 2 by ring] at hK
  have hAeq : analyticA (1 - (b + t * x) ^ 2) =
      analyticK (1 - (b + t * x) ^ 2) +
        2 * (b + t * x) ^ 2 * analyticA1 (1 - (b + t * x) ^ 2) := by linarith
  unfold jointLine1 jointLine2
  convert h using 1
  · funext v
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, Function.comp_apply, id_eq]
    ring
  · simp only [Pi.pow_apply, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Function.comp_apply,
      id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul]
    unfold hessianBB hessianBU hessianUU
    rw [hAeq]
    ring

def signedTriangleInterior : Set (ℝ × ℝ) :=
  {z | 0 < z.1 ∧ z.1 < 1 ∧ |z.2| < z.1}

theorem signedTriangleInterior_convex : Convex ℝ signedTriangleInterior := by
  intro z hz w hw r s hr hs hrs
  change 0 < r * z.1 + s * w.1 ∧ r * z.1 + s * w.1 < 1 ∧
    |r * z.2 + s * w.2| < r * z.1 + s * w.1
  rcases hz with ⟨hz0, hz1, hzu⟩
  rcases hw with ⟨hw0, hw1, hwu⟩
  have hzu' := abs_lt.mp hzu
  have hwu' := abs_lt.mp hwu
  rcases eq_or_lt_of_le hr with hr | hr
  · have hr0 : r = 0 := hr.symm
    have hs1 : s = 1 := by linarith
    simpa [hr0, hs1] using (show 0 < w.1 ∧ w.1 < 1 ∧ |w.2| < w.1 from ⟨hw0, hw1, hwu⟩)
  · have h0 := add_pos_of_pos_of_nonneg (mul_pos hr hz0) (mul_nonneg hs hw0.le)
    have h1 := add_pos_of_pos_of_nonneg (mul_pos hr (show 0 < 1 - z.1 by linarith))
      (mul_nonneg hs (show 0 ≤ 1 - w.1 by linarith))
    have hlu := add_pos_of_pos_of_nonneg (mul_pos hr (show 0 < z.1 + z.2 by linarith [hzu'.1]))
      (mul_nonneg hs (show 0 ≤ w.1 + w.2 by linarith [hwu'.1]))
    have hru := add_pos_of_pos_of_nonneg (mul_pos hr (show 0 < z.1 - z.2 by linarith [hzu'.2]))
      (mul_nonneg hs (show 0 ≤ w.1 - w.2 by linarith [hwu'.2]))
    refine ⟨h0, by nlinarith, abs_lt.mpr ⟨by nlinarith, by nlinarith⟩⟩

theorem jointLine_segment_mem (z w : ℝ × ℝ) (hz : z ∈ signedTriangleInterior)
    (hw : w ∈ signedTriangleInterior) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (z.1 + t * (w.1 - z.1), z.2 + t * (w.2 - z.2)) ∈ signedTriangleInterior := by
  have h := signedTriangleInterior_convex hz hw (show 0 ≤ 1 - t by linarith [ht.2])
    ht.1 (show (1 - t) + t = 1 by ring)
  convert h using 1 <;> ext <;> simp [smul_eq_mul] <;> ring

theorem jointLine_continuous (b u x y : ℝ) : Continuous (jointLine b u x y) := by
  have hv : Continuous (fun t : ℝ => (b + t * x) ^ 2) := by fun_prop
  have hw : Continuous (fun t : ℝ => (b + t * x) ^ 2 - (u + t * y) ^ 2) := by fun_prop
  exact continuous_const.mul
    ((Scalar.formationPhi_continuous.comp hv).sub (Scalar.formationPhi_continuous.comp hw))

theorem jointLine_segment_convex (z w : ℝ × ℝ)
    (hz : z ∈ signedTriangleInterior) (hw : w ∈ signedTriangleInterior) :
    ConvexOn ℝ (Icc (0 : ℝ) 1)
      (jointLine z.1 z.2 (w.1 - z.1) (w.2 - z.2)) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (f' := jointLine1 z.1 z.2 (w.1 - z.1) (w.2 - z.2))
    (f'' := jointLine2 z.1 z.2 (w.1 - z.1) (w.2 - z.2)) (convex_Icc 0 1)
  · exact (jointLine_continuous _ _ _ _).continuousOn
  · intro t ht
    rcases jointLine_segment_mem z w hz hw t (interior_subset ht) with ⟨hb0, hb1, hu⟩
    exact (jointLine_hasDerivAt _ _ _ _ t hb0 hb1 hu).hasDerivWithinAt
  · intro t ht
    rcases jointLine_segment_mem z w hz hw t (interior_subset ht) with ⟨hb0, hb1, hu⟩
    exact (jointLine1_hasDerivAt _ _ _ _ t hb0 hb1 hu).hasDerivWithinAt
  · intro t ht
    rcases jointLine_segment_mem z w hz hw t (interior_subset ht) with ⟨hb0, hb1, hu⟩
    exact hessian_quadratic_nonnegative _ _ _ _ hb0 hb1 hu

theorem jointDeficit_convexOn_interior : ConvexOn ℝ signedTriangleInterior
    (fun z : ℝ × ℝ => Scalar.jointDeficit z.1 z.2) := by
  refine ⟨signedTriangleInterior_convex, ?_⟩
  intro z hz w hw r s hr hs hrs
  have hc := jointLine_segment_convex z w hz hw
  have h := hc.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hr hs hrs
  have hr' : r = 1 - s := by linarith
  have hm1 : z.1 + s * (w.1 - z.1) = r * z.1 + s * w.1 := by rw [hr']; ring
  have hm2 : z.2 + s * (w.2 - z.2) = r * z.2 + s * w.2 := by rw [hr']; ring
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, jointLine, zero_mul,
    add_zero, one_mul, add_sub_cancel_left, hm1, hm2] at h
  rw [show z.1 + (w.1 - z.1) = w.1 by ring,
    show z.2 + (w.2 - z.2) = w.2 by ring] at h
  have heq : r * (Real.log 2 * Scalar.jointDeficit z.1 z.2) +
      s * (Real.log 2 * Scalar.jointDeficit w.1 w.2) =
      Real.log 2 * (r * Scalar.jointDeficit z.1 z.2 + s * Scalar.jointDeficit w.1 w.2) := by ring
  rw [heq] at h
  change Scalar.jointDeficit (r * z.1 + s * w.1) (r * z.2 + s * w.2) ≤
    r * Scalar.jointDeficit z.1 z.2 + s * Scalar.jointDeficit w.1 w.2
  exact (mul_le_mul_iff_of_pos_left Scalar.log_two_pos).mp h

end QuantumProver.BellDiagonalSquashedEntanglement.DJointSeries

noncomputable section
open Set
open scoped BigOperators Topology
namespace QuantumProver.BellDiagonalSquashedEntanglement.DJointSeries

def signedTriangle : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ |z.2| ≤ z.1}

theorem signedTriangle_convex : Convex ℝ signedTriangle := by
  intro z hz w hw r s hr hs hrs
  change 0 ≤ r * z.1 + s * w.1 ∧ r * z.1 + s * w.1 ≤ 1 ∧
    |r * z.2 + s * w.2| ≤ r * z.1 + s * w.1
  rcases hz with ⟨hz0, hz1, hzu⟩
  rcases hw with ⟨hw0, hw1, hwu⟩
  have hzu' := abs_le.mp hzu
  have hwu' := abs_le.mp hwu
  have h0 := add_nonneg (mul_nonneg hr hz0) (mul_nonneg hs hw0)
  have h1 := add_nonneg (mul_nonneg hr (show 0 ≤ 1 - z.1 by linarith))
    (mul_nonneg hs (show 0 ≤ 1 - w.1 by linarith))
  have hlu := add_nonneg (mul_nonneg hr (show 0 ≤ z.1 + z.2 by linarith [hzu'.1]))
    (mul_nonneg hs (show 0 ≤ w.1 + w.2 by linarith [hwu'.1]))
  have hru := add_nonneg (mul_nonneg hr (show 0 ≤ z.1 - z.2 by linarith [hzu'.2]))
    (mul_nonneg hs (show 0 ≤ w.1 - w.2 by linarith [hwu'.2]))
  exact ⟨h0, by nlinarith, abs_le.mpr ⟨by nlinarith, by nlinarith⟩⟩

def interiorRegularize (e : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - e) * z.1 + e / 2, (1 - e) * z.2)

theorem interiorRegularize_mem (e : ℝ) (he0 : 0 < e) (he1 : e < 1)
    (z : ℝ × ℝ) (hz : z ∈ signedTriangle) :
    interiorRegularize e z ∈ signedTriangleInterior := by
  rcases hz with ⟨hz0, hz1, hzu⟩
  have h0 := mul_nonneg (show 0 ≤ 1 - e by linarith) hz0
  have h1 := mul_nonneg (show 0 ≤ 1 - e by linarith) (show 0 ≤ 1 - z.1 by linarith)
  have hu := mul_le_mul_of_nonneg_left hzu (show 0 ≤ 1 - e by linarith)
  change 0 < (1 - e) * z.1 + e / 2 ∧ (1 - e) * z.1 + e / 2 < 1 ∧
    |(1 - e) * z.2| < (1 - e) * z.1 + e / 2
  rw [abs_mul, abs_of_nonneg (show 0 ≤ 1 - e by linarith)]
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

theorem interiorRegularize_mix (e r s : ℝ) (z w : ℝ × ℝ) (hrs : r + s = 1) :
    interiorRegularize e (r • z + s • w) =
      r • interiorRegularize e z + s • interiorRegularize e w := by
  ext <;> simp only [interiorRegularize, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · rw [show r = 1 - s by linarith]
    ring
  · ring

theorem interiorRegularize_cost_continuous (z : ℝ × ℝ) :
    Continuous (fun e : ℝ => Scalar.jointDeficit (interiorRegularize e z).1
      (interiorRegularize e z).2) := by
  exact Scalar.jointDeficit_continuous.comp
    (show Continuous (fun e : ℝ => interiorRegularize e z) by
      unfold interiorRegularize
      fun_prop)

theorem jointDeficit_convexOn : ConvexOn ℝ signedTriangle
    (fun z : ℝ × ℝ => Scalar.jointDeficit z.1 z.2) := by
  refine ⟨signedTriangle_convex, ?_⟩
  intro z hz w hw r s hr hs hrs
  let combo : ℝ × ℝ := r • z + s • w
  let good : Set ℝ := {e | Scalar.jointDeficit (interiorRegularize e combo).1
      (interiorRegularize e combo).2 ≤
    r * Scalar.jointDeficit (interiorRegularize e z).1 (interiorRegularize e z).2 +
      s * Scalar.jointDeficit (interiorRegularize e w).1 (interiorRegularize e w).2}
  have hclosed : IsClosed good := isClosed_le (interiorRegularize_cost_continuous combo)
    ((continuous_const.mul (interiorRegularize_cost_continuous z)).add
      (continuous_const.mul (interiorRegularize_cost_continuous w)))
  have hsub : Ioo (0 : ℝ) 1 ⊆ good := by
    intro e he
    have h := jointDeficit_convexOn_interior.2
      (interiorRegularize_mem e he.1 he.2 z hz)
      (interiorRegularize_mem e he.1 he.2 w hw) hr hs hrs
    rw [← interiorRegularize_mix e r s z w hrs] at h
    exact h
  have h0 : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)]
    simp
  have h := closure_minimal hsub hclosed h0
  simpa only [good, Set.mem_setOf_eq, interiorRegularize, sub_zero, one_mul, zero_div, add_zero,
    combo, smul_eq_mul] using h

theorem jointDeficit_jensen {J : Type*} (t : Finset J) (r b u : J → ℝ)
    (hr : ∀ j ∈ t, 0 ≤ r j) (hsum : ∑ j ∈ t, r j = 1)
    (hb0 : ∀ j ∈ t, 0 ≤ b j) (hb1 : ∀ j ∈ t, b j ≤ 1)
    (hu : ∀ j ∈ t, |u j| ≤ b j) :
    Scalar.jointDeficit (∑ j ∈ t, r j * b j) (∑ j ∈ t, r j * u j) ≤
      ∑ j ∈ t, r j * Scalar.jointDeficit (b j) (u j) := by
  have h := jointDeficit_convexOn.map_sum_le hr hsum
    (p := fun j => (b j, u j)) (fun j hj => ⟨hb0 j hj, hb1 j hj, hu j hj⟩)
  simpa only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using h

end QuantumProver.BellDiagonalSquashedEntanglement.DJointSeries

namespace QuantumProver.BellDiagonalSquashedEntanglement.Scalar

theorem formationPhi_monotoneOn : MonotoneOn formationPhi (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  rcases eq_or_lt_of_le hab with h | hab
  · subst b
    rfl
  · have h := formationPhi_difference_lower a b ha.1 hab hb.2
    have hb0 : 0 < b := by linarith [ha.1]
    have hnum : 0 ≤ (b - a) * (-Real.log b) :=
      mul_nonneg (sub_nonneg.mpr hab.le) (neg_nonneg.mpr (Real.log_nonpos hb0.le hb.2))
    have hterm : 0 ≤ (b - a) * (-Real.log b) / (4 * Real.log 2) := by
      exact div_nonneg hnum (by positivity)
    linarith

end QuantumProver.BellDiagonalSquashedEntanglement.Scalar
