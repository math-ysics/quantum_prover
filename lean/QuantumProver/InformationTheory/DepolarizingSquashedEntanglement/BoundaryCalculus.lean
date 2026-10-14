import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace QuantumProver.DepolarizingSquashedEntanglement.Scalar

def boundaryDelta (r : ℝ) : ℝ := (18 * r + 33 * r ^ 2) / 160

def boundaryR (δ : ℝ) : ℝ :=
  320 * δ / (Real.sqrt (324 + 21120 * δ) + 18)

def boundaryKappa : ℝ := (2059 / 5600) * Real.log 29 - 2171 / 5800

@[simp] theorem boundaryDelta_zero : boundaryDelta 0 = 0 := by
  norm_num [boundaryDelta]

theorem boundaryDelta_quarter : boundaryDelta (1 / 4) = 21 / 512 := by
  norm_num [boundaryDelta]

theorem boundaryDelta_strictMonoOn : StrictMonoOn boundaryDelta (Set.Ici 0) := by
  intro a ha b hb hab
  have hp : 0 ≤ (b - a) * (b + a) :=
    mul_nonneg (sub_nonneg.mpr hab.le) (add_nonneg hb ha)
  dsimp [boundaryDelta]
  nlinarith

theorem boundaryDelta_linear_lower (r : ℝ) : (9 / 80) * r ≤ boundaryDelta r := by
  dsimp [boundaryDelta]
  nlinarith [sq_nonneg r]

theorem boundaryR_nonneg {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ boundaryR δ := by
  unfold boundaryR
  positivity

theorem boundaryR_pos {δ : ℝ} (hδ : 0 < δ) : 0 < boundaryR δ := by
  unfold boundaryR
  positivity

theorem boundaryR_eq_sub {δ : ℝ} (hδ : 0 ≤ δ) :
    boundaryR δ = (Real.sqrt (324 + 21120 * δ) - 18) / 66 := by
  have hd : Real.sqrt (324 + 21120 * δ) + 18 ≠ 0 := by positivity
  have hs : Real.sqrt (324 + 21120 * δ) ^ 2 = 324 + 21120 * δ :=
    Real.sq_sqrt (by positivity)
  unfold boundaryR
  apply (div_eq_div_iff hd (by norm_num : (66 : ℝ) ≠ 0)).2
  nlinarith

theorem boundaryDelta_boundaryR {δ : ℝ} (hδ : 0 ≤ δ) :
    boundaryDelta (boundaryR δ) = δ := by
  rw [boundaryR_eq_sub hδ]
  have hs : Real.sqrt (324 + 21120 * δ) ^ 2 = 324 + 21120 * δ :=
    Real.sq_sqrt (by positivity)
  unfold boundaryDelta
  field_simp
  nlinarith

theorem boundaryR_le_quarter {δ : ℝ} (hδ : 0 ≤ δ) (hmax : δ ≤ 21 / 512) :
    boundaryR δ ≤ 1 / 4 := by
  by_contra h
  have hlt : (1 / 4 : ℝ) < boundaryR δ := lt_of_not_ge h
  have hdlt := boundaryDelta_strictMonoOn
    (show (1 / 4 : ℝ) ∈ Set.Ici 0 by norm_num)
    (boundaryR_nonneg hδ) hlt
  rw [boundaryDelta_quarter, boundaryDelta_boundaryR hδ] at hdlt
  exact (not_lt_of_ge hmax) hdlt

theorem boundaryR_le_linear {δ : ℝ} (hδ : 0 ≤ δ) :
    boundaryR δ ≤ (80 / 9) * δ := by
  have hs : (18 : ℝ) ≤ Real.sqrt (324 + 21120 * δ) := by
    have h := Real.sqrt_le_sqrt (show (324 : ℝ) ≤ 324 + 21120 * δ by linarith)
    norm_num at h
    exact h
  have hp : 0 ≤ δ * (Real.sqrt (324 + 21120 * δ) - 18) :=
    mul_nonneg hδ (sub_nonneg.mpr hs)
  have hd : 0 < Real.sqrt (324 + 21120 * δ) + 18 := by positivity
  unfold boundaryR
  apply (div_le_iff₀ hd).2
  nlinarith

theorem boundaryR_unique {δ r : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hf : boundaryDelta r = δ) : r = boundaryR δ := by
  exact boundaryDelta_strictMonoOn.injOn hr (boundaryR_nonneg hδ)
    (hf.trans (boundaryDelta_boundaryR hδ).symm)

theorem two_lt_log_twentyNine : (2 : ℝ) < Real.log 29 := by
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hexp : Real.exp 2 < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 29)).2
  linarith

theorem boundaryKappa_pos : 0 < boundaryKappa := by
  unfold boundaryKappa
  nlinarith [two_lt_log_twentyNine]

theorem log_two_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

theorem boundary_coefficient_pos : 0 < 3200 * boundaryKappa / (81 * Real.log 2) := by
  exact div_pos (mul_pos (by norm_num) boundaryKappa_pos)
    (mul_pos (by norm_num) log_two_pos)

theorem boundary_coefficient_conversion :
    (boundaryKappa / (2 * Real.log 2)) * (80 / 9) ^ 2 =
      3200 * boundaryKappa / (81 * Real.log 2) := by
  ring

end QuantumProver.DepolarizingSquashedEntanglement.Scalar

namespace QuantumProver.DepolarizingSquashedEntanglement.Fixed16Calculus

open scoped Topology

def quadraticRoot (a b c r : ℝ) : ℝ := Real.sqrt (a + b * r + c * r ^ 2)

def quadraticRootDerivative (a b c r : ℝ) : ℝ :=
  (b + 2 * c * r) / (2 * quadraticRoot a b c r)

theorem quadraticRoot_hasDerivAt (a b c r : ℝ)
    (hpos : 0 < a + b * r + c * r ^ 2) :
    HasDerivAt (quadraticRoot a b c) (quadraticRootDerivative a b c r) r := by
  have hp := ((hasDerivAt_const r a).add ((hasDerivAt_id r).const_mul b)).add
    (((hasDerivAt_id r).pow 2).const_mul c)
  have hs := hp.sqrt (ne_of_gt hpos)
  convert hs using 1
  · ext t
    simp [quadraticRoot]
  · dsimp [quadraticRoot, quadraticRootDerivative]
    norm_num
    ring

def oneRoot (r : ℝ) : ℝ := quadraticRoot 19600 (-6160) 1444 r
def bothRoot (r : ℝ) : ℝ := quadraticRoot 19600 (-12320) 18320 r
def oneRootDerivative (r : ℝ) : ℝ := quadraticRootDerivative 19600 (-6160) 1444 r
def bothRootDerivative (r : ℝ) : ℝ := quadraticRootDerivative 19600 (-12320) 18320 r

theorem oneDiscriminant_pos (r : ℝ) : 0 < 19600 - 6160 * r + 1444 * r ^ 2 := by
  nlinarith [sq_nonneg (2888 * r - 6160)]

theorem bothDiscriminant_pos (r : ℝ) : 0 < 19600 - 12320 * r + 18320 * r ^ 2 := by
  nlinarith [sq_nonneg (36640 * r - 12320)]

theorem oneRoot_zero : oneRoot 0 = 140 := by
  norm_num [oneRoot, quadraticRoot]

theorem bothRoot_zero : bothRoot 0 = 140 := by
  norm_num [bothRoot, quadraticRoot]

theorem oneRoot_hasDerivAt (r : ℝ) : HasDerivAt oneRoot (oneRootDerivative r) r := by
  apply quadraticRoot_hasDerivAt
  simpa only [neg_mul, sub_eq_add_neg] using oneDiscriminant_pos r

theorem bothRoot_hasDerivAt (r : ℝ) : HasDerivAt bothRoot (bothRootDerivative r) r := by
  apply quadraticRoot_hasDerivAt
  simpa only [neg_mul, sub_eq_add_neg] using bothDiscriminant_pos r

theorem oneRootDerivative_zero : oneRootDerivative 0 = -22 := by
  change (-6160 + 2 * 1444 * 0) / (2 * oneRoot 0) = -22
  rw [oneRoot_zero]
  norm_num

theorem bothRootDerivative_zero : bothRootDerivative 0 = -44 := by
  change (-12320 + 2 * 18320 * 0) / (2 * bothRoot 0) = -44
  rw [bothRoot_zero]
  norm_num

theorem oneRoot_secondJet : HasDerivAt oneRootDerivative (48 / 7) 0 := by
  have hn := (hasDerivAt_const (0 : ℝ) (-6160 : ℝ)).add
    ((hasDerivAt_id (0 : ℝ)).const_mul (2 * 1444))
  have hd := (oneRoot_hasDerivAt 0).const_mul 2
  have hne : 2 * oneRoot 0 ≠ 0 := by rw [oneRoot_zero]; norm_num
  have h := hn.div hd hne
  convert h using 1
  · ext t
    simp [oneRootDerivative, quadraticRootDerivative, oneRoot]
  · norm_num [oneRootDerivative_zero, oneRoot_zero]

theorem bothRoot_secondJet : HasDerivAt bothRootDerivative (4096 / 35) 0 := by
  have hn := (hasDerivAt_const (0 : ℝ) (-12320 : ℝ)).add
    ((hasDerivAt_id (0 : ℝ)).const_mul (2 * 18320))
  have hd := (bothRoot_hasDerivAt 0).const_mul 2
  have hne : 2 * bothRoot 0 ≠ 0 := by rw [bothRoot_zero]; norm_num
  have h := hn.div hd hne
  convert h using 1
  · ext t
    simp [bothRootDerivative, quadraticRootDerivative, bothRoot]
  · norm_num [bothRootDerivative_zero, bothRoot_zero]

def onePlus (r : ℝ) : ℝ := (150 - 28 * r + oneRoot r) / 320
def oneMinus (r : ℝ) : ℝ := (150 - 28 * r - oneRoot r) / 320
def bothPlus (r : ℝ) : ℝ := (150 - 56 * r + 66 * r ^ 2 + bothRoot r) / 320
def bothMinus (r : ℝ) : ℝ := (150 - 56 * r + 66 * r ^ 2 - bothRoot r) / 320
def oneOddLeft (r : ℝ) : ℝ := (5 - 5 * r) / 160
def oneOddRight (r : ℝ) : ℝ := (5 + 33 * r) / 160
def bothOdd (r : ℝ) : ℝ := (5 + 28 * r - 33 * r ^ 2) / 160

theorem evenBranches_zero :
    onePlus 0 = 29 / 32 ∧ oneMinus 0 = 1 / 32 ∧
      bothPlus 0 = 29 / 32 ∧ bothMinus 0 = 1 / 32 := by
  norm_num [onePlus, oneMinus, bothPlus, bothMinus, oneRoot_zero, bothRoot_zero]

theorem onePlus_firstJet : HasDerivAt onePlus (-5 / 32) 0 := by
  have h := (((hasDerivAt_const (0 : ℝ) (150 : ℝ)).sub
    ((hasDerivAt_id (0 : ℝ)).const_mul 28)).add (oneRoot_hasDerivAt 0)).div_const 320
  convert h using 1 <;> (try rfl) <;> norm_num [onePlus, oneRootDerivative_zero]

theorem oneMinus_firstJet : HasDerivAt oneMinus (-3 / 160) 0 := by
  have h := (((hasDerivAt_const (0 : ℝ) (150 : ℝ)).sub
    ((hasDerivAt_id (0 : ℝ)).const_mul 28)).sub (oneRoot_hasDerivAt 0)).div_const 320
  convert h using 1 <;> (try rfl) <;> norm_num [oneMinus, oneRootDerivative_zero]

theorem bothPlus_firstJet : HasDerivAt bothPlus (-5 / 16) 0 := by
  have hp := ((hasDerivAt_const (0 : ℝ) (150 : ℝ)).sub
    ((hasDerivAt_id (0 : ℝ)).const_mul 56)).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 66)
  have h := (hp.add (bothRoot_hasDerivAt 0)).div_const 320
  convert h using 1 <;> (try rfl) <;> norm_num [bothPlus, bothRootDerivative_zero]

theorem bothMinus_firstJet : HasDerivAt bothMinus (-3 / 80) 0 := by
  have hp := ((hasDerivAt_const (0 : ℝ) (150 : ℝ)).sub
    ((hasDerivAt_id (0 : ℝ)).const_mul 56)).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 66)
  have h := (hp.sub (bothRoot_hasDerivAt 0)).div_const 320
  convert h using 1 <;> (try rfl) <;> norm_num [bothMinus, bothRootDerivative_zero]

def onePlusDerivative (r : ℝ) : ℝ := (-28 + oneRootDerivative r) / 320
def oneMinusDerivative (r : ℝ) : ℝ := (-28 - oneRootDerivative r) / 320
def bothPlusDerivative (r : ℝ) : ℝ := (-56 + 132 * r + bothRootDerivative r) / 320
def bothMinusDerivative (r : ℝ) : ℝ := (-56 + 132 * r - bothRootDerivative r) / 320

theorem onePlus_hasDerivAt (r : ℝ) : HasDerivAt onePlus (onePlusDerivative r) r := by
  have h := (((hasDerivAt_const r (150 : ℝ)).sub
    ((hasDerivAt_id r).const_mul 28)).add (oneRoot_hasDerivAt r)).div_const 320
  convert h using 1 <;> (try rfl) <;> norm_num [onePlus, onePlusDerivative]

theorem oneMinus_hasDerivAt (r : ℝ) : HasDerivAt oneMinus (oneMinusDerivative r) r := by
  have h := (((hasDerivAt_const r (150 : ℝ)).sub
    ((hasDerivAt_id r).const_mul 28)).sub (oneRoot_hasDerivAt r)).div_const 320
  convert h using 1 <;> (try rfl) <;> norm_num [oneMinus, oneMinusDerivative]

theorem bothPlus_hasDerivAt (r : ℝ) : HasDerivAt bothPlus (bothPlusDerivative r) r := by
  have hp := ((hasDerivAt_const r (150 : ℝ)).sub
    ((hasDerivAt_id r).const_mul 56)).add (((hasDerivAt_id r).pow 2).const_mul 66)
  have h := (hp.add (bothRoot_hasDerivAt r)).div_const 320
  convert h using 1 <;> (try rfl) <;> norm_num [bothPlus, bothPlusDerivative] <;> ring

theorem bothMinus_hasDerivAt (r : ℝ) : HasDerivAt bothMinus (bothMinusDerivative r) r := by
  have hp := ((hasDerivAt_const r (150 : ℝ)).sub
    ((hasDerivAt_id r).const_mul 56)).add (((hasDerivAt_id r).pow 2).const_mul 66)
  have h := (hp.sub (bothRoot_hasDerivAt r)).div_const 320
  convert h using 1 <;> (try rfl) <;> norm_num [bothMinus, bothMinusDerivative] <;> ring

theorem deriv_onePlus : deriv onePlus = onePlusDerivative := by
  funext r
  exact (onePlus_hasDerivAt r).deriv

theorem deriv_oneMinus : deriv oneMinus = oneMinusDerivative := by
  funext r
  exact (oneMinus_hasDerivAt r).deriv

theorem deriv_bothPlus : deriv bothPlus = bothPlusDerivative := by
  funext r
  exact (bothPlus_hasDerivAt r).deriv

theorem deriv_bothMinus : deriv bothMinus = bothMinusDerivative := by
  funext r
  exact (bothMinus_hasDerivAt r).deriv

theorem onePlus_secondJet : HasDerivAt (deriv onePlus) (3 / 140) 0 := by
  rw [deriv_onePlus]
  have h := ((hasDerivAt_const (0 : ℝ) (-28 : ℝ)).add oneRoot_secondJet).div_const 320
  convert h using 1 <;> (try rfl) <;> norm_num [onePlusDerivative]

theorem oneMinus_secondJet : HasDerivAt (deriv oneMinus) (-3 / 140) 0 := by
  rw [deriv_oneMinus]
  have h := ((hasDerivAt_const (0 : ℝ) (-28 : ℝ)).sub oneRoot_secondJet).div_const 320
  convert h using 1 <;> (try rfl) <;> norm_num [oneMinusDerivative]

theorem bothPlus_secondJet : HasDerivAt (deriv bothPlus) (2179 / 2800) 0 := by
  rw [deriv_bothPlus]
  have h := (((hasDerivAt_const (0 : ℝ) (-56 : ℝ)).add
    ((hasDerivAt_id (0 : ℝ)).const_mul 132)).add bothRoot_secondJet).div_const 320
  convert h using 1 <;> (try rfl) <;> norm_num [bothPlusDerivative]

theorem bothMinus_secondJet : HasDerivAt (deriv bothMinus) (131 / 2800) 0 := by
  rw [deriv_bothMinus]
  have h := (((hasDerivAt_const (0 : ℝ) (-56 : ℝ)).add
    ((hasDerivAt_id (0 : ℝ)).const_mul 132)).sub bothRoot_secondJet).div_const 320
  convert h using 1 <;> (try rfl) <;> norm_num [bothMinusDerivative]

theorem negMulLog_derivative_composition {f fD : ℝ → ℝ} {a b x : ℝ}
    (hf : HasDerivAt f a x) (hfD : HasDerivAt fD b x)
    (hval : fD x = a) (hne : f x ≠ 0) :
    HasDerivAt (fun r => (-Real.log (f r) - 1) * fD r)
      (-a ^ 2 / f x + (-Real.log (f x) - 1) * b) x := by
  have hl := (Real.hasDerivAt_log hne).comp x hf
  have h := ((hl.neg.sub (hasDerivAt_const x (1 : ℝ))).mul hfD)
  convert h using 1
  · rfl
  · simp only [hval, Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply, sub_zero]
    ring

def entropyJetSecond (eigen d dd : ℝ) : ℝ :=
  -d ^ 2 / eigen + (-Real.log eigen - 1) * dd

def oneEntropySecondJet : ℝ :=
  entropyJetSecond (29 / 32) (-5 / 32) (3 / 140) +
    entropyJetSecond (1 / 32) (-3 / 160) (-3 / 140) +
    entropyJetSecond (1 / 32) (-5 / 160) 0 +
    entropyJetSecond (1 / 32) (33 / 160) 0

def bothEntropySecondJet : ℝ :=
  entropyJetSecond (29 / 32) (-5 / 16) (2179 / 2800) +
    entropyJetSecond (1 / 32) (-3 / 80) (131 / 2800) +
    2 * entropyJetSecond (1 / 32) (7 / 40) (-33 / 80)

theorem entropy_jet_coefficient :
    (2 * oneEntropySecondJet - bothEntropySecondJet) / 2 = Scalar.boundaryKappa := by
  have ha : Real.log (29 / 32 : ℝ) = Real.log 29 - Real.log 32 :=
    Real.log_div (by norm_num) (by norm_num)
  have hb : Real.log (1 / 32 : ℝ) = -Real.log 32 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    simp
  dsimp [oneEntropySecondJet, bothEntropySecondJet, entropyJetSecond,
    Scalar.boundaryKappa]
  rw [ha, hb]
  ring

def oneEntropy (r : ℝ) : ℝ := Real.negMulLog (onePlus r) +
  Real.negMulLog (oneMinus r) + Real.negMulLog (oneOddLeft r) +
    Real.negMulLog (oneOddRight r)

def bothEntropy (r : ℝ) : ℝ := Real.negMulLog (bothPlus r) +
  Real.negMulLog (bothMinus r) + 2 * Real.negMulLog (bothOdd r)

def entropyCombination (r : ℝ) : ℝ := 2 * oneEntropy r - bothEntropy r - oneEntropy 0

theorem entropyCombination_zero : entropyCombination 0 = 0 := by
  rcases evenBranches_zero with ⟨ha, hb, hc, hd⟩
  simp only [entropyCombination, oneEntropy, bothEntropy, ha, hb, hc, hd]
  norm_num [oneOddLeft, oneOddRight, bothOdd]
  ring

theorem oneMinus_support_lower {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1 / 4) :
    9 / 512 ≤ oneMinus r := by
  have hsq : r ^ 2 ≤ r / 4 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr hr1)]
  have hs : Real.sqrt (19600 - 6160 * r + 1444 * r ^ 2) ≤
      150 - 28 * r - 45 / 8 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith
  dsimp [oneMinus, oneRoot, quadraticRoot]
  simp only [neg_mul, ← sub_eq_add_neg]
  nlinarith

theorem bothMinus_support_lower {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1 / 4) :
    9 / 512 ≤ bothMinus r := by
  have h3 : r ^ 3 ≤ r ^ 2 / 4 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r) (sub_nonpos.mpr hr1)]
  have h4 : 0 ≤ r ^ 4 := by positivity
  have hs : Real.sqrt (19600 - 12320 * r + 18320 * r ^ 2) ≤
      150 - 56 * r + 66 * r ^ 2 - 45 / 8 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · nlinarith [sq_nonneg r]
    · nlinarith [sq_nonneg r]
  dsimp [bothMinus, bothRoot, quadraticRoot]
  simp only [neg_mul, ← sub_eq_add_neg]
  nlinarith

theorem onePlus_support_lower {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1 / 4) :
    9 / 512 ≤ onePlus r := by
  have hm := oneMinus_support_lower hr hr1
  have hs := Real.sqrt_nonneg (19600 - 6160 * r + 1444 * r ^ 2)
  dsimp [onePlus, oneMinus, oneRoot, quadraticRoot] at *
  simp only [neg_mul, ← sub_eq_add_neg] at *
  linarith

theorem bothPlus_support_lower {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1 / 4) :
    9 / 512 ≤ bothPlus r := by
  have hm := bothMinus_support_lower hr hr1
  have hs := Real.sqrt_nonneg (19600 - 12320 * r + 18320 * r ^ 2)
  dsimp [bothPlus, bothMinus, bothRoot, quadraticRoot] at *
  simp only [neg_mul, ← sub_eq_add_neg] at *
  linarith

theorem oddBranches_support_lower {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1 / 4) :
    9 / 512 ≤ oneOddLeft r ∧ 9 / 512 ≤ oneOddRight r ∧ 9 / 512 ≤ bothOdd r := by
  have hsq : r ^ 2 ≤ r / 4 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr hr1)]
  dsimp [oneOddLeft, oneOddRight, bothOdd]
  constructor
  · linarith
  · constructor
    · linarith
    · nlinarith

@[fun_prop] theorem oneRoot_contDiff : ContDiff ℝ 3 oneRoot := by
  unfold oneRoot quadraticRoot
  have hp : ContDiff ℝ 3 (fun r : ℝ => 19600 - 6160 * r + 1444 * r ^ 2) := by
    fun_prop
  simpa only [neg_mul, sub_eq_add_neg] using
    hp.sqrt (fun r => ne_of_gt (oneDiscriminant_pos r))

@[fun_prop] theorem bothRoot_contDiff : ContDiff ℝ 3 bothRoot := by
  unfold bothRoot quadraticRoot
  have hp : ContDiff ℝ 3 (fun r : ℝ => 19600 - 12320 * r + 18320 * r ^ 2) := by
    fun_prop
  simpa only [neg_mul, sub_eq_add_neg] using
    hp.sqrt (fun r => ne_of_gt (bothDiscriminant_pos r))

theorem onePlus_contDiff : ContDiff ℝ 3 onePlus := by
  unfold onePlus
  fun_prop

theorem oneMinus_contDiff : ContDiff ℝ 3 oneMinus := by
  unfold oneMinus
  fun_prop

theorem bothPlus_contDiff : ContDiff ℝ 3 bothPlus := by
  unfold bothPlus
  have hp : ContDiff ℝ 3 (fun r : ℝ => 150 - 56 * r + 66 * r ^ 2) := by fun_prop
  exact (hp.add bothRoot_contDiff).div_const (320 : ℝ)

theorem bothMinus_contDiff : ContDiff ℝ 3 bothMinus := by
  unfold bothMinus
  have hp : ContDiff ℝ 3 (fun r : ℝ => 150 - 56 * r + 66 * r ^ 2) := by fun_prop
  exact (hp.sub bothRoot_contDiff).div_const (320 : ℝ)

theorem oddBranches_contDiff : ContDiff ℝ 3 oneOddLeft ∧
    ContDiff ℝ 3 oneOddRight ∧ ContDiff ℝ 3 bothOdd := by
  constructor
  · unfold oneOddLeft
    fun_prop
  · constructor
    · unfold oneOddRight
      fun_prop
    · unfold bothOdd
      fun_prop

theorem negMulLog_contDiffAt_composition {f : ℝ → ℝ} {r : ℝ}
    (hf : ContDiffAt ℝ 3 f r) (hne : f r ≠ 0) :
    ContDiffAt ℝ 3 (fun x => Real.negMulLog (f x)) r := by
  simpa only [Real.negMulLog] using hf.neg.mul (hf.log hne)

theorem oneEntropy_contDiffAt {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1 / 4) :
    ContDiffAt ℝ 3 oneEntropy r := by
  have h0 : (0 : ℝ) < 9 / 512 := by norm_num
  have hp := negMulLog_contDiffAt_composition onePlus_contDiff.contDiffAt
    (ne_of_gt (h0.trans_le (onePlus_support_lower hr hr1)))
  have hm := negMulLog_contDiffAt_composition oneMinus_contDiff.contDiffAt
    (ne_of_gt (h0.trans_le (oneMinus_support_lower hr hr1)))
  rcases oddBranches_support_lower hr hr1 with ⟨hl, hq, he⟩
  rcases oddBranches_contDiff with ⟨hld, hqd, hed⟩
  have hl' := negMulLog_contDiffAt_composition hld.contDiffAt (ne_of_gt (h0.trans_le hl))
  have hq' := negMulLog_contDiffAt_composition hqd.contDiffAt (ne_of_gt (h0.trans_le hq))
  unfold oneEntropy
  exact ((hp.add hm).add hl').add hq'

theorem bothEntropy_contDiffAt {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1 / 4) :
    ContDiffAt ℝ 3 bothEntropy r := by
  have h0 : (0 : ℝ) < 9 / 512 := by norm_num
  have hp := negMulLog_contDiffAt_composition bothPlus_contDiff.contDiffAt
    (ne_of_gt (h0.trans_le (bothPlus_support_lower hr hr1)))
  have hm := negMulLog_contDiffAt_composition bothMinus_contDiff.contDiffAt
    (ne_of_gt (h0.trans_le (bothMinus_support_lower hr hr1)))
  have ho := negMulLog_contDiffAt_composition oddBranches_contDiff.2.2.contDiffAt
    (ne_of_gt (h0.trans_le (oddBranches_support_lower hr hr1).2.2))
  have hc : ContDiffAt ℝ 3 (fun _ : ℝ => (2 : ℝ)) r := contDiffAt_const
  unfold bothEntropy
  exact (hp.add hm).add (hc.mul ho)

theorem entropyCombination_contDiffAt {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1 / 4) :
    ContDiffAt ℝ 3 entropyCombination r := by
  have hc : ContDiffAt ℝ 3 (fun _ : ℝ => (2 : ℝ)) r := contDiffAt_const
  unfold entropyCombination
  exact ((hc.mul (oneEntropy_contDiffAt hr hr1)).sub
    (bothEntropy_contDiffAt hr hr1)).sub contDiffAt_const

theorem oneOddLeft_firstJet : HasDerivAt oneOddLeft (-1 / 32) 0 := by
  have h := ((hasDerivAt_const (0 : ℝ) (5 : ℝ)).sub
    ((hasDerivAt_id (0 : ℝ)).const_mul 5)).div_const 160
  convert h using 1 <;> (try rfl) <;> norm_num [oneOddLeft]

theorem oneOddRight_firstJet : HasDerivAt oneOddRight (33 / 160) 0 := by
  have h := ((hasDerivAt_const (0 : ℝ) (5 : ℝ)).add
    ((hasDerivAt_id (0 : ℝ)).const_mul 33)).div_const 160
  convert h using 1 <;> (try rfl) <;> norm_num [oneOddRight]

theorem bothOdd_firstJet : HasDerivAt bothOdd (7 / 40) 0 := by
  have h := (((hasDerivAt_const (0 : ℝ) (5 : ℝ)).add
    ((hasDerivAt_id (0 : ℝ)).const_mul 28)).sub
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 33)).div_const 160
  convert h using 1 <;> (try rfl) <;> norm_num [bothOdd]

theorem oneEntropy_firstJet : HasDerivAt oneEntropy ((5 / 32) * Real.log 29) 0 := by
  rcases evenBranches_zero with ⟨a0, b0, c0, d0⟩
  have hp := (Real.hasDerivAt_negMulLog
    (show onePlus 0 ≠ 0 by rw [a0]; norm_num)).comp 0 onePlus_firstJet
  have hm := (Real.hasDerivAt_negMulLog
    (show oneMinus 0 ≠ 0 by rw [b0]; norm_num)).comp 0 oneMinus_firstJet
  have hl := (Real.hasDerivAt_negMulLog
    (show oneOddLeft 0 ≠ 0 by norm_num [oneOddLeft])).comp 0 oneOddLeft_firstJet
  have hq := (Real.hasDerivAt_negMulLog
    (show oneOddRight 0 ≠ 0 by norm_num [oneOddRight])).comp 0 oneOddRight_firstJet
  have h := ((hp.add hm).add hl).add hq
  have ha : Real.log (29 / 32 : ℝ) = Real.log 29 - Real.log 32 :=
    Real.log_div (by norm_num) (by norm_num)
  have hb : Real.log (1 / 32 : ℝ) = -Real.log 32 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    simp
  convert h using 1 <;> (try rfl) <;>
    norm_num [oneEntropy, a0, b0, oneOddLeft, oneOddRight, ha, hb] <;> ring

theorem bothEntropy_firstJet : HasDerivAt bothEntropy ((5 / 16) * Real.log 29) 0 := by
  rcases evenBranches_zero with ⟨a0, b0, c0, d0⟩
  have hp := (Real.hasDerivAt_negMulLog
    (show bothPlus 0 ≠ 0 by rw [c0]; norm_num)).comp 0 bothPlus_firstJet
  have hm := (Real.hasDerivAt_negMulLog
    (show bothMinus 0 ≠ 0 by rw [d0]; norm_num)).comp 0 bothMinus_firstJet
  have ho := (Real.hasDerivAt_negMulLog
    (show bothOdd 0 ≠ 0 by norm_num [bothOdd])).comp 0 bothOdd_firstJet
  have h := (hp.add hm).add (ho.const_mul (2 : ℝ))
  have ha : Real.log (29 / 32 : ℝ) = Real.log 29 - Real.log 32 :=
    Real.log_div (by norm_num) (by norm_num)
  have hb : Real.log (1 / 32 : ℝ) = -Real.log 32 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    simp
  convert h using 1 <;> (try rfl) <;> norm_num [bothEntropy, c0, d0, bothOdd, ha, hb] <;> ring

theorem entropyCombination_firstJet : HasDerivAt entropyCombination 0 0 := by
  have h := ((oneEntropy_firstJet.const_mul (2 : ℝ)).sub bothEntropy_firstJet).sub
    (hasDerivAt_const (0 : ℝ) (oneEntropy 0))
  convert h using 1 <;> (try rfl) <;> norm_num [entropyCombination] <;> ring

theorem oneOddLeft_secondJet : HasDerivAt (deriv oneOddLeft) 0 0 := by
  have hd : deriv oneOddLeft = fun _ => (-1 / 32 : ℝ) := by
    funext r
    have h := ((hasDerivAt_const r (5 : ℝ)).sub
      ((hasDerivAt_id r).const_mul 5)).div_const 160
    have h' : HasDerivAt oneOddLeft (-1 / 32) r := by
      convert h using 1 <;> (try rfl) <;> norm_num [oneOddLeft]
    exact h'.deriv
  rw [hd]
  exact hasDerivAt_const 0 (-1 / 32 : ℝ)

theorem oneOddRight_secondJet : HasDerivAt (deriv oneOddRight) 0 0 := by
  have hd : deriv oneOddRight = fun _ => (33 / 160 : ℝ) := by
    funext r
    have h := ((hasDerivAt_const r (5 : ℝ)).add
      ((hasDerivAt_id r).const_mul 33)).div_const 160
    have h' : HasDerivAt oneOddRight (33 / 160) r := by
      convert h using 1 <;> (try rfl) <;> norm_num [oneOddRight]
    exact h'.deriv
  rw [hd]
  exact hasDerivAt_const 0 (33 / 160 : ℝ)

theorem bothOdd_secondJet : HasDerivAt (deriv bothOdd) (-33 / 80) 0 := by
  have hd : deriv bothOdd = fun r => (28 - 66 * r) / 160 := by
    funext r
    have h := (((hasDerivAt_const r (5 : ℝ)).add
      ((hasDerivAt_id r).const_mul 28)).sub
        (((hasDerivAt_id r).pow 2).const_mul 33)).div_const 160
    have h' : HasDerivAt bothOdd ((28 - 66 * r) / 160) r := by
      convert h using 1 <;> (try rfl) <;> norm_num [bothOdd] <;> ring
    exact h'.deriv
  rw [hd]
  have h := ((hasDerivAt_const (0 : ℝ) (28 : ℝ)).sub
    ((hasDerivAt_id (0 : ℝ)).const_mul 66)).div_const 160
  convert h using 1 <;> (try rfl) <;> norm_num

theorem negMulLog_hasDerivAt_of_smooth {f : ℝ → ℝ} {x : ℝ}
    (hs : ContDiff ℝ 3 f) (hne : f x ≠ 0) :
    HasDerivAt (fun r => Real.negMulLog (f r))
      ((-Real.log (f x) - 1) * deriv f x) x := by
  exact (Real.hasDerivAt_negMulLog hne).comp x
    (hs.differentiable (by norm_num)).differentiableAt.hasDerivAt

theorem negMulLog_secondJet {f : ℝ → ℝ} {a b x : ℝ}
    (hs : ContDiff ℝ 3 f) (hf : HasDerivAt f a x)
    (hf2 : HasDerivAt (deriv f) b x) (hne : f x ≠ 0) :
    HasDerivAt (deriv (fun r => Real.negMulLog (f r)))
      (entropyJetSecond (f x) a b) x := by
  have h := negMulLog_derivative_composition hf hf2 hf.deriv hne
  have heq : deriv (fun r => Real.negMulLog (f r)) =ᶠ[𝓝 x]
      (fun r => (-Real.log (f r) - 1) * deriv f r) := by
    filter_upwards [hf.continuousAt.eventually_ne hne] with r hr
    exact (negMulLog_hasDerivAt_of_smooth hs hr).deriv
  exact h.congr_of_eventuallyEq heq

theorem oneEntropy_secondJet : HasDerivAt (deriv oneEntropy) oneEntropySecondJet 0 := by
  rcases evenBranches_zero with ⟨a0, b0, c0, d0⟩
  have hpa : onePlus 0 ≠ 0 := by rw [a0]; norm_num
  have hma : oneMinus 0 ≠ 0 := by rw [b0]; norm_num
  have hla : oneOddLeft 0 ≠ 0 := by norm_num [oneOddLeft]
  have hqa : oneOddRight 0 ≠ 0 := by norm_num [oneOddRight]
  have hp := negMulLog_secondJet onePlus_contDiff onePlus_firstJet onePlus_secondJet hpa
  have hm := negMulLog_secondJet oneMinus_contDiff oneMinus_firstJet oneMinus_secondJet hma
  have hl := negMulLog_secondJet oddBranches_contDiff.1
    oneOddLeft_firstJet oneOddLeft_secondJet hla
  have hq := negMulLog_secondJet oddBranches_contDiff.2.1
    oneOddRight_firstJet oneOddRight_secondJet hqa
  have heq : deriv oneEntropy =ᶠ[𝓝 (0 : ℝ)] (fun r =>
      deriv (fun t => Real.negMulLog (onePlus t)) r +
      deriv (fun t => Real.negMulLog (oneMinus t)) r +
      deriv (fun t => Real.negMulLog (oneOddLeft t)) r +
      deriv (fun t => Real.negMulLog (oneOddRight t)) r) := by
    filter_upwards [onePlus_contDiff.continuous.continuousAt.eventually_ne hpa,
      oneMinus_contDiff.continuous.continuousAt.eventually_ne hma,
      oddBranches_contDiff.1.continuous.continuousAt.eventually_ne hla,
      oddBranches_contDiff.2.1.continuous.continuousAt.eventually_ne hqa] with r hpr hmr hlr hqr
    have hp' := negMulLog_hasDerivAt_of_smooth onePlus_contDiff hpr
    have hm' := negMulLog_hasDerivAt_of_smooth oneMinus_contDiff hmr
    have hl' := negMulLog_hasDerivAt_of_smooth oddBranches_contDiff.1 hlr
    have hq' := negMulLog_hasDerivAt_of_smooth oddBranches_contDiff.2.1 hqr
    rw [hp'.deriv, hm'.deriv, hl'.deriv, hq'.deriv]
    exact (((hp'.add hm').add hl').add hq').deriv
  have h := (((hp.add hm).add hl).add hq).congr_of_eventuallyEq heq
  convert h using 1 <;> (try rfl) <;>
    norm_num [oneEntropySecondJet, entropyJetSecond, a0, b0, oneOddLeft, oneOddRight]

theorem bothEntropy_secondJet : HasDerivAt (deriv bothEntropy) bothEntropySecondJet 0 := by
  rcases evenBranches_zero with ⟨a0, b0, c0, d0⟩
  have hpa : bothPlus 0 ≠ 0 := by rw [c0]; norm_num
  have hma : bothMinus 0 ≠ 0 := by rw [d0]; norm_num
  have hoa : bothOdd 0 ≠ 0 := by norm_num [bothOdd]
  have hp := negMulLog_secondJet bothPlus_contDiff bothPlus_firstJet bothPlus_secondJet hpa
  have hm := negMulLog_secondJet bothMinus_contDiff bothMinus_firstJet bothMinus_secondJet hma
  have ho := negMulLog_secondJet oddBranches_contDiff.2.2 bothOdd_firstJet bothOdd_secondJet hoa
  have heq : deriv bothEntropy =ᶠ[𝓝 (0 : ℝ)] (fun r =>
      deriv (fun t => Real.negMulLog (bothPlus t)) r +
      deriv (fun t => Real.negMulLog (bothMinus t)) r +
      2 * deriv (fun t => Real.negMulLog (bothOdd t)) r) := by
    filter_upwards [bothPlus_contDiff.continuous.continuousAt.eventually_ne hpa,
      bothMinus_contDiff.continuous.continuousAt.eventually_ne hma,
      oddBranches_contDiff.2.2.continuous.continuousAt.eventually_ne hoa] with r hpr hmr hor
    have hp' := negMulLog_hasDerivAt_of_smooth bothPlus_contDiff hpr
    have hm' := negMulLog_hasDerivAt_of_smooth bothMinus_contDiff hmr
    have ho' := negMulLog_hasDerivAt_of_smooth oddBranches_contDiff.2.2 hor
    rw [hp'.deriv, hm'.deriv, ho'.deriv]
    exact ((hp'.add hm').add (ho'.const_mul (2 : ℝ))).deriv
  have h := ((hp.add hm).add (ho.const_mul (2 : ℝ))).congr_of_eventuallyEq heq
  convert h using 1 <;> (try rfl) <;> norm_num [bothEntropySecondJet, entropyJetSecond, c0, d0, bothOdd]

theorem entropyCombination_secondJet :
    HasDerivAt (deriv entropyCombination) (2 * Scalar.boundaryKappa) 0 := by
  have h1 : ContDiffAt ℝ 3 oneEntropy 0 := oneEntropy_contDiffAt (by norm_num) (by norm_num)
  have h2 : ContDiffAt ℝ 3 bothEntropy 0 := bothEntropy_contDiffAt (by norm_num) (by norm_num)
  have heq : deriv entropyCombination =ᶠ[𝓝 (0 : ℝ)]
      (fun r => 2 * deriv oneEntropy r - deriv bothEntropy r) := by
    filter_upwards [h1.eventually (by norm_num), h2.eventually (by norm_num)] with r hr1 hr2
    have hd1 := (hr1.differentiableAt (by norm_num)).hasDerivAt
    have hd2 := (hr2.differentiableAt (by norm_num)).hasDerivAt
    have h := ((hd1.const_mul (2 : ℝ)).sub hd2).sub (hasDerivAt_const r (oneEntropy 0))
    have hf : ((fun y => 2 * oneEntropy y) - bothEntropy - fun _ => oneEntropy 0) =
        (fun t => 2 * oneEntropy t - bothEntropy t - oneEntropy 0) := by
      ext t
      rfl
    rw [hf] at h
    change deriv (fun t => 2 * oneEntropy t - bothEntropy t - oneEntropy 0) r = _
    simpa only [sub_zero] using h.deriv
  have h := ((oneEntropy_secondJet.const_mul (2 : ℝ)).sub
    bothEntropy_secondJet).congr_of_eventuallyEq heq
  apply h.congr_deriv
  linarith [entropy_jet_coefficient]

theorem entropyCombination_uniform_remainder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → r ≤ 1 / 4 →
      |entropyCombination r - Scalar.boundaryKappa * r ^ 2| ≤ C * r ^ 3 := by
  have hat : ContDiffAt ℝ 3 entropyCombination 0 :=
    entropyCombination_contDiffAt (by norm_num) (by norm_num)
  have hon : ContDiffOn ℝ 3 entropyCombination (Set.Icc (0 : ℝ) (1 / 4)) := by
    intro r hr
    exact (entropyCombination_contDiffAt hr.1 hr.2).contDiffWithinAt
  have hu : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (1 / 4)) := uniqueDiffOn_Icc (by norm_num)
  have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 4) := by norm_num
  have hi1 := iteratedDerivWithin_eq_iteratedDeriv (n := 1) hu
    (hat.of_le (by norm_num)) hmem
  have hi2 := iteratedDerivWithin_eq_iteratedDeriv (n := 2) hu
    (hat.of_le (by norm_num)) hmem
  have ht (r : ℝ) : taylorWithinEval entropyCombination 2
      (Set.Icc (0 : ℝ) (1 / 4)) 0 r = Scalar.boundaryKappa * r ^ 2 := by
    rw [taylorWithinEval_succ entropyCombination 1,
      taylorWithinEval_succ entropyCombination 0, taylor_within_zero_eval,
      entropyCombination_zero, hi1, hi2]
    norm_num [iteratedDeriv_succ, iteratedDeriv_one,
      entropyCombination_firstJet.deriv, entropyCombination_secondJet.deriv]
    ring
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
    (n := 2) (by norm_num : (0 : ℝ) ≤ 1 / 4) hon
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro r hr hr1
  have h := hC r ⟨hr, hr1⟩
  rw [ht r, Real.norm_eq_abs, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity))

theorem boundaryR_quadratic_error {δ : ℝ} (hδ : 0 ≤ δ) :
    Scalar.boundaryR δ - (80 / 9) * δ = -(11 / 6) * Scalar.boundaryR δ ^ 2 := by
  have h := Scalar.boundaryDelta_boundaryR hδ
  dsimp [Scalar.boundaryDelta] at h
  nlinarith

theorem boundaryR_square_error {δ : ℝ} (hδ : 0 ≤ δ) :
    |Scalar.boundaryR δ ^ 2 - (80 / 9 : ℝ) ^ 2 * δ ^ 2| ≤
      (11 / 3) * (80 / 9 : ℝ) ^ 3 * δ ^ 3 := by
  have hr := Scalar.boundaryR_nonneg hδ
  have hl := Scalar.boundaryR_le_linear hδ
  have hs : Scalar.boundaryR δ ^ 2 ≤ ((80 / 9 : ℝ) * δ) ^ 2 :=
    pow_le_pow_left₀ hr hl 2
  have he : |Scalar.boundaryR δ - (80 / 9) * δ| = (11 / 6) * Scalar.boundaryR δ ^ 2 := by
    rw [boundaryR_quadratic_error hδ]
    rw [show -(11 / 6) * Scalar.boundaryR δ ^ 2 =
      -((11 / 6) * Scalar.boundaryR δ ^ 2) by ring, abs_neg,
      abs_of_nonneg (by positivity)]
  have hf : Scalar.boundaryR δ ^ 2 - (80 / 9 : ℝ) ^ 2 * δ ^ 2 =
      (Scalar.boundaryR δ + (80 / 9) * δ) * (Scalar.boundaryR δ - (80 / 9) * δ) := by ring
  rw [hf, abs_mul, abs_of_nonneg (by positivity), he]
  calc
    _ ≤ (2 * (80 / 9) * δ) * ((11 / 6) * ((80 / 9) * δ) ^ 2) := by
      apply mul_le_mul
      · linarith
      · exact mul_le_mul_of_nonneg_left hs (by norm_num)
      · positivity
      · positivity
    _ = (11 / 3) * (80 / 9 : ℝ) ^ 3 * δ ^ 3 := by ring

def spectralBoundaryCost (δ : ℝ) : ℝ :=
  entropyCombination (Scalar.boundaryR δ) / (2 * Real.log 2)

theorem spectralBoundaryCost_uniform_remainder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ 21 / 512 →
      |spectralBoundaryCost δ -
        (3200 * Scalar.boundaryKappa / (81 * Real.log 2)) * δ ^ 2| ≤ C * δ ^ 3 := by
  obtain ⟨C, hC, hrem⟩ := entropyCombination_uniform_remainder
  have hk := Scalar.boundaryKappa_pos
  have hlog := Scalar.log_two_pos
  let Cδ : ℝ := (80 / 9 : ℝ) ^ 3 * (C + (11 / 3) * Scalar.boundaryKappa) /
    (2 * Real.log 2)
  refine ⟨Cδ, by dsimp [Cδ]; positivity, ?_⟩
  intro δ hδ hmax
  have hr := Scalar.boundaryR_nonneg hδ
  have hrmax := Scalar.boundaryR_le_quarter hδ hmax
  have hl := Scalar.boundaryR_le_linear hδ
  have hpow : Scalar.boundaryR δ ^ 3 ≤ ((80 / 9 : ℝ) * δ) ^ 3 :=
    pow_le_pow_left₀ hr hl 3
  have h1 := hrem (Scalar.boundaryR δ) hr hrmax
  have h2 := boundaryR_square_error hδ
  have habs : |entropyCombination (Scalar.boundaryR δ) -
      Scalar.boundaryKappa * (80 / 9 : ℝ) ^ 2 * δ ^ 2| ≤
      (80 / 9 : ℝ) ^ 3 * (C + (11 / 3) * Scalar.boundaryKappa) * δ ^ 3 := by
    have he : entropyCombination (Scalar.boundaryR δ) -
        Scalar.boundaryKappa * (80 / 9 : ℝ) ^ 2 * δ ^ 2 =
        (entropyCombination (Scalar.boundaryR δ) - Scalar.boundaryKappa * Scalar.boundaryR δ ^ 2) +
        Scalar.boundaryKappa * (Scalar.boundaryR δ ^ 2 - (80 / 9 : ℝ) ^ 2 * δ ^ 2) := by ring
    rw [he]
    calc
      _ ≤ |entropyCombination (Scalar.boundaryR δ) - Scalar.boundaryKappa * Scalar.boundaryR δ ^ 2| +
        |Scalar.boundaryKappa * (Scalar.boundaryR δ ^ 2 - (80 / 9 : ℝ) ^ 2 * δ ^ 2)| := abs_add_le _ _
      _ ≤ C * Scalar.boundaryR δ ^ 3 + Scalar.boundaryKappa *
          ((11 / 3) * (80 / 9 : ℝ) ^ 3 * δ ^ 3) := by
        rw [abs_mul, abs_of_pos hk]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 hk.le)
      _ ≤ C * ((80 / 9 : ℝ) * δ) ^ 3 + Scalar.boundaryKappa *
          ((11 / 3) * (80 / 9 : ℝ) ^ 3 * δ ^ 3) :=
        add_le_add (mul_le_mul_of_nonneg_left hpow hC) (le_refl _)
      _ = _ := by ring
  have he : spectralBoundaryCost δ -
      (3200 * Scalar.boundaryKappa / (81 * Real.log 2)) * δ ^ 2 =
      (entropyCombination (Scalar.boundaryR δ) -
        Scalar.boundaryKappa * (80 / 9 : ℝ) ^ 2 * δ ^ 2) / (2 * Real.log 2) := by
    dsimp [spectralBoundaryCost]
    ring
  have hden : 0 < 2 * Real.log 2 := mul_pos (by norm_num) hlog
  rw [he, abs_div, abs_of_pos hden]
  have h := div_le_div_of_nonneg_right habs hden.le
  dsimp [Cδ]
  convert h using 1 <;> (try rfl) <;> ring

end QuantumProver.DepolarizingSquashedEntanglement.Fixed16Calculus
