import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.FlaggedStates

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.SuperchannelDiscrimination.EffectPerturbation

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def traceNorm (A : Matrix n n ℂ) : ℝ := (CFC.abs A).trace.re

def effectValue (E A : Matrix n n ℂ) : ℝ := (E * A).trace.re

theorem effectValue_eq_acceptance (E A : Matrix n n ℂ) :
    effectValue E A = FlaggedStates.acceptanceProbability A E := by
  exact congrArg Complex.re (Matrix.trace_mul_comm E A)

theorem traceNorm_nonneg (A : Matrix n n ℂ) : 0 ≤ traceNorm A :=
  (Complex.nonneg_iff.mp (CFC.abs_nonneg A).posSemidef.trace_nonneg).1

theorem traceNorm_of_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    traceNorm A = A.trace.re := by
  simp only [traceNorm, CFC.abs_of_nonneg A hA.nonneg]

theorem effect_trace_mul_le_trace {E A : Matrix n n ℂ}
    (hEcomp : (1 - E).PosSemidef) (hA : A.PosSemidef) :
    effectValue E A ≤ A.trace.re := by
  have hc := FlaggedStates.trace_mul_re_nonneg hEcomp hA
  simp only [sub_mul, one_mul, Matrix.trace_sub, Complex.sub_re] at hc
  exact sub_nonneg.mp hc

theorem traceNorm_eq_jordan {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm A = A⁺.trace.re + A⁻.trace.re := by
  unfold traceNorm
  rw [← CFC.posPart_add_negPart A hA.isSelfAdjoint, Matrix.trace_add, Complex.add_re]

theorem trace_eq_jordan {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.trace.re = A⁺.trace.re - A⁻.trace.re := by
  have he := congrArg (fun M : Matrix n n ℂ => M.trace.re)
    (CFC.posPart_sub_negPart A hA.isSelfAdjoint)
  simpa only [Matrix.trace_sub, Complex.sub_re] using he.symm

theorem effectValue_eq_jordan {E A : Matrix n n ℂ} (hA : A.IsHermitian) :
    effectValue E A = effectValue E A⁺ - effectValue E A⁻ := by
  nth_rw 1 [← CFC.posPart_sub_negPart A hA.isSelfAdjoint]
  simp [effectValue, mul_sub, Matrix.trace_sub]

theorem effectValue_jordan_bounds {E A : Matrix n n ℂ}
    (hE : FlaggedStates.IsEffect E) (hA : A.IsHermitian) :
    -A⁻.trace.re ≤ effectValue E A ∧ effectValue E A ≤ A⁺.trace.re := by
  have hpos : A⁺.PosSemidef := (CFC.posPart_nonneg A).posSemidef
  have hneg : A⁻.PosSemidef := (CFC.negPart_nonneg A).posSemidef
  have hp0 := FlaggedStates.trace_mul_re_nonneg hE.1 hpos
  have hn0 := FlaggedStates.trace_mul_re_nonneg hE.1 hneg
  have hp1 := effect_trace_mul_le_trace hE.2 hpos
  have hn1 := effect_trace_mul_le_trace hE.2 hneg
  change 0 ≤ effectValue E A⁺ at hp0
  change 0 ≤ effectValue E A⁻ at hn0
  rw [effectValue_eq_jordan hA]
  constructor <;> linarith

theorem effectValue_abs_le_traceNorm {E A : Matrix n n ℂ}
    (hE : FlaggedStates.IsEffect E) (hA : A.IsHermitian) :
    |effectValue E A| ≤ traceNorm A := by
  have hp := (Complex.nonneg_iff.mp (CFC.posPart_nonneg A).posSemidef.trace_nonneg).1
  have hn := (Complex.nonneg_iff.mp (CFC.negPart_nonneg A).posSemidef.trace_nonneg).1
  have hb := effectValue_jordan_bounds hE hA
  rw [traceNorm_eq_jordan hA]
  apply abs_le.mpr
  constructor <;> linarith

theorem effectValue_abs_le_half_traceNorm_add_abs_trace {E A : Matrix n n ℂ}
    (hE : FlaggedStates.IsEffect E) (hA : A.IsHermitian) :
    |effectValue E A| ≤ (1 / 2) * (traceNorm A + |A.trace.re|) := by
  have hb := effectValue_jordan_bounds hE hA
  have hs := traceNorm_eq_jordan hA
  have ht := trace_eq_jordan hA
  have ht1 := le_abs_self A.trace.re
  have ht2 := neg_le_abs A.trace.re
  apply abs_le.mpr
  constructor <;> linarith

theorem effect_traceless_bound {E A : Matrix n n ℂ}
    (hE : FlaggedStates.IsEffect E) (hA : A.IsHermitian) (htr : A.trace = 0) :
    |effectValue E A| ≤ (1 / 2) * traceNorm A := by
  simpa only [htr, Complex.zero_re, abs_zero, add_zero] using
    effectValue_abs_le_half_traceNorm_add_abs_trace hE hA

theorem acceptanceDifference_abs_le_traceNorm {A B E : Matrix n n ℂ}
    (hE : FlaggedStates.IsEffect E) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    |FlaggedStates.acceptanceProbability A E - FlaggedStates.acceptanceProbability B E| ≤
      traceNorm (A - B) := by
  rw [← effectValue_eq_acceptance E A, ← effectValue_eq_acceptance E B]
  simpa [effectValue, mul_sub, Matrix.trace_sub] using
    effectValue_abs_le_traceNorm hE (hA.sub hB)

theorem density_acceptanceDifference_abs_le_half_traceNorm {A B E : Matrix n n ℂ}
    (hE : FlaggedStates.IsEffect E) (hA : FlaggedStates.IsDensity A) (hB : FlaggedStates.IsDensity B) :
    |FlaggedStates.acceptanceProbability A E - FlaggedStates.acceptanceProbability B E| ≤
      (1 / 2) * traceNorm (A - B) := by
  have ht : (A - B).trace = 0 := by simp [Matrix.trace_sub, hA.2, hB.2]
  rw [← effectValue_eq_acceptance E A, ← effectValue_eq_acceptance E B]
  simpa [effectValue, mul_sub, Matrix.trace_sub] using
    effect_traceless_bound hE (hA.1.isHermitian.sub hB.1.isHermitian) ht

theorem successful_acceptanceDifference_abs_le_traceNorm
    {A C E : Matrix n n ℂ} (B : Matrix m m ℂ)
    (hE : FlaggedStates.IsEffect E) (hA : A.IsHermitian) (hC : C.IsHermitian) :
    |FlaggedStates.acceptanceProbability (FlaggedStates.flagBlock A B) (FlaggedStates.successfulEffect E) -
      FlaggedStates.acceptanceProbability C E| ≤ traceNorm (A - C) := by
  rw [FlaggedStates.acceptanceProbability_success]
  exact acceptanceDifference_abs_le_traceNorm hE hA hC

theorem traceNorm_flagBlock {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    traceNorm (FlaggedStates.flagBlock A B) = traceNorm A + traceNorm B := by
  have habs : CFC.abs (FlaggedStates.flagBlock A B) =
      FlaggedStates.flagBlock (CFC.abs A) (CFC.abs B) := by
    rw [CFC.abs_eq_cfc_norm _ (FlaggedStates.flagBlock_isHermitian hA hB).isSelfAdjoint,
      FlaggedStates.cfc_flagBlock _ hA hB,
      ← CFC.abs_eq_cfc_norm A hA.isSelfAdjoint, ← CFC.abs_eq_cfc_norm B hB.isSelfAdjoint]
  simp only [traceNorm, habs, FlaggedStates.flagBlock_trace, Complex.add_re]

theorem completed_flag_acceptanceDifference_abs_bound
    {A C E : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hE : FlaggedStates.IsEffect E) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htr : A.trace + B.trace = 1) (hC : FlaggedStates.IsDensity C) :
    |FlaggedStates.acceptanceProbability (FlaggedStates.flagBlock A B) (FlaggedStates.successfulEffect E) -
      FlaggedStates.acceptanceProbability C E| ≤ (1 / 2) * (traceNorm (A - C) + B.trace.re) := by
  have hactual := FlaggedStates.flagBlock_isDensity hA hB htr
  have hideal : FlaggedStates.IsDensity (FlaggedStates.flagBlock C (0 : Matrix m m ℂ)) :=
    FlaggedStates.flagBlock_isDensity hC.1 Matrix.PosSemidef.zero (by simpa using hC.2)
  have hb := density_acceptanceDifference_abs_le_half_traceNorm
    (FlaggedStates.successfulEffect_isEffect hE) hactual hideal
  have hdiff : FlaggedStates.flagBlock A B - FlaggedStates.flagBlock C 0 = FlaggedStates.flagBlock (A - C) B := by
    ext i j
    cases i <;> cases j <;> simp [FlaggedStates.flagBlock]
  rw [FlaggedStates.acceptanceProbability_success, FlaggedStates.acceptanceProbability_success,
    hdiff, traceNorm_flagBlock (hA.isHermitian.sub hC.1.isHermitian) hB.isHermitian,
    traceNorm_of_posSemidef hB] at hb
  simpa only [FlaggedStates.acceptanceProbability_success] using hb

theorem acceptanceDifference_two_errors {A B C E : Matrix n n ℂ}
    (hE : FlaggedStates.IsEffect E) (hA : A.IsHermitian)
    (hB : FlaggedStates.IsDensity B) (hC : FlaggedStates.IsDensity C) :
    |FlaggedStates.acceptanceProbability A E - FlaggedStates.acceptanceProbability C E| ≤
      traceNorm (A - B) + (1 / 2) * traceNorm (B - C) := by
  have h1 := acceptanceDifference_abs_le_traceNorm hE hA hB.1.isHermitian
  have h2 := density_acceptanceDifference_abs_le_half_traceNorm hE hB hC
  have ht := abs_sub_le (FlaggedStates.acceptanceProbability A E)
    (FlaggedStates.acceptanceProbability B E) (FlaggedStates.acceptanceProbability C E)
  linarith

theorem acceptance_lower_bound_of_matrix_errors {A B C E : Matrix n n ℂ}
    (hE : FlaggedStates.IsEffect E) (hA : A.IsHermitian)
    (hB : FlaggedStates.IsDensity B) (hC : FlaggedStates.IsDensity C) {delta eta : ℝ}
    (hdelta : traceNorm (A - B) ≤ delta) (heta : traceNorm (B - C) ≤ eta) :
    FlaggedStates.acceptanceProbability C E - delta - (1 / 2) * eta ≤
      FlaggedStates.acceptanceProbability A E := by
  have hb := (abs_le.mp (acceptanceDifference_two_errors hE hA hB hC)).1
  linarith

def positiveIndicator (x : ℝ) : ℝ := if 0 < x then 1 else 0

def positiveSupport (A : Matrix n n ℂ) : Matrix n n ℂ := cfc positiveIndicator A

theorem positiveSupport_isEffect {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    FlaggedStates.IsEffect (positiveSupport A) := by
  have hpos : (positiveSupport A).PosSemidef := by
    refine (show (0 : Matrix n n ℂ) ≤ cfc positiveIndicator A from ?_).posSemidef
    apply cfc_nonneg (p := IsSelfAdjoint)
    intro x hx
    simp only [positiveIndicator]
    split_ifs <;> norm_num
  have hcomp : 1 - positiveSupport A = cfc (fun x : ℝ => 1 - positiveIndicator x) A := by
    rw [cfc_sub (p := IsSelfAdjoint) (fun _ : ℝ => 1) positiveIndicator A
      (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
      cfc_const_one (p := IsSelfAdjoint) ℝ A hA.isSelfAdjoint]
    rfl
  refine ⟨hpos, ?_⟩
  rw [hcomp]
  refine (show (0 : Matrix n n ℂ) ≤ cfc (fun x : ℝ => 1 - positiveIndicator x) A from ?_).posSemidef
  apply cfc_nonneg (p := IsSelfAdjoint)
  intro x hx
  simp only [positiveIndicator]
  split_ifs <;> norm_num

theorem positiveSupport_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    positiveSupport A * A = A⁺ := by
  have hfun : (fun x : ℝ => positiveIndicator x * x) = (fun x : ℝ => x⁺) := by
    funext x
    by_cases hx : 0 < x
    · simp [positiveIndicator, hx, posPart_eq_self.mpr (le_of_lt hx)]
    · simp [positiveIndicator, hx, posPart_eq_zero.mpr (le_of_not_gt hx)]
  calc
    positiveSupport A * A = cfc positiveIndicator A * cfc (fun x : ℝ => x) A := by
      rw [cfc_id' (p := IsSelfAdjoint) ℝ A hA.isSelfAdjoint]
      rfl
    _ = cfc (fun x : ℝ => positiveIndicator x * x) A :=
      (cfc_mul (p := IsSelfAdjoint) positiveIndicator (fun x : ℝ => x) A
        (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)).symm
    _ = A⁺ := by rw [hfun, CFC.posPart_def, cfcₙ_eq_cfc]

theorem positiveSupport_idempotent (A : Matrix n n ℂ) :
    positiveSupport A * positiveSupport A = positiveSupport A := by
  have hfun : (fun x : ℝ => positiveIndicator x * positiveIndicator x) = positiveIndicator := by
    funext x
    simp only [positiveIndicator]
    split_ifs <;> norm_num
  unfold positiveSupport
  rw [← cfc_mul (p := IsSelfAdjoint) positiveIndicator positiveIndicator A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _), hfun]

theorem traceNorm_eq_positiveSupport {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm A = 2 * effectValue (positiveSupport A) A - A.trace.re := by
  have hp : effectValue (positiveSupport A) A = A⁺.trace.re := by
    simp only [effectValue, positiveSupport_mul hA]
  have hn := traceNorm_eq_jordan hA
  have ht := trace_eq_jordan hA
  linarith

theorem effectValue_positiveSupport {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    effectValue (positiveSupport A) A = (1 / 2) * (traceNorm A + A.trace.re) := by
  have h := traceNorm_eq_positiveSupport hA
  linarith

theorem density_traceNorm_effect_characterization {A B : Matrix n n ℂ}
    (hA : FlaggedStates.IsDensity A) (hB : FlaggedStates.IsDensity B) :
    (∀ E, FlaggedStates.IsEffect E →
      |FlaggedStates.acceptanceProbability A E - FlaggedStates.acceptanceProbability B E| ≤
        (1 / 2) * traceNorm (A - B)) ∧
    (∃ E, FlaggedStates.IsEffect E ∧
      FlaggedStates.acceptanceProbability A E - FlaggedStates.acceptanceProbability B E =
        (1 / 2) * traceNorm (A - B)) := by
  have hH := hA.1.isHermitian.sub hB.1.isHermitian
  refine ⟨fun E hE => density_acceptanceDifference_abs_le_half_traceNorm hE hA hB, ?_⟩
  refine ⟨positiveSupport (A - B), positiveSupport_isEffect hH, ?_⟩
  rw [← effectValue_eq_acceptance, ← effectValue_eq_acceptance]
  have he : effectValue (positiveSupport (A - B)) A - effectValue (positiveSupport (A - B)) B =
      effectValue (positiveSupport (A - B)) (A - B) := by
    simp [effectValue, mul_sub, Matrix.trace_sub]
  rw [he, effectValue_positiveSupport hH]
  simp only [Matrix.trace_sub, hA.2, hB.2, sub_self, Complex.zero_re, add_zero]

theorem traceNorm_sub_le_traces {P Q : Matrix n n ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    traceNorm (P - Q) ≤ P.trace.re + Q.trace.re := by
  have hH := hP.isHermitian.sub hQ.isHermitian
  have hE := positiveSupport_isEffect hH
  have hp := effect_trace_mul_le_trace hE.2 hP
  have hq := FlaggedStates.trace_mul_re_nonneg hE.1 hQ
  have he : effectValue (positiveSupport (P - Q)) (P - Q) =
      effectValue (positiveSupport (P - Q)) P - effectValue (positiveSupport (P - Q)) Q := by
    simp [effectValue, mul_sub, Matrix.trace_sub]
  rw [traceNorm_eq_positiveSupport hH, he, Matrix.trace_sub, Complex.sub_re]
  change 0 ≤ effectValue (positiveSupport (P - Q)) Q at hq
  linarith

theorem traceNorm_contracts_positive_traceNonincreasing
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (hpos : ∀ P, P.PosSemidef → (Φ P).PosSemidef)
    (htrace : ∀ P, P.PosSemidef → (Φ P).trace.re ≤ P.trace.re)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (Φ A) ≤ traceNorm A := by
  have hp := hpos A⁺ (CFC.posPart_nonneg A).posSemidef
  have hn := hpos A⁻ (CFC.negPart_nonneg A).posSemidef
  have he : Φ A = Φ A⁺ - Φ A⁻ := by
    rw [← map_sub, CFC.posPart_sub_negPart A hA.isSelfAdjoint]
  rw [he]
  calc
    traceNorm (Φ A⁺ - Φ A⁻) ≤ (Φ A⁺).trace.re + (Φ A⁻).trace.re :=
      traceNorm_sub_le_traces hp hn
    _ ≤ A⁺.trace.re + A⁻.trace.re :=
      add_le_add (htrace A⁺ (CFC.posPart_nonneg A).posSemidef)
        (htrace A⁻ (CFC.negPart_nonneg A).posSemidef)
    _ = traceNorm A := (traceNorm_eq_jordan hA).symm

theorem traceNorm_contracts_positive_tracePreserving
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (hpos : ∀ P, P.PosSemidef → (Φ P).PosSemidef)
    (htrace : ∀ P, (Φ P).trace = P.trace)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    traceNorm (Φ A) ≤ traceNorm A := by
  apply traceNorm_contracts_positive_traceNonincreasing Φ hpos _ hA
  intro P hP
  rw [htrace]

theorem traceNorm_difference_contracts
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (hpos : ∀ P, P.PosSemidef → (Φ P).PosSemidef)
    (htrace : ∀ P, (Φ P).trace = P.trace)
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    traceNorm (Φ A - Φ B) ≤ traceNorm (A - B) := by
  rw [← map_sub]
  exact traceNorm_contracts_positive_tracePreserving Φ hpos htrace (hA.sub hB)

theorem isDensity_map_positive_tracePreserving
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (hpos : ∀ P, P.PosSemidef → (Φ P).PosSemidef)
    (htrace : ∀ P, (Φ P).trace = P.trace)
    {A : Matrix n n ℂ} (hA : FlaggedStates.IsDensity A) :
    FlaggedStates.IsDensity (Φ A) :=
  ⟨hpos A hA.1, (htrace A).trans hA.2⟩

theorem density_acceptanceDifference_after_map
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (hpos : ∀ P, P.PosSemidef → (Φ P).PosSemidef)
    (htrace : ∀ P, (Φ P).trace = P.trace)
    {A B : Matrix n n ℂ} {E : Matrix m m ℂ}
    (hE : FlaggedStates.IsEffect E) (hA : FlaggedStates.IsDensity A)
    (hB : FlaggedStates.IsDensity B) :
    |FlaggedStates.acceptanceProbability (Φ A) E - FlaggedStates.acceptanceProbability (Φ B) E| ≤
      (1 / 2) * traceNorm (A - B) := by
  have hb := density_acceptanceDifference_abs_le_half_traceNorm hE
    (isDensity_map_positive_tracePreserving Φ hpos htrace hA)
    (isDensity_map_positive_tracePreserving Φ hpos htrace hB)
  have hc := traceNorm_difference_contracts Φ hpos htrace hA.1.isHermitian hB.1.isHermitian
  linarith

theorem acceptance_lower_bound_of_input_and_output_errors
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (hpos : ∀ P, P.PosSemidef → (Φ P).PosSemidef)
    (htrace : ∀ P, (Φ P).trace = P.trace)
    {A E : Matrix m m ℂ} {B C : Matrix n n ℂ}
    (hE : FlaggedStates.IsEffect E) (hA : A.IsHermitian)
    (hB : FlaggedStates.IsDensity B) (hC : FlaggedStates.IsDensity C) {delta eta : ℝ}
    (hdelta : traceNorm (A - Φ B) ≤ delta) (heta : traceNorm (B - C) ≤ eta) :
    FlaggedStates.acceptanceProbability (Φ C) E - delta - (1 / 2) * eta ≤
      FlaggedStates.acceptanceProbability A E := by
  apply acceptance_lower_bound_of_matrix_errors hE hA
    (isDensity_map_positive_tracePreserving Φ hpos htrace hB)
    (isDensity_map_positive_tracePreserving Φ hpos htrace hC) hdelta
  exact (traceNorm_difference_contracts Φ hpos htrace hB.1.isHermitian hC.1.isHermitian).trans heta

theorem successful_acceptance_lower_bound_of_input_and_output_errors
    {k : Type*} [Fintype k] [DecidableEq k]
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (hpos : ∀ P, P.PosSemidef → (Φ P).PosSemidef)
    (htrace : ∀ P, (Φ P).trace = P.trace)
    {A E : Matrix m m ℂ} {B C : Matrix n n ℂ} (repair : Matrix k k ℂ)
    (hE : FlaggedStates.IsEffect E) (hA : A.IsHermitian)
    (hB : FlaggedStates.IsDensity B) (hC : FlaggedStates.IsDensity C) {delta eta : ℝ}
    (hdelta : traceNorm (A - Φ B) ≤ delta) (heta : traceNorm (B - C) ≤ eta) :
    FlaggedStates.acceptanceProbability (Φ C) E - delta - (1 / 2) * eta ≤
      FlaggedStates.acceptanceProbability (FlaggedStates.flagBlock A repair)
        (FlaggedStates.successfulEffect E) := by
  rw [FlaggedStates.acceptanceProbability_success]
  exact acceptance_lower_bound_of_input_and_output_errors Φ hpos htrace hE hA hB hC hdelta heta

end QuantumProver.SuperchannelDiscrimination.EffectPerturbation
