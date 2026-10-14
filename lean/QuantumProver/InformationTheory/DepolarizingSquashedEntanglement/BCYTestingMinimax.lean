import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYCompositeTesting
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYOneWaySeparation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix Set Filter
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal NNReal

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYTestingMinimax

open BCYRelativeEntropy BCYCompositeTesting

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

def matrixEffectMatrices (I : Type*) [Fintype I] [DecidableEq I] : Set (QMatrix I) :=
  {T | T.PosSemidef ∧ (1 - T).PosSemidef}

def feasibleEffectMatrices (ρ : Density I) (epsilon : ℝ) : Set (QMatrix I) :=
  {T | T ∈ matrixEffectMatrices I ∧ 1 - epsilon ≤ (ρ.matrix * T).trace.re}

theorem matrixEffectMatrices_isClosed : IsClosed (matrixEffectMatrices I) := by
  change IsClosed ({T : QMatrix I | T.PosSemidef} ∩
    (fun T : QMatrix I => 1 - T) ⁻¹' {T : QMatrix I | T.PosSemidef})
  exact Matrix.posSemidef_is_closed.inter
    (Matrix.posSemidef_is_closed.preimage (by fun_prop))

theorem matrixEffectMatrices_norm_le_one {T : QMatrix I}
    (hT : T ∈ matrixEffectMatrices I) : ‖T‖ ≤ 1 := by
  apply (CStarAlgebra.norm_le_iff_le_algebraMap T zero_le_one hT.1.nonneg).mpr
  simpa only [map_one] using (sub_nonneg.mp hT.2.nonneg)

theorem matrixEffectMatrices_isCompact : IsCompact (matrixEffectMatrices I) := by
  apply (isCompact_closedBall (0 : QMatrix I) 1).of_isClosed_subset
    matrixEffectMatrices_isClosed
  intro T hT
  simpa only [Metric.mem_closedBall, dist_zero_right] using matrixEffectMatrices_norm_le_one hT

theorem matrixEffectMatrices_convex : Convex ℝ (matrixEffectMatrices I) := by
  intro R hR S hS a b ha hb hab
  refine ⟨(hR.1.smul ha).add (hS.1.smul hb), ?_⟩
  have he : 1 - (a • R + b • S) = a • (1 - R) + b • (1 - S) := by
    calc
      1 - (a • R + b • S) = (a + b) • (1 : QMatrix I) - (a • R + b • S) := by
        rw [hab, one_smul]
      _ = a • (1 - R) + b • (1 - S) := by
        rw [add_smul]
        simp only [smul_sub]
        abel
  rw [he]
  exact (hR.2.smul ha).add (hS.2.smul hb)

omit [DecidableEq I] in
private theorem tracePair_mix_right (R S T : QMatrix I) (a b : ℝ) :
    (R * (a • S + b • T)).trace.re =
      a * (R * S).trace.re + b * (R * T).trace.re := by
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul]

omit [DecidableEq I] in
private theorem tracePair_mix_left (R S T : QMatrix I) (a b : ℝ) :
    ((a • R + b • S) * T).trace.re =
      a * (R * T).trace.re + b * (S * T).trace.re := by
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul]

theorem feasibleEffectMatrices_isClosed (ρ : Density I) (epsilon : ℝ) :
    IsClosed (feasibleEffectMatrices ρ epsilon) := by
  change IsClosed (matrixEffectMatrices I ∩
    (fun T : QMatrix I => (ρ.matrix * T).trace.re) ⁻¹' Set.Ici (1 - epsilon))
  exact matrixEffectMatrices_isClosed.inter (isClosed_Ici.preimage (by fun_prop))

theorem feasibleEffectMatrices_isCompact (ρ : Density I) (epsilon : ℝ) :
    IsCompact (feasibleEffectMatrices ρ epsilon) :=
  matrixEffectMatrices_isCompact.of_isClosed_subset
    (feasibleEffectMatrices_isClosed ρ epsilon) (fun _ h => h.1)

theorem feasibleEffectMatrices_convex (ρ : Density I) (epsilon : ℝ) :
    Convex ℝ (feasibleEffectMatrices ρ epsilon) := by
  intro R hR S hS a b ha hb hab
  refine ⟨matrixEffectMatrices_convex hR.1 hS.1 ha hb hab, ?_⟩
  rw [tracePair_mix_right]
  have hr := mul_le_mul_of_nonneg_left hR.2 ha
  have hs := mul_le_mul_of_nonneg_left hS.2 hb
  calc
    1 - epsilon = a * (1 - epsilon) + b * (1 - epsilon) := by rw [← add_mul, hab, one_mul]
    _ ≤ a * (ρ.matrix * R).trace.re + b * (ρ.matrix * S).trace.re := add_le_add hr hs

theorem feasibleEffectMatrices_nonempty (ρ : Density I) {epsilon : ℝ}
    (he : 0 ≤ epsilon) : (feasibleEffectMatrices ρ epsilon).Nonempty := by
  refine ⟨1, ⟨⟨Matrix.PosSemidef.one, ?_⟩, ?_⟩⟩
  · simpa using (Matrix.PosSemidef.zero : (0 : QMatrix I).PosSemidef)
  · simpa only [Matrix.mul_one, ρ.trace_one, Complex.one_re] using sub_le_self 1 he

theorem exists_fixedError_saddle (ρ : Density (A × B)) {epsilon : ℝ}
    (he : 0 ≤ epsilon) :
    ∃ T : BinaryEffect (A × B), ∃ σ : SeparableDensity A B,
      1 - epsilon ≤ acceptance ρ T ∧
      (∀ γ : SeparableDensity A B, acceptance γ.val T ≤ acceptance σ.val T) ∧
      (∀ U : BinaryEffect (A × B), 1 - epsilon ≤ acceptance ρ U →
        acceptance σ.val T ≤ acceptance σ.val U) := by
  let X := feasibleEffectMatrices ρ epsilon
  let Y := BCYOneWaySeparation.separableMatrices A B
  let f := fun (T S : QMatrix (A × B)) => (S * T).trace.re
  have cX : Convex ℝ X := feasibleEffectMatrices_convex ρ epsilon
  have cY : Convex ℝ Y := BCYOneWaySeparation.separableMatrices_convex
  have hfy (S : QMatrix (A × B)) (_hS : S ∈ Y) :
      LowerSemicontinuousOn (fun T => f T S) X :=
    (show Continuous (fun T => f T S) by dsimp [f]; fun_prop).continuousOn.lowerSemicontinuousOn
  have hfx (T : QMatrix (A × B)) (_hT : T ∈ X) :
      UpperSemicontinuousOn (fun S => f T S) Y :=
    (show Continuous (fun S => f T S) by dsimp [f]; fun_prop).continuousOn.upperSemicontinuousOn
  have hfy' (S : QMatrix (A × B)) (_hS : S ∈ Y) :
      QuasiconvexOn ℝ X (fun T => f T S) := by
    apply ConvexOn.quasiconvexOn
    refine ⟨cX, ?_⟩
    intro R hR T hT a b ha hb hab
    exact le_of_eq (tracePair_mix_right S R T a b)
  have hfx' (T : QMatrix (A × B)) (_hT : T ∈ X) :
      QuasiconcaveOn ℝ Y (fun S => f T S) := by
    apply ConcaveOn.quasiconcaveOn
    refine ⟨cY, ?_⟩
    intro R hR S hS a b ha hb hab
    exact le_of_eq (tracePair_mix_left R S T a b).symm
  obtain ⟨T, hT, S, hS, hs⟩ := Sion.exists_isSaddlePointOn'
    (X := X) (Y := Y) (f := f)
    (ne_X := feasibleEffectMatrices_nonempty ρ he)
    (cX := cX) (kX := feasibleEffectMatrices_isCompact ρ epsilon)
    (hfy := hfy) (hfy' := hfy') (cY := cY)
    (ne_Y := BCYOneWaySeparation.separableMatrices_nonempty ρ)
    (kY := BCYOneWaySeparation.separableMatrices_isCompact)
    (hfx := hfx) (hfx' := hfx')
  have hSd := BCYOneWaySeparation.separableMatrices_subset_density hS
  let σ : SeparableDensity A B := ⟨⟨S, hSd.1, hSd.2⟩, hS⟩
  let t : BinaryEffect (A × B) := ⟨T, hT.1.1, hT.1.2⟩
  refine ⟨t, σ, hT.2, ?_, ?_⟩
  · intro γ
    exact hs T hT γ.val.matrix γ.property
  · intro U hU
    exact hs U.matrix ⟨U.represented, hU⟩ S hS

theorem exists_fixedError_optimizers (ρ : Density (A × B)) {epsilon : ℝ}
    (he : 0 ≤ epsilon) :
    ∃ T : BinaryEffect (A × B), ∃ σ : SeparableDensity A B,
      1 - epsilon ≤ acceptance ρ T ∧
      worstSeparableBeta T = acceptance σ.val T ∧
      fixedErrorBeta ρ epsilon = ENNReal.ofReal (acceptance σ.val T) ∧
      singleAlternativeBeta ρ σ.val epsilon = ENNReal.ofReal (acceptance σ.val T) := by
  obtain ⟨T, σ, hT, hmax, hmin⟩ := exists_fixedError_saddle ρ he
  have hw : worstSeparableBeta T = acceptance σ.val T :=
    le_antisymm (worstSeparableBeta_le ρ T hmax) (acceptance_le_worstSeparableBeta T σ)
  have hslo : ENNReal.ofReal (acceptance σ.val T) ≤ singleAlternativeBeta ρ σ.val epsilon := by
    apply le_iInf
    intro U
    exact ENNReal.ofReal_le_ofReal (hmin U.val U.property)
  have hshi : singleAlternativeBeta ρ σ.val epsilon ≤ ENNReal.ofReal (acceptance σ.val T) :=
    iInf_le_of_le ⟨T, hT⟩ le_rfl
  have hchi : fixedErrorBeta ρ epsilon ≤ ENNReal.ofReal (acceptance σ.val T) := by
    apply iInf_le_of_le ⟨T, hT⟩
    rw [hw]
  have hclo := hslo.trans (singleAlternativeBeta_le_fixedErrorBeta ρ σ epsilon)
  exact ⟨T, σ, hT, hw, le_antisymm hchi hclo, le_antisymm hshi hslo⟩

theorem exists_fixedErrorBeta_eq_singleAlternativeBeta (ρ : Density (A × B))
    {epsilon : ℝ} (he : 0 ≤ epsilon) :
    ∃ σ : SeparableDensity A B,
      fixedErrorBeta ρ epsilon = singleAlternativeBeta ρ σ.val epsilon := by
  obtain ⟨T, σ, hT, hw, hc, hs⟩ := exists_fixedError_optimizers ρ he
  exact ⟨σ, hc.trans hs.symm⟩

theorem exists_hypothesisTestingNat_eq_singleAlternative (ρ : Density (A × B))
    {epsilon : ℝ} (he : 0 ≤ epsilon) :
    ∃ σ : SeparableDensity A B,
      hypothesisTestingNat ρ epsilon = hypothesisTestingSingleNat ρ σ.val epsilon := by
  obtain ⟨σ, hσ⟩ := exists_fixedErrorBeta_eq_singleAlternativeBeta ρ he
  exact ⟨σ, congrArg (fun q : ℝ≥0∞ => -ENNReal.log q) hσ⟩

theorem fixedErrorBeta_eq_iSup_singleAlternativeBeta (ρ : Density (A × B))
    {epsilon : ℝ} (he : 0 ≤ epsilon) :
    fixedErrorBeta ρ epsilon =
      ⨆ σ : SeparableDensity A B, singleAlternativeBeta ρ σ.val epsilon := by
  apply le_antisymm
  · obtain ⟨σ, hσ⟩ := exists_fixedErrorBeta_eq_singleAlternativeBeta ρ he
    rw [hσ]
    exact le_iSup (fun γ : SeparableDensity A B => singleAlternativeBeta ρ γ.val epsilon) σ
  · apply iSup_le
    intro σ
    exact singleAlternativeBeta_le_fixedErrorBeta ρ σ epsilon

theorem exists_fixedErrorBetaReal_eq_singleAlternativeBetaReal (ρ : Density (A × B))
    {epsilon : ℝ} (he : 0 ≤ epsilon) :
    ∃ σ : SeparableDensity A B,
      fixedErrorBetaReal ρ epsilon = singleAlternativeBetaReal ρ σ.val epsilon := by
  obtain ⟨σ, hσ⟩ := exists_fixedErrorBeta_eq_singleAlternativeBeta ρ he
  have hc : 0 ≤ fixedErrorBetaReal ρ epsilon :=
    Real.iInf_nonneg fun U => (worstSeparableBeta_bounds ρ U.val).1
  have hs : 0 ≤ singleAlternativeBetaReal ρ σ.val epsilon :=
    Real.iInf_nonneg fun U => (acceptance_bounds σ.val U.val).1
  rw [fixedErrorBeta_eq_ofReal ρ he, singleAlternativeBeta_eq_ofReal ρ σ.val he] at hσ
  have h := congrArg ENNReal.toReal hσ
  rw [ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hs] at h
  exact ⟨σ, h⟩

end QuantumProver.DepolarizingSquashedEntanglement.BCYTestingMinimax
