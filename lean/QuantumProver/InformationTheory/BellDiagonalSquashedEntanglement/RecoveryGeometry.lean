import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.ExtensionIdentities
import QuantumProver.LinearAlgebra.SBTProbabilityWeight
import QuantumProver.InformationTheory.MeasuredRelativeEntropyVariational
import QuantumProver.InformationTheory.MeasuredRelativeEntropyContinuity
import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.ExtensionGeometry
import QuantumProver.InformationTheory.QuantumEntropy.PartialTraceKraus
import QuantumProver.InformationTheory.ConditionalEntropy.ProbabilityMixtures
import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.SBTModularLimits
import QuantumProver.LinearAlgebra.SBTProbabilityLimits
import QuantumProver.LinearAlgebra.RotatedPetzTraceComparison
import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.SBTIsometryChannels
import QuantumProver.InformationTheory.BellDiagonalSquashedEntanglement.SBTSupportTransport
import QuantumProver.InformationTheory.QuantumRelativeEntropyRegularization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix
  Matrix.Norms.L2Operator

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.ChannelAveraging

open MeasureTheory
open scoped Topology

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def cptpSet : Set (Mat I →L[ℂ] Mat O) :=
  {L | CompletelyPositive L.toLinearMap ∧ TracePreserving L.toLinearMap}

theorem cptpSet_convex : Convex ℝ (cptpSet (I := I) (O := O)) := by
  intro L hL M hM a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro r Y hY
    have heq : amplify (a • L + b • M).toLinearMap (Fin r) Y =
        a • amplify L.toLinearMap (Fin r) Y +
          b • amplify M.toLinearMap (Fin r) Y := by
      ext x y
      rfl
    rw [heq]
    exact ((hL.1 r Y hY).smul ha).add ((hM.1 r Y hY).smul hb)
  · intro A
    have hLt : (L A).trace = A.trace := hL.2 A
    have hMt : (M A).trace = A.trace := hM.2 A
    change ((a • L + b • M) A).trace = A.trace
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      Matrix.trace_add, Matrix.trace_smul]
    rw [hLt, hMt, ← add_smul, hab, one_smul]

theorem cptpSet_isClosed : IsClosed (cptpSet (I := I) (O := O)) := by
  unfold cptpSet CompletelyPositive TracePreserving
  simp only [Set.setOf_and, Set.setOf_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro r
    apply isClosed_iInter
    intro Y
    apply isClosed_iInter
    intro hY
    have hc : Continuous (fun L : Mat I →L[ℂ] Mat O =>
        amplify L.toLinearMap (Fin r) Y) := by
      change Continuous (fun L : Mat I →L[ℂ] Mat O =>
        fun (x y : O × Fin r) =>
          L (fun (i j : I) => Y (i, x.2) (j, y.2)) x.1 y.1)
      fun_prop
    exact Matrix.posSemidef_is_closed.preimage hc
  · apply isClosed_iInter
    intro A
    apply isClosed_eq _ continuous_const
    change Continuous (fun L : Mat I →L[ℂ] Mat O => (L A).trace)
    fun_prop

def probabilityAverageChannel {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (L : α → Mat I →L[ℂ] Mat O)
    (hCP : ∀ t, CompletelyPositive (L t).toLinearMap)
    (hTP : ∀ t, TracePreserving (L t).toLinearMap)
    (hInt : Integrable L μ) : Channel I O := by
  let M : Mat I →L[ℂ] Mat O := ∫ t, L t ∂μ
  have hMem : ∀ᵐ t ∂μ, L t ∈ cptpSet (I := I) (O := O) :=
    Filter.Eventually.of_forall fun t => ⟨hCP t, hTP t⟩
  have hm : (∫ t, L t ∂μ) ∈ cptpSet (I := I) (O := O) :=
    Convex.integral_mem (E := Mat I →L[ℂ] Mat O) (μ := μ) (f := L)
      (s := cptpSet (I := I) (O := O))
      (cptpSet_convex (I := I) (O := O))
      (cptpSet_isClosed (I := I) (O := O)) hMem hInt
  exact ⟨M.toLinearMap, hm.1, hm.2⟩

theorem probabilityAverageChannel_apply {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (L : α → Mat I →L[ℂ] Mat O)
    (hCP : ∀ t, CompletelyPositive (L t).toLinearMap)
    (hTP : ∀ t, TracePreserving (L t).toLinearMap)
    (hInt : Integrable L μ) (A : Mat I) :
    (probabilityAverageChannel μ L hCP hTP hInt).map A = ∫ t, L t A ∂μ := by
  exact ContinuousLinearMap.integral_apply hInt A

theorem probabilityAverageChannel_reference {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (L : α → Mat I →L[ℂ] Mat O)
    (hCP : ∀ t, CompletelyPositive (L t).toLinearMap)
    (hTP : ∀ t, TracePreserving (L t).toLinearMap)
    (hInt : Integrable L μ) (A : Mat I) (B : Mat O)
    (hRef : ∀ t, L t A = B) :
    (probabilityAverageChannel μ L hCP hTP hInt).map A = B := by
  rw [probabilityAverageChannel_apply]
  simp_rw [hRef]
  simp

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.ChannelAveraging

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

open QuantumProver.SuperchannelDiscrimination.TensorEntropy
open QuantumProver.SuperchannelDiscrimination.OutputSupport

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem output_support_root_columns (N : Channel I O) (σ : Density I) (q : I × O) :
    supportProjection (N.map σ.val) *
      (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map q * CFC.sqrt σ.val) =
      QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map q * CFC.sqrt σ.val := by
  let K := QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map
  let L : I × O → Matrix O I ℂ := fun j => K j * CFC.sqrt σ.val
  have hS : (CFC.sqrt σ.val).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ.val)).isHermitian
  have hτ : QuantumProver.SuperchannelDiscrimination.KrausCompletion.krausAction L 1 =
      N.map σ.val := by
    change (∑ j : I × O, L j * (1 : Mat I) * (L j)ᴴ) = N.map σ.val
    calc
      _ = ∑ j : I × O, K j * σ.val * (K j)ᴴ := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [L, Matrix.mul_one, Matrix.conjTranspose_mul, hS.eq,
          Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (CFC.sqrt σ.val) (CFC.sqrt σ.val),
          CFC.sqrt_mul_sqrt_self σ.val σ.property.1.nonneg]
      _ = _ := (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_reconstruct
        N.map N.completelyPositive σ.val).symm
  have h := QuantumProver.SuperchannelDiscrimination.OutputSupport.kraus_supportProjection
    L (B := (1 : Mat I)) Matrix.PosDef.one q
  rw [hτ] at h
  exact h

theorem petz_action_reference (N : Channel I O) (σ : Density I) :
    Geometry.krausAction (petzKraus N σ) (N.map σ.val) = σ.val := by
  let K := QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map
  let S := CFC.sqrt σ.val
  let R := inverseRoot (N.map σ.val)
  let P := supportProjection (N.map σ.val)
  have hS : Sᴴ = S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ.val)).isHermitian.eq
  have hR : Rᴴ = R := (inverseRoot_isHermitian _).eq
  have hSand : R * N.map σ.val * R = P :=
    inverseRoot_sandwich _ (N.posSemidef σ.property.1)
  have hSupp (q : I × O) : P * (K q * S) = K q * S :=
    output_support_root_columns N σ q
  have hTerm (q : I × O) :
      petzKraus N σ q * N.map σ.val * (petzKraus N σ q)ᴴ =
        S * ((K q)ᴴ * K q) * S := by
    change (S * (K q)ᴴ * R) * N.map σ.val * (S * (K q)ᴴ * R)ᴴ = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hS, hR]
    calc
      _ = S * (K q)ᴴ * (R * N.map σ.val * R) * K q * S := by
        simp only [Matrix.mul_assoc]
      _ = (K q * S)ᴴ * (P * (K q * S)) := by
        rw [hSand, Matrix.conjTranspose_mul, hS]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hSupp, Matrix.conjTranspose_mul, hS]; simp only [Matrix.mul_assoc]
  calc
    _ = ∑ q : I × O, S * ((K q)ᴴ * K q) * S := by
      exact Finset.sum_congr rfl (fun q hq => hTerm q)
    _ = S * (∑ q : I × O, (K q)ᴴ * K q) * S := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = σ.val := by
      rw [QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_gram
        N.map N.completelyPositive N.tracePreserving, Matrix.mul_one]
      exact CFC.sqrt_mul_sqrt_self σ.val σ.property.1.nonneg

theorem modularPhase_commutes_self (A : Mat I) (t : ℝ) :
    Commute (modularPhase A t : Mat I) A := by
  have h : Commute (cfc Real.log A) A := (Commute.refl A).cfc_real Real.log
  have h' := (h.smul_left (t / 2 : ℝ)).smul_left Complex.I
  change Commute (NormedSpace.exp (Complex.I • ((t / 2 : ℝ) • cfc Real.log A))) A
  exact h'.exp_left

theorem rotatedPetz_action (N : Channel I O) (σ : Density I) (t : ℝ) (A : Mat O) :
    Geometry.krausAction (rotatedPetzKraus N σ t) A =
      (modularPhase σ.val t : Mat I) *
        Geometry.krausAction (petzKraus N σ)
          ((modularPhase (N.map σ.val) t : Mat O)ᴴ * A *
            (modularPhase (N.map σ.val) t : Mat O)) *
        (modularPhase σ.val t : Mat I)ᴴ := by
  simp only [Geometry.krausAction, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [rotatedPetzKraus, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem rotatedPetz_action_reference (N : Channel I O) (σ : Density I) (t : ℝ) :
    Geometry.krausAction (rotatedPetzKraus N σ t) (N.map σ.val) = σ.val := by
  let W := modularPhase (N.map σ.val) t
  let U := modularPhase σ.val t
  have hW : (W : Mat O)ᴴ * (W : Mat O) = 1 := Matrix.mem_unitaryGroup_iff'.mp W.property
  have hU : (U : Mat I) * (U : Mat I)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp U.property
  have hWc := (modularPhase_commutes_self (N.map σ.val) t).eq
  have hUc := (modularPhase_commutes_self σ.val t).eq
  have hRot : (W : Mat O)ᴴ * N.map σ.val * (W : Mat O) = N.map σ.val := by
    calc
      _ = (W : Mat O)ᴴ * ((W : Mat O) * N.map σ.val) := by rw [Matrix.mul_assoc, ← hWc]
      _ = _ := by rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
  rw [rotatedPetz_action, hRot, petz_action_reference]
  change (U : Mat I) * σ.val * (U : Mat I)ᴴ = _
  rw [hUc, Matrix.mul_assoc, hU, Matrix.mul_one]

theorem completedPetzChannel_action (N : Channel I O) (σ : Density I)
    (o₀ : I) (A : Mat O) :
    (completedPetzChannel N σ o₀).map A =
      Geometry.krausAction (petzKraus N σ) A +
        Matrix.single o₀ o₀ (((1 - supportProjection (N.map σ.val)) * A).trace) := by
  dsimp only [completedPetzChannel]
  rw [supportCompletionChannel_action]
  rfl

theorem completedRotatedPetzChannel_action (N : Channel I O) (σ : Density I)
    (t : ℝ) (o₀ : I) (A : Mat O) :
    (completedRotatedPetzChannel N σ t o₀).map A =
      Geometry.krausAction (rotatedPetzKraus N σ t) A +
        Matrix.single o₀ o₀ (((1 - supportProjection (N.map σ.val)) * A).trace) := by
  dsimp only [completedRotatedPetzChannel]
  rw [supportCompletionChannel_action]
  rfl

theorem completedPetzChannel_reference (N : Channel I O) (σ : Density I) (o₀ : I) :
    (completedPetzChannel N σ o₀).map (N.map σ.val) = σ.val := by
  rw [completedPetzChannel_action, petz_action_reference,
    complement_mul_zero (N.posSemidef σ.property.1).isHermitian]
  simp

theorem completedRotatedPetzChannel_reference (N : Channel I O) (σ : Density I)
    (t : ℝ) (o₀ : I) :
    (completedRotatedPetzChannel N σ t o₀).map (N.map σ.val) = σ.val := by
  rw [completedRotatedPetzChannel_action, rotatedPetz_action_reference,
    complement_mul_zero (N.posSemidef σ.property.1).isHermitian]
  simp

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

open MeasureTheory

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def conjugationCLM (U : Mat I) : Mat I →L[ℂ] Mat I :=
  ContinuousLinearMap.mulLeftRight ℂ (Mat I) U Uᴴ

theorem conjugationCLM_norm_le_one (U : Mat I)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) : ‖conjugationCLM U‖ ≤ 1 := by
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup I ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  change ‖U * A * Uᴴ‖ ≤ 1 * ‖A‖
  rw [CStarRing.norm_mul_mem_unitary _ hUstar,
    CStarRing.norm_mem_unitary_mul A hU, one_mul]

theorem conjugationCLM_comp_norm_le (U : Matrix.unitaryGroup I ℂ)
    (W : Matrix.unitaryGroup O ℂ) (Φ : Mat O →L[ℂ] Mat I) :
    ‖(conjugationCLM (U : Mat I)).comp
      (Φ.comp (conjugationCLM (W : Mat O)ᴴ))‖ ≤ ‖Φ‖ := by
  have hU : ‖conjugationCLM (U : Mat I)‖ ≤ 1 :=
    conjugationCLM_norm_le_one (U : Mat I) U.property
  have hWstar : (W : Mat O)ᴴ ∈ Matrix.unitaryGroup O ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp W.property)
  have hW : ‖conjugationCLM (W : Mat O)ᴴ‖ ≤ 1 :=
    conjugationCLM_norm_le_one (W : Mat O)ᴴ hWstar
  have hInner : ‖Φ.comp (conjugationCLM (W : Mat O)ᴴ)‖ ≤ ‖Φ‖ := by
    calc
      _ ≤ ‖Φ‖ * ‖conjugationCLM (W : Mat O)ᴴ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Φ‖ * 1 := mul_le_mul_of_nonneg_left hW (norm_nonneg Φ)
      _ = ‖Φ‖ := mul_one _
  calc
    _ ≤ ‖conjugationCLM (U : Mat I)‖ *
        ‖Φ.comp (conjugationCLM (W : Mat O)ᴴ)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖Φ‖ := mul_le_mul hU hInner (norm_nonneg _) zero_le_one
    _ = ‖Φ‖ := one_mul _

theorem conjugationCLM_comp_add_norm_le (U : Matrix.unitaryGroup I ℂ)
    (W : Matrix.unitaryGroup O ℂ) (Φ Ψ : Mat O →L[ℂ] Mat I) :
    ‖(conjugationCLM (U : Mat I)).comp
      (Φ.comp (conjugationCLM (W : Mat O)ᴴ)) + Ψ‖ ≤ ‖Φ‖ + ‖Ψ‖ :=
  (norm_add_le _ Ψ).trans
    (add_le_add (conjugationCLM_comp_norm_le (I := I) (O := O) U W Φ) (le_refl ‖Ψ‖))

theorem modularPhase_continuous (A : Mat I) :
    Continuous (fun t : ℝ => (modularPhase A t : Mat I)) := by
  change Continuous (fun t : ℝ =>
    NormedSpace.exp (Complex.I • ((t / 2 : ℝ) • cfc Real.log A)))
  have hExp : Continuous (NormedSpace.exp : Mat I → Mat I) := by
    rw [← continuousOn_univ, ← Metric.eball_top_eq_univ (0 : Mat I),
      ← NormedSpace.expSeries_radius_eq_top ℂ (Mat I)]
    exact NormedSpace.continuousOn_exp
  apply hExp.comp
  fun_prop

theorem conjugationCLM_modularPhase_continuous (A : Mat I) :
    Continuous (fun t : ℝ => conjugationCLM (modularPhase A t : Mat I)) := by
  have hU := modularPhase_continuous A
  unfold conjugationCLM
  fun_prop

theorem conjugationCLM_modularPhase_star_continuous (A : Mat I) :
    Continuous (fun t : ℝ => conjugationCLM (modularPhase A t : Mat I)ᴴ) := by
  have hU := modularPhase_continuous A
  unfold conjugationCLM
  fun_prop

theorem completedRotatedPetzChannel_clm (N : Channel I O) (σ : Density I)
    (o₀ : I) (t : ℝ) :
    (completedRotatedPetzChannel N σ t o₀).map.toContinuousLinearMap =
      (conjugationCLM (modularPhase σ.val t : Mat I)).comp
        ((QuantumProver.ElegantJointMeasurement.CP.krausMap (petzKraus N σ)).toContinuousLinearMap.comp
          (conjugationCLM (modularPhase (N.map σ.val) t : Mat O)ᴴ)) +
      ((completedPetzChannel N σ o₀).map.toContinuousLinearMap -
        (QuantumProver.ElegantJointMeasurement.CP.krausMap (petzKraus N σ)).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro A
  change (completedRotatedPetzChannel N σ t o₀).map A = _
  rw [completedRotatedPetzChannel_action, rotatedPetz_action]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, conjugationCLM,
    ContinuousLinearMap.mulLeftRight_apply, Matrix.conjTranspose_conjTranspose]
  change _ = (modularPhase σ.val t : Mat I) *
      Geometry.krausAction (petzKraus N σ)
        ((modularPhase (N.map σ.val) t : Mat O)ᴴ * A *
          (modularPhase (N.map σ.val) t : Mat O)) *
        (modularPhase σ.val t : Mat I)ᴴ +
      ((completedPetzChannel N σ o₀).map A - Geometry.krausAction (petzKraus N σ) A)
  rw [completedPetzChannel_action]
  abel

theorem completedRotatedPetzChannel_clm_continuous
    (N : Channel I O) (σ : Density I) (o₀ : I) :
    Continuous (fun t : ℝ =>
      (completedRotatedPetzChannel N σ t o₀).map.toContinuousLinearMap) := by
  simp_rw [completedRotatedPetzChannel_clm]
  have hIn := conjugationCLM_modularPhase_continuous σ.val
  have hOut := conjugationCLM_modularPhase_star_continuous (N.map σ.val)
  exact (hIn.clm_comp (continuous_const.clm_comp hOut)).add continuous_const

def completedRotatedPetzChannel_normBudget (N : Channel I O)
    (σ : Density I) (o₀ : I) : ℝ :=
  ‖(QuantumProver.ElegantJointMeasurement.CP.krausMap (petzKraus N σ)).toContinuousLinearMap‖ +
    ‖(completedPetzChannel N σ o₀).map.toContinuousLinearMap -
      (QuantumProver.ElegantJointMeasurement.CP.krausMap (petzKraus N σ)).toContinuousLinearMap‖

theorem completedRotatedPetzChannel_clm_norm_le
    (N : Channel I O) (σ : Density I) (o₀ : I) (t : ℝ) :
    ‖(completedRotatedPetzChannel N σ t o₀).map.toContinuousLinearMap‖ ≤
      completedRotatedPetzChannel_normBudget N σ o₀ := by
  have hEq := congrArg (fun L : Mat O →L[ℂ] Mat I => ‖L‖)
    (completedRotatedPetzChannel_clm N σ o₀ t)
  have hBound := conjugationCLM_comp_add_norm_le (I := I) (O := O)
    (modularPhase σ.val t) (modularPhase (N.map σ.val) t)
    (QuantumProver.ElegantJointMeasurement.CP.krausMap (petzKraus N σ)).toContinuousLinearMap
    ((completedPetzChannel N σ o₀).map.toContinuousLinearMap -
      (QuantumProver.ElegantJointMeasurement.CP.krausMap (petzKraus N σ)).toContinuousLinearMap)
  exact le_of_eq_of_le hEq hBound

theorem completedRotatedPetzChannel_clm_integrable
    (N : Channel I O) (σ : Density I) (o₀ : I)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun t : ℝ =>
      (completedRotatedPetzChannel N σ t o₀).map.toContinuousLinearMap) μ := by
  apply Integrable.of_bound (f := fun t : ℝ =>
    (completedRotatedPetzChannel N σ t o₀).map.toContinuousLinearMap)
    (completedRotatedPetzChannel_clm_continuous N σ o₀).aestronglyMeasurable
    (completedRotatedPetzChannel_normBudget N σ o₀)
  exact Filter.Eventually.of_forall fun t => completedRotatedPetzChannel_clm_norm_le N σ o₀ t

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.ReferenceEntropy

open QuantumProver.SuperchannelDiscrimination.FlaggedStates

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem relativeEntropyBits_channel_dpi (N : Channel I O) (A B : Mat I)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    relativeEntropyBits (N.map A) (N.map B) ≤ relativeEntropyBits A B := by
  let K := QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map
  have hGram : QuantumProver.SuperchannelDiscrimination.KrausCompletion.krausGram K = 1 :=
    QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_gram
      N.map N.completelyPositive N.tracePreserving
  have hRec (X : Mat I) :
      QuantumProver.SuperchannelDiscrimination.KrausCompletion.krausAction K X = N.map X :=
    (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_reconstruct
      N.map N.completelyPositive X).symm
  have h := QuantumProver.SuperchannelDiscrimination.InputSupport.relativeEntropyBits_kraus_dpi
    K hGram hA hB
  rw [hRec A, hRec B] at h
  exact h

theorem binaryHolevoLoss_nonneg (A B : Density I) (N : Channel I O) :
    0 ≤ binaryHolevo A.val B.val - binaryHolevo (N.map A.val) (N.map B.val) := by
  let μ : Mat I := (1 / 2 : ℝ) • (A.val + B.val)
  have hμ : μ.PosSemidef := (A.property.1.add B.property.1).smul (by norm_num)
  have hDA := relativeEntropyBits_channel_dpi N A.val μ A.property.1 hμ
  have hDB := relativeEntropyBits_channel_dpi N B.val μ B.property.1 hμ
  have hAμ : HasSupportIn A.val μ :=
    hasSupportIn_equalPriorAverage_left A.property.1 B.property.1
  have hBμ : HasSupportIn B.val μ :=
    hasSupportIn_equalPriorAverage_right A.property.1 B.property.1
  obtain ⟨hNA, hNB⟩ := channel_outputs_supported_on_average A B N
  change HasSupportIn (N.map A.val) (N.map μ) at hNA
  change HasSupportIn (N.map B.val) (N.map μ) at hNB
  simp only [relativeEntropyBits, if_pos hAμ, if_pos hBμ,
    if_pos hNA, if_pos hNB] at hDA hDB
  have hRealA : finiteRelativeEntropyBits (N.map A.val) (N.map μ) ≤
      finiteRelativeEntropyBits A.val μ := by exact_mod_cast hDA
  have hRealB : finiteRelativeEntropyBits (N.map B.val) (N.map μ) ≤
      finiteRelativeEntropyBits B.val μ := by exact_mod_cast hDB
  rw [binaryHolevoLoss_eq_average_referenceGaps]
  change 0 ≤ (finiteRelativeEntropyBits A.val μ -
      finiteRelativeEntropyBits (N.map A.val) (N.map μ) +
      (finiteRelativeEntropyBits B.val μ -
        finiteRelativeEntropyBits (N.map B.val) (N.map μ))) / 2
  linarith

theorem binaryHolevo_channel_dpi (A B : Density I) (N : Channel I O) :
    binaryHolevo (N.map A.val) (N.map B.val) ≤ binaryHolevo A.val B.val :=
  sub_nonneg.mp (binaryHolevoLoss_nonneg A B N)

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.ReferenceEntropy

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

open MeasureTheory

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def averagedCompletedRotatedPetzChannel (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (N : Channel I O) (σ : Density I) (o₀ : I) : Channel O I :=
  ChannelAveraging.probabilityAverageChannel μ
    (fun t => (completedRotatedPetzChannel N σ t o₀).map.toContinuousLinearMap)
    (fun t => (completedRotatedPetzChannel N σ t o₀).completelyPositive)
    (fun t => (completedRotatedPetzChannel N σ t o₀).tracePreserving)
    (completedRotatedPetzChannel_clm_integrable N σ o₀ μ)

theorem averagedCompletedRotatedPetzChannel_apply
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (N : Channel I O)
    (σ : Density I) (o₀ : I) (A : Mat O) :
    (averagedCompletedRotatedPetzChannel μ N σ o₀).map A =
      ∫ t, (completedRotatedPetzChannel N σ t o₀).map A ∂μ := by
  unfold averagedCompletedRotatedPetzChannel
  rw [ChannelAveraging.probabilityAverageChannel_apply]
  rfl

theorem averagedCompletedRotatedPetzChannel_reference
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (N : Channel I O)
    (σ : Density I) (o₀ : I) :
    (averagedCompletedRotatedPetzChannel μ N σ o₀).map (N.map σ.val) = σ.val := by
  unfold averagedCompletedRotatedPetzChannel
  apply ChannelAveraging.probabilityAverageChannel_reference
  intro t
  exact completedRotatedPetzChannel_reference N σ t o₀

def sbtRecoveryChannel (N : Channel I O) (σ : Density I) (o₀ : I) : Channel O I :=
  averagedCompletedRotatedPetzChannel QuantumProver.SBTProbabilityWeight.beta0Probability N σ o₀

theorem sbtRecoveryChannel_reference (N : Channel I O) (σ : Density I) (o₀ : I) :
    (sbtRecoveryChannel N σ o₀).map (N.map σ.val) = σ.val :=
  averagedCompletedRotatedPetzChannel_reference _ N σ o₀

theorem sbtRecoveryChannel_apply (N : Channel I O) (σ : Density I)
    (o₀ : I) (A : Mat O) :
    (sbtRecoveryChannel N σ o₀).map A =
      ∫ t : ℝ, QuantumProver.SBTProbabilityWeight.beta0 t •
        (completedRotatedPetzChannel N σ t o₀).map A := by
  unfold sbtRecoveryChannel
  rw [averagedCompletedRotatedPetzChannel_apply,
    QuantumProver.SBTProbabilityWeight.integral_beta0Probability]

theorem sbtRecoveryChannel_supported_apply (N : Channel I O) (σ : Density I)
    (o₀ : I) (A : Mat O)
    (hSupport : QuantumProver.SuperchannelDiscrimination.TensorEntropy.supportProjection
      (N.map σ.val) * A = A) :
    (sbtRecoveryChannel N σ o₀).map A =
      ∫ t : ℝ, QuantumProver.SBTProbabilityWeight.beta0 t •
        Geometry.krausAction (rotatedPetzKraus N σ t) A := by
  have hz : (1 - QuantumProver.SuperchannelDiscrimination.TensorEntropy.supportProjection
      (N.map σ.val)) * A = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hSupport, sub_self]
  rw [sbtRecoveryChannel_apply]
  simp_rw [completedRotatedPetzChannel_action, hz]
  simp

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.MeasuredDivergence

variable {I O K : Type*} [Fintype I] [Fintype O] [Fintype K]
  [DecidableEq I] [DecidableEq O]

def channelPullbackPOVM (N : Channel I O) (M : POVM O K) : POVM I K where
  effect k := ∑ q : I × O,
    (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map q)ᴴ *
      M.effect k * QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map q
  positive k := Matrix.posSemidef_sum _ fun q _ =>
    (M.positive k).conjTranspose_mul_mul_same
      (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map q)
  normalized := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ q : I × O,
          (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map q)ᴴ *
            QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map q := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [← Matrix.sum_mul, ← Matrix.mul_sum, M.normalized, Matrix.mul_one]
      _ = 1 := QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_gram
        N.map N.completelyPositive N.tracePreserving

theorem channelPullbackPOVM_probability (N : Channel I O) (M : POVM O K)
    (A : Mat I) (k : K) :
    measurementProbability (channelPullbackPOVM N M) A k =
      measurementProbability M (N.map A) k := by
  unfold measurementProbability
  apply congrArg Complex.re
  change (A * ∑ q : I × O,
      (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map q)ᴴ *
        M.effect k * QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map q).trace = _
  rw [QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_reconstruct
    N.map N.completelyPositive A, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.trace_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro q hq
  let L := QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map q
  change (A * (Lᴴ * M.effect k * L)).trace = (L * A * Lᴴ * M.effect k).trace
  calc
    _ = (A * Lᴴ * M.effect k * L).trace := by simp only [Matrix.mul_assoc]
    _ = (L * (A * Lᴴ * M.effect k)).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem measuredRelativeEntropyBits_channel_dpi (N : Channel I O) (A B : Mat I) :
    measuredRelativeEntropyBits (N.map A) (N.map B) ≤ measuredRelativeEntropyBits A B := by
  unfold measuredRelativeEntropyBits
  apply sSup_le
  rintro z ⟨m, hm, M, rfl⟩
  apply le_sSup
  refine ⟨m, hm, channelPullbackPOVM N M, ?_⟩
  simp only [classicalRelativeEntropyBits, channelPullbackPOVM_probability]

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.MeasuredDivergence

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.MeasuredVariationalBridge

variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I]

def toSharedPOVM (M : POVM I K) : QuantumProver.MeasuredRelativeEntropyVariational.POVM I K where
  effect := M.effect
  positive := M.positive
  normalized := M.normalized

def fromSharedPOVM (M : QuantumProver.MeasuredRelativeEntropyVariational.POVM I K) : POVM I K where
  effect := M.effect
  positive := M.positive
  normalized := M.normalized

theorem classicalRelativeEntropyBits_eq_shared (p q : K → ℝ) :
    classicalRelativeEntropyBits p q =
      QuantumProver.MeasuredRelativeEntropyVariational.classicalRelativeEntropyBits p q := rfl

theorem measuredRelativeEntropyBits_eq_shared (A B : Mat I) :
    measuredRelativeEntropyBits A B =
      QuantumProver.MeasuredRelativeEntropyVariational.measuredRelativeEntropyBits A B := by
  apply congrArg sSup
  ext z
  constructor
  · rintro ⟨m, hm, M, hM⟩
    exact ⟨m, hm, toSharedPOVM M, hM⟩
  · rintro ⟨m, hm, M, hM⟩
    exact ⟨m, hm, fromSharedPOVM M, hM⟩

theorem measuredRelativeEntropyBits_variational (rho sigma : Mat I)
    (hRho : IsDensity rho) (hSigma : sigma.PosSemidef) :
    measuredRelativeEntropyBits rho sigma =
      sSup {z : EReal | ∃ Omega : Mat I, Omega.PosDef ∧
        z = (((rho * cfc Real.log Omega).trace.re + 1 -
          (sigma * Omega).trace.re) / Real.log 2 : ℝ)} := by
  rw [measuredRelativeEntropyBits_eq_shared]
  exact QuantumProver.MeasuredRelativeEntropyVariational.measuredRelativeEntropyBits_variational
    rho sigma hRho hSigma

open Filter Set Topology

theorem lowerSemicontinuousOn_measuredRelativeEntropyBits :
    LowerSemicontinuousOn (fun p : Mat I × Mat I =>
      measuredRelativeEntropyBits p.1 p.2) {p | IsDensity p.1 ∧ p.2.PosSemidef} := by
  simp_rw [measuredRelativeEntropyBits_eq_shared]
  exact QuantumProver.MeasuredRelativeEntropyContinuity.lowerSemicontinuousOn_measuredRelativeEntropyBits

theorem measuredRelativeEntropyBits_le_liminf
    {α : Type*} {l : Filter α} [NeBot l]
    {rho sigma : Mat I} {rhoSeq sigmaSeq : α → Mat I}
    (hRho : IsDensity rho) (hSigma : sigma.PosSemidef)
    (hRhoSeq : ∀ a, IsDensity (rhoSeq a))
    (hSigmaSeq : ∀ a, (sigmaSeq a).PosSemidef)
    (hRhoLim : Tendsto rhoSeq l (𝓝 rho))
    (hSigmaLim : Tendsto sigmaSeq l (𝓝 sigma)) :
    measuredRelativeEntropyBits rho sigma ≤
      Filter.liminf (fun a => measuredRelativeEntropyBits (rhoSeq a) (sigmaSeq a)) l := by
  simp_rw [measuredRelativeEntropyBits_eq_shared]
  exact QuantumProver.MeasuredRelativeEntropyContinuity.measuredRelativeEntropyBits_le_liminf
    hRho hSigma hRhoSeq hSigmaSeq hRhoLim hSigmaLim

theorem measuredRelativeEntropyBits_le_liminf_atTop
    {rho sigma : Mat I} {rhoSeq sigmaSeq : ℕ → Mat I}
    (hRho : IsDensity rho) (hSigma : sigma.PosSemidef)
    (hRhoSeq : ∀ n, IsDensity (rhoSeq n))
    (hSigmaSeq : ∀ n, (sigmaSeq n).PosSemidef)
    (hRhoLim : Tendsto rhoSeq atTop (𝓝 rho))
    (hSigmaLim : Tendsto sigmaSeq atTop (𝓝 sigma)) :
    measuredRelativeEntropyBits rho sigma ≤
      Filter.liminf (fun n => measuredRelativeEntropyBits (rhoSeq n) (sigmaSeq n)) atTop :=
  measuredRelativeEntropyBits_le_liminf hRho hSigma hRhoSeq hSigmaSeq hRhoLim hSigmaLim

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.MeasuredVariationalBridge

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.QuantumVariational

open QuantumProver.SuperchannelDiscrimination.FlaggedStates

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem hermitian_exp_posDef (H : Mat I) (hH : H.IsHermitian) :
    (NormedSpace.exp H).PosDef := by
  have hp : (NormedSpace.exp H).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hH.isSelfAdjoint.exp_nonneg
  exact hp.posDef_iff_isUnit.mpr (Matrix.isUnit_exp H)

theorem finiteRelativeEntropyBits_ge_exponential_test
    (A : Density I) (B H : Mat I) (hH : H.IsHermitian) :
    ((A.val * H).trace.re + 1 -
      (NormedSpace.exp (cfc Real.log B + H)).trace.re) / Real.log 2 ≤
      finiteRelativeEntropyBits A.val B := by
  let K : Mat I := cfc Real.log B + H
  have hK : K.IsHermitian := (cfc_predicate Real.log B).add hH
  have hExp : (NormedSpace.exp K).PosDef := hermitian_exp_posDef K hK
  have hSupp : HasSupportIn A.val (NormedSpace.exp K) :=
    hasSupportIn_of_posDef A.val hExp
  have h := QuantumProver.SuperchannelDiscrimination.Klein.klein_trace_of_support
    A.property.1 hExp.posSemidef hSupp
  have hLog : cfc Real.log (NormedSpace.exp K) = K :=
    CFC.log_exp K hK.isSelfAdjoint
  rw [hLog, A.property.2, Complex.one_re] at h
  have hProduct : (A.val * K).trace.re =
      (A.val * cfc Real.log B).trace.re + (A.val * H).trace.re := by
    simp only [K, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  rw [hProduct] at h
  rw [finiteRelativeEntropyBits_eq_spectral A.property.1.isHermitian]
  exact div_le_div_of_nonneg_right (by linarith) (le_of_lt log_two_pos)

theorem relativeEntropyBits_ge_exponential_test
    (A : Density I) (B H : Mat I) (hH : H.IsHermitian)
    (hSupp : HasSupportIn A.val B) :
    (((A.val * H).trace.re + 1 -
      (NormedSpace.exp (cfc Real.log B + H)).trace.re) / Real.log 2 : ℝ) ≤
      relativeEntropyBits A.val B := by
  simp only [relativeEntropyBits, if_pos hSupp]
  exact_mod_cast finiteRelativeEntropyBits_ge_exponential_test A B H hH

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.QuantumVariational

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.MeasuredDivergence

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem measuredRelativeEntropyBits_ge_bures_of_posDef
    (A B : Density I) (hA : A.val.PosDef) :
    ((2 * (1 - rootFidelity A.val B.val) / Real.log 2 : ℝ) : EReal) ≤
      measuredRelativeEntropyBits A.val B.val := by
  letI : Nonempty I := density_index_nonempty A
  exact measuredRelativeEntropyBits_ge_bures_of_attaining_measurement A B
    (FCColumns.fcPOVM A B) (FCColumns.fc_measurement_affinity_rootFidelity A B hA)

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.MeasuredDivergence

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PartialTraceEntropy

open QuantumProver.SuperchannelDiscrimination.FlaggedStates
open scoped Kronecker

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

def liftLeft (H : Mat I) : Mat (I × E) := H ⊗ₖ (1 : Mat E)

theorem liftLeft_isHermitian (H : Mat I) (hH : H.IsHermitian) :
    (liftLeft (E := E) H).IsHermitian := by
  change (H ⊗ₖ (1 : Mat E))ᴴ = H ⊗ₖ (1 : Mat E)
  rw [Matrix.conjTranspose_kronecker, hH, Matrix.conjTranspose_one]

theorem trace_mul_liftLeft (A : Mat (I × E)) (H : Mat I) :
    (A * liftLeft H).trace = (partialTraceRight A * H).trace :=
  QuantumProver.QuantumEntropy.partialTrace_right_mul_trace A H

def partialTraceLogReference (A B : Mat (I × E)) : Mat (I × E) :=
  cfc Real.log B + liftLeft (cfc Real.log (partialTraceRight A)) -
    liftLeft (cfc Real.log (partialTraceRight B))

theorem partialTraceLogReference_isHermitian (A B : Mat (I × E)) :
    (partialTraceLogReference A B).IsHermitian :=
  ((cfc_predicate Real.log B).add
    (liftLeft_isHermitian _ (cfc_predicate Real.log (partialTraceRight A)))).sub
    (liftLeft_isHermitian _ (cfc_predicate Real.log (partialTraceRight B)))

theorem finiteRelativeEntropyBits_partialTraceGap_eq (A B : Mat (I × E)) :
    finiteRelativeEntropyBits A B -
      finiteRelativeEntropyBits (partialTraceRight A) (partialTraceRight B) =
    finiteRelativeEntropyBits A (NormedSpace.exp (partialTraceLogReference A B)) := by
  have hLog : cfc Real.log (NormedSpace.exp (partialTraceLogReference A B)) =
      partialTraceLogReference A B :=
    CFC.log_exp _ (partialTraceLogReference_isHermitian A B).isSelfAdjoint
  unfold finiteRelativeEntropyBits
  rw [hLog]
  simp only [partialTraceLogReference, Matrix.mul_sub, Matrix.mul_add,
    Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re,
    trace_mul_liftLeft]
  ring

theorem finiteRelativeEntropyBits_partialTraceGap_ge_exponential_test
    (A : Density (I × E)) (B H : Mat (I × E)) (hH : H.IsHermitian) :
    ((A.val * H).trace.re + 1 -
      (NormedSpace.exp (partialTraceLogReference A.val B + H)).trace.re) / Real.log 2 ≤
      finiteRelativeEntropyBits A.val B -
        finiteRelativeEntropyBits (partialTraceRight A.val) (partialTraceRight B) := by
  have h := QuantumVariational.finiteRelativeEntropyBits_ge_exponential_test A
    (NormedSpace.exp (partialTraceLogReference A.val B)) H hH
  have hLog : cfc Real.log (NormedSpace.exp (partialTraceLogReference A.val B)) =
      partialTraceLogReference A.val B :=
    CFC.log_exp _ (partialTraceLogReference_isHermitian A.val B).isSelfAdjoint
  rw [hLog, ← finiteRelativeEntropyBits_partialTraceGap_eq A.val B] at h
  exact h

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PartialTraceEntropy

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.SingularReference

open Filter Set Topology

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

def identityRegularizationDenom (I : Type*) [Fintype I] (δ : ℝ) : ℝ :=
  1 + δ * (Fintype.card I : ℝ)

def identityRegularizedMatrix (A : Mat I) (δ : ℝ) : Mat I :=
  (identityRegularizationDenom I δ)⁻¹ • (A + δ • (1 : Mat I))

theorem identityRegularizationDenom_pos (δ : ℝ) (hδ : 0 ≤ δ) :
    0 < identityRegularizationDenom I δ := by
  unfold identityRegularizationDenom
  positivity

theorem identityRegularizedMatrix_posSemidef (A : Mat I) (hA : A.PosSemidef)
    (δ : ℝ) (hδ : 0 ≤ δ) : (identityRegularizedMatrix A δ).PosSemidef :=
  (hA.add (Matrix.PosSemidef.one.smul hδ)).smul
    (inv_nonneg.mpr (identityRegularizationDenom_pos δ hδ).le)

theorem identityRegularizedMatrix_posDef (A : Mat I) (hA : A.PosSemidef)
    (δ : ℝ) (hδ : 0 < δ) : (identityRegularizedMatrix A δ).PosDef :=
  (Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hδ)).smul
    (inv_pos.mpr (identityRegularizationDenom_pos δ hδ.le))

theorem identityRegularizedMatrix_isDensity (A : Density I)
    (δ : ℝ) (hδ : 0 ≤ δ) : IsDensity (identityRegularizedMatrix A.val δ) := by
  refine ⟨identityRegularizedMatrix_posSemidef A.val A.property.1 δ hδ, ?_⟩
  have hD : identityRegularizationDenom I δ ≠ 0 :=
    (identityRegularizationDenom_pos δ hδ).ne'
  have hInner : (A.val + δ • (1 : Mat I)).trace =
      (identityRegularizationDenom I δ : ℂ) := by
    simp only [Matrix.trace_add, Matrix.trace_smul, A.property.2, Matrix.trace_one,
      Complex.real_smul, identityRegularizationDenom, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_one]
  rw [identityRegularizedMatrix, Matrix.trace_smul, hInner]
  simp only [Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hD,
    Complex.ofReal_one]

def identityRegularizedDensity (A : Density I) (δ : ℝ) (hδ : 0 ≤ δ) : Density I :=
  ⟨identityRegularizedMatrix A.val δ, identityRegularizedMatrix_isDensity A δ hδ⟩

theorem identityRegularizedMatrix_tendsto (A : Mat I) :
    Tendsto (identityRegularizedMatrix A) (𝓝 (0 : ℝ)) (𝓝 A) := by
  have hD : ContinuousAt (fun δ : ℝ => 1 + δ * (Fintype.card I : ℝ)) (0 : ℝ) := by
    fun_prop
  have hInv := hD.inv₀ (by simp : (1 : ℝ) + 0 * (Fintype.card I : ℝ) ≠ 0)
  have hInner : ContinuousAt (fun δ : ℝ => A + δ • (1 : Mat I)) (0 : ℝ) := by
    fun_prop
  have h : ContinuousAt (fun δ : ℝ => (1 + δ * (Fintype.card I : ℝ))⁻¹ •
      (A + δ • (1 : Mat I))) (0 : ℝ) := hInv.smul hInner
  change Tendsto (fun δ : ℝ => (1 + δ * (Fintype.card I : ℝ))⁻¹ •
    (A + δ • (1 : Mat I))) (𝓝 (0 : ℝ)) (𝓝 A)
  simpa only [zero_mul, add_zero, inv_one, zero_smul, one_smul] using h.tendsto

theorem identityRegularizedMatrix_tendsto_right (A : Mat I) :
    Tendsto (identityRegularizedMatrix A) (𝓝[>] (0 : ℝ)) (𝓝 A) :=
  (identityRegularizedMatrix_tendsto A).mono_left nhdsWithin_le_nhds

theorem partialTraceRight_real_smul (r : ℝ) (A : Mat (I × E)) :
    partialTraceRight (r • A) = r • partialTraceRight A := by
  ext i j
  simp only [partialTraceRight, Matrix.smul_apply, Finset.smul_sum]

theorem partialTraceRight_add (A B : Mat (I × E)) :
    partialTraceRight (A + B) = partialTraceRight A + partialTraceRight B :=
  partialTraceRightLM.map_add A B

theorem partialTraceRight_one :
    partialTraceRight (1 : Mat (I × E)) = (Fintype.card E : ℝ) • (1 : Mat I) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [partialTraceRight, Matrix.one_apply, Complex.real_smul]
  · simp [partialTraceRight, Matrix.one_apply, h, Complex.real_smul]

theorem partialTraceRight_identityRegularizedMatrix (A : Mat (I × E)) (δ : ℝ) :
    partialTraceRight (identityRegularizedMatrix A δ) =
      (identityRegularizationDenom (I × E) δ)⁻¹ •
        (partialTraceRight A + (δ * (Fintype.card E : ℝ)) • (1 : Mat I)) := by
  rw [identityRegularizedMatrix, partialTraceRight_real_smul,
    partialTraceRight_add, partialTraceRight_real_smul, partialTraceRight_one, smul_smul]

theorem partialTraceRight_identityRegularizedMatrix_posDef [Nonempty E]
    (A : Mat (I × E)) (hA : A.PosSemidef) (δ : ℝ) (hδ : 0 < δ) :
    (partialTraceRight (identityRegularizedMatrix A δ)).PosDef := by
  rw [partialTraceRight_identityRegularizedMatrix]
  have hMass : 0 < δ * (Fintype.card E : ℝ) :=
    mul_pos hδ (Nat.cast_pos.mpr Fintype.card_pos)
  exact (Matrix.PosDef.posSemidef_add (partialTraceRight_posSemidef hA)
    (Matrix.PosDef.one.smul hMass)).smul
    (inv_pos.mpr (identityRegularizationDenom_pos δ hδ.le))

theorem commute_smul_add_identity (A : Mat I) (r s : ℝ) :
    Commute A (r • (A + s • (1 : Mat I))) := by
  change A * (r • (A + s • (1 : Mat I))) = (r • (A + s • (1 : Mat I))) * A
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.one_mul]

theorem identityRegularizedMatrix_commutes (A : Mat I) (δ : ℝ) :
    Commute A (identityRegularizedMatrix A δ) :=
  commute_smul_add_identity A _ _

theorem partialTraceRight_identityRegularizedMatrix_commutes
    (A : Mat (I × E)) (δ : ℝ) :
    Commute (partialTraceRight A) (partialTraceRight (identityRegularizedMatrix A δ)) := by
  rw [partialTraceRight_identityRegularizedMatrix]
  exact commute_smul_add_identity _ _ _

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.SingularReference

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

open MeasureTheory

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem completedRotatedPetzChannel_apply_norm_le_one
    (N : Channel I O) (σ : Density I) (o₀ : I) (A : Density O) (t : ℝ) :
    ‖(completedRotatedPetzChannel N σ t o₀).map A.val‖ ≤ 1 :=
  QuantumProver.ConditionalEntropy.ProbabilityMixtures.isDensity_norm_le_one
    ((completedRotatedPetzChannel N σ t o₀).isDensity A.property)

theorem completedRotatedPetzChannel_apply_continuous
    (N : Channel I O) (σ : Density I) (o₀ : I) (A : Mat O) :
    Continuous (fun t : ℝ => (completedRotatedPetzChannel N σ t o₀).map A) := by
  change Continuous (fun t : ℝ =>
    (completedRotatedPetzChannel N σ t o₀).map.toContinuousLinearMap A)
  exact (completedRotatedPetzChannel_clm_continuous N σ o₀).clm_apply continuous_const

def identityRegularizedRotatedRecoveryFamily (N : Channel I O) (σ : Density I)
    (o₀ : I) (δ t : ℝ) : Channel O I :=
  completedRotatedPetzChannel N
    (SingularReference.identityRegularizedDensity σ (max δ 0) (le_max_right δ 0)) t o₀

theorem identityRegularizedRotatedRecoveryFamily_reference
    (N : Channel I O) (σ : Density I) (o₀ : I) (δ t : ℝ) :
    (identityRegularizedRotatedRecoveryFamily N σ o₀ δ t).map
      (N.map (SingularReference.identityRegularizedMatrix σ.val (max δ 0))) =
        SingularReference.identityRegularizedMatrix σ.val (max δ 0) :=
  completedRotatedPetzChannel_reference N _ t o₀

theorem identityRegularizedRotatedRecoveryFamily_apply_norm_le_one
    (N : Channel I O) (σ : Density I) (o₀ : I) (A : Density O) (δ t : ℝ) :
    ‖(identityRegularizedRotatedRecoveryFamily N σ o₀ δ t).map A.val‖ ≤ 1 :=
  completedRotatedPetzChannel_apply_norm_le_one N _ o₀ A t

theorem identityRegularizedRotatedRecoveryFamily_apply_continuous
    (N : Channel I O) (σ : Density I) (o₀ : I) (A : Mat O) (δ : ℝ) :
    Continuous (fun t : ℝ =>
      (identityRegularizedRotatedRecoveryFamily N σ o₀ δ t).map A) :=
  completedRotatedPetzChannel_apply_continuous N _ o₀ A

theorem identityRegularizedRotatedRecoveryFamily_apply_integrable
    (N : Channel I O) (σ : Density I) (o₀ : I) (A : Density O) (δ : ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun t : ℝ =>
      (identityRegularizedRotatedRecoveryFamily N σ o₀ δ t).map A.val) μ := by
  apply QuantumProver.ConditionalEntropy.ProbabilityMixtures.integrable_densityFamily μ
    (fun t : ℝ => (identityRegularizedRotatedRecoveryFamily N σ o₀ δ t).map A.val)
    (identityRegularizedRotatedRecoveryFamily_apply_continuous N σ o₀ A.val δ).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t =>
    (identityRegularizedRotatedRecoveryFamily N σ o₀ δ t).isDensity A.property

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

open scoped Kronecker

open QuantumProver.SuperchannelDiscrimination.TensorEntropy

variable {I O E : Type*} [Fintype I] [Fintype O] [Fintype E]
  [DecidableEq I] [DecidableEq O] [DecidableEq E]

def canonicalAdjointMatrix (N : Channel I O) (B : Mat O) : Mat I :=
  ∑ q : I × O, (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map q)ᴴ *
    B * QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map q

theorem canonicalAdjointMatrix_trace_pairing (N : Channel I O)
    (B : Mat O) (A : Mat I) :
    (canonicalAdjointMatrix N B * A).trace = (N.map A * B).trace := by
  let K := QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map
  calc
    _ = ∑ q : I × O, (K q * A * (K q)ᴴ * B).trace := by
      simp only [canonicalAdjointMatrix, Finset.sum_mul, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro q hq
      change (((K q)ᴴ * B * K q) * A).trace = _
      calc
        _ = (((K q)ᴴ * B) * (K q * A)).trace := by simp only [Matrix.mul_assoc]
        _ = ((K q * A) * ((K q)ᴴ * B)).trace := Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.mul_assoc]
    _ = ((∑ q : I × O, K q * A * (K q)ᴴ) * B).trace := by
      rw [Finset.sum_mul, Matrix.trace_sum]
    _ = _ := by
      rw [← QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_reconstruct
        N.map N.completelyPositive A]

theorem canonicalAdjointMatrix_partialTrace (B : Mat I) :
    canonicalAdjointMatrix (partialTraceRightChannel (I := I) (E := E)) B =
      B ⊗ₖ (1 : Mat E) := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro A
  rw [canonicalAdjointMatrix_trace_pairing]
  change (partialTraceRight A * B).trace = ((B ⊗ₖ (1 : Mat E)) * A).trace
  rw [Matrix.trace_mul_comm (B ⊗ₖ (1 : Mat E)) A]
  exact (QuantumProver.QuantumEntropy.partialTrace_right_mul_trace A B).symm

theorem petz_action_adjoint (N : Channel I O) (σ : Density I) (A : Mat O) :
    Geometry.krausAction (petzKraus N σ) A =
      CFC.sqrt σ.val * canonicalAdjointMatrix N
        (inverseRoot (N.map σ.val) * A * inverseRoot (N.map σ.val)) *
      CFC.sqrt σ.val := by
  have hS : (CFC.sqrt σ.val)ᴴ = CFC.sqrt σ.val :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ.val)).isHermitian.eq
  simp only [Geometry.krausAction, canonicalAdjointMatrix, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [petzKraus, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hS, (inverseRoot_isHermitian _).eq, Matrix.mul_assoc]

def partialTraceRotatedPetzMatrix (σ : Density (I × E)) (A : Mat I) (t : ℝ) :
    Mat (I × E) :=
  (modularPhase σ.val t : Mat (I × E)) * CFC.sqrt σ.val *
    ((inverseRoot (partialTraceRight σ.val) *
      (modularPhase (partialTraceRight σ.val) t : Mat I)ᴴ * A *
      (modularPhase (partialTraceRight σ.val) t : Mat I) *
      inverseRoot (partialTraceRight σ.val)) ⊗ₖ (1 : Mat E)) *
    CFC.sqrt σ.val * (modularPhase σ.val t : Mat (I × E))ᴴ

theorem partialTrace_rotatedPetz_action (σ : Density (I × E)) (A : Mat I) (t : ℝ) :
    Geometry.krausAction
      (rotatedPetzKraus (partialTraceRightChannel (I := I) (E := E)) σ t) A =
        partialTraceRotatedPetzMatrix σ A t := by
  rw [rotatedPetz_action, petz_action_adjoint, canonicalAdjointMatrix_partialTrace]
  simp only [partialTraceRightChannel, partialTraceRightLM, LinearMap.coe_mk,
    AddHom.coe_mk, partialTraceRotatedPetzMatrix, Matrix.mul_assoc]

theorem completedPartialTraceRotatedPetzChannel_action (σ : Density (I × E))
    (A : Mat I) (t : ℝ) (o₀ : I × E) :
    (completedRotatedPetzChannel (partialTraceRightChannel (I := I) (E := E)) σ t o₀).map A =
      partialTraceRotatedPetzMatrix σ A t + Matrix.single o₀ o₀
        (((1 - supportProjection (partialTraceRight σ.val)) * A).trace) := by
  rw [completedRotatedPetzChannel_action, partialTrace_rotatedPetz_action]
  rfl

theorem completedPartialTraceRotatedPetzChannel_on_supported (σ : Density (I × E))
    (A : Mat I) (t : ℝ) (o₀ : I × E)
    (hA : supportProjection (partialTraceRight σ.val) * A = A) :
    (completedRotatedPetzChannel (partialTraceRightChannel (I := I) (E := E)) σ t o₀).map A =
      partialTraceRotatedPetzMatrix σ A t := by
  rw [completedPartialTraceRotatedPetzChannel_action]
  have hz : (1 - supportProjection (partialTraceRight σ.val)) * A = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hA, sub_self]
  simp [hz]

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

open scoped Kronecker
open QuantumProver.SuperchannelDiscrimination.TensorEntropy

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

theorem modularPhase_conjTranspose (A : Mat I) (t : ℝ) :
    (modularPhase A t : Mat I)ᴴ = (modularPhase A (-t) : Mat I) := by
  have hLog : (cfc Real.log A).IsHermitian := cfc_predicate _ _
  change (NormedSpace.exp (Complex.I • ((t / 2 : ℝ) • cfc Real.log A)))ᴴ =
    NormedSpace.exp (Complex.I • (((-t) / 2 : ℝ) • cfc Real.log A))
  rw [← Matrix.exp_conjTranspose]
  apply congrArg NormedSpace.exp
  simp [Matrix.conjTranspose_smul, hLog.eq, neg_div, neg_smul]

theorem compressed_inverse_sandwich (R W P A : Mat I)
    (hR : Rᴴ = R) (hP : Pᴴ = P) (hPA : P * A = A) (hAP : A * P = A) :
    (R * Wᴴ * P) * A * (R * Wᴴ * P)ᴴ = R * Wᴴ * A * W * R := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hR, hP]
  calc
    _ = R * Wᴴ * (P * A * P) * W * R := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hPA, hAP]

def modularRootMatrix (A : Mat I) (t : ℝ) : Mat I :=
  (modularPhase A t : Mat I) * CFC.sqrt A

def compressedInversePhase (A B : Mat I) (t : ℝ) : Mat I :=
  inverseRoot B * (modularPhase B t : Mat I)ᴴ * supportProjection A

theorem partialTraceRotatedPetzMatrix_eq_compressed
    (σ : Density (I × E)) (A P : Mat I) (t : ℝ)
    (hP : Pᴴ = P) (hPA : P * A = A) (hAP : A * P = A) :
    partialTraceRotatedPetzMatrix σ A t =
      modularRootMatrix σ.val t *
        (((inverseRoot (partialTraceRight σ.val) *
          (modularPhase (partialTraceRight σ.val) t : Mat I)ᴴ * P) * A *
          (inverseRoot (partialTraceRight σ.val) *
            (modularPhase (partialTraceRight σ.val) t : Mat I)ᴴ * P)ᴴ) ⊗ₖ (1 : Mat E)) *
        (modularRootMatrix σ.val t)ᴴ := by
  have hS : (CFC.sqrt σ.val)ᴴ = CFC.sqrt σ.val :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg σ.val)).isHermitian.eq
  rw [compressed_inverse_sandwich _ _ _ _ (inverseRoot_isHermitian _).eq hP hPA hAP]
  simp only [partialTraceRotatedPetzMatrix, modularRootMatrix,
    Matrix.conjTranspose_mul, hS, Matrix.mul_assoc]

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

open Filter Set MeasureTheory
open scoped Topology Kronecker
open QuantumProver.SuperchannelDiscrimination.TensorEntropy
open QuantumProver.SuperchannelDiscrimination.OutputSupport

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

theorem identityRegularized_modularRoot_tendsto (A : Mat I) (hA : A.PosSemidef) (t : ℝ) :
    Tendsto (fun δ : ℝ => modularRootMatrix
      (SingularReference.identityRegularizedMatrix A (max δ 0)) t) (𝓝[>] 0)
      (𝓝 (modularRootMatrix A t)) := by
  have hRaw : Tendsto (fun δ : ℝ => modularRootMatrix
      (SingularReference.identityRegularizedMatrix A δ) t) (𝓝[>] 0)
      (𝓝 (modularRootMatrix A t)) := by
    simpa only [modularRootMatrix, SingularReference.identityRegularizedMatrix,
      SingularReference.identityRegularizationDenom, SBTModularLimits.normalizedIdentity,
      mul_one] using SBTModularLimits.modularRoot_normalizedIdentity_tendsto hA
        (Fintype.card I : ℝ) 1 t (Nat.cast_nonneg _) (by norm_num)
  apply hRaw.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [max_eq_left hδ.le]

theorem partialTrace_identityRegularized_compressedInverse_tendsto
    (A : Mat (I × E)) (hA : A.PosSemidef) (t : ℝ) :
    Tendsto (fun δ : ℝ => compressedInversePhase (partialTraceRight A)
      (partialTraceRight (SingularReference.identityRegularizedMatrix A (max δ 0))) t)
      (𝓝[>] 0) (𝓝 (compressedInversePhase (partialTraceRight A) (partialTraceRight A) t)) := by
  have hRaw : Tendsto (fun δ : ℝ => compressedInversePhase (partialTraceRight A)
      (partialTraceRight (SingularReference.identityRegularizedMatrix A δ)) t)
      (𝓝[>] 0) (𝓝 (compressedInversePhase (partialTraceRight A) (partialTraceRight A) t)) := by
    simpa only [compressedInversePhase, modularPhase_conjTranspose,
      SingularReference.partialTraceRight_identityRegularizedMatrix,
      SingularReference.identityRegularizationDenom, SBTModularLimits.normalizedIdentity]
      using SBTModularLimits.compressedInverse_normalizedIdentity_tendsto
        (partialTraceRight_posSemidef hA) (Fintype.card (I × E) : ℝ)
        (Fintype.card E : ℝ) (-t)
  apply hRaw.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [max_eq_left hδ.le]

theorem tensorLeft_continuous :
    Continuous (fun A : Mat I => A ⊗ₖ (1 : Mat E)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun A : Mat I => A i.1 j.1 * (1 : Mat E) i.2 j.2)
  fun_prop

theorem identityRegularizedPartialTraceRecovery_apply_tendsto [Nonempty E]
    (σ : Density (I × E)) (A : Density I) (t : ℝ) (o₀ : I × E)
    (hPA : supportProjection (partialTraceRight σ.val) * A.val = A.val) :
    Tendsto (fun δ : ℝ =>
      (identityRegularizedRotatedRecoveryFamily
        (partialTraceRightChannel (I := I) (E := E)) σ o₀ δ t).map A.val)
      (𝓝[>] 0)
      (𝓝 ((completedRotatedPetzChannel
        (partialTraceRightChannel (I := I) (E := E)) σ t o₀).map A.val)) := by
  let σδ := fun δ : ℝ => SingularReference.identityRegularizedDensity σ
    (max δ 0) (le_max_right δ 0)
  let P : Mat I := supportProjection (partialTraceRight σ.val)
  have hP : Pᴴ = P :=
    (supportProjection_isHermitian (partialTraceRight_posSemidef σ.property.1).isHermitian).eq
  have hAP : A.val * P = A.val := by
    have hPA' : P * A.val = A.val := hPA
    have h := congrArg Matrix.conjTranspose hPA'
    simpa only [Matrix.conjTranspose_mul, A.property.1.isHermitian.eq, hP] using h
  let S := fun δ : ℝ => modularRootMatrix (σδ δ).val t
  let L := fun δ : ℝ => compressedInversePhase (partialTraceRight σ.val)
    (partialTraceRight (σδ δ).val) t
  let S₀ := modularRootMatrix σ.val t
  let L₀ := compressedInversePhase (partialTraceRight σ.val) (partialTraceRight σ.val) t
  have hS : Tendsto S (𝓝[>] 0) (𝓝 S₀) :=
    identityRegularized_modularRoot_tendsto σ.val σ.property.1 t
  have hL : Tendsto L (𝓝[>] 0) (𝓝 L₀) :=
    partialTrace_identityRegularized_compressedInverse_tendsto σ.val σ.property.1 t
  have hMiddle : Tendsto (fun δ : ℝ => L δ * A.val * (L δ)ᴴ) (𝓝[>] 0)
      (𝓝 (L₀ * A.val * L₀ᴴ)) := (hL.mul tendsto_const_nhds).mul hL.star
  have hLift : Tendsto (fun δ : ℝ => (L δ * A.val * (L δ)ᴴ) ⊗ₖ (1 : Mat E))
      (𝓝[>] 0) (𝓝 ((L₀ * A.val * L₀ᴴ) ⊗ₖ (1 : Mat E))) :=
    (tensorLeft_continuous.tendsto _).comp hMiddle
  have hTotal := (hS.mul hLift).mul hS.star
  change Tendsto (fun δ : ℝ =>
    S δ * ((L δ * A.val * (L δ)ᴴ) ⊗ₖ (1 : Mat E)) * (S δ)ᴴ) (𝓝[>] 0)
    (𝓝 (S₀ * ((L₀ * A.val * L₀ᴴ) ⊗ₖ (1 : Mat E)) * S₀ᴴ)) at hTotal
  have hAt : S₀ * ((L₀ * A.val * L₀ᴴ) ⊗ₖ (1 : Mat E)) * S₀ᴴ =
      (completedRotatedPetzChannel (partialTraceRightChannel (I := I) (E := E)) σ t o₀).map A.val := by
    rw [completedPartialTraceRotatedPetzChannel_on_supported σ A.val t o₀ hPA]
    exact (partialTraceRotatedPetzMatrix_eq_compressed σ A.val P t hP hPA hAP).symm
  rw [hAt] at hTotal
  apply hTotal.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hτδ : (partialTraceRight (σδ δ).val).PosDef := by
    change (partialTraceRight
      (SingularReference.identityRegularizedMatrix σ.val (max δ 0))).PosDef
    rw [max_eq_left hδ.le]
    exact SingularReference.partialTraceRight_identityRegularizedMatrix_posDef
      σ.val σ.property.1 δ hδ
  have hSupport : supportProjection (partialTraceRight (σδ δ).val) * A.val = A.val := by
    rw [QuantumProver.SuperchannelDiscrimination.ModularMatrix.supportProjection_posDef hτδ,
      Matrix.one_mul]
  change S δ * ((L δ * A.val * (L δ)ᴴ) ⊗ₖ (1 : Mat E)) * (S δ)ᴴ =
    (completedRotatedPetzChannel (partialTraceRightChannel (I := I) (E := E))
      (σδ δ) t o₀).map A.val
  rw [completedPartialTraceRotatedPetzChannel_on_supported (σδ δ) A.val t o₀ hSupport]
  exact (partialTraceRotatedPetzMatrix_eq_compressed (σδ δ) A.val P t hP hPA hAP).symm

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

open Filter Set MeasureTheory
open scoped Topology
open QuantumProver.SuperchannelDiscrimination.TensorEntropy

variable {I O E : Type*} [Fintype I] [Fintype O] [Fintype E]
  [DecidableEq I] [DecidableEq O] [DecidableEq E]

theorem identityRegularizedPartialTraceRecovery_average_tendsto [Nonempty E]
    (σ : Density (I × E)) (A : Density I) (o₀ : I × E)
    (hPA : supportProjection (partialTraceRight σ.val) * A.val = A.val) :
    Tendsto (fun δ : ℝ =>
      (sbtRecoveryChannel (partialTraceRightChannel (I := I) (E := E))
        (SingularReference.identityRegularizedDensity σ (max δ 0) (le_max_right δ 0))
        o₀).map A.val) (𝓝[>] 0)
      (𝓝 ((sbtRecoveryChannel (partialTraceRightChannel (I := I) (E := E)) σ o₀).map A.val)) := by
  have h := QuantumProver.SBTProbabilityLimits.tendsto_beta0Probability_integral_density_of_continuous
    (F := fun δ t => (identityRegularizedRotatedRecoveryFamily
      (partialTraceRightChannel (I := I) (E := E)) σ o₀ δ t).map A.val)
    (G := fun t => (completedRotatedPetzChannel
      (partialTraceRightChannel (I := I) (E := E)) σ t o₀).map A.val)
    (fun δ _ => identityRegularizedRotatedRecoveryFamily_apply_continuous _ σ o₀ A.val δ)
    (fun δ _ t => (identityRegularizedRotatedRecoveryFamily _ σ o₀ δ t).isDensity A.property)
    (Filter.Eventually.of_forall fun t =>
      identityRegularizedPartialTraceRecovery_apply_tendsto σ A t o₀ hPA)
  simpa only [sbtRecoveryChannel, averagedCompletedRotatedPetzChannel_apply,
    identityRegularizedRotatedRecoveryFamily] using h

theorem channel_apply_one_norm_le_card (N : Channel I O) :
    ‖N.map (1 : Mat I)‖ ≤ (Fintype.card I : ℝ) := by
  have h := QuantumProver.ConditionalEntropy.ProbabilityMixtures.posSemidef_norm_le_trace
    (N.map (1 : Mat I)) (N.posSemidef Matrix.PosSemidef.one)
  rw [N.tracePreserving] at h
  simpa using h

theorem channel_normalizedIdentity_target_tendsto (R : ℝ → Channel I O)
    (A : Mat I) (B : Mat O) (m n : ℝ)
    (hLim : Tendsto (fun δ : ℝ => (R δ).map A) (𝓝[>] 0) (𝓝 B)) :
    Tendsto (fun δ : ℝ => (R δ).map (SBTModularLimits.normalizedIdentity A m n δ))
      (𝓝[>] 0) (𝓝 B) := by
  have hInv : Tendsto (fun δ : ℝ => (1 + δ * m)⁻¹) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    have h : ContinuousAt (fun δ : ℝ => (1 + δ * m)⁻¹) (0 : ℝ) := by
      apply ContinuousAt.inv₀
      · fun_prop
      · simp
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  have hδ : Tendsto (fun δ : ℝ => δ * n) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).mul
      (tendsto_const_nhds (x := n)) |>.mono_left nhdsWithin_le_nhds
  have hCoeff : Tendsto (fun δ : ℝ => (1 + δ * m)⁻¹ * (δ * n)) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa using hInv.mul hδ
  have hSmall : Tendsto (fun δ : ℝ =>
      ((1 + δ * m)⁻¹ * (δ * n)) • (R δ).map (1 : Mat I)) (𝓝[>] 0) (𝓝 (0 : Mat O)) := by
    have hMajor : Tendsto (fun δ : ℝ =>
        ‖(1 + δ * m)⁻¹ * (δ * n)‖ * (Fintype.card I : ℝ)) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
      simpa using hCoeff.norm.mul (tendsto_const_nhds (x := (Fintype.card I : ℝ)))
    apply squeeze_zero_norm (fun δ => ?_) hMajor
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (channel_apply_one_norm_le_card (R δ)) (norm_nonneg _)
  have hSum := (hInv.smul hLim).add hSmall
  simpa only [SBTModularLimits.normalizedIdentity, map_add, LinearMap.map_smul_of_tower,
    smul_add, smul_smul, one_smul, add_zero] using hSum

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

open Filter Set MeasureTheory
open scoped Topology
open QuantumProver.SuperchannelDiscrimination.TensorEntropy

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

theorem identityRegularizedPartialTraceRecovery_regularizedTarget_average_tendsto [Nonempty E]
    (σ ρ : Density (I × E)) (o₀ : I × E)
    (hPA : supportProjection (partialTraceRight σ.val) * partialTraceRight ρ.val =
      partialTraceRight ρ.val) :
    Tendsto (fun δ : ℝ =>
      (sbtRecoveryChannel (partialTraceRightChannel (I := I) (E := E))
        (SingularReference.identityRegularizedDensity σ (max δ 0) (le_max_right δ 0)) o₀).map
        (partialTraceRight (SingularReference.identityRegularizedMatrix ρ.val (max δ 0))))
      (𝓝[>] 0)
      (𝓝 ((sbtRecoveryChannel (partialTraceRightChannel (I := I) (E := E)) σ o₀).map
        (partialTraceRight ρ.val))) := by
  let A : Density I := ⟨partialTraceRight ρ.val, partialTraceRight_isDensity ρ.property⟩
  let R := fun δ : ℝ => sbtRecoveryChannel (partialTraceRightChannel (I := I) (E := E))
    (SingularReference.identityRegularizedDensity σ (max δ 0) (le_max_right δ 0)) o₀
  have hLim := identityRegularizedPartialTraceRecovery_average_tendsto σ A o₀ hPA
  have h := channel_normalizedIdentity_target_tendsto R A.val
    ((sbtRecoveryChannel (partialTraceRightChannel (I := I) (E := E)) σ o₀).map A.val)
    (Fintype.card (I × E) : ℝ) (Fintype.card E : ℝ) hLim
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change (R δ).map (SBTModularLimits.normalizedIdentity (partialTraceRight ρ.val)
    (Fintype.card (I × E) : ℝ) (Fintype.card E : ℝ) δ) =
      (R δ).map (partialTraceRight
        (SingularReference.identityRegularizedMatrix ρ.val (max δ 0)))
  rw [max_eq_left hδ.le, SingularReference.partialTraceRight_identityRegularizedMatrix]
  rfl

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.QuantumVariational

open MeasureTheory

variable {I : Type*} [Fintype I] [DecidableEq I]

def traceTestLM (Ω : Mat I) : Mat I →ₗ[ℝ] ℝ where
  toFun X := (X * Ω).trace.re
  map_add' X Y := by simp [Matrix.add_mul, Matrix.trace_add]
  map_smul' r X := by simp [Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul]

def traceTestCLM (Ω : Mat I) : Mat I →L[ℝ] ℝ := (traceTestLM Ω).toContinuousLinearMap

theorem traceTest_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (Ω : Mat I) (F : α → Mat I) (hF : Integrable F μ) :
    (∫ t, (F t * Ω).trace.re ∂μ) = ((∫ t, F t ∂μ) * Ω).trace.re :=
  (traceTestCLM Ω).integral_comp_comm hF

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.QuantumVariational

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

open MeasureTheory

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem sbtRecoveryChannel_trace_pairing (N : Channel I O) (σ : Density I)
    (o₀ : I) (A : Mat O) (Ω : Mat I) :
    ((sbtRecoveryChannel N σ o₀).map A * Ω).trace.re =
      ∫ t : ℝ, QuantumProver.SBTProbabilityWeight.beta0 t *
        ((completedRotatedPetzChannel N σ t o₀).map A * Ω).trace.re := by
  have hInt : Integrable (fun t : ℝ =>
      (completedRotatedPetzChannel N σ t o₀).map A)
      QuantumProver.SBTProbabilityWeight.beta0Probability :=
    (ContinuousLinearMap.apply ℂ (Mat I) A).integrable_comp
      (completedRotatedPetzChannel_clm_integrable N σ o₀ _)
  unfold sbtRecoveryChannel
  rw [averagedCompletedRotatedPetzChannel_apply,
    ← QuantumVariational.traceTest_integral _ Ω _ hInt,
    QuantumProver.SBTProbabilityWeight.integral_beta0Probability]
  rfl

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PetzSupportMap

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PartialTraceEntropy

open MeasureTheory
open PetzSupportMap
open QuantumProver.SuperchannelDiscrimination.FlaggedStates
open QuantumProver.SuperchannelDiscrimination.TensorEntropy

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

theorem faithful_partialTrace_trace_test (A σ : Density (I × E)) (o₀ : I × E)
    (hσ : σ.val.PosDef) (hτ : (partialTraceRight σ.val).PosDef)
    (hA : (partialTraceRight A.val).PosDef) (Ω : Mat (I × E)) (hΩ : Ω.PosDef) :
    (NormedSpace.exp (partialTraceLogReference A.val σ.val + cfc Real.log Ω)).trace.re ≤
      ((sbtRecoveryChannel (partialTraceRightChannel (I := I) (E := E)) σ o₀).map
        (partialTraceRight A.val) * Ω).trace.re := by
  have hGT := QuantumProver.RotatedPetzTraceComparison.trace_exp_le_weighted_rotatedPetzTrace
    σ.val Ω (partialTraceRight A.val) hσ hτ hA hΩ
  have hExp : partialTraceLogReference A.val σ.val + cfc Real.log Ω =
      QuantumProver.RotatedPetzTraceComparison.matrixLog Ω +
      QuantumProver.RotatedPetzTraceComparison.matrixLog σ.val -
      QuantumProver.RotatedPetzTraceComparison.liftRight
        (QuantumProver.RotatedPetzTraceComparison.matrixLog (partialTraceRight σ.val)) +
      QuantumProver.RotatedPetzTraceComparison.liftRight
        (QuantumProver.RotatedPetzTraceComparison.matrixLog (partialTraceRight A.val)) := by
    change cfc Real.log σ.val + liftLeft (cfc Real.log (partialTraceRight A.val)) -
      liftLeft (cfc Real.log (partialTraceRight σ.val)) + cfc Real.log Ω =
      cfc Real.log Ω + cfc Real.log σ.val -
      liftLeft (cfc Real.log (partialTraceRight σ.val)) +
      liftLeft (cfc Real.log (partialTraceRight A.val))
    abel
  rw [← hExp] at hGT
  have hSupport : supportProjection (partialTraceRight σ.val) *
      partialTraceRight A.val = partialTraceRight A.val := by
    rw [QuantumProver.SuperchannelDiscrimination.ModularMatrix.supportProjection_posDef hτ,
      Matrix.one_mul]
  have hTrace (t : ℝ) :
      (Ω * QuantumProver.RotatedPetzTraceComparison.rotatedPetzMatrix
        σ.val (partialTraceRight A.val) t).trace.re =
      ((completedRotatedPetzChannel (partialTraceRightChannel (I := I) (E := E))
        σ t o₀).map (partialTraceRight A.val) * Ω).trace.re := by
    change (Ω * partialTraceRotatedPetzMatrix σ (partialTraceRight A.val) t).trace.re = _
    rw [← completedPartialTraceRotatedPetzChannel_on_supported
      σ (partialTraceRight A.val) t o₀ hSupport, Matrix.trace_mul_comm]
  simp_rw [hTrace] at hGT
  rw [← sbtRecoveryChannel_trace_pairing] at hGT
  exact hGT

theorem measuredRelativeEntropyBits_partialTrace_recovery_of_posDef
    (A σ : Density (I × E)) (o₀ : I × E)
    (hσ : σ.val.PosDef) (hτ : (partialTraceRight σ.val).PosDef)
    (hA : (partialTraceRight A.val).PosDef) :
    measuredRelativeEntropyBits A.val
      ((sbtRecoveryChannel (partialTraceRightChannel (I := I) (E := E)) σ o₀).map
        (partialTraceRight A.val)) ≤
      ((finiteRelativeEntropyBits A.val σ.val -
        finiteRelativeEntropyBits (partialTraceRight A.val) (partialTraceRight σ.val) : ℝ) : EReal) := by
  let R := sbtRecoveryChannel (partialTraceRightChannel (I := I) (E := E)) σ o₀
  have hR : (R.map (partialTraceRight A.val)).PosSemidef :=
    R.posSemidef (partialTraceRight_posSemidef A.property.1)
  rw [MeasuredVariationalBridge.measuredRelativeEntropyBits_variational
    A.val (R.map (partialTraceRight A.val)) A.property hR]
  apply sSup_le
  rintro z ⟨Ω, hΩ, rfl⟩
  have hHerm : (cfc Real.log Ω).IsHermitian := cfc_predicate _ _
  have hKlein := finiteRelativeEntropyBits_partialTraceGap_ge_exponential_test
    A σ.val (cfc Real.log Ω) hHerm
  have hTrace := faithful_partialTrace_trace_test A σ o₀ hσ hτ hA Ω hΩ
  have hCompare :
      ((A.val * cfc Real.log Ω).trace.re + 1 -
        (R.map (partialTraceRight A.val) * Ω).trace.re) / Real.log 2 ≤
      ((A.val * cfc Real.log Ω).trace.re + 1 -
        (NormedSpace.exp (partialTraceLogReference A.val σ.val + cfc Real.log Ω)).trace.re) /
        Real.log 2 :=
    div_le_div_of_nonneg_right (sub_le_sub_left hTrace _) log_two_pos.le
  exact_mod_cast hCompare.trans hKlein

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PartialTraceEntropy

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.CommonReferenceRecovery

open MeasureTheory
open PetzSupportMap

variable {I O J : Type*} [Fintype I] [Fintype O] [Fintype J]
  [DecidableEq I] [DecidableEq O] [DecidableEq J]

def composeChannel (M : Channel O J) (N : Channel I O) : Channel I J where
  map := M.map.comp N.map
  completelyPositive :=
    (QuantumProver.SuperchannelDiscrimination.CPTPKraus.completelyPositive_iff_EJMCP _).mpr
      (((QuantumProver.SuperchannelDiscrimination.CPTPKraus.completelyPositive_iff_EJMCP _).mp
        M.completelyPositive).comp
          ((QuantumProver.SuperchannelDiscrimination.CPTPKraus.completelyPositive_iff_EJMCP _).mp
            N.completelyPositive))
  tracePreserving := by
    intro A
    change (M.map (N.map A)).trace = A.trace
    rw [M.tracePreserving, N.tracePreserving]

theorem composeChannel_apply (M : Channel O J) (N : Channel I O) (A : Mat I) :
    (composeChannel M N).map A = M.map (N.map A) := rfl

def canonicalStinespring (N : Channel I O) : Matrix (O × (I × O)) I ℂ :=
  Geometry.krausDilation (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus N.map)

theorem canonicalStinespring_isometry (N : Channel I O) :
    (canonicalStinespring N)ᴴ * canonicalStinespring N = 1 :=
  Geometry.krausDilation_isometry _
    (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_gram
      N.map N.completelyPositive N.tracePreserving)

theorem canonicalStinespring_partialTrace (N : Channel I O) (A : Mat I) :
    partialTraceRight (canonicalStinespring N * A * (canonicalStinespring N)ᴴ) = N.map A := by
  change Geometry.traceRight (Geometry.krausDilation _ * A * (Geometry.krausDilation _)ᴴ) = _
  rw [Geometry.traceRight_krausDilation]
  exact (QuantumProver.SuperchannelDiscrimination.CPTPKraus.canonicalKraus_reconstruct
    N.map N.completelyPositive A).symm

def stinespringReferenceDensity (N : Channel I O) (σ : Density I) : Density (O × (I × O)) :=
  ⟨(SBTIsometryChannels.isometryExtensionChannel (canonicalStinespring N)
      (canonicalStinespring_isometry N)).map σ.val,
    (SBTIsometryChannels.isometryExtensionChannel (canonicalStinespring N)
      (canonicalStinespring_isometry N)).isDensity σ.property⟩

theorem stinespringReferenceDensity_val (N : Channel I O) (σ : Density I) :
    (stinespringReferenceDensity N σ).val =
      canonicalStinespring N * σ.val * (canonicalStinespring N)ᴴ :=
  SBTIsometryChannels.isometryExtensionChannel_action _ _ _

theorem stinespringReferenceDensity_marginal (N : Channel I O) (σ : Density I) :
    partialTraceRight (stinespringReferenceDensity N σ).val = N.map σ.val := by
  rw [stinespringReferenceDensity_val, canonicalStinespring_partialTrace]

def stinespringCompletionIndex (N : Channel I O) (σ : Density I) : O × (I × O) :=
  Classical.choice (density_index_nonempty (stinespringReferenceDensity N σ))

def commonStinespringRecovery (N : Channel I O) (σ : Density I) (o₀ : I) : Channel O I :=
  composeChannel
    (SBTIsometryChannels.completedCompressionChannel (canonicalStinespring N)
      (canonicalStinespring_isometry N) o₀)
    (sbtRecoveryChannel (partialTraceRightChannel (I := O) (E := I × O))
      (stinespringReferenceDensity N σ) (stinespringCompletionIndex N σ))

theorem commonStinespringRecovery_reference (N : Channel I O) (σ : Density I) (o₀ : I) :
    (commonStinespringRecovery N σ o₀).map (N.map σ.val) = σ.val := by
  unfold commonStinespringRecovery
  rw [composeChannel_apply, ← stinespringReferenceDensity_marginal N σ]
  change (SBTIsometryChannels.completedCompressionChannel (canonicalStinespring N)
    (canonicalStinespring_isometry N) o₀).map
    ((sbtRecoveryChannel (partialTraceRightChannel (I := O) (E := I × O))
      (stinespringReferenceDensity N σ) (stinespringCompletionIndex N σ)).map
      ((partialTraceRightChannel (I := O) (E := I × O)).map
        (stinespringReferenceDensity N σ).val)) = σ.val
  rw [sbtRecoveryChannel_reference, stinespringReferenceDensity_val]
  exact SBTIsometryChannels.completedCompressionChannel_reference _ _ _ _

theorem commonStinespringRecovery_apply (N : Channel I O) (σ : Density I)
    (o₀ : I) (A : Mat O) :
    (commonStinespringRecovery N σ o₀).map A =
      ∫ t : ℝ, QuantumProver.SBTProbabilityWeight.beta0 t •
        (SBTIsometryChannels.completedCompressionChannel (canonicalStinespring N)
          (canonicalStinespring_isometry N) o₀).map
        ((completedRotatedPetzChannel (partialTraceRightChannel (I := O) (E := I × O))
          (stinespringReferenceDensity N σ) t (stinespringCompletionIndex N σ)).map A) := by
  let T := SBTIsometryChannels.completedCompressionChannel (canonicalStinespring N)
    (canonicalStinespring_isometry N) o₀
  let μ := QuantumProver.SBTProbabilityWeight.beta0Probability
  have hInt : Integrable (fun t : ℝ =>
      (completedRotatedPetzChannel (partialTraceRightChannel (I := O) (E := I × O))
        (stinespringReferenceDensity N σ) t (stinespringCompletionIndex N σ)).map A) μ :=
    (ContinuousLinearMap.apply ℂ (Mat (O × (I × O))) A).integrable_comp
      (completedRotatedPetzChannel_clm_integrable _ _ _ μ)
  unfold commonStinespringRecovery sbtRecoveryChannel
  rw [composeChannel_apply, averagedCompletedRotatedPetzChannel_apply]
  change T.map.toContinuousLinearMap (∫ t : ℝ,
    (completedRotatedPetzChannel (partialTraceRightChannel (I := O) (E := I × O))
      (stinespringReferenceDensity N σ) t (stinespringCompletionIndex N σ)).map A ∂μ) = _
  rw [← T.map.toContinuousLinearMap.integral_comp_comm hInt,
    QuantumProver.SBTProbabilityWeight.integral_beta0Probability]
  rfl

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.CommonReferenceRecovery

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.SingularReference

open Filter Set
open scoped Topology
open QuantumProver.SuperchannelDiscrimination.FlaggedStates

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

theorem identityRegularizedMatrix_clipped_tendsto (A : Mat I) :
    Tendsto (fun δ : ℝ => identityRegularizedMatrix A (max δ 0)) (𝓝[>] 0) (𝓝 A) := by
  apply (identityRegularizedMatrix_tendsto_right A).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [max_eq_left hδ.le]

theorem partialTrace_identityRegularizedMatrix_eq_shared (A : Mat (I × E)) (δ : ℝ) :
    partialTraceRight (identityRegularizedMatrix A δ) =
      QuantumProver.QuantumRelativeEntropyRegularization.identityRegularizedMatrix
        (partialTraceRight A) (Fintype.card E : ℝ) δ := by
  have hDen : 1 + δ * (Fintype.card (I × E) : ℝ) =
      1 + δ * (Fintype.card E : ℝ) * (Fintype.card I : ℝ) := by
    rw [Fintype.card_prod, Nat.cast_mul]
    ring
  rw [partialTraceRight_identityRegularizedMatrix]
  simp only [identityRegularizationDenom,
    QuantumProver.QuantumRelativeEntropyRegularization.identityRegularizedMatrix, hDen]

theorem identityRegularized_relativeEntropy_tendsto (A B : Density I)
    (hs : HasSupportIn A.val B.val) :
    Tendsto (fun δ : ℝ => finiteRelativeEntropyBits
      (identityRegularizedMatrix A.val (max δ 0))
      (identityRegularizedMatrix B.val (max δ 0))) (𝓝[>] 0)
      (𝓝 (finiteRelativeEntropyBits A.val B.val)) := by
  have hRaw : Tendsto (fun δ : ℝ => finiteRelativeEntropyBits
      (identityRegularizedMatrix A.val δ) (identityRegularizedMatrix B.val δ)) (𝓝[>] 0)
      (𝓝 (finiteRelativeEntropyBits A.val B.val)) := by
    simpa only [identityRegularizedMatrix, identityRegularizationDenom,
      QuantumProver.QuantumRelativeEntropyRegularization.identityRegularizedMatrix, mul_one] using
      QuantumProver.QuantumRelativeEntropyRegularization.identityRegularization_relativeEntropy_tendsto_one
        A.property B.property hs
  apply hRaw.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [max_eq_left hδ.le]

theorem partialTrace_identityRegularized_relativeEntropy_tendsto
    (A B : Density (I × E))
    (hs : HasSupportIn (partialTraceRight A.val) (partialTraceRight B.val)) :
    Tendsto (fun δ : ℝ => finiteRelativeEntropyBits
      (partialTraceRight (identityRegularizedMatrix A.val (max δ 0)))
      (partialTraceRight (identityRegularizedMatrix B.val (max δ 0)))) (𝓝[>] 0)
      (𝓝 (finiteRelativeEntropyBits (partialTraceRight A.val) (partialTraceRight B.val))) := by
  have hRaw : Tendsto (fun δ : ℝ => finiteRelativeEntropyBits
      (partialTraceRight (identityRegularizedMatrix A.val δ))
      (partialTraceRight (identityRegularizedMatrix B.val δ))) (𝓝[>] 0)
      (𝓝 (finiteRelativeEntropyBits (partialTraceRight A.val) (partialTraceRight B.val))) := by
    simpa only [partialTrace_identityRegularizedMatrix_eq_shared] using
      QuantumProver.QuantumRelativeEntropyRegularization.identityRegularization_relativeEntropy_tendsto
        (partialTraceRight_isDensity A.property) (partialTraceRight_isDensity B.property)
        hs (Nat.cast_nonneg (Fintype.card E))
  apply hRaw.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [max_eq_left hδ.le]

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.SingularReference

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PartialTraceEntropy

open Filter Set
open scoped Topology
open PetzSupportMap QuantumVariational
open QuantumProver.SuperchannelDiscrimination.FlaggedStates

variable {I E : Type*} [Fintype I] [Fintype E] [DecidableEq I] [DecidableEq E]

theorem measuredRelativeEntropyBits_partialTrace_recovery
    (A σ : Density (I × E)) (o₀ : I × E) (hs : HasSupportIn A.val σ.val) :
    measuredRelativeEntropyBits A.val
      ((sbtRecoveryChannel (partialTraceRightChannel (I := I) (E := E)) σ o₀).map
        (partialTraceRight A.val)) ≤
      ((finiteRelativeEntropyBits A.val σ.val -
        finiteRelativeEntropyBits (partialTraceRight A.val) (partialTraceRight σ.val) : ℝ) : EReal) := by
  haveI : Nonempty E := by
    obtain ⟨⟨i, e⟩⟩ := density_index_nonempty A
    exact ⟨e⟩
  let ρδ := fun δ : ℝ => SingularReference.identityRegularizedDensity A
    (max δ 0) (le_max_right δ 0)
  let σδ := fun δ : ℝ => SingularReference.identityRegularizedDensity σ
    (max δ 0) (le_max_right δ 0)
  let R := sbtRecoveryChannel (partialTraceRightChannel (I := I) (E := E)) σ o₀
  let Rδ := fun δ : ℝ => sbtRecoveryChannel (partialTraceRightChannel (I := I) (E := E)) (σδ δ) o₀
  let recδ := fun δ : ℝ => (Rδ δ).map (partialTraceRight (ρδ δ).val)
  have hsOut : HasSupportIn (partialTraceRight A.val) (partialTraceRight σ.val) :=
    SBTSupportTransport.channel_hasSupportIn (partialTraceRightChannel (I := I) (E := E))
      A.val σ.val A.property.1 σ.property.1 hs
  have hPA := SBTSupportTransport.channel_supportProjection_mul_left
    (partialTraceRightChannel (I := I) (E := E)) A.val σ.val A.property.1 σ.property.1 hs
  have hρLim : Tendsto (fun δ : ℝ => (ρδ δ).val) (𝓝[>] 0) (𝓝 A.val) :=
    SingularReference.identityRegularizedMatrix_clipped_tendsto A.val
  have hRecLim : Tendsto recδ (𝓝[>] 0) (𝓝 (R.map (partialTraceRight A.val))) :=
    identityRegularizedPartialTraceRecovery_regularizedTarget_average_tendsto σ A o₀ hPA
  have hGapLim : Tendsto (fun δ : ℝ =>
      finiteRelativeEntropyBits (ρδ δ).val (σδ δ).val -
        finiteRelativeEntropyBits (partialTraceRight (ρδ δ).val) (partialTraceRight (σδ δ).val))
      (𝓝[>] 0) (𝓝 (finiteRelativeEntropyBits A.val σ.val -
        finiteRelativeEntropyBits (partialTraceRight A.val) (partialTraceRight σ.val))) :=
    (SingularReference.identityRegularized_relativeEntropy_tendsto A σ hs).sub
      (SingularReference.partialTrace_identityRegularized_relativeEntropy_tendsto A σ hsOut)
  have hRecPSD : (R.map (partialTraceRight A.val)).PosSemidef :=
    R.posSemidef (partialTraceRight_posSemidef A.property.1)
  rw [MeasuredVariationalBridge.measuredRelativeEntropyBits_variational
    A.val (R.map (partialTraceRight A.val)) A.property hRecPSD]
  apply sSup_le
  rintro z ⟨Ω, hΩ, rfl⟩
  have hRhoTestLim : Tendsto (fun δ : ℝ => ((ρδ δ).val * cfc Real.log Ω).trace.re)
      (𝓝[>] 0) (𝓝 ((A.val * cfc Real.log Ω).trace.re)) :=
    ((traceTestCLM (cfc Real.log Ω)).continuous.tendsto A.val).comp hρLim
  have hRecTestLim : Tendsto (fun δ : ℝ => (recδ δ * Ω).trace.re)
      (𝓝[>] 0) (𝓝 (R.map (partialTraceRight A.val) * Ω).trace.re) :=
    ((traceTestCLM Ω).continuous.tendsto _).comp hRecLim
  have hOne : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 (1 : ℝ)) := tendsto_const_nhds
  have hTestLim : Tendsto (fun δ : ℝ =>
      (((ρδ δ).val * cfc Real.log Ω).trace.re + 1 - (recδ δ * Ω).trace.re) / Real.log 2)
      (𝓝[>] 0) (𝓝 (((A.val * cfc Real.log Ω).trace.re + 1 -
        (R.map (partialTraceRight A.val) * Ω).trace.re) / Real.log 2)) :=
    ((hRhoTestLim.add hOne).sub hRecTestLim).div_const (Real.log 2)
  have hBound : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (((ρδ δ).val * cfc Real.log Ω).trace.re + 1 - (recδ δ * Ω).trace.re) / Real.log 2 ≤
        finiteRelativeEntropyBits (ρδ δ).val (σδ δ).val -
          finiteRelativeEntropyBits (partialTraceRight (ρδ δ).val) (partialTraceRight (σδ δ).val) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hσPD : (σδ δ).val.PosDef := by
      change (SingularReference.identityRegularizedMatrix σ.val (max δ 0)).PosDef
      rw [max_eq_left hδ.le]
      exact SingularReference.identityRegularizedMatrix_posDef σ.val σ.property.1 δ hδ
    have hτPD : (partialTraceRight (σδ δ).val).PosDef := by
      change (partialTraceRight (SingularReference.identityRegularizedMatrix σ.val (max δ 0))).PosDef
      rw [max_eq_left hδ.le]
      exact SingularReference.partialTraceRight_identityRegularizedMatrix_posDef σ.val σ.property.1 δ hδ
    have hρPD : (partialTraceRight (ρδ δ).val).PosDef := by
      change (partialTraceRight (SingularReference.identityRegularizedMatrix A.val (max δ 0))).PosDef
      rw [max_eq_left hδ.le]
      exact SingularReference.partialTraceRight_identityRegularizedMatrix_posDef A.val A.property.1 δ hδ
    have hSBT := measuredRelativeEntropyBits_partialTrace_recovery_of_posDef
      (ρδ δ) (σδ δ) o₀ hσPD hτPD hρPD
    have hRecδPSD : (recδ δ).PosSemidef :=
      (Rδ δ).posSemidef (partialTraceRight_posSemidef (ρδ δ).property.1)
    have hTest :
        (((((ρδ δ).val * cfc Real.log Ω).trace.re + 1 - (recδ δ * Ω).trace.re) /
          Real.log 2 : ℝ) : EReal) ≤ measuredRelativeEntropyBits (ρδ δ).val (recδ δ) := by
      rw [MeasuredVariationalBridge.measuredRelativeEntropyBits_variational
        (ρδ δ).val (recδ δ) (ρδ δ).property hRecδPSD]
      exact le_sSup ⟨Ω, hΩ, rfl⟩
    exact_mod_cast hTest.trans hSBT
  exact_mod_cast le_of_tendsto_of_tendsto hTestLim hGapLim hBound

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.PartialTraceEntropy

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.CommonReferenceRecovery

open PetzSupportMap
open QuantumProver.SuperchannelDiscrimination.FlaggedStates

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem measuredRelativeEntropyBits_recovery (N : Channel I O)
    (A σ : Density I) (o₀ : I) (hs : HasSupportIn A.val σ.val) :
    measuredRelativeEntropyBits A.val
      ((commonStinespringRecovery N σ o₀).map (N.map A.val)) ≤
      ((finiteRelativeEntropyBits A.val σ.val -
        finiteRelativeEntropyBits (N.map A.val) (N.map σ.val) : ℝ) : EReal) := by
  let V := canonicalStinespring N
  have hV : Vᴴ * V = 1 := canonicalStinespring_isometry N
  let σV := stinespringReferenceDensity N σ
  let AV : Density (O × (I × O)) :=
    ⟨V * A.val * Vᴴ, SBTSupportTransport.isDensity_isometry V hV A.val A.property⟩
  let j₀ := stinespringCompletionIndex N σ
  let RP := sbtRecoveryChannel (partialTraceRightChannel (I := O) (E := I × O)) σV j₀
  let T := SBTIsometryChannels.completedCompressionChannel V hV o₀
  have hsV : HasSupportIn AV.val σV.val := by
    rw [stinespringReferenceDensity_val]
    exact (SBTSupportTransport.hasSupportIn_isometry_iff V hV A.val σ.val).mpr hs
  have hSBT := PartialTraceEntropy.measuredRelativeEntropyBits_partialTrace_recovery AV σV j₀ hsV
  have hDPI := MeasuredDivergence.measuredRelativeEntropyBits_channel_dpi
    T AV.val (RP.map (partialTraceRight AV.val))
  have hLeft : T.map AV.val = A.val :=
    SBTIsometryChannels.completedCompressionChannel_reference V hV o₀ A.val
  have hRecovered : T.map (RP.map (partialTraceRight AV.val)) =
      (commonStinespringRecovery N σ o₀).map (N.map A.val) := by
    change T.map (RP.map (partialTraceRight (V * A.val * Vᴴ))) =
      T.map (RP.map (N.map A.val))
    rw [canonicalStinespring_partialTrace]
  rw [hLeft, hRecovered] at hDPI
  have hGap : finiteRelativeEntropyBits AV.val σV.val -
      finiteRelativeEntropyBits (partialTraceRight AV.val) (partialTraceRight σV.val) =
      finiteRelativeEntropyBits A.val σ.val -
        finiteRelativeEntropyBits (N.map A.val) (N.map σ.val) := by
    rw [stinespringReferenceDensity_val]
    change finiteRelativeEntropyBits (V * A.val * Vᴴ) (V * σ.val * Vᴴ) -
      finiteRelativeEntropyBits (partialTraceRight (V * A.val * Vᴴ))
        (partialTraceRight (V * σ.val * Vᴴ)) = _
    rw [SBTSupportTransport.finiteRelativeEntropyBits_isometry V hV
      A.val σ.val A.property.1.isHermitian σ.property.1.isHermitian,
      canonicalStinespring_partialTrace, canonicalStinespring_partialTrace]
  rw [hGap] at hSBT
  exact hDPI.trans hSBT

theorem buresBudget_channel_recovery_of_posDef (N : Channel I O)
    (A σ : Density I) (o₀ : I) (hA : A.val.PosDef) (hs : HasSupportIn A.val σ.val) :
    2 * (1 - rootFidelity A.val
      ((commonStinespringRecovery N σ o₀).map (N.map A.val))) ≤
      Real.log 2 * (finiteRelativeEntropyBits A.val σ.val -
        finiteRelativeEntropyBits (N.map A.val) (N.map σ.val)) := by
  let R := commonStinespringRecovery N σ o₀
  let B : Density I := ⟨R.map (N.map A.val), R.isDensity (N.isDensity A.property)⟩
  have hBures := MeasuredDivergence.measuredRelativeEntropyBits_ge_bures_of_posDef A B hA
  have hSBT := measuredRelativeEntropyBits_recovery N A σ o₀ hs
  have hReal : 2 * (1 - rootFidelity A.val B.val) / Real.log 2 ≤
      finiteRelativeEntropyBits A.val σ.val -
        finiteRelativeEntropyBits (N.map A.val) (N.map σ.val) := by
    exact_mod_cast hBures.trans hSBT
  simpa only [mul_comm] using (div_le_iff₀ log_two_pos).mp hReal

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.CommonReferenceRecovery

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.FidelityLoss

open CommonReferenceRecovery
open QuantumProver.SuperchannelDiscrimination.FlaggedStates

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem rootFidelity_increase_sq_le_holevoLoss_of_posDef (A B : Density I)
    (N : Channel I O) (hA : A.val.PosDef) (hB : B.val.PosDef) :
    (rootFidelity (N.map A.val) (N.map B.val) - rootFidelity A.val B.val) ^ 2 ≤
      4 * Real.log 2 * (binaryHolevo A.val B.val - binaryHolevo (N.map A.val) (N.map B.val)) := by
  let σ : Density I := ⟨(1 / 2 : ℝ) • (A.val + B.val),
    equalPriorAverage_isDensity A.property B.property⟩
  obtain ⟨o₀⟩ := density_index_nonempty σ
  let R := commonStinespringRecovery N σ o₀
  let r₀ : Density I := ⟨R.map (N.map A.val), R.isDensity (N.isDensity A.property)⟩
  let r₁ : Density I := ⟨R.map (N.map B.val), R.isDensity (N.isDensity B.property)⟩
  let g₀ := finiteRelativeEntropyBits A.val σ.val -
    finiteRelativeEntropyBits (N.map A.val) (N.map σ.val)
  let g₁ := finiteRelativeEntropyBits B.val σ.val -
    finiteRelativeEntropyBits (N.map B.val) (N.map σ.val)
  have hs₀ : HasSupportIn A.val σ.val :=
    ReferenceEntropy.hasSupportIn_equalPriorAverage_left A.property.1 B.property.1
  have hs₁ : HasSupportIn B.val σ.val :=
    ReferenceEntropy.hasSupportIn_equalPriorAverage_right A.property.1 B.property.1
  have hBudget₀ : 2 * (1 - rootFidelity A.val r₀.val) ≤ Real.log 2 * g₀ :=
    buresBudget_channel_recovery_of_posDef N A σ o₀ hA hs₀
  have hBudget₁ : 2 * (1 - rootFidelity B.val r₁.val) ≤ Real.log 2 * g₁ :=
    buresBudget_channel_recovery_of_posDef N B σ o₀ hB hs₁
  obtain ⟨b₀, b₁, hb₀, hb₁, hDifference, hSquare₀, hSquare₁⟩ :=
    UhlmannGeometry.rootFidelity_difference_has_bures_budget A B r₀ r₁
  have hSquareBudget₀ : b₀ ^ 2 ≤ Real.log 2 * g₀ := by rw [hSquare₀]; exact hBudget₀
  have hSquareBudget₁ : b₁ ^ 2 ≤ Real.log 2 * g₁ := by rw [hSquare₁]; exact hBudget₁
  have hForward := UhlmannGeometry.rootFidelity_channel_mono N A.val B.val A.property.1 B.property.1
  have hRecovery := UhlmannGeometry.rootFidelity_channel_mono R
    (N.map A.val) (N.map B.val) (N.posSemidef A.property.1) (N.posSemidef B.property.1)
  have hIncrease : rootFidelity (N.map A.val) (N.map B.val) - rootFidelity A.val B.val ≤ b₀ + b₁ :=
    (sub_le_sub_right hRecovery _).trans hDifference
  have hNonneg : 0 ≤ rootFidelity (N.map A.val) (N.map B.val) - rootFidelity A.val B.val :=
    sub_nonneg.mpr hForward
  have hSquared : (rootFidelity (N.map A.val) (N.map B.val) - rootFidelity A.val B.val) ^ 2 ≤
      (b₀ + b₁) ^ 2 := by
    have hMul := mul_nonneg (sub_nonneg.mpr hIncrease) (add_nonneg (add_nonneg hb₀ hb₁) hNonneg)
    nlinarith
  rw [ReferenceEntropy.binaryHolevoLoss_eq_average_referenceGaps A B N]
  change (rootFidelity (N.map A.val) (N.map B.val) - rootFidelity A.val B.val) ^ 2 ≤
    4 * Real.log 2 * ((g₀ + g₁) / 2)
  calc
    _ ≤ (b₀ + b₁) ^ 2 := hSquared
    _ ≤ 2 * (b₀ ^ 2 + b₁ ^ 2) := by nlinarith [sq_nonneg (b₀ - b₁)]
    _ ≤ 2 * (Real.log 2 * g₀ + Real.log 2 * g₁) :=
      mul_le_mul_of_nonneg_left (add_le_add hSquareBudget₀ hSquareBudget₁) (by norm_num)
    _ = _ := by ring

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.FidelityLoss

namespace QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.FidelityLoss

open Filter Set
open scoped Topology

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem rootFidelity_increase_sq_le_holevoLoss (A B : Density I) (N : Channel I O) :
    (rootFidelity (N.map A.val) (N.map B.val) - rootFidelity A.val B.val) ^ 2 ≤
      4 * Real.log 2 * (binaryHolevo A.val B.val - binaryHolevo (N.map A.val) (N.map B.val)) := by
  let Aδ := fun δ : ℝ => SingularReference.identityRegularizedDensity A
    (max δ 0) (le_max_right δ 0)
  let Bδ := fun δ : ℝ => SingularReference.identityRegularizedDensity B
    (max δ 0) (le_max_right δ 0)
  have hA : Tendsto (fun δ : ℝ => (Aδ δ).val) (𝓝[>] 0) (𝓝 A.val) :=
    SingularReference.identityRegularizedMatrix_clipped_tendsto A.val
  have hB : Tendsto (fun δ : ℝ => (Bδ δ).val) (𝓝[>] 0) (𝓝 B.val) :=
    SingularReference.identityRegularizedMatrix_clipped_tendsto B.val
  have hNA : Tendsto (fun δ : ℝ => N.map (Aδ δ).val) (𝓝[>] 0) (𝓝 (N.map A.val)) :=
    (N.map.toContinuousLinearMap.continuous.tendsto A.val).comp hA
  have hNB : Tendsto (fun δ : ℝ => N.map (Bδ δ).val) (𝓝[>] 0) (𝓝 (N.map B.val)) :=
    (N.map.toContinuousLinearMap.continuous.tendsto B.val).comp hB
  have hPA : ∀ᶠ δ : ℝ in 𝓝[>] 0, (Aδ δ).val.PosSemidef :=
    Eventually.of_forall fun δ => (Aδ δ).property.1
  have hPB : ∀ᶠ δ : ℝ in 𝓝[>] 0, (Bδ δ).val.PosSemidef :=
    Eventually.of_forall fun δ => (Bδ δ).property.1
  have hPNA : ∀ᶠ δ : ℝ in 𝓝[>] 0, (N.map (Aδ δ).val).PosSemidef :=
    Eventually.of_forall fun δ => N.posSemidef (Aδ δ).property.1
  have hPNB : ∀ᶠ δ : ℝ in 𝓝[>] 0, (N.map (Bδ δ).val).PosSemidef :=
    Eventually.of_forall fun δ => N.posSemidef (Bδ δ).property.1
  have hFin := SingularLimit.tendsto_rootFidelity hA hB hPA hPB A.property.1 B.property.1
  have hFout := SingularLimit.tendsto_rootFidelity hNA hNB hPNA hPNB
    (N.posSemidef A.property.1) (N.posSemidef B.property.1)
  have hLeft : Tendsto (fun δ : ℝ =>
      (rootFidelity (N.map (Aδ δ).val) (N.map (Bδ δ).val) -
        rootFidelity (Aδ δ).val (Bδ δ).val) ^ 2) (𝓝[>] 0)
      (𝓝 ((rootFidelity (N.map A.val) (N.map B.val) - rootFidelity A.val B.val) ^ 2)) :=
    (hFout.sub hFin).pow 2
  have hPairIn := SingularLimit.tendsto_pairCost hA hB hPA hPB A.property.1 B.property.1
  have hPairOut := SingularLimit.tendsto_pairCost hNA hNB hPNA hPNB
    (N.posSemidef A.property.1) (N.posSemidef B.property.1)
  have hOne : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 (1 : ℝ)) := tendsto_const_nhds
  have hChiIn : Tendsto (fun δ : ℝ => binaryHolevo (Aδ δ).val (Bδ δ).val)
      (𝓝[>] 0) (𝓝 (binaryHolevo A.val B.val)) := by
    simpa only [pairCost, sub_sub_cancel] using hOne.sub hPairIn
  have hChiOut : Tendsto (fun δ : ℝ => binaryHolevo (N.map (Aδ δ).val) (N.map (Bδ δ).val))
      (𝓝[>] 0) (𝓝 (binaryHolevo (N.map A.val) (N.map B.val))) := by
    simpa only [pairCost, sub_sub_cancel] using hOne.sub hPairOut
  have hConst : Tendsto (fun _ : ℝ => 4 * Real.log 2) (𝓝[>] 0) (𝓝 (4 * Real.log 2)) :=
    tendsto_const_nhds
  have hRight := hConst.mul (hChiIn.sub hChiOut)
  apply le_of_tendsto_of_tendsto hLeft hRight
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hAPD : (Aδ δ).val.PosDef := by
    change (SingularReference.identityRegularizedMatrix A.val (max δ 0)).PosDef
    rw [max_eq_left hδ.le]
    exact SingularReference.identityRegularizedMatrix_posDef A.val A.property.1 δ hδ
  have hBPD : (Bδ δ).val.PosDef := by
    change (SingularReference.identityRegularizedMatrix B.val (max δ 0)).PosDef
    rw [max_eq_left hδ.le]
    exact SingularReference.identityRegularizedMatrix_posDef B.val B.property.1 δ hδ
  exact rootFidelity_increase_sq_le_holevoLoss_of_posDef (Aδ δ) (Bδ δ) N hAPD hBPD

end QuantumProver.BellDiagonalSquashedEntanglement.RecoveryGeometry.FidelityLoss
