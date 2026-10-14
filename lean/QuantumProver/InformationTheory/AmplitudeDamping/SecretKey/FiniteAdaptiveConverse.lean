import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.FiniteCodeConverse
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.LaneMergeHistory
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.LaneRetainedOutput
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.LanePureKeyTransport
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.PublicCopyProtocol
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.UniformPaddingKeyTransport
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.LaneConverseLimit
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.AdaptiveConverse
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.OptimizedAdaptiveConverse

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.FiniteAdaptiveConverse

open LaneMergeHistory PhysicalPurification PrivateTest PrivateTestResource FiniteCodeConverse
open QuantumProver.AmplitudeDamping.FiniteModel

theorem pairPriorEveInput_honest {a b c d : ℕ} {E F : Type*}
    [Fintype E] [Fintype F]
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ)
    (σ : Matrix ((Fin c × Fin d) × F) ((Fin c × Fin d) × F) ℂ) :
    partialTraceRight (pairPriorEveInput_B ρ σ) =
      pairMatrixB (partialTraceRight ρ) (partialTraceRight σ) := by
  ext x y
  simp [partialTraceRight, pairPriorEveInput_B, pairMatrixB, pairOperatorB,
    Matrix.submatrix_apply, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem lanePriorMatrix_honest {a b : ℕ} {E : Type*} [Fintype E]
    (ρ : Matrix ((Fin a × Fin b) × E) ((Fin a × Fin b) × E) ℂ) (n : ℕ) :
    partialTraceRight (lanePriorMatrix_B ρ n) =
      lanePowerMatrixB (partialTraceRight ρ) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change partialTraceRight (pairPriorEveInput_B (lanePriorMatrix_B ρ n) ρ) =
        pairMatrixB (lanePowerMatrixB (partialTraceRight ρ) n) (partialTraceRight ρ)
      rw [pairPriorEveInput_honest, ih]

theorem lanePriorMatrix_honest_isDensity {a b : ℕ} {E : Type*}
    [Fintype E] (ρ : Density ((Fin a × Fin b) × E)) (n : ℕ) :
    IsDensity (partialTraceRight (lanePriorMatrix_B ρ.mat n)) := by
  rw [lanePriorMatrix_honest]
  exact lanePowerMatrixB_isDensity
    ⟨(honestMarginal ρ).positive, (honestMarginal ρ).normalized⟩ n

theorem preparedLaneInput_quantum_resource_le_bits {p k z : ℝ} {m d : ℕ}
    (C : OutputContinuity.FiniteSeedKeyCode p m d k)
    (hz0 : 0 < z) (hz1 : z < 1) (n : ℕ) :
    sandwichedEntanglement (1 / (1 - z))
      (lanePowerDimB n (C.seedSize * ((C.aliceAncillaSize * C.priorEveSize) *
        (C.seedSize * C.aliceAncillaSize))))
      (lanePowerDimB n (C.bobAncillaSize * (C.seedSize * C.bobAncillaSize)))
      (partialTraceRight (lanePriorMatrix_B (preparedInput C).mat n)) ≤
        (((n + 1 : ℕ) : ℝ) * k : EReal) := by
  rw [lanePriorMatrix_honest]
  have hden : 0 < 1 - z := sub_pos.mpr hz1
  have hα : 1 < 1 / (1 - z) := (lt_div_iff₀ hden).mpr (by linarith)
  exact lanePowerMatrixB_entanglement_le
    ⟨(honestMarginal (preparedInput C)).positive,
      (honestMarginal (preparedInput C)).normalized⟩
    hα
    (preparedInput_quantum_resource_le_bits C hz0 hz1) n

theorem preparedSchedulerInput_quantum_resource_le_bits {p k z : ℝ} {m d : ℕ}
    (C : OutputContinuity.FiniteSeedKeyCode p m d k)
    (hz0 : 0 < z) (hz1 : z < 1) (n : ℕ) :
    sandwichedEntanglement (1 / (1 - z))
      (lanePowerDimB n (C.seedSize * ((C.aliceAncillaSize * C.priorEveSize) *
        (C.seedSize * C.aliceAncillaSize))))
      (lanePowerDimB n (C.bobAncillaSize * (C.seedSize * C.bobAncillaSize)))
      (honestMarginal (density
        (LanePureKeyTransport.schedulerCoefficient (preparedCoefficient C) n)
        (LanePureKeyTransport.schedulerCoefficient_normalized (preparedCoefficient C)
          (preparedCoefficient_normalized C) n))).mat ≤
        (((n + 1 : ℕ) : ℝ) * k : EReal) := by
  change sandwichedEntanglement _ _ _ (partialTraceRight
    (density (LanePureKeyTransport.schedulerCoefficient (preparedCoefficient C) n)
      (LanePureKeyTransport.schedulerCoefficient_normalized (preparedCoefficient C)
        (preparedCoefficient_normalized C) n)).mat) ≤ _
  rw [LanePureKeyTransport.schedulerCoefficient_density_mat (preparedCoefficient C)
    (preparedCoefficient_normalized C) n,
    ← preparedInput_eq_density C]
  exact preparedLaneInput_quantum_resource_le_bits C hz0 hz1 n

section MatrixLaneKey

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol LanePureKeyTransport
open LaneFidelity OutputContinuity IndependentLanes

variable {p : ℝ} {a b af bf d n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
  {P : FiniteProtocol p a b af bf}
  {R : FiniteBlockProtocolB p (n + 1) (lanePowerDimB n a) (lanePowerDimB n b)
    (lanePowerDimB n af) (lanePowerDimB n bf)}

theorem independentLanes_keyG_pow_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hR : IndependentLanesDerivationB p P n R)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1) (hd : 0 < d) :
    optimalWholeKeySquaredFidelity d hd
      ((fromQuantum_B P).finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E
        (density C hC)) ^ (n + 1) ≤
    optimalWholeKeySquaredFidelity (laneAlphabet d (n + 1))
      (laneAlphabet_pos d hd (n + 1))
      ((blockExpansion_B R).finalKeyStateWithPriorEveLabels hp0 hp1
        (schedulerLabelA (n := n) labelA) (schedulerLabelB (n := n) labelB)
        (LaneEveRegister_B E n)
        (density (schedulerCoefficient C n) (schedulerCoefficient_normalized C hC n))) := by
  rcases independentLanes_pure_finalKeyState (E := E) hp0 hp1 hR labelA labelB with
    ⟨eH,eT,hK,hT,hO⟩
  rw [hO C hC, keyG_Eve_relabel]
  exact keyG_pow_le_keyLaneDensity _ hd (n + 1)

theorem log2_laneAlphabet (d N : ℕ) :
    log2 (laneAlphabet d N : ℝ) = (N : ℝ) * log2 (d : ℝ) := by
  rw [laneAlphabet_eq_pow, Nat.cast_pow]
  unfold log2
  rw [Real.log_pow]
  ring

theorem independentLanes_keyG_pow_le_of_retained_resource_le
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hR : IndependentLanesDerivationB p P n R)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1) (hd : 0 < d)
    (m : ℕ) (k c z : ℝ) (hz0 : 0 < z) (hz1 : z < 1)
    (hE : normalizedSEPEntanglement (1 / (1 - z))
      (honestMarginal ((PublicHistory.wholeRetainedChannelWithEve_B hp0 hp1
        (blockExpansion_B R) (LaneEveRegister_B E n)).onDensity
        (density (schedulerCoefficient C n) (schedulerCoefficient_normalized C hC n)))) ≤
      ((((n + 1 : ℕ) : ℝ) * k + (m : ℝ) * c : ℝ) : EReal)) :
    optimalWholeKeySquaredFidelity d hd
      ((fromQuantum_B P).finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E
        (density C hC)) ^ (n + 1) ≤
      (2 : ℝ) ^ (-z * (((n + 1 : ℕ) : ℝ) * log2 (d : ℝ) -
        ((n + 1 : ℕ) : ℝ) * k - (m : ℝ) * c)) := by
  have hden : 0 < 1 - z := sub_pos.mpr hz1
  have hα : 1 < 1 / (1 - z) := (lt_div_iff₀ hden).mpr (by linarith)
  have hratio : ((1 / (1 - z) - 1) / (1 / (1 - z))) = z := by
    field_simp [hden.ne']
    ring
  have htest := protocol_keyG_le_of_retained_resource_le hp0 hp1 (blockExpansion_B R)
    (schedulerLabelA (n := n) labelA) (schedulerLabelB (n := n) labelB)
    (schedulerCoefficient C n) (schedulerCoefficient_normalized C hC n)
    (laneAlphabet_pos d hd (n + 1)) hα hE
  have hpow := (independentLanes_keyG_pow_le hp0 hp1 hR labelA labelB C hC hd).trans
    (htest.trans (min_le_right _ _))
  rw [hratio, log2_laneAlphabet] at hpow
  have hexp : z * (((n + 1 : ℕ) : ℝ) * k + (m : ℝ) * c -
      ((n + 1 : ℕ) : ℝ) * log2 (d : ℝ)) =
      -z * (((n + 1 : ℕ) : ℝ) * log2 (d : ℝ) -
        ((n + 1 : ℕ) : ℝ) * k - (m : ℝ) * c) := by ring
  simpa only [hexp] using hpow

end MatrixLaneKey

section MatrixPublicResource

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol IndependentLanes

theorem retainedHonest_resource_le_copyPublic {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {N a b af bf : ℕ} (R : FiniteBlockProtocolB p N a b af bf)
    {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : Density ((Fin a × Fin b) × E)) (α : ℝ) :
    normalizedSEPEntanglement α
      (honestMarginal ((PublicHistory.wholeRetainedChannelWithEve_B hp0 hp1
        (blockExpansion_B R) E).onDensity ρ)) ≤
    sandwichedEntanglement α (Nat.card (R.publicHistory_B × Fin af))
      (Nat.card (R.publicHistory_B × Fin bf))
      (R.copyPublic.output (partialTraceRight ρ.mat)) := by
  rcases MatrixPublicCopy.exists_copyPublic_retained_honest_B (E := E) hp0 hp1 R with
    ⟨eA,eB,hO⟩
  have h := normalizedSEP_le_quantum_chart eA eB
    (honestMarginal ((PublicHistory.wholeRetainedChannelWithEve_B hp0 hp1
      (blockExpansion_B R) E).onDensity ρ)) α
  change normalizedSEPEntanglement α _ ≤ sandwichedEntanglement α _ _
    ((partialTraceRight ((PublicHistory.wholeRetainedChannelWithEve_B hp0 hp1
      (blockExpansion_B R) E).eval ρ.mat)).submatrix (eA.prodCongr eB) (eA.prodCongr eB)) at h
  rw [← hO ρ.mat] at h
  exact h

theorem preparedQuantum_calls_le {p k : ℝ} {m d : ℕ}
    (C : OutputContinuity.FiniteSeedKeyCode p m d k) :
    (toQuantum_B (preparedProtocol C)).calls ≤ m := by
  rw [toQuantum_calls_B]
  exact preparedProtocol_calls_le C

theorem preparedQuantum_keyG {p k : ℝ} {m d : ℕ}
    (C : OutputContinuity.FiniteSeedKeyCode p m d k)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hd : 0 < d) :
    optimalWholeKeySquaredFidelity d hd
      ((fromQuantum_B (toQuantum_B (preparedProtocol C))).finalKeyStateWithPriorEveLabels
        hp0 hp1 (preparedLabelA C) (preparedLabelB C) (Fin C.priorEveSize)
        (density (preparedCoefficient C) (preparedCoefficient_normalized C))) =
      optimalWholeKeySquaredFidelity d hd (C.output hp0 hp1) := by
  rw [fromQuantum_toQuantum_B, ← preparedInput_eq_density C]
  exact prepared_keyG C hp0 hp1 hd

end MatrixPublicResource

section PhysicalCodeLanes

open PhysicalProtocol PhysicalProtocol.FiniteKeyProtocol IndependentLanes LaneFidelity
open LanePureKeyTransport OutputContinuity MatrixTraceNorm UniformPaddingKeyTransport

variable {p k : ℝ} {m d : ℕ}

abbrev preparedAliceInputDim (C : FiniteSeedKeyCode p m d k) :=
  C.seedSize * ((C.aliceAncillaSize * C.priorEveSize) * (C.seedSize * C.aliceAncillaSize))
abbrev preparedBobInputDim (C : FiniteSeedKeyCode p m d k) :=
  C.bobAncillaSize * (C.seedSize * C.bobAncillaSize)
abbrev preparedAliceOutputDim (C : FiniteSeedKeyCode p m d k) :=
  C.seedSize * ((C.aliceAncillaSize * C.priorEveSize) * C.aliceFinalSize)
abbrev preparedBobOutputDim (C : FiniteSeedKeyCode p m d k) :=
  C.bobAncillaSize * C.bobFinalSize

theorem exists_codeLanes_keyG_power (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (C : FiniteSeedKeyCode p m d k) (hd : 0 < d) (n : ℕ) :
    ∃ R : FiniteBlockProtocolB p (n + 1)
        (lanePowerDimB n (preparedAliceInputDim C))
        (lanePowerDimB n (preparedBobInputDim C))
        (lanePowerDimB n (preparedAliceOutputDim C))
        (lanePowerDimB n (preparedBobOutputDim C)),
      R.calls ≤ m ∧ (blockExpansion_B R).calls ≤ (n + 1) * m ∧
      optimalWholeKeySquaredFidelity d hd (C.output hp0 hp1) ^ (n + 1) ≤
        optimalWholeKeySquaredFidelity (laneAlphabet d (n + 1))
          (laneAlphabet_pos d hd (n + 1))
          ((blockExpansion_B R).finalKeyStateWithPriorEveLabels hp0 hp1
            (schedulerLabelA (n := n) (preparedLabelA C))
            (schedulerLabelB (n := n) (preparedLabelB C))
            (LaneEveRegister_B (Fin C.priorEveSize) n)
            (density (schedulerCoefficient (preparedCoefficient C) n)
              (schedulerCoefficient_normalized (preparedCoefficient C)
                (preparedCoefficient_normalized C) n))) := by
  let P := toQuantum_B (preparedProtocol C)
  let ρ := density (preparedCoefficient C) (preparedCoefficient_normalized C)
  rcases exists_uniformPadding_keyG_B (E := Fin C.priorEveSize) hp0 hp1 hd P m
      (preparedQuantum_calls_le C) with ⟨Q,hQP,hQC,hQU,hQG⟩
  rcases Q.exists_uniform_lanes_with_derivationB hQU n with ⟨R,hR,hRC,hRU,hRN,hRO⟩
  refine ⟨R,hRC,?_,?_⟩
  · simpa only [blockExpansion_B, fromQuantum_calls_B] using hRN
  · have hG0 := (optimalWholeKeySquaredFidelity_mem_Icc d hd
      ((fromQuantum_B P).finalKeyStateWithPriorEveLabels hp0 hp1
        (preparedLabelA C) (preparedLabelB C) (Fin C.priorEveSize) ρ)).1
    have hMono := pow_le_pow_left₀ hG0
      (hQG (preparedLabelA C) (preparedLabelB C) ρ) (n + 1)
    have hLane := independentLanes_keyG_pow_le hp0 hp1 hR
      (preparedLabelA C) (preparedLabelB C) (preparedCoefficient C)
      (preparedCoefficient_normalized C) hd
    have h := hMono.trans hLane
    dsimp only [P, ρ] at h
    rw [preparedQuantum_keyG C hp0 hp1 hd] at h
    exact h

theorem quantumBudget_eq_channelBz {p z : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hz1 : z < 1) :
    converseBudget p z = channelBz p z := by
  unfold converseBudget
  rw [ite_eq_right hp0.ne', ite_eq_right hp1.ne, ite_eq_right hz1.ne]
  rfl

theorem preparedCodeLane_retained_resource_le {z : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (C : FiniteSeedKeyCode p m d k) (n : ℕ)
    (R : FiniteBlockProtocolB p (n + 1)
      (lanePowerDimB n (preparedAliceInputDim C))
      (lanePowerDimB n (preparedBobInputDim C))
      (lanePowerDimB n (preparedAliceOutputDim C))
      (lanePowerDimB n (preparedBobOutputDim C)))
    (hR : R.calls ≤ m) (hz0 : 0 < z) (hz1 : z < 1) :
    normalizedSEPEntanglement (1 / (1 - z))
      (honestMarginal ((PublicHistory.wholeRetainedChannelWithEve_B hp0.le hp1.le
        (blockExpansion_B R) (LaneEveRegister_B (Fin C.priorEveSize) n)).onDensity
        (density (schedulerCoefficient (preparedCoefficient C) n)
          (schedulerCoefficient_normalized (preparedCoefficient C)
            (preparedCoefficient_normalized C) n)))) ≤
      ((((n + 1 : ℕ) : ℝ) * k + (m : ℝ) * (((n + 1 : ℕ) : ℝ) * channelBz p z +
        (2 / z) * log2 (((n + 1 : ℕ) : ℝ) + 1)) : ℝ) : EReal) := by
  let D := density (schedulerCoefficient (preparedCoefficient C) n)
    (schedulerCoefficient_normalized (preparedCoefficient C) (preparedCoefficient_normalized C) n)
  have hD : IsDensity (partialTraceRight D.mat) :=
    ⟨(honestMarginal D).positive, (honestMarginal D).normalized⟩
  have hEin : sandwichedEntanglement (optimizedBlockOrderA z)
      (lanePowerDimB n (preparedAliceInputDim C))
      (lanePowerDimB n (preparedBobInputDim C)) (partialTraceRight D.mat) ≤
      (((n + 1 : ℕ) : ℝ) * k : EReal) := by
    simpa only [D, optimizedBlockOrderA, honestMarginal,
      preparedAliceInputDim, preparedBobInputDim] using
      preparedSchedulerInput_quantum_resource_le_bits C hz0 hz1 n
  have hCopyCalls : R.copyPublic.calls ≤ m := by
    rw [FiniteBlockProtocolB.copyPublic_calls]
    exact hR
  have hOut := R.copyPublic.sandwichedEntanglement_output_optimized_le_uniformA z
    (Nat.succ_pos n) hp0.le hp1.le hz0 hz1 hCopyCalls hD hEin
  rw [quantumBudget_eq_channelBz hp0 hp1 hz1] at hOut
  have hBridge := retainedHonest_resource_le_copyPublic hp0.le hp1.le R D (1 / (1 - z))
  simpa only [D, optimizedBlockOrderA, logTwo, log2] using hBridge.trans hOut

theorem code_keyG_finite_lane_power {z : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (C : FiniteSeedKeyCode p m d k)
    (hd : 0 < d) (hz0 : 0 < z) (hz1 : z < 1) (n : ℕ) :
    optimalWholeKeySquaredFidelity d hd (C.output hp0.le hp1.le) ^ (n + 1) ≤
      (2 : ℝ) ^ (-z * (((n + 1 : ℕ) : ℝ) * log2 (d : ℝ) -
        ((n + 1 : ℕ) : ℝ) * k - (m : ℝ) * (((n + 1 : ℕ) : ℝ) * channelBz p z +
          (2 / z) * log2 (((n + 1 : ℕ) : ℝ) + 1)))) := by
  rcases exists_codeLanes_keyG_power hp0.le hp1.le C hd n with ⟨R,hR,hCalls,hG⟩
  have hE := preparedCodeLane_retained_resource_le hp0 hp1 C n R hR hz0 hz1
  have hden : 0 < 1 - z := sub_pos.mpr hz1
  have hα : 1 < 1 / (1 - z) := (lt_div_iff₀ hden).mpr (by linarith)
  have hratio : ((1 / (1 - z) - 1) / (1 / (1 - z))) = z := by
    field_simp [hden.ne']
    ring
  have htest := protocol_keyG_le_of_retained_resource_le hp0.le hp1.le (blockExpansion_B R)
    (schedulerLabelA (n := n) (preparedLabelA C))
    (schedulerLabelB (n := n) (preparedLabelB C))
    (schedulerCoefficient (preparedCoefficient C) n)
    (schedulerCoefficient_normalized (preparedCoefficient C) (preparedCoefficient_normalized C) n)
    (laneAlphabet_pos d hd (n + 1)) hα hE
  have h := hG.trans (htest.trans (min_le_right _ _))
  rw [hratio, log2_laneAlphabet] at h
  have hexp : z * (((n + 1 : ℕ) : ℝ) * k + (m : ℝ) *
      (((n + 1 : ℕ) : ℝ) * channelBz p z + (2 / z) * log2 (((n + 1 : ℕ) : ℝ) + 1)) -
      ((n + 1 : ℕ) : ℝ) * log2 (d : ℝ)) =
      -z * (((n + 1 : ℕ) : ℝ) * log2 (d : ℝ) - ((n + 1 : ℕ) : ℝ) * k -
        (m : ℝ) * (((n + 1 : ℕ) : ℝ) * channelBz p z +
          (2 / z) * log2 (((n + 1 : ℕ) : ℝ) + 1))) := by ring
  simpa only [hexp] using h

theorem code_keyG_strong_converse {z : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (C : FiniteSeedKeyCode p m d k)
    (hd : 0 < d) (hz0 : 0 < z) (hz1 : z < 1) :
    optimalWholeKeySquaredFidelity d hd (C.output hp0.le hp1.le) ≤
      min 1 (strongExponentBound p z k m d) := by
  have hG := optimalWholeKeySquaredFidelity_mem_Icc d hd (C.output hp0.le hp1.le)
  apply LaneConverseLimit.strong_bound_of_finite_lane_overhead hG.1 hG.2 hz0
  intro N hN
  cases N with
  | zero => omega
  | succ n => exact code_keyG_finite_lane_power hp0 hp1 C hd hz0 hz1 n

section ActualOutputClosure

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem strong_bound_uniform_error {z : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hd : 0 < d) (hz0 : 0 < z) (hz1 : z < 1)
    (ρ τ : Density ((Fin d × Fin d) × E))
    (hτ : τ ∈ finiteSeedKeyOutputs hp0.le hp1.le m d k) {ε : ℝ}
    (herror : traceNorm (ρ.mat - τ.mat) ≤ ε) :
    optimalWholeKeySquaredFidelity d hd ρ ≤
      min 1 (strongExponentBound p z k m d + 2 * Real.sqrt ε) := by
  apply OutputContinuity.strong_bound_uniform_error hp0.le hp1.le m d hd k z _ ρ τ hτ herror
  intro C
  exact (code_keyG_strong_converse hp0 hp1 C hd hz0 hz1).trans (min_le_right _ _)

theorem strong_bound_on_operationalOutputs {z : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hd : 0 < d) (hz0 : 0 < z) (hz1 : z < 1)
    (ρ : Density ((Fin d × Fin d) × E))
    (hρ : ρ ∈ operationalSeedKeyOutputs hp0.le hp1.le m d k) :
    optimalWholeKeySquaredFidelity d hd ρ ≤ min 1 (strongExponentBound p z k m d) := by
  apply OutputContinuity.strong_bound_on_operationalOutputs hp0.le hp1.le m d hd k z _ ρ hρ
  intro C
  exact (code_keyG_strong_converse hp0 hp1 C hd hz0 hz1).trans (min_le_right _ _)

end ActualOutputClosure

end PhysicalCodeLanes

end QuantumProver.AmplitudeDamping.SecretKey.FiniteAdaptiveConverse
