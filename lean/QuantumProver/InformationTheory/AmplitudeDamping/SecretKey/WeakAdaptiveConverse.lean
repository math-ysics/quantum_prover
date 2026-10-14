import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.FiniteAdaptiveConverse
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.WeakResourceOrder
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.WeakPrivateTestResource
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.CoherentLaneOutput
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.WeakScalarLimit
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.WeakOutputClosure
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.WeakBinaryConjugate

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace QuantumProver.AmplitudeDamping.SecretKey.WeakAdaptiveConverse

open PhysicalPurification PhysicalProtocol PrivateTest PrivateTestResource
open FiniteCodeConverse FiniteAdaptiveConverse MatrixCoherentLaneOutput
open LanePureKeyTransport IndependentLanes OutputContinuity MatrixTraceNorm LaneMergeHistory
open QuantumProver.AmplitudeDamping.FiniteModel

variable {p k : ℝ} {m d : ℕ}

theorem normalizedSEPEntanglement_decidableEq_eq
    {A B : Type*} [Fintype A] [Fintype B]
    [hA : DecidableEq A] [hB : DecidableEq B]
    (dA : DecidableEq A) (dB : DecidableEq B) (alpha : ℝ) (rho : Density (A × B)) :
    @normalizedSEPEntanglement A B _ _ dA dB alpha rho =
      @normalizedSEPEntanglement A B _ _ hA hB alpha rho := by
  have hDA : dA = hA := Subsingleton.elim _ _
  have hDB : dB = hB := Subsingleton.elim _ _
  cases hDA
  cases hDB
  rfl

theorem normalizedSEPEntanglement_bound_decidableEq
    {A B : Type*} [Fintype A] [Fintype B]
    {dA : DecidableEq A} {dB : DecidableEq B}
    (newA : DecidableEq A) (newB : DecidableEq B)
    {alpha : ℝ} {rho : Density (A × B)} {e : EReal}
    (h : @normalizedSEPEntanglement A B _ _ dA dB alpha rho ≤ e) :
    @normalizedSEPEntanglement A B _ _ newA newB alpha rho ≤ e := by
  have hEq := normalizedSEPEntanglement_decidableEq_eq
    (hA := newA) (hB := newB) dA dB alpha rho
  exact hEq.symm.le.trans h

set_option backward.isDefEq.respectTransparency false in

theorem exists_protocol_lane_weak_resource
    {E : Type*} [Fintype E] [DecidableEq E] {a b af bf : ℕ} {alpha : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : FiniteProtocol p a b af bf)
    (hP : P.calls ≤ m) (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1)
    (hd : 0 < d) (n : ℕ) (hAlpha : 1 < alpha) :
    ∃ R : FiniteBlockProtocolB p (n+1) (lanePowerDimB n a) (lanePowerDimB n b)
        (lanePowerDimB n af) (lanePowerDimB n bf),
      R.calls ≤ m ∧
      ((((n+1 : ℕ) : ℝ) * WeakPrivateTestResource.weakTestLowerBound d
        (optimalWholeKeySquaredFidelity d hd
          ((fromQuantum_B P).finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E
            (density C hC))) : ℝ) : EReal) ≤
        normalizedSEPEntanglement alpha
          (honestMarginal ((PublicHistory.wholeRetainedChannelWithEve_B hp0 hp1
            (blockExpansion_B R) (LaneEveRegister_B E n)).onDensity
            (density (schedulerCoefficient C n) (schedulerCoefficient_normalized C hC n)))) := by
  let rho := density C hC
  let rhoHat := honestMarginal
    (((fromQuantum_B P).retainedProtocolPrivateLiftChannel
      (E := E) hp0 hp1 labelA labelB).onDensity rho)
  letI dAc : DecidableEq (Register (PhysicalLiftAlice_B (fromQuantum_B P) E d) (n+1)) :=
    registerDecidableEq _ (n+1)
  letI dBc : DecidableEq (Register (PhysicalLiftBob_B (fromQuantum_B P) d) (n+1)) :=
    registerDecidableEq _ (n+1)
  rcases exists_physical_coherent_lanes_B (E := E)
    hp0 hp1 P m hP n labelA labelB with
    ⟨Q,hPadding,hQC,hQU,R,hLanes,hR,hPhysical,j,kj,hkj,eT,hOutput⟩
  have hInput : physicalPriorLaneDensity_B rho n =
      density (schedulerCoefficient C n) (schedulerCoefficient_normalized C hC n) := by
    apply Density.eq_of_mat_eq
    rw [physicalPriorLaneDensity_mat_B, schedulerCoefficient_density_mat]
  have hResource := (hOutput rho).2 alpha hAlpha
  rw [hInput] at hResource
  have hResourceFixed := normalizedSEPEntanglement_bound_decidableEq dAc dBc hResource
  have hOrder := WeakResourceOrder.normalizedSEPUmegaki_le_normalizedSEPEntanglement
    (WeakPrivateTestResource.privacyLaneDensity rhoHat (n+1)) hAlpha
  have hExtensive := WeakPrivateTestResource.protocol_keyG_extensive_umegaki_weak_test
    hp0 hp1 (fromQuantum_B P) labelA labelB C hC hd (n+1)
  dsimp only [WeakPrivateTestResource.normalizedSEPUmegaki,
    WeakPrivateTestResource.umegakiBits, rhoHat, rho] at hExtensive hOrder
  exact ⟨R,hR,hExtensive.trans (hOrder.trans hResourceFixed)⟩

theorem code_keyG_finite_lane_weak {z : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (C : FiniteSeedKeyCode p m d k)
    (hd : 0 < d) (hz0 : 0 < z) (hz1 : z < 1) (n : ℕ) :
    (((n+1 : ℕ) : ℝ) * WeakPrivateTestResource.weakTestLowerBound d
      (optimalWholeKeySquaredFidelity d hd (C.output hp0.le hp1.le))) ≤
      ((n+1 : ℕ) : ℝ) * k + (m : ℝ) *
        (((n+1 : ℕ) : ℝ) * channelBz p z + (2/z) * log2 (((n+1 : ℕ) : ℝ)+1)) := by
  have hden : 0 < 1-z := sub_pos.mpr hz1
  have hAlpha : 1 < 1/(1-z) := (lt_div_iff₀ hden).mpr (by linarith)
  obtain ⟨R,hR,hTest⟩ := exists_protocol_lane_weak_resource
    hp0.le hp1.le (toQuantum_B (preparedProtocol C)) (preparedQuantum_calls_le C)
    (preparedLabelA C) (preparedLabelB C) (preparedCoefficient C)
    (preparedCoefficient_normalized C) hd n hAlpha
  rw [preparedQuantum_keyG C hp0.le hp1.le hd] at hTest
  exact EReal.coe_le_coe_iff.mp
    (hTest.trans (preparedCodeLane_retained_resource_le hp0 hp1 C n R hR hz0 hz1))

theorem code_keyG_weak_converse
    (hp0 : 0 < p) (hp1 : p < 1) (C : FiniteSeedKeyCode p m d k) (hd : 2 ≤ d) :
    WeakPrivateTestResource.weakTestLowerBound d
      (optimalWholeKeySquaredFidelity d (by omega) (C.output hp0.le hp1.le)) ≤
      k + (m : ℝ) * channelCZ p := by
  apply WeakScalarLimit.weak_bound_of_finite_lane_overhead_all_orders hp0 hp1
  intro z hz0 hz1 n
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ)+1 = 2 by norm_num] using
    code_keyG_finite_lane_weak hp0 hp1 C (by omega) hz0 hz1 n

theorem code_keyG_weak_entropy_converse
    (hp0 : 0 < p) (hp1 : p < 1) (C : FiniteSeedKeyCode p m d k) (hd : 2 ≤ d) :
    let G := optimalWholeKeySquaredFidelity d (by omega) (C.output hp0.le hp1.le)
    G * log2 (d : ℝ) - binaryEntropyBits G ≤ k + (m : ℝ) * channelCZ p := by
  have hG := optimalWholeKeySquaredFidelity_mem_Icc d (by omega) (C.output hp0.le hp1.le)
  exact (WeakBinaryConjugate.weak_binary_entropy_bound hd hG.1 hG.2).trans
    (code_keyG_weak_converse hp0 hp1 C hd)

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem weak_bound_on_operationalOutputs (hp0 : 0 < p) (hp1 : p < 1)
    (m d : ℕ) (hd : 2 ≤ d) (k : ℝ)
    (rho : Density ((Fin d × Fin d) × E))
    (hrho : rho ∈ operationalSeedKeyOutputs hp0.le hp1.le m d k) :
    WeakPrivateTestResource.weakTestLowerBound d
      (optimalWholeKeySquaredFidelity d (by omega) rho) ≤ k + (m : ℝ) * channelCZ p := by
  exact MatrixWeakOutputClosure.weak_bound_on_operationalOutputs hp0.le hp1.le m d
    (by omega) k (k + (m : ℝ) * channelCZ p)
    (fun C => code_keyG_weak_converse hp0 hp1 C hd) rho hrho

theorem weak_entropy_bound_on_operationalOutputs (hp0 : 0 < p) (hp1 : p < 1)
    (m d : ℕ) (hd : 2 ≤ d) (k : ℝ)
    (rho : Density ((Fin d × Fin d) × E))
    (hrho : rho ∈ operationalSeedKeyOutputs hp0.le hp1.le m d k) :
    let G := optimalWholeKeySquaredFidelity d (by omega) rho
    G * log2 (d : ℝ) - binaryEntropyBits G ≤ k + (m : ℝ) * channelCZ p := by
  have hG := optimalWholeKeySquaredFidelity_mem_Icc d (by omega) rho
  exact (WeakBinaryConjugate.weak_binary_entropy_bound hd hG.1 hG.2).trans
    (weak_bound_on_operationalOutputs hp0 hp1 m d hd k rho hrho)

end QuantumProver.AmplitudeDamping.SecretKey.WeakAdaptiveConverse
