import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYCopyProtocol
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYAsymptoticComposition
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.SquashingBounds
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTensorRegularization
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYOneWaySeparation
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYRedistributionCode
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYCompositeTesting
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYBoundary

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker Topology

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYFaithfulnessAssembly

open BCYRelativeEntropy BCYOneWaySeparation

variable {A B E X Y : Type*} [Fintype A] [Fintype B] [Fintype E]
  [Fintype X] [Fintype Y] [DecidableEq A] [DecidableEq B] [DecidableEq E]
  [DecidableEq X] [DecidableEq Y]

def abDensity (tau : Density ((A × B) × E)) : Density (A × B) where
  matrix := partialTraceRight tau.matrix
  positive := partialTraceRight_positive tau.positive
  trace_one := (partialTraceRight_trace tau.matrix).trans tau.trace_one

def receiverEnvironment (tau : Density ((A × B) × E)) : Density (B × E) where
  matrix := traceFirst tau.matrix
  positive := traceFirst_positive tau.positive
  trace_one := (Fixed16FlagEntropy.traceFirst_trace tau.matrix).trans tau.trace_one

def senderEnvironment (tau : Density ((A × B) × E)) : Density (A × E) where
  matrix := traceMiddle tau.matrix
  positive := traceMiddle_positive tau.positive
  trace_one := (Fixed16FlagEntropy.traceMiddle_trace tau.matrix).trans tau.trace_one

def receiverCutEquiv : ((A × B) × E) ≃ (B × (E × A)) where
  toFun z := (z.1.2,(z.2,z.1.1))
  invFun z := ((z.2.2,z.1),z.2.1)
  left_inv := by rintro ⟨⟨a,b⟩,e⟩; rfl
  right_inv := by rintro ⟨b,⟨e,a⟩⟩; rfl

def receiverCut (tau : Density ((A × B) × E)) : Density (B × (E × A)) :=
  densityReindex receiverCutEquiv tau

def receiverCodeCut (tau : Density ((A × B) × E)) : Density (B × (A × E)) :=
  densityReindex (Equiv.prodCongr (Equiv.refl B) (Equiv.prodComm E A)) (receiverCut tau)

def swapABDensity (tau : Density ((A × B) × E)) : Density ((B × A) × E) :=
  densityReindex (Equiv.prodCongr (Equiv.prodComm A B) (Equiv.refl E)) tau

theorem swapABDensity_traceMiddle (tau : Density ((A × B) × E)) :
    traceMiddle (swapABDensity tau).matrix = traceFirst tau.matrix := by
  ext ⟨b,e⟩ ⟨c,f⟩
  rfl

theorem swapABDensity_traceFirst (tau : Density ((A × B) × E)) :
    traceFirst (swapABDensity tau).matrix = traceMiddle tau.matrix := by
  ext ⟨a,e⟩ ⟨c,f⟩
  rfl

theorem swapABDensity_environment (tau : Density ((A × B) × E)) :
    partialTraceLeft (swapABDensity tau).matrix = partialTraceLeft tau.matrix := by
  ext e f
  simp only [partialTraceLeft,QuantumProver.WernerEndpoint.partialTraceRight,Fintype.sum_prod_type]
  change (∑ b : B, ∑ a : A, tau.matrix ((a,b),e) ((a,b),f)) =
    ∑ a : A, ∑ b : B, tau.matrix ((a,b),e) ((a,b),f)
  exact Finset.sum_comm

theorem cmiNat_swapAB (tau : Density ((A × B) × E)) :
    cmiNat (swapABDensity tau).matrix = cmiNat tau.matrix := by
  have hs : entropyNat (swapABDensity tau).matrix = entropyNat tau.matrix :=
    entropyNat_reindex (Equiv.prodCongr (Equiv.prodComm A B) (Equiv.refl E)) tau.positive.1
  unfold cmiNat
  rw [swapABDensity_traceMiddle,swapABDensity_traceFirst,swapABDensity_environment,hs]
  ring

def copyEquiv (e : A ≃ X) : (n : ℕ) → CopyIndex A n ≃ CopyIndex X n
  | 0 => {
      toFun := fun _ => PUnit.unit
      invFun := fun _ => PUnit.unit
      left_inv := by intro z; cases z; rfl
      right_inv := by intro z; cases z; rfl }
  | n+1 => Equiv.prodCongr (copyEquiv e n) e

theorem tensorCopies_reindex (eA : A ≃ X) (eB : B ≃ Y)
    (rho : Density (A × B)) (n : ℕ) :
    tensorCopies (densityReindex (Equiv.prodCongr eA eB) rho) n =
      densityReindex (Equiv.prodCongr (copyEquiv eA n) (copyEquiv eB n)) (tensorCopies rho n) := by
  induction n with
  | zero =>
      apply density_ext
      ext ⟨a,b⟩ ⟨c,d⟩
      cases a; cases b; cases c; cases d
      rfl
  | succ n ih =>
      apply density_ext
      ext ⟨⟨a,i⟩,⟨b,j⟩⟩ ⟨⟨c,k⟩,⟨d,l⟩⟩
      have h := congrArg (fun sigma => sigma.matrix (a,b) (c,d)) ih
      change (tensorCopies (densityReindex (Equiv.prodCongr eA eB) rho) n).matrix
        (a,b) (c,d) * rho.matrix (eA.symm i,eB.symm j) (eA.symm k,eB.symm l) =
        (tensorCopies rho n).matrix
          ((copyEquiv eA n).symm a,(copyEquiv eB n).symm b)
          ((copyEquiv eA n).symm c,(copyEquiv eB n).symm d) *
          rho.matrix (eA.symm i,eB.symm j) (eA.symm k,eB.symm l)
      rw [h]
      rfl

theorem tensorEntanglementSequence_reindex (eA : A ≃ X) (eB : B ≃ Y)
    (rho : Density (A × B)) (n : ℕ) :
    tensorEntanglementSequence (densityReindex (Equiv.prodCongr eA eB) rho) n =
      tensorEntanglementSequence rho n := by
  unfold tensorEntanglementSequence
  rw [tensorCopies_reindex,relativeEntropyEntanglementReal_reindex]

theorem regularizedER_reindex (eA : A ≃ X) (eB : B ≃ Y)
    (rho : Density (A × B)) :
    regularizedRelativeEntropyEntanglementNat (densityReindex (Equiv.prodCongr eA eB) rho) =
      regularizedRelativeEntropyEntanglementNat rho := by
  have h : (fun n : ℕ => tensorEntanglementSequence
      (densityReindex (Equiv.prodCongr eA eB) rho) n/(n:ℝ)) =
      (fun n : ℕ => tensorEntanglementSequence rho n/(n:ℝ)) := by
    funext n
    rw [tensorEntanglementSequence_reindex]
  unfold regularizedRelativeEntropyEntanglementNat
  rw [h]

theorem receiverCodeCut_regularizedER (tau : Density ((A × B) × E)) :
    regularizedRelativeEntropyEntanglementNat (receiverCodeCut tau) =
      regularizedRelativeEntropyEntanglementNat (receiverCut tau) :=
  regularizedER_reindex (Equiv.refl B) (Equiv.prodComm E A) (receiverCut tau)

def receiverIncrementNat (tau : Density ((A × B) × E)) : ℝ :=
  regularizedRelativeEntropyEntanglementNat (receiverCut tau)-
    regularizedRelativeEntropyEntanglementNat (receiverEnvironment tau)

theorem separableDistance_nonneg (rho : Density (A × B)) :
    0 ≤ separableOneWayDistance rho := by
  unfold separableOneWayDistance
  apply le_csInf
  · exact ⟨_,marginalProduct rho,marginalProduct_isSeparable rho,rfl⟩
  · rintro v ⟨sigma,hsigma,rfl⟩
    exact oneWayNorm_difference_nonneg rho sigma

theorem oneWayNorm_difference_le_two (rho sigma : Density (A × B)) :
    oneWayNorm (rho.matrix-sigma.matrix) ≤ 2 := by
  unfold oneWayNorm
  apply csSup_le
  · exact ⟨_,1,1,trivialPOVM,rfl⟩
  · rintro v ⟨m,n,M,rfl⟩
    exact c1_oneWay_difference_variation_le_two M rho sigma

theorem separableDistance_le_two (rho : Density (A × B)) :
    separableOneWayDistance rho ≤ 2 :=
  (separableOneWayDistance_le rho (marginalProduct rho)
    (marginalProduct_isSeparable rho)).trans (oneWayNorm_difference_le_two rho _)

theorem closed_square_eighth_bound_of_strict {d x : ℝ} (hd : 0 ≤ d) (hx : 0 ≤ x)
    (hstrict : ∀ u : ℝ,0<u → u<d → u^2/8 ≤ x) : d^2/8 ≤ x := by
  by_cases hz : d=0
  · simpa [hz] using hx
  have hdpos : 0<d := lt_of_le_of_ne hd (Ne.symm hz)
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop := by
    have hm : ∀ n : ℕ,(n:ℝ) ≤ (n:ℝ)+1 := by intro n; linarith
    exact tendsto_atTop_mono hm tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => d/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  have hseq : Tendsto (fun n : ℕ => d-d/((n:ℝ)+1)) atTop (𝓝 d) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x:=d)).sub hzero
  have hsquare : Tendsto (fun n : ℕ => (d-d/((n:ℝ)+1))^2/8) atTop (𝓝 (d^2/8)) :=
    (hseq.pow 2).div_const 8
  apply le_of_tendsto_of_tendsto hsquare tendsto_const_nhds
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hden : (0:ℝ)<(n:ℝ)+1 := by positivity
  have hsmall : d/((n:ℝ)+1)<d := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith only [hdpos,hnpos]
  exact hstrict _ (sub_pos.mpr hsmall) (sub_lt_self d (div_pos hdpos hden))

theorem eighth_nat_bound_to_half_bits {d x : ℝ} (h : d^2/8 ≤ x) :
    d^2/(16*Real.log 2) ≤ x/(2*Real.log 2) := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hc := div_le_div_of_nonneg_right h (by positivity : (0:ℝ)≤2*Real.log 2)
  convert hc using 1 <;> field_simp [hl.ne'] <;> ring

theorem receiverCodeCut_discardMiddle (tau : Density ((A × B) × E)) :
    BCYNonlockability.discardMiddleDensity (receiverCodeCut tau) = receiverEnvironment tau := by
  apply density_ext
  ext i j
  rfl

theorem receiver_increment_le_code_rate
    {Dreg Freg Greg : ℕ → Type*}
    [∀ n, Fintype (Dreg n)] [∀ n, Fintype (Freg n)] [∀ n, Fintype (Greg n)]
    [∀ n, DecidableEq (Dreg n)] [∀ n, DecidableEq (Freg n)] [∀ n, DecidableEq (Greg n)]
    [∀ n, Nonempty (Dreg n)] [∀ n, Nonempty (Freg n)]
    (tau : Density ((A × B) × E))
    (C : ∀ n, BCYRedistributionCode.FiniteCode (CopyIndex A n) (CopyIndex E n)
      (Dreg n) (Freg n) (Greg n)) {q : ℝ}
    (hRecovery : Tendsto (fun n => (C n).recoveryError
      (BCYRedistributionCode.tripleCopies (receiverCodeCut tau) n)) atTop (𝓝 0))
    (hSide : Tendsto (fun n => (C n).sideError
      (BCYRedistributionCode.tripleCopies (receiverCodeCut tau) n)) atTop (𝓝 0))
    (hCommunication : Tendsto (fun n => (C n).communicationCost/(n:ℝ)) atTop (𝓝 q)) :
    receiverIncrementNat tau ≤ 2*q := by
  have h := BCYRedistributionCode.regularized_difference_le_communication_rate
    (receiverCodeCut tau) C hRecovery hSide hCommunication
  rw [receiverCodeCut_regularizedER,receiverCodeCut_discardMiddle] at h
  exact h

theorem all_receiver_rate_nonneg (tau : Density ((A × B) × E)) :
    0 ≤ BCYCompositeTesting.allEffectsTestingRateReal (receiverCut tau) := by
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_zero,BCYCompositeTesting.coe_allEffectsTestingRateReal]
  exact BCYCompositeTesting.allEffectsTestingRateNat_nonneg _

theorem all_receiver_rate_le_regularizedER (tau : Density ((A × B) × E)) :
    BCYCompositeTesting.allEffectsTestingRateReal (receiverCut tau) ≤
      regularizedRelativeEntropyEntanglementNat (receiverCut tau) :=
  BCYCompositeTesting.allEffectsTestingRateReal_le_regularizedER _

theorem abDensity_boundaryBell (delta : ℝ) (hdelta : 0 ≤ delta)
    (hmax : delta ≤ 21/512) (S : CPTP CanonicalEnvironment E) :
    abDensity (BCYBoundary.boundaryBellDensity delta hdelta hmax S) =
      BCYBoundary.boundaryBellABDensity delta hdelta hmax S := by
  apply density_ext
  rfl

theorem boundary_distance_squared_lower (delta : ℝ) (hdelta : 0 ≤ delta)
    (hmax : delta ≤ 21/512) (S : CPTP CanonicalEnvironment E) :
    delta^2/(9*Real.log 2) ≤
      (separableOneWayDistance
        (abDensity (BCYBoundary.boundaryBellDensity delta hdelta hmax S)))^2/(16*Real.log 2) := by
  rw [abDensity_boundaryBell]
  exact BCYBoundary.boundaryBellABDensity_separableOneWayDistance_squared_lower
    delta hdelta hmax S

theorem half_cmiBits_eq_nat (tau : Density ((A × B) × E)) :
    (1/2:ℝ)*cmiBits tau.matrix=cmiNat tau.matrix/(2*Real.log 2) := by
  rw [cmiBits]
  ring

theorem receiver_testing_environment (tau : Density ((A × B) × E)) :
    BCYAsymptoticComposition.environmentDensity (receiverCut tau) =
      receiverEnvironment tau := by
  apply density_ext
  ext i j
  rfl

theorem receiver_testing_pair (tau : Density ((A × B) × E)) :
    BCYAsymptoticComposition.partySwapDensity
      (BCYAsymptoticComposition.pairDensity (receiverCut tau)) = abDensity tau := by
  apply density_ext
  ext i j
  rfl

theorem receiverCodeCut_regroup (tau : Density ((A × B) × E)) :
    densityReindex (Equiv.prodAssoc B A E).symm (receiverCodeCut tau) =
      swapABDensity tau := by
  apply density_ext
  ext i j
  rfl

theorem receiverCodeCut_cmiNat (tau : Density ((A × B) × E)) :
    cmiNat (densityReindex (Equiv.prodAssoc B A E).symm (receiverCodeCut tau)).matrix =
      cmiNat tau.matrix := by
  rw [receiverCodeCut_regroup,cmiNat_swapAB]

def receiverTestingIncrementNat (tau : Density ((A × B) × E)) : ℝ :=
  BCYCompositeTesting.allEffectsTestingRateReal (receiverCut tau)-
    BCYCompositeTesting.allEffectsTestingRateReal (receiverEnvironment tau)

theorem oneWay_rate_nonneg (rho : Density (A × B)) :
    0 ≤ BCYAsymptoticComposition.oneWayTestingRateReal rho := by
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_zero,BCYAsymptoticComposition.coe_oneWayTestingRateReal]
  exact BCYAsymptoticComposition.oneWayTestingRateNat_nonneg _

theorem oneWay_rate_le_receiver_testing_increment (tau : Density ((A × B) × E)) :
    BCYAsymptoticComposition.oneWayTestingRateReal (abDensity tau) ≤
      receiverTestingIncrementNat tau := by
  have h := BCYAsymptoticComposition.allEffectsTestingRateReal_receiver_ge_sum
    (receiverCut tau)
  rw [receiver_testing_environment,receiver_testing_pair] at h
  unfold receiverTestingIncrementNat
  linarith only [h]

theorem receiver_testing_increment_nonneg (tau : Density ((A × B) × E)) :
    0 ≤ receiverTestingIncrementNat tau :=
  (oneWay_rate_nonneg (abDensity tau)).trans
    (oneWay_rate_le_receiver_testing_increment tau)

theorem oneWay_rate_le_ER_minus_allEnvironment (tau : Density ((A × B) × E)) :
    BCYAsymptoticComposition.oneWayTestingRateReal (abDensity tau) ≤
      regularizedRelativeEntropyEntanglementNat (receiverCut tau)-
        BCYCompositeTesting.allEffectsTestingRateReal (receiverEnvironment tau) := by
  have h := oneWay_rate_le_receiver_testing_increment tau
  have hc := all_receiver_rate_le_regularizedER tau
  unfold receiverTestingIncrementNat at h
  linarith only [h,hc]

theorem squashedInputValue_lower_of_all_costs (p : ℝ) {r : ℕ}
    (psi : (Fin r × Qubit) → ℂ) (L : ℝ)
    (h : ∀ e : ℕ,∀ S : CPTP CanonicalEnvironment (Fin e),
      L ≤ (1/2:ℝ)*cmiBits (postSquashing p psi S)) :
    L ≤ squashedInputValue p psi := by
  have hInf : 2*L ≤ sInf (inputCosts p psi) := by
    apply le_csInf (inputCosts_nonempty p psi)
    intro v hv
    rcases hv with ⟨e,S,rfl⟩
    have hs := h e S
    linarith only [hs]
  unfold squashedInputValue
  linarith only [hInf]

theorem bell_input_le_channel {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    squashedInputValue p bellKet ≤ channelSquashed p :=
  le_csSup (channelInputValues_bddAbove hp0 hp1) ⟨2,bellKet,bellKet_normalized,rfl⟩

theorem channelSquashed_lower_of_all_bell_costs {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (L : ℝ)
    (h : ∀ e : ℕ,∀ S : CPTP CanonicalEnvironment (Fin e),
      L ≤ (1/2:ℝ)*cmiBits (postSquashing p bellKet S)) :
    L ≤ channelSquashed p :=
  (squashedInputValue_lower_of_all_costs p bellKet L h).trans
    (bell_input_le_channel hp0 hp1)

theorem erReal_discardMiddle_le (rho : Density (B × (A × E))) :
    relativeEntropyEntanglementReal (BCYNonlockability.discardMiddleDensity rho) ≤
      relativeEntropyEntanglementReal rho := by
  have h := BCYRedistributionCode.erReal_localRight_mono
    (BCYRedistributionCode.discardRightChannel E A)
    (densityReindex (Equiv.prodCongr (Equiv.refl B) (Equiv.prodComm A E)) rho)
  rw [BCYRedistributionCode.local_discard_density,
    relativeEntropyEntanglementReal_reindex] at h
  exact h

theorem regularizedER_discardMiddle_le (rho : Density (B × (A × E))) :
    regularizedRelativeEntropyEntanglementNat (BCYNonlockability.discardMiddleDensity rho) ≤
      regularizedRelativeEntropyEntanglementNat rho := by
  apply le_of_tendsto_of_tendsto
    (tendsto_relativeEntropyEntanglement_rate (BCYNonlockability.discardMiddleDensity rho))
    (BCYRedistributionCode.tendsto_erReal_tripleCopies_rate rho)
  apply Filter.Eventually.of_forall
  intro n
  have h := erReal_discardMiddle_le (BCYRedistributionCode.tripleCopies rho n)
  rw [BCYRedistributionCode.discardMiddle_tripleCopies] at h
  exact div_le_div_of_nonneg_right h (Nat.cast_nonneg n)

theorem receiver_increment_nonneg (tau : Density ((A × B) × E)) :
    0 ≤ receiverIncrementNat tau := by
  have h := regularizedER_discardMiddle_le (receiverCodeCut tau)
  rw [receiverCodeCut_regularizedER,receiverCodeCut_discardMiddle] at h
  unfold receiverIncrementNat
  linarith only [h]

theorem oneWay_distance_squared_lower (rho : Density (A × B)) :
    (separableOneWayDistance rho)^2/8 ≤
      BCYAsymptoticComposition.oneWayTestingRateReal rho := by
  apply closed_square_eighth_bound_of_strict (separableDistance_nonneg rho)
    (oneWay_rate_nonneg rho)
  intro d hd0 hd
  have h := BCYCopyProtocol.oneWayTestingRateNat_ge_of_lt_distance rho hd0 hd
  rw [← BCYAsymptoticComposition.coe_oneWayTestingRateReal] at h
  exact EReal.coe_le_coe_iff.mp h

theorem distance_squared_le_receiver_testing_increment (tau : Density ((A × B) × E)) :
    (separableOneWayDistance (abDensity tau))^2/8 ≤ receiverTestingIncrementNat tau :=
  (oneWay_distance_squared_lower (abDensity tau)).trans
    (oneWay_rate_le_receiver_testing_increment tau)

theorem distance_squared_le_ER_minus_allEnvironment (tau : Density ((A × B) × E)) :
    (separableOneWayDistance (abDensity tau))^2/8 ≤
      regularizedRelativeEntropyEntanglementNat (receiverCut tau)-
        BCYCompositeTesting.allEffectsTestingRateReal (receiverEnvironment tau) :=
  (oneWay_distance_squared_lower (abDensity tau)).trans
    (oneWay_rate_le_ER_minus_allEnvironment tau)

theorem boundary_oneWay_testing_rate_lower (delta : ℝ) (hdelta : 0 ≤ delta)
    (hmax : delta ≤ 21/512) (S : CPTP CanonicalEnvironment E) :
    delta^2/(9*Real.log 2) ≤
      BCYAsymptoticComposition.oneWayTestingRateReal
        (abDensity (BCYBoundary.boundaryBellDensity delta hdelta hmax S))/(2*Real.log 2) := by
  exact (boundary_distance_squared_lower delta hdelta hmax S).trans
    (eighth_nat_bound_to_half_bits (oneWay_distance_squared_lower
      (abDensity (BCYBoundary.boundaryBellDensity delta hdelta hmax S))))

end QuantumProver.DepolarizingSquashedEntanglement.BCYFaithfulnessAssembly
