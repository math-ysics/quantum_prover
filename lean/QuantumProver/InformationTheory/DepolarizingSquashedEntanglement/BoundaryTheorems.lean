import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYFaithfulnessAssembly
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYPurification
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.Teleportation
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYGeneralizedStein
import QuantumProver.InformationTheory.QuantumRedistributionAchievability

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Matrix Set Filter
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.DepolarizingSquashedEntanglement.BoundaryTheorems

open BCYRelativeEntropy BCYFaithfulnessAssembly BCYOneWaySeparation

variable {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E]

theorem receiverCodeCut_sourceMarginal (tau : Density ((A × B) × E)) :
    BCYPurification.sourceMarginal (receiverCodeCut tau) = swapABDensity tau :=
  receiverCodeCut_regroup tau

theorem receiverCodeCut_sourceCMI (tau : Density ((A × B) × E)) :
    cmiNat (BCYPurification.sourceMarginal (receiverCodeCut tau)).matrix =
      cmiNat tau.matrix := by
  rw [receiverCodeCut_sourceMarginal, cmiNat_swapAB]

theorem unrestricted_lowNoise_isBigO :
    Asymptotics.IsBigO (𝓝[>] (0 : ℝ))
      (fun p : ℝ => channelSquashed p - lowNoiseProfile p) (fun p : ℝ => p) :=
  channelSquashed_lowNoise_isBigO

theorem unrestricted_channel_to_bell {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    channelSquashed p = squashedInputValue p bellKet :=
  Teleportation.channelSquashed_eq_bell hp0 hp1

theorem fixed16_same_map_maximum (delta : ℝ) (hdelta : 0 ≤ delta)
    (hmax : delta ≤ 21/512) :
    IsGreatest (fixed16MapHalfCosts delta hdelta hmax)
      (Fixed16FlagEntropy.boundaryOmegaHalfCMIBits delta) :=
  fixed16SameMapMaximum delta hdelta hmax

theorem fixed16_same_map_uniform_remainder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (delta : ℝ) (hdelta : 0 ≤ delta) (hmax : delta ≤ 21/512),
      |cmiBits (postSquashing (boundaryMixing delta) bellKet
        (fixed16SquashingFin delta hdelta hmax))/2 -
        (3200*Scalar.boundaryKappa/(81*Real.log 2))*delta^2| ≤ C*delta^3 :=
  fixed16SameMapCost_uniform_remainder

theorem unrestricted_boundary_quadratic_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ delta : ℝ, 0 ≤ delta → delta ≤ 21/512 →
      channelSquashed (boundaryMixing delta) ≤ C*delta^2 :=
  channelSquashed_boundary_quadratic_upper

theorem capped_pressure_quadratic_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ ell0 : ℝ, 0 < ell0 ∧ ∀ D : ℕ, 16 ≤ D →
      ∀ ell : ℝ, 0 < ell → ell ≤ ell0 → c*ell^2 ≤ PressureBound.cappedPressure D ell :=
  PressureBound.cappedPressure_fixed16_quadratic_lower

theorem fixed16_core_Bell_fidelity :
    (Matrix.trace (c1BellProjector * Fixed16.coreXi)).re = (131/160 : ℝ) := by
  norm_num [Matrix.trace,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_two,
    c1BellProjector,pureDensity,QuantumProver.WernerEndpoint.pureDensity,QuantumProver.WernerEndpoint.crossDensity,
    Fixed16.coreXi,Fixed16.coreVector,Matrix.smul_apply,Matrix.add_apply,Matrix.one_apply,
    Matrix.vecMulVec_apply,RCLike.real_smul_eq_coe_mul,Complex.star_def]

theorem fixed16_core_oneWay_acceptance :
    (Matrix.trace (c1OneWayAccept * Fixed16.coreXi)).re = (211/240 : ℝ) := by
  have h := c1OneWayAccept_eq_fidelity Identities.coreDensity
  change (Matrix.trace (c1OneWayAccept * Fixed16.coreXi)).re =
    (1/3 : ℝ) + (2/3 : ℝ)*(Matrix.trace (c1BellProjector * Fixed16.coreXi)).re at h
  rw [fixed16_core_Bell_fidelity] at h
  norm_num at h ⊢
  exact h

theorem fixed16_core_not_separable : ¬ IsSeparable Fixed16.coreXi := by
  intro hsep
  have h := c1OneWayAccept_separable_le hsep
  rw [fixed16_core_oneWay_acceptance] at h
  norm_num at h

def fixed16CoreH (x y : ℝ) : ℝ :=
  entropyNat (Identities.tensorEnvironment x y Fixed16.coreXi)

def fixed16J (r : ℝ) : ℝ :=
  (fixed16CoreH 0 r + fixed16CoreH r 0 - fixed16CoreH r r - fixed16CoreH 0 0)/
    (2*Real.log 2)

theorem fixed16J_eq_matrix (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    fixed16J r = Identities.matrixCoreEntropyCombination r hr hr1/(2*Real.log 2) := by
  simp only [fixed16J,fixed16CoreH,Identities.matrixCoreEntropyCombination,
    Identities.dampedCoreDensity,Identities.tensorEnvironmentFamily_apply]

theorem fixed16J_seed_cost (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    cmiBits (partialTraceRight (Identities.seedDensity r hr hr1).matrix)/2 = fixed16J r :=
  (Identities.seed_cmiBits_eq_matrixCoreEntropyCombination r hr hr1).trans
    (fixed16J_eq_matrix r hr hr1).symm

theorem fixed16J_eq_scalar (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    fixed16J r = Fixed16Calculus.entropyCombination r/(2*Real.log 2) := by
  rw [fixed16J_eq_matrix r hr hr1,Identities.matrixCoreEntropyCombination_eq_scalar]

theorem fixed16J_uniform_r_remainder :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → r ≤ 1/4 →
      |fixed16J r - (Scalar.boundaryKappa/(2*Real.log 2))*r^2| ≤ C*r^3 := by
  obtain ⟨C,hC,hbound⟩ := Fixed16Calculus.entropyCombination_uniform_remainder
  have hl : 0 < 2*Real.log 2 := by positivity
  refine ⟨C/(2*Real.log 2),div_nonneg hC hl.le,?_⟩
  intro r hr hrq
  have hr1 : r ≤ 1 := hrq.trans (by norm_num)
  have he : fixed16J r - (Scalar.boundaryKappa/(2*Real.log 2))*r^2 =
      (Fixed16Calculus.entropyCombination r - Scalar.boundaryKappa*r^2)/(2*Real.log 2) := by
    rw [fixed16J_eq_scalar r hr hr1]
    ring
  rw [he,abs_div,abs_of_pos hl]
  calc
    _ ≤ (C*r^3)/(2*Real.log 2) := div_le_div_of_nonneg_right (hbound r hr hrq) hl.le
    _ = _ := by ring

theorem fixed16J_cubic_isBigO :
    Asymptotics.IsBigO (𝓝[>] (0 : ℝ))
      (fun r : ℝ => fixed16J r - (Scalar.boundaryKappa/(2*Real.log 2))*r^2)
      (fun r : ℝ => r^3) := by
  obtain ⟨C,hC,hbound⟩ := fixed16J_uniform_r_remainder
  apply Asymptotics.IsBigO.of_bound C
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < 1/4 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/4)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos,hsmall] with r hr hrq
  simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr.le 3)] using hbound r hr.le hrq.le

theorem fixed16_kappa_exact_positive :
    Scalar.boundaryKappa = (2059/5600 : ℝ)*Real.log 29 - 2171/5800 ∧
      0 < Scalar.boundaryKappa :=
  ⟨rfl,Scalar.boundaryKappa_pos⟩

theorem allEffectsTestingRateReal_eq_regularizedER (rho : Density (A × B)) :
    BCYCompositeTesting.allEffectsTestingRateReal rho =
      regularizedRelativeEntropyEntanglementNat rho := by
  classical
  obtain ⟨⟨a,b⟩⟩ := BCYNonlockability.density_nonempty rho
  exact @BCYGeneralizedStein.generalizedStein_allEffectsTestingRateReal
    A B _ _ _ _ ⟨a⟩ ⟨b⟩ rho

theorem distance_squared_le_receiver_increment (tau : Density ((A × B) × E)) :
    (separableOneWayDistance (abDensity tau))^2/8 ≤ receiverIncrementNat tau := by
  have h := distance_squared_le_ER_minus_allEnvironment tau
  rw [allEffectsTestingRateReal_eq_regularizedER] at h
  exact h

theorem receiver_increment_le_cmiNat (tau : Density ((A × B) × E)) :
    receiverIncrementNat tau ≤ cmiNat tau.matrix := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro x hx
  let q : ℝ := x/2
  have hq : cmiNat (BCYPurification.sourceMarginal (receiverCodeCut tau)).matrix/2 < q := by
    rw [receiverCodeCut_sourceCMI]
    dsimp [q]
    linarith only [hx]
  obtain ⟨t,ht,hstrict,C,hRecovery,hSide,hCommunication⟩ :=
    QuantumProver.QuantumRedistributionAchievability.exists_strict_physical_code_family
      (receiverCodeCut tau) q hq
  have h := receiver_increment_le_code_rate tau C hRecovery hSide hCommunication
  dsimp [q] at hstrict
  linarith only [h,hstrict]

theorem cmiNat_faithfulness (tau : Density ((A × B) × E)) :
    (separableOneWayDistance (abDensity tau))^2/8 ≤ cmiNat tau.matrix :=
  (distance_squared_le_receiver_increment tau).trans (receiver_increment_le_cmiNat tau)

theorem half_cmiBits_faithfulness (tau : Density ((A × B) × E)) :
    (separableOneWayDistance (abDensity tau))^2/(16*Real.log 2) ≤
      (1/2 : ℝ)*cmiBits tau.matrix := by
  rw [half_cmiBits_eq_nat]
  exact eighth_nat_bound_to_half_bits (cmiNat_faithfulness tau)

theorem boundary_every_finite_map_lower (delta : ℝ) (hdelta : 0 ≤ delta)
    (hmax : delta ≤ 21/512) (S : CPTP CanonicalEnvironment E) :
    delta^2/(9*Real.log 2) ≤ (1/2 : ℝ)*cmiBits (postSquashing (boundaryMixing delta) bellKet S) :=
  (boundary_distance_squared_lower delta hdelta hmax S).trans
    (half_cmiBits_faithfulness (BCYBoundary.boundaryBellDensity delta hdelta hmax S))

theorem unrestricted_boundary_lower (delta : ℝ) (hdelta : 0 ≤ delta)
    (hmax : delta ≤ 21/512) :
    delta^2/(9*Real.log 2) ≤ channelSquashed (boundaryMixing delta) := by
  have hp := Identities.boundaryMixing_physical hdelta hmax
  apply channelSquashed_lower_of_all_bell_costs hp.1 hp.2
  intro e S
  exact boundary_every_finite_map_lower delta hdelta hmax S

theorem unrestricted_boundary_two_sided :
    ∃ C : ℝ, 0 < C ∧ ∀ delta : ℝ, 0 ≤ delta → delta ≤ 21/512 →
      delta^2/(9*Real.log 2) ≤ channelSquashed (boundaryMixing delta) ∧
        channelSquashed (boundaryMixing delta) ≤ C*delta^2 := by
  obtain ⟨C,hC,hu⟩ := unrestricted_boundary_quadratic_upper
  exact ⟨C,hC,fun delta hdelta hmax =>
    ⟨unrestricted_boundary_lower delta hdelta hmax,hu delta hdelta hmax⟩⟩

theorem unrestricted_boundary_isTheta :
    Asymptotics.IsTheta (𝓝[>] (0 : ℝ))
      (fun delta : ℝ => channelSquashed (boundaryMixing delta)) (fun delta : ℝ => delta^2) := by
  obtain ⟨C,hC,hbound⟩ := unrestricted_boundary_two_sided
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ), 0 < delta := self_mem_nhdsWithin
  have hsmall : ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ), delta < 21/512 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 21/512)).filter_mono nhdsWithin_le_nhds
  constructor
  · apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hpos,hsmall] with delta hdelta hmax
    have h := hbound delta hdelta.le hmax.le
    have hvalue : 0 ≤ channelSquashed (boundaryMixing delta) :=
      (div_nonneg (sq_nonneg delta) (by positivity : (0 : ℝ) ≤ 9*Real.log 2)).trans h.1
    simpa only [Real.norm_eq_abs,abs_of_nonneg hvalue,abs_of_nonneg (sq_nonneg delta)] using h.2
  · apply Asymptotics.IsBigO.of_bound (9*Real.log 2)
    filter_upwards [hpos,hsmall] with delta hdelta hmax
    have h := (hbound delta hdelta.le hmax.le).1
    have hvalue : 0 ≤ channelSquashed (boundaryMixing delta) :=
      (div_nonneg (sq_nonneg delta) (by positivity : (0 : ℝ) ≤ 9*Real.log 2)).trans h
    have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < 9*Real.log 2)).mp h
    simpa only [Real.norm_eq_abs,abs_of_nonneg hvalue,abs_of_nonneg (sq_nonneg delta),mul_comm] using hmul

end QuantumProver.DepolarizingSquashedEntanglement.BoundaryTheorems
