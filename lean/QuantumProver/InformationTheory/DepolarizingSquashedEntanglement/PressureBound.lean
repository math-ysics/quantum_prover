import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.SquashingBounds

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
  ContinuousFunctionalCalculus Kronecker

namespace QuantumProver.DepolarizingSquashedEntanglement.PressureBound

def bellFidelity {E : Type*} [Fintype E]
    (ρ : QMatrix ((Qubit×Qubit)×E)) : ℝ :=
  (Matrix.trace (c1BellProjector*partialTraceRight ρ)).re

theorem bellProjector_eq_pureDensity : c1BellProjector=pureDensity bellKet := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [c1BellProjector,pureDensity,QuantumProver.WernerEndpoint.pureDensity,
      QuantumProver.WernerEndpoint.crossDensity,bellKet,Matrix.smul_apply,
      ← pow_two,splitterScale_complex_sq,Complex.star_def]

theorem bellProjector_square : c1BellProjector*c1BellProjector=c1BellProjector := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [c1BellProjector,pureDensity,QuantumProver.WernerEndpoint.pureDensity,
      QuantumProver.WernerEndpoint.crossDensity,Matrix.mul_apply,Fintype.sum_prod_type,
      Fin.sum_univ_succ,Matrix.smul_apply]

theorem bellProjector_isEffect :
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.IsEffect c1BellProjector := by
  refine ⟨c1BellProjector_posSemidef,?_⟩
  have he : ((1 : QMatrix (Qubit×Qubit))-c1BellProjector)*
      ((1 : QMatrix (Qubit×Qubit))-c1BellProjector)ᴴ=
        (1 : QMatrix (Qubit×Qubit))-c1BellProjector := by
    rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,c1BellProjector_posSemidef.1]
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,Matrix.one_mul,
      bellProjector_square]
    abel
  exact he ▸ Matrix.posSemidef_self_mul_conjTranspose
    ((1 : QMatrix (Qubit×Qubit))-c1BellProjector)

theorem bellFidelity_bounds {E : Type*} [Fintype E] [DecidableEq E]
    (ρ : Density ((Qubit×Qubit)×E)) :
    0 ≤ bellFidelity ρ.matrix ∧ bellFidelity ρ.matrix ≤ 1 := by
  have hρ : QuantumProver.SuperchannelDiscrimination.FlaggedStates.IsDensity
      (partialTraceRight ρ.matrix) :=
    ⟨partialTraceRight_positive ρ.positive,(partialTraceRight_trace ρ.matrix).trans ρ.trace_one⟩
  have h := QuantumProver.SuperchannelDiscrimination.FlaggedStates.acceptanceProbability_bounds
    hρ bellProjector_isEffect
  unfold QuantumProver.SuperchannelDiscrimination.FlaggedStates.acceptanceProbability at h
  rw [Matrix.trace_mul_comm] at h
  exact h

def pressureProfit {E : Type*} [Fintype E] [DecidableEq E]
    (ell : ℝ) (ρ : Density ((Qubit×Qubit)×E)) : ℝ :=
  ell*(bellFidelity ρ.matrix-1/2)-cmiNat ρ.matrix

def pressureValues (D : ℕ) (ell : ℝ) : Set ℝ :=
  {x | ∃ e : ℕ,e≤D ∧ ∃ ρ : Density ((Qubit×Qubit)×Fin e),x=pressureProfit ell ρ}

def cappedPressure (D : ℕ) (ell : ℝ) : ℝ := sSup (pressureValues D ell)

theorem pressureProfit_le_half {E : Type*} [Fintype E] [DecidableEq E]
    {ell : ℝ} (hell : 0 ≤ ell) (ρ : Density ((Qubit×Qubit)×E)) :
    pressureProfit ell ρ ≤ ell/2 := by
  have hf := (bellFidelity_bounds ρ).2
  have hi := cmiNat_nonneg_of_positive ρ.positive
  have hm := mul_le_mul_of_nonneg_left (by linarith only [hf] :
    bellFidelity ρ.matrix-1/2 ≤ (1/2 : ℝ)) hell
  unfold pressureProfit
  linarith only [hm,hi]

theorem pressureValues_bddAbove (D : ℕ) {ell : ℝ} (hell : 0 ≤ ell) :
    BddAbove (pressureValues D ell) := by
  refine ⟨ell/2,?_⟩
  rintro x ⟨e,he,ρ,rfl⟩
  exact pressureProfit_le_half hell ρ

def fixed16PressureDensity (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) :
    Density ((Qubit×Qubit)×Fin 16) :=
  postSquashingDensity (Identities.boundaryMixing_physical hδ hmax).1
    (Identities.boundaryMixing_physical hδ hmax).2 bellKet bellKet_normalized
    (fixed16SquashingFin δ hδ hmax)

theorem fixed16PressureDensity_fidelity (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) :
    bellFidelity (fixed16PressureDensity δ hδ hmax).matrix=1/2+δ := by
  have hp := Identities.boundaryMixing_physical hδ hmax
  change (Matrix.trace (c1BellProjector*partialTraceRight
    (postSquashing (boundaryMixing δ) bellKet (fixed16SquashingFin δ hδ hmax)))).re=_
  rw [postSquashing_AB,extendedInputKet_AB hp.1 hp.2,depolarizing_bell_density,
    ← bellProjector_eq_pureDensity]
  simp only [Matrix.mul_add,Matrix.mul_smul,Matrix.trace_add,Complex.add_re,
    bellProjector_square,Matrix.mul_one,Matrix.trace_smul,c1BellProjector_trace,
    smul_eq_mul,mul_one,Complex.ofReal_re]
  dsimp [boundaryMixing]
  ring

theorem fixed16PressureDensity_quadratic_upper :
    ∃ C : ℝ,0<C ∧ ∀ (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512),
      cmiNat (fixed16PressureDensity δ hδ hmax).matrix ≤ C*δ^2 := by
  obtain ⟨C,hC,hb⟩ := Fixed16FlagEntropy.boundaryOmegaHalfCMIBits_quadratic_upper
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2*Real.log 2*C,by positivity,?_⟩
  intro δ hδ hmax
  have hbit : cmiBits (postSquashing (boundaryMixing δ) bellKet
      (fixed16SquashingFin δ hδ hmax))/2 ≤ C*δ^2 := by
    rw [fixed16SquashingFin_Bell_cost]
    exact hb δ hδ hmax
  rw [cmiBits,div_div] at hbit
  have hn := (div_le_iff₀ (mul_pos hl (by norm_num : (0:ℝ)<2))).mp hbit
  change cmiNat (postSquashing (boundaryMixing δ) bellKet
    (fixed16SquashingFin δ hδ hmax)) ≤ _
  convert hn using 1 <;> ring

theorem fixed16Pressure_profit_lower {C : ℝ}
    (hbound : ∀ (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512),
      cmiNat (fixed16PressureDensity δ hδ hmax).matrix ≤ C*δ^2)
    {D : ℕ} (hD : 16 ≤ D) {ell : ℝ} (hell : 0 ≤ ell)
    (δ : ℝ) (hδ : 0 ≤ δ) (hmax : δ ≤ 21/512) :
    ell*δ-C*δ^2 ≤ cappedPressure D ell := by
  have hs : pressureProfit ell (fixed16PressureDensity δ hδ hmax) ≤ cappedPressure D ell :=
    le_csSup (pressureValues_bddAbove D hell)
      ⟨16,hD,fixed16PressureDensity δ hδ hmax,rfl⟩
  rw [pressureProfit,fixed16PressureDensity_fidelity] at hs
  have hc := hbound δ hδ hmax
  linarith only [hs,hc]

theorem cappedPressure_fixed16_quadratic_lower :
    ∃ c : ℝ,0<c ∧ ∃ ell0 : ℝ,0<ell0 ∧ ∀ D : ℕ,16≤D →
      ∀ ell : ℝ,0<ell → ell≤ell0 → c*ell^2 ≤ cappedPressure D ell := by
  obtain ⟨C,hC,hbound⟩ := fixed16PressureDensity_quadratic_upper
  refine ⟨1/(4*C),by positivity,2*C*(21/512),by positivity,?_⟩
  intro D hD ell hell hsmall
  have hden : 0 < 2*C := by positivity
  have hδ : 0 ≤ ell/(2*C) := (div_pos hell hden).le
  have hmax : ell/(2*C) ≤ 21/512 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hsmall]
  have hp := fixed16Pressure_profit_lower hbound hD hell.le (ell/(2*C)) hδ hmax
  calc
    (1/(4*C))*ell^2=ell*(ell/(2*C))-C*(ell/(2*C))^2 := by
      field_simp [hC.ne'] <;> ring
    _ ≤ _ := hp

theorem cappedPressure16_quadratic_lower :
    ∃ c : ℝ,0<c ∧ ∃ ell0 : ℝ,0<ell0 ∧ ∀ ell : ℝ,0<ell → ell≤ell0 →
      c*ell^2 ≤ cappedPressure 16 ell := by
  obtain ⟨c,hc,ell0,hell0,hb⟩ := cappedPressure_fixed16_quadratic_lower
  exact ⟨c,hc,ell0,hell0,hb 16 le_rfl⟩

end QuantumProver.DepolarizingSquashedEntanglement.PressureBound
