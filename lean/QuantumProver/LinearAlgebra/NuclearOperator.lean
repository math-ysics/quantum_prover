import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false

noncomputable section

open Filter
open scoped BigOperators Topology lp Classical ENNReal

namespace QuantumProver.NuclearOperator

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

abbrev Atom (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] :=
  {φ : E →L[𝕜] 𝕜 // ‖φ‖ ≤ 1} × {y : F // ‖y‖ ≤ 1}

abbrev Coefficients (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] :=
  ℓ¹(Atom 𝕜 E F, 𝕜)

def atomOperator (a : Atom 𝕜 E F) : E →L[𝕜] F := a.1.1.smulRight a.2.1

@[simp] theorem atomOperator_apply (a : Atom 𝕜 E F) (x : E) :
    atomOperator a x = a.1.1 x • a.2.1 := rfl

theorem norm_atomOperator_le_one (a : Atom 𝕜 E F) : ‖atomOperator a‖ ≤ 1 := by
  rw [atomOperator, ContinuousLinearMap.norm_smulRight_apply]
  calc
    ‖a.1.1‖ * ‖a.2.1‖ ≤ 1 * 1 := mul_le_mul a.1.2 a.2.2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

def terms : Coefficients 𝕜 E F →L[𝕜] ℓ¹(Atom 𝕜 E F, E →L[𝕜] F) :=
  lp.mapCLM 1 (fun a => ContinuousLinearMap.toSpanSingleton 𝕜 (atomOperator a))
    zero_le_one (fun a => by simpa using norm_atomOperator_le_one a)

@[simp] theorem terms_apply (c : Coefficients 𝕜 E F) (a : Atom 𝕜 E F) :
    terms c a = c a • atomOperator a := by
  simp [terms]

theorem norm_terms_le_one : ‖terms (𝕜 := 𝕜) (E := E) (F := F)‖ ≤ 1 :=
  lp.norm_mapCLM_le 1
    (fun a => ContinuousLinearMap.toSpanSingleton 𝕜 (atomOperator a))
    zero_le_one (fun a => by simpa using norm_atomOperator_le_one a)

def synthesis : Coefficients 𝕜 E F →L[𝕜] (E →L[𝕜] F) :=
  lp.tsumCLM 𝕜 (Atom 𝕜 E F) (E →L[𝕜] F) ∘L terms

@[simp] theorem synthesis_apply (c : Coefficients 𝕜 E F) :
    synthesis c = ∑' a, c a • atomOperator a := by
  simp [synthesis]

theorem norm_synthesis_le_one : ‖synthesis (𝕜 := 𝕜) (E := E) (F := F)‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc
    ‖lp.tsumCLM 𝕜 (Atom 𝕜 E F) (E →L[𝕜] F)‖ * ‖terms (𝕜 := 𝕜) (E := E) (F := F)‖
        ≤ 1 * 1 := mul_le_mul lp.norm_tsumCLM_le
          norm_terms_le_one (norm_nonneg (terms (𝕜 := 𝕜) (E := E) (F := F))) zero_le_one
    _ = 1 := one_mul _

theorem norm_synthesis_apply_le (c : Coefficients 𝕜 E F) : ‖synthesis c‖ ≤ ‖c‖ := by
  simpa using (synthesis (𝕜 := 𝕜) (E := E) (F := F)).le_of_opNorm_le norm_synthesis_le_one c

def synthesisKernel : Submodule 𝕜 (Coefficients 𝕜 E F) := synthesis.ker

instance synthesisKernel_isClosed :
    IsClosed (synthesisKernel (𝕜 := 𝕜) (E := E) (F := F) : Set (Coefficients 𝕜 E F)) :=
  (synthesis (𝕜 := 𝕜) (E := E) (F := F)).isClosed_ker

abbrev Nuclear (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] :=
  Coefficients 𝕜 E F ⧸ synthesisKernel (𝕜 := 𝕜) (E := E) (F := F)

def ofCoefficients : Coefficients 𝕜 E F →L[𝕜] Nuclear 𝕜 E F := synthesisKernel.mkQL

def toOperator : Nuclear 𝕜 E F →L[𝕜] (E →L[𝕜] F) :=
  synthesisKernel.liftQL synthesis le_rfl

@[simp] theorem toOperator_ofCoefficients (c : Coefficients 𝕜 E F) :
    toOperator (ofCoefficients c) = synthesis c := rfl

theorem toOperator_injective :
    Function.Injective (toOperator (𝕜 := 𝕜) (E := E) (F := F)) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ le_rfl le_rfl

theorem ofCoefficients_surjective :
    Function.Surjective (ofCoefficients (𝕜 := 𝕜) (E := E) (F := F)) :=
  Submodule.mkQ_surjective _

theorem norm_ofCoefficients_le (c : Coefficients 𝕜 E F) : ‖ofCoefficients c‖ ≤ ‖c‖ :=
  Submodule.Quotient.norm_mk_le _ c

theorem exists_representation_norm_lt (T : Nuclear 𝕜 E F) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : Coefficients 𝕜 E F, ofCoefficients c = T ∧ ‖c‖ < ‖T‖ + ε :=
  Submodule.Quotient.norm_mk_lt T hε

theorem norm_toOperator_le (T : Nuclear 𝕜 E F) : ‖toOperator T‖ ≤ ‖T‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨c, rfl, hc⟩ := exists_representation_norm_lt T hε
  exact (norm_synthesis_apply_le c).trans hc.le

theorem norm_eq_sInf_representation_cost (T : Nuclear 𝕜 E F) :
    ‖T‖ = sInf {r : ℝ | ∃ c : Coefficients 𝕜 E F,
      ofCoefficients c = T ∧ r = ‖c‖} := by
  have hne : {r : ℝ | ∃ c : Coefficients 𝕜 E F,
      ofCoefficients c = T ∧ r = ‖c‖}.Nonempty := by
    obtain ⟨c, hc⟩ := ofCoefficients_surjective T
    exact ⟨‖c‖, c, hc, rfl⟩
  have hbelow : BddBelow {r : ℝ | ∃ c : Coefficients 𝕜 E F,
      ofCoefficients c = T ∧ r = ‖c‖} := by
    refine ⟨0, ?_⟩
    rintro r ⟨c, hc, rfl⟩
    exact norm_nonneg c
  apply le_antisymm
  · apply le_csInf hne
    rintro r ⟨c, rfl, rfl⟩
    exact norm_ofCoefficients_le c
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨c, hc, hcost⟩ := exists_representation_norm_lt T hε
    exact (csInf_le hbelow ⟨c, hc, rfl⟩).trans hcost.le

theorem synthesis_single (a : Atom 𝕜 E F) (c : 𝕜) :
    synthesis (lp.single 1 a c : Coefficients 𝕜 E F) = c • atomOperator a := by
  classical
  rw [synthesis_apply, tsum_eq_single a]
  · simp
  · intro b hba
    simp [lp.single_apply, Pi.single_eq_of_ne hba]

def ofAtom (a : Atom 𝕜 E F) : Nuclear 𝕜 E F :=
  ofCoefficients (lp.single 1 a (1 : 𝕜))

@[simp] theorem toOperator_ofAtom (a : Atom 𝕜 E F) :
    toOperator (ofAtom a) = atomOperator a := by
  rw [ofAtom, toOperator_ofCoefficients, synthesis_single, one_smul]

theorem norm_ofAtom_le_one (a : Atom 𝕜 E F) : ‖ofAtom a‖ ≤ 1 := by
  classical
  simpa [ofAtom, lp.norm_single (by simp : (0 : ℝ≥0∞) < 1)] using
    norm_ofCoefficients_le (lp.single 1 a (1 : 𝕜) : Coefficients 𝕜 E F)

theorem ofCoefficients_single (a : Atom 𝕜 E F) (c : 𝕜) :
    ofCoefficients (lp.single 1 a c : Coefficients 𝕜 E F) = c • ofAtom a := by
  classical
  rw [ofAtom, ← map_smul, ← lp.single_smul]
  simp

section Normalization

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

def normalizedVector (v : V) : V := (‖v‖ : 𝕜)⁻¹ • v

theorem norm_normalizedVector_le_one (v : V) : ‖normalizedVector (𝕜 := 𝕜) v‖ ≤ 1 := by
  rw [normalizedVector, norm_smul, norm_inv, RCLike.norm_of_nonneg (norm_nonneg v)]
  by_cases hv : v = 0
  · simp [hv]
  · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem normalizedVector_reconstitute (v : V) :
    (‖v‖ : 𝕜) • normalizedVector (𝕜 := 𝕜) v = v := by
  by_cases hv : v = 0
  · simp [normalizedVector, hv]
  · rw [normalizedVector, smul_smul,
      mul_inv_cancel₀ (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)), one_smul]

end Normalization

def normalizedAtom (φ : E →L[𝕜] 𝕜) (y : F) : Atom 𝕜 E F :=
  (⟨normalizedVector (𝕜 := 𝕜) φ, norm_normalizedVector_le_one (𝕜 := 𝕜) φ⟩,
    ⟨normalizedVector (𝕜 := 𝕜) y, norm_normalizedVector_le_one (𝕜 := 𝕜) y⟩)

def rankOne (φ : E →L[𝕜] 𝕜) (y : F) : Nuclear 𝕜 E F :=
  ((‖φ‖ : 𝕜) * (‖y‖ : 𝕜)) • ofAtom (normalizedAtom φ y)

@[simp] theorem toOperator_rankOne (φ : E →L[𝕜] 𝕜) (y : F) :
    toOperator (rankOne φ y) = φ.smulRight y := by
  rw [rankOne, map_smul, toOperator_ofAtom]
  ext x
  change ((‖φ‖ : 𝕜) * (‖y‖ : 𝕜)) •
      ((normalizedVector (𝕜 := 𝕜) φ) x • normalizedVector (𝕜 := 𝕜) y) = φ x • y
  calc
    ((‖φ‖ : 𝕜) * (‖y‖ : 𝕜)) •
        ((normalizedVector (𝕜 := 𝕜) φ) x • normalizedVector (𝕜 := 𝕜) y)
        = ((‖φ‖ : 𝕜) • (normalizedVector (𝕜 := 𝕜) φ) x) •
            ((‖y‖ : 𝕜) • normalizedVector (𝕜 := 𝕜) y) := by
              simp only [smul_smul, smul_eq_mul]
              congr 1
              ring
    _ = φ x • y := by
      rw [← ContinuousLinearMap.smul_apply, normalizedVector_reconstitute,
        normalizedVector_reconstitute]

theorem norm_rankOne_le (φ : E →L[𝕜] 𝕜) (y : F) : ‖rankOne φ y‖ ≤ ‖φ‖ * ‖y‖ := by
  rw [rankOne, norm_smul, norm_mul,
    RCLike.norm_of_nonneg (norm_nonneg φ), RCLike.norm_of_nonneg (norm_nonneg y)]
  simpa using mul_le_mul_of_nonneg_left (norm_ofAtom_le_one (normalizedAtom φ y))
    (mul_nonneg (norm_nonneg φ) (norm_nonneg y))

theorem norm_rankOne (φ : E →L[𝕜] 𝕜) (y : F) : ‖rankOne φ y‖ = ‖φ‖ * ‖y‖ := by
  apply le_antisymm (norm_rankOne_le φ y)
  calc
    ‖φ‖ * ‖y‖ = ‖φ.smulRight y‖ := (ContinuousLinearMap.norm_smulRight_apply φ y).symm
    _ = ‖toOperator (rankOne φ y)‖ := by rw [toOperator_rankOne]
    _ ≤ ‖rankOne φ y‖ := norm_toOperator_le _

theorem summable_rankOne {ι : Type*} (φ : ι → E →L[𝕜] 𝕜) (y : ι → F)
    (h : Summable (fun i => ‖φ i‖ * ‖y i‖)) :
    Summable (fun i => rankOne (φ i) (y i)) :=
  h.of_norm_bounded (fun i => norm_rankOne_le (φ i) (y i))

def ofSeries {ι : Type*} (φ : ι → E →L[𝕜] 𝕜) (y : ι → F)
    (_h : Summable (fun i => ‖φ i‖ * ‖y i‖)) : Nuclear 𝕜 E F :=
  ∑' i, rankOne (φ i) (y i)

theorem hasSum_rankOne {ι : Type*} (φ : ι → E →L[𝕜] 𝕜) (y : ι → F)
    (h : Summable (fun i => ‖φ i‖ * ‖y i‖)) :
    HasSum (fun i => rankOne (φ i) (y i)) (ofSeries φ y h) :=
  (summable_rankOne φ y h).hasSum

@[simp] theorem toOperator_ofSeries {ι : Type*} (φ : ι → E →L[𝕜] 𝕜) (y : ι → F)
    (h : Summable (fun i => ‖φ i‖ * ‖y i‖)) :
    toOperator (ofSeries φ y h) = ∑' i, (φ i).smulRight (y i) := by
  rw [ofSeries, ContinuousLinearMap.map_tsum _ (summable_rankOne φ y h)]
  simp

theorem norm_ofSeries_le {ι : Type*} (φ : ι → E →L[𝕜] 𝕜) (y : ι → F)
    (h : Summable (fun i => ‖φ i‖ * ‖y i‖)) :
    ‖ofSeries φ y h‖ ≤ ∑' i, ‖φ i‖ * ‖y i‖ := by
  have hn : Summable (fun i => ‖rankOne (φ i) (y i)‖) := by simpa [norm_rankOne] using h
  simpa [ofSeries, norm_rankOne] using norm_tsum_le_tsum_norm hn

theorem hasSum_ofCoefficients (c : Coefficients 𝕜 E F) :
    HasSum (fun a => c a • ofAtom a) (ofCoefficients c) := by
  simpa only [ofCoefficients_single] using
    (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) c).mapL
      (ofCoefficients (𝕜 := 𝕜) (E := E) (F := F))

def finiteApproximation (c : Coefficients 𝕜 E F) (s : Finset (Atom 𝕜 E F)) : Nuclear 𝕜 E F :=
  ∑ a ∈ s, c a • ofAtom a

@[simp] theorem toOperator_finiteApproximation (c : Coefficients 𝕜 E F)
    (s : Finset (Atom 𝕜 E F)) :
    toOperator (finiteApproximation c s) = ∑ a ∈ s, c a • atomOperator a := by
  simp [finiteApproximation]

theorem finiteApproximation_range_le_span (c : Coefficients 𝕜 E F)
    (s : Finset (Atom 𝕜 E F)) :
    (toOperator (finiteApproximation c s)).toLinearMap.range ≤
      Submodule.span 𝕜 ((fun a : Atom 𝕜 E F => a.2.1) '' (s : Set (Atom 𝕜 E F))) := by
  rintro z ⟨x, rfl⟩
  change toOperator (finiteApproximation c s) x ∈ _
  rw [toOperator_finiteApproximation]
  simp only [sum_apply, ContinuousLinearMap.smul_apply, atomOperator_apply, smul_smul]
  apply Submodule.sum_mem
  intro a ha
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)

theorem finiteApproximation_finiteRank (c : Coefficients 𝕜 E F)
    (s : Finset (Atom 𝕜 E F)) :
    FiniteDimensional 𝕜 (toOperator (finiteApproximation c s)).toLinearMap.range := by
  letI := FiniteDimensional.span_of_finite 𝕜
    (s.finite_toSet.image (fun a : Atom 𝕜 E F => a.2.1))
  exact Submodule.finiteDimensional_of_le (finiteApproximation_range_le_span c s)

theorem finiteApproximation_tendsto (c : Coefficients 𝕜 E F) :
    Tendsto (finiteApproximation c) atTop (𝓝 (ofCoefficients c)) :=
  hasSum_ofCoefficients c

theorem exists_finiteRank_norm_lt (T : Nuclear 𝕜 E F) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Nuclear 𝕜 E F,
      FiniteDimensional 𝕜 (toOperator S).toLinearMap.range ∧ ‖T - S‖ < ε := by
  obtain ⟨c, rfl⟩ := ofCoefficients_surjective T
  obtain ⟨s, hs⟩ := ((Metric.tendsto_nhds.1 (finiteApproximation_tendsto c)) ε hε).exists
  refine ⟨finiteApproximation c s, finiteApproximation_finiteRank c s, ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hs

theorem dense_finiteRank : Dense {T : Nuclear 𝕜 E F |
    FiniteDimensional 𝕜 (toOperator T).toLinearMap.range} := by
  rw [Metric.dense_iff]
  intro T ε hε
  obtain ⟨S, hS, hs⟩ := exists_finiteRank_norm_lt T hε
  exact ⟨S, by simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hs, hS⟩

end QuantumProver.NuclearOperator
