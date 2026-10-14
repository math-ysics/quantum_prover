import Mathlib

open Filter Set
open scoped Topology

namespace QuantumProver.EntanglementAssistedEndpoint.Closure

def grossRectangle (cost rate : ℝ) : Set (ℝ × ℝ) :=
  {x | cost ≤ x.1 ∧ 0 ≤ x.2 ∧ x.2 ≤ rate}

def rawGrossRegion {ι : Type*} (cost rate : ι → ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ i, x ∈ grossRectangle (cost i) (rate i)}

theorem endpoint_cost_le_of_mem_closure
    {S : Set (ℝ × ℝ)} {C beta e : ℝ} {m : ℝ → ℝ}
    (hcap : ∀ x ∈ S, x.2 ≤ C)
    (hbound : ∀ x ∈ S, beta - m (C - x.2) ≤ x.1)
    (hm : Tendsto m (𝓝[Set.Ici 0] 0) (𝓝 0))
    (he : (e, C) ∈ closure S) : beta ≤ e := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp he
  have hfst : Tendsto (fun n => (u n).1) atTop (𝓝 e) :=
    continuous_fst.continuousAt.tendsto.comp hlim
  have hsnd : Tendsto (fun n => (u n).2) atTop (𝓝 C) :=
    continuous_snd.continuousAt.tendsto.comp hlim
  have hdeficit : Tendsto (fun n => C - (u n).2) atTop (𝓝[Set.Ici 0] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
      simpa using hconst.sub hsnd
    · exact Eventually.of_forall fun n => sub_nonneg.mpr (hcap (u n) (hu n))
  have hmlim := hm.comp hdeficit
  have hle : beta - 0 ≤ e :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds.sub hmlim) hfst
      (Eventually.of_forall fun n => hbound (u n) (hu n))
  simpa using hle

theorem rate_le_of_mem_closure {S : Set (ℝ × ℝ)} {C : ℝ}
    (hcap : ∀ x ∈ S, x.2 ≤ C) {x : ℝ × ℝ} (hx : x ∈ closure S) : x.2 ≤ C := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hx
  exact le_of_tendsto (continuous_snd.continuousAt.tendsto.comp hlim)
    (Eventually.of_forall fun n => hcap (u n) (hu n))

theorem rawGrossRegion_cost_bound {ι : Type*} {cost rate : ι → ℝ}
    {C beta : ℝ} {m : ℝ → ℝ} (hm : MonotoneOn m (Set.Ici 0))
    (hcap : ∀ i, rate i ≤ C)
    (hcost : ∀ i, beta - m (C - rate i) ≤ cost i)
    {x : ℝ × ℝ} (hx : x ∈ rawGrossRegion cost rate) :
    beta - m (C - x.2) ≤ x.1 := by
  obtain ⟨i, hicost, _, hirate⟩ := hx
  have hmi : m (C - rate i) ≤ m (C - x.2) :=
    hm (sub_nonneg.mpr (hcap i))
      (sub_nonneg.mpr (hirate.trans (hcap i))) (sub_le_sub_left hirate C)
  linarith [hcost i]

theorem rawGrossRegion_rate_bound {ι : Type*} {cost rate : ι → ℝ}
    {C : ℝ} (hcap : ∀ i, rate i ≤ C) {x : ℝ × ℝ}
    (hx : x ∈ rawGrossRegion cost rate) : x.2 ≤ C := by
  obtain ⟨i, _, _, hirate⟩ := hx
  exact hirate.trans (hcap i)

theorem isLeast_endpoint_cost_of_modulus {ι : Type*} {cost rate : ι → ℝ}
    {C beta : ℝ} {m : ℝ → ℝ} (hC : 0 ≤ C)
    (hmmono : MonotoneOn m (Set.Ici 0))
    (hm : Tendsto m (𝓝[Set.Ici 0] 0) (𝓝 0))
    (hcap : ∀ i, rate i ≤ C)
    (hcost : ∀ i, beta - m (C - rate i) ≤ cost i)
    (hattain : ∃ i, cost i = beta ∧ rate i = C) :
    IsLeast {e : ℝ | (e, C) ∈ closure (rawGrossRegion cost rate)} beta := by
  constructor
  · obtain ⟨i, hiCost, hiRate⟩ := hattain
    apply subset_closure
    exact ⟨i, by simpa [grossRectangle, hiCost, hiRate] using hC⟩
  · intro e he
    exact endpoint_cost_le_of_mem_closure
      (fun _ hx => rawGrossRegion_rate_bound hcap hx)
      (fun _ hx => rawGrossRegion_cost_bound hmmono hcap hcost hx) hm he

theorem zero_budget_rate_lt_of_positive_endpoint
    {S : Set (ℝ × ℝ)} {C C0 beta : ℝ} {m : ℝ → ℝ}
    (hbeta : 0 < beta) (hcap : ∀ x ∈ S, x.2 ≤ C)
    (hbound : ∀ x ∈ S, beta - m (C - x.2) ≤ x.1)
    (hm : Tendsto m (𝓝[Set.Ici 0] 0) (𝓝 0))
    (hC0 : (0, C0) ∈ closure S) : C0 < C := by
  apply lt_of_le_of_ne (rate_le_of_mem_closure hcap hC0)
  intro heq
  change C0 = C at heq
  subst C0
  have hle := endpoint_cost_le_of_mem_closure hcap hbound hm hC0
  linarith

end QuantumProver.EntanglementAssistedEndpoint.Closure

namespace QuantumProver.EntanglementAssistedEndpoint.MatrixEntropy

open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

theorem posSemidef_norm_le_trace {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.PosSemidef) : ‖A‖ ≤ A.trace.re := by
  have hnorm : ‖A‖ = ‖fun i => (hA.isHermitian.eigenvalues i : ℂ)‖ := by
    conv_lhs => rw [hA.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
    rfl
  have ht : A.trace.re = ∑ i, hA.isHermitian.eigenvalues i := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    simp
  rw [hnorm, ht]
  apply (pi_norm_le_iff_of_nonneg
    (Finset.sum_nonneg (fun i _ => hA.eigenvalues_nonneg i))).mpr
  intro i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
  exact Finset.single_le_sum (fun k _ => hA.eigenvalues_nonneg k) (Finset.mem_univ i)

end QuantumProver.EntanglementAssistedEndpoint.MatrixEntropy
