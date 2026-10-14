import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYMeasurement
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.StinespringEntropyBounds
import QuantumProver.InformationTheory.EntanglementAssistedEndpoint.QuantumEntropy
import Mathlib.Topology.Sion

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker Topology

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYOneWaySeparation

open BCYMeasurement

private def simplexSet (n : ℕ) : Set (Fin n → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

private theorem simplexSet_isCompact (n : ℕ) : IsCompact (simplexSet n) := by
  have hnonneg : IsClosed {w : Fin n → ℝ | ∀ i, 0 ≤ w i} := by
    have heq : {w : Fin n → ℝ | ∀ i, 0 ≤ w i} = ⋂ i, {w : Fin n → ℝ | 0 ≤ w i} := by
      ext w
      simp
    rw [heq]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hsum : IsClosed {w : Fin n → ℝ | ∑ i, w i = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hclosed : IsClosed (simplexSet n) := hnonneg.inter hsum
  apply isCompact_Icc.of_isClosed_subset hclosed
  intro w hw
  exact ⟨hw.1, fun i => hw.2 ▸ Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)⟩

private theorem compact_convexHull_finiteDimensional {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  let N := Module.finrank ℝ E + 2
  let K (n : Fin N) : Set ((Fin n.val → ℝ) × (Fin n.val → E)) :=
    simplexSet n.val ×ˢ Set.pi Set.univ (fun _ => s)
  let F (n : Fin N) (u : (Fin n.val → ℝ) × (Fin n.val → E)) : E :=
    ∑ i, u.1 i • u.2 i
  have hK (n : Fin N) : IsCompact (K n) :=
    (simplexSet_isCompact n.val).prod (isCompact_univ_pi fun _ => hs)
  have hF (n : Fin N) : Continuous (F n) := by fun_prop
  have hcompact : IsCompact (⋃ n : Fin N, F n '' K n) :=
    isCompact_iUnion fun n => (hK n).image (hF n)
  have heq : convexHull ℝ s = ⋃ n : Fin N, F n '' K n := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨ι, hι, z, w, hz, hi, hw0, hw1, hsum⟩ :=
        eq_pos_convex_span_of_mem_convexHull hx
      let _ := hι
      have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
        hi.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      let n : Fin N := ⟨Fintype.card ι, by dsimp [N]; omega⟩
      let e : Fin n.val ≃ ι := (Fintype.equivFin ι).symm
      refine Set.mem_iUnion.mpr ⟨n, ⟨(w ∘ e, z ∘ e), ?_, ?_⟩⟩
      · refine ⟨⟨fun i => (hw0 (e i)).le, ?_⟩, ?_⟩
        · exact (e.sum_comp w).trans hw1
        · intro i _
          exact hz ⟨e i, rfl⟩
      · exact (e.sum_comp (fun i => w i • z i)).trans hsum
    · intro x hx
      obtain ⟨n, u, hu, rfl⟩ := Set.mem_iUnion.mp hx
      exact mem_convexHull_of_exists_fintype u.1 u.2 hu.1.1 hu.1.2
        (fun i => hu.2 i (Set.mem_univ i)) rfl
  rw [heq]
  exact hcompact

variable {A B X Y : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def densityMatrices (I : Type*) [Fintype I] [DecidableEq I] : Set (QMatrix I) :=
  {R | R.PosSemidef ∧ R.trace = 1}

theorem densityMatrices_isCompact {I : Type*} [Fintype I] [DecidableEq I] :
    IsCompact (densityMatrices I) := by
  have hpositive : IsClosed {R : QMatrix I | R.PosSemidef} := by
    simp_rw [← Matrix.nonneg_iff_posSemidef]
    exact isClosed_le continuous_const continuous_id
  have hclosed : IsClosed (densityMatrices I) :=
    hpositive.inter
      (isClosed_eq continuous_id.matrix_trace continuous_const)
  apply (isCompact_closedBall (0 : QMatrix I) 1).of_isClosed_subset hclosed
  intro R hR
  have hn := QuantumProver.EntanglementAssistedEndpoint.MatrixEntropy.posSemidef_norm_le_trace R hR.1
  rw [hR.2, Complex.one_re] at hn
  simpa only [Metric.mem_closedBall, dist_zero_right] using hn

theorem densityMatrices_convex {I : Type*} [Fintype I] [DecidableEq I] :
    Convex ℝ (densityMatrices I) := by
  intro R hR S hS a b ha hb hab
  refine ⟨(hR.1.smul ha).add (hS.1.smul hb), ?_⟩
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hR.2, hS.2,
    ← add_smul, hab, one_smul]

theorem productDensities_isCompact : IsCompact (productDensities A B) := by
  have hcont : Continuous (fun u : QMatrix A × QMatrix B => u.1 ⊗ₖ u.2) := by
    apply continuous_matrix
    intro i j
    have ha : Continuous (fun u : QMatrix A × QMatrix B => u.1 i.1 j.1) :=
      continuous_fst.matrix_elem i.1 j.1
    have hb : Continuous (fun u : QMatrix A × QMatrix B => u.2 i.2 j.2) :=
      continuous_snd.matrix_elem i.2 j.2
    exact ha.mul hb
  have heq : productDensities A B =
      (fun u : QMatrix A × QMatrix B => u.1 ⊗ₖ u.2) ''
        (densityMatrices A ×ˢ densityMatrices B) := by
    ext R
    constructor
    · rintro ⟨a, b, rfl⟩
      exact ⟨(a.matrix, b.matrix), ⟨⟨a.positive, a.trace_one⟩,
        ⟨b.positive, b.trace_one⟩⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨⟨a, ha.1, ha.2⟩, ⟨b, hb.1, hb.2⟩, rfl⟩
  rw [heq]
  exact (densityMatrices_isCompact.prod densityMatrices_isCompact).image hcont

def separableMatrices (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] : Set (QMatrix (A × B)) :=
  {R | IsSeparable R}

theorem separableMatrices_isCompact : IsCompact (separableMatrices A B) :=
  compact_convexHull_finiteDimensional productDensities_isCompact

theorem separableMatrices_convex : Convex ℝ (separableMatrices A B) :=
  convex_convexHull ℝ _

theorem separableMatrices_subset_density : separableMatrices A B ⊆ densityMatrices (A × B) := by
  apply convexHull_min _ densityMatrices_convex
  rintro R ⟨a, b, rfl⟩
  exact ⟨product_posSemidef a.positive b.positive,
    by rw [Matrix.trace_kronecker, a.trace_one, b.trace_one, one_mul]⟩

def acceptEffect [Fintype X] [Fintype Y] (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) : QMatrix (A × B) :=
  ∑ z ∈ s, M.alice z.1 ⊗ₖ M.bob z.1 z.2

def acceptance (R T : QMatrix (A × B)) : ℝ := (R * T).trace.re

theorem acceptance_eq_coarse_probability [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (M : OneWayPOVM A B X Y)
    (s : Finset (X × Y)) (R : QMatrix (A × B)) :
    acceptance R (acceptEffect M s) = (coarseApply M s R).trace.re := by
  rw [acceptance, acceptEffect, Matrix.mul_sum, Matrix.trace_sum, coarseApply_trace]

theorem continuous_acceptance_left (T : QMatrix (A × B)) :
    Continuous (fun R : QMatrix (A × B) => acceptance R T) := by
  unfold acceptance
  fun_prop

theorem continuous_acceptance_right (R : QMatrix (A × B)) :
    Continuous (fun T : QMatrix (A × B) => acceptance R T) := by
  unfold acceptance
  fun_prop

def oneWayEffects (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] : Set (QMatrix (A × B)) :=
  {T | ∃ m n : ℕ, ∃ M : OneWayPOVM A B (Fin m) (Fin n),
    ∃ s : Finset (Fin m × Fin n), T = acceptEffect M s}

section ActualMixtures

variable {m₁ m₂ n₁ n₂ : ℕ}

def reindexPOVM [Fintype X] [Fintype Y] {X' Y' : Type*} [Fintype X'] [Fintype Y']
    (M : OneWayPOVM A B X Y) (eX : X' ≃ X) (eY : Y' ≃ Y) : OneWayPOVM A B X' Y' where
  alice x := M.alice (eX x)
  alice_positive x := M.alice_positive (eX x)
  alice_complete := (eX.sum_comp M.alice).trans M.alice_complete
  bob x y := M.bob (eX x) (eY y)
  bob_positive x y := M.bob_positive (eX x) (eY y)
  bob_complete x := (eY.sum_comp (M.bob (eX x))).trans (M.bob_complete (eX x))

theorem acceptEffect_reindex [Fintype X] [Fintype Y] {X' Y' : Type*}
    [Fintype X'] [Fintype Y'] (M : OneWayPOVM A B X Y) (eX : X' ≃ X) (eY : Y' ≃ Y)
    (s : Finset (X × Y)) :
    acceptEffect (reindexPOVM M eX eY) (s.map (eX.prodCongr eY).symm.toEmbedding) =
      acceptEffect M s := by
  unfold acceptEffect
  rw [Finset.sum_map]
  simp only [reindexPOVM, Equiv.coe_toEmbedding, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map, Equiv.apply_symm_apply]

def mixedPOVM (M₁ : OneWayPOVM A B (Fin m₁) (Fin n₁))
    (M₂ : OneWayPOVM A B (Fin m₂) (Fin n₂)) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    OneWayPOVM A B (Fin m₁ ⊕ Fin m₂) (Fin n₁ ⊕ Fin n₂) where
  alice := Sum.elim (fun x => a • M₁.alice x) (fun x => b • M₂.alice x)
  alice_positive x := by
    cases x with
    | inl x => exact (M₁.alice_positive x).smul ha
    | inr x => exact (M₂.alice_positive x).smul hb
  alice_complete := by
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.smul_sum, ← Finset.smul_sum, M₁.alice_complete, M₂.alice_complete,
      ← add_smul, hab, one_smul]
  bob := Sum.elim
    (fun x => Sum.elim (M₁.bob x) (fun _ => 0))
    (fun x => Sum.elim (fun _ => 0) (M₂.bob x))
  bob_positive x y := by
    cases x with
    | inl x =>
        cases y with
        | inl y => exact M₁.bob_positive x y
        | inr y => exact Matrix.PosSemidef.zero
    | inr x =>
        cases y with
        | inl y => exact Matrix.PosSemidef.zero
        | inr y => exact M₂.bob_positive x y
  bob_complete x := by
    cases x with
    | inl x => simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Finset.sum_const_zero, add_zero, M₁.bob_complete]
    | inr x => simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Finset.sum_const_zero, zero_add, M₂.bob_complete]

def mixedEvent (s₁ : Finset (Fin m₁ × Fin n₁)) (s₂ : Finset (Fin m₂ × Fin n₂)) :
    Finset ((Fin m₁ ⊕ Fin m₂) × (Fin n₁ ⊕ Fin n₂)) := by
  classical
  exact Finset.univ.filter fun z => match z with
    | (.inl x, .inl y) => (x, y) ∈ s₁
    | (.inr x, .inr y) => (x, y) ∈ s₂
    | _ => False

private theorem acceptEffect_eq_sum_ite [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (M : OneWayPOVM A B X Y) (s : Finset (X × Y)) :
    acceptEffect M s = ∑ x, ∑ y, if (x,y) ∈ s then M.alice x ⊗ₖ M.bob x y else 0 := by
  unfold acceptEffect
  simpa only [Fintype.sum_prod_type] using
    (Finset.sum_ite_mem_eq s (fun z : X × Y => M.alice z.1 ⊗ₖ M.bob z.1 z.2)).symm

theorem acceptEffect_mixed (M₁ : OneWayPOVM A B (Fin m₁) (Fin n₁))
    (M₂ : OneWayPOVM A B (Fin m₂) (Fin n₂)) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (s₁ : Finset (Fin m₁ × Fin n₁)) (s₂ : Finset (Fin m₂ × Fin n₂)) :
    acceptEffect (mixedPOVM M₁ M₂ a b ha hb hab) (mixedEvent s₁ s₂) =
      a • acceptEffect M₁ s₁ + b • acceptEffect M₂ s₂ := by
  rw [acceptEffect_eq_sum_ite, acceptEffect_eq_sum_ite, acceptEffect_eq_sum_ite]
  simp only [Fintype.sum_sum_type, mixedPOVM, mixedEvent, Sum.elim_inl, Sum.elim_inr,
    Finset.mem_filter, Finset.mem_univ, true_and, ite_false, Finset.sum_const_zero,
    add_zero, zero_add, Matrix.smul_kronecker, Finset.smul_sum, smul_ite, smul_zero]

theorem oneWayEffects_convex : Convex ℝ (oneWayEffects A B) := by
  classical
  rintro T ⟨m₁,n₁,M₁,s₁,rfl⟩ S ⟨m₂,n₂,M₂,s₂,rfl⟩ a b ha hb hab
  let M := mixedPOVM M₁ M₂ a b ha hb hab
  let s := mixedEvent s₁ s₂
  let eX := (Fintype.equivFin (Fin m₁ ⊕ Fin m₂)).symm
  let eY := (Fintype.equivFin (Fin n₁ ⊕ Fin n₂)).symm
  refine ⟨_, _, reindexPOVM M eX eY, s.map (eX.prodCongr eY).symm.toEmbedding, ?_⟩
  rw [acceptEffect_reindex]
  exact (acceptEffect_mixed M₁ M₂ a b ha hb hab s₁ s₂).symm

end ActualMixtures

def marginalProduct (ρ : Density (A × B)) : Density (A × B) where
  matrix := partialTraceRight ρ.matrix ⊗ₖ partialTraceLeft ρ.matrix
  positive := product_posSemidef (partialTraceRight_positive ρ.positive)
    (partialTraceLeft_positive ρ.positive)
  trace_one := by rw [Matrix.trace_kronecker, partialTraceRight_trace,
    partialTraceLeft_trace, ρ.trace_one, one_mul]

theorem marginalProduct_isSeparable (ρ : Density (A × B)) :
    IsSeparable (marginalProduct ρ).matrix :=
  subset_convexHull ℝ _ ⟨⟨partialTraceRight ρ.matrix,
    partialTraceRight_positive ρ.positive, (partialTraceRight_trace _).trans ρ.trace_one⟩,
    ⟨partialTraceLeft ρ.matrix, partialTraceLeft_positive ρ.positive,
      (partialTraceLeft_trace _).trans ρ.trace_one⟩, rfl⟩

theorem separableMatrices_nonempty (ρ : Density (A × B)) : (separableMatrices A B).Nonempty :=
  ⟨(marginalProduct ρ).matrix, marginalProduct_isSeparable ρ⟩

def trivialPOVM : OneWayPOVM A B (Fin 1) (Fin 1) where
  alice _ := 1
  alice_positive _ := Matrix.PosSemidef.one
  alice_complete := by simp
  bob _ _ := 1
  bob_positive _ _ := Matrix.PosSemidef.one
  bob_complete _ := by simp

theorem oneWayNorm_difference_nonneg (ρ σ : Density (A × B)) :
    0 ≤ oneWayNorm (ρ.matrix - σ.matrix) :=
  (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => abs_nonneg _).trans
    (c1_oneWayNorm_ge_measurement ρ σ trivialPOVM)

def separableOneWayDistance (ρ : Density (A × B)) : ℝ :=
  sInf {v | ∃ σ : Density (A × B), IsSeparable σ.matrix ∧
    v = oneWayNorm (ρ.matrix - σ.matrix)}

theorem separableOneWayDistance_le (ρ σ : Density (A × B))
    (hσ : IsSeparable σ.matrix) :
    separableOneWayDistance ρ ≤ oneWayNorm (ρ.matrix - σ.matrix) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨τ, hτ, rfl⟩
    exact oneWayNorm_difference_nonneg ρ τ
  · exact ⟨σ, hσ, rfl⟩

private theorem positive_event_variation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (hzero : ∑ i, f i = 0) :
    (∑ i, |f i|) = 2 * ∑ i ∈ Finset.univ.filter (fun i => 0 ≤ f i), f i := by
  have hpoint (i : ι) : |f i| = 2 * (if 0 ≤ f i then f i else 0) - f i := by
    by_cases hi : 0 ≤ f i
    · rw [if_pos hi, abs_of_nonneg hi]
      ring
    · rw [if_neg hi, abs_of_neg (lt_of_not_ge hi)]
      ring
  simp only [hpoint, Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, sub_zero,
    Finset.sum_filter]

def separatingGap (ρ σ T : QMatrix (A × B)) : ℝ := acceptance ρ T - acceptance σ T

theorem exists_effect_of_lt_norm (ρ σ : Density (A × B)) {d : ℝ}
    (hd : d < oneWayNorm (ρ.matrix - σ.matrix)) :
    ∃ T ∈ oneWayEffects A B, d / 2 < separatingGap ρ.matrix σ.matrix T := by
  classical
  have hne : {v : ℝ | ∃ m n : ℕ, ∃ M : OneWayPOVM A B (Fin m) (Fin n),
      v = ∑ x, ∑ y, |oneWayOutcome M (ρ.matrix - σ.matrix) x y|}.Nonempty :=
    ⟨_, 1, 1, trivialPOVM, rfl⟩
  obtain ⟨v, ⟨m,n,M,rfl⟩, hv⟩ := exists_lt_of_lt_csSup hne hd
  let f (z : Fin m × Fin n) := oneWayOutcome M (ρ.matrix - σ.matrix) z.1 z.2
  let s := Finset.univ.filter (fun z => 0 ≤ f z)
  have hzero : ∑ z, f z = 0 := by
    rw [Fintype.sum_prod_type]
    change (∑ x, ∑ y, oneWayOutcome M (ρ.matrix - σ.matrix) x y) = 0
    rw [c1_oneWayOutcome_sum, Matrix.trace_sub, ρ.trace_one, σ.trace_one, sub_self,
      Complex.zero_re]
  have hvar := positive_event_variation f hzero
  have hgap : separatingGap ρ.matrix σ.matrix (acceptEffect M s) = ∑ z ∈ s, f z := by
    rw [separatingGap, acceptance, acceptance, ← Complex.sub_re, ← Matrix.trace_sub,
      ← Matrix.sub_mul, ← acceptance, acceptance_eq_coarse_probability,
      coarseApply_probability]
  refine ⟨acceptEffect M s, ⟨m,n,M,s,rfl⟩, ?_⟩
  rw [hgap]
  have hv' : d < ∑ z, |f z| := by
    simpa only [f, Fintype.sum_prod_type] using hv
  rw [hvar] at hv'
  dsimp [s]
  linarith

private theorem acceptance_smul_add_left (R S T : QMatrix (A × B)) (a b : ℝ) :
    acceptance (a • R + b • S) T = a * acceptance R T + b * acceptance S T := by
  simp only [acceptance, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]

private theorem acceptance_smul_add_right (R S T : QMatrix (A × B)) (a b : ℝ) :
    acceptance R (a • S + b • T) = a * acceptance R S + b * acceptance R T := by
  simp only [acceptance, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]

private theorem gap_convexOn_left (ρ T : QMatrix (A × B)) :
    ConvexOn ℝ (separableMatrices A B) (fun σ => separatingGap ρ σ T) := by
  refine ⟨separableMatrices_convex, ?_⟩
  intro R hR S hS a b ha hb hab
  apply le_of_eq
  simp only [separatingGap, acceptance_smul_add_left, smul_eq_mul]
  calc
    _ = (a + b) * acceptance ρ T -
        (a * acceptance R T + b * acceptance S T) := by rw [hab, one_mul]
    _ = _ := by ring

private theorem gap_concaveOn_right (ρ σ : QMatrix (A × B)) :
    ConcaveOn ℝ (oneWayEffects A B) (fun T => separatingGap ρ σ T) := by
  refine ⟨oneWayEffects_convex, ?_⟩
  intro R hR S hS a b ha hb hab
  apply le_of_eq
  simp only [separatingGap, acceptance_smul_add_right, smul_eq_mul]
  ring

private theorem continuous_gap_left (ρ T : QMatrix (A × B)) :
    Continuous (fun σ => separatingGap ρ σ T) :=
  continuous_const.sub (continuous_acceptance_left T)

private theorem continuous_gap_right (ρ σ : QMatrix (A × B)) :
    Continuous (fun T => separatingGap ρ σ T) :=
  (continuous_acceptance_right ρ).sub (continuous_acceptance_right σ)

theorem exists_uniform_effect_of_lt_distance (ρ : Density (A × B)) {d : ℝ}
    (hd : d < separableOneWayDistance ρ) :
    ∃ T ∈ oneWayEffects A B, ∀ σ ∈ separableMatrices A B,
      d / 2 < separatingGap ρ.matrix σ T := by
  classical
  have hpoint (σ : QMatrix (A × B)) (hσ : σ ∈ separableMatrices A B) :
      ∃ T ∈ oneWayEffects A B, d / 2 < separatingGap ρ.matrix σ T := by
    have hs := separableMatrices_subset_density hσ
    let τ : Density (A × B) := ⟨σ, hs.1, hs.2⟩
    exact exists_effect_of_lt_norm ρ τ (hd.trans_le (separableOneWayDistance_le ρ τ hσ))
  let U (T : oneWayEffects A B) : Set (QMatrix (A × B)) :=
    {σ | d / 2 < separatingGap ρ.matrix σ T}
  have hU (T : oneWayEffects A B) : IsOpen (U T) :=
    isOpen_lt continuous_const (continuous_gap_left ρ.matrix T)
  have hcover : separableMatrices A B ⊆ ⋃ T : oneWayEffects A B, U T := by
    intro σ hσ
    obtain ⟨T,hT,hgap⟩ := hpoint σ hσ
    exact Set.mem_iUnion.mpr ⟨⟨T,hT⟩,hgap⟩
  obtain ⟨s,hs⟩ := separableMatrices_isCompact.elim_finite_subcover U hU hcover
  have hfinite : (Subtype.val '' (s : Set (oneWayEffects A B))).Finite := s.finite_toSet.image _
  have hsubset : Subtype.val '' (s : Set (oneWayEffects A B)) ⊆ oneWayEffects A B := by
    rintro T ⟨t,ht,rfl⟩
    exact t.property
  have hfiniteCover : ∀ σ ∈ separableMatrices A B,
      ∃ T ∈ Subtype.val '' (s : Set (oneWayEffects A B)),
        d / 2 < separatingGap ρ.matrix σ T := by
    intro σ hσ
    have hσc := hs hσ
    simp only [Set.mem_iUnion] at hσc
    obtain ⟨T,hTs,hgap⟩ := hσc
    exact ⟨T,⟨T,hTs,rfl⟩,hgap⟩
  exact Sion.exists_lt_iInf_of_lt_iInf_of_finite
    (separableMatrices_nonempty ρ) separableMatrices_isCompact
    (fun T _ => (continuous_gap_left ρ.matrix T).continuousOn.lowerSemicontinuousOn)
    (fun T _ => (gap_convexOn_left ρ.matrix T).quasiconvexOn)
    oneWayEffects_convex
    (fun σ _ => (continuous_gap_right ρ.matrix σ).continuousOn.upperSemicontinuousOn)
    (fun σ _ => (gap_concaveOn_right ρ.matrix σ).quasiconcaveOn)
    separableMatrices_convex hfinite hsubset hfiniteCover

theorem acceptance_nonneg_of_oneWayEffect (ρ : Density (A × B))
    {T : QMatrix (A × B)} (hT : T ∈ oneWayEffects A B) : 0 ≤ acceptance ρ.matrix T := by
  obtain ⟨m,n,M,s,rfl⟩ := hT
  rw [acceptance_eq_coarse_probability]
  exact coarseApply_probability_nonneg M s ρ.positive

theorem acceptance_le_one_of_oneWayEffect (ρ : Density (A × B))
    {T : QMatrix (A × B)} (hT : T ∈ oneWayEffects A B) : acceptance ρ.matrix T ≤ 1 := by
  obtain ⟨m,n,M,s,rfl⟩ := hT
  rw [acceptance_eq_coarse_probability]
  exact coarseApply_probability_le_one M s ρ

theorem exists_oneWay_separator_of_lt_distance (ρ : Density (A × B)) {d : ℝ}
    (hd0 : 0 < d) (hd : d < separableOneWayDistance ρ) :
    ∃ m n : ℕ, ∃ M : OneWayPOVM A B (Fin m) (Fin n),
      ∃ s : Finset (Fin m × Fin n), ∃ a b : ℝ,
        a ∈ Set.Icc 0 1 ∧ b = (coarseApply M s ρ.matrix).trace.re ∧
        (∀ σ : Density (A × B), IsSeparable σ.matrix →
          (coarseApply M s σ.matrix).trace.re ≤ a) ∧
        d / 2 ≤ b - a ∧ a < b := by
  classical
  obtain ⟨T,hT,hgap⟩ := exists_uniform_effect_of_lt_distance ρ hd
  let V : Set ℝ := {v | ∃ σ : Density (A × B), IsSeparable σ.matrix ∧
    v = acceptance σ.matrix T}
  have hne : V.Nonempty :=
    ⟨_, marginalProduct ρ, marginalProduct_isSeparable ρ, rfl⟩
  have hbdd : BddAbove V := by
    refine ⟨1, ?_⟩
    rintro v ⟨σ,hσ,rfl⟩
    exact acceptance_le_one_of_oneWayEffect σ hT
  let a := sSup V
  have ha0 : 0 ≤ a :=
    (acceptance_nonneg_of_oneWayEffect (marginalProduct ρ) hT).trans
      (le_csSup hbdd ⟨marginalProduct ρ, marginalProduct_isSeparable ρ, rfl⟩)
  have ha1 : a ≤ 1 := by
    apply csSup_le hne
    rintro v ⟨σ,hσ,rfl⟩
    exact acceptance_le_one_of_oneWayEffect σ hT
  have haccept (σ : Density (A × B)) (hσ : IsSeparable σ.matrix) :
      acceptance σ.matrix T ≤ a := le_csSup hbdd ⟨σ,hσ,rfl⟩
  have hagap : a ≤ acceptance ρ.matrix T - d / 2 := by
    apply csSup_le hne
    rintro v ⟨σ,hσ,rfl⟩
    have h := hgap σ.matrix hσ
    dsimp [separatingGap] at h
    linarith
  obtain ⟨m,n,M,s,rfl⟩ := hT
  refine ⟨m,n,M,s,a,(coarseApply M s ρ.matrix).trace.re,⟨ha0,ha1⟩,rfl,?_,?_,?_⟩
  · intro σ hσ
    rw [← acceptance_eq_coarse_probability]
    exact haccept σ hσ
  · rw [← acceptance_eq_coarse_probability]
    linarith
  · rw [← acceptance_eq_coarse_probability]
    linarith

end QuantumProver.DepolarizingSquashedEntanglement.BCYOneWaySeparation
