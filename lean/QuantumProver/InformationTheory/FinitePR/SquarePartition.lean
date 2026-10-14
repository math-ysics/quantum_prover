import QuantumProver.InformationTheory.FinitePR.SphereGeometry
import QuantumProver.InformationTheory.FinitePR.CapacityBounds
import Mathlib

/-! Exact endpoint-assigned equal-mass partition of the actual unit-square source.
This module does not assume a sphere cell law or any residual-density identity. -/

namespace FinitePR.Square

open MeasureTheory Set
open scoped BigOperators unitInterval

abbrev Source := I × I

noncomputable def referenceMeasure : Measure Source :=
  (volume : Measure I).prod (volume : Measure I)

instance referenceMeasure_probability : IsProbabilityMeasure referenceMeasure := by
  dsimp [referenceMeasure]
  infer_instance

noncomputable def referenceProbability : ProbabilityMeasure Source :=
  ⟨referenceMeasure, inferInstance⟩

noncomputable def lower (k : ℕ) (hk : 0 < k) (i : Fin k) : I :=
  ⟨(i.val : ℝ) / (k : ℝ), div_nonneg (by positivity) (by positivity),
    (div_le_one (by positivity : (0 : ℝ) < k)).2
      (by exact_mod_cast Nat.le_of_lt i.isLt)⟩

noncomputable def upper (k : ℕ) (hk : 0 < k) (i : Fin k) : I :=
  ⟨((i.val + 1 : ℕ) : ℝ) / (k : ℝ), div_nonneg (by positivity) (by positivity),
    (div_le_one (by positivity : (0 : ℝ) < k)).2
      (by exact_mod_cast Nat.succ_le_of_lt i.isLt)⟩

lemma upper_sub_lower (k : ℕ) (hk : 0 < k) (i : Fin k) :
    (upper k hk i : ℝ) - (lower k hk i : ℝ) = 1 / (k : ℝ) := by
  simp only [upper, lower, Nat.cast_add, Nat.cast_one]
  ring

/-- Every interior right endpoint is assigned to the next interval;1 belongs to the last. -/
def intervalCell (k : ℕ) (hk : 0 < k) (i : Fin k) : Set I :=
  if i.val + 1 = k then Icc (lower k hk i) (upper k hk i)
  else Ico (lower k hk i) (upper k hk i)

theorem measurable_intervalCell (k : ℕ) (hk : 0 < k) (i : Fin k) :
    MeasurableSet (intervalCell k hk i) := by
  unfold intervalCell
  split_ifs <;> measurability

lemma intervalCell_bounds (k : ℕ) (hk : 0 < k) (i : Fin k) {u : I}
    (hu : u ∈ intervalCell k hk i) :
    (lower k hk i : ℝ) ≤ u ∧ (u : ℝ) ≤ upper k hk i := by
  unfold intervalCell at hu
  split_ifs at hu with hi
  · exact hu
  · exact ⟨hu.1, hu.2.le⟩

lemma intervalCell_strict_upper (k : ℕ) (hk : 0 < k) (i : Fin k)
    (hi : i.val + 1 ≠ k) {u : I} (hu : u ∈ intervalCell k hk i) :
    (u : ℝ) < upper k hk i := by
  exact (by simpa [intervalCell, hi] using hu : u ∈ Ico (lower k hk i) (upper k hk i)).2

theorem intervalCell_disjoint (k : ℕ) (hk : 0 < k) :
    Pairwise (fun i j : Fin k => Disjoint (intervalCell k hk i) (intervalCell k hk j)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro u hui huj
  have hval : i.val ≠ j.val := fun he => hij (Fin.ext he)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  rcases lt_or_gt_of_ne hval with hijv | hjiv
  · have hi : i.val + 1 ≠ k := by omega
    have hedges : (upper k hk i : ℝ) ≤ lower k hk j := by
      apply (div_le_div_iff_of_pos_right hkr).2
      exact_mod_cast Nat.succ_le_of_lt hijv
    exact (lt_irrefl (u : ℝ))
      ((intervalCell_strict_upper k hk i hi hui).trans_le
        (hedges.trans (intervalCell_bounds k hk j huj).1))
  · have hj : j.val + 1 ≠ k := by omega
    have hedges : (upper k hk j : ℝ) ≤ lower k hk i := by
      apply (div_le_div_iff_of_pos_right hkr).2
      exact_mod_cast Nat.succ_le_of_lt hjiv
    exact (lt_irrefl (u : ℝ))
      ((intervalCell_strict_upper k hk j hj huj).trans_le
        (hedges.trans (intervalCell_bounds k hk i hui).1))

theorem exists_intervalCell (k : ℕ) (hk : 0 < k) (u : I) :
    ∃ i : Fin k, u ∈ intervalCell k hk i := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases hu : u = 1
  · subst u
    let i : Fin k := ⟨k - 1, by omega⟩
    have hi : i.val + 1 = k := by dsimp [i]; omega
    have hupper : upper k hk i = 1 := by
      apply Subtype.ext
      change ((i.val + 1 : ℕ) : ℝ) / (k : ℝ) = 1
      rw [hi, div_self hkr.ne']
    refine ⟨i, ?_⟩
    rw [intervalCell, if_pos hi, hupper]
    exact ⟨(lower k hk i).property.2, le_rfl⟩
  · have hu₁ : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 (by
      intro he
      exact hu (Subtype.ext he))
    have hnonneg : 0 ≤ (k : ℝ) * (u : ℝ) := mul_nonneg hkr.le u.property.1
    have hfloor : Nat.floor ((k : ℝ) * (u : ℝ)) < k :=
      (Nat.floor_lt hnonneg).2 (by nlinarith)
    let i : Fin k := ⟨Nat.floor ((k : ℝ) * (u : ℝ)), hfloor⟩
    have hlo : (lower k hk i : ℝ) ≤ u := by
      apply (div_le_iff₀ hkr).2
      simpa [i, mul_comm] using Nat.floor_le hnonneg
    have hhi : (u : ℝ) < upper k hk i := by
      apply (lt_div_iff₀ hkr).2
      simpa [i, Nat.cast_add, Nat.cast_one, mul_comm] using
        Nat.lt_floor_add_one ((k : ℝ) * (u : ℝ))
    refine ⟨i, ?_⟩
    unfold intervalCell
    split_ifs <;> exact ⟨hlo, by first | exact hhi.le | exact hhi⟩

theorem intervalCell_cover (k : ℕ) (hk : 0 < k) :
    (⋃ i : Fin k, intervalCell k hk i) = univ := by
  ext u
  simp only [mem_iUnion, mem_univ, iff_true]
  exact exists_intervalCell k hk u

theorem intervalCell_volume (k : ℕ) (hk : 0 < k) (i : Fin k) :
    (volume : Measure I) (intervalCell k hk i) = ENNReal.ofReal (1 / (k : ℝ)) := by
  unfold intervalCell
  split_ifs <;>
    simp only [unitInterval.volume_Icc, unitInterval.volume_Ico, upper_sub_lower]

theorem intervalCell_real_volume (k : ℕ) (hk : 0 < k) (i : Fin k) :
    (volume : Measure I).real (intervalCell k hk i) = 1 / (k : ℝ) := by
  rw [measureReal_def, intervalCell_volume, ENNReal.toReal_ofReal (by positivity)]

def cell (k : ℕ) (hk : 0 < k) (j : Fin k × Fin k) : Set Source :=
  intervalCell k hk j.1 ×ˢ intervalCell k hk j.2

theorem measurable_cell (k : ℕ) (hk : 0 < k) (j : Fin k × Fin k) :
    MeasurableSet (cell k hk j) :=
  (measurable_intervalCell k hk j.1).prod (measurable_intervalCell k hk j.2)

theorem cell_disjoint (k : ℕ) (hk : 0 < k) :
    Pairwise (fun i j : Fin k × Fin k => Disjoint (cell k hk i) (cell k hk j)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro p hpi hpj
  by_cases hfst : i.1 = j.1
  · have hsnd : i.2 ≠ j.2 := fun h => hij (Prod.ext hfst h)
    exact Set.disjoint_left.1 (intervalCell_disjoint k hk hsnd) hpi.2 hpj.2
  · exact Set.disjoint_left.1 (intervalCell_disjoint k hk hfst) hpi.1 hpj.1

theorem cell_cover (k : ℕ) (hk : 0 < k) :
    (⋃ j : Fin k × Fin k, cell k hk j) = univ := by
  ext p
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨i, hi⟩ := exists_intervalCell k hk p.1
  obtain ⟨j, hj⟩ := exists_intervalCell k hk p.2
  exact ⟨(i, j), hi, hj⟩

theorem cell_real_mass (k : ℕ) (hk : 0 < k) (j : Fin k × Fin k) :
    referenceMeasure.real (cell k hk j) = 1 / (k : ℝ) ^ 2 := by
  rw [referenceMeasure, cell, measureReal_prod_prod,
    intervalCell_real_volume, intervalCell_real_volume]
  ring

theorem cell_positive_mass (k : ℕ) (hk : 0 < k) (j : Fin k × Fin k) :
    0 < referenceMeasure.real (cell k hk j) := by
  rw [cell_real_mass]
  positivity

theorem number_cells (k : ℕ) : Fintype.card (Fin k × Fin k) = k ^ 2 := by
  simp [pow_two]

def intervalBoundary (k : ℕ) (hk : 0 < k) : Set I :=
  ⋃ i : Fin k, ({lower k hk i} ∪ {upper k hk i})

theorem intervalBoundary_null (k : ℕ) (hk : 0 < k) :
    (volume : Measure I) (intervalBoundary k hk) = 0 := by
  apply measure_iUnion_null
  intro i
  exact measure_union_null (by simp) (by simp)

def gridBoundary (k : ℕ) (hk : 0 < k) : Set Source :=
  (intervalBoundary k hk ×ˢ univ) ∪ (univ ×ˢ intervalBoundary k hk)

theorem gridBoundary_null (k : ℕ) (hk : 0 < k) :
    referenceMeasure (gridBoundary k hk) = 0 := by
  unfold referenceMeasure gridBoundary
  apply measure_union_null <;> simp [Measure.prod_prod, intervalBoundary_null]

lemma intervalCell_width (k : ℕ) (hk : 0 < k) (i : Fin k) {u v : I}
    (hu : u ∈ intervalCell k hk i) (hv : v ∈ intervalCell k hk i) :
    |(u : ℝ) - (v : ℝ)| ≤ 1 / (k : ℝ) := by
  have hbu := intervalCell_bounds k hk i hu
  have hbv := intervalCell_bounds k hk i hv
  have hgap := upper_sub_lower k hk i
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The same literal chart as A's uniformChart, with no Main import. -/
noncomputable def chart (p : Source) : Sphere.Height × ℝ :=
  (⟨2 * (p.1 : ℝ) - 1, by
    constructor <;> linarith [p.1.property.1, p.1.property.2]⟩,
    -Real.pi + 2 * Real.pi * (p.2 : ℝ))

theorem continuous_chart : Continuous chart := by
  apply Continuous.prodMk
  · exact ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).sub
      continuous_const).subtype_mk _
  · fun_prop

noncomputable def sphereSample (p : Source) : Direction := Sphere.parameterDirection (chart p)

theorem continuous_sphereSample : Continuous sphereSample :=
  Sphere.continuous_parameterDirection.comp continuous_chart

theorem cell_chart_mesh (k : ℕ) (hk : 0 < k) (j : Fin k × Fin k)
    {p q : Source} (hp : p ∈ cell k hk j) (hq : q ∈ cell k hk j) :
    Sphere.coordinateDistance (sphereSample p) (sphereSample q) ≤
      3 * Real.pi / Real.sqrt (k : ℝ) := by
  have hh : |((chart p).1 : ℝ) - ((chart q).1 : ℝ)| ≤ 2 / (k : ℝ) := by
    calc
      _ = 2 * |(p.1 : ℝ) - (q.1 : ℝ)| := by
        change |(2 * (p.1 : ℝ) - 1) - (2 * (q.1 : ℝ) - 1)| = _
        rw [show (2 * (p.1 : ℝ) - 1) - (2 * (q.1 : ℝ) - 1) =
          2 * ((p.1 : ℝ) - (q.1 : ℝ)) by ring, abs_mul, abs_of_nonneg (by norm_num)]
      _ ≤ 2 * (1 / (k : ℝ)) :=
        mul_le_mul_of_nonneg_left (intervalCell_width k hk j.1 hp.1 hq.1) (by norm_num)
      _ = _ := by ring
  have hφ : |(chart p).2 - (chart q).2| ≤ 2 * Real.pi / (k : ℝ) := by
    calc
      _ = (2 * Real.pi) * |(p.2 : ℝ) - (q.2 : ℝ)| := by
        change |(-Real.pi + 2 * Real.pi * (p.2 : ℝ)) -
          (-Real.pi + 2 * Real.pi * (q.2 : ℝ))| = _
        rw [show (-Real.pi + 2 * Real.pi * (p.2 : ℝ)) -
          (-Real.pi + 2 * Real.pi * (q.2 : ℝ)) =
          (2 * Real.pi) * ((p.2 : ℝ) - (q.2 : ℝ)) by ring,
          abs_mul, abs_of_nonneg (by positivity)]
      _ ≤ (2 * Real.pi) * (1 / (k : ℝ)) :=
        mul_le_mul_of_nonneg_left (intervalCell_width k hk j.2 hp.2 hq.2) (by positivity)
      _ = _ := by ring
  exact Sphere.rectangular_mesh_bound_pi k (by omega) (chart p) (chart q) hh hφ

def cellIndexEquiv (k : ℕ) : (Fin k × Fin k) ≃ Fin (k ^ 2) :=
  (finProdFinEquiv : (Fin k × Fin k) ≃ Fin (k * k)).trans
    (finCongr (by simp [pow_two]))

def finCell (k : ℕ) (hk : 0 < k) (i : Fin (k ^ 2)) : Set Source :=
  cell k hk ((cellIndexEquiv k).symm i)

theorem measurable_finCell (k : ℕ) (hk : 0 < k) (i : Fin (k ^ 2)) :
    MeasurableSet (finCell k hk i) := measurable_cell k hk _

theorem finCell_disjoint (k : ℕ) (hk : 0 < k) :
    Pairwise (fun i j : Fin (k ^ 2) => Disjoint (finCell k hk i) (finCell k hk j)) := by
  intro i j hij
  exact cell_disjoint k hk (fun h => hij ((cellIndexEquiv k).symm.injective h))

theorem exists_finCell (k : ℕ) (hk : 0 < k) (p : Source) :
    ∃ i : Fin (k ^ 2), p ∈ finCell k hk i := by
  obtain ⟨i, hi⟩ := exists_intervalCell k hk p.1
  obtain ⟨j, hj⟩ := exists_intervalCell k hk p.2
  refine ⟨cellIndexEquiv k (i, j), ?_⟩
  simpa [finCell] using (show p ∈ cell k hk (i, j) from ⟨hi, hj⟩)

theorem finCell_cover (k : ℕ) (hk : 0 < k) :
    (⋃ i : Fin (k ^ 2), finCell k hk i) = univ := by
  ext p
  simp only [mem_iUnion, mem_univ, iff_true]
  exact exists_finCell k hk p

theorem finCell_real_mass (k : ℕ) (hk : 0 < k) (i : Fin (k ^ 2)) :
    referenceMeasure.real (finCell k hk i) = 1 / (k : ℝ) ^ 2 := cell_real_mass k hk _

theorem finCell_ne_zero (k : ℕ) (hk : 0 < k) (i : Fin (k ^ 2)) :
    referenceMeasure (finCell k hk i) ≠ 0 := by
  intro hz
  have hp : 0 < referenceMeasure.real (finCell k hk i) := by
    rw [finCell_real_mass]
    positivity
  have hr : referenceMeasure.real (finCell k hk i) = 0 := by
    simp [Measure.real, hz]
  linarith

theorem stratifiedSource_probability (k : ℕ) (hk : 0 < k) :
    IsProbabilityMeasure (Measure.pi (fun i : Fin (k ^ 2) =>
      ProbabilityTheory.cond referenceMeasure (finCell k hk i))) := by
  letI : ∀ i : Fin (k ^ 2), IsProbabilityMeasure
      (ProbabilityTheory.cond referenceMeasure (finCell k hk i)) :=
    fun i => ProbabilityTheory.cond_isProbabilityMeasure (finCell_ne_zero k hk i)
  infer_instance

theorem finCell_chart_mesh (k : ℕ) (hk : 0 < k) (i : Fin (k ^ 2))
    {p q : Source} (hp : p ∈ finCell k hk i) (hq : q ∈ finCell k hk i) :
    Sphere.coordinateDistance (sphereSample p) (sphereSample q) ≤
      3 * Real.pi / Real.sqrt (k : ℝ) := cell_chart_mesh k hk _ hp hq

/-- A normalized continuous density actually has a whole positive cell on a fine mesh. -/
theorem exists_positive_finCell (k : ℕ) (hk : 0 < k)
    (f : Source → ℝ) (hcontinuous : Continuous f) (hf : Integrable f referenceMeasure)
    (hnormalized : ∫ p, f p ∂referenceMeasure = 1)
    (L : ℝ) (hL : 0 ≤ L)
    (hvariation : ∀ p q, |f p - f q| ≤
      L * Sphere.coordinateDistance (sphereSample p) (sphereSample q))
    (hmesh : L * (3 * Real.pi / Real.sqrt (k : ℝ)) ≤ 1 / 2) :
    ∃ i : Fin (k ^ 2), ∀ p ∈ finCell k hk i, (1 / 2 : ℝ) ≤ f p := by
  obtain ⟨p, _, hmax⟩ :=
    isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (univ : Set Source).Nonempty)
      hcontinuous.continuousOn
  have hfp : 1 ≤ f p := by
    have hi := integral_mono hf (integrable_const (f p)) (fun q => hmax (mem_univ q))
    simpa [hnormalized] using hi
  obtain ⟨i, hi⟩ := exists_finCell k hk p
  refine ⟨i, ?_⟩
  intro q hq
  have hdiff : |f q - f p| ≤ 1 / 2 :=
    (hvariation q p).trans
      ((mul_le_mul_of_nonneg_left (finCell_chart_mesh k hk i hq hi) hL).trans hmesh)
  linarith [(abs_le.mp hdiff).1]

/-- The explicit finite source prior satisfies hitting capacity, with no partition
or positive-cell witness assumed. The remaining hypotheses are analytic density
and numerical bounds, not equal-area or coupling existence assumptions. -/
theorem source_hit_capacity (k : ℕ) (hk : 0 < k)
    (f : Source → ℝ) (hcontinuous : Continuous f) (hf : Integrable f referenceMeasure)
    (hnonneg : ∀ p, 0 ≤ f p) (hnormalized : ∫ p, f p ∂referenceMeasure = 1)
    (L M δ : ℝ) (hL : 0 ≤ L)
    (hvariation : ∀ p q, |f p - f q| ≤
      L * Sphere.coordinateDistance (sphereSample p) (sphereSample q))
    (hmesh : L * (3 * Real.pi / Real.sqrt (k : ℝ)) ≤ 1 / 2)
    (hbound : ∀ p, f p ≤ M) (hδ : 0 < δ)
    (hsmall : M * δ ≤ 1 - Real.exp (-(k : ℝ) ^ 2 * δ))
    (hlarge : Real.exp (1 - (k : ℝ) ^ 2 * δ) ≤ (1 / 2 : ℝ) / (k : ℝ) ^ 2)
    (B : Set Source) (hB : MeasurableSet B) :
    (∫ p in B, f p ∂referenceMeasure) ≤
      (Measure.pi (fun i : Fin (k ^ 2) =>
        ProbabilityTheory.cond referenceMeasure (finCell k hk i))).real
          {z : Fin (k ^ 2) → Source | ∃ i, z i ∈ B} := by
  classical
  exact Capacity.stratified_list_hit_capacity referenceMeasure (finCell k hk)
    (measurable_finCell k hk) (finCell_disjoint k hk) (finCell_cover k hk)
    ((k : ℝ) ^ 2) (by positivity) (finCell_real_mass k hk) f hf hnonneg hnormalized
    M (1 / 2) δ hbound
    (exists_positive_finCell k hk f hcontinuous hf hnormalized L hL hvariation hmesh)
    hδ hsmall hlarge B hB

/-- An actual finite grid size simultaneously meets the mesh and both capacity
numerical conditions; no numerical or geometric witness is assumed. -/
theorem exists_capacity_size (L M : ℝ) (hM : 0 < M) :
    ∃ k : ℕ, 0 < k ∧ ∃ δ : ℝ, 0 < δ ∧
      L * (3 * Real.pi / Real.sqrt (k : ℝ)) ≤ 1 / 2 ∧
      M * δ ≤ 1 - Real.exp (-(k : ℝ) ^ 2 * δ) ∧
      Real.exp (1 - (k : ℝ) ^ 2 * δ) ≤ (1 / 2 : ℝ) / (k : ℝ) ^ 2 := by
  let δ : ℝ := 1 / (2 * M)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hMδ : M * δ = 1 / 2 := by dsimp [δ]; field_simp
  have hnum := Capacity.eventually_capacity_numerics (fun k : ℕ => k ^ 2)
    (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)) δ (1 / 2) hδ (by norm_num)
  simp only [Nat.cast_pow] at hnum
  have hlim : Filter.Tendsto (fun k : ℕ => L * (3 * Real.pi / Real.sqrt (k : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa using Sphere.tendsto_mesh_bound_zero.const_mul L
  have hmesh := hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  have hgood : ∀ᶠ k : ℕ in Filter.atTop, 0 < k ∧
      L * (3 * Real.pi / Real.sqrt (k : ℝ)) ≤ 1 / 2 ∧
      M * δ ≤ 1 - Real.exp (-(k : ℝ) ^ 2 * δ) ∧
      Real.exp (1 - (k : ℝ) ^ 2 * δ) ≤ (1 / 2 : ℝ) / (k : ℝ) ^ 2 := by
    filter_upwards [hnum, hmesh, Filter.eventually_gt_atTop (0 : ℕ)] with k hn hm hk
    exact ⟨hk, hm.le, by simpa [hMδ] using hn.1, hn.2⟩
  obtain ⟨k, hk, hm, hs, hl⟩ := hgood.exists
  exact ⟨k, hk, δ, hδ, hm, hs, hl⟩

/-- One fixed finite independent conditional-cell source prior dominates every
member of a uniformly bounded and chart-Lipschitz normalized continuous family.
The count and prior are chosen before the parameter. -/
theorem exists_source_hit_capacity {X : Type*} (f : X → Source → ℝ)
    (hcontinuous : ∀ x, Continuous (f x))
    (hf : ∀ x, Integrable (f x) referenceMeasure)
    (hnonneg : ∀ x p, 0 ≤ f x p)
    (hnormalized : ∀ x, ∫ p, f x p ∂referenceMeasure = 1)
    (L M : ℝ) (hL : 0 ≤ L) (hM : 0 < M)
    (hvariation : ∀ x p q, |f x p - f x q| ≤
      L * Sphere.coordinateDistance (sphereSample p) (sphereSample q))
    (hbound : ∀ x p, f x p ≤ M) :
    ∃ k : ℕ, ∃ hk : 0 < k, ∀ x B, MeasurableSet B →
      (∫ p in B, f x p ∂referenceMeasure) ≤
        (Measure.pi (fun i : Fin (k ^ 2) =>
          ProbabilityTheory.cond referenceMeasure (finCell k hk i))).real
            {z : Fin (k ^ 2) → Source | ∃ i, z i ∈ B} := by
  obtain ⟨k, hk, δ, hδ, hm, hs, hl⟩ := exists_capacity_size L M hM
  refine ⟨k, hk, ?_⟩
  intro x B hB
  exact source_hit_capacity k hk (f x) (hcontinuous x) (hf x) (hnonneg x)
    (hnormalized x) L M δ hL (hvariation x) hm (hbound x) hδ hs hl B hB

end FinitePR.Square
