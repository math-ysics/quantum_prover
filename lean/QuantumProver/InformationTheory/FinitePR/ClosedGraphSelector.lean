import Mathlib

/-!
Measurable selection for a closed relation with compact metrizable codomain.
The construction uses measurable least-index shrinking-ball approximations,
summable consecutive distances, and their pointwise limit. No selection theorem
is assumed. This module is independent of the quantum/PR formalization.
-/

namespace FinitePR.Selection

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [CompactSpace Y]

/-- Parameters whose fiber meets a specified closed subset of the compact codomain. -/
def closedHit (G : Set (X × Y)) (C : Set Y) : Set X :=
  {x | ∃ y, y ∈ C ∧ (x, y) ∈ G}

theorem isClosed_closedHit {G : Set (X × Y)} (hG : IsClosed G)
    {C : Set Y} (hC : IsClosed C) : IsClosed (closedHit G C) := by
  have heq : closedHit G C = Prod.fst '' (G ∩ Set.univ.prod C) := by
    ext x
    constructor
    · rintro ⟨y, hyC, hyG⟩
      exact ⟨(x, y), ⟨hyG, ⟨Set.mem_univ x, hyC⟩⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨hpG, hpC⟩, hp⟩
      dsimp at hp
      subst a
      exact ⟨b, hpC.2, hpG⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ (hG.inter (isClosed_univ.prod hC))

theorem measurableSet_closedHit {G : Set (X × Y)} (hG : IsClosed G)
    {C : Set Y} (hC : IsClosed C) : MeasurableSet (closedHit G C) :=
  (isClosed_closedHit hG hC).measurableSet

private noncomputable def radius (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

private theorem radius_pos (n : ℕ) : 0 < radius n := by
  exact pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n

private theorem radius_succ_le (n : ℕ) : radius (n + 1) ≤ radius n := by
  dsimp [radius]
  rw [pow_succ]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]

private theorem radius_tendsto : Tendsto radius atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- A measurable dense-center index with a point of the fiber within the given radius. -/
private def Approximation (G : Set (X × Y)) (q : ℕ → Y) (n : ℕ) :=
  {a : X → ℕ // Measurable a ∧
    ∀ x, ∃ y, (x, y) ∈ G ∧ dist y (q (a x)) ≤ radius n}

private noncomputable def firstApprox {G : Set (X × Y)} (hG : IsClosed G)
    (hne : ∀ x, ∃ y, (x, y) ∈ G) (q : ℕ → Y) (hq : DenseRange q) :
    Approximation G q 0 := by
  classical
  let P : X → ℕ → Prop := fun x k =>
    x ∈ closedHit G (Metric.closedBall (q k) (radius 0))
  have hp : ∀ x, ∃ k, P x k := by
    intro x
    obtain ⟨y, hy⟩ := hne x
    obtain ⟨k, hk⟩ := hq.exists_dist_lt y (radius_pos 0)
    exact ⟨k, y, hk.le, hy⟩
  refine ⟨(fun x => Nat.find (hp x)), measurable_find hp (fun k =>
    measurableSet_closedHit hG Metric.isClosed_closedBall), ?_⟩
  intro x
  obtain ⟨y, hyC, hyG⟩ := Nat.find_spec (hp x)
  exact ⟨y, hyG, hyC⟩

/-- Refine the radius while keeping a summable movement bound. -/
private noncomputable def refineApprox {G : Set (X × Y)} (hG : IsClosed G)
    (q : ℕ → Y) (hq : DenseRange q) (n : ℕ) (a : Approximation G q n) :
    {b : Approximation G q (n + 1) //
      ∀ x, dist (q (a.1 x)) (q (b.1 x)) ≤ 2 * radius n} := by
  classical
  let P : X → ℕ → Prop := fun x k =>
    x ∈ closedHit G (Metric.closedBall (q k) (radius (n + 1))) ∧
      dist (q (a.1 x)) (q k) ≤ 2 * radius n
  have hp : ∀ x, ∃ k, P x k := by
    intro x
    obtain ⟨y, hyG, hyd⟩ := a.2.2 x
    obtain ⟨k, hk⟩ := hq.exists_dist_lt y (radius_pos (n + 1))
    refine ⟨k, ⟨y, hk.le, hyG⟩, ?_⟩
    calc
      dist (q (a.1 x)) (q k) ≤ dist (q (a.1 x)) y + dist y (q k) :=
        dist_triangle _ _ _
      _ ≤ radius n + radius (n + 1) :=
        add_le_add (by simpa only [dist_comm] using hyd) hk.le
      _ ≤ 2 * radius n := by linarith [radius_succ_le n]
  have hm : ∀ k, MeasurableSet {x | P x k} := by
    intro k
    exact (measurableSet_closedHit hG Metric.isClosed_closedBall).inter
      (measurableSet_le
        ((measurable_from_nat.comp a.2.1).dist measurable_const) measurable_const)
  let b : X → ℕ := fun x => Nat.find (hp x)
  refine ⟨⟨b, measurable_find hp hm, ?_⟩, ?_⟩
  · intro x
    obtain ⟨y, hyC, hyG⟩ := (Nat.find_spec (hp x)).1
    exact ⟨y, hyG, hyC⟩
  · intro x
    exact (Nat.find_spec (hp x)).2

/-- A Borel measurable selector of every nonempty fiber of a closed relation.

Only the codomain is required compact. The domain can be any topological
measurable space whose open sets are measurable. Nonempty Y is harmless for the
intended coupling application; it permits a fixed dense sequence.
-/
theorem exists_measurable_selector [Nonempty Y] (G : Set (X × Y))
    (hG : IsClosed G) (hne : ∀ x, ∃ y, (x, y) ∈ G) :
    ∃ s : X → Y, Measurable s ∧ ∀ x, (x, s x) ∈ G := by
  classical
  obtain ⟨q, hq⟩ := exists_dense_seq Y
  let A : (n : ℕ) → Approximation G q n := fun n =>
    Nat.rec (firstApprox hG hne q hq)
      (fun n a => (refineApprox hG q hq n a).1) n
  let f : ℕ → X → Y := fun n x => q ((A n).1 x)
  have hf : ∀ n, Measurable (f n) := fun n =>
    measurable_from_nat.comp (A n).2.1
  have hdist : ∀ n x, dist (f n x) (f (n + 1) x) ≤ 2 * radius n := by
    intro n x
    change dist (q ((A n).1 x))
      (q (((refineApprox hG q hq n (A n)).1).1 x)) ≤ 2 * radius n
    exact (refineApprox hG q hq n (A n)).2 x
  have hcauchy (x : X) : CauchySeq (fun n => f n x) := by
    apply cauchySeq_of_le_geometric (1 / 2) 2 (by norm_num)
    intro n
    exact hdist n x
  have hex : ∀ x, ∃ y, Tendsto (fun n => f n x) atTop (𝓝 y) :=
    fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  choose s hs using hex
  refine ⟨s, measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.mpr hs), ?_⟩
  intro x
  have hnear : ∀ n, ∃ y, (x, y) ∈ G ∧ dist y (f n x) ≤ radius n :=
    fun n => (A n).2.2 x
  choose z hz hzd using hnear
  have hzero : Tendsto (fun n => dist (f n x) (z n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => dist_nonneg)
      (fun n => by simpa only [dist_comm] using hzd n) radius_tendsto
  have hztend : Tendsto z atTop (𝓝 (s x)) := (hs x).congr_dist hzero
  exact hG.mem_of_tendsto (tendsto_const_nhds.prodMk_nhds hztend)
    (Eventually.of_forall hz)

end FinitePR.Selection

namespace FinitePR.Selection

/-- Topological version: no chosen metric appears in the public hypotheses. -/
theorem exists_measurable_selector_of_metrizable {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [CompactSpace Y] [Nonempty Y]
    (G : Set (X × Y)) (hG : IsClosed G) (hne : ∀ x, ∃ y, (x, y) ∈ G) :
    ∃ s : X → Y, Measurable s ∧ ∀ x, (x, s x) ∈ G := by
  letI : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
  exact exists_measurable_selector G hG hne

end FinitePR.Selection
