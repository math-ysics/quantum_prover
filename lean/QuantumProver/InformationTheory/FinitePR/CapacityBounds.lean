import Mathlib

/-!
Finite-product inequalities for the hitting capacity of a stratified random list.
-/

namespace FinitePR.Capacity

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Filter

/-- The two capacity numerical conditions hold along every unbounded list size.

This gives a fixed sufficiently large finite list size.
-/
theorem eventually_capacity_numerics (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ j in atTop,
      (1 / 2 : ℝ) ≤ 1 - Real.exp (-(N j : ℝ) * δ) ∧
      Real.exp (1 - (N j : ℝ) * δ) ≤ ε / (N j : ℝ) := by
  have hreal : Tendsto (fun j => (N j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hzero : Tendsto (fun j => Real.exp (-(N j : ℝ) * δ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_zero, one_mul, neg_mul, mul_neg,
      mul_comm] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 δ hδ).comp hreal
  have hone : Tendsto (fun j => (N j : ℝ) * Real.exp (1 - (N j : ℝ) * δ))
      atTop (𝓝 0) := by
    simpa [Real.rpow_one, sub_eq_add_neg, Real.exp_add,
      neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 δ hδ).comp hreal).const_mul
        (Real.exp 1)
  have hsmall := hzero.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  have hlarge := hone.eventually_lt_const hε
  have hpositive := hreal.eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hsmall, hlarge, hpositive] with j hs hl hp
  constructor
  · linarith
  · apply (le_div_iff₀ hp).mpr
    simpa [mul_comm] using hl.le

/-- Independent finite-list samples give the exact product hitting probability. -/
theorem product_list_hit_probability {S ι : Type*} [MeasurableSpace S]
    [Fintype ι] (μ : ι → Measure S) [∀ i, IsProbabilityMeasure (μ i)]
    (B : Set S) (hB : MeasurableSet B) :
    (Measure.pi μ).real {z : ι → S | ∃ i, z i ∈ B} =
      1 - ∏ i, (1 - (μ i).real B) := by
  classical
  let R : Set (ι → S) := Set.pi Set.univ (fun _ => Bᶜ)
  have hR : MeasurableSet R :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => hB.compl)
  have hhit : {z : ι → S | ∃ i, z i ∈ B} = Rᶜ := by
    ext z
    simp [R, Set.mem_pi]
  have hmiss : (Measure.pi μ).real R = ∏ i, (μ i).real Bᶜ := by
    simp only [R, Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  rw [hhit, measureReal_compl hR, probReal_univ, hmiss]
  simp_rw [measureReal_compl hB, probReal_univ]

/-- The conditional law on an equal-mass cell has the expected intersection mass. -/
theorem conditioned_cell_mass {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (C B : Set S) (hC : MeasurableSet C)
    (n : ℝ) (hmass : μ.real C = 1 / n) :
    (ProbabilityTheory.cond μ C).real B = n * μ.real (C ∩ B) := by
  rw [Measure.real, ProbabilityTheory.cond_apply hC, ENNReal.toReal_mul,
    ENNReal.toReal_inv]
  change (μ.real C)⁻¹ * μ.real (C ∩ B) = n * μ.real (C ∩ B)
  rw [hmass]
  simp

/-- The probability of missing a list is bounded by an exponential. -/
theorem prod_one_sub_le_exp_neg_sum {ι : Type*} (s : Finset ι) (β : ι → ℝ)
    (hβ : ∀ i ∈ s, β i ≤ 1) :
    (∏ i ∈ s, (1 - β i)) ≤ Real.exp (-(∑ i ∈ s, β i)) := by
  calc
    (∏ i ∈ s, (1 - β i)) ≤ ∏ i ∈ s, Real.exp (-β i) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact sub_nonneg.mpr (hβ i hi)
      · intro i _
        simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-β i)
    _ = Real.exp (-(∑ i ∈ s, β i)) := by
      rw [← Real.exp_sum, Finset.sum_neg_distrib]

/-- The exponential hitting function lies above its chord from zero to `δ`. -/
theorem exp_hit_chord (n t δ M : ℝ) (hδ : 0 < δ) (ht : 0 ≤ t) (htδ : t ≤ δ)
    (hgap : M * δ ≤ 1 - Real.exp (-n * δ)) :
    M * t ≤ 1 - Real.exp (-n * t) := by
  have ha : 0 ≤ t / δ := div_nonneg ht hδ.le
  have hb : 0 ≤ 1 - t / δ := by
    exact sub_nonneg.mpr ((div_le_one hδ).mpr htδ)
  have hab : t / δ + (1 - t / δ) = 1 := by ring
  have hconv := convexOn_exp.2
    (Set.mem_univ (-n * δ)) (Set.mem_univ (0 : ℝ)) ha hb hab
  simp only [smul_eq_mul, Real.exp_zero] at hconv
  have hx : t / δ * (-n * δ) + (1 - t / δ) * 0 = -n * t := by
    field_simp [hδ.ne']
    ring
  rw [hx] at hconv
  have hmul := mul_le_mul_of_nonneg_left hgap ha
  have heq : t / δ * (M * δ) = M * t := by
    field_simp [hδ.ne']
  rw [heq] at hmul
  nlinarith

/-- The small-set half of the all-Borel hitting-capacity estimate. -/
theorem small_set_capacity {ι : Type*} [Fintype ι] (β : ι → ℝ)
    (n t δ M ν : ℝ) (hβ : ∀ i, β i ≤ 1)
    (hsum : ∑ i, β i = n * t) (hδ : 0 < δ) (ht : 0 ≤ t) (htδ : t ≤ δ)
    (hgap : M * δ ≤ 1 - Real.exp (-n * δ)) (hν : ν ≤ M * t) :
    ν ≤ 1 - ∏ i, (1 - β i) := by
  have hprod := prod_one_sub_le_exp_neg_sum Finset.univ β (fun i _ => hβ i)
  rw [hsum] at hprod
  have hchord := exp_hit_chord n t δ M hδ ht htδ hgap
  have hneg : -(n * t) = -n * t := by ring
  rw [hneg] at hprod
  linarith

/-- A distinguished positive cell controls the large-set missed-list mass.

There is no division by `1 - β d`, so the endpoint `β d = 1` is included.
-/
theorem distinguished_miss_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → ℝ) (d : ι) (D K : ℝ) (hβ : ∀ i, β i ≤ 1)
    (hsum : D ≤ ∑ i, β i) (hcap : Real.exp (1 - D) ≤ K) :
    (∏ i, (1 - β i)) ≤ (1 - β d) * K := by
  have hd : 0 ≤ 1 - β d := sub_nonneg.mpr (hβ d)
  have hprod := prod_one_sub_le_exp_neg_sum (Finset.univ.erase d) β
    (fun i _ => hβ i)
  have hsumd := Finset.add_sum_erase Finset.univ β (Finset.mem_univ d)
  have harg : -(∑ i ∈ Finset.univ.erase d, β i) ≤ 1 - D := by
    linarith [hβ d]
  calc
    (∏ i, (1 - β i)) = (1 - β d) * ∏ i ∈ Finset.univ.erase d, (1 - β i) :=
      (Finset.mul_prod_erase Finset.univ (fun i => 1 - β i)
        (Finset.mem_univ d)).symm
    _ ≤ (1 - β d) * Real.exp (-(∑ i ∈ Finset.univ.erase d, β i)) :=
      mul_le_mul_of_nonneg_left hprod hd
    _ ≤ (1 - β d) * Real.exp (1 - D) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hd
    _ ≤ (1 - β d) * K := mul_le_mul_of_nonneg_left hcap hd

/-- The large-set half of the hitting-capacity estimate for a normalized target. -/
theorem large_set_capacity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → ℝ) (d : ι) (D K ν : ℝ) (hβ : ∀ i, β i ≤ 1)
    (hsum : D ≤ ∑ i, β i) (hcap : Real.exp (1 - D) ≤ K)
    (hcomplement : (1 - β d) * K ≤ 1 - ν) :
    ν ≤ 1 - ∏ i, (1 - β i) := by
  have hmiss := distinguished_miss_bound β d D K hβ hsum hcap
  linarith

/-- Both branches cover every set mass, with a fixed positive-cell witness. -/
theorem all_set_capacity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → ℝ) (n t δ M K ν : ℝ) (hβ : ∀ i, β i ≤ 1)
    (hn : 0 ≤ n) (hsum : ∑ i, β i = n * t)
    (hδ : 0 < δ) (ht : 0 ≤ t) (hgap : M * δ ≤ 1 - Real.exp (-n * δ))
    (hν : ν ≤ M * t) (hcap : Real.exp (1 - n * δ) ≤ K)
    (hcell : ∃ d, (1 - β d) * K ≤ 1 - ν) :
    ν ≤ 1 - ∏ i, (1 - β i) := by
  by_cases htδ : t ≤ δ
  · exact small_set_capacity β n t δ M ν hβ hsum hδ ht htδ hgap hν
  · obtain ⟨d, hd⟩ := hcell
    have hsumlarge : n * δ ≤ ∑ i, β i := by
      rw [hsum]
      exact mul_le_mul_of_nonneg_left (le_of_not_ge htδ) hn
    exact large_set_capacity β d (n * δ) K ν hβ hsumlarge hcap hd

/-- A uniform density upper bound supplies the small-set target-mass bound. -/
theorem setIntegral_le_density_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] (f : S → ℝ) (hf : Integrable f μ)
    (B : Set S) (hB : MeasurableSet B) (M : ℝ) (hbound : ∀ z, f z ≤ M) :
    (∫ z in B, f z ∂μ) ≤ M * μ.real B := by
  calc
    (∫ z in B, f z ∂μ) ≤ ∫ _ in B, M ∂μ := by
      apply setIntegral_mono_on hf.integrableOn
        (integrableOn_const (measure_ne_top μ B)) hB
      intro z _
      exact hbound z
    _ = M * μ.real B := by simp [mul_comm]

/-- One cell on which the density is positive supplies the complement bound. -/
theorem positive_cell_complement_mass {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] (f : S → ℝ) (hf : Integrable f μ)
    (C B : Set S) (hC : MeasurableSet C) (hB : MeasurableSet B)
    (ε : ℝ) (hnonneg : ∀ z, 0 ≤ f z) (hcell : ∀ z ∈ C, ε ≤ f z) :
    ε * μ.real (C \ B) ≤ ∫ z in Bᶜ, f z ∂μ := by
  calc
    ε * μ.real (C \ B) ≤ ∫ z in C \ B, f z ∂μ := by
      apply setIntegral_ge_of_const_le_real (hC.diff hB) (measure_ne_top μ (C \ B))
      · intro z hz
        exact hcell z hz.1
      · exact hf.integrableOn
    _ ≤ ∫ z in Bᶜ, f z ∂μ := by
      apply setIntegral_mono_set hf.integrableOn
      · exact ae_of_all _ hnonneg
      · exact Filter.Eventually.of_forall (fun z hz => hz.2)

/-- A finite equal-mass partition gives every required hitting-capacity bound.

The right side is the stratified-list hitting expression. Proving that these
bounds yield a jointly Borel exact selection kernel is a separate obligation.
-/
theorem partition_capacity {S ι : Type*} [MeasurableSpace S]
    [Fintype ι] [DecidableEq ι] (μ : Measure S) [IsProbabilityMeasure μ]
    (C : ι → Set S) (hC : ∀ i, MeasurableSet (C i))
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : (⋃ i, C i) = Set.univ)
    (n : ℝ) (hn : 0 < n) (hmass : ∀ i, μ.real (C i) = 1 / n)
    (f : S → ℝ) (hf : Integrable f μ) (hnonneg : ∀ z, 0 ≤ f z)
    (hnormalized : ∫ z, f z ∂μ = 1) (M ε δ : ℝ)
    (hbound : ∀ z, f z ≤ M) (hpositive : ∃ d, ∀ z ∈ C d, ε ≤ f z)
    (hδ : 0 < δ) (hsmall : M * δ ≤ 1 - Real.exp (-n * δ))
    (hlarge : Real.exp (1 - n * δ) ≤ ε / n)
    (B : Set S) (hB : MeasurableSet B) :
    (∫ z in B, f z ∂μ) ≤ 1 - ∏ i, (1 - n * μ.real (C i ∩ B)) := by
  let β : ι → ℝ := fun i => n * μ.real (C i ∩ B)
  have hβ : ∀ i, β i ≤ 1 := by
    intro i
    calc
      β i = n * μ.real (C i ∩ B) := rfl
      _ ≤ n * μ.real (C i) :=
        mul_le_mul_of_nonneg_left (measureReal_mono Set.inter_subset_left) hn.le
      _ = 1 := by rw [hmass i]; field_simp [hn.ne']
  have hdisjointB : Pairwise (fun i j => Disjoint (C i ∩ B) (C j ∩ B)) := by
    intro i j hij
    exact (hdisjoint hij).mono Set.inter_subset_left Set.inter_subset_left
  have hcoverB : (⋃ i, C i ∩ B) = B := by
    rw [← Set.iUnion_inter, hcover, Set.univ_inter]
  have hmeasureSum := measureReal_iUnion_fintype (μ := μ) hdisjointB
    (fun i => (hC i).inter hB)
  rw [hcoverB] at hmeasureSum
  have hsum : ∑ i, β i = n * μ.real B := by
    dsimp [β]
    rw [← Finset.mul_sum, ← hmeasureSum]
  have htarget := setIntegral_le_density_bound μ f hf B hB M hbound
  have hcell : ∃ d, (1 - β d) * (ε / n) ≤ 1 - ∫ z in B, f z ∂μ := by
    obtain ⟨d, hd⟩ := hpositive
    refine ⟨d, ?_⟩
    have hcomplement := positive_cell_complement_mass μ f hf (C d) B (hC d) hB
      ε hnonneg hd
    rw [setIntegral_compl hB hf, hnormalized] at hcomplement
    have hdiff : μ.real (C d \ B) = (1 - β d) / n := by
      have hadd := measureReal_inter_add_sdiff (μ := μ) (s := C d) hB
      rw [hmass d] at hadd
      dsimp [β]
      field_simp [hn.ne'] at hadd ⊢
      nlinarith
    rw [hdiff] at hcomplement
    have hfactor : ε * ((1 - β d) / n) = (1 - β d) * (ε / n) := by ring
    rw [hfactor] at hcomplement
    exact hcomplement
  exact all_set_capacity β n (μ.real B) δ M (ε / n) (∫ z in B, f z ∂μ)
    hβ hn.le hsum hδ measureReal_nonneg hsmall htarget hlarge hcell

/-- The actual fixed stratified list dominates the target law on every set.

This verifies the capacity hypothesis for exact sampling. It does not assume a
coupling theorem or assert that a measurable index-selection rule exists.
-/
theorem stratified_list_hit_capacity {S ι : Type*} [MeasurableSpace S]
    [Fintype ι] [DecidableEq ι] (μ : Measure S) [IsProbabilityMeasure μ]
    (C : ι → Set S) (hC : ∀ i, MeasurableSet (C i))
    (hdisjoint : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : (⋃ i, C i) = Set.univ)
    (n : ℝ) (hn : 0 < n) (hmass : ∀ i, μ.real (C i) = 1 / n)
    (f : S → ℝ) (hf : Integrable f μ) (hnonneg : ∀ z, 0 ≤ f z)
    (hnormalized : ∫ z, f z ∂μ = 1) (M ε δ : ℝ)
    (hbound : ∀ z, f z ≤ M) (hpositive : ∃ d, ∀ z ∈ C d, ε ≤ f z)
    (hδ : 0 < δ) (hsmall : M * δ ≤ 1 - Real.exp (-n * δ))
    (hlarge : Real.exp (1 - n * δ) ≤ ε / n)
    (B : Set S) (hB : MeasurableSet B) :
    (∫ z in B, f z ∂μ) ≤
      (Measure.pi (fun i => ProbabilityTheory.cond μ (C i))).real
        {z : ι → S | ∃ i, z i ∈ B} := by
  have hcellne (i : ι) : μ (C i) ≠ 0 := by
    intro hzero
    have hrzero : μ.real (C i) = 0 := by simp [Measure.real, hzero]
    rw [hmass i] at hrzero
    have hpositiveMass : 0 < 1 / n := one_div_pos.mpr hn
    linarith
  letI : ∀ i, IsProbabilityMeasure (ProbabilityTheory.cond μ (C i)) :=
    fun i => ProbabilityTheory.cond_isProbabilityMeasure (hcellne i)
  rw [product_list_hit_probability (fun i => ProbabilityTheory.cond μ (C i)) B hB]
  have hcond : ∀ i, (ProbabilityTheory.cond μ (C i)).real B =
      n * μ.real (C i ∩ B) :=
    fun i => conditioned_cell_mass μ (C i) B (hC i) n (hmass i)
  simp_rw [hcond]
  exact partition_capacity μ C hC hdisjoint hcover n hn hmass f hf hnonneg
    hnormalized M ε δ hbound hpositive hδ hsmall hlarge B hB

end FinitePR.Capacity
