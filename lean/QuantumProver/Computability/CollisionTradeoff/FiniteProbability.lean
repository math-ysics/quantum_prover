import QuantumProver.Computability.CollisionTradeoff.Definitions

/-!
Finite probability inequalities used by the short-tag collision proof.

Every result below is proved from normalized nonnegative finite weights.
The file does not assume an algorithm, a binomial law, or a circuit resource bound.
-/

namespace CollisionTradeoff

open scoped BigOperators Classical

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

theorem prob_nonneg (E : Finset Ω) : 0 ≤ μ.prob E :=
  Finset.sum_nonneg fun ω _ => μ.nonneg ω

@[simp] theorem prob_univ : μ.prob Finset.univ = 1 := μ.total

theorem prob_mono {E F : Finset Ω} (h : E ⊆ F) : μ.prob E ≤ μ.prob F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro ω _ _
  exact μ.nonneg ω

theorem prob_le_one (E : Finset Ω) : μ.prob E ≤ 1 := by
  simpa using μ.prob_mono (Finset.subset_univ E)

theorem prob_compl (E : Finset Ω) : μ.prob Eᶜ = 1 - μ.prob E := by
  classical
  have h := Finset.sum_compl_add_sum E μ.weight
  change μ.prob Eᶜ + μ.prob E = ∑ ω, μ.weight ω at h
  rw [μ.total] at h
  linarith

theorem prob_eq_sum_ite (E : Finset Ω) :
    μ.prob E = ∑ ω, if ω ∈ E then μ.weight ω else 0 := by
  classical
  simpa only [prob, Finset.filter_mem_eq_inter, Finset.univ_inter] using
    (Finset.sum_filter (s := Finset.univ) (p := fun ω => ω ∈ E) (f := μ.weight))

theorem prob_union_le (E F : Finset Ω) : μ.prob (E ∪ F) ≤ μ.prob E + μ.prob F := by
  classical
  rw [μ.prob_eq_sum_ite, μ.prob_eq_sum_ite, μ.prob_eq_sum_ite,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hE : ω ∈ E <;> by_cases hF : ω ∈ F <;>
    simp [hE, hF, μ.nonneg ω]

theorem prob_biUnion_le {ι : Type*} (s : Finset ι) (E : ι → Finset Ω) :
    μ.prob (s.biUnion E) ≤ ∑ i ∈ s, μ.prob (E i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prob]
  | @insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (μ.prob_union_le (E i) (s.biUnion E)).trans (add_le_add le_rfl ih)

theorem prob_biUnion_le_card_mul {ι : Type*} (s : Finset ι) (E : ι → Finset Ω)
    (c : ℝ) (hE : ∀ i ∈ s, μ.prob (E i) ≤ c) :
    μ.prob (s.biUnion E) ≤ s.card * c := by
  calc
    μ.prob (s.biUnion E) ≤ ∑ i ∈ s, μ.prob (E i) := μ.prob_biUnion_le s E
    _ ≤ ∑ _i ∈ s, c := Finset.sum_le_sum hE
    _ = s.card * c := by simp

theorem expect_nonneg {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) : 0 ≤ μ.expect X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (hX ω)

theorem expect_mono {X Y : Ω → ℝ} (hXY : ∀ ω, X ω ≤ Y ω) :
    μ.expect X ≤ μ.expect Y :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hXY ω) (μ.nonneg ω)

@[simp] theorem expect_const (c : ℝ) : μ.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, μ.total]

theorem expect_add (X Y : Ω → ℝ) :
    μ.expect (fun ω => X ω + Y ω) = μ.expect X + μ.expect Y := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sum {ι : Type*} (s : Finset ι) (X : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, μ.expect (X i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_sq_deviation (X : Ω → ℝ) (a : ℝ) :
    μ.expect (fun ω => (X ω - a) ^ 2) =
      μ.expect (fun ω => X ω ^ 2) - 2 * a * μ.expect X + a ^ 2 := by
  unfold expect
  calc
    (∑ ω, μ.weight ω * (X ω - a) ^ 2) =
        ∑ ω, (μ.weight ω * X ω ^ 2 - 2 * a * (μ.weight ω * X ω) +
          a ^ 2 * μ.weight ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, μ.total]
      ring

theorem variance_eq_second_moment (X : Ω → ℝ) :
    μ.variance X = μ.expect (fun ω => X ω ^ 2) - (μ.expect X) ^ 2 := by
  unfold variance
  rw [μ.expect_sq_deviation]
  ring

/-- Finite second-moment Chebyshev inequality; the center need not be the mean. -/
theorem prob_abs_ge_le_second_moment (X : Ω → ℝ) (a c v : ℝ)
    (hc : 0 < c) (hv : μ.expect (fun ω => (X ω - a) ^ 2) ≤ v) :
    μ.prob (Finset.univ.filter (fun ω => c ≤ |X ω - a|)) ≤ v / c ^ 2 := by
  classical
  let E := Finset.univ.filter (fun ω => c ≤ |X ω - a|)
  have hmoment : μ.prob E * c ^ 2 ≤ v := by
    calc
      μ.prob E * c ^ 2 = ∑ ω ∈ E, μ.weight ω * c ^ 2 := by
        exact Finset.sum_mul E μ.weight (c ^ 2)
      _ ≤ ∑ ω ∈ E, μ.weight ω * (X ω - a) ^ 2 := by
        apply Finset.sum_le_sum
        intro ω hω
        have hdev := (Finset.mem_filter.mp hω).2
        have hsq : c ^ 2 ≤ (X ω - a) ^ 2 := by
          have h := (sq_le_sq₀ hc.le (abs_nonneg (X ω - a))).2 hdev
          simpa only [sq_abs] using h
        exact mul_le_mul_of_nonneg_left hsq (μ.nonneg ω)
      _ ≤ μ.expect (fun ω => (X ω - a) ^ 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
        intro ω _ _
        exact mul_nonneg (μ.nonneg ω) (sq_nonneg _)
      _ ≤ v := hv
  exact (le_div_iff₀ (sq_pos_of_pos hc)).2 hmoment

theorem prob_abs_le_ge_second_moment (X : Ω → ℝ) (a c v : ℝ)
    (hc : 0 < c) (hv : μ.expect (fun ω => (X ω - a) ^ 2) ≤ v) :
    1 - v / c ^ 2 ≤ μ.prob (Finset.univ.filter (fun ω => |X ω - a| ≤ c)) := by
  classical
  let E := Finset.univ.filter (fun ω => |X ω - a| ≤ c)
  let F := Finset.univ.filter (fun ω => c ≤ |X ω - a|)
  have hEF : Eᶜ ⊆ F := by
    intro ω hω
    have hnot : ¬ |X ω - a| ≤ c := by simpa [E] using hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (lt_of_not_ge hnot).le⟩
  have h := (μ.prob_mono hEF).trans (μ.prob_abs_ge_le_second_moment X a c v hc hv)
  rw [μ.prob_compl] at h
  linarith

/-- The exact count-concentration probability used in the proof. -/
theorem prob_centered_good_ge (X : Ω → ℝ) (r : ℝ)
    (hr : 1024 ≤ r) (hv : μ.variance X ≤ r) :
    (15 : ℝ) / 16 ≤
      μ.prob (Finset.univ.filter (fun ω => |X ω - μ.expect X| ≤ r / 8)) := by
  classical
  have hrpos : 0 < r := by linarith
  have h := μ.prob_abs_le_ge_second_moment X (μ.expect X) (r / 8) r
    (by positivity) hv
  have hratio : r / (r / 8) ^ 2 = 64 / r := by
    field_simp [ne_of_gt hrpos]
    ring
  have htail : 64 / r ≤ (1 : ℝ) / 16 := by
    apply (div_le_iff₀ hrpos).2
    nlinarith
  rw [hratio] at h
  linarith

/-- A nonnegative outcome probability bounded on an event contributes its event mass. -/
theorem expect_ge_event (E : Finset Ω) (X : Ω → ℝ) (c : ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (hE : ∀ ω ∈ E, c ≤ X ω) :
    c * μ.prob E ≤ μ.expect X := by
  classical
  rw [μ.prob_eq_sum_ite, Finset.mul_sum]
  unfold expect
  apply Finset.sum_le_sum
  intro ω _
  by_cases hω : ω ∈ E
  · simp only [hω, ite_true]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hE ω hω) (μ.nonneg ω)
  · simp only [hω, ite_false, mul_zero]
    exact mul_nonneg (μ.nonneg ω) (hX ω)

theorem success_product_bound (E F : Finset Ω) (s : Ω → ℝ)
    (hE : (63 : ℝ) / 64 ≤ μ.prob E)
    (hF : (15 : ℝ) / 16 * μ.prob E ≤ μ.prob (E ∩ F))
    (hs : ∀ ω, 0 ≤ s ω) (hgood : ∀ ω ∈ E ∩ F, (3 : ℝ) / 4 ≤ s ω) :
    (2835 : ℝ) / 4096 ≤ μ.expect s := by
  have h := μ.expect_ge_event (E ∩ F) s ((3 : ℝ) / 4) hs hgood
  have hEF : (945 : ℝ) / 1024 ≤ μ.prob (E ∩ F) := by nlinarith
  nlinarith

end FiniteLaw

/-- Bucket probabilities with an upper bound give the required pair-collision bound. -/
theorem sum_squares_le_bucket_bound {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (c : ℝ) (hq : ∀ i, 0 ≤ q i) (htotal : ∑ i, q i = 1)
    (hbound : ∀ i, q i ≤ c) : ∑ i, q i ^ 2 ≤ c := by
  calc
    (∑ i, q i ^ 2) ≤ ∑ i, c * q i := by
      apply Finset.sum_le_sum
      intro i _
      simpa [pow_two, mul_comm] using mul_le_mul_of_nonneg_right (hbound i) (hq i)
    _ = c := by rw [← Finset.mul_sum, htotal, mul_one]

theorem tag_union_error_le (r N B : ℝ) (hr : 1 ≤ r)
    (hN : 64 * r ^ 2 ≤ N) (hB : 64 * r ^ 2 ≤ B) :
    (r * (r - 1) / 2) * (1 / B + 1 / N) ≤ (1 : ℝ) / 64 := by
  have hrpos : 0 < r := by linarith
  have hden : 0 < 64 * r ^ 2 := by positivity
  have hNpos : 0 < N := lt_of_lt_of_le hden hN
  have hBpos : 0 < B := lt_of_lt_of_le hden hB
  have hb := one_div_le_one_div_of_le hden hB
  have hn := one_div_le_one_div_of_le hden hN
  have hq : 1 / B + 1 / N ≤ 1 / (32 * r ^ 2) := by
    calc
      1 / B + 1 / N ≤ 1 / (64 * r ^ 2) + 1 / (64 * r ^ 2) := add_le_add hb hn
      _ = _ := by field_simp [ne_of_gt hrpos]; ring
  have hpair : r * (r - 1) / 2 ≤ r ^ 2 / 2 := by nlinarith
  calc
    (r * (r - 1) / 2) * (1 / B + 1 / N) ≤ (r ^ 2 / 2) * (1 / B + 1 / N) :=
      mul_le_mul_of_nonneg_right hpair (by positivity)
    _ ≤ (r ^ 2 / 2) * (1 / (32 * r ^ 2)) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = (1 : ℝ) / 64 := by field_simp [ne_of_gt hrpos]; ring

theorem marked_count_bounds (r N K : ℝ) (hr : 1 ≤ r) (hN : 0 < N)
    (hsmall : r ^ 2 / N ≤ (1 : ℝ) / 64)
    (hdev : |K - (r - r ^ 2 / N)| ≤ r / 8) :
    3 * r / 4 ≤ K ∧ K ≤ 5 * r / 4 := by
  have hnonneg : 0 ≤ r ^ 2 / N := div_nonneg (sq_nonneg r) hN.le
  rw [abs_le] at hdev
  constructor <;> nlinarith

theorem success_constant_gt_two_thirds : (2 : ℝ) / 3 < 2835 / 4096 := by norm_num

end CollisionTradeoff
