import QuantumProver.Computability.CollisionTradeoff.FiniteProbability

/-!
Actual finite product laws and their count moments.  No independence axiom is
used: the product law is defined by the product of its coordinate weights and
normalized using the finite distributive identity `Fintype.prod_sum`.
-/

namespace CollisionTradeoff

open scoped BigOperators Classical

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem eq_of_weight_eq (μ ν : FiniteLaw Ω) (h : ∀ ω, μ.weight ω = ν.weight ω) : μ = ν := by
  cases μ with
  | mk w hw ht =>
    cases ν with
    | mk v hv ht' =>
      have hfun : w = v := funext h
      cases hfun
      rfl

/-- The actual product distribution of independent copies of a finite law. -/
noncomputable def iid (μ : FiniteLaw Ω) {ι : Type*} [Fintype ι] [DecidableEq ι] :
    FiniteLaw (ι → Ω) where
  weight f := ∏ i, μ.weight (f i)
  nonneg f := Finset.prod_nonneg fun i _ => μ.nonneg (f i)
  total := by
    calc
      (∑ f : ι → Ω, ∏ i, μ.weight (f i)) = ∏ _i : ι, ∑ ω, μ.weight ω :=
        (Fintype.prod_sum (fun _i : ι => μ.weight)).symm
      _ = 1 := by simp [μ.total]

/-- Uniform weights on a finite nonempty type. -/
noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

theorem uniform_prob [Nonempty Ω] (E : Finset Ω) :
    (uniform Ω).prob E = E.card / (Fintype.card Ω : ℝ) := by
  simp [prob, uniform, div_eq_mul_inv]

theorem iid_uniform_eq_uniform [Nonempty Ω] {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (uniform Ω).iid (ι := ι) = uniform (ι → Ω) := by
  apply eq_of_weight_eq
  intro f
  simp [iid, uniform, Nat.cast_pow]

/-- Change finite outcome labels through an actual equivalence. -/
noncomputable def reindex {Λ : Type*} [Fintype Λ] (μ : FiniteLaw Ω) (e : Ω ≃ Λ) : FiniteLaw Λ where
  weight b := μ.weight (e.symm b)
  nonneg b := μ.nonneg (e.symm b)
  total := (e.symm.sum_comp μ.weight).trans μ.total

theorem uniform_reindex [Nonempty Ω] {Λ : Type*} [Fintype Λ] [Nonempty Λ] (e : Ω ≃ Λ) :
    (uniform Ω).reindex e = uniform Λ := by
  apply eq_of_weight_eq
  intro b
  simp [reindex, uniform, Fintype.card_congr e]

theorem prob_reindex {Λ : Type*} [Fintype Λ] (μ : FiniteLaw Ω) (e : Ω ≃ Λ)
    (H : Finset Λ) :
    (μ.reindex e).prob H = μ.prob (Finset.univ.filter (fun a => e a ∈ H)) := by
  rw [FiniteLaw.prob_eq_sum_ite, μ.prob_eq_sum_ite]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  apply Fintype.sum_equiv e.symm
  intro b
  simp [reindex]

variable (μ : FiniteLaw Ω) {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem iid_expect_prod (g : ι → Ω → ℝ) :
    (μ.iid (ι := ι)).expect (fun f => ∏ i, g i (f i)) = ∏ i, μ.expect (g i) := by
  unfold expect
  simp only [iid]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i ω => μ.weight ω * g i ω)).symm

theorem iid_expect_apply (g : Ω → ℝ) (i : ι) :
    (μ.iid (ι := ι)).expect (fun f => g (f i)) = μ.expect g := by
  have h := μ.iid_expect_prod (fun j ω => if j = i then g ω else 1)
  have hmean (j : ι) :
      μ.expect (fun ω => if j = i then g ω else 1) =
        if j = i then μ.expect g else 1 := by
    by_cases hj : j = i <;> simp [hj]
  simp_rw [hmean] at h
  simpa using h

theorem iid_expect_mul_apply (g h : Ω → ℝ) (i j : ι) (hij : i ≠ j) :
    (μ.iid (ι := ι)).expect (fun f => g (f i) * h (f j)) = μ.expect g * μ.expect h := by
  let G : ι → Ω → ℝ := fun k ω =>
    (if k = i then g ω else 1) * (if k = j then h ω else 1)
  have hmean (k : ι) : μ.expect (G k) =
      (if k = i then μ.expect g else 1) * (if k = j then μ.expect h else 1) := by
    by_cases hki : k = i <;> by_cases hkj : k = j
    · exact (hij (hki.symm.trans hkj)).elim
    · simp [G, hki, hij]
    · simp [G, hkj, Ne.symm hij]
    · simp [G, hki, hkj]
  calc
    (μ.iid (ι := ι)).expect (fun f => g (f i) * h (f j)) =
        (μ.iid (ι := ι)).expect (fun f => ∏ k, G k (f k)) := by
      congr 1
      funext f
      simp only [G, Finset.prod_mul_distrib]
      simp
    _ = ∏ k, μ.expect (G k) := μ.iid_expect_prod G
    _ = μ.expect g * μ.expect h := by simp_rw [hmean, Finset.prod_mul_distrib]; simp

theorem iid_expect_sum (g : Ω → ℝ) :
    (μ.iid (ι := ι)).expect (fun f => ∑ i, g (f i)) = (Fintype.card ι : ℝ) * μ.expect g := by
  rw [FiniteLaw.expect_sum]
  simp [μ.iid_expect_apply]

theorem iid_second_moment_sum (g : Ω → ℝ) :
    (μ.iid (ι := ι)).expect (fun f => (∑ i, g (f i)) ^ 2) =
      (Fintype.card ι : ℝ) ^ 2 * (μ.expect g) ^ 2 +
        (Fintype.card ι : ℝ) * (μ.expect (fun ω => g ω ^ 2) - (μ.expect g) ^ 2) := by
  let p := μ.expect g
  let v := μ.expect (fun ω => g ω ^ 2)
  have hpair (i j : ι) :
      (μ.iid (ι := ι)).expect (fun f => g (f i) * g (f j)) =
        p ^ 2 + if j = i then v - p ^ 2 else 0 := by
    by_cases hji : j = i
    · subst j
      have hs : (fun f : ι → Ω => g (f i) * g (f i)) =
          (fun f => g (f i) ^ 2) := by funext f; ring
      rw [hs, μ.iid_expect_apply (fun ω => g ω ^ 2) i]
      simp only [ite_true]
      dsimp [p, v]
      ring
    · rw [μ.iid_expect_mul_apply g g i j (Ne.symm hji)]
      simp [p, hji, pow_two]
  calc
    (μ.iid (ι := ι)).expect (fun f => (∑ i, g (f i)) ^ 2) =
        (μ.iid (ι := ι)).expect (fun f => ∑ i, ∑ j, g (f i) * g (f j)) := by
      congr 1
      funext f
      rw [pow_two, Fintype.sum_mul_sum]
    _ = ∑ i, ∑ j, (μ.iid (ι := ι)).expect (fun f => g (f i) * g (f j)) := by
      rw [FiniteLaw.expect_sum]
      simp_rw [FiniteLaw.expect_sum]
    _ = ∑ i : ι, ∑ j : ι, (p ^ 2 + if j = i then v - p ^ 2 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl fun j _ => hpair i j
    _ = _ := by
      simp [Finset.sum_add_distrib, p, v]
      ring

/-- Variance additivity for the defined iid finite law, derived from its weights. -/
theorem iid_variance_sum (g : Ω → ℝ) :
    (μ.iid (ι := ι)).variance (fun f => ∑ i, g (f i)) =
      (Fintype.card ι : ℝ) * μ.variance g := by
  rw [FiniteLaw.variance_eq_second_moment, μ.iid_second_moment_sum,
    μ.iid_expect_sum, μ.variance_eq_second_moment]
  ring

variable [DecidableEq Ω]

theorem expect_indicator (E : Finset Ω) :
    μ.expect (fun ω => if ω ∈ E then 1 else 0) = μ.prob E := by
  rw [μ.prob_eq_sum_ite]
  unfold expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : ω ∈ E <;> simp [hω]

theorem variance_indicator (E : Finset Ω) :
    μ.variance (fun ω => if ω ∈ E then 1 else 0) = μ.prob E * (1 - μ.prob E) := by
  rw [μ.variance_eq_second_moment]
  have hsquare : (fun ω : Ω => (if ω ∈ E then (1 : ℝ) else 0) ^ 2) =
      (fun ω => if ω ∈ E then 1 else 0) := by
    funext ω
    by_cases hω : ω ∈ E <;> simp [hω]
  rw [hsquare, μ.expect_indicator]
  ring

theorem iid_indicator_count_mean (E : Finset Ω) :
    (μ.iid (ι := ι)).expect (fun f => ∑ i, if f i ∈ E then (1 : ℝ) else 0) =
      (Fintype.card ι : ℝ) * μ.prob E := by
  rw [μ.iid_expect_sum (fun ω => if ω ∈ E then (1 : ℝ) else 0), μ.expect_indicator]

theorem iid_indicator_count_variance (E : Finset Ω) :
    (μ.iid (ι := ι)).variance (fun f => ∑ i, if f i ∈ E then (1 : ℝ) else 0) =
      (Fintype.card ι : ℝ) * μ.prob E * (1 - μ.prob E) := by
  rw [μ.iid_variance_sum (fun ω => if ω ∈ E then (1 : ℝ) else 0), μ.variance_indicator]
  ring

/-- The actual law of independent sample and outside records. -/
noncomputable def prod {Λ : Type*} [Fintype Λ] (ν : FiniteLaw Λ) : FiniteLaw (Ω × Λ) where
  weight p := μ.weight p.1 * ν.weight p.2
  nonneg p := mul_nonneg (μ.nonneg p.1) (ν.nonneg p.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ν.total, mul_one, μ.total]

theorem prod_uniform_eq_uniform [Nonempty Ω] {Λ : Type*} [Fintype Λ] [Nonempty Λ] :
    (uniform Ω).prod (uniform Λ) = uniform (Ω × Λ) := by
  apply eq_of_weight_eq
  intro p
  simp [prod, uniform, Fintype.card_prod, Nat.cast_mul, mul_comm]

theorem prob_prod_section {Λ : Type*} [Fintype Λ] (ν : FiniteLaw Λ)
    (H : Finset (Ω × Λ)) :
    (μ.prod ν).prob H = ∑ a, μ.weight a *
      ν.prob (Finset.univ.filter (fun b => (a, b) ∈ H)) := by
  rw [FiniteLaw.prob_eq_sum_ite, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [ν.prob_eq_sum_ite, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp [prod, mul_ite]

/-- Average proved outside-event bounds over complete good sample records. -/
theorem prob_prod_good_section_ge {Λ : Type*} [Fintype Λ] (ν : FiniteLaw Λ)
    (E : Finset Ω) (H : Ω → Λ → Prop) [DecidableRel H] (c : ℝ)
    (hH : ∀ a ∈ E, c ≤ ν.prob (Finset.univ.filter (H a))) :
    c * μ.prob E ≤ (μ.prod ν).prob
      (Finset.univ.filter (fun p => p.1 ∈ E ∧ H p.1 p.2)) := by
  let s : Ω → ℝ := fun a => if a ∈ E then ν.prob (Finset.univ.filter (H a)) else 0
  have hnonneg : ∀ a, 0 ≤ s a := by
    intro a
    by_cases ha : a ∈ E <;> simp [s, ha, ν.prob_nonneg]
  have hgood : ∀ a ∈ E, c ≤ s a := by
    intro a ha
    simpa [s, ha] using hH a ha
  have hprob : (μ.prod ν).prob
      (Finset.univ.filter (fun p => p.1 ∈ E ∧ H p.1 p.2)) = μ.expect s := by
    rw [μ.prob_prod_section]
    unfold expect
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ E <;> simp [s, ha, prob]
  rw [hprob]
  exact μ.expect_ge_event E s c hnonneg hgood

end FiniteLaw

/-- Count outside values lying in the complete sample's full-value image. -/
noncomputable def markedCount {Ω ι : Type*} [Fintype ι] [DecidableEq Ω]
    (E : Finset Ω) (f : ι → Ω) : ℝ := ∑ i, if f i ∈ E then 1 else 0

theorem uniform_marked_count_moments {N L r : ℕ} [NeZero N]
    (E : Finset (Fin N)) (hE : E.card = r) (hL : L ≤ N) :
    ((FiniteLaw.uniform (Fin N)).iid (ι := Fin L)).expect (markedCount E) =
      (L : ℝ) * ((r : ℝ) / N) ∧
    ((FiniteLaw.uniform (Fin N)).iid (ι := Fin L)).variance (markedCount E) ≤ r := by
  have hX : (markedCount E : (Fin L → Fin N) → ℝ) =
      (fun f => ∑ i, if f i ∈ E then (1 : ℝ) else 0) := by
    funext f
    unfold markedCount
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : f i ∈ E <;> simp [hi]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hp : (0 : ℝ) ≤ (r : ℝ) / N := by positivity
  have hLp : (L : ℝ) * ((r : ℝ) / N) ≤ r := by
    calc
      (L : ℝ) * ((r : ℝ) / N) ≤ (N : ℝ) * ((r : ℝ) / N) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hL) hp
      _ = r := by field_simp [ne_of_gt hNpos]
  constructor
  · rw [hX]
    simpa [FiniteLaw.uniform_prob, hE] using
      (FiniteLaw.uniform (Fin N)).iid_indicator_count_mean (ι := Fin L) E
  · rw [hX]
    simp only [FiniteLaw.iid_indicator_count_variance,
      FiniteLaw.uniform_prob, hE, Fintype.card_fin]
    calc
      (L : ℝ) * ((r : ℝ) / N) * (1 - (r : ℝ) / N) ≤
          (L : ℝ) * ((r : ℝ) / N) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by positivity) hp)
      _ ≤ r := by simpa using hLp

/-- Actual concentration for iid uniform outside values and any r-element sample image. -/
theorem uniform_outside_count_concentration {N r : ℕ} [NeZero N]
    (E : Finset (Fin N)) (hE : E.card = r) (hr : 1024 ≤ r) (hN : 64 * r ^ 2 ≤ N) :
    (15 : ℝ) / 16 ≤
      ((FiniteLaw.uniform (Fin N)).iid (ι := Fin (N - r))).prob
        (Finset.univ.filter (fun f =>
          3 * (r : ℝ) / 4 ≤ markedCount E f ∧ markedCount E f ≤ 5 * (r : ℝ) / 4)) := by
  let μ := (FiniteLaw.uniform (Fin N)).iid (ι := Fin (N - r))
  let X : (Fin (N - r) → Fin N) → ℝ := markedCount E
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hrreal : (1024 : ℝ) ≤ r := by exact_mod_cast hr
  have hrN : r ≤ N := by nlinarith
  have hm := uniform_marked_count_moments (L := N - r) E hE (Nat.sub_le N r)
  have hmean : μ.expect X = (r : ℝ) - (r : ℝ) ^ 2 / N := by
    rw [hm.1, Nat.cast_sub hrN]
    field_simp [ne_of_gt hNpos]
  have hgood := μ.prob_centered_good_ge X (r : ℝ) hrreal hm.2
  have hsmall : (r : ℝ) ^ 2 / N ≤ (1 : ℝ) / 64 := by
    have hlarge : (64 : ℝ) * (r : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
    apply (div_le_iff₀ hNpos).2
    nlinarith
  have hsub : (Finset.univ.filter (fun f => |X f - μ.expect X| ≤ (r : ℝ) / 8)) ⊆
      Finset.univ.filter (fun f =>
        3 * (r : ℝ) / 4 ≤ X f ∧ X f ≤ 5 * (r : ℝ) / 4) := by
    intro f hf
    have hdev := (Finset.mem_filter.mp hf).2
    rw [hmean] at hdev
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      marked_count_bounds (r : ℝ) N (X f) (by linarith) hNpos hsmall hdev⟩
  exact hgood.trans (μ.prob_mono hsub)

/-- A concrete modulo bucket bound, proved by injecting each bucket into quotients. -/
theorem mod_bucket_card_le (N B t : ℕ) :
    (Finset.univ.filter (fun y : Fin N => y.val % B = t)).card ≤ N / B + 1 := by
  classical
  let E := Finset.univ.filter (fun y : Fin N => y.val % B = t)
  have hcard : E.card ≤ (Finset.range (N / B + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun y : Fin N => y.val / B)
    · intro y _
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt y.isLt))
    · intro y hy z hz hyz
      apply Fin.ext
      have hy' : y.val % B = t := (Finset.mem_filter.mp hy).2
      have hz' : z.val % B = t := (Finset.mem_filter.mp hz).2
      change y.val / B = z.val / B at hyz
      have hry := Nat.mod_add_div y.val B
      have hrz := Nat.mod_add_div z.val B
      rw [hy', hyz] at hry
      rw [hz'] at hrz
      omega
  simpa [E] using hcard

theorem mod_bucket_fraction_le (N B t : ℕ) (hN : 0 < N) (hB : 0 < B) :
    ((Finset.univ.filter (fun y : Fin N => y.val % B = t)).card : ℝ) / N ≤
      1 / (B : ℝ) + 1 / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hb := mod_bucket_card_le N B t
  have hc : ((Finset.univ.filter (fun y : Fin N => y.val % B = t)).card : ℝ) ≤
      (N : ℝ) / B + 1 := by
    calc
      _ ≤ ((N / B + 1 : ℕ) : ℝ) := by exact_mod_cast hb
      _ ≤ (N : ℝ) / B + 1 := by
        push_cast
        have hdiv : ((N / B : ℕ) : ℝ) ≤ (N : ℝ) / B := Nat.cast_div_le
        exact add_le_add hdiv le_rfl
  calc
    _ ≤ ((N : ℝ) / B + 1) / N := div_le_div_of_nonneg_right hc hNpos.le
    _ = _ := by field_simp [ne_of_gt hNpos, ne_of_gt hBpos]

end CollisionTradeoff
