import QuantumProver.Computability.CollisionTradeoff.ProductMoments

/-!
The actual probability of a good short-tag sample under a finite product law.
The pair equality probability is computed from the coordinate weights, and the
bad-sample event is an explicitly proved union over unordered index pairs.
-/

namespace CollisionTradeoff

open scoped BigOperators Classical

namespace FiniteLaw

variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [DecidableEq Ω] [DecidableEq Λ]
  (μ : FiniteLaw Ω)

noncomputable def tagProb (h : Ω → Λ) (t : Λ) : ℝ :=
  μ.prob (Finset.univ.filter (fun ω => h ω = t))

theorem tagProb_nonneg (h : Ω → Λ) (t : Λ) : 0 ≤ μ.tagProb h t := μ.prob_nonneg _

theorem sum_tagProb (h : Ω → Λ) : ∑ t, μ.tagProb h t = 1 := by
  simp only [tagProb]
  simp_rw [μ.prob_eq_sum_ite]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_comm]
  simpa [eq_comm] using μ.total

theorem expect_tag_indicator (h : Ω → Λ) (t : Λ) :
    μ.expect (fun ω => if h ω = t then 1 else 0) = μ.tagProb h t := by
  simpa [tagProb] using μ.expect_indicator (Finset.univ.filter (fun ω => h ω = t))

theorem iid_prob_tag_equal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : Ω → Λ) (i j : ι) (hij : i ≠ j) :
    (μ.iid (ι := ι)).prob (Finset.univ.filter (fun f => h (f i) = h (f j))) =
      ∑ t, (μ.tagProb h t) ^ 2 := by
  let ν := μ.iid (ι := ι)
  have hpoint (f : ι → Ω) :
      (if h (f i) = h (f j) then (1 : ℝ) else 0) =
        ∑ t : Λ, (if h (f i) = t then (1 : ℝ) else 0) *
          (if h (f j) = t then (1 : ℝ) else 0) := by
    simp only [ite_mul, one_mul, zero_mul]
    simp [eq_comm]
  calc
    ν.prob (Finset.univ.filter (fun f => h (f i) = h (f j))) =
        ν.expect (fun f => if h (f i) = h (f j) then 1 else 0) := by
      simpa using (ν.expect_indicator (Finset.univ.filter (fun f => h (f i) = h (f j)))).symm
    _ = ν.expect (fun f => ∑ t : Λ, (if h (f i) = t then (1 : ℝ) else 0) *
        (if h (f j) = t then (1 : ℝ) else 0)) := congrArg ν.expect (funext hpoint)
    _ = ∑ t : Λ, ν.expect (fun f => (if h (f i) = t then (1 : ℝ) else 0) *
        (if h (f j) = t then (1 : ℝ) else 0)) := ν.expect_sum _ _
    _ = ∑ t, (μ.tagProb h t) ^ 2 := by
      apply Finset.sum_congr rfl
      intro t _
      rw [μ.iid_expect_mul_apply (fun ω => if h ω = t then (1 : ℝ) else 0)
        (fun ω => if h ω = t then (1 : ℝ) else 0) i j hij]
      simp only [μ.expect_tag_indicator, pow_two]

theorem iid_prob_injective_tag_ge {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (h : Ω → Λ) (c : ℝ) (hbound : ∀ t, μ.tagProb h t ≤ c) :
    1 - ((Fintype.card ι).choose 2 : ℝ) * c ≤
      (μ.iid (ι := ι)).prob
        (Finset.univ.filter (fun f => Function.Injective (fun i => h (f i)))) := by
  let ν := μ.iid (ι := ι)
  let G := Finset.univ.filter (fun f : ι → Ω => Function.Injective (fun i => h (f i)))
  let P := ((Finset.univ : Finset ι) ×ˢ Finset.univ).filter (fun p => p.1 < p.2)
  let C : (ι × ι) → Finset (ι → Ω) := fun p =>
    Finset.univ.filter (fun f => h (f p.1) = h (f p.2))
  have hbad : Gᶜ = P.biUnion C := by
    ext f
    constructor
    · intro hf
      have hnot : ¬ Function.Injective (fun i => h (f i)) := by simpa [G] using hf
      obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp hnot
      rcases lt_or_gt_of_ne hne with hij | hji
      · exact Finset.mem_biUnion.mpr ⟨(i, j), by simp [P, hij], by simp [C, heq]⟩
      · exact Finset.mem_biUnion.mpr ⟨(j, i), by simp [P, hji], by simp [C, heq]⟩
    · intro hf
      obtain ⟨⟨i, j⟩, hp, hc⟩ := Finset.mem_biUnion.mp hf
      have hij : i < j := by simpa [P] using hp
      have heq : h (f i) = h (f j) := by simpa [C] using hc
      have hnot : ¬ Function.Injective (fun i => h (f i)) :=
        fun hinj => (ne_of_lt hij) (hinj heq)
      simpa [G] using hnot
  have hcollision : ∀ p ∈ P, ν.prob (C p) ≤ c := by
    intro p hp
    have hlt : p.1 < p.2 := by simpa [P] using hp
    rw [iid_prob_tag_equal μ h p.1 p.2 (ne_of_lt hlt)]
    exact sum_squares_le_bucket_bound (μ.tagProb h) c (μ.tagProb_nonneg h)
      (μ.sum_tagProb h) hbound
  have hbadprob : ν.prob Gᶜ ≤ ((Fintype.card ι).choose 2 : ℝ) * c := by
    rw [hbad]
    have h := ν.prob_biUnion_le_card_mul P C c hcollision
    have hcard : P.card = (Fintype.card ι).choose 2 := by
      simpa [P] using Finset.card_product_filter_lt (s := (Finset.univ : Finset ι))
    rw [hcard] at h
    convert h using 1 <;> congr 1 <;> ext f <;> simp only [Finset.mem_biUnion]
  have hcompl : ν.prob Gᶜ = 1 - ν.prob G := by
    have h := ν.prob_compl G
    convert h using 1 <;> congr 1 <;> ext f <;> simp only [Finset.mem_compl]
  rw [hcompl] at hbadprob
  linarith

end FiniteLaw

/-- The concrete modulo tag with a finite codomain. -/
def modTag {N B : ℕ} [NeZero B] (y : Fin N) : Fin B :=
  ⟨y.val % B, Nat.mod_lt _ (NeZero.pos B)⟩

theorem uniform_mod_tag_good_prob {N r B : ℕ} [NeZero N] [NeZero B]
    (hr : 1 ≤ r) (hN : 64 * r ^ 2 ≤ N) (hB : 64 * r ^ 2 ≤ B) :
    (63 : ℝ) / 64 ≤
      ((FiniteLaw.uniform (Fin N)).iid (ι := Fin r)).prob
        (Finset.univ.filter (fun f => Function.Injective (fun i => modTag (B := B) (f i)))) := by
  let μ := FiniteLaw.uniform (Fin N)
  have hbound (t : Fin B) : μ.tagProb (modTag (B := B)) t ≤ 1 / (B : ℝ) + 1 / N := by
    simpa [μ, FiniteLaw.tagProb, FiniteLaw.uniform_prob, modTag, Fin.ext_iff] using
      mod_bucket_fraction_le N B t.val (NeZero.pos N) (NeZero.pos B)
  have h := μ.iid_prob_injective_tag_ge (ι := Fin r) (modTag (B := B))
    (1 / (B : ℝ) + 1 / N) hbound
  rw [Fintype.card_fin, Nat.cast_choose_two] at h
  have herr := tag_union_error_le (r : ℝ) N B (by exact_mod_cast hr)
    (by exact_mod_cast hN) (by exact_mod_cast hB)
  linarith

/-- Joint good-tag and good-count probability for actual independent uniform records. -/
theorem uniform_sample_count_joint_prob {N r B : ℕ} [NeZero N] [NeZero B]
    (hr : 1024 ≤ r) (hN : 64 * r ^ 2 ≤ N) (hB : 64 * r ^ 2 ≤ B) :
    (945 : ℝ) / 1024 ≤
      (((FiniteLaw.uniform (Fin N)).iid (ι := Fin r)).prod
        ((FiniteLaw.uniform (Fin N)).iid (ι := Fin (N - r)))).prob
          (Finset.univ.filter (fun p =>
            Function.Injective (fun i => modTag (B := B) (p.1 i)) ∧
            3 * (r : ℝ) / 4 ≤ markedCount (Finset.univ.image p.1) p.2 ∧
              markedCount (Finset.univ.image p.1) p.2 ≤ 5 * (r : ℝ) / 4)) := by
  let μ := (FiniteLaw.uniform (Fin N)).iid (ι := Fin r)
  let ν := (FiniteLaw.uniform (Fin N)).iid (ι := Fin (N - r))
  let E := Finset.univ.filter (fun a : Fin r → Fin N =>
    Function.Injective (fun i => modTag (B := B) (a i)))
  let H : (Fin r → Fin N) → (Fin (N - r) → Fin N) → Prop := fun a b =>
    3 * (r : ℝ) / 4 ≤ markedCount (Finset.univ.image a) b ∧
      markedCount (Finset.univ.image a) b ≤ 5 * (r : ℝ) / 4
  have hE : (63 : ℝ) / 64 ≤ μ.prob E :=
    uniform_mod_tag_good_prob (by omega) hN hB
  have hH : ∀ a ∈ E, (15 : ℝ) / 16 ≤ ν.prob (Finset.univ.filter (H a)) := by
    intro a ha
    have htag : Function.Injective (fun i => modTag (B := B) (a i)) :=
      (Finset.mem_filter.mp ha).2
    have hinj : Function.Injective a := fun i j hij => htag (congrArg (modTag (B := B)) hij)
    have hcard : (Finset.univ.image a).card = r := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    exact uniform_outside_count_concentration (Finset.univ.image a) hcard hr hN
  have h := μ.prob_prod_good_section_ge ν E H ((15 : ℝ) / 16) hH
  have hbound : (945 : ℝ) / 1024 ≤ (μ.prod ν).prob
      (Finset.univ.filter (fun p => p.1 ∈ E ∧ H p.1 p.2)) := by nlinarith
  simpa [E, H, and_assoc] using hbound

/-- An actual full oracle table is equivalently its fixed sample and outside records. -/
def splitOracleEquiv {N r : ℕ} (hrN : r ≤ N) :
    (Fin N → Fin N) ≃ ((Fin r → Fin N) × (Fin (N - r) → Fin N)) :=
  let e : Fin r ⊕ Fin (N - r) ≃ Fin N :=
    (finSumFinEquiv : Fin r ⊕ Fin (N - r) ≃ Fin (r + (N - r))).trans
      (finCongr (Nat.add_sub_of_le hrN))
  (Equiv.arrowCongr e.symm (Equiv.refl (Fin N))).trans
    (Equiv.sumArrowEquivProdArrow (Fin r) (Fin (N - r)) (Fin N))

theorem splitOracleEquiv_fst {N r : ℕ} (hrN : r ≤ N) (f : Fin N → Fin N) (i : Fin r) :
    (splitOracleEquiv hrN f).1 i = f (sampleAddress hrN i) := by
  change f _ = f _
  congr 1

/-- The numerical outside interval is represented without a new oracle. -/
def outsideAddress {N r : ℕ} (hrN : r ≤ N) (i : Fin (N - r)) : Fin N :=
  ⟨r + i.val, by have hi := i.isLt; omega⟩

theorem outsideAddress_ge {N r : ℕ} (hrN : r ≤ N) (i : Fin (N - r)) :
    r ≤ (outsideAddress hrN i).val := Nat.le_add_right r i.val

theorem splitOracleEquiv_snd {N r : ℕ} (hrN : r ≤ N) (f : Fin N → Fin N)
    (i : Fin (N - r)) : (splitOracleEquiv hrN f).2 i = f (outsideAddress hrN i) := by
  change f _ = f _
  congr 1

theorem split_goodTags_iff_goodTable {N r B : ℕ} [NeZero B] (hrN : r ≤ N)
    (f : Fin N → Fin N) :
    Function.Injective (fun i => modTag (B := B) ((splitOracleEquiv hrN f).1 i)) ↔
      GoodTable (tagTable hrN B f) := by
  have htags (i : Fin r) :
      (modTag (B := B) ((splitOracleEquiv hrN f).1 i)).val = tagTable hrN B f i := by
    rw [splitOracleEquiv_fst]
    rfl
  constructor
  · intro hgood i j hij
    apply hgood
    apply Fin.ext
    rw [htags, htags]
    exact hij
  · intro hgood i j hij
    apply hgood
    have h := congrArg Fin.val hij
    rwa [htags, htags] at h

noncomputable def sampleCollisionCount {N r : ℕ} (hrN : r ≤ N) (f : Fin N → Fin N) : ℝ :=
  ∑ i : Fin (N - r), if sampleCollision hrN f (outsideAddress hrN i) then 1 else 0

/-- The real count is the cardinality of the actual outside marked subset. -/
theorem sampleCollisionCount_eq_card {N r : ℕ} (hrN : r ≤ N) (f : Fin N → Fin N) :
    sampleCollisionCount hrN f =
      ((Finset.univ.filter (fun i : Fin (N - r) =>
        sampleCollision hrN f (outsideAddress hrN i))).card : ℝ) := by
  simp [sampleCollisionCount]

theorem sampleCollisionCount_eq_markedCount {N r : ℕ} (hrN : r ≤ N) (f : Fin N → Fin N) :
    sampleCollisionCount hrN f =
      markedCount (Finset.univ.image (splitOracleEquiv hrN f).1) (splitOracleEquiv hrN f).2 := by
  unfold sampleCollisionCount markedCount
  apply Finset.sum_congr rfl
  intro i _
  have hmember : (splitOracleEquiv hrN f).2 i ∈
      Finset.univ.image (splitOracleEquiv hrN f).1 ↔
        sampleCollision hrN f (outsideAddress hrN i) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, sampleCollision]
    simp_rw [splitOracleEquiv_fst, splitOracleEquiv_snd]
  simp only [hmember]

theorem uniform_oracle_split_law {N r : ℕ} [NeZero N] (hrN : r ≤ N) :
    (FiniteLaw.uniform (Fin N → Fin N)).reindex (splitOracleEquiv hrN) =
      ((FiniteLaw.uniform (Fin N)).iid (ι := Fin r)).prod
        ((FiniteLaw.uniform (Fin N)).iid (ι := Fin (N - r))) := by
  rw [FiniteLaw.uniform_reindex, FiniteLaw.iid_uniform_eq_uniform,
    FiniteLaw.iid_uniform_eq_uniform, FiniteLaw.prod_uniform_eq_uniform]

/-- Good-sample/good-count bound for one uniformly random complete fixed oracle. -/
theorem uniform_oracle_good_sample_count_prob {N r B : ℕ} [NeZero N] [NeZero B]
    (hrN : r ≤ N) (hr : 1024 ≤ r) (hN : 64 * r ^ 2 ≤ N) (hB : 64 * r ^ 2 ≤ B) :
    (945 : ℝ) / 1024 ≤
      (FiniteLaw.uniform (Fin N → Fin N)).prob
        (Finset.univ.filter (fun f =>
          Function.Injective (fun i => modTag (B := B) ((splitOracleEquiv hrN f).1 i)) ∧
          3 * (r : ℝ) / 4 ≤
              markedCount (Finset.univ.image (splitOracleEquiv hrN f).1)
                (splitOracleEquiv hrN f).2 ∧
            markedCount (Finset.univ.image (splitOracleEquiv hrN f).1)
              (splitOracleEquiv hrN f).2 ≤ 5 * (r : ℝ) / 4)) := by
  have h := uniform_sample_count_joint_prob hr hN hB
  rw [← uniform_oracle_split_law hrN, FiniteLaw.prob_reindex] at h
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h

/-- The probability bridge in the exact original oracle/sample predicates. -/
theorem uniform_function_good_count_prob {N r B : ℕ} [NeZero N] [NeZero B]
    (hrN : r ≤ N) (hr : 1024 ≤ r) (hN : 64 * r ^ 2 ≤ N) (hB : 64 * r ^ 2 ≤ B) :
    (945 : ℝ) / 1024 ≤
      (FiniteLaw.uniform (Fin N → Fin N)).prob
        (Finset.univ.filter (fun f =>
          GoodTable (tagTable hrN B f) ∧
          3 * (r : ℝ) / 4 ≤ sampleCollisionCount hrN f ∧
            sampleCollisionCount hrN f ≤ 5 * (r : ℝ) / 4)) := by
  have h := uniform_oracle_good_sample_count_prob hrN hr hN hB
  simpa only [split_goodTags_iff_goodTable, ← sampleCollisionCount_eq_markedCount] using h

/-- Integration interface for an independently derived per-oracle outcome probability.
This is a supporting inequality and does not assert that an unspecified algorithm exists. -/
theorem uniform_function_outcome_ge {N r B : ℕ} [NeZero N] [NeZero B]
    (hrN : r ≤ N) (hr : 1024 ≤ r) (hN : 64 * r ^ 2 ≤ N) (hB : 64 * r ^ 2 ≤ B)
    (s : (Fin N → Fin N) → ℝ) (hs : ∀ f, 0 ≤ s f)
    (hgood : ∀ f, GoodTable (tagTable hrN B f) →
      3 * (r : ℝ) / 4 ≤ sampleCollisionCount hrN f →
      sampleCollisionCount hrN f ≤ 5 * (r : ℝ) / 4 → (3 : ℝ) / 4 ≤ s f) :
    (2835 : ℝ) / 4096 ≤ (FiniteLaw.uniform (Fin N → Fin N)).expect s := by
  let μ := FiniteLaw.uniform (Fin N → Fin N)
  let E := Finset.univ.filter (fun f =>
    GoodTable (tagTable hrN B f) ∧
      3 * (r : ℝ) / 4 ≤ sampleCollisionCount hrN f ∧
        sampleCollisionCount hrN f ≤ 5 * (r : ℝ) / 4)
  have hp : (945 : ℝ) / 1024 ≤ μ.prob E := uniform_function_good_count_prob hrN hr hN hB
  have hsgood : ∀ f ∈ E, (3 : ℝ) / 4 ≤ s f := by
    intro f hf
    obtain ⟨hF, hlo, hhi⟩ := (Finset.mem_filter.mp hf).2
    exact hgood f hF hlo hhi
  have h := μ.expect_ge_event E s ((3 : ℝ) / 4) hs hsgood
  nlinarith

end CollisionTradeoff
