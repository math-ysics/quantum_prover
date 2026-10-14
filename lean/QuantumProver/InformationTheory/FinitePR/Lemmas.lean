import QuantumProver.InformationTheory.FinitePR.Definitions

/-!
Finite algebra for binary PR-box wirings.
-/

namespace FinitePR

open scoped BigOperators

/-- Every alphabet element is one of the two numerical bits. -/
theorem bit_cases (a : Bit) : a = 0 ∨ a = 1 := by
  have hlt := ZMod.val_lt a
  have hval : a.val = 0 ∨ a.val = 1 := by omega
  rcases hval with hval | hval
  · left
    apply ZMod.val_injective 2
    simpa only [ZMod.val_zero] using hval
  · right
    apply ZMod.val_injective 2
    simpa only [ZMod.val_one_eq_one_mod] using hval

/-- A one-hot vector contains exactly one nonzero bit. -/
theorem sum_oneHot {N : ℕ} (I : Fin N) : ∑ i, oneHot I i = 1 := by
  simp [oneHot]

/-- The one-hot PR inputs select Bob's bit at Alice's chosen finite index. -/
theorem sum_oneHot_mul {N : ℕ} (I : Fin N) (e : Fin N → Bit) :
    ∑ i, oneHot I i * e i = e I := by
  simp [oneHot, ite_mul]

/-- The deterministic support calculation uses exactly `N` PR relations. -/
theorem oneHot_parity {N : ℕ} (I : Fin N) (d : Bit)
    (e α β : Fin N → Bit)
    (h : ∀ i, prRelation (oneHot I i) (e i) (α i) (β i)) :
    aliceParity d α + bobParity β = d + e I := by
  unfold aliceParity bobParity
  calc
    d + (∑ i, α i) + ∑ i, β i = d + ∑ i, (α i + β i) := by
      rw [Finset.sum_add_distrib]
      ac_rfl
    _ = d + ∑ i, oneHot I i * e i := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact h i
    _ = d + e I := by rw [sum_oneHot_mul]

/-- Flipping the bit at one existing coordinate is a permutation of all vectors. -/
def flipEquiv {N : ℕ} (I : Fin N) : (Fin N → Bit) ≃ (Fin N → Bit) where
  toFun α i := α i + oneHot I i
  invFun α i := α i + oneHot I i
  left_inv α := by
    funext i
    simp [add_assoc, ZModModule.add_self]
  right_inv α := by
    funext i
    simp [add_assoc, ZModModule.add_self]

/-- The permutation changes the final Alice parity by one bit. -/
theorem aliceParity_flip {N : ℕ} (I : Fin N) (d : Bit) (α : Fin N → Bit) :
    aliceParity d (flipEquiv I α) = aliceParity d α + 1 := by
  simp [aliceParity, flipEquiv, Finset.sum_add_distrib, sum_oneHot, add_assoc]

/-- Probability mass in a parity fiber for an arbitrary real vector weight. -/
noncomputable def parityMass {N : ℕ} (p : (Fin N → Bit) → ℝ) (d a : Bit) : ℝ :=
  ∑ α, if aliceParity d α = a then p α else 0

/-- A flip-invariant vector law has equal mass in the two final parity fibers. -/
theorem parityMass_eq_flip {N : ℕ} (I : Fin N)
    (p : (Fin N → Bit) → ℝ) (d a : Bit)
    (hp : ∀ α, p (flipEquiv I α) = p α) :
    parityMass p d (a + 1) = parityMass p d a := by
  unfold parityMass
  calc
    (∑ α, if aliceParity d α = a + 1 then p α else 0) =
        ∑ α, if aliceParity d (flipEquiv I α) = a + 1 then
          p (flipEquiv I α) else 0 :=
      ((flipEquiv I).sum_comp
        (fun α => if aliceParity d α = a + 1 then p α else 0)).symm
    _ = ∑ α, if aliceParity d α = a then p α else 0 := by
      apply Finset.sum_congr rfl
      intro α _
      simp only [aliceParity_flip, add_right_cancel_iff, hp]

/-- Both parity fibers exhaust the vector law. -/
theorem parityMass_add {N : ℕ} (p : (Fin N → Bit) → ℝ) (d a : Bit) :
    parityMass p d a + parityMass p d (a + 1) = ∑ α, p α := by
  unfold parityMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  have hbit : aliceParity d α = a ∨ aliceParity d α = a + 1 := by
    have hcases : ∀ a b : Bit, b = a ∨ b = a + 1 := by
      intro a b
      have hone : (1 : Bit) + 1 = 0 := ZModModule.add_self 1
      rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
        simp [hone]
    exact hcases a (aliceParity d α)
  have hne : a ≠ a + 1 := by
    intro h
    have hbad : (0 : Bit) = 1 :=
      add_left_cancel (show a + 0 = a + 1 from by simpa using h)
    exact zero_ne_one hbad
  rcases hbit with hbit | hbit
  · simp [hbit, hne]
  · simp [hbit, hne.symm]

/-- Exact fairness follows from normalization and the bit-flip symmetry. -/
theorem parityMass_fair {N : ℕ} (I : Fin N)
    (p : (Fin N → Bit) → ℝ) (d a : Bit)
    (hp : ∀ α, p (flipEquiv I α) = p α) (hprob : ∑ α, p α = 1) :
    parityMass p d a = 1 / 2 := by
  have hpair := parityMass_add p d a
  have hflip := parityMass_eq_flip I p d a hp
  rw [hprob, hflip] at hpair
  linarith

/-- The conditional uniform PR vector has a fair final Alice parity. -/
theorem uniformVectorParity {N : ℕ} (I : Fin N) (d a : Bit) :
    (∑ α : Fin N → Bit, if aliceParity d α = a then
      1 / (Fintype.card (Fin N → Bit) : ℝ) else 0) = 1 / 2 := by
  apply parityMass_fair I (fun _ => 1 / (Fintype.card (Fin N → Bit) : ℝ)) d a
  · intro α
    rfl
  · simp

/-- There are exactly `2^N` binary vectors for `N` independent PR copies. -/
theorem bitVector_card (N : ℕ) : Fintype.card (Fin N → Bit) = 2 ^ N := by
  simp [Bit, Fintype.card_pi]

/-- The product-PR vector weight `(1/2)^N` has exactly fair parity. -/
theorem uniformVectorParity_binaryWeight {N : ℕ} (I : Fin N) (d a : Bit) :
    (∑ α : Fin N → Bit, if aliceParity d α = a then (1 / 2 : ℝ) ^ N else 0) =
      1 / 2 := by
  have hcard : (Fintype.card (Fin N → Bit) : ℝ) = (2 : ℝ) ^ N := by
    exact_mod_cast bitVector_card N
  simpa [hcard, div_pow] using uniformVectorParity I d a

/-- Fair Alice parity and the PR support relations determine the full pair law.

`β α` denotes Bob's output vector paired with Alice's output vector `α`.
The theorem holds for every normalized vector law invariant under `flipEquiv`.
-/
theorem oneHot_joint_mass {N : ℕ} (I : Fin N) (d : Bit) (e : Fin N → Bit)
    (β : (Fin N → Bit) → (Fin N → Bit)) (p : (Fin N → Bit) → ℝ)
    (hrel : ∀ α i, prRelation (oneHot I i) (e i) (α i) (β α i))
    (hp : ∀ α, p (flipEquiv I α) = p α) (hprob : ∑ α, p α = 1) (a b : Bit) :
    (∑ α, if aliceParity d α = a ∧ bobParity (β α) = b then p α else 0) =
      if a + b = d + e I then 1 / 2 else 0 := by
  by_cases htarget : a + b = d + e I
  · rw [ite_eq_left htarget]
    have hmass :
        (∑ α, if aliceParity d α = a ∧ bobParity (β α) = b then p α else 0) =
          parityMass p d a := by
      unfold parityMass
      apply Finset.sum_congr rfl
      intro α _
      by_cases ha : aliceParity d α = a
      · have hsupport := oneHot_parity I d e α (β α) (hrel α)
        rw [ha] at hsupport
        have hb : bobParity (β α) = b :=
          add_left_cancel (hsupport.trans htarget.symm)
        simp [ha, hb]
      · simp [ha]
    rw [hmass]
    exact parityMass_fair I p d a hp hprob
  · rw [ite_eq_right htarget]
    apply Finset.sum_eq_zero
    intro α _
    have hnot : ¬(aliceParity d α = a ∧ bobParity (β α) = b) := by
      intro hab
      have hsupport := oneHot_parity I d e α (β α) (hrel α)
      rw [hab.1, hab.2] at hsupport
      exact htarget hsupport
    simp [hnot]

/-- Bob's vector paired with a fixed Alice vector under the PR relations. -/
def pairedOutputs {N : ℕ} (u v α : Fin N → Bit) : Fin N → Bit :=
  fun i => u i * v i - α i

/-- The literal product PR table is uniform on its support graph. -/
theorem prProduct_graph {N : ℕ} (u v α β : Fin N → Bit) :
    (∏ i, prWeight (u i) (v i) (α i) (β i)) =
      if β = pairedOutputs u v α then (1 / 2 : ℝ) ^ N else 0 := by
  by_cases hβ : β = pairedOutputs u v α
  · rw [ite_eq_left hβ]
    subst β
    have hrel : ∀ i, prRelation (u i) (v i) (α i) (pairedOutputs u v α i) := by
      intro i
      unfold prRelation pairedOutputs
      ring
    simp [prWeight, hrel]
  · rw [ite_eq_right hβ]
    have hex : ∃ i, ¬prRelation (u i) (v i) (α i) (β i) := by
      by_contra hnot
      have hrel : ∀ i, prRelation (u i) (v i) (α i) (β i) := not_exists_not.mp hnot
      apply hβ
      funext i
      change β i = u i * v i - α i
      apply (eq_sub_iff_add_eq).mpr
      simpa [prRelation, add_comm] using hrel i
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [prWeight, hi]

/-- The full finite independent-PR output law produces the exact desired pair.

The sum uses all `N` literal resource tables and both output vectors. The result
includes both fair marginals and the selected parity.
-/
theorem oneHot_product_joint {N : ℕ} (I : Fin N) (d : Bit) (e : Fin N → Bit)
    (a b : Bit) :
    (∑ α : Fin N → Bit, ∑ β : Fin N → Bit,
      if aliceParity d α = a ∧ bobParity β = b then
        ∏ i, prWeight (oneHot I i) (e i) (α i) (β i) else 0) =
      if a + b = d + e I then 1 / 2 else 0 := by
  have hinner : ∀ α : Fin N → Bit,
      (∑ β : Fin N → Bit,
        if aliceParity d α = a ∧ bobParity β = b then
          ∏ i, prWeight (oneHot I i) (e i) (α i) (β i) else 0) =
        if aliceParity d α = a ∧ bobParity (pairedOutputs (oneHot I) e α) = b then
          (1 / 2 : ℝ) ^ N else 0 := by
    intro α
    simp_rw [prProduct_graph]
    have hswap : ∀ β : Fin N → Bit,
        (if aliceParity d α = a ∧ bobParity β = b then
          if β = pairedOutputs (oneHot I) e α then (1 / 2 : ℝ) ^ N else 0
        else 0) =
        if β = pairedOutputs (oneHot I) e α then
          if aliceParity d α = a ∧ bobParity β = b then (1 / 2 : ℝ) ^ N else 0
        else 0 := by
      intro β
      split_ifs <;> rfl
    simp_rw [hswap]
    simp
  simp_rw [hinner]
  apply oneHot_joint_mass I d e (pairedOutputs (oneHot I) e)
    (fun _ => (1 / 2 : ℝ) ^ N)
  · intro α i
    unfold prRelation pairedOutputs
    ring
  · intro α
    rfl
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      bitVector_card, Nat.cast_pow, Nat.cast_ofNat]
    rw [← mul_pow]
    norm_num

/-- Fair binary marginals and a correlator determine every joint probability. -/
theorem uniform_joint_from_correlator (P : Bit → Bit → ℝ)
    (hrow0 : P 0 0 + P 0 1 = 1 / 2)
    (hrow1 : P 1 0 + P 1 1 = 1 / 2)
    (hcol0 : P 0 0 + P 1 0 = 1 / 2)
    (hcol1 : P 0 1 + P 1 1 = 1 / 2)
    (a b : Bit) :
    P a b = (1 + bitSign a * bitSign b *
      (P 0 0 - P 0 1 - P 1 0 + P 1 1)) / 4 := by
  rcases bit_cases a with ha | ha <;> rcases bit_cases b with hb | hb <;>
    rw [ha, hb] <;> norm_num [bitSign] <;>
    linarith only [hrow0, hrow1, hcol0, hcol1]

end FinitePR
