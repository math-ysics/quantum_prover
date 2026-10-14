import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Filter Set
open scoped Topology

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYScalarThresholdMass

variable {α : Type*} {f : Filter α}

theorem frequently_mass_lt_of_rate_implication
    (a h c : α → ℝ) (R slack L : ℝ) (hslack : 0 < slack)
    (hc : Tendsto c f (𝓝 0))
    (hR : liminf (fun n => (h n : EReal)) f = (R : EReal))
    (hpoint : ∀ᶠ n in f, L ≤ a n → R + slack - c n ≤ h n) :
    ∃ᶠ n in f, a n < L := by
  have hsep : (0 : ℝ) < slack / 2 := by linarith
  have hlow : ∃ᶠ n in f, (h n : EReal) < ((R + slack / 2 : ℝ) : EReal) := by
    apply frequently_lt_of_liminf_lt (by isBoundedDefault)
    rw [hR]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have herror : ∀ᶠ n in f, c n < slack / 2 := hc.eventually (gt_mem_nhds hsep)
  exact ((hlow.and_eventually herror).and_eventually hpoint).mono fun n hn => by
    have hrate : h n < R + slack / 2 := EReal.coe_lt_coe_iff.mp hn.1.1
    by_contra ha
    have htest := hn.2 (le_of_not_gt ha)
    linarith [hn.1.2]

theorem liminf_mass_le_of_rate_implication
    (a h c : α → ℝ) (R slack L : ℝ) (hslack : 0 < slack)
    (hc : Tendsto c f (𝓝 0))
    (hR : liminf (fun n => (h n : EReal)) f = (R : EReal))
    (hpoint : ∀ᶠ n in f, L ≤ a n → R + slack - c n ≤ h n) :
    liminf (fun n => (a n : EReal)) f ≤ (L : EReal) := by
  exact liminf_le_of_frequently_le'
    ((frequently_mass_lt_of_rate_implication a h c R slack L hslack hc hR hpoint).mono
      fun n hn => EReal.coe_le_coe_iff.mpr hn.le)

theorem scalar_threshold_mass_liminf_le
    (a h c : ℕ → ℝ) (R slack epsilon : ℝ) (hslack : 0 < slack)
    (hc : Tendsto c atTop (𝓝 0))
    (hR : liminf (fun n => (h n : EReal)) atTop = (R : EReal))
    (hpoint : ∀ᶠ n in atTop, 1 - epsilon ≤ a n → R + slack - c n ≤ h n) :
    liminf (fun n => (a n : EReal)) atTop ≤ ((1 - epsilon : ℝ) : EReal) :=
  liminf_mass_le_of_rate_implication a h c R slack (1 - epsilon) hslack hc hR hpoint

theorem threshold_mass_low_indices_infinite
    (a h c : ℕ → ℝ) (R slack epsilon : ℝ) (hslack : 0 < slack)
    (hc : Tendsto c atTop (𝓝 0))
    (hR : liminf (fun n => (h n : EReal)) atTop = (R : EReal))
    (hpoint : ∀ᶠ n in atTop, 1 - epsilon ≤ a n → R + slack - c n ≤ h n) :
    Set.Infinite {n : ℕ | a n < 1 - epsilon} :=
  Nat.frequently_atTop_iff_infinite.mp
    (frequently_mass_lt_of_rate_implication a h c R slack (1 - epsilon) hslack hc hR hpoint)

theorem exists_strictMono_threshold_subsequence
    (a h c : ℕ → ℝ) (R slack epsilon : ℝ) (hslack : 0 < slack)
    (hc : Tendsto c atTop (𝓝 0))
    (hR : liminf (fun n => (h n : EReal)) atTop = (R : EReal))
    (hpoint : ∀ᶠ n in atTop, 1 - epsilon ≤ a n → R + slack - c n ≤ h n) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Tendsto subseq atTop atTop ∧
      ∀ j, a (subseq j) < 1 - epsilon := by
  obtain ⟨subseq, hmono, hlow⟩ := extraction_of_frequently_atTop
    (frequently_mass_lt_of_rate_implication a h c R slack (1 - epsilon) hslack hc hR hpoint)
  exact ⟨subseq, hmono, hmono.tendsto_atTop, hlow⟩

end QuantumProver.DepolarizingSquashedEntanglement.BCYScalarThresholdMass
