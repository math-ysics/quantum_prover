import Mathlib
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYThreeRegions

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Filter Set
open scoped Topology

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYAsymptoticGap

open BCYThreeRegions

variable {α : Type*} {f : Filter α} [NeBot f]

theorem liminf_mass_bounds (u : α → ℝ)
    (hmass : ∀ᶠ n in f, 0 ≤ u n ∧ u n ≤ 1) :
    0 ≤ liminf (fun n => (u n : EReal)) f ∧
      liminf (fun n => (u n : EReal)) f ≤ 1 := by
  constructor
  · have h : ∀ᶠ n in f, (0 : EReal) ≤ (u n : EReal) :=
      hmass.mono fun n hn => EReal.coe_nonneg.mpr hn.1
    simpa only [liminf_const] using liminf_le_liminf h
  · have h : ∀ᶠ n in f, (u n : EReal) ≤ (1 : EReal) :=
      hmass.mono fun n hn => EReal.coe_le_coe_iff.mpr hn.2
    simpa only [liminf_const] using liminf_le_liminf h

theorem liminf_affine_le_of_mass (a u b : α → ℝ) (c B L : ℝ)
    (hc : 0 ≤ c) (hmass : ∀ᶠ n in f, 0 ≤ u n ∧ u n ≤ 1)
    (hu : liminf (fun n => (u n : EReal)) f ≤ (L : EReal))
    (hb : Tendsto b f (𝓝 B))
    (hpoint : ∀ᶠ n in f, a n ≤ b n + c * u n) :
    liminf (fun n => (a n : EReal)) f ≤ ((B + c * L : ℝ) : EReal) := by
  have hcE : (0 : EReal) ≤ (c : EReal) := EReal.coe_nonneg.mpr hc
  have hm := liminf_mass_bounds u hmass
  have hmul := EReal.liminf_const_mul_of_nonneg_of_ne_top
    (f := f) (u := fun n => (u n : EReal)) hcE (EReal.coe_ne_top c)
  have hm0 : (0 : EReal) ≤ liminf (fun n => (c : EReal) * (u n : EReal)) f := by
    rw [hmul]
    exact mul_nonneg hcE hm.1
  have hm1 : liminf (fun n => (c : EReal) * (u n : EReal)) f ≤ (c : EReal) := by
    rw [hmul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hm.2 hcE
  have hbot : liminf (fun n => (c : EReal) * (u n : EReal)) f ≠ ⊥ :=
    ne_of_gt ((EReal.bot_lt_coe 0).trans_le hm0)
  have htop : liminf (fun n => (c : EReal) * (u n : EReal)) f ≠ ⊤ :=
    ne_of_lt (hm1.trans_lt (EReal.coe_lt_top c))
  have hbE : limsup (fun n => (b n : EReal)) f = (B : EReal) :=
    (EReal.tendsto_coe.mpr hb).limsup_eq
  calc
    _ ≤ liminf (fun n => (b n : EReal) + (c : EReal) * (u n : EReal)) f := by
      have hcomp : ∀ᶠ n in f,
          (a n : EReal) ≤ (b n : EReal) + (c : EReal) * (u n : EReal) := by
        filter_upwards [hpoint] with n hn
        simpa only [← EReal.coe_mul, ← EReal.coe_add] using EReal.coe_le_coe_iff.mpr hn
      exact liminf_le_liminf hcomp
    _ ≤ limsup (fun n => (b n : EReal)) f +
        liminf (fun n => (c : EReal) * (u n : EReal)) f :=
      EReal.liminf_add_le (.inr htop) (.inr hbot)
    _ = (B : EReal) + (c : EReal) * liminf (fun n => (u n : EReal)) f := by
      rw [hbE, hmul]
    _ ≤ (B : EReal) + (c : EReal) * (L : EReal) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hu hcE)
    _ = _ := by rw [← EReal.coe_mul, ← EReal.coe_add]

theorem liminf_le_fixed_three_region_bound
    (a u v err : ℕ → ℝ) (Re slack c d epsilon : ℝ)
    (hc : 0 ≤ c) (hmass : ∀ᶠ n in atTop, 0 ≤ u n ∧ u n ≤ 1)
    (hu : liminf (fun n => (u n : EReal)) atTop ≤ ((1 - epsilon : ℝ) : EReal))
    (hv : Tendsto v atTop (𝓝 0)) (herr : Tendsto err atTop (𝓝 0))
    (hpoint : ∀ᶠ n in atTop,
      a n ≤ Re + slack + c * u n + d * v n + err n) :
    liminf (fun n => (a n : EReal)) atTop ≤
      ((Re + slack + c * (1 - epsilon) : ℝ) : EReal) := by
  have hb : Tendsto (fun n => Re + slack + d * v n + err n)
      atTop (𝓝 (Re + slack)) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_const_nhds.add (hv.const_mul d)).add herr)
  apply liminf_affine_le_of_mass a u (fun n => Re + slack + d * v n + err n)
    c (Re + slack) (1 - epsilon) hc hmass hu hb
  filter_upwards [hpoint] with n hn
  calc
    a n ≤ Re + slack + c * u n + d * v n + err n := hn
    _ = _ := by ring

theorem ereal_le_of_forall_pos_add {z : EReal} {C : ℝ}
    (h : ∀ slack : ℝ, 0 < slack → z ≤ ((C + slack : ℝ) : EReal)) :
    z ≤ (C : EReal) := by
  have hc : Continuous (fun slack : ℝ => C + slack) := by fun_prop
  have ht : Tendsto (fun slack : ℝ => C + slack)
      (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    simpa only [add_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto (EReal.tendsto_coe.mpr ht)
  filter_upwards [self_mem_nhdsWithin] with slack hs
  exact h slack hs

theorem liminf_le_three_region_contraction
    (a : ℕ → ℝ) (u v err : ℝ → ℕ → ℝ) (Re Rprime kappa epsilon eta : ℝ)
    (he : epsilon < 1) (heta : eta ≤ epsilon) (hR : Re ≤ Rprime)
    (hmass : ∀ slack : ℝ, 0 < slack →
      ∀ᶠ n in atTop, 0 ≤ u slack n ∧ u slack n ≤ 1)
    (hu : ∀ slack : ℝ, 0 < slack →
      liminf (fun n => (u slack n : EReal)) atTop ≤ ((1 - epsilon : ℝ) : EReal))
    (hv : ∀ slack : ℝ, 0 < slack → Tendsto (v slack) atTop (𝓝 0))
    (herr : ∀ slack : ℝ, 0 < slack → Tendsto (err slack) atTop (𝓝 0))
    (hpoint : ∀ slack : ℝ, 0 < slack → ∀ᶠ n in atTop,
      a n ≤ Re + slack + (Rprime + epsilon0 epsilon eta Rprime Re - Re) * u slack n +
        (2 * kappa - Rprime - epsilon0 epsilon eta Rprime Re - slack) * v slack n +
        err slack n) :
    liminf (fun n => (a n : EReal)) atTop ≤
      ((Re + (1 - eta) * (Rprime - Re) : ℝ) : EReal) := by
  have hc : 0 ≤ Rprime + epsilon0 epsilon eta Rprime Re - Re := by
    linarith [epsilon0_nonneg he heta hR]
  have hslack : liminf (fun n => (a n : EReal)) atTop ≤
      ((Re + (Rprime + epsilon0 epsilon eta Rprime Re - Re) * (1 - epsilon) : ℝ) : EReal) := by
    apply ereal_le_of_forall_pos_add
    intro slack hs
    have h := liminf_le_fixed_three_region_bound a (u slack) (v slack) (err slack)
      Re slack (Rprime + epsilon0 epsilon eta Rprime Re - Re)
      (2 * kappa - Rprime - epsilon0 epsilon eta Rprime Re - slack) epsilon
      hc (hmass slack hs) (hu slack hs) (hv slack hs) (herr slack hs) (hpoint slack hs)
    convert h using 1
    congr 1
    ring
  have hid : Re + (Rprime + epsilon0 epsilon eta Rprime Re - Re) * (1 - epsilon) =
      Re + (1 - eta) * (Rprime - Re) := by
    simpa only [mul_comm] using epsilon0_rate_identity (ne_of_lt he)
  simpa only [hid] using hslack

theorem liminf_sub_const_le (a : α → ℝ) (C R : ℝ)
    (h : liminf (fun n => (a n : EReal)) f ≤ (C : EReal)) :
    liminf (fun n => ((a n - R : ℝ) : EReal)) f ≤ ((C - R : ℝ) : EReal) := by
  have hfun : (fun n => ((a n - R : ℝ) : EReal)) =
      (fun _ : α => ((-R : ℝ) : EReal)) + (fun n => (a n : EReal)) := by
    funext n
    simp only [Pi.add_apply, ← EReal.coe_add]
    congr 1
    ring
  rw [hfun]
  calc
    _ ≤ limsup (fun _ : α => ((-R : ℝ) : EReal)) f +
        liminf (fun n => (a n : EReal)) f :=
      EReal.liminf_add_le (.inl (by simpa only [limsup_const] using EReal.coe_ne_bot (-R)))
        (.inl (by simpa only [limsup_const] using EReal.coe_ne_top (-R)))
    _ ≤ ((-R : ℝ) : EReal) + (C : EReal) := by
      rw [limsup_const]
      exact add_le_add le_rfl h
    _ = _ := by rw [← EReal.coe_add]; congr 1; ring

theorem liminf_gap_le_three_region_contraction
    (a : ℕ → ℝ) (u v err : ℝ → ℕ → ℝ) (Re Rprime kappa epsilon eta : ℝ)
    (he : epsilon < 1) (heta : eta ≤ epsilon) (hR : Re ≤ Rprime)
    (hmass : ∀ slack : ℝ, 0 < slack →
      ∀ᶠ n in atTop, 0 ≤ u slack n ∧ u slack n ≤ 1)
    (hu : ∀ slack : ℝ, 0 < slack →
      liminf (fun n => (u slack n : EReal)) atTop ≤ ((1 - epsilon : ℝ) : EReal))
    (hv : ∀ slack : ℝ, 0 < slack → Tendsto (v slack) atTop (𝓝 0))
    (herr : ∀ slack : ℝ, 0 < slack → Tendsto (err slack) atTop (𝓝 0))
    (hpoint : ∀ slack : ℝ, 0 < slack → ∀ᶠ n in atTop,
      a n ≤ Re + slack + (Rprime + epsilon0 epsilon eta Rprime Re - Re) * u slack n +
        (2 * kappa - Rprime - epsilon0 epsilon eta Rprime Re - slack) * v slack n +
        err slack n) :
    liminf (fun n => ((a n - Re : ℝ) : EReal)) atTop ≤
      (((1 - eta) * (Rprime - Re) : ℝ) : EReal) := by
  have h := liminf_sub_const_le a (Re + (1 - eta) * (Rprime - Re)) Re
    (liminf_le_three_region_contraction a u v err Re Rprime kappa epsilon eta
      he heta hR hmass hu hv herr hpoint)
  simpa only [add_sub_cancel_left] using h

end QuantumProver.DepolarizingSquashedEntanglement.BCYAsymptoticGap
