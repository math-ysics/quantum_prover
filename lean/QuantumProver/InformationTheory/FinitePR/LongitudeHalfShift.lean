import Mathlib

/-! Actual Lebesgue-probability preserving half-period shift on the unit interval.
The circle quotient is an auxiliary proof of this concrete interval map. -/

namespace FinitePR.Sphere

open MeasureTheory Set
open scoped unitInterval

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def intervalToCircle (u : I) : UnitAddCircle := (u : ℝ)

lemma measurable_intervalToCircle : Measurable intervalToCircle :=
  AddCircle.measurable_mk'.comp measurable_subtype_coe

theorem measurePreserving_intervalToCircle :
    MeasurePreserving intervalToCircle (volume : Measure I) (volume : Measure UnitAddCircle) := by
  have hp := UnitAddCircle.measurePreserving_mk (0 : ℝ)
  simp only [zero_add] at hp
  rw [restrict_Ioc_eq_restrict_Icc] at hp
  exact hp.comp unitInterval.measurePreserving_coe

noncomputable def circleToInterval (c : UnitAddCircle) : I :=
  let v := AddCircle.equivIoc (1 : ℝ) 0 c
  ⟨v.1, ⟨v.2.1.le, by simpa using v.2.2⟩⟩

lemma measurable_circleToInterval : Measurable circleToInterval := by
  exact (measurable_subtype_coe.comp
    (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable).subtype_mk

lemma circleToInterval_intervalToCircle_ae :
    (circleToInterval ∘ intervalToCircle) =ᵐ[(volume : Measure I)] id := by
  filter_upwards [(volume : Measure I).ae_ne (0 : I)] with u hu
  have hune : (u : ℝ) ≠ 0 := fun h => hu (Subtype.ext h)
  have hup : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 hune.symm
  apply Subtype.ext
  change (AddCircle.equivIoc (1 : ℝ) 0 ((u : ℝ) : UnitAddCircle)).1 = (u : ℝ)
  rw [AddCircle.equivIoc_coe_eq (show (u : ℝ) ∈ Ioc 0 (0 + 1) from
    ⟨hup, by simpa using u.property.2⟩)]

theorem measurePreserving_circleToInterval :
    MeasurePreserving circleToInterval (volume : Measure UnitAddCircle) (volume : Measure I) := by
  refine ⟨measurable_circleToInterval, ?_⟩
  calc
    (volume : Measure UnitAddCircle).map circleToInterval =
        ((volume : Measure I).map intervalToCircle).map circleToInterval := by
      rw [measurePreserving_intervalToCircle.map_eq]
    _ = (volume : Measure I).map (circleToInterval ∘ intervalToCircle) :=
      Measure.map_map measurable_circleToInterval measurable_intervalToCircle
    _ = (volume : Measure I).map id :=
      Measure.map_congr circleToInterval_intervalToCircle_ae
    _ = _ := Measure.map_id

noncomputable def longitudeHalfShift (u : I) : I :=
  circleToInterval (intervalToCircle u + ((1 / 2 : ℝ) : UnitAddCircle))

theorem measurePreserving_longitudeHalfShift :
    MeasurePreserving longitudeHalfShift (volume : Measure I) (volume : Measure I) :=
  measurePreserving_circleToInterval.comp
    ((measurePreserving_add_right (volume : Measure UnitAddCircle)
      ((1 / 2 : ℝ) : UnitAddCircle)).comp measurePreserving_intervalToCircle)

/-- Exact endpoint convention: the midpoint goes to1, and all other values shift
by one half modulo one. The duplicated endpoints have proved zero mass. -/
theorem longitudeHalfShift_coe (u : I) :
    (longitudeHalfShift u : ℝ) =
      if (u : ℝ) ≤ 1 / 2 then (u : ℝ) + 1 / 2 else (u : ℝ) - 1 / 2 := by
  change (AddCircle.equivIoc (1 : ℝ) 0
    (((u : ℝ) : UnitAddCircle) + ((1 / 2 : ℝ) : UnitAddCircle))).1 = _
  rw [← AddCircle.coe_add]
  by_cases hu : (u : ℝ) ≤ 1 / 2
  · rw [if_pos hu, AddCircle.equivIoc_coe_eq (show (u : ℝ) + 1 / 2 ∈ Ioc 0 (0 + 1) from
      ⟨by linarith [u.property.1], by linarith⟩)]
  · have he : (u : ℝ) + 1 / 2 = ((u : ℝ) - 1 / 2) + 1 := by ring
    rw [if_neg hu, he, AddCircle.coe_add_period,
      AddCircle.equivIoc_coe_eq (show (u : ℝ) - 1 / 2 ∈ Ioc 0 (0 + 1) from
        ⟨by linarith, by linarith [u.property.2]⟩)]

theorem cos_longitudeHalfShift (u : I) :
    Real.cos (-Real.pi + 2 * Real.pi * (longitudeHalfShift u : ℝ)) =
      -Real.cos (-Real.pi + 2 * Real.pi * (u : ℝ)) := by
  rw [longitudeHalfShift_coe]
  split_ifs
  · rw [show -Real.pi + 2 * Real.pi * ((u : ℝ) + 1 / 2) =
      (-Real.pi + 2 * Real.pi * (u : ℝ)) + Real.pi by ring, Real.cos_add_pi]
  · rw [show -Real.pi + 2 * Real.pi * ((u : ℝ) - 1 / 2) =
      (-Real.pi + 2 * Real.pi * (u : ℝ)) - Real.pi by ring, Real.cos_sub_pi]

theorem sin_longitudeHalfShift (u : I) :
    Real.sin (-Real.pi + 2 * Real.pi * (longitudeHalfShift u : ℝ)) =
      -Real.sin (-Real.pi + 2 * Real.pi * (u : ℝ)) := by
  rw [longitudeHalfShift_coe]
  split_ifs
  · rw [show -Real.pi + 2 * Real.pi * ((u : ℝ) + 1 / 2) =
      (-Real.pi + 2 * Real.pi * (u : ℝ)) + Real.pi by ring, Real.sin_add_pi]
  · rw [show -Real.pi + 2 * Real.pi * ((u : ℝ) - 1 / 2) =
      (-Real.pi + 2 * Real.pi * (u : ℝ)) - Real.pi by ring, Real.sin_sub_pi]

end FinitePR.Sphere
