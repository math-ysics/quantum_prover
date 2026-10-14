import QuantumProver.InformationTheory.FinitePR.Definitions
import Mathlib

/-!
Actual height--longitude unit-sphere geometry for the finite-list source.
No surface-measure, capacity, density normalization or simulation is assumed.
-/

namespace FinitePR.Sphere

open scoped BigOperators

abbrev Height := Set.Icc (-1 : ℝ) 1

noncomputable def radius (h : Height) : ℝ := Real.sqrt (1 - (h : ℝ) ^ 2)

lemma height_sq_le_one (h : Height) : (h : ℝ) ^ 2 ≤ 1 := by
  nlinarith [h.property.1, h.property.2]

lemma radius_nonneg (h : Height) : 0 ≤ radius h := Real.sqrt_nonneg _

lemma radius_sq (h : Height) : radius h ^ 2 = 1 - (h : ℝ) ^ 2 :=
  Real.sq_sqrt (sub_nonneg.mpr (height_sq_le_one h))

lemma radius_le_one (h : Height) : radius h ≤ 1 := by
  nlinarith [radius_sq h, radius_nonneg h, sq_nonneg (h : ℝ)]

noncomputable def parameterCoordinates (p : Height × ℝ) : Fin 3 → ℝ :=
  ![radius p.1 * Real.cos p.2, radius p.1 * Real.sin p.2, (p.1 : ℝ)]

lemma parameterCoordinates_unit (p : Height × ℝ) :
    ∑ i, (parameterCoordinates p i) ^ 2 = 1 := by
  simp only [parameterCoordinates, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  have ht := Real.sin_sq_add_cos_sq p.2
  have hr := radius_sq p.1
  calc
    (radius p.1 * Real.cos p.2) ^ 2 + (radius p.1 * Real.sin p.2) ^ 2 +
        (p.1 : ℝ) ^ 2 =
      radius p.1 ^ 2 * (Real.sin p.2 ^ 2 + Real.cos p.2 ^ 2) + (p.1 : ℝ) ^ 2 := by ring
    _ = 1 := by rw [ht, mul_one, hr]; ring

noncomputable def parameterDirection (p : Height × ℝ) : Direction :=
  ⟨parameterCoordinates p, parameterCoordinates_unit p⟩

lemma continuous_parameterCoordinates : Continuous parameterCoordinates := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [parameterCoordinates, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, radius] <;> fun_prop

theorem continuous_parameterDirection : Continuous parameterDirection :=
  continuous_parameterCoordinates.subtype_mk _

theorem measurable_parameterDirection : Measurable parameterDirection :=
  continuous_parameterDirection.measurable

noncomputable def parameterVector (p : Height × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (parameterCoordinates p)

noncomputable def coordinateDistance (x y : Direction) : ℝ :=
  Real.sqrt (∑ i, (x.1 i - y.1 i) ^ 2)

lemma coordinateDistance_parameter_eq_norm (p q : Height × ℝ) :
    coordinateDistance (parameterDirection p) (parameterDirection q) =
      ‖parameterVector p - parameterVector q‖ := by
  simp [coordinateDistance, parameterDirection, parameterVector,
    EuclideanSpace.norm_eq, PiLp.sub_apply, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]

lemma square_difference_le_abs_square_difference {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : (a - b) ^ 2 ≤ |a ^ 2 - b ^ 2| := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (by nlinarith)]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hab)]
  · rw [abs_of_nonneg (by nlinarith)]
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hba)]

lemma radius_difference_sq_le (h h' : Height) :
    (radius h - radius h') ^ 2 ≤ 2 * |(h : ℝ) - (h' : ℝ)| := by
  calc
    (radius h - radius h') ^ 2 ≤ |radius h ^ 2 - radius h' ^ 2| :=
      square_difference_le_abs_square_difference (radius_nonneg h) (radius_nonneg h')
    _ = |(h : ℝ) - (h' : ℝ)| * |(h : ℝ) + (h' : ℝ)| := by
      rw [radius_sq, radius_sq]
      have he : (1 - (h : ℝ) ^ 2) - (1 - (h' : ℝ) ^ 2) =
          -(((h : ℝ) - (h' : ℝ)) * ((h : ℝ) + (h' : ℝ))) := by ring
      rw [he, abs_neg, abs_mul]
    _ ≤ |(h : ℝ) - (h' : ℝ)| * 2 :=
      mul_le_mul_of_nonneg_left
        (abs_le.mpr ⟨by linarith [h.property.1, h'.property.1],
          by linarith [h.property.2, h'.property.2]⟩) (abs_nonneg _)
    _ = _ := by ring

lemma height_difference_sq_le (h h' : Height) :
    ((h : ℝ) - (h' : ℝ)) ^ 2 ≤ 2 * |(h : ℝ) - (h' : ℝ)| := by
  have hd : |(h : ℝ) - (h' : ℝ)| ≤ 2 :=
    abs_le.mpr ⟨by linarith [h.property.1, h'.property.2],
      by linarith [h.property.2, h'.property.1]⟩
  nlinarith [sq_abs ((h : ℝ) - (h' : ℝ)), abs_nonneg ((h : ℝ) - (h' : ℝ))]

lemma same_longitude_distance_le (h h' : Height) (φ : ℝ) :
    ‖parameterVector (h, φ) - parameterVector (h', φ)‖ ≤
      2 * Real.sqrt |(h : ℝ) - (h' : ℝ)| := by
  have he : ‖parameterVector (h, φ) - parameterVector (h', φ)‖ ^ 2 =
      (radius h - radius h') ^ 2 + ((h : ℝ) - (h' : ℝ)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    change (radius h * Real.cos φ - radius h' * Real.cos φ) ^ 2 +
      (radius h * Real.sin φ - radius h' * Real.sin φ) ^ 2 +
      ((h : ℝ) - (h' : ℝ)) ^ 2 = _
    calc
      _ = (radius h - radius h') ^ 2 * (Real.sin φ ^ 2 + Real.cos φ ^ 2) +
          ((h : ℝ) - (h' : ℝ)) ^ 2 := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]
  have hb := radius_difference_sq_le h h'
  have hc := height_difference_sq_le h h'
  have hs := Real.sq_sqrt (abs_nonneg ((h : ℝ) - (h' : ℝ)))
  nlinarith [norm_nonneg (parameterVector (h, φ) - parameterVector (h', φ)),
    Real.sqrt_nonneg |(h : ℝ) - (h' : ℝ)|]

lemma circle_difference_sq_le (φ ψ : ℝ) :
    (Real.cos φ - Real.cos ψ) ^ 2 + (Real.sin φ - Real.sin ψ) ^ 2 ≤
      (φ - ψ) ^ 2 := by
  have hφ := Real.sin_sq_add_cos_sq φ
  have hψ := Real.sin_sq_add_cos_sq ψ
  have hc := Real.cos_sub φ ψ
  have hb := Real.one_sub_sq_div_two_le_cos (x := φ - ψ)
  nlinarith

lemma same_height_distance_le (h : Height) (φ ψ : ℝ) :
    ‖parameterVector (h, φ) - parameterVector (h, ψ)‖ ≤ |φ - ψ| := by
  have he : ‖parameterVector (h, φ) - parameterVector (h, ψ)‖ ^ 2 =
      radius h ^ 2 * ((Real.cos φ - Real.cos ψ) ^ 2 +
        (Real.sin φ - Real.sin ψ) ^ 2) := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    change (radius h * Real.cos φ - radius h * Real.cos ψ) ^ 2 +
      (radius h * Real.sin φ - radius h * Real.sin ψ) ^ 2 +
      ((h : ℝ) - (h : ℝ)) ^ 2 = _
    ring
  have hb : radius h ^ 2 ≤ 1 := by nlinarith [radius_sq h, sq_nonneg (h : ℝ)]
  have hc := circle_difference_sq_le φ ψ
  have hm := mul_le_mul_of_nonneg_right hb
    (add_nonneg (sq_nonneg (Real.cos φ - Real.cos ψ))
      (sq_nonneg (Real.sin φ - Real.sin ψ)))
  nlinarith [sq_abs (φ - ψ), abs_nonneg (φ - ψ),
    norm_nonneg (parameterVector (h, φ) - parameterVector (h, ψ))]

/-- The actual Euclidean bound remains valid at both poles. -/
theorem parameterDirection_distance_le (p q : Height × ℝ) :
    coordinateDistance (parameterDirection p) (parameterDirection q) ≤
      2 * Real.sqrt |(p.1 : ℝ) - (q.1 : ℝ)| + |p.2 - q.2| := by
  rw [coordinateDistance_parameter_eq_norm]
  calc
    ‖parameterVector p - parameterVector q‖ ≤
        ‖parameterVector p - parameterVector (q.1, p.2)‖ +
          ‖parameterVector (q.1, p.2) - parameterVector q‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (same_longitude_distance_le p.1 q.1 p.2)
      (same_height_distance_le q.1 p.2 q.2)

/-- Rectangular parameter cells give a completely explicit shrinking mesh. -/
theorem rectangular_mesh_bound (k : ℕ) (p q : Height × ℝ)
    (hh : |(p.1 : ℝ) - (q.1 : ℝ)| ≤ 2 / (k : ℝ))
    (hφ : |p.2 - q.2| ≤ 2 * Real.pi / (k : ℝ)) :
    coordinateDistance (parameterDirection p) (parameterDirection q) ≤
      2 * Real.sqrt (2 / (k : ℝ)) + 2 * Real.pi / (k : ℝ) := by
  exact (parameterDirection_distance_le p q).trans
    (add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hh) (by norm_num)) hφ)

/-- The manuscript mesh constant follows from the coordinate estimate. -/
theorem rectangular_mesh_bound_pi (k : ℕ) (hk : 1 ≤ k) (p q : Height × ℝ)
    (hh : |(p.1 : ℝ) - (q.1 : ℝ)| ≤ 2 / (k : ℝ))
    (hφ : |p.2 - q.2| ≤ 2 * Real.pi / (k : ℝ)) :
    coordinateDistance (parameterDirection p) (parameterDirection q) ≤
      3 * Real.pi / Real.sqrt (k : ℝ) := by
  have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hks : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hs₁ : 1 ≤ Real.sqrt (k : ℝ) := by
    simpa using Real.sqrt_le_sqrt hk₁
  have hsq := Real.sq_sqrt (show 0 ≤ (k : ℝ) by linarith)
  have hsk : Real.sqrt (k : ℝ) ≤ k := by nlinarith
  have hπ : 2 * Real.sqrt 2 ≤ Real.pi := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2, Real.pi_gt_three]
  calc
    coordinateDistance (parameterDirection p) (parameterDirection q) ≤
        2 * Real.sqrt (2 / (k : ℝ)) + 2 * Real.pi / (k : ℝ) :=
      rectangular_mesh_bound k p q hh hφ
    _ ≤ 2 * (Real.sqrt 2 / Real.sqrt (k : ℝ)) +
        2 * Real.pi / Real.sqrt (k : ℝ) := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
      exact add_le_add le_rfl
        (div_le_div_of_nonneg_left
          (show (0 : ℝ) ≤ 2 * Real.pi by positivity) hks hsk)
    _ = (2 * Real.sqrt 2 + 2 * Real.pi) / Real.sqrt (k : ℝ) := by ring
    _ ≤ 3 * Real.pi / Real.sqrt (k : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hks.le

theorem tendsto_mesh_bound_zero :
    Filter.Tendsto (fun k : ℕ => 3 * Real.pi / Real.sqrt (k : ℝ))
      Filter.atTop (nhds 0) :=
  (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop _

theorem exists_mesh_size (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ p q : Height × ℝ,
      |(p.1 : ℝ) - (q.1 : ℝ)| ≤ 2 / (k : ℝ) →
      |p.2 - q.2| ≤ 2 * Real.pi / (k : ℝ) →
      coordinateDistance (parameterDirection p) (parameterDirection q) < ε := by
  have he : ∀ᶠ k : ℕ in Filter.atTop,
      3 * Real.pi / Real.sqrt (k : ℝ) < ε :=
    tendsto_mesh_bound_zero.eventually (gt_mem_nhds hε)
  rcases Filter.eventually_atTop.1 he with ⟨K, hK⟩
  refine ⟨max K 1, le_max_right _ _, ?_⟩
  intro p q hh hφ
  exact (rectangular_mesh_bound_pi (max K 1) (le_max_right _ _) p q hh hφ).trans_lt
    (hK _ (le_max_left _ _))

/-- A compact longitude band already covers every unit direction. -/
theorem exists_bounded_parameters (x : Direction) :
    ∃ p : Height × ℝ, p.2 ∈ Set.Icc (-Real.pi) Real.pi ∧ parameterDirection p = x := by
  have hx : (x.1 0) ^ 2 + (x.1 1) ^ 2 + (x.1 2) ^ 2 = 1 := by
    simpa [Fin.sum_univ_three] using x.property
  have hh : x.1 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.1 1)]
  let h : Height := ⟨x.1 2, hh⟩
  let z : ℂ := ⟨x.1 0, x.1 1⟩
  have hr : radius h = ‖z‖ := by
    rw [radius, Complex.norm_def, Complex.normSq_apply]
    congr 1
    change 1 - (x.1 2) ^ 2 = x.1 0 * x.1 0 + x.1 1 * x.1 1
    nlinarith
  refine ⟨(h, z.arg), ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩, ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i
  · change radius h * Real.cos z.arg = x.1 0
    simpa [hr, z] using Complex.norm_mul_cos_arg z
  · change radius h * Real.sin z.arg = x.1 1
    simpa [hr, z] using Complex.norm_mul_sin_arg z
  · rfl

/-- All unit directions occur in the chart, including the two poles. -/
theorem surjective_parameterDirection : Function.Surjective parameterDirection := by
  intro x
  rcases exists_bounded_parameters x with ⟨p, _, hp⟩
  exact ⟨p, hp⟩

noncomputable def directionVector (x : Direction) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 x.1

lemma norm_directionVector (x : Direction) : ‖directionVector x‖ = 1 := by
  have hs : ‖directionVector x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact x.property
  nlinarith [norm_nonneg (directionVector x)]

lemma coordinateDistance_eq_norm (x y : Direction) :
    coordinateDistance x y = ‖directionVector x - directionVector y‖ := by
  simp [coordinateDistance, directionVector, EuclideanSpace.norm_eq,
    PiLp.sub_apply, Real.norm_eq_abs, sq_abs]

noncomputable def blochDot (x y : Direction) : ℝ := ∑ i, x.1 i * y.1 i

/-- The Euclidean mesh controls every unit-direction test uniformly. -/
theorem blochDot_difference_le (x u v : Direction) :
    |blochDot x u - blochDot x v| ≤ coordinateDistance u v := by
  have he : blochDot x u - blochDot x v =
      inner ℝ (directionVector x) (directionVector u - directionVector v) := by
    simp [blochDot, PiLp.inner_apply, Real.inner_apply, directionVector,
      PiLp.sub_apply, Fin.sum_univ_three] <;> ring
  rw [he, coordinateDistance_eq_norm]
  simpa [norm_directionVector] using
    abs_real_inner_le_norm (directionVector x) (directionVector u - directionVector v)

end FinitePR.Sphere
