import Mathlib

open scoped BigOperators Topology
open MeasureTheory Set

namespace QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature

noncomputable section

set_option maxHeartbeats 600000

variable {Ω V : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [MeasurableSpace Ω] [CompleteSpace V] in

private theorem actual_finite_convex_representation (f : Ω → V) (s : Set Ω) {x : V}
    (hx : x ∈ convexHull ℝ (f '' s)) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (point : Fin n → Ω),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      (∀ i, point i ∈ s) ∧ (∑ i, w i • f (point i)) = x := by
  classical
  obtain ⟨ι, hι, w, z, hw, hsum, hz, heq⟩ := mem_convexHull_iff_exists_fintype.mp hx
  let : Fintype ι := hι
  have hpoints : ∀ i, ∃ a, a ∈ s ∧ f a = z i := hz
  choose point hpoint hvalue using hpoints
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => w (e.symm i), fun i => point (e.symm i),
    fun i => hw (e.symm i), ?_, fun i => hpoint (e.symm i), ?_⟩
  · exact (e.symm.sum_comp w).trans hsum
  · simp only [hvalue]
    exact (e.symm.sum_comp (fun i => w i • z i)).trans heq

theorem exists_integral_actual_point_quadrature_on
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → V) (hf : Integrable f μ)
    (s : Set Ω) (hs : ∀ᵐ a ∂μ, a ∈ s) :
    ∃ (n : ℕ → ℕ) (w : (a : ℕ) → Fin (n a) → ℝ)
      (point : (a : ℕ) → Fin (n a) → Ω),
      (∀ a i, 0 ≤ w a i) ∧
      (∀ a, (∑ i, w a i) = μ.real univ) ∧
      (∀ a i, point a i ∈ s) ∧
      Filter.Tendsto (fun a => ∑ i, w a i • f (point a i))
        Filter.atTop (nhds (∫ a, f a ∂μ)) := by
  classical
  by_cases hμ : μ = 0
  · subst μ
    refine ⟨fun _ => 0, fun _ _ => 0, fun _ i => Fin.elim0 i, ?_, ?_, ?_, ?_⟩
    · intro a i
      exact le_refl _
    · intro a
      simp
    · intro a i
      exact Fin.elim0 i
    · simp
  · have : NeZero μ := ⟨hμ⟩
    have hmean : (⨍ a, f a ∂μ) ∈ closure (convexHull ℝ (f '' s)) :=
      (convex_convexHull ℝ (f '' s)).closure.average_mem isClosed_closure
        (hs.mono fun a ha => subset_closure (subset_convexHull ℝ (f '' s) ⟨a, ha, rfl⟩)) hf
    obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.mp hmean
    choose n w point hw hsum hpoint heq using
      fun a => actual_finite_convex_representation f s (hq a)
    refine ⟨n, fun a i => μ.real univ * w a i, point, ?_, ?_, hpoint, ?_⟩
    · intro a i
      exact mul_nonneg ENNReal.toReal_nonneg (hw a i)
    · intro a
      rw [← Finset.mul_sum, hsum a, mul_one]
    · have hconst : Filter.Tendsto (fun _ : ℕ => μ.real univ)
          Filter.atTop (nhds (μ.real univ)) := tendsto_const_nhds
      have h := hconst.smul hlim
      have hvalues (a : ℕ) :
          (∑ i, (μ.real univ * w a i) • f (point a i)) = μ.real univ • q a := by
        rw [← heq a, Finset.smul_sum]
        simp only [mul_smul]
      simpa only [hvalues, measure_smul_average] using h

theorem exists_integral_actual_point_quadrature
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → V) (hf : Integrable f μ) :
    ∃ (n : ℕ → ℕ) (w : (a : ℕ) → Fin (n a) → ℝ)
      (point : (a : ℕ) → Fin (n a) → Ω),
      (∀ a i, 0 ≤ w a i) ∧ (∀ a, (∑ i, w a i) = μ.real univ) ∧
      Filter.Tendsto (fun a => ∑ i, w a i • f (point a i))
        Filter.atTop (nhds (∫ a, f a ∂μ)) := by
  obtain ⟨n, w, point, hw, hmass, hpoint, hlim⟩ :=
    exists_integral_actual_point_quadrature_on μ f hf univ (Filter.Eventually.of_forall fun _ => mem_univ _)
  exact ⟨n, w, point, hw, hmass, hlim⟩

omit [MeasurableSpace Ω] [CompleteSpace V] in

def actualPositiveQuadratureValues (mass : ℝ) (f : Ω → V) (s : Set Ω) : Set V :=
  {x | ∃ (n : ℕ) (w : Fin n → ℝ) (point : Fin n → Ω),
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = mass ∧
    (∀ i, point i ∈ s) ∧ (∑ i, w i • f (point i)) = x}

theorem integral_mem_closure_actual_positive_quadratures_on
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → V) (hf : Integrable f μ)
    (s : Set Ω) (hs : ∀ᵐ a ∂μ, a ∈ s) :
    (∫ a, f a ∂μ) ∈ closure (actualPositiveQuadratureValues (μ.real univ) f s) := by
  obtain ⟨n, w, point, hw, hmass, hpoint, hlim⟩ :=
    exists_integral_actual_point_quadrature_on μ f hf s hs
  exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun a =>
    ⟨n a, w a, point a, hw a, hmass a, hpoint a, rfl⟩)

end

section Kraus

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

variable {Ω κ η J V : Type*} [MeasurableSpace Ω]
variable [Fintype κ] [Fintype η] [DecidableEq κ]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

noncomputable def weightedKraus (w : ℝ) (A : Matrix η κ ℂ) : Matrix η κ ℂ :=
  (Real.sqrt w : ℝ) • A

omit [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] in

theorem weightedKraus_gram (w : ℝ) (A : Matrix η κ ℂ) (hw : 0 ≤ w) :
    (weightedKraus w A)ᴴ * weightedKraus w A = w • (Aᴴ * A) := by
  simp only [weightedKraus, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt hw]

theorem exists_joint_sampled_kraus_quadrature_on
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → Matrix η κ ℂ) (f : Ω → V)
    (hf : Integrable (fun a => ((K a)ᴴ * K a, f a)) μ)
    (s : Set Ω) (hs : ∀ᵐ a ∂μ, a ∈ s) :
    ∃ (n : ℕ → ℕ) (w : (a : ℕ) → Fin (n a) → ℝ)
      (point : (a : ℕ) → Fin (n a) → Ω),
      (∀ a i, 0 ≤ w a i) ∧
      (∀ a, (∑ i, w a i) = μ.real univ) ∧
      (∀ a i, point a i ∈ s) ∧
      Filter.Tendsto (fun a => ∑ i,
        (weightedKraus (w a i) (K (point a i)))ᴴ *
          weightedKraus (w a i) (K (point a i)))
        Filter.atTop (nhds (∫ a, (K a)ᴴ * K a ∂μ)) ∧
      Filter.Tendsto (fun a => ∑ i, w a i • f (point a i))
        Filter.atTop (nhds (∫ a, f a ∂μ)) := by
  classical
  obtain ⟨n, w, point, hw, hmass, hpoint, hlim⟩ :=
    exists_integral_actual_point_quadrature_on μ (fun a => ((K a)ᴴ * K a, f a)) hf s hs
  refine ⟨n, w, point, hw, hmass, hpoint, ?_, ?_⟩
  · have h := (continuous_fst.tendsto _).comp hlim
    simpa only [Function.comp_def, Prod.fst_sum, Prod.smul_fst, fst_integral hf,
      weightedKraus_gram _ _ (hw _ _)] using h
  · have h := (continuous_snd.tendsto _).comp hlim
    simpa only [Function.comp_def, Prod.snd_sum, Prod.smul_snd, snd_integral hf] using h

variable [Fintype J] [DecidableEq J]

def reportedGram (K : Ω → Matrix η κ ℂ) (report : Ω → J) (a : Ω) :
    J → Matrix κ κ ℂ :=
  fun j => if report a = j then (K a)ᴴ * K a else 0

theorem exists_reported_sampled_kraus_quadrature_on
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → Matrix η κ ℂ) (report : Ω → J)
    (hf : Integrable (fun a => ((K a)ᴴ * K a, reportedGram K report a)) μ)
    (s : Set Ω) (hs : ∀ᵐ a ∂μ, a ∈ s) :
    ∃ (n : ℕ → ℕ) (w : (a : ℕ) → Fin (n a) → ℝ)
      (point : (a : ℕ) → Fin (n a) → Ω),
      (∀ a i, 0 ≤ w a i) ∧
      (∀ a, (∑ i, w a i) = μ.real univ) ∧
      (∀ a i, point a i ∈ s) ∧
      Filter.Tendsto (fun a => ∑ i,
        (weightedKraus (w a i) (K (point a i)))ᴴ *
          weightedKraus (w a i) (K (point a i)))
        Filter.atTop (nhds (∫ a, (K a)ᴴ * K a ∂μ)) ∧
      Filter.Tendsto (fun a j => ∑ i,
        if report (point a i) = j then
          (weightedKraus (w a i) (K (point a i)))ᴴ *
            weightedKraus (w a i) (K (point a i)) else 0)
        Filter.atTop (nhds (fun j => ∫ a, reportedGram K report a j ∂μ)) := by
  classical
  obtain ⟨n, w, point, hw, hmass, hpoint, hGram, hreport⟩ :=
    exists_joint_sampled_kraus_quadrature_on μ K (reportedGram K report) hf s hs
  refine ⟨n, w, point, hw, hmass, hpoint, hGram, ?_⟩
  have hvalues (a : ℕ) :
      (fun j => ∑ i, if report (point a i) = j then
        (weightedKraus (w a i) (K (point a i)))ᴴ *
          weightedKraus (w a i) (K (point a i)) else 0) =
      ∑ i, w a i • reportedGram K report (point a i) := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, reportedGram,
      weightedKraus_gram _ _ (hw _ _), smul_ite, smul_zero]
  have hintegral : (∫ a, reportedGram K report a ∂μ) =
      (fun j => ∫ a, reportedGram K report a j ∂μ) := by
    funext j
    exact eval_integral (fun j => hf.snd.eval j) j
  have hreport' := hreport.congr' (Filter.Eventually.of_forall fun a => (hvalues a).symm)
  simpa only [hintegral] using hreport'

theorem exists_complete_reported_kraus_quadrature
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → Matrix η κ ℂ) (report : Ω → J)
    (hK : Integrable (fun a => (K a)ᴴ * K a) μ)
    (hreport : ∀ j, Integrable (fun a => reportedGram K report a j) μ)
    (hcomplete : (∫ a, (K a)ᴴ * K a ∂μ) = 1) :
    ∃ (n : ℕ → ℕ) (w : (a : ℕ) → Fin (n a) → ℝ)
      (point : (a : ℕ) → Fin (n a) → Ω),
      (∀ a i, 0 ≤ w a i) ∧
      (∀ a, (∑ i, w a i) = μ.real univ) ∧
      Filter.Tendsto (fun a => ∑ i,
        (weightedKraus (w a i) (K (point a i)))ᴴ *
          weightedKraus (w a i) (K (point a i))) Filter.atTop (nhds 1) ∧
      Filter.Tendsto (fun a j => ∑ i,
        if report (point a i) = j then
          (weightedKraus (w a i) (K (point a i)))ᴴ *
            weightedKraus (w a i) (K (point a i)) else 0)
        Filter.atTop (nhds (fun j => ∫ a, reportedGram K report a j ∂μ)) := by
  have hjoint : Integrable (fun a => ((K a)ᴴ * K a, reportedGram K report a)) μ :=
    hK.prodMk (integrable_pi_iff.mpr hreport)
  obtain ⟨n, w, point, hw, hmass, _, hGram, hF⟩ :=
    exists_reported_sampled_kraus_quadrature_on μ K report hjoint univ
      (Filter.Eventually.of_forall fun _ => mem_univ _)
  exact ⟨n, w, point, hw, hmass, hcomplete ▸ hGram, hF⟩

end Kraus

end QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature
