import Mathlib

/-!
Actual real weak-dual integration map for finite measures, affine weak images,
continuous-test representation, and compact-convex separation/membership.
These results do not assume a coupling or a capacity sufficiency theorem.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace FinitePR.Dual

open MeasureTheory Set TopologicalSpace
open scoped Topology NNReal

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S]

abbrev RealTests (S : Type*) [TopologicalSpace S] := BoundedContinuousFunction S ℝ
abbrev RealWeak (S : Type*) [TopologicalSpace S] := WeakDual ℝ (RealTests S)

instance realWeak_locallyConvex : LocallyConvexSpace ℝ (RealWeak S) := by
  convert (WeakBilin.locallyConvexSpace (𝕜 := ℝ) (E := StrongDual ℝ (RealTests S))
    (F := RealTests S) (B := topDualPairing ℝ (RealTests S))) using 1 <;> rfl

/-- Integration is a genuine real linear functional of a bounded continuous test. -/
def integralLinear (μ : FiniteMeasure S) : RealTests S →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x ∂(μ : Measure S)
  map_add' f g := by
    change (∫ x, f x + g x ∂(μ : Measure S)) =
      (∫ x, f x ∂(μ : Measure S)) + ∫ x, g x ∂(μ : Measure S)
    exact integral_add (f.integrable _) (g.integrable _)
  map_smul' c f := by
    change (∫ x, c • f x ∂(μ : Measure S)) = c • ∫ x, f x ∂(μ : Measure S)
    exact integral_smul c _

/-- The finite-mass sup-norm bound makes the integration functional continuous. -/
def integralCLM (μ : FiniteMeasure S) : RealTests S →L[ℝ] ℝ :=
  (integralLinear μ).mkContinuous ((μ : Measure S).real Set.univ)
    (fun f => f.norm_integral_le_mul_norm (μ : Measure S))

/-- The finite measure's integration functional with the real weak-star topology. -/
def finiteMeasureWeak (μ : FiniteMeasure S) : RealWeak S :=
  StrongDual.toWeakDual (integralCLM μ)

@[simp] theorem finiteMeasureWeak_apply (μ : FiniteMeasure S) (f : RealTests S) :
    finiteMeasureWeak μ f = ∫ x, f x ∂(μ : Measure S) := rfl

theorem continuous_finiteMeasureWeak :
    Continuous (finiteMeasureWeak : FiniteMeasure S → RealWeak S) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  simpa only [finiteMeasureWeak_apply] using
    FiniteMeasure.continuous_integral_boundedContinuousFunction f

def probabilityMeasureWeak (μ : ProbabilityMeasure S) : RealWeak S :=
  finiteMeasureWeak μ.toFiniteMeasure

@[simp] theorem probabilityMeasureWeak_apply (μ : ProbabilityMeasure S) (f : RealTests S) :
    probabilityMeasureWeak μ f = ∫ x, f x ∂(μ : Measure S) := rfl

theorem continuous_probabilityMeasureWeak :
    Continuous (probabilityMeasureWeak : ProbabilityMeasure S → RealWeak S) :=
  continuous_finiteMeasureWeak.comp ProbabilityMeasure.toFiniteMeasure_continuous

@[simp] theorem finiteMeasureWeak_zero : finiteMeasureWeak (0 : FiniteMeasure S) = 0 := by
  apply DFunLike.ext
  intro f
  change (∫ x, f x ∂((0 : FiniteMeasure S) : Measure S)) = 0
  simp

theorem finiteMeasureWeak_add (μ ν : FiniteMeasure S) :
    finiteMeasureWeak (μ + ν) = finiteMeasureWeak μ + finiteMeasureWeak ν := by
  apply DFunLike.ext
  intro f
  change (∫ x, f x ∂((μ + ν : FiniteMeasure S) : Measure S)) =
    (∫ x, f x ∂(μ : Measure S)) + ∫ x, f x ∂(ν : Measure S)
  rw [FiniteMeasure.toMeasure_add]
  exact integral_add_measure (f.integrable _) (f.integrable _)

theorem finiteMeasureWeak_smul (c : ℝ≥0) (μ : FiniteMeasure S) :
    finiteMeasureWeak (c • μ) = (c : ℝ) • finiteMeasureWeak μ := by
  apply DFunLike.ext
  intro f
  change (∫ x, f x ∂((c • μ : FiniteMeasure S) : Measure S)) =
    (c : ℝ) • ∫ x, f x ∂(μ : Measure S)
  simp only [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure, NNReal.smul_def]

theorem finiteMeasureWeak_mix (a b : ℝ≥0) (μ ν : FiniteMeasure S) :
    finiteMeasureWeak (a • μ + b • ν) =
      (a : ℝ) • finiteMeasureWeak μ + (b : ℝ) • finiteMeasureWeak ν := by
  rw [finiteMeasureWeak_add, finiteMeasureWeak_smul, finiteMeasureWeak_smul]

theorem realWeak_image_compact {M : Set (FiniteMeasure S)} (hM : IsCompact M) :
    IsCompact (finiteMeasureWeak '' M) := hM.image continuous_finiteMeasureWeak

/-- Nonnegative-real cone convexity becomes real convexity in the genuine vector space. -/
theorem realWeak_image_convex {M : Set (FiniteMeasure S)} (hM : Convex ℝ≥0 M) :
    Convex ℝ (finiteMeasureWeak '' M) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨μ, hμ, rfl⟩ := hx
  obtain ⟨ν, hν, rfl⟩ := hy
  let a' : ℝ≥0 := ⟨a, ha⟩
  let b' : ℝ≥0 := ⟨b, hb⟩
  have hab' : a' + b' = 1 := by
    apply NNReal.eq
    exact hab
  refine ⟨a' • μ + b' • ν,
    hM hμ hν (by positivity) (by positivity) hab', ?_⟩
  rw [finiteMeasureWeak_mix]
  rfl

/-- Every weakly continuous real linear functional is one continuous-test evaluation. -/
theorem weak_continuous_functional_eq_test (L : RealWeak S →L[ℝ] ℝ) :
    ∃ f : RealTests S, ∀ w : RealWeak S, L w = w f := by
  let L' : StrongDual ℝ (WeakBilin (topDualPairing ℝ (RealTests S))) := L
  obtain ⟨f, hf⟩ := LinearMap.dualEmbedding_surjective (𝕜 := ℝ)
    (E := StrongDual ℝ (RealTests S)) (F := RealTests S)
    (topDualPairing ℝ (RealTests S)) L'
  refine ⟨f, fun w => ?_⟩
  have h := congrArg (fun A : RealWeak S →L[ℝ] ℝ => A w) hf
  change w f = L w at h
  exact h.symm

theorem weak_continuous_functional_is_integral (L : RealWeak S →L[ℝ] ℝ) :
    ∃ f : RealTests S, ∀ μ : FiniteMeasure S,
      L (finiteMeasureWeak μ) = ∫ x, f x ∂(μ : Measure S) := by
  obtain ⟨f, hf⟩ := weak_continuous_functional_eq_test L
  exact ⟨f, fun μ => hf (finiteMeasureWeak μ)⟩

section Injective

variable [HasOuterApproxClosed S] [BorelSpace S]

theorem finiteMeasureWeak_injective :
    Function.Injective (finiteMeasureWeak : FiniteMeasure S → RealWeak S) := by
  intro μ ν h
  apply FiniteMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact congrArg (fun w : RealWeak S => w f) h

/-- A finite measure outside a compact convex set is strictly separated by one real test. -/
theorem integral_test_strict_separation (M : Set (FiniteMeasure S))
    (hcompact : IsCompact M) (hconvex : Convex ℝ≥0 M)
    (ν : FiniteMeasure S) (hν : ν ∉ M) :
    ∃ (f : RealTests S) (u : ℝ),
      (∀ μ ∈ M, (∫ x, f x ∂(μ : Measure S)) < u) ∧
        u < ∫ x, f x ∂(ν : Measure S) := by
  have hnot : finiteMeasureWeak ν ∉ finiteMeasureWeak '' M := by
    rintro ⟨μ, hμ, heq⟩
    have hμν := finiteMeasureWeak_injective heq
    exact hν (hμν ▸ hμ)
  obtain ⟨L, u, hL, hu⟩ := geometric_hahn_banach_closed_point
    (realWeak_image_convex hconvex) (realWeak_image_compact hcompact).isClosed hnot
  obtain ⟨f, hf⟩ := weak_continuous_functional_is_integral L
  refine ⟨f, u, ?_, ?_⟩
  · intro μ hμ
    simpa only [hf μ] using hL (finiteMeasureWeak μ) (Set.mem_image_of_mem _ hμ)
  · simpa only [hf ν] using hu

/-- Continuous-test domination is sufficient for membership in a compact convex measure set.

The witnesses in the premise can be supplied by maximizing list couplings; no
coupling existence or capacity theorem is built into this result.
-/
theorem mem_of_forall_test_exists (M : Set (FiniteMeasure S))
    (hcompact : IsCompact M) (hconvex : Convex ℝ≥0 M) (ν : FiniteMeasure S)
    (hbound : ∀ f : RealTests S, ∃ μ ∈ M,
      (∫ x, f x ∂(ν : Measure S)) ≤ ∫ x, f x ∂(μ : Measure S)) :
    ν ∈ M := by
  by_contra hν
  obtain ⟨f, u, hf, hu⟩ := integral_test_strict_separation M hcompact hconvex ν hν
  obtain ⟨μ, hμ, hcmp⟩ := hbound f
  have hμu := hf μ hμ
  linarith

end Injective

end FinitePR.Dual
