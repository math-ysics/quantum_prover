import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Register finite-dimensional dependencies for the environment-qubit exclusion.
This module does not assume the research result and does not import the main
theorem. In particular, rectangular Gram alignment includes singular ranks.
-/

noncomputable section

open Matrix
open scoped InnerProductSpace ComplexOrder

namespace TransposeDegradability

section RangeAlignment

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- Equal pullback inner products allow a map on a possibly singular range
to extend to an isometry of the full finite-dimensional ambient space. -/
theorem exists_linearIsometry_extends_of_inner_eq
    (f g : E →ₗ[ℂ] F)
    (hinner : ∀ x y, ⟪f x, f y⟫_ℂ = ⟪g x, g y⟫_ℂ) :
    ∃ U : F →ₗᵢ[ℂ] F, ∀ x, U (f x) = g x := by
  classical
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective
    f.range_rangeRestrict
  have hfs (v : LinearMap.range f) : f (s v) = v := by
    exact congrArg Subtype.val (LinearMap.congr_fun hs v)
  let L : LinearMap.range f →ₗ[ℂ] F := g.comp s
  have hLinner : ∀ v w, ⟪L v, L w⟫_ℂ = ⟪v, w⟫_ℂ := by
    intro v w
    change ⟪g (s v), g (s w)⟫_ℂ = ⟪(v : F), (w : F)⟫_ℂ
    rw [← hinner, hfs, hfs]
  let Li : LinearMap.range f →ₗᵢ[ℂ] F := L.isometryOfInner hLinner
  refine ⟨Li.extend, ?_⟩
  intro x
  let v : LinearMap.range f := ⟨f x, LinearMap.mem_range_self f x⟩
  have hfzero : f (s v - x) = 0 := by
    rw [map_sub, hfs]
    exact sub_self (f x)
  have hgzero : g (s v - x) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [← hinner, hfzero]
    simp
  have hgs : g (s v) = g x := by
    simpa only [map_sub, sub_eq_zero] using hgzero
  calc
    Li.extend (f x) = Li.extend v := rfl
    _ = Li v := Li.extend_apply v
    _ = g (s v) := rfl
    _ = g x := hgs

end RangeAlignment

section RectangularGram

variable {R K : Type*} [Fintype R] [DecidableEq R]
  [Fintype K] [DecidableEq K]

omit [DecidableEq R] [DecidableEq K] in
/-- A zero rectangular row Gram forces the entire factor to vanish. -/
theorem rowGram_eq_zero_iff (B : Matrix R K ℂ) : B * Bᴴ = 0 ↔ B = 0 := by
  constructor
  · intro h
    apply Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
    rw [h]
    simp
  · rintro rfl
    simp

omit [DecidableEq R] in
/-- At rank zero the matching column unitary can explicitly be the identity. -/
theorem exists_unitary_right_of_zero_rowGram
    (B G : Matrix R K ℂ) (hzero : B * Bᴴ = 0)
    (hGram : B * Bᴴ = G * Gᴴ) :
    ∃ W : Matrix K K ℂ,
      W = 1 ∧ W * Wᴴ = 1 ∧ Wᴴ * W = 1 ∧ G = B * W := by
  have hB : B = 0 := (rowGram_eq_zero_iff B).mp hzero
  have hG : G = 0 := (rowGram_eq_zero_iff G).mp (hGram.symm.trans hzero)
  exact ⟨1, rfl, by simp, by simp, by simp [hB, hG]⟩

/-- Matching rectangular row Grams implies a unitary rotation of the common
factor-column space. Neither Gram invertibility nor full row rank is needed. -/
theorem exists_unitary_right_of_rowGram_eq
    (B G : Matrix R K ℂ) (hGram : B * Bᴴ = G * Gᴴ) :
    ∃ W : Matrix K K ℂ,
      W * Wᴴ = 1 ∧ Wᴴ * W = 1 ∧ G = B * W := by
  classical
  let f : EuclideanSpace ℂ R →ₗ[ℂ] EuclideanSpace ℂ K := Bᴴ.toEuclideanLin
  let g : EuclideanSpace ℂ R →ₗ[ℂ] EuclideanSpace ℂ K := Gᴴ.toEuclideanLin
  have hop : f.adjoint.comp f = g.adjoint.comp g := by
    have h := congrArg (fun M : Matrix R R ℂ => M.toEuclideanLin) hGram
    simpa only [f, g, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
      LinearMap.adjoint_adjoint] using h
  have hinner : ∀ x y, ⟪f x, f y⟫_ℂ = ⟪g x, g y⟫_ℂ := by
    intro x y
    calc
      ⟪f x, f y⟫_ℂ = ⟪x, f.adjoint (f y)⟫_ℂ :=
        (LinearMap.adjoint_inner_right f x (f y)).symm
      _ = ⟪x, g.adjoint (g y)⟫_ℂ := by
        rw [← LinearMap.comp_apply, hop, LinearMap.comp_apply]
      _ = ⟪g x, g y⟫_ℂ := LinearMap.adjoint_inner_right g x (g y)
  obtain ⟨U, hU⟩ := exists_linearIsometry_extends_of_inner_eq f g hinner
  let M : Matrix K K ℂ := Matrix.toEuclideanLin.symm U.toLinearMap
  have hM : M.toEuclideanLin = U.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply U.toLinearMap
  have hMstar : Mᴴ * M = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, Matrix.toLpLin_one]
    change Mᴴ.toEuclideanLin.comp M.toEuclideanLin = LinearMap.id
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hM]
    exact U.adjoint_comp_self'
  have hMMstar : M * Mᴴ = 1 := (mul_eq_one_comm).mp hMstar
  have hMB : M * Bᴴ = Gᴴ := by
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same]
    change M.toEuclideanLin.comp f = g
    rw [hM]
    exact LinearMap.ext hU
  have hBG : B * Mᴴ = G := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      using congrArg Matrix.conjTranspose hMB
  refine ⟨Mᴴ, ?_, ?_, hBG.symm⟩
  · simpa only [Matrix.conjTranspose_conjTranspose] using hMstar
  · simpa only [Matrix.conjTranspose_conjTranspose] using hMMstar

omit [Fintype R] [DecidableEq R] in
/-- The off-diagonal block retained by the aligned qubit factor. -/
theorem aligned_crossGram (B G D : Matrix R K ℂ) (W : Matrix K K ℂ)
    (hW : W * Wᴴ = 1) (hG : G = B * W) :
    G * (D * W)ᴴ = B * Dᴴ := by
  calc
    G * (D * W)ᴴ = (B * W) * (Wᴴ * Dᴴ) := by
      rw [hG, Matrix.conjTranspose_mul]
    _ = B * (W * Wᴴ) * Dᴴ := by simp only [Matrix.mul_assoc]
    _ = B * Dᴴ := by rw [hW, Matrix.mul_one]

omit [Fintype R] [DecidableEq R] in
/-- A unitary factor-column rotation preserves the last diagonal block. -/
theorem aligned_lastGram (D : Matrix R K ℂ) (W : Matrix K K ℂ)
    (hW : W * Wᴴ = 1) : (D * W) * (D * W)ᴴ = D * Dᴴ := by
  rw [Matrix.conjTranspose_mul]
  calc
    (D * W) * (Wᴴ * Dᴴ) = D * (W * Wᴴ) * Dᴴ := by
      simp only [Matrix.mul_assoc]
    _ = D * Dᴴ := by rw [hW, Matrix.mul_one]

end RectangularGram

end TransposeDegradability
