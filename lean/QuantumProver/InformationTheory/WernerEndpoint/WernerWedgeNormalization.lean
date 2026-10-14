import QuantumProver.InformationTheory.WernerEndpoint.AntisymmetricStates

noncomputable section

namespace QuantumProver.WernerEndpoint

open scoped BigOperators
open Matrix

def literalWedge {d : ℕ} (x y : Fin d → ℂ) : Edge d → ℂ :=
  fun e => x e.val.1 * y e.val.2 - x e.val.2 * y e.val.1

namespace WedgeNormalization

theorem normSq_smul {I : Type*} [Fintype I] (z : ℂ) (x : I → ℂ) :
    vectorNormSq (z • x) = Complex.normSq z * vectorNormSq x := by
  simp [vectorNormSq, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Finset.mul_sum]

theorem normSq_nonneg {I : Type*} [Fintype I] (x : I → ℂ) :
    0 ≤ vectorNormSq x := by
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (x i)

theorem gram_self {I : Type*} [Fintype I] (x : I → ℂ) :
    dotProduct (star x) x = (vectorNormSq x : ℂ) := by
  simp [dotProduct, vectorNormSq, mul_comm, Complex.mul_conj]

def minor {d : ℕ} (x y : Fin d → ℂ) (a b : Fin d) : ℂ :=
  x a * y b - x b * y a

theorem minor_self {d : ℕ} (x y : Fin d → ℂ) (a : Fin d) :
    minor x y a a = 0 := by
  simp [minor]

theorem minor_swap {d : ℕ} (x y : Fin d → ℂ) (a b : Fin d) :
    minor x y b a = -minor x y a b := by
  simp [minor]

theorem minor_normProduct {d : ℕ} (x y : Fin d → ℂ) (a b : Fin d) :
    minor x y a b * star (minor x y a b) =
      (star (x a) * x a) * (star (y b) * y b) +
      (star (y a) * y a) * (star (x b) * x b) -
      (star (y a) * x a) * (star (x b) * y b) -
      (star (x a) * y a) * (star (y b) * x b) := by
  simp only [minor, star_sub, star_mul]
  ring

theorem minor_full_normProduct {d : ℕ} (x y : Fin d → ℂ) :
    (∑ a : Fin d, ∑ b : Fin d, minor x y a b * star (minor x y a b)) =
      (2 : ℂ) * ((vectorNormSq x : ℂ) * (vectorNormSq y : ℂ) -
        (Complex.normSq (dotProduct (star x) y) : ℂ)) := by
  simp_rw [minor_normProduct, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  change dotProduct (star x) x * dotProduct (star y) y +
      dotProduct (star y) y * dotProduct (star x) x -
      dotProduct (star y) x * dotProduct (star x) y -
      dotProduct (star x) y * dotProduct (star y) x = _
  rw [gram_self, gram_self, star_dotProduct y x]
  have hmul : dotProduct (star x) y * star (dotProduct (star x) y) =
      (Complex.normSq (dotProduct (star x) y) : ℂ) := by
    simpa only [Complex.star_def] using Complex.mul_conj (dotProduct (star x) y)
  calc
    _ = (2 : ℂ) * ((vectorNormSq x : ℂ) * (vectorNormSq y : ℂ) -
        dotProduct (star x) y * star (dotProduct (star x) y)) := by ring
    _ = _ := by rw [hmul]

theorem minor_full_normSq {d : ℕ} (x y : Fin d → ℂ) :
    (∑ a : Fin d, ∑ b : Fin d, Complex.normSq (minor x y a b)) =
      2 * (vectorNormSq x * vectorNormSq y -
        Complex.normSq (dotProduct (star x) y)) := by
  have h := congrArg Complex.re (minor_full_normProduct x y)
  simpa [Complex.star_def, Complex.mul_conj] using h

theorem minor_edge_double {d : ℕ} (x y : Fin d → ℂ) :
    (∑ a : Fin d, ∑ b : Fin d, Complex.normSq (minor x y a b)) =
      2 * vectorNormSq (literalWedge x y) := by
  classical
  let f : Fin d × Fin d → ℝ := fun p => Complex.normSq (minor x y p.1 p.2)
  have hm : (∑ p : Fin d × Fin d, if p.1 < p.2 then f p else 0) =
      ∑ e : Edge d, f e.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) f
  have hswap : (∑ p : Fin d × Fin d, if p.2 < p.1 then f p else 0) =
      ∑ p : Fin d × Fin d, if p.1 < p.2 then f p else 0 := by
    calc
      _ = ∑ p : Fin d × Fin d, if p.2 < p.1 then f (p.2, p.1) else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        simp only [f]
        rw [minor_swap x y p.1 p.2, Complex.normSq_neg]
      _ = _ := (Equiv.prodComm (Fin d) (Fin d)).sum_comp
        (fun p : Fin d × Fin d => if p.1 < p.2 then f p else 0)
  have hsplit : (∑ p : Fin d × Fin d, f p) =
      (∑ p : Fin d × Fin d, if p.1 < p.2 then f p else 0) +
      (∑ p : Fin d × Fin d, if p.2 < p.1 then f p else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · simp [f, h, minor_self]
    · simp [h, not_lt_of_ge h.le]
  rw [hswap, hm] at hsplit
  simpa [Fintype.sum_prod_type, f, vectorNormSq, literalWedge, minor, two_mul]
    using hsplit

end WedgeNormalization

theorem literalWedge_normSq {d : ℕ} (x y : Fin d → ℂ) :
    vectorNormSq (literalWedge x y) = vectorNormSq x * vectorNormSq y -
      Complex.normSq (dotProduct (star x) y) := by
  have h := WedgeNormalization.minor_edge_double x y
  rw [WedgeNormalization.minor_full_normSq] at h
  linarith

theorem literalWedge_normSq_of_orthogonal {d : ℕ} (x y : Fin d → ℂ)
    (hxy : dotProduct (star x) y = 0) :
    vectorNormSq (literalWedge x y) = vectorNormSq x * vectorNormSq y := by
  rw [literalWedge_normSq, hxy]
  simp

theorem literalWedge_normSq_of_orthonormal {d : ℕ} (x y : Fin d → ℂ)
    (hx : vectorNormSq x = 1) (hy : vectorNormSq y = 1)
    (hxy : dotProduct (star x) y = 0) :
    vectorNormSq (literalWedge x y) = 1 := by
  rw [literalWedge_normSq_of_orthogonal x y hxy, hx, hy, one_mul]

theorem literalWedge_smul_smul {d : ℕ} (x y : Fin d → ℂ) (z t : ℂ) :
    literalWedge (z • x) (t • y) = (z * t) • literalWedge x y := by
  ext e
  simp only [literalWedge, Pi.smul_apply, smul_eq_mul]
  ring

theorem literalWedge_sub_smul {d : ℕ} (x y : Fin d → ℂ) (c : ℂ) :
    literalWedge x (y - c • x) = literalWedge x y := by
  ext e
  simp only [literalWedge, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem normalize_literalWedge {d : ℕ} (x y : Fin d → ℂ)
    (h : vectorNormSq (literalWedge x y) = 1) :
    ∃ v w : Fin d → ℂ, vectorNormSq v = 1 ∧ vectorNormSq w = 1 ∧
      dotProduct (star v) w = 0 ∧ literalWedge v w = literalWedge x y := by
  have hx_nonneg := WedgeNormalization.normSq_nonneg x
  have hx_pos : 0 < vectorNormSq x := by
    have hx_ne : vectorNormSq x ≠ 0 := by
      intro hx_zero
      have hg := literalWedge_normSq x y
      rw [h, hx_zero, zero_mul] at hg
      have hgn := Complex.normSq_nonneg (dotProduct (star x) y)
      linarith
    exact lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)
  let a : ℝ := Real.sqrt (vectorNormSq x)
  have ha_pos : 0 < a := Real.sqrt_pos.2 hx_pos
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have ha_square : a * a = vectorNormSq x := Real.mul_self_sqrt hx_nonneg
  let v : Fin d → ℂ := ((a⁻¹ : ℝ) : ℂ) • x
  let b : Fin d → ℂ := (a : ℂ) • y
  let w : Fin d → ℂ := b - dotProduct (star v) b • v
  have hv : vectorNormSq v = 1 := by
    change vectorNormSq (((a⁻¹ : ℝ) : ℂ) • x) = 1
    rw [WedgeNormalization.normSq_smul, Complex.normSq_ofReal, ← ha_square]
    field_simp [ha_ne]
  have hvw : dotProduct (star v) w = 0 := by
    change dotProduct (star v) (b - dotProduct (star v) b • v) = 0
    rw [dotProduct_sub, dotProduct_smul (dotProduct (star v) b) (star v) v,
      WedgeNormalization.gram_self, hv]
    simp
  have heq : literalWedge v w = literalWedge x y := by
    change literalWedge v (b - dotProduct (star v) b • v) = _
    rw [literalWedge_sub_smul]
    change literalWedge (((a⁻¹ : ℝ) : ℂ) • x) ((a : ℂ) • y) = _
    rw [literalWedge_smul_smul]
    have hc : ((a⁻¹ : ℝ) : ℂ) * (a : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ ha_ne, Complex.ofReal_one]
    rw [hc, one_smul]
  have hw : vectorNormSq w = 1 := by
    have hg := literalWedge_normSq v w
    rw [heq, h, hv, hvw] at hg
    simpa using hg.symm
  exact ⟨v, w, hv, hw, hvw, heq⟩

end QuantumProver.WernerEndpoint
