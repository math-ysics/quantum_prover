import QuantumProver.InformationTheory.WernerEndpoint.PurityTheorems
import QuantumProver.InformationTheory.WernerEndpoint.WernerWedgeNormalization

noncomputable section

namespace QuantumProver.WernerEndpoint

open Matrix
open scoped BigOperators ComplexOrder Kronecker

def IsNormalizedSlater {d : ℕ} (u : Edge d → ℂ) : Prop :=
  ∃ x y : Fin d → ℂ, vectorNormSq x = 1 ∧ vectorNormSq y = 1 ∧
    dotProduct (star x) y = 0 ∧
    ∀ e : Edge d, u e = x e.val.1 * y e.val.2 - x e.val.2 * y e.val.1

theorem IsNormalizedSlater.normSq {d : ℕ} {u : Edge d → ℂ}
    (hu : IsNormalizedSlater u) : vectorNormSq u = 1 := by
  obtain ⟨x, y, hx, hy, hxy, heq⟩ := hu
  have hu : u = literalWedge x y := funext heq
  rw [hu]
  exact literalWedge_normSq_of_orthonormal x y hx hy hxy

theorem wedgeScale_ne_zero : wedgeScale ≠ 0 := by
  intro h
  have hs := wedgeScale_square
  rw [h] at hs
  norm_num at hs

def skewCoefficient {d : ℕ} (u : Edge d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun a b => wedgeScale⁻¹ * (wedgeInclusion d).mulVec u (a, b)

theorem skewCoefficient_forward {d : ℕ} (u : Edge d → ℂ)
    (a b : Fin d) (hab : a < b) :
    skewCoefficient u a b = u ⟨(a, b), hab⟩ := by
  simp [skewCoefficient, wedgeInclusion_mulVec_forward d a b hab, wedgeScale_ne_zero]

theorem skewCoefficient_swap {d : ℕ} (u : Edge d → ℂ) (a b : Fin d) :
    skewCoefficient u b a = -skewCoefficient u a b := by
  unfold skewCoefficient
  rw [wedgeInclusion_mulVec_swap d a b u]
  ring

theorem skewCoefficient_self {d : ℕ} (u : Edge d → ℂ) (a : Fin d) :
    skewCoefficient u a a = 0 := by
  simp [skewCoefficient, Matrix.mulVec, dotProduct, wedgeInclusion_diagonal]

theorem physicalCoefficient_eq_scale_skew {d : ℕ} (u : Edge d → ℂ)
    (a b : Fin d) :
    (wedgeInclusion d).mulVec u (a, b) = wedgeScale * skewCoefficient u a b := by
  simp [skewCoefficient, wedgeScale_ne_zero]

theorem skewCoefficient_literalWedge {d : ℕ} (x y : Fin d → ℂ) (a b : Fin d) :
    skewCoefficient (literalWedge x y) a b = x a * y b - x b * y a := by
  rcases lt_trichotomy a b with hab | hab | hba
  · rw [skewCoefficient_forward _ a b hab]
    rfl
  · subst b
    simp [skewCoefficient_self]
  · rw [skewCoefficient_swap, skewCoefficient_forward _ b a hba]
    dsimp [literalWedge]
    ring

def SatisfiesPlucker {d : ℕ} (u : Edge d → ℂ) : Prop :=
  ∀ a b c f : Fin d,
    skewCoefficient u a b * skewCoefficient u c f -
      skewCoefficient u a c * skewCoefficient u b f +
      skewCoefficient u a f * skewCoefficient u b c = 0

theorem literalWedge_satisfiesPlucker {d : ℕ} (x y : Fin d → ℂ) :
    SatisfiesPlucker (literalWedge x y) := by
  intro a b c f
  simp only [skewCoefficient_literalWedge]
  ring

theorem IsNormalizedSlater.satisfiesPlucker {d : ℕ} {u : Edge d → ℂ}
    (hu : IsNormalizedSlater u) : SatisfiesPlucker u := by
  obtain ⟨x, y, _, _, _, hxy⟩ := hu
  have heq : u = literalWedge x y := funext hxy
  rw [heq]
  exact literalWedge_satisfiesPlucker x y

theorem pairWedgeInclusion_replicaVector {d : ℕ} (u : Edge d → ℂ) :
    (pairWedgeInclusion d).mulVec (replicaVector u) =
      tensorVector ((wedgeInclusion d).mulVec u) ((wedgeInclusion d).mulVec u) := by
  change (wedgeInclusion d ⊗ₖ wedgeInclusion d).mulVec (tensorVector u u) = _
  exact QuantumProver.WernerEndpoint.SlaterMoments.kronecker_tensorVector_mulVec _ u u

theorem fourAntisymmetrizer_pairReplica_entry {d : ℕ} (u : Edge d → ℂ)
    (a b c f : Fin d) :
    (fourAntisymmetrizer d).mulVec
      ((pairWedgeInclusion d).mulVec (replicaVector u)) ((a, b), (c, f)) =
      (1 / 6 : ℂ) *
        (skewCoefficient u a b * skewCoefficient u c f -
          skewCoefficient u a c * skewCoefficient u b f +
          skewCoefficient u a f * skewCoefficient u b c) := by
  have hpair : (pairAntisymmetrizer d).mulVec
      ((pairWedgeInclusion d).mulVec (replicaVector u)) =
      (pairWedgeInclusion d).mulVec (replicaVector u) := by
    rw [Matrix.mulVec_mulVec, pairAntisymmetrizer_pairWedge]
  rw [fourAntisymmetrizer, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hpair]
  simp only [Pi.smul_apply, smul_eq_mul, sixCosetOperator_mulVec,
    pairWedgeInclusion_replicaVector, tensorVector,
    quadPairSwap, quadSwap13, quadSwap14, quadSwap23, quadSwap24]
  simp only [physicalCoefficient_eq_scale_skew,
    skewCoefficient_swap u b c, skewCoefficient_swap u b f,
    skewCoefficient_swap u a c]
  calc
    _ = (wedgeScale * wedgeScale) / 3 *
        (skewCoefficient u a b * skewCoefficient u c f -
          skewCoefficient u a c * skewCoefficient u b f +
          skewCoefficient u a f * skewCoefficient u b c) := by ring
    _ = _ := by rw [wedgeScale_square]; ring

theorem pairWedge_exterior_intertwines (d : ℕ) :
    pairWedgeInclusion d * exteriorReplicaProjector d =
      fourAntisymmetrizer d * pairWedgeInclusion d := by
  simp only [exteriorReplicaProjector]
  calc
    _ = (pairWedgeInclusion d * (pairWedgeInclusion d).conjTranspose) *
        fourAntisymmetrizer d * pairWedgeInclusion d := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [pairWedgeInclusion_projector, pairAntisymmetrizer_fourAntisymmetrizer]

theorem exterior_replica_zero_iff_plucker {d : ℕ} (u : Edge d → ℂ) :
    (exteriorReplicaProjector d).mulVec (replicaVector u) = 0 ↔
      SatisfiesPlucker u := by
  constructor
  · intro hzero a b c f
    have hphysical : (fourAntisymmetrizer d).mulVec
        ((pairWedgeInclusion d).mulVec (replicaVector u)) = 0 := by
      calc
        _ = (pairWedgeInclusion d).mulVec
            ((exteriorReplicaProjector d).mulVec (replicaVector u)) := by
          simp only [Matrix.mulVec_mulVec, pairWedge_exterior_intertwines]
        _ = 0 := by rw [hzero, Matrix.mulVec_zero]
    have he := congrFun hphysical ((a, b), (c, f))
    rw [fourAntisymmetrizer_pairReplica_entry] at he
    simpa only [Pi.zero_apply, mul_eq_zero, show (1 / 6 : ℂ) ≠ 0 by norm_num,
      false_or] using he
  · intro hp
    have hphysical : (fourAntisymmetrizer d).mulVec
        ((pairWedgeInclusion d).mulVec (replicaVector u)) = 0 := by
      ext ⟨⟨a, b⟩, ⟨c, f⟩⟩
      rw [fourAntisymmetrizer_pairReplica_entry, hp a b c f, mul_zero]
      rfl
    simp only [exteriorReplicaProjector, ← Matrix.mulVec_mulVec]
    rw [hphysical, Matrix.mulVec_zero]

theorem antisymmetric_purity_half_iff_plucker {d : ℕ} (u : Edge d → ℂ)
    (hu : vectorNormSq u = 1) :
    purity (antisymmetricChannel d (pureDensity u)) = 1 / 2 ↔
      SatisfiesPlucker u := by
  have ht := congrArg Complex.re (antisymmetric_pure_trace_coset d u)
  change purity (antisymmetricChannel d (pureDensity u)) = _ at ht
  norm_num [hu, Complex.sub_re, Complex.mul_re] at ht
  rw [← exterior_replica_zero_iff_plucker]
  constructor
  · intro hpur
    have hre : (dotProduct (star (replicaVector u))
        ((exteriorReplicaProjector d).mulVec (replicaVector u))).re = 0 := by
      linarith
    have hp := (exteriorReplicaProjector_posSemidef d).dotProduct_mulVec_nonneg
      (replicaVector u)
    have hz : dotProduct (star (replicaVector u))
        ((exteriorReplicaProjector d).mulVec (replicaVector u)) = 0 := by
      apply Complex.ext
      · exact hre
      · exact (Complex.nonneg_iff.mp hp).2.symm
    exact (exteriorReplicaProjector_posSemidef d).dotProduct_mulVec_zero_iff.mp hz
  · intro hzero
    simp only [hzero, dotProduct_zero, Complex.zero_re] at ht
    linarith

theorem exists_literalWedge_of_plucker {d : ℕ} (u : Edge d → ℂ)
    (hu : vectorNormSq u = 1) (hp : SatisfiesPlucker u) :
    ∃ x y : Fin d → ℂ, u = literalWedge x y := by
  classical
  have hex : ∃ e : Edge d, u e ≠ 0 := by
    by_contra hh
    have hz : ∀ e, u e = 0 := by simpa using hh
    have hn : vectorNormSq u = 0 := by simp [vectorNormSq, hz]
    linarith
  obtain ⟨e, he⟩ := hex
  let a := e.val.1
  let b := e.val.2
  let x : Fin d → ℂ := fun i => skewCoefficient u a i
  let y : Fin d → ℂ := fun i => skewCoefficient u b i / skewCoefficient u a b
  have hab : skewCoefficient u a b ≠ 0 := by
    simpa only [a, b, skewCoefficient_forward u e.val.1 e.val.2 e.property] using he
  refine ⟨x, y, ?_⟩
  ext f
  rw [← skewCoefficient_forward u f.val.1 f.val.2 f.property]
  dsimp [literalWedge, x, y]
  field_simp [hab]
  linear_combination hp a b f.val.1 f.val.2

theorem antisymmetric_purity_half_iff_slater {d : ℕ} (u : Edge d → ℂ)
    (hu : vectorNormSq u = 1) :
    purity (antisymmetricChannel d (pureDensity u)) = 1 / 2 ↔
      IsNormalizedSlater u := by
  constructor
  · intro hpur
    have hp := (antisymmetric_purity_half_iff_plucker u hu).mp hpur
    obtain ⟨x, y, hxy⟩ := exists_literalWedge_of_plucker u hu hp
    have hn : vectorNormSq (literalWedge x y) = 1 := by rw [← hxy]; exact hu
    obtain ⟨v, w, hv, hw, hvw, heq⟩ := normalize_literalWedge x y hn
    refine ⟨v, w, hv, hw, hvw, ?_⟩
    intro e
    exact congrFun (hxy.trans heq.symm) e
  · intro hslater
    exact (antisymmetric_purity_half_iff_plucker u hu).mpr hslater.satisfiesPlucker

theorem IsNormalizedSlater.physical {d : ℕ} {u : Edge d → ℂ}
    (hu : IsNormalizedSlater u) :
    ∃ x y : Fin d → ℂ, vectorNormSq x = 1 ∧ vectorNormSq y = 1 ∧
      dotProduct (star x) y = 0 ∧
      (wedgeInclusion d).mulVec u =
        fun ab => wedgeScale * (x ab.1 * y ab.2 - x ab.2 * y ab.1) := by
  obtain ⟨x, y, hx, hy, hxy, heq⟩ := hu
  refine ⟨x, y, hx, hy, hxy, ?_⟩
  have hu : u = literalWedge x y := funext heq
  rw [hu]
  ext ⟨a, b⟩
  rw [physicalCoefficient_eq_scale_skew, skewCoefficient_literalWedge]

theorem antisymmetric_slater_purity {d : ℕ} {u : Edge d → ℂ}
    (hu : IsNormalizedSlater u) :
    purity (antisymmetricChannel d (pureDensity u)) = 1 / 2 :=
  (antisymmetric_purity_half_iff_slater u hu.normSq).mpr hu

theorem antisymmetric_purity_half_iff_physicalSlater {d : ℕ} (u : Edge d → ℂ)
    (hu : vectorNormSq u = 1) :
    purity (antisymmetricChannel d (pureDensity u)) = 1 / 2 ↔
    ∃ x y : Fin d → ℂ, vectorNormSq x = 1 ∧ vectorNormSq y = 1 ∧
      dotProduct (star x) y = 0 ∧
      (wedgeInclusion d).mulVec u =
        fun ab => wedgeScale * (x ab.1 * y ab.2 - x ab.2 * y ab.1) := by
  rw [antisymmetric_purity_half_iff_slater u hu]
  constructor
  · exact IsNormalizedSlater.physical
  · rintro ⟨x, y, hx, hy, hxy, hphysical⟩
    refine ⟨x, y, hx, hy, hxy, ?_⟩
    intro e
    apply mul_left_cancel₀ wedgeScale_ne_zero
    have he := congrFun hphysical e.val
    simpa only [wedgeInclusion_mulVec_forward d e.val.1 e.val.2 e.property] using he

end QuantumProver.WernerEndpoint
