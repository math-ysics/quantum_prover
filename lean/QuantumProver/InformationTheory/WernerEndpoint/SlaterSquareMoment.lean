import Mathlib
import QuantumProver.InformationTheory.WernerEndpoint.AntisymmetricStates
import QuantumProver.InformationTheory.WernerEndpoint.D5SupportFactor

noncomputable section

namespace QuantumProver.WernerEndpoint.SlaterMoments

open QuantumProver.WernerEndpoint MeasureTheory TopologicalSpace
open scoped BigOperators ComplexOrder Kronecker Matrix.Norms.Elementwise

local instance matrixContinuousENorm {I J : Type*} [Fintype I] [Fintype J] :
    ContinuousENorm (Matrix I J ℂ) :=
  inferInstanceAs (ContinuousENorm (I → J → ℂ))

local instance matrixPseudoMetrizableSpace {I J : Type*} [Fintype I] [Fintype J] :
    PseudoMetrizableSpace (Matrix I J ℂ) :=
  inferInstanceAs (PseudoMetrizableSpace (I → J → ℂ))

local instance matrixSecondCountableTopology {I J : Type*} [Fintype I] [Fintype J] :
    SecondCountableTopology (Matrix I J ℂ) :=
  inferInstanceAs (SecondCountableTopology (I → J → ℂ))

abbrev PhysicalUnitary (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

def columnMinor {d : ℕ} (U : PhysicalUnitary d) (i j a b : Fin d) : ℂ :=
  U a i * U b j - U a j * U b i

def slaterVector {d : ℕ} (U : PhysicalUnitary d) (i j : Fin d) : Edge d → ℂ :=
  fun e => columnMinor U i j e.val.1 e.val.2

def slaterSquare {d : ℕ} (U : PhysicalUnitary d) (i j : Fin d) : Edge d × Edge d → ℂ :=
  fun ef => slaterVector U i j ef.1 * slaterVector U i j ef.2

def slaterSquareDensity {d : ℕ} (U : PhysicalUnitary d) (i j : Fin d) :
    Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ :=
  pureDensity (slaterSquare U i j)

theorem slaterSquareDensity_entry {d : ℕ} (U : PhysicalUnitary d) (i j : Fin d)
    (ef gh : Edge d × Edge d) :
    slaterSquareDensity U i j ef gh =
      slaterVector U i j ef.1 * slaterVector U i j ef.2 *
        (star (slaterVector U i j gh.1) * star (slaterVector U i j gh.2)) := by
  simp only [slaterSquareDensity, pureDensity, crossDensity, slaterSquare, star_mul]
  ring

theorem columnMinor_self {d : ℕ} (U : PhysicalUnitary d) (i j a : Fin d) :
    columnMinor U i j a a = 0 := by
  simp [columnMinor, mul_comm]

theorem columnMinor_swap {d : ℕ} (U : PhysicalUnitary d) (i j a b : Fin d) :
    columnMinor U i j b a = -columnMinor U i j a b := by
  dsimp [columnMinor]
  ring

theorem columnMinor_plucker {d : ℕ} (U : PhysicalUnitary d) (i j a b c f : Fin d) :
    columnMinor U i j a b * columnMinor U i j c f -
      columnMinor U i j a c * columnMinor U i j b f +
      columnMinor U i j a f * columnMinor U i j b c = 0 := by
  dsimp [columnMinor]
  ring

theorem columnMinor_swap_columns {d : ℕ} (U : PhysicalUnitary d) (i j a b : Fin d) :
    columnMinor U j i a b = -columnMinor U i j a b := by
  dsimp [columnMinor]
  ring

theorem ordered_sum_eq_twice_edge {d : ℕ} (g : Fin d × Fin d → ℂ)
    (hdiag : ∀ a, g (a, a) = 0) (hsym : ∀ a b, g (b, a) = g (a, b)) :
    (∑ a : Fin d, ∑ b : Fin d, g (a, b)) = 2 * ∑ e : Edge d, g e.val := by
  classical
  have hm : (∑ p : Fin d × Fin d, if p.1 < p.2 then g p else 0) =
      ∑ e : Edge d, g e.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) g
  have hswap : (∑ p : Fin d × Fin d, if p.2 < p.1 then g p else 0) =
      ∑ p : Fin d × Fin d, if p.1 < p.2 then g p else 0 := by
    calc
      _ = ∑ p : Fin d × Fin d, if p.2 < p.1 then g (p.2, p.1) else 0 := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hsym]
      _ = _ := (Equiv.prodComm (Fin d) (Fin d)).sum_comp
        (fun p : Fin d × Fin d => if p.1 < p.2 then g p else 0)
  have hsplit : (∑ p : Fin d × Fin d, g p) =
      (∑ p : Fin d × Fin d, if p.1 < p.2 then g p else 0) +
      (∑ p : Fin d × Fin d, if p.2 < p.1 then g p else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · rcases p with ⟨a, b⟩
      dsimp at h
      subst b
      simp [hdiag]
    · simp [h, not_lt_of_ge h.le]
  rw [hswap, hm] at hsplit
  simpa [Fintype.sum_prod_type, two_mul] using hsplit

theorem columnMinor_mul {d : ℕ} (V U : PhysicalUnitary d) (i j a b : Fin d) :
    columnMinor (V * U) i j a b = ∑ e : Edge d,
      columnMinor V e.val.1 e.val.2 a b * columnMinor U i j e.val.1 e.val.2 := by
  let g : Fin d × Fin d → ℂ := fun p =>
    columnMinor V p.1 p.2 a b * columnMinor U i j p.1 p.2
  have hdiag : ∀ c, g (c, c) = 0 := by
    intro c
    simp [g, columnMinor_self]
  have hsym : ∀ c f, g (f, c) = g (c, f) := by
    intro c f
    simp only [g, columnMinor_swap_columns V c f a b, columnMinor_swap U i j c f]
    ring
  have hp : ∀ c f, g (c, f) =
      (V a c * U c i) * (V b f * U f j) -
      (V a c * U c j) * (V b f * U f i) -
      (V b c * U c i) * (V a f * U f j) +
      (V b c * U c j) * (V a f * U f i) := by
    intro c f
    dsimp [g, columnMinor]
    ring
  have hfull : (∑ c : Fin d, ∑ f : Fin d, g (c, f)) =
      2 * columnMinor (V * U) i j a b := by
    simp_rw [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    simp only [columnMinor, Matrix.UnitaryGroup.mul_apply, Matrix.mul_apply]
    ring
  have horder := ordered_sum_eq_twice_edge g hdiag hsym
  rw [hfull] at horder
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) horder

def wedgeAction {d : ℕ} (V : PhysicalUnitary d) : Matrix (Edge d) (Edge d) ℂ :=
  fun e f => columnMinor V f.val.1 f.val.2 e.val.1 e.val.2

theorem slaterVector_mul {d : ℕ} (V U : PhysicalUnitary d) (i j : Fin d) :
    slaterVector (V * U) i j = (wedgeAction V).mulVec (slaterVector U i j) := by
  ext e
  exact columnMinor_mul V U i j e.val.1 e.val.2

theorem wedgeAction_mul {d : ℕ} (V U : PhysicalUnitary d) :
    wedgeAction (V * U) = wedgeAction V * wedgeAction U := by
  ext e f
  exact columnMinor_mul V U f.val.1 f.val.2 e.val.1 e.val.2

theorem wedgeAction_one (d : ℕ) : wedgeAction (1 : PhysicalUnitary d) = 1 := by
  classical
  ext e f
  rcases e with ⟨⟨a, b⟩, hab⟩
  rcases f with ⟨⟨c, k⟩, hck⟩
  simp only [wedgeAction, columnMinor, Matrix.UnitaryGroup.one_apply, Matrix.one_apply]
  dsimp only at hab hck ⊢
  by_cases hac : a = c <;> by_cases hbk : b = k <;>
    by_cases hak : a = k <;> by_cases hbc : b = c <;>
    simp_all [Subtype.ext_iff, Prod.ext_iff] <;> omega

theorem wedgeAction_inv {d : ℕ} (V : PhysicalUnitary d) :
    wedgeAction V⁻¹ = (wedgeAction V).conjTranspose := by
  ext e f
  simp only [wedgeAction, columnMinor, Matrix.UnitaryGroup.inv_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_sub, star_mul]
  ring

theorem wedgeAction_mem_unitary {d : ℕ} (V : PhysicalUnitary d) :
    wedgeAction V ∈ Matrix.unitaryGroup (Edge d) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [Matrix.star_eq_conjTranspose, ← wedgeAction_inv, ← wedgeAction_mul,
    inv_mul_cancel, wedgeAction_one]

def wedgeSquareAction {d : ℕ} (V : PhysicalUnitary d) :
    Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ :=
  wedgeAction V ⊗ₖ wedgeAction V

theorem wedgeSquareAction_mem_unitary {d : ℕ} (V : PhysicalUnitary d) :
    wedgeSquareAction V ∈ Matrix.unitaryGroup (Edge d × Edge d) ℂ :=
  Matrix.kronecker_mem_unitary (wedgeAction_mem_unitary V) (wedgeAction_mem_unitary V)

theorem slaterSquare_mul {d : ℕ} (V U : PhysicalUnitary d) (i j : Fin d) :
    slaterSquare (V * U) i j = (wedgeSquareAction V).mulVec (slaterSquare U i j) := by
  ext ef
  simp only [slaterSquare, slaterVector_mul, wedgeSquareAction, Matrix.mulVec,
    dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  ring

theorem slaterSquareDensity_mul {d : ℕ} (V U : PhysicalUnitary d) (i j : Fin d) :
    slaterSquareDensity (V * U) i j =
      wedgeSquareAction V * slaterSquareDensity U i j * (wedgeSquareAction V).conjTranspose := by
  simp only [slaterSquareDensity, pureDensity, slaterSquare_mul]
  exact (sandwich_crossDensity (wedgeSquareAction V)
    (slaterSquare U i j) (slaterSquare U i j)).symm

def matrixSandwichCLM {I : Type*} [Fintype I] (R : Matrix I I ℂ) :
    (I → I → ℂ) →L[ℂ] (I → I → ℂ) :=
  LinearMap.toContinuousLinearMap
    ((mulRightLinearMap I ℂ R.conjTranspose).comp (mulLeftLinearMap I ℂ R))

theorem matrixSandwichCLM_apply {I : Type*} [Fintype I] (R A : Matrix I I ℂ) :
    matrixSandwichCLM R A = R * A * R.conjTranspose := rfl

def physicalPermutation {d : ℕ} (σ : Equiv.Perm (Fin d)) : PhysicalUnitary d := by
  refine ⟨σ.permMatrix ℂ, Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
  rw [← Matrix.permMatrix_mul]
  simp

theorem physicalPermutation_mul_entry {d : ℕ} (σ : Equiv.Perm (Fin d))
    (U : PhysicalUnitary d) (a i : Fin d) :
    (physicalPermutation σ * U) a i = U (σ a) i := by
  change (σ.permMatrix ℂ * (U : Matrix (Fin d) (Fin d) ℂ)) a i = _
  exact congrFun (Matrix.permMatrix_mulVec σ (v := fun b => U b i)) a

theorem physicalPermutation_columnMinor {d : ℕ} (σ : Equiv.Perm (Fin d))
    (U : PhysicalUnitary d) (i j a b : Fin d) :
    columnMinor (physicalPermutation σ * U) i j a b =
      columnMinor U i j (σ a) (σ b) := by
  simp only [columnMinor, physicalPermutation_mul_entry]

theorem exists_physicalPermutation_pair {d : ℕ} (a b c f : Fin d)
    (hab : a ≠ b) (hcf : c ≠ f) :
    ∃ σ : Equiv.Perm (Fin d), σ a = c ∧ σ b = f := by
  have hcb : c ≠ (Equiv.swap a c) b := by
    intro h
    have h' : (Equiv.swap a c) a = (Equiv.swap a c) b := by
      simpa only [Equiv.swap_apply_left] using h
    exact hab ((Equiv.swap a c).injective h')
  refine ⟨Equiv.swap ((Equiv.swap a c) b) f * Equiv.swap a c, ?_, ?_⟩
  · change Equiv.swap ((Equiv.swap a c) b) f ((Equiv.swap a c) a) = c
    rw [Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hcb hcf
  · change Equiv.swap ((Equiv.swap a c) b) f ((Equiv.swap a c) b) = f
    exact Equiv.swap_apply_left _ _

def planeRotationColumn {d : ℕ} (a b k : Fin d) : Fin d → ℂ :=
  if k = a then (3 / 5 : ℂ) • Pi.single a 1 + (4 / 5 : ℂ) • Pi.single b 1
  else if k = b then (-4 / 5 : ℂ) • Pi.single a 1 + (3 / 5 : ℂ) • Pi.single b 1
  else Pi.single k 1

def planeRotationMatrix {d : ℕ} (a b : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  fun r k => planeRotationColumn a b k r

theorem planeRotationMatrix_mem_unitary {d : ℕ} (a b : Fin d) (hab : a ≠ b) :
    planeRotationMatrix a b ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  ext i j
  change (star (planeRotationColumn a b i) ⬝ᵥ planeRotationColumn a b j) =
    if i = j then 1 else 0
  by_cases hi : i = a <;> by_cases hi' : i = b <;>
    by_cases hj : j = a <;> by_cases hj' : j = b <;>
    simp_all [planeRotationColumn, star_add, star_smul, Pi.star_single,
      dotProduct_add, dotProduct_smul, Pi.single_apply, smul_eq_mul, eq_comm] <;> norm_num

def physicalPlaneRotation {d : ℕ} (a b : Fin d) (hab : a ≠ b) : PhysicalUnitary d :=
  ⟨planeRotationMatrix a b, planeRotationMatrix_mem_unitary a b hab⟩

theorem physicalPlaneRotation_column {d : ℕ} (a b : Fin d) (hab : a ≠ b) (k : Fin d) :
    (fun r => physicalPlaneRotation a b hab r k) = planeRotationColumn a b k := rfl

def exteriorCoordinates {d : ℕ} (u v : Fin d → ℂ) : Edge d → ℂ :=
  fun e => u e.val.1 * v e.val.2 - v e.val.1 * u e.val.2

def orderedWedge {d : ℕ} (a b : Fin d) : Edge d → ℂ :=
  exteriorCoordinates (Pi.single a 1) (Pi.single b 1)

theorem orderedWedge_swap {d : ℕ} (a b : Fin d) :
    orderedWedge b a = -orderedWedge a b := by
  ext e
  simp only [orderedWedge, exteriorCoordinates, Pi.neg_apply]
  ring

theorem orderedWedge_self {d : ℕ} (a : Fin d) : orderedWedge a a = 0 := by
  ext e
  simp [orderedWedge, exteriorCoordinates]

theorem orderedWedge_edge {d : ℕ} (e : Edge d) :
    orderedWedge e.val.1 e.val.2 = Pi.single e 1 := by
  classical
  ext f
  have h := congrArg (fun R : Matrix (Edge d) (Edge d) ℂ => R f e) (wedgeAction_one d)
  simpa [wedgeAction, columnMinor, orderedWedge, exteriorCoordinates,
    Matrix.one_apply, Pi.single_apply, eq_comm] using h

theorem slaterVector_one {d : ℕ} (a b : Fin d) :
    slaterVector (1 : PhysicalUnitary d) a b = orderedWedge a b := by
  ext e
  simp [slaterVector, columnMinor, orderedWedge, exteriorCoordinates,
    Matrix.one_apply, Pi.single_apply, eq_comm]

theorem wedgeAction_orderedWedge {d : ℕ} (V : PhysicalUnitary d) (a b : Fin d) :
    (wedgeAction V).mulVec (orderedWedge a b) =
      exteriorCoordinates (fun r => V r a) (fun r => V r b) := by
  have h := slaterVector_mul V (1 : PhysicalUnitary d) a b
  rw [mul_one, slaterVector_one] at h
  exact h.symm

theorem physicalPlaneRotation_wedge_first {d : ℕ} (a b : Fin d) (hab : a ≠ b)
    (k : Fin d) (hka : k ≠ a) (hkb : k ≠ b) :
    (wedgeAction (physicalPlaneRotation a b hab)).mulVec (orderedWedge a k) =
      (3 / 5 : ℂ) • orderedWedge a k + (4 / 5 : ℂ) • orderedWedge b k := by
  rw [wedgeAction_orderedWedge]
  change exteriorCoordinates (planeRotationColumn a b a) (planeRotationColumn a b k) = _
  simp [planeRotationColumn, hka, hkb]
  ext e
  simp only [exteriorCoordinates, orderedWedge, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem physicalPlaneRotation_wedge_second {d : ℕ} (a b : Fin d) (hab : a ≠ b)
    (k : Fin d) (hka : k ≠ a) (hkb : k ≠ b) :
    (wedgeAction (physicalPlaneRotation a b hab)).mulVec (orderedWedge b k) =
      (-4 / 5 : ℂ) • orderedWedge a k + (3 / 5 : ℂ) • orderedWedge b k := by
  rw [wedgeAction_orderedWedge]
  change exteriorCoordinates (planeRotationColumn a b b) (planeRotationColumn a b k) = _
  simp [planeRotationColumn, Ne.symm hab, hka, hkb]
  ext e
  simp only [exteriorCoordinates, orderedWedge, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem physicalPlaneRotation_wedge_fixed {d : ℕ} (a b : Fin d) (hab : a ≠ b)
    (k l : Fin d) (hka : k ≠ a) (hkb : k ≠ b) (hla : l ≠ a) (hlb : l ≠ b) :
    (wedgeAction (physicalPlaneRotation a b hab)).mulVec (orderedWedge k l) =
      orderedWedge k l := by
  rw [wedgeAction_orderedWedge]
  change exteriorCoordinates (planeRotationColumn a b k) (planeRotationColumn a b l) = _
  simp [planeRotationColumn, hka, hkb, hla, hlb, orderedWedge]

theorem physicalPlaneRotation_wedge_right_first {d : ℕ} (a b : Fin d) (hab : a ≠ b)
    (k : Fin d) (hka : k ≠ a) (hkb : k ≠ b) :
    (wedgeAction (physicalPlaneRotation a b hab)).mulVec (orderedWedge k a) =
      (3 / 5 : ℂ) • orderedWedge k a + (4 / 5 : ℂ) • orderedWedge k b := by
  rw [wedgeAction_orderedWedge]
  change exteriorCoordinates (planeRotationColumn a b k) (planeRotationColumn a b a) = _
  simp [planeRotationColumn, hka, hkb]
  ext e
  simp only [exteriorCoordinates, orderedWedge, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

def replicaProduct {d : ℕ} (u v : Edge d → ℂ) : Edge d × Edge d → ℂ :=
  fun ef => u ef.1 * v ef.2

def replicaSym {d : ℕ} (u v : Edge d → ℂ) : Edge d × Edge d → ℂ :=
  replicaProduct u v + replicaProduct v u

@[simp] theorem replicaProduct_zero_left {d : ℕ} (v : Edge d → ℂ) :
    replicaProduct 0 v = 0 := by
  ext ef
  simp [replicaProduct]

@[simp] theorem replicaProduct_zero_right {d : ℕ} (v : Edge d → ℂ) :
    replicaProduct v 0 = 0 := by
  ext ef
  simp [replicaProduct]

theorem replicaProduct_basis {d : ℕ} (e f : Edge d) :
    replicaProduct (Pi.single e 1) (Pi.single f 1) = Pi.single (e, f) 1 := by
  classical
  ext gh
  by_cases he : gh.1 = e <;> by_cases hf : gh.2 = f <;>
    simp [replicaProduct, Pi.single_apply, Prod.ext_iff, he, hf]

theorem replicaProduct_neg_neg {d : ℕ} (u v : Edge d → ℂ) :
    replicaProduct (-u) (-v) = replicaProduct u v := by
  ext ef
  simp [replicaProduct]

theorem replicaSym_swap {d : ℕ} (u v : Edge d → ℂ) : replicaSym v u = replicaSym u v :=
  add_comm _ _

theorem replicaSym_neg_left {d : ℕ} (u v : Edge d → ℂ) :
    replicaSym (-u) v = -replicaSym u v := by
  ext ef
  simp only [replicaSym, replicaProduct, Pi.add_apply, Pi.neg_apply]
  ring

theorem replicaSym_neg_neg {d : ℕ} (u v : Edge d → ℂ) :
    replicaSym (-u) (-v) = replicaSym u v := by
  simp only [replicaSym, replicaProduct_neg_neg]

theorem replicaSquare_expansion {d : ℕ} (u v : Edge d → ℂ) (c s : ℂ) :
    replicaProduct (c • u + s • v) (c • u + s • v) =
      (c * c) • replicaProduct u u + (s * s) • replicaProduct v v +
        (c * s) • replicaSym u v := by
  ext ef
  simp only [replicaProduct, replicaSym, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem wedgeSquareAction_replicaProduct {d : ℕ} (V : PhysicalUnitary d)
    (u v : Edge d → ℂ) :
    (wedgeSquareAction V).mulVec (replicaProduct u v) =
      replicaProduct ((wedgeAction V).mulVec u) ((wedgeAction V).mulVec v) := by
  ext ef
  simp only [replicaProduct, wedgeSquareAction, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  ring

theorem wedgeSquareAction_replicaSym {d : ℕ} (V : PhysicalUnitary d)
    (u v : Edge d → ℂ) :
    (wedgeSquareAction V).mulVec (replicaSym u v) =
      replicaSym ((wedgeAction V).mulVec u) ((wedgeAction V).mulVec v) := by
  simp only [replicaSym, Matrix.mulVec_add, wedgeSquareAction_replicaProduct]

theorem physicalPlaneRotation_replica_x_sub_t {d : ℕ} (a b c f : Fin d)
    (hac : a ≠ c) (hba : b ≠ a) (hbc : b ≠ c) (hfa : f ≠ a) (hfc : f ≠ c) :
    (wedgeSquareAction (physicalPlaneRotation a c hac)).mulVec
        (replicaSym (orderedWedge a b) (orderedWedge a f)) =
      (9 / 25 : ℂ) • replicaSym (orderedWedge a b) (orderedWedge a f) -
      (16 / 25 : ℂ) • replicaSym (orderedWedge b c) (orderedWedge c f) +
      (12 / 25 : ℂ) •
        (replicaSym (orderedWedge a b) (orderedWedge c f) -
          replicaSym (orderedWedge a f) (orderedWedge b c)) := by
  rw [wedgeSquareAction_replicaSym,
    physicalPlaneRotation_wedge_first a c hac b hba hbc,
    physicalPlaneRotation_wedge_first a c hac f hfa hfc,
    orderedWedge_swap c b]
  ext ef
  simp only [replicaSym, replicaProduct, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.neg_apply, smul_eq_mul]
  ring

theorem physicalPlaneRotation_replica_neg_x_add_y {d : ℕ} (a b c f : Fin d)
    (haf : a ≠ f) (hba : b ≠ a) (hbf : b ≠ f) (hca : c ≠ a) (hcf : c ≠ f) :
    (wedgeSquareAction (physicalPlaneRotation a f haf)).mulVec
        (replicaSym (orderedWedge a b) (orderedWedge a c)) =
      (9 / 25 : ℂ) • replicaSym (orderedWedge a b) (orderedWedge a c) +
      (16 / 25 : ℂ) • replicaSym (orderedWedge b f) (orderedWedge c f) -
      (12 / 25 : ℂ) •
        (replicaSym (orderedWedge a b) (orderedWedge c f) +
          replicaSym (orderedWedge a c) (orderedWedge b f)) := by
  rw [wedgeSquareAction_replicaSym,
    physicalPlaneRotation_wedge_first a f haf b hba hbf,
    physicalPlaneRotation_wedge_first a f haf c hca hcf,
    orderedWedge_swap f b, orderedWedge_swap f c]
  ext ef
  simp only [replicaSym, replicaProduct, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.neg_apply, smul_eq_mul]
  ring

theorem columnGram {d : ℕ} (U : PhysicalUnitary d) (i j : Fin d) :
    (∑ a : Fin d, star (U a i) * U a j) = if i = j then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) U.property.1
  simpa [Matrix.star_eq_conjTranspose, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply] using h

theorem columnNormSq {d : ℕ} (U : PhysicalUnitary d) (j : Fin d) :
    (∑ a : Fin d, Complex.normSq (U a j)) = 1 := by
  have h := congrArg Complex.re (columnGram U j j)
  simpa [Complex.star_def, mul_comm, Complex.mul_conj] using h

theorem columnMinor_normProduct {d : ℕ} (U : PhysicalUnitary d) (i j a b : Fin d) :
    columnMinor U i j a b * star (columnMinor U i j a b) =
      (star (U a i) * U a i) * (star (U b j) * U b j) +
      (star (U a j) * U a j) * (star (U b i) * U b i) -
      (star (U a j) * U a i) * (star (U b i) * U b j) -
      (star (U a i) * U a j) * (star (U b j) * U b i) := by
  simp only [columnMinor, star_sub, star_mul]
  ring

theorem columnMinor_full_normProduct {d : ℕ} (U : PhysicalUnitary d) (i j : Fin d)
    (hij : i ≠ j) :
    (∑ a : Fin d, ∑ b : Fin d,
      columnMinor U i j a b * star (columnMinor U i j a b)) = 2 := by
  simp_rw [columnMinor_normProduct, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, columnGram]
  norm_num [hij, Ne.symm hij]

theorem columnMinor_full_normSq {d : ℕ} (U : PhysicalUnitary d) (i j : Fin d)
    (hij : i ≠ j) :
    (∑ a : Fin d, ∑ b : Fin d, Complex.normSq (columnMinor U i j a b)) = 2 := by
  have h := congrArg Complex.re (columnMinor_full_normProduct U i j hij)
  simpa [Complex.star_def, Complex.mul_conj] using h

theorem columnMinor_edge_double {d : ℕ} (U : PhysicalUnitary d) (i j : Fin d) :
    (∑ a : Fin d, ∑ b : Fin d, Complex.normSq (columnMinor U i j a b)) =
      2 * vectorNormSq (slaterVector U i j) := by
  classical
  let f : Fin d × Fin d → ℝ := fun p => Complex.normSq (columnMinor U i j p.1 p.2)
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
        rw [columnMinor_swap U i j p.1 p.2, Complex.normSq_neg]
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
    · simp [f, h, columnMinor_self]
    · simp [h, not_lt_of_ge h.le]
  rw [hswap, hm] at hsplit
  simpa [Fintype.sum_prod_type, f, vectorNormSq, slaterVector, two_mul] using hsplit

theorem slaterVector_normSq {d : ℕ} (U : PhysicalUnitary d) (i j : Fin d)
    (hij : i ≠ j) : vectorNormSq (slaterVector U i j) = 1 := by
  have h := columnMinor_edge_double U i j
  rw [columnMinor_full_normSq U i j hij] at h
  linarith

theorem slaterSquare_normSq {d : ℕ} (U : PhysicalUnitary d) (i j : Fin d)
    (hij : i ≠ j) : vectorNormSq (slaterSquare U i j) = 1 := by
  simp only [vectorNormSq, slaterSquare, Fintype.sum_prod_type, Complex.normSq_mul,
    ← Finset.mul_sum, ← Finset.sum_mul]
  change vectorNormSq (slaterVector U i j) * vectorNormSq (slaterVector U i j) = 1
  rw [slaterVector_normSq U i j hij]
  norm_num

theorem slaterSquareDensity_trace {d : ℕ} (U : PhysicalUnitary d) (i j : Fin d)
    (hij : i ≠ j) : Matrix.trace (slaterSquareDensity U i j) = 1 := by
  rw [slaterSquareDensity, pureDensity_trace, slaterSquare_normSq U i j hij]
  norm_num

theorem fourFormOmega_slaterSquare_zero {d : ℕ} (U : PhysicalUnitary d) (i j : Fin d)
    (S : FourSet d) :
    star (fourFormOmega S) ⬝ᵥ slaterSquare U i j = 0 := by
  classical
  let a := (S.val.orderEmbOfFin S.property) (0 : Fin 4)
  let b := (S.val.orderEmbOfFin S.property) (1 : Fin 4)
  let c := (S.val.orderEmbOfFin S.property) (2 : Fin 4)
  let f := (S.val.orderEmbOfFin S.property) (3 : Fin 4)
  have hp := columnMinor_plucker U i j a b c f
  simp only [fourFormOmega, star_add, star_sub, Pi.star_single, star_one,
    add_dotProduct, sub_dotProduct, single_dotProduct, one_mul,
    slaterSquare, slaterVector, fourSetEdge]
  dsimp [a, b, c, f] at hp
  linear_combination 2 * hp

theorem entry_norm_le_one {d : ℕ} (U : PhysicalUnitary d) (a j : Fin d) :
    ‖U a j‖ ≤ 1 := by
  have hle : Complex.normSq (U a j) ≤ ∑ b : Fin d, Complex.normSq (U b j) :=
    Finset.single_le_sum (fun b _ => Complex.normSq_nonneg (U b j)) (Finset.mem_univ a)
  rw [columnNormSq U j, Complex.normSq_eq_norm_sq] at hle
  nlinarith [norm_nonneg (U a j)]

theorem unitary_isCompact (d : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) := by
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset isClosed_unitary
  intro U hU a j
  simpa [Metric.mem_closedBall, dist_zero_right] using entry_norm_le_one ⟨U, hU⟩ a j

instance physicalUnitary_compactSpace (d : ℕ) : CompactSpace (PhysicalUnitary d) :=
  isCompact_iff_compactSpace.mp (unitary_isCompact d)

def unitaryUniverse (d : ℕ) : PositiveCompacts (PhysicalUnitary d) where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simp

def normalizedHaar (d : ℕ) : Measure (PhysicalUnitary d) :=
  Measure.haarMeasure (unitaryUniverse d)

instance normalizedHaar_isHaarMeasure (d : ℕ) : (normalizedHaar d).IsHaarMeasure := by
  dsimp [normalizedHaar]
  infer_instance

instance normalizedHaar_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (normalizedHaar d) where
  measure_univ := by
    exact Measure.haarMeasure_self (K₀ := unitaryUniverse d)

theorem normalizedHaar_univ (d : ℕ) : normalizedHaar d Set.univ = 1 :=
  measure_univ

def edgeReplicaSwap (d : ℕ) : Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ :=
  fun ef gh => if gh = (ef.2, ef.1) then 1 else 0

def positiveSector (d : ℕ) : Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ :=
  (1 / 2 : ℂ) • (1 + edgeReplicaSwap d) -
    (pairWedgeInclusion d).conjTranspose * fourAntisymmetrizer d * pairWedgeInclusion d

theorem slaterSquare_swap {d : ℕ} (U : PhysicalUnitary d) (i j : Fin d)
    (ef : Edge d × Edge d) :
    slaterSquare U i j (ef.2, ef.1) = slaterSquare U i j ef := by
  simp [slaterSquare, mul_comm]

theorem columnMinor_continuous {d : ℕ} (i j a b : Fin d) :
    Continuous (fun U : PhysicalUnitary d => columnMinor U i j a b) := by
  exact ((continuous_subtype_val.matrix_elem a i).mul
    (continuous_subtype_val.matrix_elem b j)).sub
      ((continuous_subtype_val.matrix_elem a j).mul
        (continuous_subtype_val.matrix_elem b i))

theorem slaterSquareDensity_continuous {d : ℕ} (i j : Fin d) :
    Continuous (fun U : PhysicalUnitary d => slaterSquareDensity U i j) := by
  apply continuous_matrix
  intro ef gh
  exact ((columnMinor_continuous i j ef.1.val.1 ef.1.val.2).mul
      (columnMinor_continuous i j ef.2.val.1 ef.2.val.2)).mul
    (((columnMinor_continuous i j gh.1.val.1 gh.1.val.2).mul
      (columnMinor_continuous i j gh.2.val.1 gh.2.val.2)).star)

theorem slaterSquareDensity_integrable {d : ℕ} (i j : Fin d) :
    Integrable (fun U : PhysicalUnitary d => slaterSquareDensity U i j) (normalizedHaar d) := by
  have hint := (slaterSquareDensity_continuous i j).continuousOn.integrableOn_compact
    (μ := normalizedHaar d) isCompact_univ
  refine ⟨(slaterSquareDensity_continuous i j).aestronglyMeasurable, ?_⟩
  simpa only [Measure.restrict_univ] using hint.2

theorem slaterSquareDensity_entry_integrable {d : ℕ} (i j : Fin d)
    (ef gh : Edge d × Edge d) :
    Integrable (fun U : PhysicalUnitary d => slaterSquareDensity U i j ef gh)
      (normalizedHaar d) := by
  have hc : Continuous (fun U : PhysicalUnitary d => slaterSquareDensity U i j ef gh) := by
    exact (slaterSquareDensity_continuous i j).matrix_elem ef gh
  simpa [MeasureTheory.IntegrableOn] using hc.continuousOn.integrableOn_compact
    (μ := normalizedHaar d) isCompact_univ

theorem slaterSquareDensity_function_integrable {d : ℕ} (i j : Fin d) :
    Integrable
      (fun U : PhysicalUnitary d =>
        (fun ef gh : Edge d × Edge d => slaterSquareDensity U i j ef gh))
      (normalizedHaar d) := by
  have hc : Continuous
      (fun U : PhysicalUnitary d =>
        (fun ef gh : Edge d × Edge d => slaterSquareDensity U i j ef gh)) :=
    continuous_pi fun ef => continuous_pi fun gh =>
      (slaterSquareDensity_continuous i j).matrix_elem ef gh
  simpa [MeasureTheory.IntegrableOn] using hc.continuousOn.integrableOn_compact
    (μ := normalizedHaar d) isCompact_univ

def slaterMoment {d : ℕ} (i j : Fin d) : Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ :=
  ∫ U : PhysicalUnitary d, slaterSquareDensity U i j ∂normalizedHaar d

theorem slaterMoment_entry {d : ℕ} (i j : Fin d) (ef gh : Edge d × Edge d) :
    slaterMoment i j ef gh =
      ∫ U : PhysicalUnitary d, slaterSquareDensity U i j ef gh ∂normalizedHaar d := by
  let L : ((Edge d × Edge d) → (Edge d × Edge d) → ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj gh : ((Edge d × Edge d) → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj ef :
        ((Edge d × Edge d) → (Edge d × Edge d) → ℂ) →L[ℂ] ((Edge d × Edge d) → ℂ))
  exact (L.integral_comp_comm (slaterSquareDensity_function_integrable i j)).symm

theorem slaterMoment_trace {d : ℕ} (i j : Fin d) (hij : i ≠ j) :
    Matrix.trace (slaterMoment i j) = 1 := by
  simp only [Matrix.trace, Matrix.diag, slaterMoment_entry]
  rw [← integral_finsetSum]
  · have ht : (fun U : PhysicalUnitary d => ∑ ef : Edge d × Edge d,
        slaterSquareDensity U i j ef ef) = fun _ => (1 : ℂ) := by
      funext U
      exact slaterSquareDensity_trace U i j hij
    rw [ht]
    simp
  · intro ef _
    exact slaterSquareDensity_entry_integrable i j ef ef

def columnZero (d : ℕ) (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩

def columnOne (d : ℕ) (hd : 2 ≤ d) : Fin d := ⟨1, by omega⟩

theorem firstColumns_ne (d : ℕ) (hd : 2 ≤ d) : columnZero d hd ≠ columnOne d hd := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [columnZero, columnOne] at hv

def normalizedSlaterMoment (d : ℕ) (hd : 2 ≤ d) :=
  slaterMoment (columnZero d hd) (columnOne d hd)

theorem normalizedSlaterMoment_trace (d : ℕ) (hd : 2 ≤ d) :
    Matrix.trace (normalizedSlaterMoment d hd) = 1 :=
  slaterMoment_trace _ _ (firstColumns_ne d hd)

theorem slaterMoment_leftInvariant {d : ℕ} (i j : Fin d) (V : PhysicalUnitary d) :
    (∫ U : PhysicalUnitary d, slaterSquareDensity (V * U) i j ∂normalizedHaar d) =
      slaterMoment i j := by
  exact integral_mul_left_eq_self (μ := normalizedHaar d)
    (fun U : PhysicalUnitary d => slaterSquareDensity U i j) V

theorem slaterMoment_swap_left {d : ℕ} (i j : Fin d) (ef gh : Edge d × Edge d) :
    slaterMoment i j (ef.2, ef.1) gh = slaterMoment i j ef gh := by
  rw [slaterMoment_entry, slaterMoment_entry]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun U => by
    simp only [slaterSquareDensity, pureDensity, crossDensity, slaterSquare_swap]

theorem fourFormOmega_slaterMoment_zero {d : ℕ} (i j : Fin d) (S : FourSet d)
    (gh : Edge d × Edge d) :
    star (fourFormOmega S) ⬝ᵥ (fun ef => slaterMoment i j ef gh) = 0 := by
  unfold dotProduct
  simp only [Pi.star_apply]
  simp_rw [slaterMoment_entry, ← integral_const_mul]
  rw [← integral_finsetSum]
  · have hz : (fun U : PhysicalUnitary d =>
        ∑ ef : Edge d × Edge d, star (fourFormOmega S ef) *
          slaterSquareDensity U i j ef gh) = fun _ => (0 : ℂ) := by
      funext U
      have hp := fourFormOmega_slaterSquare_zero U i j S
      change (∑ ef : Edge d × Edge d, star (fourFormOmega S ef) *
        slaterSquare U i j ef) = 0 at hp
      simp only [slaterSquareDensity, pureDensity, crossDensity, ← mul_assoc,
        ← Finset.sum_mul, hp, zero_mul]
    rw [hz]
    simp
  · intro ef _
    exact (slaterSquareDensity_entry_integrable i j ef gh).const_mul _

def physicalPhase {d : ℕ} (z : Fin d → ℂ)
    (hz : ∀ a, star (z a) * z a = 1) : PhysicalUnitary d := by
  refine ⟨Matrix.diagonal z, Matrix.mem_unitaryGroup_iff'.mpr ?_⟩
  simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases hab : a = b
  · subst b
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    change star (z a) * z a = 1
    exact hz a
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]

theorem physicalPhase_mul_entry {d : ℕ} (z : Fin d → ℂ)
    (hz : ∀ a, star (z a) * z a = 1) (U : PhysicalUnitary d) (a i : Fin d) :
    (physicalPhase z hz * U) a i = z a * U a i := by
  simp [physicalPhase, Matrix.mul_apply, Matrix.diagonal]

theorem physicalPhase_columnMinor {d : ℕ} (z : Fin d → ℂ)
    (hz : ∀ a, star (z a) * z a = 1) (U : PhysicalUnitary d) (i j a b : Fin d) :
    columnMinor (physicalPhase z hz * U) i j a b =
      (z a * z b) * columnMinor U i j a b := by
  simp only [columnMinor, physicalPhase_mul_entry]
  ring

def phaseCharacter {d : ℕ} (z : Fin d → ℂ) (ef : Edge d × Edge d) : ℂ :=
  z ef.1.val.1 * z ef.1.val.2 * z ef.2.val.1 * z ef.2.val.2

theorem physicalPhase_slaterSquare {d : ℕ} (z : Fin d → ℂ)
    (hz : ∀ a, star (z a) * z a = 1) (U : PhysicalUnitary d) (i j : Fin d)
    (ef : Edge d × Edge d) :
    slaterSquare (physicalPhase z hz * U) i j ef =
      phaseCharacter z ef * slaterSquare U i j ef := by
  simp only [slaterSquare, slaterVector, physicalPhase_columnMinor, phaseCharacter]
  ring

theorem physicalPhase_density_entry {d : ℕ} (z : Fin d → ℂ)
    (hz : ∀ a, star (z a) * z a = 1) (U : PhysicalUnitary d) (i j : Fin d)
    (ef gh : Edge d × Edge d) :
    slaterSquareDensity (physicalPhase z hz * U) i j ef gh =
      (phaseCharacter z ef * star (phaseCharacter z gh)) *
        slaterSquareDensity U i j ef gh := by
  simp only [slaterSquareDensity, pureDensity, crossDensity, physicalPhase_slaterSquare,
    star_mul]
  ring

theorem slaterMoment_phase_entry {d : ℕ} (z : Fin d → ℂ)
    (hz : ∀ a, star (z a) * z a = 1) (i j : Fin d) (ef gh : Edge d × Edge d) :
    (phaseCharacter z ef * star (phaseCharacter z gh)) * slaterMoment i j ef gh =
      slaterMoment i j ef gh := by
  have h := integral_mul_left_eq_self (μ := normalizedHaar d)
    (fun U : PhysicalUnitary d => slaterSquareDensity U i j ef gh) (physicalPhase z hz)
  simp_rw [physicalPhase_density_entry, integral_const_mul] at h
  simpa only [slaterMoment_entry] using h

theorem slaterMoment_entry_eq_zero_of_phase {d : ℕ} (z : Fin d → ℂ)
    (hz : ∀ a, star (z a) * z a = 1) (i j : Fin d) (ef gh : Edge d × Edge d)
    (hsep : phaseCharacter z ef * star (phaseCharacter z gh) ≠ 1) :
    slaterMoment i j ef gh = 0 := by
  have h := slaterMoment_phase_entry z hz i j ef gh
  have hm : (phaseCharacter z ef * star (phaseCharacter z gh) - 1) *
      slaterMoment i j ef gh = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hsep)

def edgeMultiplicity {d : ℕ} (e : Edge d) (a : Fin d) : ℕ :=
  (if e.val.1 = a then 1 else 0) + (if e.val.2 = a then 1 else 0)

theorem edgeMultiplicity_le_one {d : ℕ} (e : Edge d) (a : Fin d) :
    edgeMultiplicity e a ≤ 1 := by
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  by_cases h₁ : e.val.1 = a
  · have h₂ : e.val.2 ≠ a := fun h₂ => hne (h₁.trans h₂.symm)
    simp [edgeMultiplicity, h₁, h₂]
  · by_cases h₂ : e.val.2 = a <;> simp [edgeMultiplicity, h₁, h₂]

def weightMultiplicity {d : ℕ} (ef : Edge d × Edge d) (a : Fin d) : ℕ :=
  edgeMultiplicity ef.1 a + edgeMultiplicity ef.2 a

theorem weightMultiplicity_le_two {d : ℕ} (ef : Edge d × Edge d) (a : Fin d) :
    weightMultiplicity ef a ≤ 2 := by
  have h₁ := edgeMultiplicity_le_one ef.1 a
  have h₂ := edgeMultiplicity_le_one ef.2 a
  dsimp [weightMultiplicity]
  omega

theorem edgeMultiplicity_pos_iff {d : ℕ} (e : Edge d) (a : Fin d) :
    0 < edgeMultiplicity e a ↔ e.val.1 = a ∨ e.val.2 = a := by
  by_cases h₁ : e.val.1 = a <;> by_cases h₂ : e.val.2 = a <;>
    simp [edgeMultiplicity, h₁, h₂]

theorem edge_eq_of_coordinate_support {d : ℕ} (f e : Edge d)
    (h₁ : e.val.1 = f.val.1 ∨ e.val.2 = f.val.1)
    (h₂ : e.val.1 = f.val.2 ∨ e.val.2 = f.val.2) : f = e := by
  have hf := f.property
  have he := e.property
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · omega
  · apply Subtype.ext
    exact Prod.ext h₁.symm h₂.symm
  · omega
  · omega

theorem weight_eq_square_rigid {d : ℕ} (ef : Edge d × Edge d) (e : Edge d)
    (h : ∀ a : Fin d, weightMultiplicity ef a = weightMultiplicity (e, e) a) :
    ef = (e, e) := by
  have hs : ∀ f : Edge d, f = ef.1 ∨ f = ef.2 →
      ∀ a : Fin d, 0 < edgeMultiplicity f a → 0 < edgeMultiplicity e a := by
    intro f hf a ha
    have hw := h a
    dsimp [weightMultiplicity] at hw
    rcases hf with hf | hf <;> subst f <;> omega
  have h₁ : ef.1 = e := by
    apply edge_eq_of_coordinate_support
    · apply (edgeMultiplicity_pos_iff e ef.1.val.1).mp
      exact hs ef.1 (Or.inl rfl) _ ((edgeMultiplicity_pos_iff _ _).mpr (Or.inl rfl))
    · apply (edgeMultiplicity_pos_iff e ef.1.val.2).mp
      exact hs ef.1 (Or.inl rfl) _ ((edgeMultiplicity_pos_iff _ _).mpr (Or.inr rfl))
  have h₂ : ef.2 = e := by
    apply edge_eq_of_coordinate_support
    · apply (edgeMultiplicity_pos_iff e ef.2.val.1).mp
      exact hs ef.2 (Or.inr rfl) _ ((edgeMultiplicity_pos_iff _ _).mpr (Or.inl rfl))
    · apply (edgeMultiplicity_pos_iff e ef.2.val.2).mp
      exact hs ef.2 (Or.inr rfl) _ ((edgeMultiplicity_pos_iff _ _).mpr (Or.inr rfl))
  exact Prod.ext h₁ h₂

def coordinatePhase {d : ℕ} (a : Fin d) (b : Fin d) : ℂ := if b = a then Complex.I else 1

theorem coordinatePhase_unitary {d : ℕ} (a b : Fin d) :
    star (coordinatePhase a b) * coordinatePhase a b = 1 := by
  by_cases h : b = a
  · simp [coordinatePhase, h, Complex.I_mul_I]
  · simp [coordinatePhase, h]

theorem coordinatePhase_edge_character {d : ℕ} (a : Fin d) (e : Edge d) :
    coordinatePhase a e.val.1 * coordinatePhase a e.val.2 =
      Complex.I ^ edgeMultiplicity e a := by
  simp only [edgeMultiplicity, pow_add]
  by_cases h₁ : e.val.1 = a <;> by_cases h₂ : e.val.2 = a <;>
    simp [coordinatePhase, h₁, h₂]

theorem coordinatePhase_character {d : ℕ} (a : Fin d) (ef : Edge d × Edge d) :
    phaseCharacter (coordinatePhase a) ef = Complex.I ^ weightMultiplicity ef a := by
  calc
    _ = (coordinatePhase a ef.1.val.1 * coordinatePhase a ef.1.val.2) *
        (coordinatePhase a ef.2.val.1 * coordinatePhase a ef.2.val.2) := by
      unfold phaseCharacter
      ring
    _ = Complex.I ^ edgeMultiplicity ef.1 a * Complex.I ^ edgeMultiplicity ef.2 a := by
      rw [coordinatePhase_edge_character, coordinatePhase_edge_character]
    _ = _ := by rw [← pow_add]; rfl

theorem I_pow_injective_le_two {m n : ℕ} (hm : m ≤ 2) (hn : n ≤ 2)
    (h : Complex.I ^ m = Complex.I ^ n) : m = n := by
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  have hn' : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hm' with hm' | hm' | hm' <;> rcases hn' with hn' | hn' | hn' <;>
    subst m <;> subst n
  all_goals try rfl
  all_goals
    have hre := congrArg Complex.re h
    norm_num [pow_succ, Complex.I_mul_I] at hre

theorem phaseCharacter_star_mul_self {d : ℕ} (z : Fin d → ℂ)
    (hz : ∀ a, star (z a) * z a = 1) (ef : Edge d × Edge d) :
    star (phaseCharacter z ef) * phaseCharacter z ef = 1 := by
  calc
    _ = (star (z ef.1.val.1) * z ef.1.val.1) *
        (star (z ef.1.val.2) * z ef.1.val.2) *
        (star (z ef.2.val.1) * z ef.2.val.1) *
        (star (z ef.2.val.2) * z ef.2.val.2) := by
      simp only [phaseCharacter, star_mul]
      ring
    _ = _ := by simp only [hz, mul_one]

theorem slaterMoment_entry_eq_zero_of_weight {d : ℕ} (i j a : Fin d)
    (ef gh : Edge d × Edge d) (hmul : weightMultiplicity ef a ≠ weightMultiplicity gh a) :
    slaterMoment i j ef gh = 0 := by
  have hne : phaseCharacter (coordinatePhase a) ef ≠ phaseCharacter (coordinatePhase a) gh := by
    intro h
    rw [coordinatePhase_character, coordinatePhase_character] at h
    exact hmul (I_pow_injective_le_two (weightMultiplicity_le_two ef a)
      (weightMultiplicity_le_two gh a) h)
  apply slaterMoment_entry_eq_zero_of_phase (coordinatePhase a) (coordinatePhase_unitary a)
    i j ef gh
  intro h
  have heq := congrArg (fun c : ℂ => c * phaseCharacter (coordinatePhase a) gh) h
  rw [mul_assoc, phaseCharacter_star_mul_self _ (coordinatePhase_unitary a),
    mul_one, one_mul] at heq
  exact hne heq

theorem slaterMoment_square_eigenvector {d : ℕ} (i j : Fin d) (e : Edge d) :
    (slaterMoment i j).mulVec (Pi.single (e, e) 1) =
      slaterMoment i j (e, e) (e, e) • Pi.single (e, e) 1 := by
  classical
  rw [Matrix.mulVec_single_one]
  ext ef
  by_cases hef : ef = (e, e)
  · subst ef
    simp
  · have hw : ∃ a : Fin d, weightMultiplicity ef a ≠ weightMultiplicity (e, e) a := by
      by_contra hh
      push Not at hh
      exact hef (weight_eq_square_rigid ef e hh)
    obtain ⟨a, ha⟩ := hw
    have hz := slaterMoment_entry_eq_zero_of_weight i j a ef (e, e) ha
    simp [hef, hz]

theorem slaterMoment_square_diagonal_eq {d : ℕ} (i j : Fin d) (e f : Edge d) :
    slaterMoment i j (e, e) (e, e) = slaterMoment i j (f, f) (f, f) := by
  obtain ⟨σ, ha, hb⟩ := exists_physicalPermutation_pair e.val.1 e.val.2 f.val.1 f.val.2
    (ne_of_lt e.property) (ne_of_lt f.property)
  have hp : ∀ U : PhysicalUnitary d,
      slaterSquareDensity (physicalPermutation σ * U) i j (e, e) (e, e) =
        slaterSquareDensity U i j (f, f) (f, f) := by
    intro U
    simp only [slaterSquareDensity_entry, slaterVector, physicalPermutation_columnMinor, ha, hb]
  have h := integral_mul_left_eq_self (μ := normalizedHaar d)
    (fun U : PhysicalUnitary d => slaterSquareDensity U i j (e, e) (e, e))
    (physicalPermutation σ)
  simp_rw [hp] at h
  simpa only [slaterMoment_entry] using h.symm

theorem slaterMoment_square_eigenvector_common {d : ℕ} (i j : Fin d) (e f : Edge d) :
    (slaterMoment i j).mulVec (Pi.single (f, f) 1) =
      slaterMoment i j (e, e) (e, e) • Pi.single (f, f) 1 := by
  rw [slaterMoment_square_eigenvector, slaterMoment_square_diagonal_eq i j f e]

theorem slaterMoment_covariance {d : ℕ} (i j : Fin d) (V : PhysicalUnitary d) :
    wedgeSquareAction V * slaterMoment i j * (wedgeSquareAction V).conjTranspose =
      slaterMoment i j := by
  have hi := (matrixSandwichCLM (wedgeSquareAction V)).integral_comp_comm
    (slaterSquareDensity_function_integrable i j)
  have hi' : wedgeSquareAction V * slaterMoment i j *
      (wedgeSquareAction V).conjTranspose = ∫ U : PhysicalUnitary d,
        wedgeSquareAction V * slaterSquareDensity U i j * (wedgeSquareAction V).conjTranspose
        ∂normalizedHaar d := hi.symm
  simp_rw [← slaterSquareDensity_mul] at hi'
  exact hi'.trans (slaterMoment_leftInvariant i j V)

theorem slaterMoment_commutes {d : ℕ} (i j : Fin d) (V : PhysicalUnitary d) :
    wedgeSquareAction V * slaterMoment i j = slaterMoment i j * wedgeSquareAction V := by
  have hr : (wedgeSquareAction V).conjTranspose * wedgeSquareAction V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (wedgeSquareAction_mem_unitary V).1
  have h := congrArg (fun A : Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ =>
    A * wedgeSquareAction V) (slaterMoment_covariance i j V)
  simpa only [Matrix.mul_assoc, hr, Matrix.mul_one] using h

theorem slaterMoment_rotated_square_eigenvector {d : ℕ} (i j : Fin d) (V : PhysicalUnitary d)
    (e f : Edge d) :
    (slaterMoment i j).mulVec ((wedgeSquareAction V).mulVec (Pi.single (f, f) 1)) =
      slaterMoment i j (e, e) (e, e) •
        (wedgeSquareAction V).mulVec (Pi.single (f, f) 1) := by
  rw [Matrix.mulVec_mulVec, ← slaterMoment_commutes, ← Matrix.mulVec_mulVec,
    slaterMoment_square_eigenvector_common i j e f, Matrix.mulVec_smul]

def momentEigenspace {d : ℕ} (i j : Fin d) (e : Edge d) :
    Submodule ℂ (Edge d × Edge d → ℂ) :=
  Module.End.eigenspace (Matrix.mulVecLin (slaterMoment i j)) (slaterMoment i j (e, e) (e, e))

theorem momentEigenspace_mem {d : ℕ} (i j : Fin d) (e : Edge d)
    (v : Edge d × Edge d → ℂ) :
    v ∈ momentEigenspace i j e ↔ (slaterMoment i j).mulVec v =
      slaterMoment i j (e, e) (e, e) • v :=
  Module.End.mem_eigenspace_iff

theorem momentEigenspace_square {d : ℕ} (i j : Fin d) (e f : Edge d) :
    Pi.single (f, f) 1 ∈ momentEigenspace i j e :=
  (momentEigenspace_mem i j e _).mpr (slaterMoment_square_eigenvector_common i j e f)

theorem momentEigenspace_rotated {d : ℕ} (i j : Fin d) (e : Edge d)
    (V : PhysicalUnitary d) (v : Edge d × Edge d → ℂ)
    (hv : v ∈ momentEigenspace i j e) :
    (wedgeSquareAction V).mulVec v ∈ momentEigenspace i j e := by
  rw [momentEigenspace_mem] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← slaterMoment_commutes, ← Matrix.mulVec_mulVec,
    hv, Matrix.mulVec_smul]

theorem momentEigenspace_ordered_square {d : ℕ} (i j : Fin d) (e : Edge d) (a b : Fin d) :
    replicaProduct (orderedWedge a b) (orderedWedge a b) ∈ momentEigenspace i j e := by
  by_cases hab : a = b
  · subst b
    simp [orderedWedge_self]
  rcases lt_or_gt_of_ne hab with h | h
  · let f : Edge d := ⟨(a, b), h⟩
    have hw : orderedWedge a b = Pi.single f 1 := orderedWedge_edge f
    rw [hw, replicaProduct_basis]
    exact momentEigenspace_square i j e f
  · let f : Edge d := ⟨(b, a), h⟩
    have hw : orderedWedge a b = -Pi.single f 1 :=
      (orderedWedge_swap b a).trans (congrArg Neg.neg (orderedWedge_edge f))
    rw [hw, replicaProduct_neg_neg, replicaProduct_basis]
    exact momentEigenspace_square i j e f

theorem submodule_extract_scaled_sum {I : Type*} (S : Submodule ℂ (I → ℂ))
    {u v w : I → ℂ} {c s t : ℂ} (hu : u ∈ S) (hv : v ∈ S)
    (hsum : c • u + s • v + t • w ∈ S) (ht : t ≠ 0) : w ∈ S := by
  have hscaled : t • w ∈ S := by
    have h := S.sub_mem hsum (S.add_mem (S.smul_mem c hu) (S.smul_mem s hv))
    simpa only [add_sub_cancel_left] using h
  have h := S.smul_mem t⁻¹ hscaled
  simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using h

theorem momentEigenspace_common {d : ℕ} (i j : Fin d) (e : Edge d) (a b c : Fin d) :
    replicaSym (orderedWedge a b) (orderedWedge a c) ∈ momentEigenspace i j e := by
  by_cases hab : a = b
  · subst b
    simp [orderedWedge_self, replicaSym]
  by_cases hac : a = c
  · subst c
    simp [orderedWedge_self, replicaSym]
  by_cases hbc : b = c
  · subst c
    have h := (momentEigenspace i j e).smul_mem (2 : ℂ)
      (momentEigenspace_ordered_square i j e a b)
    convert h using 1
    ext ef
    simp [replicaSym, replicaProduct, two_mul]
  have h := momentEigenspace_rotated i j e (physicalPlaneRotation b c hbc)
    (replicaProduct (orderedWedge a b) (orderedWedge a b))
    (momentEigenspace_ordered_square i j e a b)
  rw [wedgeSquareAction_replicaProduct,
    physicalPlaneRotation_wedge_right_first b c hbc a hab hac, replicaSquare_expansion] at h
  exact submodule_extract_scaled_sum (momentEigenspace i j e)
    (momentEigenspace_ordered_square i j e a b)
    (momentEigenspace_ordered_square i j e a c) h (by norm_num)

theorem momentEigenspace_common_second {d : ℕ} (i j : Fin d) (e : Edge d)
    (a b c : Fin d) :
    replicaSym (orderedWedge a b) (orderedWedge b c) ∈ momentEigenspace i j e := by
  have h := momentEigenspace_common i j e b a c
  rw [orderedWedge_swap a b, replicaSym_neg_left] at h
  simpa only [neg_neg] using (momentEigenspace i j e).neg_mem h

theorem momentEigenspace_common_last {d : ℕ} (i j : Fin d) (e : Edge d)
    (a b c : Fin d) :
    replicaSym (orderedWedge a b) (orderedWedge c b) ∈ momentEigenspace i j e := by
  have h := momentEigenspace_common i j e b a c
  rw [orderedWedge_swap a b, orderedWedge_swap c b, replicaSym_neg_neg] at h
  exact h

theorem momentEigenspace_four_x_sub_t {d : ℕ} (i j : Fin d) (e : Edge d)
    (a b c f : Fin d) (hab : a < b) (hbc : b < c) (hcf : c < f) :
    replicaSym (orderedWedge a b) (orderedWedge c f) -
      replicaSym (orderedWedge a f) (orderedWedge b c) ∈ momentEigenspace i j e := by
  have h := momentEigenspace_rotated i j e (physicalPlaneRotation a c (by omega))
    (replicaSym (orderedWedge a b) (orderedWedge a f))
    (momentEigenspace_common i j e a b f)
  rw [physicalPlaneRotation_replica_x_sub_t a b c f
    (by omega) (by omega) (by omega) (by omega) (by omega)] at h
  have hsum : (9 / 25 : ℂ) • replicaSym (orderedWedge a b) (orderedWedge a f) +
      (-16 / 25 : ℂ) • replicaSym (orderedWedge b c) (orderedWedge c f) +
      (12 / 25 : ℂ) • (replicaSym (orderedWedge a b) (orderedWedge c f) -
        replicaSym (orderedWedge a f) (orderedWedge b c)) ∈ momentEigenspace i j e := by
    simpa only [sub_eq_add_neg, neg_div, neg_smul] using h
  exact submodule_extract_scaled_sum (momentEigenspace i j e)
    (momentEigenspace_common i j e a b f)
    (momentEigenspace_common_second i j e b c f) hsum (by norm_num)

theorem momentEigenspace_four_x_add_y {d : ℕ} (i j : Fin d) (e : Edge d)
    (a b c f : Fin d) (hab : a < b) (hbc : b < c) (hcf : c < f) :
    replicaSym (orderedWedge a b) (orderedWedge c f) +
      replicaSym (orderedWedge a c) (orderedWedge b f) ∈ momentEigenspace i j e := by
  have h := momentEigenspace_rotated i j e (physicalPlaneRotation a f (by omega))
    (replicaSym (orderedWedge a b) (orderedWedge a c))
    (momentEigenspace_common i j e a b c)
  rw [physicalPlaneRotation_replica_neg_x_add_y a b c f
    (by omega) (by omega) (by omega) (by omega) (by omega)] at h
  have hsum : (9 / 25 : ℂ) • replicaSym (orderedWedge a b) (orderedWedge a c) +
      (16 / 25 : ℂ) • replicaSym (orderedWedge b f) (orderedWedge c f) +
      (-12 / 25 : ℂ) • (replicaSym (orderedWedge a b) (orderedWedge c f) +
        replicaSym (orderedWedge a c) (orderedWedge b f)) ∈ momentEigenspace i j e := by
    simpa only [sub_eq_add_neg, neg_div, neg_smul] using h
  exact submodule_extract_scaled_sum (momentEigenspace i j e)
    (momentEigenspace_common i j e a b c)
    (momentEigenspace_common_last i j e b f c) hsum (by norm_num)

def elementaryPositiveGenerators (d : ℕ) : Set (Edge d × Edge d → ℂ) :=
  {v | (∃ a b : Fin d, v = replicaProduct (orderedWedge a b) (orderedWedge a b)) ∨
    (∃ a b c : Fin d, v = replicaSym (orderedWedge a b) (orderedWedge a c)) ∨
    (∃ a b c f : Fin d, a < b ∧ b < c ∧ c < f ∧
      (v = replicaSym (orderedWedge a b) (orderedWedge c f) -
        replicaSym (orderedWedge a f) (orderedWedge b c) ∨
       v = replicaSym (orderedWedge a b) (orderedWedge c f) +
        replicaSym (orderedWedge a c) (orderedWedge b f)))}

def elementaryPositiveSpan (d : ℕ) : Submodule ℂ (Edge d × Edge d → ℂ) :=
  Submodule.span ℂ (elementaryPositiveGenerators d)

theorem elementaryPositiveSpan_le_momentEigenspace {d : ℕ} (i j : Fin d) (e : Edge d) :
    elementaryPositiveSpan d ≤ momentEigenspace i j e := by
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩ | ⟨a, b, c, f, hab, hbc, hcf, hv⟩
  · exact momentEigenspace_ordered_square i j e a b
  · exact momentEigenspace_common i j e a b c
  · rcases hv with rfl | rfl
    · exact momentEigenspace_four_x_sub_t i j e a b c f hab hbc hcf
    · exact momentEigenspace_four_x_add_y i j e a b c f hab hbc hcf

theorem slaterMoment_scalar_on_elementaryPositiveSpan {d : ℕ} (i j : Fin d) (e : Edge d)
    (v : Edge d × Edge d → ℂ) (hv : v ∈ elementaryPositiveSpan d) :
    (slaterMoment i j).mulVec v = slaterMoment i j (e, e) (e, e) • v :=
  (momentEigenspace_mem i j e v).mp (elementaryPositiveSpan_le_momentEigenspace i j e hv)

theorem four_coordinates_impossible {d : ℕ} (hd : d ≤ 3) (a b c f : Fin d)
    (hab : a < b) (hbc : b < c) (hcf : c < f) : False := by
  omega

theorem momentEigenspace_slaterSquare {d : ℕ} (i j : Fin d) (e : Edge d)
    (U : PhysicalUnitary d) : slaterSquare U i j ∈ momentEigenspace i j e := by
  have h := momentEigenspace_rotated i j e U
    (replicaProduct (orderedWedge i j) (orderedWedge i j))
    (momentEigenspace_ordered_square i j e i j)
  have hp : replicaProduct (orderedWedge i j) (orderedWedge i j) =
      slaterSquare (1 : PhysicalUnitary d) i j := by
    ext ef
    simp only [replicaProduct, slaterSquare, slaterVector_one]
  rw [hp, ← slaterSquare_mul, mul_one] at h
  exact h

def slaterSquareOrbitSpan {d : ℕ} (i j : Fin d) : Submodule ℂ (Edge d × Edge d → ℂ) :=
  Submodule.span ℂ {v | ∃ U : PhysicalUnitary d, v = slaterSquare U i j}

theorem slaterSquareOrbitSpan_le_momentEigenspace {d : ℕ} (i j : Fin d) (e : Edge d) :
    slaterSquareOrbitSpan i j ≤ momentEigenspace i j e := by
  apply Submodule.span_le.mpr
  rintro v ⟨U, rfl⟩
  exact momentEigenspace_slaterSquare i j e U

theorem slaterSquareDensity_fourFormOmega_mulVec_zero {d : ℕ} (U : PhysicalUnitary d)
    (i j : Fin d) (S : FourSet d) :
    (slaterSquareDensity U i j).mulVec (fourFormOmega S) = 0 := by
  have hz : (∑ gh : Edge d × Edge d,
      star (slaterSquare U i j gh) * fourFormOmega S gh) = 0 := by
    have h := congrArg star (fourFormOmega_slaterSquare_zero U i j S)
    simp only [dotProduct, Pi.star_apply, star_sum, star_mul, star_star, star_zero] at h
    exact h
  ext ef
  simp only [slaterSquareDensity, pureDensity, crossDensity, Matrix.mulVec, dotProduct]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hz, mul_zero]
  rfl

theorem slaterMoment_fourFormOmega_mulVec_zero {d : ℕ} (i j : Fin d) (S : FourSet d) :
    (slaterMoment i j).mulVec (fourFormOmega S) = 0 := by
  ext ef
  simp only [Matrix.mulVec, dotProduct, slaterMoment_entry]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum]
  · have hz : (fun U : PhysicalUnitary d => ∑ gh : Edge d × Edge d,
        slaterSquareDensity U i j ef gh * fourFormOmega S gh) = fun _ => (0 : ℂ) := by
      funext U
      exact congrFun (slaterSquareDensity_fourFormOmega_mulVec_zero U i j S) ef
    rw [hz]
    simp
  · intro gh _
    exact (slaterSquareDensity_entry_integrable i j ef gh).mul_const _

def fourFormSpan (d : ℕ) : Submodule ℂ (Edge d × Edge d → ℂ) :=
  Submodule.span ℂ (Set.range (fourFormOmega (d := d)))

theorem positive_mem_positive_sup_four {d : ℕ} {v : Edge d × Edge d → ℂ}
    (hv : v ∈ elementaryPositiveSpan d) :
    v ∈ elementaryPositiveSpan d ⊔ fourFormSpan d :=
  (show elementaryPositiveSpan d ≤ elementaryPositiveSpan d ⊔ fourFormSpan d from le_sup_left) hv

theorem four_mem_positive_sup_four {d : ℕ} {v : Edge d × Edge d → ℂ}
    (hv : v ∈ fourFormSpan d) :
    v ∈ elementaryPositiveSpan d ⊔ fourFormSpan d :=
  (show fourFormSpan d ≤ elementaryPositiveSpan d ⊔ fourFormSpan d from le_sup_right) hv

theorem elementaryPositiveSpan_square {d : ℕ} (a b : Fin d) :
    replicaProduct (orderedWedge a b) (orderedWedge a b) ∈ elementaryPositiveSpan d :=
  Submodule.subset_span (Or.inl ⟨a, b, rfl⟩)

theorem elementaryPositiveSpan_common {d : ℕ} (a b c : Fin d) :
    replicaSym (orderedWedge a b) (orderedWedge a c) ∈ elementaryPositiveSpan d :=
  Submodule.subset_span (Or.inr (Or.inl ⟨a, b, c, rfl⟩))

theorem elementaryPositiveSpan_common_second {d : ℕ} (a b c : Fin d) :
    replicaSym (orderedWedge a b) (orderedWedge b c) ∈ elementaryPositiveSpan d := by
  have h := elementaryPositiveSpan_common b a c
  rw [orderedWedge_swap a b, replicaSym_neg_left] at h
  simpa only [neg_neg] using (elementaryPositiveSpan d).neg_mem h

theorem elementaryPositiveSpan_common_last {d : ℕ} (a b c : Fin d) :
    replicaSym (orderedWedge a b) (orderedWedge c b) ∈ elementaryPositiveSpan d := by
  have h := elementaryPositiveSpan_common b a c
  rw [orderedWedge_swap a b, orderedWedge_swap c b, replicaSym_neg_neg] at h
  exact h

theorem elementaryPositiveSpan_four_x_sub_t {d : ℕ} (a b c f : Fin d)
    (hab : a < b) (hbc : b < c) (hcf : c < f) :
    replicaSym (orderedWedge a b) (orderedWedge c f) -
      replicaSym (orderedWedge a f) (orderedWedge b c) ∈ elementaryPositiveSpan d :=
  Submodule.subset_span (Or.inr (Or.inr ⟨a, b, c, f, hab, hbc, hcf, Or.inl rfl⟩))

theorem elementaryPositiveSpan_four_x_add_y {d : ℕ} (a b c f : Fin d)
    (hab : a < b) (hbc : b < c) (hcf : c < f) :
    replicaSym (orderedWedge a b) (orderedWedge c f) +
      replicaSym (orderedWedge a c) (orderedWedge b f) ∈ elementaryPositiveSpan d :=
  Submodule.subset_span (Or.inr (Or.inr ⟨a, b, c, f, hab, hbc, hcf, Or.inr rfl⟩))

theorem fourFormOmega_eq_replicaSym {d : ℕ} (S : FourSet d) :
    fourFormOmega S =
      replicaSym (orderedWedge ((S.val.orderEmbOfFin S.property) 0)
        ((S.val.orderEmbOfFin S.property) 1))
        (orderedWedge ((S.val.orderEmbOfFin S.property) 2) ((S.val.orderEmbOfFin S.property) 3)) -
      replicaSym (orderedWedge ((S.val.orderEmbOfFin S.property) 0)
        ((S.val.orderEmbOfFin S.property) 2))
        (orderedWedge ((S.val.orderEmbOfFin S.property) 1) ((S.val.orderEmbOfFin S.property) 3)) +
      replicaSym (orderedWedge ((S.val.orderEmbOfFin S.property) 0)
        ((S.val.orderEmbOfFin S.property) 3))
        (orderedWedge ((S.val.orderEmbOfFin S.property) 1) ((S.val.orderEmbOfFin S.property) 2)) := by
  have hw (i j : Fin 4) (hij : i < j) :
      orderedWedge ((S.val.orderEmbOfFin S.property) i) ((S.val.orderEmbOfFin S.property) j) =
        Pi.single (fourSetEdge S i j hij) 1 := orderedWedge_edge (fourSetEdge S i j hij)
  simp only [hw 0 1 (by decide), hw 0 2 (by decide), hw 0 3 (by decide),
    hw 1 2 (by decide), hw 1 3 (by decide), hw 2 3 (by decide),
    replicaSym, replicaProduct_basis, fourFormOmega]
  abel

def sortedFourSet {d : ℕ} (a b c f : Fin d) (hab : a < b) (hbc : b < c) (hcf : c < f) :
    FourSet d :=
  ⟨{a, b, c, f}, by
    simp [ne_of_lt hab, ne_of_lt hbc, ne_of_lt hcf,
      ne_of_lt (lt_trans hab hbc), ne_of_lt (lt_trans hbc hcf),
      ne_of_lt (lt_trans hab (lt_trans hbc hcf))]⟩

theorem sortedFourSet_omega {d : ℕ} (a b c f : Fin d)
    (hab : a < b) (hbc : b < c) (hcf : c < f) :
    fourFormOmega (sortedFourSet a b c f hab hbc hcf) =
      replicaSym (orderedWedge a b) (orderedWedge c f) -
      replicaSym (orderedWedge a c) (orderedWedge b f) +
      replicaSym (orderedWedge a f) (orderedWedge b c) := by
  let S := sortedFourSet a b c f hab hbc hcf
  let g : Fin 4 → Fin d := ![a, b, c, f]
  have hmem : ∀ k, g k ∈ S.val := by
    intro k
    fin_cases k <;> simp [g, S, sortedFourSet]
  have hmono : StrictMono g := by
    intro k l hkl
    fin_cases k <;> fin_cases l <;> simp_all [g] <;> omega
  have hg : g = S.val.orderEmbOfFin S.property :=
    Finset.orderEmbOfFin_unique S.property hmem hmono
  rw [fourFormOmega_eq_replicaSym, ← hg]
  simp [g]

theorem four_pairings_mem_positive_sup_four {d : ℕ} (a b c f : Fin d)
    (hab : a < b) (hbc : b < c) (hcf : c < f) :
    (replicaSym (orderedWedge a b) (orderedWedge c f) ∈
      elementaryPositiveSpan d ⊔ fourFormSpan d) ∧
    (replicaSym (orderedWedge a c) (orderedWedge b f) ∈
      elementaryPositiveSpan d ⊔ fourFormSpan d) ∧
    (replicaSym (orderedWedge a f) (orderedWedge b c) ∈
      elementaryPositiveSpan d ⊔ fourFormSpan d) := by
  let P := elementaryPositiveSpan d ⊔ fourFormSpan d
  have h0 : replicaSym (orderedWedge a b) (orderedWedge c f) -
      replicaSym (orderedWedge a f) (orderedWedge b c) ∈ P :=
    positive_mem_positive_sup_four (elementaryPositiveSpan_four_x_sub_t a b c f hab hbc hcf)
  have h1 : replicaSym (orderedWedge a b) (orderedWedge c f) +
      replicaSym (orderedWedge a c) (orderedWedge b f) ∈ P :=
    positive_mem_positive_sup_four (elementaryPositiveSpan_four_x_add_y a b c f hab hbc hcf)
  have h2 : fourFormOmega (sortedFourSet a b c f hab hbc hcf) ∈ P :=
    four_mem_positive_sup_four (Submodule.subset_span ⟨sortedFourSet a b c f hab hbc hcf, rfl⟩)
  refine ⟨?_, ?_, ?_⟩
  · have h := P.add_mem (P.add_mem (P.smul_mem (1 / 3 : ℂ) h0)
      (P.smul_mem (1 / 3 : ℂ) h1)) (P.smul_mem (1 / 3 : ℂ) h2)
    convert h using 1
    rw [sortedFourSet_omega]
    ext ef
    simp only [replicaSym, replicaProduct, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have h := P.add_mem (P.add_mem (P.smul_mem (-1 / 3 : ℂ) h0)
      (P.smul_mem (2 / 3 : ℂ) h1)) (P.smul_mem (-1 / 3 : ℂ) h2)
    convert h using 1
    rw [sortedFourSet_omega]
    ext ef
    simp only [replicaSym, replicaProduct, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · have h := P.add_mem (P.add_mem (P.smul_mem (-2 / 3 : ℂ) h0)
      (P.smul_mem (1 / 3 : ℂ) h1)) (P.smul_mem (1 / 3 : ℂ) h2)
    convert h using 1
    rw [sortedFourSet_omega]
    ext ef
    simp only [replicaSym, replicaProduct, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem replicaSym_basis_mem_positive_sup_four {d : ℕ} (e f : Edge d) :
    replicaSym (Pi.single e 1) (Pi.single f 1) ∈ elementaryPositiveSpan d ⊔ fourFormSpan d := by
  rw [← orderedWedge_edge e, ← orderedWedge_edge f]
  have hpart : ∀ a b c k : Fin d, a < b → c < k → a < c →
      replicaSym (orderedWedge a b) (orderedWedge c k) ∈
        elementaryPositiveSpan d ⊔ fourFormSpan d := by
    intro a b c k hab hck hac
    by_cases hbc : b = c
    · subst c
      exact positive_mem_positive_sup_four (elementaryPositiveSpan_common_second a b k)
    by_cases hbk : b = k
    · subst k
      exact positive_mem_positive_sup_four (elementaryPositiveSpan_common_last a b c)
    by_cases hbclt : b < c
    · exact (four_pairings_mem_positive_sup_four a b c k hab hbclt hck).1
    have hcb : c < b := by omega
    by_cases hbklt : b < k
    · exact (four_pairings_mem_positive_sup_four a c b k hac hcb hbklt).2.1
    have hkb : k < b := by omega
    exact (four_pairings_mem_positive_sup_four a c k b hac hck hkb).2.2
  by_cases heq : e.val.1 = f.val.1
  · rw [heq]
    exact positive_mem_positive_sup_four (elementaryPositiveSpan_common f.val.1 e.val.2 f.val.2)
  rcases lt_or_gt_of_ne heq with h | h
  · exact hpart e.val.1 e.val.2 f.val.1 f.val.2 e.property f.property h
  · rw [replicaSym_swap]
    exact hpart f.val.1 f.val.2 e.val.1 e.val.2 f.property e.property h

theorem symmetric_mem_positive_sup_four {d : ℕ} (v : Edge d × Edge d → ℂ)
    (hv : ∀ e f, v (e, f) = v (f, e)) :
    v ∈ elementaryPositiveSpan d ⊔ fourFormSpan d := by
  classical
  let P := elementaryPositiveSpan d ⊔ fourFormSpan d
  have hexp : v = (1 / 2 : ℂ) • ∑ ef : Edge d × Edge d,
      v ef • replicaSym (Pi.single ef.1 1) (Pi.single ef.2 1) := by
    ext gh
    simp only [Pi.smul_apply, Finset.sum_apply, replicaSym, replicaProduct_basis,
      Pi.add_apply, smul_eq_mul, Finset.sum_add_distrib, mul_add]
    simp [Pi.single_apply, Fintype.sum_prod_type, Prod.ext_iff, ite_and, mul_ite,
      eq_comm, hv]
    ring
  rw [hexp]
  apply P.smul_mem
  apply P.sum_mem
  intro ef _
  exact P.smul_mem (v ef) (replicaSym_basis_mem_positive_sup_four ef.1 ef.2)

theorem fourFormOmega_disjoint {d : ℕ} (S T : FourSet d) (hST : S ≠ T)
    (ef : Edge d × Edge d) : fourFormOmega S ef = 0 ∨ fourFormOmega T ef = 0 := by
  by_contra h
  push Not at h
  have hs := QuantumProver.WernerEndpoint.D5SupportFactor.fourFormOmega_support S ef h.1
  have ht := QuantumProver.WernerEndpoint.D5SupportFactor.fourFormOmega_support T ef h.2
  exact hST (Subtype.ext (hs.symm.trans ht))

theorem fourFormOmega_gram {d : ℕ} (S T : FourSet d) :
    star (fourFormOmega S) ⬝ᵥ fourFormOmega T = if S = T then (6 : ℂ) else 0 := by
  classical
  by_cases h : S = T
  · subst T
    simp only [ite_true]
    have hs : star (fourFormOmega S) ⬝ᵥ fourFormOmega S =
        Complex.ofReal (vectorNormSq (fourFormOmega S)) := by
      simp [dotProduct, vectorNormSq, mul_comm, Complex.mul_conj]
    rw [hs, QuantumProver.WernerEndpoint.D5SupportFactor.fourFormOmega_normSq]
    norm_num
  · simp only [h, ite_false, dotProduct, Pi.star_apply]
    apply Finset.sum_eq_zero
    intro ef _
    rcases fourFormOmega_disjoint S T h ef with hs | ht
    · simp [hs]
    · simp [ht]

def fourContractionLin {d : ℕ} (S : FourSet d) : (Edge d × Edge d → ℂ) →ₗ[ℂ] ℂ where
  toFun := fun v => star (fourFormOmega S) ⬝ᵥ v
  map_add' := fun u v => dotProduct_add (star (fourFormOmega S)) u v
  map_smul' := fun c v => dotProduct_smul c (star (fourFormOmega S)) v

def pluckerKernel (d : ℕ) : Submodule ℂ (Edge d × Edge d → ℂ) :=
  ⨅ S : FourSet d, LinearMap.ker (fourContractionLin S)

theorem pluckerKernel_mem {d : ℕ} (v : Edge d × Edge d → ℂ) :
    v ∈ pluckerKernel d ↔ ∀ S : FourSet d, star (fourFormOmega S) ⬝ᵥ v = 0 := by
  simp [pluckerKernel, fourContractionLin]

theorem fourFormSpan_plucker_zero {d : ℕ} (w : Edge d × Edge d → ℂ)
    (hw : w ∈ fourFormSpan d) (hp : w ∈ pluckerKernel d) : w = 0 := by
  classical
  rw [pluckerKernel_mem] at hp
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw
  have hz : ∀ S : FourSet d, c S = 0 := by
    intro S
    have h := congrArg (fun v : Edge d × Edge d → ℂ => star (fourFormOmega S) ⬝ᵥ v) hc
    rw [hp S] at h
    simp only [dotProduct_sum, dotProduct_smul, smul_eq_mul, fourFormOmega_gram] at h
    have h' : c S * 6 = 0 := by simpa [mul_ite, eq_comm] using h
    exact (mul_eq_zero.mp h').resolve_right (by norm_num)
  rw [← hc]
  simp [hz]

def allSlaterSquareSpan (d : ℕ) : Submodule ℂ (Edge d × Edge d → ℂ) :=
  Submodule.span ℂ {v | ∃ U : PhysicalUnitary d, ∃ i j : Fin d, v = slaterSquare U i j}

theorem allSlaterSquareSpan_ordered_square {d : ℕ} (a b : Fin d) :
    replicaProduct (orderedWedge a b) (orderedWedge a b) ∈ allSlaterSquareSpan d := by
  have h : slaterSquare (1 : PhysicalUnitary d) a b ∈ allSlaterSquareSpan d :=
    Submodule.subset_span ⟨1, a, b, rfl⟩
  convert h using 1
  ext ef
  simp only [replicaProduct, slaterSquare, slaterVector_one]

theorem allSlaterSquareSpan_rotated {d : ℕ} (V : PhysicalUnitary d)
    (v : Edge d × Edge d → ℂ) (hv : v ∈ allSlaterSquareSpan d) :
    (wedgeSquareAction V).mulVec v ∈ allSlaterSquareSpan d := by
  have hinv : allSlaterSquareSpan d ≤
      (allSlaterSquareSpan d).comap (Matrix.mulVecLin (wedgeSquareAction V)) := by
    apply Submodule.span_le.mpr
    rintro w ⟨U, i, j, rfl⟩
    change (wedgeSquareAction V).mulVec (slaterSquare U i j) ∈ allSlaterSquareSpan d
    rw [← slaterSquare_mul]
    exact Submodule.subset_span ⟨V * U, i, j, rfl⟩
  exact hinv hv

theorem allSlaterSquareSpan_common {d : ℕ} (a b c : Fin d) :
    replicaSym (orderedWedge a b) (orderedWedge a c) ∈ allSlaterSquareSpan d := by
  by_cases hab : a = b
  · subst b
    simp [orderedWedge_self, replicaSym]
  by_cases hac : a = c
  · subst c
    simp [orderedWedge_self, replicaSym]
  by_cases hbc : b = c
  · subst c
    have h := (allSlaterSquareSpan d).smul_mem (2 : ℂ)
      (allSlaterSquareSpan_ordered_square a b)
    convert h using 1
    ext ef
    simp [replicaSym, replicaProduct, two_mul]
  have h := allSlaterSquareSpan_rotated (physicalPlaneRotation b c hbc)
    (replicaProduct (orderedWedge a b) (orderedWedge a b))
    (allSlaterSquareSpan_ordered_square a b)
  rw [wedgeSquareAction_replicaProduct,
    physicalPlaneRotation_wedge_right_first b c hbc a hab hac, replicaSquare_expansion] at h
  exact submodule_extract_scaled_sum (allSlaterSquareSpan d)
    (allSlaterSquareSpan_ordered_square a b)
    (allSlaterSquareSpan_ordered_square a c) h (by norm_num)

theorem allSlaterSquareSpan_common_second {d : ℕ} (a b c : Fin d) :
    replicaSym (orderedWedge a b) (orderedWedge b c) ∈ allSlaterSquareSpan d := by
  have h := allSlaterSquareSpan_common b a c
  rw [orderedWedge_swap a b, replicaSym_neg_left] at h
  simpa only [neg_neg] using (allSlaterSquareSpan d).neg_mem h

theorem allSlaterSquareSpan_common_last {d : ℕ} (a b c : Fin d) :
    replicaSym (orderedWedge a b) (orderedWedge c b) ∈ allSlaterSquareSpan d := by
  have h := allSlaterSquareSpan_common b a c
  rw [orderedWedge_swap a b, orderedWedge_swap c b, replicaSym_neg_neg] at h
  exact h

theorem allSlaterSquareSpan_four_x_sub_t {d : ℕ}
    (a b c f : Fin d) (hab : a < b) (hbc : b < c) (hcf : c < f) :
    replicaSym (orderedWedge a b) (orderedWedge c f) -
      replicaSym (orderedWedge a f) (orderedWedge b c) ∈ allSlaterSquareSpan d := by
  have h := allSlaterSquareSpan_rotated (physicalPlaneRotation a c (by omega))
    (replicaSym (orderedWedge a b) (orderedWedge a f))
    (allSlaterSquareSpan_common a b f)
  rw [physicalPlaneRotation_replica_x_sub_t a b c f
    (by omega) (by omega) (by omega) (by omega) (by omega)] at h
  have hsum : (9 / 25 : ℂ) • replicaSym (orderedWedge a b) (orderedWedge a f) +
      (-16 / 25 : ℂ) • replicaSym (orderedWedge b c) (orderedWedge c f) +
      (12 / 25 : ℂ) • (replicaSym (orderedWedge a b) (orderedWedge c f) -
        replicaSym (orderedWedge a f) (orderedWedge b c)) ∈ allSlaterSquareSpan d := by
    simpa only [sub_eq_add_neg, neg_div, neg_smul] using h
  exact submodule_extract_scaled_sum (allSlaterSquareSpan d)
    (allSlaterSquareSpan_common a b f)
    (allSlaterSquareSpan_common_second b c f) hsum (by norm_num)

theorem allSlaterSquareSpan_four_x_add_y {d : ℕ}
    (a b c f : Fin d) (hab : a < b) (hbc : b < c) (hcf : c < f) :
    replicaSym (orderedWedge a b) (orderedWedge c f) +
      replicaSym (orderedWedge a c) (orderedWedge b f) ∈ allSlaterSquareSpan d := by
  have h := allSlaterSquareSpan_rotated (physicalPlaneRotation a f (by omega))
    (replicaSym (orderedWedge a b) (orderedWedge a c))
    (allSlaterSquareSpan_common a b c)
  rw [physicalPlaneRotation_replica_neg_x_add_y a b c f
    (by omega) (by omega) (by omega) (by omega) (by omega)] at h
  have hsum : (9 / 25 : ℂ) • replicaSym (orderedWedge a b) (orderedWedge a c) +
      (16 / 25 : ℂ) • replicaSym (orderedWedge b f) (orderedWedge c f) +
      (-12 / 25 : ℂ) • (replicaSym (orderedWedge a b) (orderedWedge c f) +
        replicaSym (orderedWedge a c) (orderedWedge b f)) ∈ allSlaterSquareSpan d := by
    simpa only [sub_eq_add_neg, neg_div, neg_smul] using h
  exact submodule_extract_scaled_sum (allSlaterSquareSpan d)
    (allSlaterSquareSpan_common a b c)
    (allSlaterSquareSpan_common_last b f c) hsum (by norm_num)

theorem elementaryPositiveSpan_le_allSlaterSquareSpan (d : ℕ) :
    elementaryPositiveSpan d ≤ allSlaterSquareSpan d := by
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩ | ⟨a, b, c, f, hab, hbc, hcf, hv⟩
  · exact allSlaterSquareSpan_ordered_square a b
  · exact allSlaterSquareSpan_common a b c
  · rcases hv with rfl | rfl
    · exact allSlaterSquareSpan_four_x_sub_t a b c f hab hbc hcf
    · exact allSlaterSquareSpan_four_x_add_y a b c f hab hbc hcf

theorem allSlaterSquareSpan_le_pluckerKernel (d : ℕ) :
    allSlaterSquareSpan d ≤ pluckerKernel d := by
  apply Submodule.span_le.mpr
  rintro v ⟨U, i, j, rfl⟩
  change slaterSquare U i j ∈ pluckerKernel d
  rw [pluckerKernel_mem]
  exact fourFormOmega_slaterSquare_zero U i j

def symmetricReplicaSubmodule (d : ℕ) : Submodule ℂ (Edge d × Edge d → ℂ) where
  carrier := {v | ∀ e f, v (e, f) = v (f, e)}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv e f
    exact congrArg₂ (· + ·) (hu e f) (hv e f)
  smul_mem' := by
    intro c v hv e f
    exact congrArg (fun z : ℂ => c • z) (hv e f)

theorem allSlaterSquareSpan_le_symmetric (d : ℕ) :
    allSlaterSquareSpan d ≤ symmetricReplicaSubmodule d := by
  apply Submodule.span_le.mpr
  rintro v ⟨U, i, j, rfl⟩ e f
  exact (slaterSquare_swap U i j (e, f)).symm

theorem elementaryPositiveSpan_eq_symmetric_plucker (d : ℕ) :
    elementaryPositiveSpan d = symmetricReplicaSubmodule d ⊓ pluckerKernel d := by
  apply le_antisymm
  · exact le_inf
      ((elementaryPositiveSpan_le_allSlaterSquareSpan d).trans (allSlaterSquareSpan_le_symmetric d))
      ((elementaryPositiveSpan_le_allSlaterSquareSpan d).trans (allSlaterSquareSpan_le_pluckerKernel d))
  · intro v hv
    obtain ⟨u, hu, w, hw, hsum⟩ := Submodule.mem_sup.mp
      (symmetric_mem_positive_sup_four v hv.1)
    have hpu : u ∈ pluckerKernel d :=
      allSlaterSquareSpan_le_pluckerKernel d (elementaryPositiveSpan_le_allSlaterSquareSpan d hu)
    have hpw : w ∈ pluckerKernel d := by
      have h := (pluckerKernel d).sub_mem hv.2 hpu
      rw [← hsum] at h
      simpa only [add_sub_cancel_left] using h
    have hwzero := fourFormSpan_plucker_zero w hw hpw
    rw [hwzero, add_zero] at hsum
    simpa only [hsum] using hu

theorem slaterMoment_scalar_on_symmetric_plucker {d : ℕ} (i j : Fin d) (e : Edge d)
    (v : Edge d × Edge d → ℂ) (hs : ∀ f g, v (f, g) = v (g, f))
    (hp : ∀ S : FourSet d, star (fourFormOmega S) ⬝ᵥ v = 0) :
    (slaterMoment i j).mulVec v = slaterMoment i j (e, e) (e, e) • v := by
  apply slaterMoment_scalar_on_elementaryPositiveSpan
  rw [elementaryPositiveSpan_eq_symmetric_plucker]
  exact ⟨hs, (pluckerKernel_mem v).mpr hp⟩

theorem edgeReplicaSwap_mulVec {d : ℕ} (v : Edge d × Edge d → ℂ) :
    (edgeReplicaSwap d).mulVec v = fun ef => v (ef.2, ef.1) := by
  ext ef
  simp [edgeReplicaSwap, Matrix.mulVec, dotProduct]

theorem fourFormOmega_symmetric {d : ℕ} (S : FourSet d) (e f : Edge d) :
    fourFormOmega S (e, f) = fourFormOmega S (f, e) := by
  rw [fourFormOmega_eq_replicaSym]
  simp only [Pi.add_apply, Pi.sub_apply, replicaSym, replicaProduct]
  ring

theorem symmetric_dotProduct_swap {d : ℕ} (u v : Edge d × Edge d → ℂ)
    (hu : ∀ e f, u (e, f) = u (f, e)) :
    u ⬝ᵥ (fun ef => v (ef.2, ef.1)) = u ⬝ᵥ v := by
  classical
  simp only [dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  rw [hu f e]

theorem pureDensity_mulVec_literal {I : Type*} [Fintype I] (u v : I → ℂ) :
    (pureDensity u).mulVec v = (star u ⬝ᵥ v) • u := by
  ext a
  simp only [pureDensity, crossDensity, Matrix.mulVec, dotProduct,
    Pi.star_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum]
  ring

def coordinateFourProjector (d : ℕ) : Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ :=
  (1 / 6 : ℂ) • ∑ S : FourSet d, pureDensity (fourFormOmega S)

def coordinatePositiveProjector (d : ℕ) : Matrix (Edge d × Edge d) (Edge d × Edge d) ℂ :=
  (1 / 2 : ℂ) • (1 + edgeReplicaSwap d) - coordinateFourProjector d

theorem coordinateFourProjector_mulVec {d : ℕ} (v : Edge d × Edge d → ℂ) :
    (coordinateFourProjector d).mulVec v = (1 / 6 : ℂ) •
      ∑ S : FourSet d, (star (fourFormOmega S) ⬝ᵥ v) • fourFormOmega S := by
  rw [coordinateFourProjector, Matrix.smul_mulVec, Matrix.sum_mulVec]
  simp only [pureDensity_mulVec_literal]

theorem coordinatePositiveProjector_mulVec {d : ℕ} (v : Edge d × Edge d → ℂ) :
    (coordinatePositiveProjector d).mulVec v =
      (1 / 2 : ℂ) • (v + fun ef => v (ef.2, ef.1)) -
      (1 / 6 : ℂ) • ∑ S : FourSet d, (star (fourFormOmega S) ⬝ᵥ v) • fourFormOmega S := by
  rw [coordinatePositiveProjector, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.add_mulVec, Matrix.one_mulVec, edgeReplicaSwap_mulVec, coordinateFourProjector_mulVec]

theorem coordinatePositiveProjector_range {d : ℕ} (v : Edge d × Edge d → ℂ) :
    (coordinatePositiveProjector d).mulVec v ∈ elementaryPositiveSpan d := by
  classical
  rw [elementaryPositiveSpan_eq_symmetric_plucker]
  refine ⟨?_, ?_⟩
  · rw [coordinatePositiveProjector_mulVec]
    have ha : v + (fun ef => v (ef.2, ef.1)) ∈ symmetricReplicaSubmodule d := by
      intro e f
      exact add_comm _ _
    have hb : (∑ S : FourSet d, (star (fourFormOmega S) ⬝ᵥ v) • fourFormOmega S) ∈
        symmetricReplicaSubmodule d := by
      apply (symmetricReplicaSubmodule d).sum_mem
      intro S _
      exact (symmetricReplicaSubmodule d).smul_mem _ (fourFormOmega_symmetric S)
    exact (symmetricReplicaSubmodule d).sub_mem
      ((symmetricReplicaSubmodule d).smul_mem _ ha)
      ((symmetricReplicaSubmodule d).smul_mem _ hb)
  · change (coordinatePositiveProjector d).mulVec v ∈ pluckerKernel d
    rw [pluckerKernel_mem, coordinatePositiveProjector_mulVec]
    intro S
    simp only [dotProduct_sub, dotProduct_smul, dotProduct_add, dotProduct_sum,
      smul_eq_mul, fourFormOmega_gram]
    rw [symmetric_dotProduct_swap (star (fourFormOmega S)) v
      (fun e f => congrArg star (fourFormOmega_symmetric S e f))]
    simp only [mul_ite, mul_zero]
    simp; ring

theorem coordinatePositiveProjector_fixes {d : ℕ} (v : Edge d × Edge d → ℂ)
    (hv : v ∈ elementaryPositiveSpan d) : (coordinatePositiveProjector d).mulVec v = v := by
  rw [elementaryPositiveSpan_eq_symmetric_plucker] at hv
  have hp := (pluckerKernel_mem v).mp hv.2
  rw [coordinatePositiveProjector_mulVec]
  simp only [hp, zero_smul, Finset.sum_const_zero, smul_zero, sub_zero]
  ext ef
  rcases ef with ⟨e, f⟩
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hv.1 e f]
  ring

theorem coordinatePositiveProjector_idempotent (d : ℕ) :
    coordinatePositiveProjector d * coordinatePositiveProjector d = coordinatePositiveProjector d := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← Matrix.mulVec_mulVec]
  exact coordinatePositiveProjector_fixes _ (coordinatePositiveProjector_range v)

theorem slaterMoment_swap_right {d : ℕ} (i j : Fin d) (ef gh : Edge d × Edge d) :
    slaterMoment i j ef (gh.2, gh.1) = slaterMoment i j ef gh := by
  rw [slaterMoment_entry, slaterMoment_entry]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun U => by
    simp only [slaterSquareDensity, pureDensity, crossDensity, slaterSquare_swap]

theorem slaterMoment_mulVec_swap {d : ℕ} (i j : Fin d) (v : Edge d × Edge d → ℂ) :
    (slaterMoment i j).mulVec (fun ef => v (ef.2, ef.1)) = (slaterMoment i j).mulVec v := by
  ext ef
  exact symmetric_dotProduct_swap (fun gh => slaterMoment i j ef gh) v
    (fun e f => (slaterMoment_swap_right i j ef (e, f)).symm)

theorem slaterMoment_coordinatePositiveProjector {d : ℕ} (i j : Fin d)
    (v : Edge d × Edge d → ℂ) :
    (slaterMoment i j).mulVec ((coordinatePositiveProjector d).mulVec v) =
      (slaterMoment i j).mulVec v := by
  rw [coordinatePositiveProjector_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_add, slaterMoment_mulVec_swap, Matrix.mulVec_smul, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, slaterMoment_fourFormOmega_mulVec_zero,
    smul_zero, Finset.sum_const_zero, sub_zero]
  ext ef
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem slaterMoment_eq_scalar_coordinatePositiveProjector {d : ℕ} (i j : Fin d) (e : Edge d) :
    slaterMoment i j = slaterMoment i j (e, e) (e, e) • coordinatePositiveProjector d := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [Matrix.smul_mulVec]
  exact (slaterMoment_coordinatePositiveProjector i j v).symm.trans
    (slaterMoment_scalar_on_elementaryPositiveSpan i j e _ (coordinatePositiveProjector_range v))

theorem slaterMoment_eq_inv_trace_coordinatePositiveProjector {d : ℕ} (i j : Fin d)
    (hij : i ≠ j) (e : Edge d) :
    slaterMoment i j = (Matrix.trace (coordinatePositiveProjector d))⁻¹ •
      coordinatePositiveProjector d := by
  have ht : slaterMoment i j (e, e) (e, e) * Matrix.trace (coordinatePositiveProjector d) = 1 := by
    have h := congrArg Matrix.trace (slaterMoment_eq_scalar_coordinatePositiveProjector i j e)
    rw [slaterMoment_trace i j hij, Matrix.trace_smul, smul_eq_mul] at h
    exact h.symm
  have hne : Matrix.trace (coordinatePositiveProjector d) ≠ 0 := by
    intro h
    simp [h] at ht
  have hscalar : slaterMoment i j (e, e) (e, e) = (Matrix.trace (coordinatePositiveProjector d))⁻¹ := by
    apply (mul_right_cancel₀ hne)
    rw [ht, inv_mul_cancel₀ hne]
  rw [slaterMoment_eq_scalar_coordinatePositiveProjector i j e, hscalar]

theorem normalizedSlaterMoment_eq_inv_trace_coordinatePositiveProjector (d : ℕ) (hd : 2 ≤ d) :
    normalizedSlaterMoment d hd = (Matrix.trace (coordinatePositiveProjector d))⁻¹ •
      coordinatePositiveProjector d := by
  let e : Edge d := ⟨(columnZero d hd, columnOne d hd), by change (0 : ℕ) < 1; omega⟩
  exact slaterMoment_eq_inv_trace_coordinatePositiveProjector _ _ (firstColumns_ne d hd) e

theorem edgeReplicaSwap_hermitian (d : ℕ) : (edgeReplicaSwap d).IsHermitian := by
  change (edgeReplicaSwap d).conjTranspose = edgeReplicaSwap d
  ext ef gh
  rcases ef with ⟨e, f⟩
  rcases gh with ⟨g, h⟩
  simp [Matrix.conjTranspose_apply, edgeReplicaSwap, Prod.ext_iff, eq_comm, and_comm]

theorem coordinateFourProjector_hermitian (d : ℕ) : (coordinateFourProjector d).IsHermitian := by
  have hs : (∑ S : FourSet d, pureDensity (fourFormOmega S)).IsHermitian :=
    isSelfAdjoint_sum Finset.univ (fun S _ => (pureDensity_posSemidef (fourFormOmega S)).isHermitian)
  exact hs.smul (by norm_num [isSelfAdjoint_iff])

theorem coordinatePositiveProjector_hermitian (d : ℕ) :
    (coordinatePositiveProjector d).IsHermitian := by
  exact (((Matrix.isHermitian_one).add (edgeReplicaSwap_hermitian d)).smul
    (by norm_num [isSelfAdjoint_iff])).sub (coordinateFourProjector_hermitian d)

theorem coordinatePositiveProjector_posSemidef (d : ℕ) :
    (coordinatePositiveProjector d).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (coordinatePositiveProjector d)
  rw [(coordinatePositiveProjector_hermitian d).eq, coordinatePositiveProjector_idempotent] at h
  exact h

theorem edgeReplicaSwap_trace (d : ℕ) :
    Matrix.trace (edgeReplicaSwap d) = (Fintype.card (Edge d) : ℂ) := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_prod_type]
  simp [edgeReplicaSwap, Prod.ext_iff, eq_comm]

theorem coordinatePositiveProjector_trace_card (d : ℕ) :
    Matrix.trace (coordinatePositiveProjector d) =
      (1 / 2 : ℂ) * (Fintype.card (Edge d) : ℂ) * ((Fintype.card (Edge d) : ℂ) + 1) -
      (Fintype.card (FourSet d) : ℂ) := by
  rw [coordinatePositiveProjector, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_one, edgeReplicaSwap_trace, coordinateFourProjector,
    Matrix.trace_smul, Matrix.trace_sum]
  simp_rw [pureDensity_trace, QuantumProver.WernerEndpoint.D5SupportFactor.fourFormOmega_normSq]
  simp only [Fintype.card_prod, Nat.cast_mul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, smul_eq_mul]
  norm_num
  ring

end QuantumProver.WernerEndpoint.SlaterMoments
