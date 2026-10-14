import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.InfiniteRecordReadout
import QuantumProver.InformationTheory.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Set Filter Function Preorder Finset
open scoped NNReal ENNReal Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM

abbrev Prefix (R : Type*) (n : ℕ) := (i : Finset.Iic n) → R
abbrev Transcript (R : Type*) := ℕ → R

variable {R : Type*} [MeasurableSpace R]

def prefixStepEquiv (n : ℕ) : Prefix R n × R ≃ᵐ Prefix R (n + 1) :=
  ((MeasurableEquiv.refl (Prefix R n)).prodCongr
    (MeasurableEquiv.piSingleton (X := fun _ => R) n)).trans
    (MeasurableEquiv.IicProdIoc (X := fun _ => R) (Nat.le_succ n))

theorem prefixStepEquiv_symm_fst (n : ℕ) :
    Prod.fst ∘ (prefixStepEquiv (R := R) n).symm =
      frestrictLe₂ (π := fun _ => R) (Nat.le_succ n) := by
  rfl

def nextPairMeasure (P : ∀ n, Measure (Prefix R n)) (n : ℕ) :
    Measure (Prefix R n × R) :=
  (P (n + 1)).map (prefixStepEquiv n).symm

instance nextPairMeasure_isProbability (P : ∀ n, Measure (Prefix R n))
    [∀ n, IsProbabilityMeasure (P n)] (n : ℕ) :
    IsProbabilityMeasure (nextPairMeasure P n) := by
  unfold nextPairMeasure
  infer_instance

variable [StandardBorelSpace R] [Nonempty R]

def transition (P : ∀ n, Measure (Prefix R n)) [∀ n, IsProbabilityMeasure (P n)]
    (n : ℕ) : Kernel (Prefix R n) R := (nextPairMeasure P n).condKernel

instance transition_isMarkov (P : ∀ n, Measure (Prefix R n))
    [∀ n, IsProbabilityMeasure (P n)] (n : ℕ) : IsMarkovKernel (transition P n) := by
  unfold transition
  infer_instance

theorem nextPairMeasure_fst (P : ∀ n, Measure (Prefix R n))
    (hP : ∀ a b (hab : a ≤ b), (P b).map (frestrictLe₂ (π := fun _ => R) hab) = P a)
    (n : ℕ) : (nextPairMeasure P n).fst = P n := by
  unfold nextPairMeasure Measure.fst
  rw [Measure.map_map measurable_fst (prefixStepEquiv n).symm.measurable]
  rw [prefixStepEquiv_symm_fst]
  exact hP n (n + 1) (Nat.le_succ n)

theorem partialTraj_step_gluing (P : ∀ n, Measure (Prefix R n))
    [∀ n, IsProbabilityMeasure (P n)] (n : ℕ) :
    Kernel.partialTraj (X := fun _ => R) (transition P) n (n + 1) =
      (Kernel.id ×ₖ transition P n).map (prefixStepEquiv n) := by
  rw [Kernel.partialTraj_succ_self]
  have hprod : Kernel.id ×ₖ (transition P n).map
      (MeasurableEquiv.piSingleton (X := fun _ => R) n) =
      (Kernel.id ×ₖ transition P n).map
        (Prod.map id (MeasurableEquiv.piSingleton (X := fun _ => R) n)) := by
    simpa using Kernel.map_prod_map (Kernel.id : Kernel (Prefix R n) (Prefix R n))
      (transition P n) measurable_id
      (MeasurableEquiv.piSingleton (X := fun _ => R) n).measurable
  rw [hprod]
  change ((Kernel.id ×ₖ transition P n).map
    (Prod.map id (MeasurableEquiv.piSingleton (X := fun _ => R) n))).map
    (MeasurableEquiv.IicProdIoc (X := fun _ => R) (Nat.le_succ n)) = _
  rw [← Kernel.map_comp_right _ (by fun_prop)
    (MeasurableEquiv.IicProdIoc (X := fun _ => R) (Nat.le_succ n)).measurable]
  rfl

theorem partialTraj_step_comp (P : ∀ n, Measure (Prefix R n))
    [∀ n, IsProbabilityMeasure (P n)]
    (hP : ∀ a b (hab : a ≤ b), (P b).map (frestrictLe₂ (π := fun _ => R) hab) = P a)
    (n : ℕ) : Kernel.partialTraj (X := fun _ => R) (transition P) n (n + 1) ∘ₘ P n = P (n + 1) := by
  rw [partialTraj_step_gluing]
  rw [← Measure.map_comp _ _ (prefixStepEquiv n).measurable,
    ← Measure.compProd_eq_comp_prod]
  rw [← nextPairMeasure_fst P hP n]
  change ((nextPairMeasure P n).fst ⊗ₘ (nextPairMeasure P n).condKernel).map
    (prefixStepEquiv n) = P (n + 1)
  rw [Measure.disintegrate]
  exact (prefixStepEquiv n).map_map_symm

theorem partialTraj_comp_initial (P : ∀ n, Measure (Prefix R n))
    [∀ n, IsProbabilityMeasure (P n)]
    (hP : ∀ a b (hab : a ≤ b), (P b).map (frestrictLe₂ (π := fun _ => R) hab) = P a)
    (n : ℕ) : Kernel.partialTraj (X := fun _ => R) (transition P) 0 n ∘ₘ P 0 = P n := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc, hn]
    exact partialTraj_step_comp P hP n

def probabilityExtension (P : ∀ n, Measure (Prefix R n))
    [∀ n, IsProbabilityMeasure (P n)] : Measure (Transcript R) :=
  Kernel.traj (X := fun _ => R) (transition P) 0 ∘ₘ P 0

instance probabilityExtension_isProbability (P : ∀ n, Measure (Prefix R n))
    [∀ n, IsProbabilityMeasure (P n)] : IsProbabilityMeasure (probabilityExtension P) := by
  unfold probabilityExtension
  infer_instance

theorem probabilityExtension_map_prefix (P : ∀ n, Measure (Prefix R n))
    [∀ n, IsProbabilityMeasure (P n)]
    (hP : ∀ a b (hab : a ≤ b), (P b).map (frestrictLe₂ (π := fun _ => R) hab) = P a)
    (n : ℕ) : (probabilityExtension P).map (frestrictLe (π := fun _ => R) n) = P n := by
  rw [probabilityExtension, Measure.map_comp _ _ (measurable_frestrictLe n),
    Kernel.traj_map_frestrictLe]
  exact partialTraj_comp_initial P hP n

theorem exists_probability_extension_of_consistent_prefixes
    (P : ∀ n, Measure (Prefix R n)) [∀ n, IsProbabilityMeasure (P n)]
    (hP : ∀ a b (hab : a ≤ b), (P b).map (frestrictLe₂ (π := fun _ => R) hab) = P a) :
    ∃ ν : Measure (Transcript R), IsProbabilityMeasure ν ∧
      ∀ n, ν.map (frestrictLe (π := fun _ => R) n) = P n :=
  ⟨probabilityExtension P, inferInstance, probabilityExtension_map_prefix P hP⟩

theorem prefix_extension_unique (P : ∀ n, Measure (Prefix R n))
    [∀ n, IsFiniteMeasure (P n)]
    (hP : ∀ a b (hab : a ≤ b), (P b).map (frestrictLe₂ (π := fun _ => R) hab) = P a)
    (ν η : Measure (Transcript R))
    (hν : ∀ n, ν.map (frestrictLe (π := fun _ => R) n) = P n)
    (hη : ∀ n, η.map (frestrictLe (π := fun _ => R) n) = P n) : ν = η := by
  have hp := isProjectiveMeasureFamily_inducedFamily (X := fun _ => R) P hP
  haveI : ∀ i, IsFiniteMeasure (inducedFamily (X := fun _ => R) P i) := by
    intro i
    unfold inducedFamily
    infer_instance
  apply IsProjectiveLimit.unique (P := inducedFamily (X := fun _ => R) P)
  · apply (isProjectiveLimit_nat_iff hp ν).2
    intro n
    rw [inducedFamily_Iic]
    exact hν n
  · apply (isProjectiveLimit_nat_iff hp η).2
    intro n
    rw [inducedFamily_Iic]
    exact hη n

theorem exists_finite_extension_of_consistent_prefixes
    (P : ∀ n, Measure (Prefix R n)) (c : ℝ≥0)
    (htotal : ∀ n, P n univ = c)
    (hP : ∀ a b (hab : a ≤ b), (P b).map (frestrictLe₂ (π := fun _ => R) hab) = P a) :
    ∃ ν : Measure (Transcript R), IsFiniteMeasure ν ∧ ν univ = c ∧
      ∀ n, ν.map (frestrictLe (π := fun _ => R) n) = P n := by
  classical
  by_cases hc : c = 0
  · have hzero : ∀ n, P n = 0 := by
      intro n
      apply Measure.measure_univ_eq_zero.mp
      simp [htotal, hc]
    exact ⟨0, inferInstance, by simp [hc], by simp [hzero]⟩
  · let Q : ∀ n, Measure (Prefix R n) := fun n => c⁻¹ • P n
    haveI : ∀ n, IsProbabilityMeasure (Q n) := by
      intro n
      constructor
      simp [Q, Measure.smul_apply, htotal, ENNReal.smul_def, ENNReal.coe_inv hc,
        ENNReal.inv_mul_cancel (by exact_mod_cast hc) ENNReal.coe_ne_top]
    have hQ : ∀ a b (hab : a ≤ b),
        (Q b).map (frestrictLe₂ (π := fun _ => R) hab) = Q a := by
      intro a b hab
      change (c⁻¹ • P b).map (frestrictLe₂ (π := fun _ => R) hab) = c⁻¹ • P a
      exact (Measure.map_smul (c⁻¹ : ℝ≥0) (μ := P b)
        (f := frestrictLe₂ (π := fun _ => R) hab)
        (measurable_frestrictLe₂ hab).aemeasurable).trans
        (congrArg (fun μ => c⁻¹ • μ) (hP a b hab))
    refine ⟨c • probabilityExtension Q, inferInstance, ?_, ?_⟩
    · simp [Measure.smul_apply]
    · intro n
      rw [Measure.map_smul c (measurable_frestrictLe n).aemeasurable,
        probabilityExtension_map_prefix Q hQ n]
      simp [Q, smul_smul, hc]

theorem vectorMeasure_eq_of_prefix {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    [T2Space M] (F G : VectorMeasure (Transcript R) M)
    (h : ∀ n (s : Set (Prefix R n)), MeasurableSet s →
      F ((frestrictLe (π := fun _ => R) n) ⁻¹' s) =
        G ((frestrictLe (π := fun _ => R) n) ⁻¹' s)) : F = G := by
  apply VectorMeasure.ext_of_generateFrom (measurableCylinders (fun _ : ℕ => R))
  · intro B hB
    rw [measurableCylinders_nat] at hB
    simp only [mem_iUnion, mem_singleton_iff] at hB
    obtain ⟨n, s, hs, rfl⟩ := hB
    exact h n s hs
  · exact generateFrom_measurableCylinders.symm
  · exact isPiSystem_measurableCylinders
  · simpa using h 0 univ MeasurableSet.univ

section Cylinders

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

def prefixFiltration : Filtration ℕ (inferInstance : MeasurableSpace (Transcript R)) where
  seq n := (inferInstance : MeasurableSpace (Prefix R n)).comap
    (frestrictLe (π := fun _ => R) n)
  mono' := by
    intro a b hab B hB
    obtain ⟨s, hs, h⟩ := MeasurableSpace.measurableSet_comap.mp hB
    apply MeasurableSpace.measurableSet_comap.mpr
    refine ⟨(frestrictLe₂ (π := fun _ => R) hab) ⁻¹' s,
      (measurable_frestrictLe₂ hab) hs, ?_⟩
    change (frestrictLe (π := fun _ => R) a) ⁻¹' s = B
    exact h
  le' n := (measurable_frestrictLe n).comap_le

theorem iSup_prefixFiltration :
    (⨆ n, prefixFiltration (R := R) n) =
      (inferInstance : MeasurableSpace (Transcript R)) := by
  apply le_antisymm (iSup_le fun n => (prefixFiltration (R := R)).le n)
  conv_lhs => rw [← generateFrom_measurableCylinders (α := fun _ : ℕ => R)]
  apply MeasurableSpace.generateFrom_le
  intro B hB
  rw [measurableCylinders_nat] at hB
  simp only [mem_iUnion, mem_singleton_iff] at hB
  obtain ⟨n, s, hs, rfl⟩ := hB
  apply (le_iSup (fun n => prefixFiltration (R := R) n) n)
  exact MeasurableSpace.measurableSet_comap.mpr ⟨s, hs, rfl⟩

namespace MatrixProbe

def quadratic (v : Q → ℂ) (A : Matrix Q Q ℂ) : ℝ :=
  (star v ⬝ᵥ (A *ᵥ v)).re

def basisVector (a : Q) : Q → ℂ := Pi.single a 1

def quadraticComplexLinear (v : Q → ℂ) : Matrix Q Q ℂ →ₗ[ℂ] ℂ where
  toFun A := star v ⬝ᵥ (A *ᵥ v)
  map_add' A B := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' c A := by simp [Matrix.smul_mulVec, dotProduct_smul]

def quadraticCLM (v : Q → ℂ) : Matrix Q Q ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp ((LinearMap.toContinuousLinearMap
    (quadraticComplexLinear v)).restrictScalars ℝ)

@[simp] theorem quadraticCLM_apply (v : Q → ℂ) (A : Matrix Q Q ℂ) :
    quadraticCLM v A = quadratic v A := rfl

theorem quadratic_nonneg (A : Matrix Q Q ℂ) (hA : A.PosSemidef) (v : Q → ℂ) :
    0 ≤ quadratic v A :=
  (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg v)).1

def polarizationEntry (f : (Q → ℂ) → ℝ) (a b : Q) : ℂ :=
  (((f (basisVector a + basisVector b) - f (basisVector a) - f (basisVector b)) / 2 : ℝ) : ℂ) +
    (((f (basisVector a) + f (basisVector b) -
      f (basisVector a + Complex.I • basisVector b)) / 2 : ℝ) : ℂ) * Complex.I

theorem polarization_quadratic (A : Matrix Q Q ℂ) (hA : A.IsHermitian) (a b : Q) :
    polarizationEntry (fun v => quadratic v A) a b = A a b := by
  have hba : A b a = star (A a b) := (hA.apply b a).symm
  simp only [polarizationEntry, quadratic, star_add, star_smul, Matrix.mulVec_add,
    Matrix.mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul]
  simp [basisVector, dotProduct, Matrix.mulVec, Pi.single_apply, hba]
  apply Complex.ext <;> simp <;> ring

theorem matrix_eq_sum_smul_single (A : Matrix Q Q ℂ) :
    A = ∑ a, ∑ b, A a b • Matrix.single a b 1 := by
  simpa using Matrix.matrix_eq_sum_single A

variable {X : Type*} [MeasurableSpace X]

def complexify (σ : SignedMeasure X) : VectorMeasure X ℂ :=
  VectorMeasure.mapRangeL Complex.ofRealCLM σ

@[simp] theorem complexify_apply (σ : SignedMeasure X) (B : Set X) :
    complexify σ B = (σ B : ℂ) := rfl

def polarizationEntryMeasure (σ : (Q → ℂ) → SignedMeasure X) (a b : Q) :
    VectorMeasure X ℂ :=
  complexify ((1 / 2 : ℝ) • (σ (basisVector a + basisVector b) -
    σ (basisVector a) - σ (basisVector b))) +
  Complex.I • complexify ((1 / 2 : ℝ) • (σ (basisVector a) +
    σ (basisVector b) - σ (basisVector a + Complex.I • basisVector b)))

theorem polarizationEntryMeasure_apply (σ : (Q → ℂ) → SignedMeasure X)
    (a b : Q) (B : Set X) :
    polarizationEntryMeasure σ a b B = polarizationEntry (fun v => σ v B) a b := by
  simp [polarizationEntryMeasure, polarizationEntry, complexify_apply,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

def matrixSingleCLM (a b : Q) : ℂ →L[ℂ] Matrix Q Q ℂ :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (Matrix.single a b 1)

def entryLinear (a b : Q) : Matrix Q Q ℂ →ₗ[ℂ] ℂ where
  toFun A := A a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def entryCLM (a b : Q) : Matrix Q Q ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (entryLinear a b)

@[simp] theorem entryCLM_apply (a b : Q) (A : Matrix Q Q ℂ) :
    entryCLM a b A = A a b := rfl

def polarizationMeasure (σ : (Q → ℂ) → SignedMeasure X) :
    VectorMeasure X (Matrix Q Q ℂ) :=
  ∑ a, ∑ b, VectorMeasure.mapRangeL (matrixSingleCLM a b)
    (polarizationEntryMeasure σ a b)

theorem polarizationMeasure_apply (σ : (Q → ℂ) → SignedMeasure X) (B : Set X) :
    polarizationMeasure σ B = fun a b => polarizationEntry (fun v => σ v B) a b := by
  simp only [polarizationMeasure, _root_.sum_apply]
  change (∑ a, ∑ b, matrixSingleCLM a b (polarizationEntryMeasure σ a b B)) = _
  simp only [matrixSingleCLM, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, polarizationEntryMeasure_apply]
  exact (matrix_eq_sum_smul_single
    (fun a b : Q => polarizationEntry (fun v => σ v B) a b)).symm

def conjTransposeRealLinear : Matrix Q Q ℂ →ₗ[ℝ] Matrix Q Q ℂ where
  toFun A := Aᴴ
  map_add' A B := Matrix.conjTranspose_add A B
  map_smul' r A := by
    ext a b
    simp [Matrix.conjTranspose_apply, smul_eq_mul]

def conjTransposeCLM : Matrix Q Q ℂ →L[ℝ] Matrix Q Q ℂ :=
  LinearMap.toContinuousLinearMap conjTransposeRealLinear

@[simp] theorem conjTransposeCLM_apply (A : Matrix Q Q ℂ) :
    conjTransposeCLM A = Aᴴ := rfl

def bornScalar (ρ A : Matrix Q Q ℂ) : ℝ := (A * ρ).trace.re

def bornComplexLinear (ρ : Matrix Q Q ℂ) : Matrix Q Q ℂ →ₗ[ℂ] ℂ where
  toFun A := (A * ρ).trace
  map_add' A B := by simp [Matrix.add_mul, Matrix.trace_add]
  map_smul' c A := by simp [Matrix.smul_mul, Matrix.trace_smul]

def bornCLM (ρ : Matrix Q Q ℂ) : Matrix Q Q ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp ((LinearMap.toContinuousLinearMap
    (bornComplexLinear ρ)).restrictScalars ℝ)

@[simp] theorem bornCLM_apply (ρ A : Matrix Q Q ℂ) :
    bornCLM ρ A = bornScalar ρ A := rfl

theorem bornScalar_nonneg (ρ A : Matrix Q Q ℂ) (hρ : ρ.PosSemidef)
    (hA : A.PosSemidef) : 0 ≤ bornScalar ρ A := by
  have hS : (CFC.sqrt ρ)ᴴ = CFC.sqrt ρ :=
    (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
  have hT := hA.mul_mul_conjTranspose_same (CFC.sqrt ρ)
  have ht : (CFC.sqrt ρ * A * (CFC.sqrt ρ)ᴴ).trace = (A * ρ).trace := by
    rw [hS, Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg,
      Matrix.trace_mul_comm]
  exact (Complex.nonneg_iff.mp (ht ▸ hT.trace_nonneg)).1

theorem density_le_one (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) : ρ ≤ 1 := by
  have hn : ‖ρ‖ ≤ 1 := by
    simpa [htrace] using QuantumProver.ElegantJointMeasurement.InfiniteRecordReadout.posSemidef_norm_le_trace ρ hρ
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg ρ hρ.nonneg).mp hn

theorem bornScalar_le_trace (ρ A : Matrix Q Q ℂ) (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) (hA : A.PosSemidef) : bornScalar ρ A ≤ A.trace.re := by
  have hdiff : (1 - ρ).PosSemidef :=
    (sub_nonneg.mpr (density_le_one ρ hρ htrace)).posSemidef
  have hb := bornScalar_nonneg (1 - ρ) A hdiff hA
  simp only [bornScalar, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re] at hb
  unfold bornScalar
  linarith

end MatrixProbe

open MatrixProbe

structure ConsistentCylinderPOVM (R Q : Type*) [MeasurableSpace R]
    [Fintype Q] [DecidableEq Q] where
  effect : ∀ n, Set (Prefix R n) → Matrix Q Q ℂ
  empty : ∀ n, effect n ∅ = 0
  positive : ∀ n s, MeasurableSet s → (effect n s).PosSemidef
  total : ∀ n, effect n univ = 1
  coordinate_additive : ∀ n (s : ℕ → Set (Prefix R n)),
    (∀ k, MeasurableSet (s k)) → Pairwise (fun i j => Disjoint (s i) (s j)) → ∀ a b,
      HasSum (fun k => effect n (s k) a b) (effect n (⋃ k, s k) a b)
  consistent : ∀ a b (hab : a ≤ b) s, MeasurableSet s →
    effect b ((frestrictLe₂ (π := fun _ => R) hab) ⁻¹' s) = effect a s

namespace ConsistentCylinderPOVM

variable (C : ConsistentCylinderPOVM R Q)

theorem matrix_additive (n : ℕ) (s : ℕ → Set (Prefix R n))
    (hs : ∀ k, MeasurableSet (s k))
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j))) :
    HasSum (fun k => C.effect n (s k)) (C.effect n (⋃ k, s k)) := by
  have hb := hasSum_sum (s := Finset.univ) (fun a _ =>
    hasSum_sum (s := Finset.univ) (fun b _ =>
      (C.coordinate_additive n s hs hdisj a b).smul_const (Matrix.single a b (1 : ℂ))))
  simpa only [← matrix_eq_sum_smul_single] using hb

def prefixProbe (v : Q → ℂ) (n : ℕ) : Measure (Prefix R n) :=
  Measure.ofMeasurable (fun s _ => ENNReal.ofReal (quadratic v (C.effect n s)))
    (by simp [C.empty, quadratic])
    (fun s hs hdisj => by
      have hsum := (quadraticCLM v).hasSum (C.matrix_additive n s hs hdisj)
      simp only [quadraticCLM_apply] at hsum
      rw [← hsum.tsum_eq]
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun k => quadratic_nonneg _ (C.positive n (s k) (hs k)) v) hsum.summable)

theorem prefixProbe_apply (v : Q → ℂ) (n : ℕ) (s : Set (Prefix R n))
    (hs : MeasurableSet s) :
    C.prefixProbe v n s = ENNReal.ofReal (quadratic v (C.effect n s)) :=
  Measure.ofMeasurable_apply s hs

def probeMass (v : Q → ℂ) : ℝ≥0 := (quadratic v (1 : Matrix Q Q ℂ)).toNNReal

theorem prefixProbe_total (v : Q → ℂ) (n : ℕ) :
    C.prefixProbe v n univ = probeMass v := by
  rw [C.prefixProbe_apply v n univ MeasurableSet.univ, C.total]
  rfl

theorem prefixProbe_consistent (v : Q → ℂ) (a b : ℕ) (hab : a ≤ b) :
    (C.prefixProbe v b).map (frestrictLe₂ (π := fun _ => R) hab) = C.prefixProbe v a := by
  ext s hs
  have hm : Measurable (frestrictLe₂ (π := fun _ => R) hab) := measurable_frestrictLe₂ hab
  rw [Measure.map_apply hm hs,
    C.prefixProbe_apply v b _ (hm hs),
    C.prefixProbe_apply v a s hs, C.consistent a b hab s hs]

theorem exists_fullProbe (v : Q → ℂ) :
    ∃ ν : Measure (Transcript R), IsFiniteMeasure ν ∧ ν univ = probeMass v ∧
      ∀ n, ν.map (frestrictLe (π := fun _ => R) n) = C.prefixProbe v n :=
  exists_finite_extension_of_consistent_prefixes (C.prefixProbe v) (probeMass v)
    (C.prefixProbe_total v) (C.prefixProbe_consistent v)

def fullProbe (v : Q → ℂ) : Measure (Transcript R) := (C.exists_fullProbe v).choose

instance fullProbe_isFinite (v : Q → ℂ) : IsFiniteMeasure (C.fullProbe v) :=
  (C.exists_fullProbe v).choose_spec.1

theorem fullProbe_total (v : Q → ℂ) : C.fullProbe v univ = probeMass v :=
  (C.exists_fullProbe v).choose_spec.2.1

theorem fullProbe_map_prefix (v : Q → ℂ) (n : ℕ) :
    (C.fullProbe v).map (frestrictLe (π := fun _ => R) n) = C.prefixProbe v n :=
  (C.exists_fullProbe v).choose_spec.2.2 n

theorem fullProbe_apply_prefix (v : Q → ℂ) (n : ℕ) (s : Set (Prefix R n))
    (hs : MeasurableSet s) :
    C.fullProbe v ((frestrictLe (π := fun _ => R) n) ⁻¹' s) =
      ENNReal.ofReal (quadratic v (C.effect n s)) := by
  rw [← Measure.map_apply (measurable_frestrictLe n) hs, C.fullProbe_map_prefix,
    C.prefixProbe_apply v n s hs]

theorem fullProbe_signed_prefix (v : Q → ℂ) (n : ℕ) (s : Set (Prefix R n))
    (hs : MeasurableSet s) :
    (C.fullProbe v).toSignedMeasure ((frestrictLe (π := fun _ => R) n) ⁻¹' s) =
      quadratic v (C.effect n s) := by
  rw [Measure.toSignedMeasure_apply_measurable ((measurable_frestrictLe n) hs),
    measureReal_def, C.fullProbe_apply_prefix v n s hs,
    ENNReal.toReal_ofReal (quadratic_nonneg _ (C.positive n s hs) v)]

def fullVectorMeasure : VectorMeasure (Transcript R) (Matrix Q Q ℂ) :=
  polarizationMeasure (fun v => (C.fullProbe v).toSignedMeasure)

theorem fullVectorMeasure_apply (B : Set (Transcript R)) :
    C.fullVectorMeasure B = fun a b =>
      polarizationEntry (fun v => (C.fullProbe v).toSignedMeasure B) a b :=
  polarizationMeasure_apply _ B

theorem fullVectorMeasure_prefix (n : ℕ) (s : Set (Prefix R n)) (hs : MeasurableSet s) :
    C.fullVectorMeasure ((frestrictLe (π := fun _ => R) n) ⁻¹' s) = C.effect n s := by
  ext a b
  rw [C.fullVectorMeasure_apply]
  simp_rw [C.fullProbe_signed_prefix _ n s hs]
  exact polarization_quadratic _ (C.positive n s hs).isHermitian a b

theorem fullVectorMeasure_total : C.fullVectorMeasure univ = 1 := by
  simpa [C.total] using C.fullVectorMeasure_prefix 0 univ MeasurableSet.univ

theorem fullVectorMeasure_isHermitian (B : Set (Transcript R)) :
    (C.fullVectorMeasure B).IsHermitian := by
  have heq : VectorMeasure.mapRangeL conjTransposeCLM C.fullVectorMeasure =
      C.fullVectorMeasure := by
    apply vectorMeasure_eq_of_prefix
    intro n s hs
    change (C.fullVectorMeasure ((frestrictLe n) ⁻¹' s))ᴴ =
      C.fullVectorMeasure ((frestrictLe n) ⁻¹' s)
    rw [C.fullVectorMeasure_prefix n s hs]
    exact (C.positive n s hs).isHermitian
  exact congrArg (fun F : VectorMeasure (Transcript R) (Matrix Q Q ℂ) => F B) heq

theorem fullVectorMeasure_quadratic (v : Q → ℂ) :
    VectorMeasure.mapRangeL (quadraticCLM v) C.fullVectorMeasure =
      (C.fullProbe v).toSignedMeasure := by
  apply vectorMeasure_eq_of_prefix
  intro n s hs
  change quadratic v (C.fullVectorMeasure ((frestrictLe n) ⁻¹' s)) = _
  rw [C.fullVectorMeasure_prefix n s hs, C.fullProbe_signed_prefix v n s hs]

theorem fullVectorMeasure_positive (B : Set (Transcript R)) (hB : MeasurableSet B) :
    (C.fullVectorMeasure B).PosSemidef := by
  have hHerm := C.fullVectorMeasure_isHermitian B
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hHerm.im_star_dotProduct_mulVec_self v).symm⟩
  have hq := congrArg (fun σ : SignedMeasure (Transcript R) => σ B)
    (C.fullVectorMeasure_quadratic v)
  change quadratic v (C.fullVectorMeasure B) = (C.fullProbe v).toSignedMeasure B at hq
  change 0 ≤ quadratic v (C.fullVectorMeasure B)
  rw [hq, Measure.toSignedMeasure_apply_measurable hB]
  exact ENNReal.toReal_nonneg

theorem exists_full_transcript_povm :
    ∃ F : VectorMeasure (Transcript R) (Matrix Q Q ℂ),
      F univ = 1 ∧ (∀ B, MeasurableSet B → (F B).PosSemidef) ∧
      ∀ n (s : Set (Prefix R n)), MeasurableSet s →
        F ((frestrictLe (π := fun _ => R) n) ⁻¹' s) = C.effect n s :=
  ⟨C.fullVectorMeasure, C.fullVectorMeasure_total, C.fullVectorMeasure_positive,
    C.fullVectorMeasure_prefix⟩

def fullBornMeasure (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef) : Measure (Transcript R) :=
  Measure.ofMeasurable (fun B _ => ENNReal.ofReal (bornScalar ρ (C.fullVectorMeasure B)))
    (by simp [bornScalar])
    (fun s hs hdisj => by
      have hsum := (bornCLM ρ).hasSum (C.fullVectorMeasure.m_iUnion hs hdisj)
      simp only [bornCLM_apply] at hsum
      rw [← hsum.tsum_eq]
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun k => bornScalar_nonneg ρ _ hρ (C.fullVectorMeasure_positive (s k) (hs k)))
        hsum.summable)

theorem fullBornMeasure_apply (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef)
    (B : Set (Transcript R)) (hB : MeasurableSet B) :
    C.fullBornMeasure ρ hρ B = ENNReal.ofReal (bornScalar ρ (C.fullVectorMeasure B)) :=
  Measure.ofMeasurable_apply B hB

theorem fullBornMeasure_total (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef) :
    C.fullBornMeasure ρ hρ univ = ENNReal.ofReal ρ.trace.re := by
  rw [C.fullBornMeasure_apply ρ hρ univ MeasurableSet.univ, C.fullVectorMeasure_total]
  simp [bornScalar]

instance fullBornMeasure_isFinite (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef) :
    IsFiniteMeasure (C.fullBornMeasure ρ hρ) := by
  constructor
  rw [C.fullBornMeasure_total]
  exact ENNReal.ofReal_lt_top

theorem fullBornMeasure_isProbability (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) : IsProbabilityMeasure (C.fullBornMeasure ρ hρ) := by
  constructor
  simp [C.fullBornMeasure_total, htrace]

theorem fullBornMeasure_prefix (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef)
    (n : ℕ) (s : Set (Prefix R n)) (hs : MeasurableSet s) :
    C.fullBornMeasure ρ hρ ((frestrictLe (π := fun _ => R) n) ⁻¹' s) =
      ENNReal.ofReal (bornScalar ρ (C.effect n s)) := by
  rw [C.fullBornMeasure_apply ρ hρ _ ((measurable_frestrictLe n) hs),
    C.fullVectorMeasure_prefix n s hs]

theorem fullBornMeasure_add (ρ σ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    C.fullBornMeasure (ρ + σ) (hρ.add hσ) = C.fullBornMeasure ρ hρ + C.fullBornMeasure σ hσ := by
  ext B hB
  rw [Measure.add_apply, C.fullBornMeasure_apply _ _ B hB,
    C.fullBornMeasure_apply _ _ B hB, C.fullBornMeasure_apply _ _ B hB]
  simp only [bornScalar, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  exact ENNReal.ofReal_add
    (bornScalar_nonneg ρ _ hρ (C.fullVectorMeasure_positive B hB))
    (bornScalar_nonneg σ _ hσ (C.fullVectorMeasure_positive B hB))

theorem complexWeight_nonneg (c : ℝ≥0) : (0 : ℂ) ≤ (c : ℂ) :=
  Complex.nonneg_iff.mpr ⟨c.coe_nonneg, rfl⟩

def faithfulWeight : ℝ≥0 := (Fintype.card Q : ℝ≥0)⁻¹

def faithfulInput : Matrix Q Q ℂ := (faithfulWeight (Q := Q) : ℂ) • 1

theorem faithfulInput_positive : (faithfulInput (Q := Q)).PosSemidef :=
  Matrix.PosSemidef.one.smul (complexWeight_nonneg (faithfulWeight (Q := Q)))

theorem faithfulInput_eq_inverse_dim_smul :
    faithfulInput (Q := Q) = (Fintype.card Q : ℂ)⁻¹ • 1 := by
  simp [faithfulInput, faithfulWeight, NNReal.coe_inv]

theorem faithfulInput_trace [Nonempty Q] : (faithfulInput (Q := Q)).trace = 1 := by
  rw [faithfulInput_eq_inverse_dim_smul, Matrix.trace_smul, Matrix.trace_one]
  change (Fintype.card Q : ℂ)⁻¹ * (Fintype.card Q : ℂ) = 1
  exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

theorem fullBornMeasure_smul (c : ℝ≥0) (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef) :
    C.fullBornMeasure ((c : ℂ) • ρ) (hρ.smul (complexWeight_nonneg c)) =
      c • C.fullBornMeasure ρ hρ := by
  ext B hB
  rw [Measure.smul_apply, C.fullBornMeasure_apply _ _ B hB,
    C.fullBornMeasure_apply _ _ B hB]
  simp [bornScalar, Matrix.mul_smul, Matrix.trace_smul, ENNReal.smul_def,
    ← ENNReal.ofReal_mul c.coe_nonneg]

theorem fullBornMeasure_affine (c e : ℝ≥0) (ρ σ : Matrix Q Q ℂ)
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    C.fullBornMeasure ((c : ℂ) • ρ + (e : ℂ) • σ)
      ((hρ.smul (complexWeight_nonneg c)).add (hσ.smul (complexWeight_nonneg e))) =
      c • C.fullBornMeasure ρ hρ + e • C.fullBornMeasure σ hσ := by
  rw [C.fullBornMeasure_add _ _ (hρ.smul (complexWeight_nonneg c))
    (hσ.smul (complexWeight_nonneg e)),
    C.fullBornMeasure_smul c ρ hρ, C.fullBornMeasure_smul e σ hσ]

def faithfulMeasure : Measure (Transcript R) :=
  (ENNReal.ofReal (Fintype.card Q : ℝ))⁻¹ • C.fullBornMeasure 1 Matrix.PosSemidef.one

theorem faithfulMeasure_eq_Born_faithfulInput [Nonempty Q] :
    C.faithfulMeasure = C.fullBornMeasure (faithfulInput (Q := Q)) faithfulInput_positive := by
  have hc : (Fintype.card Q : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    C.faithfulMeasure = faithfulWeight (Q := Q) • C.fullBornMeasure 1 Matrix.PosSemidef.one := by
      ext B hB
      simp [faithfulMeasure, faithfulWeight, Measure.smul_apply, ENNReal.smul_def,
        ENNReal.coe_inv hc, smul_eq_mul]
    _ = C.fullBornMeasure (faithfulInput (Q := Q)) faithfulInput_positive :=
      (C.fullBornMeasure_smul (faithfulWeight (Q := Q)) 1 Matrix.PosSemidef.one).symm

theorem faithfulMeasure_apply (B : Set (Transcript R)) (hB : MeasurableSet B) :
    C.faithfulMeasure B = (ENNReal.ofReal (Fintype.card Q : ℝ))⁻¹ *
      ENNReal.ofReal (C.fullVectorMeasure B).trace.re := by
  simp [faithfulMeasure, Measure.smul_apply, C.fullBornMeasure_apply _ _ B hB,
    smul_eq_mul, bornScalar]

theorem faithfulMeasure_isProbability [Nonempty Q] : IsProbabilityMeasure C.faithfulMeasure := by
  have hd : 0 < (Fintype.card Q : ℝ) := by exact_mod_cast Fintype.card_pos
  constructor
  rw [C.faithfulMeasure_apply univ MeasurableSet.univ, C.fullVectorMeasure_total]
  simp only [Matrix.trace_one, Complex.natCast_re]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hd).ne' ENNReal.ofReal_ne_top

theorem fullBornMeasure_le_faithful [Nonempty Q] (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) (B : Set (Transcript R)) (hB : MeasurableSet B) :
    C.fullBornMeasure ρ hρ B ≤ ENNReal.ofReal (Fintype.card Q : ℝ) * C.faithfulMeasure B := by
  have hd : 0 < (Fintype.card Q : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [C.fullBornMeasure_apply ρ hρ B hB, C.faithfulMeasure_apply B hB,
    ← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hd).ne'
      ENNReal.ofReal_ne_top, one_mul]
  exact ENNReal.ofReal_le_ofReal
    (bornScalar_le_trace ρ _ hρ htrace (C.fullVectorMeasure_positive B hB))

theorem fullBornMeasure_le_faithful_measure [Nonempty Q]
    (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    C.fullBornMeasure ρ hρ ≤ ENNReal.ofReal (Fintype.card Q : ℝ) • C.faithfulMeasure := by
  apply Measure.le_iff.mpr
  intro B hB
  simpa [Measure.smul_apply, smul_eq_mul] using C.fullBornMeasure_le_faithful ρ hρ htrace B hB

theorem faithful_null_all_inputs [Nonempty Q] (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) (B : Set (Transcript R)) (hB : C.faithfulMeasure B = 0) :
    C.fullBornMeasure ρ hρ B = 0 := by
  have hb := Measure.le_iff'.mp (C.fullBornMeasure_le_faithful_measure ρ hρ htrace) B
  apply le_antisymm _ bot_le
  simpa [Measure.smul_apply, hB, smul_eq_mul] using hb

def fullCoordinateKernel :
    QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym.CoordinateChoiKernel
      (H := Unit) (Ω := Transcript R) (Q := Q) where
  effect := fun _ => C.fullVectorMeasure
  empty := fun _ => C.fullVectorMeasure.empty
  positive := fun _ => C.fullVectorMeasure_positive
  measurable_entry := fun _ _ _ _ => measurable_const
  coordinate_additive := by
    intro _ s hs hdisj a b
    have h := (entryCLM a b).hasSum (C.fullVectorMeasure.m_iUnion hs hdisj)
    simpa only [entryCLM_apply] using h

theorem exists_density_for_faithfulMeasure [Nonempty Q] :
    ∃ W : Transcript R → Matrix Q Q ℂ,
      Measurable W ∧ (∀ ω, (W ω).PosSemidef) ∧ Integrable W C.faithfulMeasure ∧
      (∀ᵐ ω ∂C.faithfulMeasure, (W ω).trace = (Fintype.card Q : ℂ)) ∧
      (∫ ω, W ω ∂C.faithfulMeasure) = 1 ∧
      ∀ B, MeasurableSet B → (∫ ω in B, W ω ∂C.faithfulMeasure) = C.fullVectorMeasure B := by
  have hd : 0 < (Fintype.card Q : ℝ) := by exact_mod_cast Fintype.card_pos
  have ht : ∀ u : Unit, (C.fullCoordinateKernel.effect u univ).trace.re =
      (Fintype.card Q : ℝ) := by
    intro u
    change (C.fullVectorMeasure univ).trace.re = _
    rw [C.fullVectorMeasure_total]
    simp
  obtain ⟨μ, hμ, W, hW, hpos, hint, hset, htrace, hμset⟩ :=
    C.fullCoordinateKernel.exists_joint_positive_density (Fintype.card Q : ℝ) hd ht
  have hμeq : μ () = C.faithfulMeasure := by
    ext B hB
    calc
      μ () B = (ENNReal.ofReal (Fintype.card Q : ℝ))⁻¹ *
          ENNReal.ofReal (C.fullVectorMeasure B).trace.re := by
        simpa only [fullCoordinateKernel] using hμset () B hB
      _ = C.faithfulMeasure B := (C.faithfulMeasure_apply B hB).symm
  have hset' : ∀ B, MeasurableSet B →
      (∫ ω in B, W () ω ∂C.faithfulMeasure) = C.fullVectorMeasure B := by
    intro B hB
    simpa only [hμeq, fullCoordinateKernel] using hset () B hB
  refine ⟨W (), hW.comp (measurable_const.prodMk measurable_id), hpos (),
    ?_, ?_, ?_, hset'⟩
  · simpa only [hμeq] using hint ()
  · have htrace' : ∀ᵐ ω ∂C.faithfulMeasure, (W () ω).trace.re = (Fintype.card Q : ℝ) := by
      simpa only [hμeq] using htrace ()
    filter_upwards [htrace'] with ω hω
    apply Complex.ext
    · exact hω
    · simpa using (Complex.nonneg_iff.mp (hpos () ω).trace_nonneg).2.symm
  · simpa using (hset' univ MeasurableSet.univ).trans C.fullVectorMeasure_total

def globalDensity [Nonempty Q] : Transcript R → Matrix Q Q ℂ :=
  C.exists_density_for_faithfulMeasure.choose

theorem measurable_globalDensity [Nonempty Q] : Measurable C.globalDensity :=
  C.exists_density_for_faithfulMeasure.choose_spec.1

theorem positive_globalDensity [Nonempty Q] (ω : Transcript R) :
    (C.globalDensity ω).PosSemidef :=
  C.exists_density_for_faithfulMeasure.choose_spec.2.1 ω

theorem integrable_globalDensity [Nonempty Q] : Integrable C.globalDensity C.faithfulMeasure :=
  C.exists_density_for_faithfulMeasure.choose_spec.2.2.1

theorem ae_trace_globalDensity [Nonempty Q] :
    ∀ᵐ ω ∂C.faithfulMeasure, (C.globalDensity ω).trace = (Fintype.card Q : ℂ) :=
  C.exists_density_for_faithfulMeasure.choose_spec.2.2.2.1

theorem integral_globalDensity [Nonempty Q] :
    (∫ ω, C.globalDensity ω ∂C.faithfulMeasure) = 1 :=
  C.exists_density_for_faithfulMeasure.choose_spec.2.2.2.2.1

theorem setIntegral_globalDensity [Nonempty Q] (B : Set (Transcript R)) (hB : MeasurableSet B) :
    (∫ ω in B, C.globalDensity ω ∂C.faithfulMeasure) = C.fullVectorMeasure B :=
  C.exists_density_for_faithfulMeasure.choose_spec.2.2.2.2.2 B hB

theorem physical_report_effect [Nonempty Q] (J : Transcript R → Fin 4) (hJ : Measurable J)
    (j : Fin 4) :
    (∫ ω, {ω | J ω = j}.indicator C.globalDensity ω ∂C.faithfulMeasure) =
      C.fullVectorMeasure {ω | J ω = j} := by
  have hB : MeasurableSet {ω | J ω = j} := hJ (measurableSet_singleton j)
  rw [integral_indicator hB]
  exact C.setIntegral_globalDensity _ hB

theorem fullBornMeasure_density [Nonempty Q] (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef)
    (B : Set (Transcript R)) (hB : MeasurableSet B) :
    C.fullBornMeasure ρ hρ B = ENNReal.ofReal
      (∫ ω in B, bornScalar ρ (C.globalDensity ω) ∂C.faithfulMeasure) := by
  rw [C.fullBornMeasure_apply ρ hρ B hB, ← C.setIntegral_globalDensity B hB]
  congr 1
  exact ((bornCLM ρ).integral_comp_comm C.integrable_globalDensity.restrict).symm

theorem finiteReadout_factors_through_actual_prefix [Nonempty Q]
    (J : Transcript R → Fin 4) (n : ℕ) :
    ∃ g : Prefix R n → Fin 4, Measurable g ∧
      QuantumProver.ElegantJointMeasurement.InfiniteRecordReadout.finiteReadout C.faithfulMeasure (prefixFiltration (R := R)) J n =
        g ∘ frestrictLe (π := fun _ => R) n :=
  QuantumProver.ElegantJointMeasurement.InfiniteRecordReadout.finiteReadout_factors_through_prefix C.faithfulMeasure
    (prefixFiltration (R := R)) J n (frestrictLe (π := fun _ => R) n) rfl

instance faithfulMeasure_probability [Nonempty Q] : IsProbabilityMeasure C.faithfulMeasure :=
  C.faithfulMeasure_isProbability

variable [Nonempty Q]

def matrixFiniteReadout (J : Transcript R → Fin 4) (n : ℕ) : Transcript R → Fin 4 :=
  QuantumProver.ElegantJointMeasurement.InfiniteRecordReadout.finiteReadout C.faithfulMeasure (prefixFiltration (R := R)) J n

def reportedEffect (J : Transcript R → Fin 4) (j : Fin 4) : Matrix Q Q ℂ :=
  ∫ ω, {ω | J ω = j}.indicator C.globalDensity ω ∂C.faithfulMeasure

def finiteReportEffect (J : Transcript R → Fin 4) (n : ℕ) (j : Fin 4) : Matrix Q Q ℂ :=
  C.reportedEffect (C.matrixFiniteReadout J n) j

theorem reportedEffect_eq_physical (J : Transcript R → Fin 4) (hJ : Measurable J) (j : Fin 4) :
    C.reportedEffect J j = C.fullVectorMeasure {ω | J ω = j} :=
  C.physical_report_effect J hJ j

theorem measurable_matrixFiniteReadout_prefix (J : Transcript R → Fin 4) (n : ℕ) :
    Measurable[prefixFiltration (R := R) n] (C.matrixFiniteReadout J n) :=
  QuantumProver.ElegantJointMeasurement.InfiniteRecordReadout.measurable_finiteReadout C.faithfulMeasure
    (prefixFiltration (R := R)) J n

theorem measurable_matrixFiniteReadout (J : Transcript R → Fin 4) (n : ℕ) :
    Measurable (C.matrixFiniteReadout J n) :=
  (C.measurable_matrixFiniteReadout_prefix J n).mono (prefixFiltration.le n) le_rfl

theorem matrixFiniteReadout_ae_eventually_eq (J : Transcript R → Fin 4) (hJ : Measurable J) :
    ∀ᵐ ω ∂C.faithfulMeasure, ∀ᶠ n in atTop, C.matrixFiniteReadout J n ω = J ω :=
  QuantumProver.ElegantJointMeasurement.InfiniteRecordReadout.ae_eventually_finiteReadout_eq C.faithfulMeasure
    (prefixFiltration (R := R)) iSup_prefixFiltration J hJ

theorem matrixFiniteReadout_disagreement_tendsto_zero (J : Transcript R → Fin 4)
    (hJ : Measurable J) :
    Tendsto (fun n => C.faithfulMeasure {ω | C.matrixFiniteReadout J n ω ≠ J ω})
      atTop (𝓝 0) :=
  QuantumProver.ElegantJointMeasurement.InfiniteRecordReadout.tendsto_disagreement_mass C.faithfulMeasure
    (prefixFiltration (R := R)) iSup_prefixFiltration J hJ

theorem reportedEffect_positive (J : Transcript R → Fin 4) (j : Fin 4) :
    (C.reportedEffect J j).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply integral_nonneg_of_ae
  filter_upwards [] with ω
  by_cases hj : J ω = j
  · simpa [reportedEffect, Set.indicator, hj] using (C.positive_globalDensity ω).nonneg
  · simp [Set.indicator, hj]

theorem reportedEffect_sum (J : Transcript R → Fin 4) (hJ : Measurable J) :
    ∑ j, C.reportedEffect J j = 1 := by
  have hJi : ∀ j ∈ (Finset.univ : Finset (Fin 4)),
      Integrable (fun ω => {ω | J ω = j}.indicator C.globalDensity ω) C.faithfulMeasure := by
    intro j _
    exact C.integrable_globalDensity.indicator ((measurableSet_singleton j).preimage hJ)
  unfold reportedEffect
  rw [← integral_finsetSum _ hJi]
  have heq : (fun ω => ∑ j, {ω | J ω = j}.indicator C.globalDensity ω) = C.globalDensity := by
    funext ω
    simp [Set.indicator, eq_comm]
  rw [heq]
  exact C.integral_globalDensity

theorem ae_norm_globalDensity_le :
    ∀ᵐ ω ∂C.faithfulMeasure, ‖C.globalDensity ω‖ ≤ (Fintype.card Q : ℝ) := by
  filter_upwards [C.ae_trace_globalDensity] with ω hω
  simpa [hω] using QuantumProver.ElegantJointMeasurement.InfiniteRecordReadout.posSemidef_norm_le_trace
    (C.globalDensity ω) (C.positive_globalDensity ω)

theorem reportedEffect_error_le (L J : Transcript R → Fin 4)
    (hL : Measurable L) (hJ : Measurable J) (j : Fin 4) :
    ‖C.reportedEffect L j - C.reportedEffect J j‖ ≤
      (Fintype.card Q : ℝ) * (C.faithfulMeasure {ω | L ω ≠ J ω}).toReal := by
  have hmis : MeasurableSet {ω | L ω ≠ J ω} := (measurableSet_eq_fun hL hJ).compl
  have hsL : MeasurableSet {ω | L ω = j} := (measurableSet_singleton j).preimage hL
  have hsJ : MeasurableSet {ω | J ω = j} := (measurableSet_singleton j).preimage hJ
  have hLi := C.integrable_globalDensity.indicator hsL
  have hJi := C.integrable_globalDensity.indicator hsJ
  rw [reportedEffect, reportedEffect, ← integral_sub hLi hJi]
  calc
    ‖∫ ω, ({ω | L ω = j}.indicator C.globalDensity ω -
        {ω | J ω = j}.indicator C.globalDensity ω) ∂C.faithfulMeasure‖
        ≤ ∫ ω, {ω | L ω ≠ J ω}.indicator (fun _ => (Fintype.card Q : ℝ)) ω
          ∂C.faithfulMeasure := by
      apply norm_integral_le_of_norm_le
        ((integrable_const (Fintype.card Q : ℝ)).indicator hmis)
      filter_upwards [C.ae_norm_globalDensity_le] with ω hn
      by_cases heq : L ω = J ω
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, heq, sub_self, norm_zero, ne_eq,
          not_true_eq_false, ite_false]
        exact le_rfl
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ne_eq, heq, not_false_eq_true, ite_true]
        by_cases hl : L ω = j <;> by_cases hj : J ω = j <;>
          simp only [hl, hj, ite_true, ite_false, sub_self, sub_zero, zero_sub, norm_neg, norm_zero]
        all_goals first | exact hn | positivity
    _ = (Fintype.card Q : ℝ) * (C.faithfulMeasure {ω | L ω ≠ J ω}).toReal := by
      rw [integral_indicator_const _ hmis]
      simp [measureReal_def, mul_comm]

theorem finiteReportEffect_operator_error_le (J : Transcript R → Fin 4)
    (hJ : Measurable J) (n : ℕ) (j : Fin 4) :
    ‖(Matrix.toEuclideanCLM (n := Q) (𝕜 := ℂ))
      (C.finiteReportEffect J n j - C.reportedEffect J j)‖ ≤
      (Fintype.card Q : ℝ) *
        (C.faithfulMeasure {ω | C.matrixFiniteReadout J n ω ≠ J ω}).toReal := by
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  exact C.reportedEffect_error_le _ J (C.measurable_matrixFiniteReadout J n) hJ j

theorem finiteReportEffect_tendsto (J : Transcript R → Fin 4) (hJ : Measurable J) (j : Fin 4) :
    Tendsto (fun n => C.finiteReportEffect J n j) atTop (𝓝 (C.reportedEffect J j)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => C.reportedEffect_error_le _ J (C.measurable_matrixFiniteReadout J n) hJ j)
  simpa [matrixFiniteReadout] using
    (QuantumProver.ElegantJointMeasurement.InfiniteRecordReadout.tendsto_disagreement_real C.faithfulMeasure
      (prefixFiltration (R := R)) iSup_prefixFiltration J hJ).const_mul (Fintype.card Q : ℝ)

theorem finiteReportEffect_family_tendsto (J : Transcript R → Fin 4) (hJ : Measurable J) :
    Tendsto (fun n j => C.finiteReportEffect J n j) atTop (𝓝 (fun j => C.reportedEffect J j)) :=
  tendsto_pi_nhds.2 (C.finiteReportEffect_tendsto J hJ)

theorem finiteReportEffect_eq_matrix_cylinder (J : Transcript R → Fin 4) (n : ℕ) :
    ∃ g : Prefix R n → Fin 4, Measurable g ∧
      C.matrixFiniteReadout J n = g ∘ frestrictLe (π := fun _ => R) n ∧
      ∀ j, C.finiteReportEffect J n j = C.effect n {h | g h = j} := by
  obtain ⟨g, hg, heq⟩ := C.finiteReadout_factors_through_actual_prefix J n
  refine ⟨g, hg, heq, ?_⟩
  intro j
  rw [finiteReportEffect, C.reportedEffect_eq_physical _ (C.measurable_matrixFiniteReadout J n) j]
  have hB : {ω | C.matrixFiniteReadout J n ω = j} =
      (frestrictLe (π := fun _ => R) n) ⁻¹' {h | g h = j} := by
    ext ω
    change (C.matrixFiniteReadout J n ω = j) ↔ _
    rw [show C.matrixFiniteReadout J n = g ∘ frestrictLe n from heq]
    rfl
  rw [hB]
  have hs : MeasurableSet {h : Prefix R n | g h = j} :=
    (measurableSet_singleton j).preimage hg
  exact C.fullVectorMeasure_prefix n {h | g h = j} hs

theorem finiteReportEffect_entry_tendsto (J : Transcript R → Fin 4) (hJ : Measurable J)
    (j : Fin 4) (a b : Q) :
    Tendsto (fun n => C.finiteReportEffect J n j a b) atTop (𝓝 (C.reportedEffect J j a b)) :=
  (continuous_apply b).tendsto _ |>.comp
    ((continuous_apply a).tendsto _ |>.comp (C.finiteReportEffect_tendsto J hJ j))

theorem actual_matrix_infinite_readout (J : Transcript R → Fin 4) (hJ : Measurable J) :
    (∀ n, Measurable[prefixFiltration (R := R) n] (C.matrixFiniteReadout J n)) ∧
    (∀ n, ∃ g : Prefix R n → Fin 4, Measurable g ∧
      C.matrixFiniteReadout J n = g ∘ frestrictLe (π := fun _ => R) n ∧
      ∀ j, C.finiteReportEffect J n j = C.effect n {h | g h = j}) ∧
    (∀ᵐ ω ∂C.faithfulMeasure, ∀ᶠ n in atTop, C.matrixFiniteReadout J n ω = J ω) ∧
    Tendsto (fun n => C.faithfulMeasure {ω | C.matrixFiniteReadout J n ω ≠ J ω}) atTop (𝓝 0) ∧
    (∀ j, C.reportedEffect J j = C.fullVectorMeasure {ω | J ω = j}) ∧
    (∀ j, (C.reportedEffect J j).PosSemidef) ∧ (∑ j, C.reportedEffect J j) = 1 ∧
    (∀ n, (∀ j, (C.finiteReportEffect J n j).PosSemidef) ∧
      (∑ j, C.finiteReportEffect J n j) = 1 ∧
      ∀ j, ‖(Matrix.toEuclideanCLM (n := Q) (𝕜 := ℂ))
        (C.finiteReportEffect J n j - C.reportedEffect J j)‖ ≤
        (Fintype.card Q : ℝ) *
          (C.faithfulMeasure {ω | C.matrixFiniteReadout J n ω ≠ J ω}).toReal) ∧
    Tendsto (fun n j => C.finiteReportEffect J n j) atTop (𝓝 (fun j => C.reportedEffect J j)) := by
  refine ⟨C.measurable_matrixFiniteReadout_prefix J, C.finiteReportEffect_eq_matrix_cylinder J,
    C.matrixFiniteReadout_ae_eventually_eq J hJ,
    C.matrixFiniteReadout_disagreement_tendsto_zero J hJ,
    C.reportedEffect_eq_physical J hJ, C.reportedEffect_positive J, C.reportedEffect_sum J hJ,
    ?_, C.finiteReportEffect_family_tendsto J hJ⟩
  intro n
  exact ⟨C.reportedEffect_positive _, C.reportedEffect_sum _ (C.measurable_matrixFiniteReadout J n),
    C.finiteReportEffect_operator_error_le J hJ n⟩

def rawReportVersion (J : Transcript R → Fin 4) (hJ : NullMeasurable J C.faithfulMeasure) :
    Transcript R → Fin 4 := hJ.aemeasurable.mk J

theorem measurable_rawReportVersion (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J C.faithfulMeasure) : Measurable (C.rawReportVersion J hJ) :=
  hJ.aemeasurable.measurable_mk

theorem rawReportVersion_ae_eq (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J C.faithfulMeasure) : J =ᵐ[C.faithfulMeasure] C.rawReportVersion J hJ :=
  hJ.aemeasurable.ae_eq_mk

theorem rawReportVersion_ae_eq_all_inputs (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J C.faithfulMeasure) (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) : J =ᵐ[C.fullBornMeasure ρ hρ] C.rawReportVersion J hJ := by
  have habs : C.fullBornMeasure ρ hρ ≪ C.faithfulMeasure :=
    fun B hB => C.faithful_null_all_inputs ρ hρ htrace B hB
  exact habs.ae_eq (C.rawReportVersion_ae_eq J hJ)

theorem reportedEffect_rawReportVersion (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J C.faithfulMeasure) (j : Fin 4) :
    C.reportedEffect J j = C.reportedEffect (C.rawReportVersion J hJ) j := by
  apply integral_congr_ae
  filter_upwards [C.rawReportVersion_ae_eq J hJ] with ω hω
  simp only [Set.indicator_apply, Set.mem_setOf_eq, hω]

theorem reportLaw_rawReportVersion_all_inputs (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J C.faithfulMeasure) (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef)
    (htrace : ρ.trace = 1) (j : Fin 4) :
    C.fullBornMeasure ρ hρ {ω | J ω = j} =
      C.fullBornMeasure ρ hρ {ω | C.rawReportVersion J hJ ω = j} := by
  apply measure_congr
  filter_upwards [C.rawReportVersion_ae_eq_all_inputs J hJ ρ hρ htrace] with ω hω
  simp only [Set.mem_setOf_eq, hω]

theorem completedReportEffect_family_tendsto (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J C.faithfulMeasure) :
    Tendsto (fun n j => C.finiteReportEffect (C.rawReportVersion J hJ) n j) atTop
      (𝓝 (fun j => C.reportedEffect J j)) := by
  have heq : (fun j => C.reportedEffect J j) =
      (fun j => C.reportedEffect (C.rawReportVersion J hJ) j) :=
    funext (C.reportedEffect_rawReportVersion J hJ)
  rw [heq]
  exact C.finiteReportEffect_family_tendsto _ (C.measurable_rawReportVersion J hJ)

theorem common_raw_report_version (J : Transcript R → Fin 4)
    (hJ : NullMeasurable J C.faithfulMeasure) :
    ∃ J₀ : Transcript R → Fin 4, Measurable J₀ ∧ J =ᵐ[C.faithfulMeasure] J₀ ∧
      (∀ (ρ : Matrix Q Q ℂ) (hρ : ρ.PosSemidef), ρ.trace = 1 →
        J =ᵐ[C.fullBornMeasure ρ hρ] J₀) ∧
      (∀ j, C.reportedEffect J j = C.reportedEffect J₀ j) ∧
      Tendsto (fun n j => C.finiteReportEffect J₀ n j) atTop (𝓝 (fun j => C.reportedEffect J j)) :=
  ⟨C.rawReportVersion J hJ, C.measurable_rawReportVersion J hJ, C.rawReportVersion_ae_eq J hJ,
    C.rawReportVersion_ae_eq_all_inputs J hJ, C.reportedEffect_rawReportVersion J hJ,
    C.completedReportEffect_family_tendsto J hJ⟩

end ConsistentCylinderPOVM

end Cylinders

end QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM
