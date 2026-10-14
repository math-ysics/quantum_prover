import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.IConcurrence
import QuantumProver.InformationTheory.ElegantJointMeasurement.ContinuousProtocol
import QuantumProver.InformationTheory.ElegantJointMeasurement.TranscriptPOVM
import QuantumProver.InformationTheory.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
import QuantumProver.InformationTheory.ElegantJointMeasurement.CountableInstruments

noncomputable section

set_option maxHeartbeats 800000

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess

open MeasureTheory ProbabilityTheory Set Function Filter Preorder
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

universe u

abbrev Prefix (R : Type u) (n : ℕ) := (i : Finset.Iic n) → R

abbrev History (R : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Prefix R n

variable {R : Type u} [MeasurableSpace R]

instance historyMeasurableSpace (n : ℕ) : MeasurableSpace (History R n) :=
  match n with
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n + 1 => inferInstanceAs (MeasurableSpace (Prefix R n))

def prefixStepEquiv (n : ℕ) : Prefix R n × R ≃ᵐ Prefix R (n + 1) :=
  ((MeasurableEquiv.refl (Prefix R n)).prodCongr
    (MeasurableEquiv.piSingleton (X := fun _ => R) n)).trans
    (MeasurableEquiv.IicProdIoc (X := fun _ => R) (Nat.le_succ n))

theorem prefixStepEquiv_symm_fst (n : ℕ) :
    Prod.fst ∘ (prefixStepEquiv (R := R) n).symm =
      frestrictLe₂ (π := fun _ => R) (Nat.le_succ n) := rfl

def firstRecordEquiv : R ≃ᵐ Prefix R 0 where
  toFun r := fun _ => r
  invFun h := h ⟨0, by simp⟩
  left_inv _ := rfl
  right_inv h := by
    funext i
    have hi : i = ⟨0, by simp⟩ := by
      apply Subtype.ext
      change i.val = 0
      exact Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.property)
    subst i
    rfl
  measurable_toFun := Measurable.of_eval (fun _ => measurable_id)
  measurable_invFun := measurable_pi_apply _

def appendHistory : (n : ℕ) → History R n × R ≃ᵐ History R (n + 1)
  | 0 =>
      { toFun := fun z => firstRecordEquiv z.2
        invFun := fun h => (PUnit.unit, firstRecordEquiv.symm h)
        left_inv := fun z => by cases z with | mk h x => cases h; rfl
        right_inv := fun h => firstRecordEquiv.apply_symm_apply h
        measurable_toFun := firstRecordEquiv.measurable.comp measurable_snd
        measurable_invFun := measurable_const.prodMk firstRecordEquiv.symm.measurable }
  | n + 1 => prefixStepEquiv n

abbrev LocalMatrix := QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.LocalMatrix
abbrev JointMatrix := QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.JointMatrix

def tensorLeft (a b : ℕ) : LocalMatrix a →L[ℝ] JointMatrix a b :=
  ({ toFun := fun G => G ⊗ₖ (1 : LocalMatrix b)
     map_add' := by
       intro G H
       ext ⟨i, i'⟩ ⟨j, j'⟩
       simp only [Matrix.kronecker_apply, Matrix.add_apply, add_mul]
     map_smul' := by
       intro r G
       ext ⟨i, i'⟩ ⟨j, j'⟩
       simp only [Matrix.kronecker_apply, Matrix.smul_apply, smul_mul_assoc, RingHom.id_apply] } :
      LocalMatrix a →ₗ[ℝ] JointMatrix a b).toContinuousLinearMap

def tensorRight (a b : ℕ) : LocalMatrix b →L[ℝ] JointMatrix a b :=
  ({ toFun := fun G => (1 : LocalMatrix a) ⊗ₖ G
     map_add' := by
       intro G H
       ext ⟨i, i'⟩ ⟨j, j'⟩
       simp only [Matrix.kronecker_apply, Matrix.add_apply, mul_add]
     map_smul' := by
       intro r G
       ext ⟨i, i'⟩ ⟨j, j'⟩
       simp only [Matrix.kronecker_apply, Matrix.smul_apply, mul_smul_comm, RingHom.id_apply] } :
      LocalMatrix b →ₗ[ℝ] JointMatrix a b).toContinuousLinearMap

structure SquareProcess (a b : ℕ) (R : Type u) [MeasurableSpace R] where
  kernel : (n : ℕ) → Kernel (History R n) R
  markov : ∀ n, IsMarkovKernel (kernel n)
  aliceTurn : (n : ℕ) → History R n → Bool
  turn_measurable : ∀ n, Measurable (aliceTurn n)
  aliceK : (n : ℕ) → History R n → R → LocalMatrix a
  bobK : (n : ℕ) → History R n → R → LocalMatrix b
  alice_measurable : ∀ n, Measurable (uncurry (aliceK n))
  bob_measurable : ∀ n, Measurable (uncurry (bobK n))
  alice_integrable : ∀ n h, aliceTurn n h = true →
    Integrable (fun x => (aliceK n h x)ᴴ * aliceK n h x) (kernel n h)
  bob_integrable : ∀ n h, aliceTurn n h ≠ true →
    Integrable (fun x => (bobK n h x)ᴴ * bobK n h x) (kernel n h)
  alice_complete : ∀ n h, aliceTurn n h = true →
    (∫ x, (aliceK n h x)ᴴ * aliceK n h x ∂kernel n h) = 1
  bob_complete : ∀ n h, aliceTurn n h ≠ true →
    (∫ x, (bobK n h x)ᴴ * bobK n h x ∂kernel n h) = 1

namespace SquareProcess

variable {a b : ℕ} (P : SquareProcess a b R)

instance processKernelMarkov (n : ℕ) : IsMarkovKernel (P.kernel n) := P.markov n

instance processKernelSFinite (n : ℕ) : IsSFiniteKernel (P.kernel n) := by
  letI := P.markov n
  infer_instance

def localOp (n : ℕ) (h : History R n) (x : R) : JointMatrix a b :=
  if P.aliceTurn n h = true then
    P.aliceK n h x ⊗ₖ (1 : LocalMatrix b)
  else (1 : LocalMatrix a) ⊗ₖ P.bobK n h x

theorem measurable_localOp (n : ℕ) : Measurable (uncurry (P.localOp n)) := by
  classical
  unfold localOp
  apply Measurable.ite
  · exact measurableSet_eq_fun ((P.turn_measurable n).comp measurable_fst) measurable_const
  · exact (tensorLeft a b).continuous.measurable.comp
      (P.alice_measurable n)
  · exact (tensorRight a b).continuous.measurable.comp
      (P.bob_measurable n)

theorem localGram_integrable (n : ℕ) (h : History R n) :
    Integrable (fun x => (P.localOp n h x)ᴴ * P.localOp n h x) (P.kernel n h) := by
  classical
  by_cases ht : P.aliceTurn n h = true
  · simpa only [localOp, if_pos ht, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul] using
      QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.integrable_leftTensor (P.kernel n h)
        (fun x => (P.aliceK n h x)ᴴ * P.aliceK n h x) (P.alice_integrable n h ht)
  · simpa only [localOp, if_neg ht, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul] using
      QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.integrable_rightTensor (P.kernel n h)
        (fun x => (P.bobK n h x)ᴴ * P.bobK n h x) (P.bob_integrable n h ht)

theorem localGram_integral (n : ℕ) (h : History R n) :
    (∫ x, (P.localOp n h x)ᴴ * P.localOp n h x ∂P.kernel n h) = 1 := by
  classical
  by_cases ht : P.aliceTurn n h = true
  · simp only [localOp, if_pos ht, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    change (∫ x, tensorLeft a b ((P.aliceK n h x)ᴴ * P.aliceK n h x)
      ∂P.kernel n h) = 1
    rw [(tensorLeft a b).integral_comp_comm (P.alice_integrable n h ht),
      P.alice_complete n h ht]
    change (1 : LocalMatrix a) ⊗ₖ (1 : LocalMatrix b) = 1
    simp
  · simp only [localOp, if_neg ht, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    change (∫ x, tensorRight a b ((P.bobK n h x)ᴴ * P.bobK n h x)
      ∂P.kernel n h) = 1
    rw [(tensorRight a b).integral_comp_comm (P.bob_integrable n h ht),
      P.bob_complete n h ht]
    change (1 : LocalMatrix a) ⊗ₖ (1 : LocalMatrix b) = 1
    simp

def prefixMeasure (P : SquareProcess a b R) : (n : ℕ) → Measure (Prefix R n)
  | 0 => (P.kernel 0 PUnit.unit).map firstRecordEquiv
  | n + 1 => ((P.prefixMeasure n) ⊗ₘ P.kernel (n + 1)).map (prefixStepEquiv n)

instance prefixMeasure_isProbability (n : ℕ) : IsProbabilityMeasure (P.prefixMeasure n) := by
  induction n with
  | zero =>
      letI := P.markov 0
      constructor
      rw [prefixMeasure, Measure.map_apply firstRecordEquiv.measurable MeasurableSet.univ]
      simp
  | succ n ih =>
      letI := P.markov (n + 1)
      letI := ih
      constructor
      rw [prefixMeasure, Measure.map_apply (prefixStepEquiv n).measurable MeasurableSet.univ]
      simp

def pathOp (P : SquareProcess a b R) : (n : ℕ) → Prefix R n → JointMatrix a b
  | 0, h => P.localOp 0 PUnit.unit (firstRecordEquiv.symm h)
  | n + 1, h =>
      let z := (prefixStepEquiv n).symm h
      P.localOp (n + 1) z.1 z.2 * P.pathOp n z.1

def pathGram (n : ℕ) (h : Prefix R n) : JointMatrix a b :=
  (P.pathOp n h)ᴴ * P.pathOp n h

theorem pathGram_posSemidef (n : ℕ) (h : Prefix R n) : (P.pathGram n h).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

theorem measurable_pathOp (n : ℕ) : Measurable (P.pathOp n) := by
  induction n with
  | zero =>
      exact (P.measurable_localOp 0).comp
        (measurable_const.prodMk firstRecordEquiv.symm.measurable)
  | succ n ih =>
      change Measurable (fun h => P.localOp (n + 1)
        ((prefixStepEquiv n).symm h).1 ((prefixStepEquiv n).symm h).2 *
        P.pathOp n ((prefixStepEquiv n).symm h).1)
      exact ((P.measurable_localOp (n + 1)).comp (prefixStepEquiv n).symm.measurable).mul
        (ih.comp (measurable_fst.comp (prefixStepEquiv n).symm.measurable))

theorem measurable_pathGram (n : ℕ) : Measurable (P.pathGram n) := by
  change Measurable (fun h => star (P.pathOp n h) * P.pathOp n h)
  exact (continuous_star.measurable.comp (P.measurable_pathOp n)).mul (P.measurable_pathOp n)

def sandwichCLM (V : JointMatrix a b) : JointMatrix a b →L[ℝ] JointMatrix a b :=
  ({ toFun := fun G => Vᴴ * G * V
     map_add' := by intro G H; simp [Matrix.mul_add, Matrix.add_mul]
     map_smul' := by intro r G; simp [Matrix.mul_smul, Matrix.smul_mul] } :
      JointMatrix a b →ₗ[ℝ] JointMatrix a b).toContinuousLinearMap

def traceReCLM (a b : ℕ) : JointMatrix a b →L[ℝ] ℝ :=
  ({ toFun := fun G => G.trace.re
     map_add' := by intro G H; simp [Matrix.trace_add]
     map_smul' := by intro r G; simp [Matrix.trace_smul, Complex.real_smul] } :
      JointMatrix a b →ₗ[ℝ] ℝ).toContinuousLinearMap

theorem positive_norm_le_trace (G : JointMatrix a b) (hG : G.PosSemidef) :
    ‖G‖ ≤ G.trace.re := by
  have hn : ‖G‖ = ‖fun i => (hG.isHermitian.eigenvalues i : ℂ)‖ := by
    conv_lhs => rw [hG.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
    simp only [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
    rfl
  have ht : G.trace.re = ∑ i, hG.isHermitian.eigenvalues i := by
    rw [hG.isHermitian.trace_eq_sum_eigenvalues]
    simp
  rw [hn, ht]
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg
    (fun i _ => hG.eigenvalues_nonneg i))).mpr
  intro i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hG.eigenvalues_nonneg i)]
  exact Finset.single_le_sum (fun k _ => hG.eigenvalues_nonneg k) (Finset.mem_univ i)

theorem integrable_positive_compProd {H X : Type*} [MeasurableSpace H]
    [MeasurableSpace X] (μ : Measure H) [SFinite μ] (κ : Kernel H X)
    [IsSFiniteKernel κ] (G : H × X → JointMatrix a b) (F : H → JointMatrix a b)
    (hG : Measurable G) (hpos : ∀ z, (G z).PosSemidef)
    (hi : ∀ h, Integrable (fun x => G (h, x)) (κ h))
    (heq : ∀ h, (∫ x, G (h, x) ∂κ h) = F h)
    (hF : Integrable F μ) : Integrable G (μ ⊗ₘ κ) := by
  apply (MeasureTheory.Measure.integrable_compProd_iff hG.aestronglyMeasurable).2
  refine ⟨Eventually.of_forall hi, ?_⟩
  have htrace : Integrable (fun h => (F h).trace.re) μ :=
    (traceReCLM a b).integrable_comp hF
  have hm : AEStronglyMeasurable (fun h => ∫ x, ‖G (h, x)‖ ∂κ h) μ :=
    hG.norm.stronglyMeasurable.integral_kernel_prod_right'.aestronglyMeasurable
  apply htrace.mono' hm
  filter_upwards with h
  rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
  calc
    (∫ x, ‖G (h, x)‖ ∂κ h) ≤ ∫ x, (G (h, x)).trace.re ∂κ h := by
      apply integral_mono (hi h).norm ((traceReCLM a b).integrable_comp (hi h))
      intro x
      exact positive_norm_le_trace _ (hpos (h, x))
    _ = (F h).trace.re := by
      change (∫ x, traceReCLM a b (G (h, x)) ∂κ h) = traceReCLM a b (F h)
      rw [(traceReCLM a b).integral_comp_comm (hi h), heq h]

theorem pathGram_step (n : ℕ) (h : Prefix R n) (x : R) :
    P.pathGram (n + 1) (prefixStepEquiv n (h, x)) =
      sandwichCLM (P.pathOp n h)
        ((P.localOp (n + 1) h x)ᴴ * P.localOp (n + 1) h x) := by
  unfold pathGram
  simp only [pathOp, MeasurableEquiv.symm_apply_apply]
  change (P.localOp (n + 1) h x * P.pathOp n h)ᴴ *
      (P.localOp (n + 1) h x * P.pathOp n h) =
    (P.pathOp n h)ᴴ * ((P.localOp (n + 1) h x)ᴴ * P.localOp (n + 1) h x) * P.pathOp n h
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem stepGram_integrable (n : ℕ) (h : Prefix R n) :
    Integrable (fun x => P.pathGram (n + 1) (prefixStepEquiv n (h, x)))
      (P.kernel (n + 1) h) := by
  simp only [P.pathGram_step]
  exact (sandwichCLM (P.pathOp n h)).integrable_comp (P.localGram_integrable (n + 1) h)

theorem stepGram_integral (n : ℕ) (h : Prefix R n) :
    (∫ x, P.pathGram (n + 1) (prefixStepEquiv n (h, x)) ∂P.kernel (n + 1) h) =
      P.pathGram n h := by
  simp only [P.pathGram_step]
  rw [(sandwichCLM (P.pathOp n h)).integral_comp_comm
    (P.localGram_integrable (n + 1) h), P.localGram_integral]
  change (P.pathOp n h)ᴴ * 1 * P.pathOp n h = _
  simp [pathGram]

theorem pathGram_integrable_and_integral (n : ℕ) :
    Integrable (P.pathGram n) (P.prefixMeasure n) ∧
      (∫ h, P.pathGram n h ∂P.prefixMeasure n) = 1 := by
  induction n with
  | zero =>
      constructor
      · rw [prefixMeasure, integrable_map_equiv firstRecordEquiv]
        simpa [pathGram, pathOp, Function.comp_def] using P.localGram_integrable 0 PUnit.unit
      · rw [prefixMeasure, integral_map_equiv]
        simpa [pathGram, pathOp] using P.localGram_integral 0 PUnit.unit
  | succ n ih =>
      letI := P.markov (n + 1)
      have hi : Integrable (fun z => P.pathGram (n + 1) (prefixStepEquiv n z))
          ((P.prefixMeasure n) ⊗ₘ P.kernel (n + 1)) := by
        apply integrable_positive_compProd (P.prefixMeasure n) (P.kernel (n + 1))
          (fun z => P.pathGram (n + 1) (prefixStepEquiv n z)) (P.pathGram n)
        · exact (P.measurable_pathGram (n + 1)).comp (prefixStepEquiv n).measurable
        · intro z; exact P.pathGram_posSemidef _ _
        · exact P.stepGram_integrable n
        · exact P.stepGram_integral n
        · exact ih.1
      constructor
      · rw [prefixMeasure, integrable_map_equiv (prefixStepEquiv n)]
        exact hi
      · rw [prefixMeasure, integral_map_equiv, MeasureTheory.Measure.integral_compProd hi]
        simp only [P.stepGram_integral]
        exact ih.2

theorem pathGram_integrable (n : ℕ) : Integrable (P.pathGram n) (P.prefixMeasure n) :=
  (P.pathGram_integrable_and_integral n).1

theorem pathGram_integral (n : ℕ) : (∫ h, P.pathGram n h ∂P.prefixMeasure n) = 1 :=
  (P.pathGram_integrable_and_integral n).2

def cylinderEffect (n : ℕ) (B : Set (Prefix R n)) : JointMatrix a b :=
  ∫ h in B, P.pathGram n h ∂P.prefixMeasure n

@[simp] theorem cylinderEffect_empty (n : ℕ) : P.cylinderEffect n ∅ = 0 := by
  simp [cylinderEffect]

theorem cylinderEffect_posSemidef (n : ℕ) (B : Set (Prefix R n)) :
    (P.cylinderEffect n B).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  exact integral_nonneg_of_ae (Eventually.of_forall (fun h =>
    (P.pathGram_posSemidef n h).nonneg))

@[simp] theorem cylinderEffect_univ (n : ℕ) : P.cylinderEffect n univ = 1 := by
  simpa [cylinderEffect] using P.pathGram_integral n

theorem cylinderEffect_hasSum (n : ℕ) (B : ℕ → Set (Prefix R n))
    (hB : ∀ k, MeasurableSet (B k)) (hd : Pairwise (fun i j => Disjoint (B i) (B j))) :
    HasSum (fun k => P.cylinderEffect n (B k)) (P.cylinderEffect n (⋃ k, B k)) := by
  exact hasSum_integral_iUnion hB hd (P.pathGram_integrable n).integrableOn

def entryCLM (i j : Fin a × Fin b) : JointMatrix a b →L[ℂ] ℂ :=
  ({ toFun := fun G => G i j
     map_add' := by intro G H; rfl
     map_smul' := by intro r G; rfl } : JointMatrix a b →ₗ[ℂ] ℂ).toContinuousLinearMap

theorem cylinderEffect_coordinate_additive (n : ℕ) (B : ℕ → Set (Prefix R n))
    (hB : ∀ k, MeasurableSet (B k)) (hd : Pairwise (fun i j => Disjoint (B i) (B j)))
    (i j : Fin a × Fin b) :
    HasSum (fun k => P.cylinderEffect n (B k) i j)
      (P.cylinderEffect n (⋃ k, B k) i j) :=
  (entryCLM i j).hasSum (P.cylinderEffect_hasSum n B hB hd)

theorem measurable_prefixRestrict {n m : ℕ} (hnm : n ≤ m) :
    Measurable (frestrictLe₂ (π := fun _ => R) hnm) := by
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply _

theorem prefixRestrict_append (n : ℕ) (z : Prefix R n × R) :
    frestrictLe₂ (π := fun _ => R) (Nat.le_succ n) (prefixStepEquiv n z) = z.1 := by
  change ((prefixStepEquiv n).symm (prefixStepEquiv n z)).1 = z.1
  simp

theorem cylinderEffect_oneStep (n : ℕ) (B : Set (Prefix R n)) (hB : MeasurableSet B) :
    P.cylinderEffect (n + 1)
      ((frestrictLe₂ (π := fun _ => R) (Nat.le_succ n)) ⁻¹' B) =
      P.cylinderEffect n B := by
  letI := P.markov (n + 1)
  let D := (frestrictLe₂ (π := fun _ => R) (Nat.le_succ n)) ⁻¹' B
  have hD : MeasurableSet D := (measurable_prefixRestrict (R := R) (Nat.le_succ n)) hB
  have hG : Integrable (fun z => P.pathGram (n + 1) (prefixStepEquiv n z))
      ((P.prefixMeasure n) ⊗ₘ P.kernel (n + 1)) := by
    exact (integrable_map_equiv (prefixStepEquiv n) (P.pathGram (n + 1))).mp
      (by simpa only [prefixMeasure] using P.pathGram_integrable (n + 1))
  change (∫ h in D, P.pathGram (n + 1) h ∂P.prefixMeasure (n + 1)) = _
  rw [← integral_indicator hD, prefixMeasure, integral_map_equiv]
  have heq : (fun z => D.indicator (P.pathGram (n + 1)) (prefixStepEquiv n z)) =
      (B ×ˢ (univ : Set R)).indicator
        (fun z => P.pathGram (n + 1) (prefixStepEquiv n z)) := by
    funext z
    by_cases hz : z.1 ∈ B
    · simp [D, Set.indicator, prefixRestrict_append, hz]
    · simp [D, Set.indicator, prefixRestrict_append, hz]
  rw [heq, integral_indicator (hB.prod MeasurableSet.univ),
    MeasureTheory.Measure.setIntegral_compProd hB MeasurableSet.univ hG.integrableOn]
  simp only [setIntegral_univ, P.stepGram_integral]
  rfl

theorem cylinderEffect_consistent (n m : ℕ) (hnm : n ≤ m)
    (B : Set (Prefix R n)) (hB : MeasurableSet B) :
    P.cylinderEffect m ((frestrictLe₂ (π := fun _ => R) hnm) ⁻¹' B) =
      P.cylinderEffect n B := by
  induction m, hnm using Nat.le_induction with
  | base =>
      have hr : frestrictLe₂ (π := fun _ => R) (le_refl n) = id := by
        funext h i
        rfl
      rw [hr, Set.preimage_id]
  | succ m hnm ih =>
      let D := (frestrictLe₂ (π := fun _ => R) hnm) ⁻¹' B
      have hD : MeasurableSet D := (measurable_prefixRestrict (R := R) hnm) hB
      have heq : (frestrictLe₂ (π := fun _ => R) (Nat.le_succ m)) ⁻¹' D =
          (frestrictLe₂ (π := fun _ => R) (hnm.trans (Nat.le_succ m))) ⁻¹' B := rfl
      rw [← heq, P.cylinderEffect_oneStep m D hD]
      exact ih

abbrev Policy (R : Type u) := (n : ℕ) → History R n → Fin 4

def treeFrom (P : SquareProcess a b R) (policy : Policy R) : (height n : ℕ) → History R n →
    QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.Tree.{u} a b height
  | 0, n, h => .leaf 0 (policy n h)
  | height + 1, n, h =>
      let child := fun x => P.treeFrom policy height (n + 1) (appendHistory n (h, x))
      if P.aliceTurn n h = true then
        .alice R inferInstance (P.kernel n h) (P.aliceK n h) child
      else .bob R inferInstance (P.kernel n h) (P.bobK n h) child

def treeEffect (policy : Policy R) (height n : ℕ) (h : History R n) (j : Fin 4) :
    JointMatrix a b :=
  QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.reportedEffect (P.treeFrom policy height n h) j

theorem treeEffect_measurable (policy : Policy R)
    (hp : ∀ n, Measurable (policy n)) (height n : ℕ) (j : Fin 4) :
    Measurable (fun h => P.treeEffect policy height n h j) := by
  classical
  induction height generalizing n with
  | zero =>
      change Measurable (fun h => if policy n h = j then (1 : JointMatrix a b) else 0)
      exact Measurable.ite (measurableSet_eq_fun (hp n) measurable_const)
        measurable_const measurable_const
  | succ height ih =>
      have hc : Measurable (fun z : History R n × R =>
          P.treeEffect policy height (n + 1) (appendHistory n z) j) :=
        (ih (n + 1)).comp (appendHistory n).measurable
      have ha : Measurable (fun z : History R n × R =>
          QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.aliceSandwich (P.aliceK n z.1 z.2)
            (P.treeEffect policy height (n + 1) (appendHistory n z) j)) := by
        have hk := (tensorLeft a b).continuous.measurable.comp (P.alice_measurable n)
        exact ((continuous_star.measurable.comp hk).mul hc).mul hk
      have hb : Measurable (fun z : History R n × R =>
          QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.bobSandwich (P.bobK n z.1 z.2)
            (P.treeEffect policy height (n + 1) (appendHistory n z) j)) := by
        have hk := (tensorRight a b).continuous.measurable.comp (P.bob_measurable n)
        exact ((continuous_star.measurable.comp hk).mul hc).mul hk
      have haI := (ha.stronglyMeasurable.integral_kernel_prod_right'
        (κ := P.kernel n)).measurable
      have hbI := (hb.stronglyMeasurable.integral_kernel_prod_right'
        (κ := P.kernel n)).measurable
      have ht : MeasurableSet {h : History R n | P.aliceTurn n h = true} :=
        measurableSet_eq_fun (P.turn_measurable n) measurable_const
      simpa only [treeEffect, treeFrom, QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.reportedEffect,
        apply_ite, ite_apply] using Measurable.ite ht haI hbI

theorem treeFrom_wellFormed (policy : Policy R) (hp : ∀ n, Measurable (policy n))
    (height n : ℕ) (h : History R n) :
    QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.WellFormed (P.treeFrom policy height n h) := by
  classical
  induction height generalizing n with
  | zero => trivial
  | succ height ih =>
      have hc (x : R) := ih (n + 1) (appendHistory n (h, x))
      have hm (j : Fin 4) : Measurable (fun x => P.treeEffect policy height (n + 1)
          (appendHistory n (h, x)) j) :=
        (P.treeEffect_measurable policy hp height (n + 1) j).comp
          ((appendHistory n).measurable.comp (measurable_const.prodMk measurable_id))
      by_cases ht : P.aliceTurn n h = true
      · simp only [treeFrom, if_pos ht, QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.WellFormed]
        exact ⟨inferInstance, (P.alice_measurable n).comp
          (measurable_const.prodMk measurable_id), P.alice_integrable n h ht,
          P.alice_complete n h ht, hc, hm⟩
      · simp only [treeFrom, if_neg ht, QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.WellFormed]
        exact ⟨inferInstance, (P.bob_measurable n).comp
          (measurable_const.prodMk measurable_id), P.bob_integrable n h ht,
          P.bob_complete n h ht, hc, hm⟩

theorem treeEffect_bounds (policy : Policy R) (hp : ∀ n, Measurable (policy n))
    (height n : ℕ) (h : History R n) (j : Fin 4) :
    (P.treeEffect policy height n h j).PosSemidef ∧
      P.treeEffect policy height n h j ≤ 1 :=
  QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.reportedEffect_bounds _
    (P.treeFrom_wellFormed policy hp height n h) j

theorem integrable_bounded_pullback {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (V E : X → JointMatrix a b)
    (hV : Measurable V) (hE : Measurable E)
    (hGram : Integrable (fun x => (V x)ᴴ * V x) μ)
    (hpos : ∀ x, (E x).PosSemidef) (hle : ∀ x, E x ≤ 1) :
    Integrable (fun x => (V x)ᴴ * E x * V x) μ := by
  apply hGram.mono (f := fun x => (V x)ᴴ * E x * V x)
    (((continuous_star.measurable.comp hV).mul hE).mul hV).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    change ‖(V x)ᴴ * E x * V x‖ ≤ ‖(V x)ᴴ * V x‖
    have hp := QuantumProver.ElegantJointMeasurement.InstrumentNormalization.matrix_pullback_posSemidef (V x) (hpos x)
    have hu := QuantumProver.ElegantJointMeasurement.InstrumentNormalization.matrix_pullback_mono (V x) (hle x)
    simpa only [Matrix.mul_one] using
      CStarAlgebra.norm_le_norm_of_le_of_nonneg hu hp.nonneg

theorem treeEffect_succ (policy : Policy R) (height n : ℕ)
    (h : History R n) (j : Fin 4) :
    P.treeEffect policy (height + 1) n h j =
      ∫ x, (P.localOp n h x)ᴴ *
        P.treeEffect policy height (n + 1) (appendHistory n (h, x)) j *
        P.localOp n h x ∂P.kernel n h := by
  classical
  by_cases ht : P.aliceTurn n h = true
  · simp only [treeEffect, treeFrom, ite_eq_left ht,
      QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.reportedEffect, localOp,
      QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.aliceSandwich]
  · simp only [treeEffect, treeFrom, ite_eq_right ht,
      QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.reportedEffect, localOp,
      QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.bobSandwich]

theorem localTreePullback_integrable (policy : Policy R)
    (hp : ∀ n, Measurable (policy n)) (height n : ℕ)
    (h : History R n) (j : Fin 4) :
    Integrable (fun x => (P.localOp n h x)ᴴ *
      P.treeEffect policy height (n + 1) (appendHistory n (h, x)) j *
      P.localOp n h x) (P.kernel n h) := by
  apply integrable_bounded_pullback (P.kernel n h)
    (P.localOp n h) (fun x => P.treeEffect policy height (n + 1)
      (appendHistory n (h, x)) j)
  · exact (P.measurable_localOp n).comp (measurable_const.prodMk measurable_id)
  · exact (P.treeEffect_measurable policy hp height (n + 1) j).comp
      ((appendHistory n).measurable.comp (measurable_const.prodMk measurable_id))
  · exact P.localGram_integrable n h
  · intro x; exact (P.treeEffect_bounds policy hp height _ _ j).1
  · intro x; exact (P.treeEffect_bounds policy hp height _ _ j).2

def treeMomentIntegrand (policy : Policy R) (height k : ℕ) (j : Fin 4)
    (h : Prefix R k) : JointMatrix a b :=
  (P.pathOp k h)ᴴ * P.treeEffect policy height (k + 1) h j * P.pathOp k h

def treeMoment (policy : Policy R) (height k : ℕ) (j : Fin 4) : JointMatrix a b :=
  ∫ h, P.treeMomentIntegrand policy height k j h ∂P.prefixMeasure k

theorem treeMomentIntegrand_measurable (policy : Policy R)
    (hp : ∀ n, Measurable (policy n)) (height k : ℕ) (j : Fin 4) :
    Measurable (P.treeMomentIntegrand policy height k j) :=
  (((continuous_star.measurable.comp (P.measurable_pathOp k)).mul
    (P.treeEffect_measurable policy hp height (k + 1) j)).mul (P.measurable_pathOp k))

theorem treeMomentIntegrand_integrable (policy : Policy R)
    (hp : ∀ n, Measurable (policy n)) (height k : ℕ) (j : Fin 4) :
    Integrable (P.treeMomentIntegrand policy height k j) (P.prefixMeasure k) := by
  apply integrable_bounded_pullback (P.prefixMeasure k) (P.pathOp k)
    (fun h => P.treeEffect policy height (k + 1) h j)
  · exact P.measurable_pathOp k
  · exact P.treeEffect_measurable policy hp height (k + 1) j
  · exact P.pathGram_integrable k
  · intro h; exact (P.treeEffect_bounds policy hp height (k + 1) h j).1
  · intro h; exact (P.treeEffect_bounds policy hp height (k + 1) h j).2

theorem treeMoment_step (policy : Policy R) (hp : ∀ n, Measurable (policy n))
    (height k : ℕ) (j : Fin 4) :
    P.treeMoment policy (height + 1) k j = P.treeMoment policy height (k + 1) j := by
  letI := P.markov (k + 1)
  have hG : Integrable (fun z =>
      P.treeMomentIntegrand policy height (k + 1) j (prefixStepEquiv k z))
      ((P.prefixMeasure k) ⊗ₘ P.kernel (k + 1)) := by
    exact (integrable_map_equiv (prefixStepEquiv k)
      (P.treeMomentIntegrand policy height (k + 1) j)).mp
      (by simpa only [prefixMeasure] using
        P.treeMomentIntegrand_integrable policy hp height (k + 1) j)
  have hpoint (h : Prefix R k) :
      (∫ x, P.treeMomentIntegrand policy height (k + 1) j
        (prefixStepEquiv k (h, x)) ∂P.kernel (k + 1) h) =
      P.treeMomentIntegrand policy (height + 1) k j h := by
    have heq : (fun x => P.treeMomentIntegrand policy height (k + 1) j
        (prefixStepEquiv k (h, x))) =
        (fun x => sandwichCLM (P.pathOp k h)
          ((P.localOp (k + 1) h x)ᴴ *
            P.treeEffect policy height (k + 2) (appendHistory (k + 1) (h, x)) j *
            P.localOp (k + 1) h x)) := by
      funext x
      simp only [treeMomentIntegrand, pathOp, MeasurableEquiv.symm_apply_apply,
        appendHistory]
      change (P.localOp (k + 1) h x * P.pathOp k h)ᴴ *
          P.treeEffect policy height (k + 2) (prefixStepEquiv k (h, x)) j *
          (P.localOp (k + 1) h x * P.pathOp k h) =
        (P.pathOp k h)ᴴ *
          ((P.localOp (k + 1) h x)ᴴ *
            P.treeEffect policy height (k + 2) (prefixStepEquiv k (h, x)) j *
            P.localOp (k + 1) h x) * P.pathOp k h
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [heq, (sandwichCLM (P.pathOp k h)).integral_comp_comm
      (P.localTreePullback_integrable policy hp height (k + 1) h j)]
    rw [← P.treeEffect_succ policy height (k + 1) h j]
    rfl
  symm
  change (∫ h, P.treeMomentIntegrand policy height (k + 1) j h
    ∂P.prefixMeasure (k + 1)) = _
  rw [prefixMeasure, integral_map_equiv, MeasureTheory.Measure.integral_compProd hG]
  exact integral_congr_ae (Eventually.of_forall hpoint)

theorem treeMoment_iter (policy : Policy R) (hp : ∀ n, Measurable (policy n))
    (height k : ℕ) (j : Fin 4) :
    P.treeMoment policy height k j = P.treeMoment policy 0 (k + height) j := by
  induction height generalizing k with
  | zero => simp
  | succ height ih =>
      rw [P.treeMoment_step policy hp height k j, ih (k + 1)]
      congr 1
      omega

theorem treeEffect_rootMoment (policy : Policy R) (height : ℕ) (j : Fin 4) :
    P.treeEffect policy (height + 1) 0 PUnit.unit j = P.treeMoment policy height 0 j := by
  rw [P.treeEffect_succ, treeMoment, prefixMeasure, integral_map_equiv]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [treeMomentIntegrand, pathOp, appendHistory,
      MeasurableEquiv.symm_apply_apply]
    rfl

theorem treeMoment_zero (policy : Policy R) (hp : ∀ n, Measurable (policy n))
    (k : ℕ) (j : Fin 4) :
    P.treeMoment policy 0 k j = P.cylinderEffect k {h | policy (k + 1) h = j} := by
  classical
  let B : Set (Prefix R k) := {h | policy (k + 1) h = j}
  have hB : MeasurableSet B := measurableSet_eq_fun (hp (k + 1)) measurable_const
  change (∫ h, P.treeMomentIntegrand policy 0 k j h ∂P.prefixMeasure k) = _
  have heq : P.treeMomentIntegrand policy 0 k j = B.indicator (P.pathGram k) := by
    funext h
    by_cases hj : policy (k + 1) h = j
    · simp [treeMomentIntegrand, treeEffect, treeFrom,
        QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.reportedEffect, B, hj, Set.indicator, pathGram]
    · simp [treeMomentIntegrand, treeEffect, treeFrom,
        QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.reportedEffect, B, hj, Set.indicator, pathGram]
  rw [heq, integral_indicator hB]
  rfl

theorem treeEffect_cylinder (policy : Policy R) (hp : ∀ n, Measurable (policy n))
    (N : ℕ) (j : Fin 4) :
    P.treeEffect policy (N + 1) 0 PUnit.unit j =
      P.cylinderEffect N {h | policy (N + 1) h = j} := by
  rw [P.treeEffect_rootMoment, P.treeMoment_iter policy hp]
  simpa only [Nat.zero_add] using P.treeMoment_zero policy hp N j

def finalPolicy (N : ℕ) (g : Prefix R N → Fin 4) : Policy R :=
  fun n h => if hn : n = N + 1 then g (cast (congrArg (History R) hn) h) else 0

@[simp] theorem finalPolicy_at (N : ℕ) (g : Prefix R N → Fin 4) (h : Prefix R N) :
    finalPolicy N g (N + 1) h = g h := by
  simp [finalPolicy]

theorem finalPolicy_measurable (N : ℕ) (g : Prefix R N → Fin 4) (hg : Measurable g) :
    ∀ n, Measurable (finalPolicy N g n) := by
  intro n
  by_cases hn : n = N + 1
  · subst n
    have heq : finalPolicy N g (N + 1) = g := funext (finalPolicy_at N g)
    rw [heq]
    exact hg
  · have heq : finalPolicy N g n = fun _ : History R n => (0 : Fin 4) := by
      funext h
      simp only [finalPolicy, dite_eq_right hn]
    rw [heq]
    exact measurable_const

theorem exists_wellFormed_tree_reportedEffect (N : ℕ) (g : Prefix R N → Fin 4)
    (hg : Measurable g) :
    ∃ T : QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.Tree.{u} a b (N + 1),
      QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.WellFormed T ∧
      ∀ j, QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.reportedEffect T j =
        P.cylinderEffect N {h | g h = j} := by
  let policy := finalPolicy N g
  have hp : ∀ n, Measurable (policy n) := finalPolicy_measurable N g hg
  refine ⟨P.treeFrom policy (N + 1) 0 PUnit.unit,
    P.treeFrom_wellFormed policy hp (N + 1) 0 PUnit.unit, ?_⟩
  intro j
  change P.treeEffect policy (N + 1) 0 PUnit.unit j = _
  rw [P.treeEffect_cylinder policy hp N j]
  simp only [policy, finalPolicy_at]

def cylinderPOVM : QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.ConsistentCylinderPOVM R (Fin a × Fin b) where
  effect := P.cylinderEffect
  empty := P.cylinderEffect_empty
  positive := fun n s _ => P.cylinderEffect_posSemidef n s
  total := P.cylinderEffect_univ
  coordinate_additive := P.cylinderEffect_coordinate_additive
  consistent := P.cylinderEffect_consistent

theorem cylinder_report_mem_actual_finite_tree_closure (N : ℕ)
    (g : Prefix R N → Fin 4) (hg : Measurable g) :
    (fun j => P.cylinderEffect N {h | g h = j}) ∈
      closure (QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.finiteKrausReportedEffectSet a b) := by
  obtain ⟨T, hT, hEffects⟩ := P.exists_wellFormed_tree_reportedEffect N g hg
  have heq : QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.reportedEffect T =
      fun j => P.cylinderEffect N {h | g h = j} := funext hEffects
  rw [← heq]
  exact QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.reportedEffect_mem_finiteKrausReportedEffectSet_closure T hT

variable [StandardBorelSpace R] [Nonempty R] [Nonempty (Fin a × Fin b)]

theorem infinite_report_mem_actual_finite_tree_closure
    (J : QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Transcript R → Fin 4) (hJ : Measurable J) :
    (fun j => P.cylinderPOVM.reportedEffect J j) ∈
      closure (QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.finiteKrausReportedEffectSet a b) := by
  apply isClosed_closure.mem_of_tendsto
    (P.cylinderPOVM.finiteReportEffect_family_tendsto J hJ)
  exact Eventually.of_forall fun n => by
    obtain ⟨g, hg, _hFactor, hEffects⟩ :=
      P.cylinderPOVM.finiteReportEffect_eq_matrix_cylinder J n
    have heq : (fun j => P.cylinderPOVM.finiteReportEffect J n j) =
        fun j => P.cylinderEffect n {h | g h = j} := funext hEffects
    rw [heq]
    exact P.cylinder_report_mem_actual_finite_tree_closure n g hg

theorem exists_actual_infinite_report_finite_tree_sequence
    (J : QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Transcript R → Fin 4) (hJ : Measurable J) :
    ∃ T : ℕ → QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree a b,
      ∃ report : (k : ℕ) → Fin (T k).terminalBraPairs.length → Fin 4,
        Tendsto (fun k => QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.finiteKrausReportedEffect
          (T k) (report k)) atTop (𝓝 (fun j => P.cylinderPOVM.reportedEffect J j)) := by
  obtain ⟨F, hF, hlim⟩ := mem_closure_iff_seq_limit.mp
    (P.infinite_report_mem_actual_finite_tree_closure J hJ)
  change ∀ k : ℕ, ∃ T : QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree a b,
    ∃ report : Fin T.terminalBraPairs.length → Fin 4,
      F k = QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.finiteKrausReportedEffect T report at hF
  choose T report hEq using hF
  exact ⟨T, report, hlim.congr' (Eventually.of_forall fun k => hEq k)⟩

theorem completed_infinite_report_mem_actual_finite_tree_closure
    (J : QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Transcript R → Fin 4)
    (hJ : NullMeasurable J P.cylinderPOVM.faithfulMeasure) :
    (fun j => P.cylinderPOVM.reportedEffect J j) ∈
      closure (QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.finiteKrausReportedEffectSet a b) := by
  obtain ⟨J₀, hJ₀, _hAE, _hAllInputs, hEffects, _hlim⟩ :=
    P.cylinderPOVM.common_raw_report_version J hJ
  have heq : (fun j => P.cylinderPOVM.reportedEffect J j) =
      fun j => P.cylinderPOVM.reportedEffect J₀ j := funext hEffects
  rw [heq]
  exact P.infinite_report_mem_actual_finite_tree_closure J₀ hJ₀

theorem exists_actual_completed_report_finite_tree_sequence
    (J : QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Transcript R → Fin 4)
    (hJ : NullMeasurable J P.cylinderPOVM.faithfulMeasure) :
    ∃ T : ℕ → QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree a b,
      ∃ report : (k : ℕ) → Fin (T k).terminalBraPairs.length → Fin 4,
        Tendsto (fun k => QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.finiteKrausReportedEffect
          (T k) (report k)) atTop (𝓝 (fun j => P.cylinderPOVM.reportedEffect J j)) := by
  obtain ⟨F, hF, hlim⟩ := mem_closure_iff_seq_limit.mp
    (P.completed_infinite_report_mem_actual_finite_tree_closure J hJ)
  change ∀ k : ℕ, ∃ T : QuantumProver.ElegantJointMeasurement.Concurrence.FiniteLocalKrausTree a b,
    ∃ report : Fin T.terminalBraPairs.length → Fin 4,
      F k = QuantumProver.ElegantJointMeasurement.HilbertContinuousProtocol.finiteKrausReportedEffect T report at hF
  choose T report hEq using hF
  exact ⟨T, report, hlim.congr' (Eventually.of_forall fun k => hEq k)⟩

end SquareProcess

end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess
namespace RawInstrumentProcess

open MeasureTheory ProbabilityTheory Set Function Filter Preorder
open QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

universe u

abbrev AliceColumn (a : Nat) := Fin a × Fin a
abbrev BobColumn (b : Nat) := Fin b × Fin b
abbrev HiddenRecord (a b : Nat) := AliceColumn a × BobColumn b
abbrev FineRecord (a b : Nat) (R : Type u) := R × HiddenRecord a b

variable {R : Type u} [MeasurableSpace R]

instance historyStandardBorel [StandardBorelSpace R] (n : Nat) :
    StandardBorelSpace (History R n) :=
  match n with
  | 0 => inferInstanceAs (StandardBorelSpace PUnit)
  | n + 1 => inferInstanceAs (StandardBorelSpace (Prefix R n))

instance historyFintype {Q : Type u} [Fintype Q] (n : Nat) :
    Fintype (History Q n) :=
  match n with
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => inferInstanceAs (Fintype (Prefix Q n))

def coarseHistory {a b : Nat} :
    (n : Nat) → History (FineRecord a b R) n → History R n
  | 0 => fun _ => PUnit.unit
  | n + 1 => fun h i => (h i).1

theorem measurable_coarseHistory {a b : Nat} (n : Nat) :
    Measurable (coarseHistory (R := R) (a := a) (b := b) n) := by
  cases n with
  | zero => exact measurable_const
  | succ n => exact Measurable.of_eval (fun i => (measurable_pi_apply i).fst)

structure MatrixProcess (a b : Nat) (R : Type u) [MeasurableSpace R] where
  alice : (n : Nat) → MatrixCPInstrument
    (H := History R n) (Ω := R) (I := Fin a) (O := Fin a)
  bob : (n : Nat) → MatrixCPInstrument
    (H := History R n) (Ω := R) (I := Fin b) (O := Fin b)
  aliceTurn : (n : Nat) → History R n → Bool
  turn_measurable : ∀ n, Measurable (aliceTurn n)

def pullbackInstrument {H H' Ω : Type*}
    [MeasurableSpace H] [MeasurableSpace H'] [MeasurableSpace Ω]
    {m p : Nat}
    (P : MatrixCPInstrument (H := H) (Ω := Ω) (I := Fin m) (O := Fin p))
    (f : H' → H) (hf : Measurable f) :
    MatrixCPInstrument (H := H') (Ω := Ω) (I := Fin m) (O := Fin p) where
  map h B := P.map (f h) B
  empty h := P.empty (f h)
  completelyPositive h B hB := P.completelyPositive (f h) B hB
  measurable_entry B hB i j k l := (P.measurable_entry B hB i j k l).comp hf
  coordinate_additive h B hB hdisj i j k l :=
    P.coordinate_additive (f h) B hB hdisj i j k l
  traceComplete h X := P.traceComplete (f h) X

variable {a b : Nat} [NeZero a] [NeZero b] [StandardBorelSpace R]
namespace MatrixProcess
variable (P : MatrixProcess a b R)

def physicalKernel (n : Nat) : Kernel (History R n) R :=
  Kernel.piecewise (measurableSet_eq_fun (P.turn_measurable n) (measurable_const (a := true)))
    (P.alice n).measureKernel (P.bob n).measureKernel

theorem physicalKernel_markov (n : Nat) : IsMarkovKernel (P.physicalKernel n) := by
  letI := (P.alice n).measureKernel_isMarkov
  letI := (P.bob n).measureKernel_isMarkov
  unfold physicalKernel
  infer_instance

def represented_physicalPrefixMeasure (P : MatrixProcess a b R) : (n : Nat) → Measure (History R n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => Measure.map (appendHistory (R := R) n)
      ((P.represented_physicalPrefixMeasure n).compProd (P.physicalKernel n))

theorem represented_physicalPrefixMeasure_probability (n : Nat) :
    IsProbabilityMeasure (P.represented_physicalPrefixMeasure n) := by
  induction n with
  | zero =>
      change IsProbabilityMeasure (Measure.dirac PUnit.unit)
      infer_instance
  | succ n ih =>
      letI := ih
      letI := P.physicalKernel_markov n
      constructor
      rw [represented_physicalPrefixMeasure,
        Measure.map_apply (appendHistory (R := R) n).measurable MeasurableSet.univ]
      simp

def physicalLocalDensity (n : Nat) (h : History R n) (r : R) :
    JointMatrix a b →ₗ[Complex] JointMatrix a b :=
  if P.aliceTurn n h = true then
    QuantumProver.ElegantJointMeasurement.CP.leftApplication ((P.alice n).cpDensity h r)
  else QuantumProver.ElegantJointMeasurement.CP.rightApplication ((P.bob n).cpDensity h r)

def physicalAction (P : MatrixProcess a b R) : (n : Nat) → History R n →
    (JointMatrix a b →ₗ[Complex] JointMatrix a b)
  | 0, _ => LinearMap.id
  | n + 1, h =>
      let z := (appendHistory (R := R) n).symm h
      (P.physicalLocalDensity n z.1 z.2).comp (P.physicalAction n z.1)

def represented_physicalPrefixAction (n : Nat) (B : Set (History R n)) (X : JointMatrix a b) :
    JointMatrix a b := ∫ h in B, P.physicalAction n h X ∂P.represented_physicalPrefixMeasure n

end MatrixProcess

section FiniteSumJointLifting

variable {Q : Type*} [Fintype Q]

theorem leftApplication_sum
    (Φ : Q → (LocalMatrix a →ₗ[Complex] LocalMatrix a)) (X : JointMatrix a b) :
    QuantumProver.ElegantJointMeasurement.CP.leftApplication (∑ q, Φ q) X = ∑ q, QuantumProver.ElegantJointMeasurement.CP.leftApplication (Φ q) X := by
  classical
  ext i j
  rw [Matrix.sum_apply]
  change (∑ q, Φ q) (Matrix.of (fun x y => X (x,i.2) (y,j.2))) i.1 j.1 =
    ∑ q, Φ q (Matrix.of (fun x y => X (x,i.2) (y,j.2))) i.1 j.1
  simp only [LinearMap.sum_apply, Matrix.sum_apply]

theorem rightApplication_sum
    (Φ : Q → (LocalMatrix b →ₗ[Complex] LocalMatrix b)) (X : JointMatrix a b) :
    QuantumProver.ElegantJointMeasurement.CP.rightApplication (∑ q, Φ q) X = ∑ q, QuantumProver.ElegantJointMeasurement.CP.rightApplication (Φ q) X := by
  classical
  ext i j
  rw [Matrix.sum_apply]
  change (∑ q, Φ q) (Matrix.of (fun x y => X (i.1,x) (j.1,y))) i.2 j.2 =
    ∑ q, Φ q (Matrix.of (fun x y => X (i.1,x) (j.1,y))) i.2 j.2
  simp only [LinearMap.sum_apply, Matrix.sum_apply]

theorem leftApplication_real_smul (c : Real)
    (Φ : LocalMatrix a →ₗ[Complex] LocalMatrix a) (X : JointMatrix a b) :
    QuantumProver.ElegantJointMeasurement.CP.leftApplication (c • Φ) X = c • QuantumProver.ElegantJointMeasurement.CP.leftApplication Φ X := by
  ext i j
  rfl

theorem rightApplication_real_smul (c : Real)
    (Φ : LocalMatrix b →ₗ[Complex] LocalMatrix b) (X : JointMatrix a b) :
    QuantumProver.ElegantJointMeasurement.CP.rightApplication (c • Φ) X = c • QuantumProver.ElegantJointMeasurement.CP.rightApplication Φ X := by
  ext i j
  rfl

theorem left_pending_finite_sum
    (RA : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery a a) (RB : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery b b)
    (Φ : LocalMatrix a →ₗ[Complex] LocalMatrix a)
    (hΦ : QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive Φ) (S : Q → LocalMatrix a)
    (Rq : Q → QuantumProver.ElegantJointMeasurement.CP.LocalRecovery a a) (c : Real)
    (hlocal : ∀ Y : LocalMatrix a,
      (∑ q, (Rq q).map (S q * Y * (S q)ᴴ)) = c • Φ (RA.map Y))
    (X : JointMatrix a b) :
    (∑ q, QuantumProver.ElegantJointMeasurement.CP.pendingApplication (Rq q) RB
      (QuantumProver.ElegantJointMeasurement.CP.leftKrausApplication (S q) X)) =
      c • QuantumProver.ElegantJointMeasurement.CP.leftApplication Φ (QuantumProver.ElegantJointMeasurement.CP.pendingApplication RA RB X) := by
  classical
  have hmaps : (∑ q, (Rq q).map.comp (QuantumProver.ElegantJointMeasurement.CP.sandwichMap (S q))) =
      c • Φ.comp RA.map := by
    apply LinearMap.ext
    intro Y
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      QuantumProver.ElegantJointMeasurement.CP.sandwichMap_apply] using hlocal Y
  calc
    _ = QuantumProver.ElegantJointMeasurement.CP.rightApplication RB.map
        (∑ q, QuantumProver.ElegantJointMeasurement.CP.leftApplication ((Rq q).map.comp (QuantumProver.ElegantJointMeasurement.CP.sandwichMap (S q))) X) := by
      simp only [QuantumProver.ElegantJointMeasurement.CP.pendingApplication, LinearMap.comp_apply, map_sum,
        QuantumProver.ElegantJointMeasurement.CP.leftApplication_comp, QuantumProver.ElegantJointMeasurement.CP.leftApplication_sandwichMap]
    _ = QuantumProver.ElegantJointMeasurement.CP.rightApplication RB.map
        (QuantumProver.ElegantJointMeasurement.CP.leftApplication (c • Φ.comp RA.map) X) := by
      rw [← leftApplication_sum, hmaps]
    _ = c • QuantumProver.ElegantJointMeasurement.CP.rightApplication RB.map
        (QuantumProver.ElegantJointMeasurement.CP.leftApplication Φ (QuantumProver.ElegantJointMeasurement.CP.leftApplication RA.map X)) := by
      rw [leftApplication_real_smul, QuantumProver.ElegantJointMeasurement.CP.leftApplication_comp,
        LinearMap.map_smul_of_tower]
    _ = _ := by
      rw [← QuantumProver.ElegantJointMeasurement.CP.left_right_application_commute Φ RB.map hΦ RB.completelyPositive]
      rfl

theorem right_pending_finite_sum
    (RA : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery a a) (RB : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery b b)
    (Φ : LocalMatrix b →ₗ[Complex] LocalMatrix b)
    (hΦ : QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive Φ) (S : Q → LocalMatrix b)
    (Rq : Q → QuantumProver.ElegantJointMeasurement.CP.LocalRecovery b b) (c : Real)
    (hlocal : ∀ Y : LocalMatrix b,
      (∑ q, (Rq q).map (S q * Y * (S q)ᴴ)) = c • Φ (RB.map Y))
    (X : JointMatrix a b) :
    (∑ q, QuantumProver.ElegantJointMeasurement.CP.pendingApplication RA (Rq q)
      (QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication (S q) X)) =
      c • QuantumProver.ElegantJointMeasurement.CP.rightApplication Φ (QuantumProver.ElegantJointMeasurement.CP.pendingApplication RA RB X) := by
  classical
  have hmaps : (∑ q, (Rq q).map.comp (QuantumProver.ElegantJointMeasurement.CP.sandwichMap (S q))) =
      c • Φ.comp RB.map := by
    apply LinearMap.ext
    intro Y
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      QuantumProver.ElegantJointMeasurement.CP.sandwichMap_apply] using hlocal Y
  have hcomm (q : Q) :
      QuantumProver.ElegantJointMeasurement.CP.leftApplication RA.map (QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication (S q) X) =
        QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication (S q) (QuantumProver.ElegantJointMeasurement.CP.leftApplication RA.map X) := by
    simpa only [QuantumProver.ElegantJointMeasurement.CP.rightApplication_sandwichMap] using
      QuantumProver.ElegantJointMeasurement.CP.left_right_application_commute RA.map (QuantumProver.ElegantJointMeasurement.CP.sandwichMap (S q))
        RA.completelyPositive (QuantumProver.ElegantJointMeasurement.CP.sandwichMap_completelyPositive _) X
  calc
    _ = ∑ q, QuantumProver.ElegantJointMeasurement.CP.rightApplication ((Rq q).map.comp (QuantumProver.ElegantJointMeasurement.CP.sandwichMap (S q)))
        (QuantumProver.ElegantJointMeasurement.CP.leftApplication RA.map X) := by
      simp only [QuantumProver.ElegantJointMeasurement.CP.pendingApplication, LinearMap.comp_apply, hcomm,
        QuantumProver.ElegantJointMeasurement.CP.rightApplication_comp, QuantumProver.ElegantJointMeasurement.CP.rightApplication_sandwichMap]
    _ = QuantumProver.ElegantJointMeasurement.CP.rightApplication (c • Φ.comp RB.map) (QuantumProver.ElegantJointMeasurement.CP.leftApplication RA.map X) := by
      rw [← rightApplication_sum, hmaps]
    _ = _ := by
      rw [rightApplication_real_smul, QuantumProver.ElegantJointMeasurement.CP.rightApplication_comp]
      rfl

end FiniteSumJointLifting
end RawInstrumentProcess
end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

open MeasureTheory ProbabilityTheory Set Function Filter Preorder
open scoped BigOperators

universe u v
variable {R : Type u} {Q : Type v} [MeasurableSpace R] [MeasurableSpace Q]

def historyPairEquiv : (n : Nat) →
    History R n × History Q n ≃ᵐ History (R × Q) n
  | 0 =>
      { toFun _ := PUnit.unit
        invFun _ := (PUnit.unit, PUnit.unit)
        left_inv := fun z => by rcases z with ⟨x,y⟩; cases x; cases y; rfl
        right_inv := fun x => by cases x; rfl
        measurable_toFun := measurable_const
        measurable_invFun := measurable_const }
  | n + 1 =>
      { toFun z i := (z.1 i, z.2 i)
        invFun h := (fun i => (h i).1, fun i => (h i).2)
        left_inv := fun z => rfl
        right_inv := fun h => by funext i; exact Prod.eta (h i)
        measurable_toFun := Measurable.of_eval (fun i =>
          ((measurable_pi_apply i).comp measurable_fst).prodMk
            ((measurable_pi_apply i).comp measurable_snd))
        measurable_invFun :=
          (Measurable.of_eval (fun i => (measurable_pi_apply i).fst)).prodMk
            (Measurable.of_eval (fun i => (measurable_pi_apply i).snd)) }

theorem coarseHistory_pair {a b : Nat} (n : Nat)
    (h : History R n) (t : History (HiddenRecord a b) n) :
    coarseHistory n (historyPairEquiv n (h,t)) = h := by
  cases n with
  | zero => cases h; rfl
  | succ n => rfl

theorem historyPair_append (n : Nat) (h : History R n) (t : History Q n)
    (r : R) (q : Q) :
    historyPairEquiv (n+1)
      (appendHistory (R := R) n (h,r), appendHistory (R := Q) n (t,q)) =
      appendHistory (R := R×Q) n (historyPairEquiv n (h,t),(r,q)) := by
  cases n with
  | zero => funext i; rfl
  | succ n =>
      funext i
      by_cases hi : i.val ≤ n
      · simp [historyPairEquiv, appendHistory, prefixStepEquiv,
          MeasurableEquiv.coe_IicProdIoc, IicProdIoc, MeasurableEquiv.piSingleton, hi] <;> rfl
      · simp [historyPairEquiv, appendHistory, prefixStepEquiv,
          MeasurableEquiv.coe_IicProdIoc, IicProdIoc, MeasurableEquiv.piSingleton, hi] <;> rfl

theorem sum_appended_history {E : Type*} [AddCommMonoid E] [Fintype Q]
    (n : Nat) (f : History Q (n+1) → E) :
    (∑ t, f t) = ∑ t : History Q n, ∑ q : Q, f (appendHistory n (t,q)) := by
  classical
  have hs := Fintype.sum_equiv (appendHistory (R := Q) n).toEquiv
    (fun z => f (appendHistory n z)) f (fun _ => rfl)
  calc
    _ = ∑ z : History Q n × Q, f (appendHistory n z) := hs.symm
    _ = _ := by rw [Fintype.sum_prod_type]

theorem history_card_succ [Fintype Q] (n : Nat) :
    Fintype.card (History Q (n+1)) = Fintype.card (History Q n) * Fintype.card Q := by
  have hc := Fintype.card_congr (appendHistory (R := Q) n).toEquiv
  simpa only [Fintype.card_prod] using hc.symm

end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator Topology

universe u
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : Nat} [NeZero a] [NeZero b]
variable (P : MatrixProcess a b R)

structure PendingColumns (a b : Nat) (R : Type u) [MeasurableSpace R] (n : Nat) where
  aliceColumn : History (FineRecord a b R) n → LocalMatrix a
  bobColumn : History (FineRecord a b R) n → LocalMatrix b
  alice_measurable : Measurable aliceColumn
  bob_measurable : Measurable bobColumn

def initialColumns : PendingColumns a b R 0 where
  aliceColumn _ := 1
  bobColumn _ := 1
  alice_measurable := measurable_const
  bob_measurable := measurable_const

theorem measurable_countable_column {Z Q M : Type*}
    [MeasurableSpace Z] [MeasurableSpace Q] [MeasurableSpace M]
    [Countable Q] [MeasurableSingletonClass Q] (K : Z → Q → M)
    (hK : ∀ q, Measurable (fun z => K z q)) :
    Measurable (fun z : Z×Q => K z.1 z.2) :=
  measurable_from_prod_countable_left hK

theorem measurable_alice_column_update {H R Q T M : Type*}
    [MeasurableSpace H] [MeasurableSpace R] [MeasurableSpace Q]
    [MeasurableSpace T] [MeasurableSpace M]
    [Countable Q] [MeasurableSingletonClass Q]
    (turn : H → Bool) (hturn : Measurable turn)
    (K : (H×R) → Q → M) (hK : ∀ q, Measurable (fun z => K z q))
    (C : H → M) (hC : Measurable C) :
    Measurable (fun z : H×(R×(Q×T)) =>
      if turn z.1 = true then K (z.1,z.2.1) z.2.2.1 else C z.1) := by
  have hm := measurable_countable_column K hK
  have hp : Measurable (fun z : H×(R×(Q×T)) => ((z.1,z.2.1),z.2.2.1)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  exact Measurable.ite
    (measurableSet_eq_fun (hturn.comp measurable_fst) measurable_const)
    (hm.comp hp) (hC.comp measurable_fst)

theorem measurable_bob_column_update {H R Q T M : Type*}
    [MeasurableSpace H] [MeasurableSpace R] [MeasurableSpace Q]
    [MeasurableSpace T] [MeasurableSpace M]
    [Countable T] [MeasurableSingletonClass T]
    (turn : H → Bool) (hturn : Measurable turn)
    (K : (H×R) → T → M) (hK : ∀ q, Measurable (fun z => K z q))
    (C : H → M) (hC : Measurable C) :
    Measurable (fun z : H×(R×(Q×T)) =>
      if turn z.1 = true then C z.1 else K (z.1,z.2.1) z.2.2.2) := by
  have hm := measurable_countable_column K hK
  have hp : Measurable (fun z : H×(R×(Q×T)) => ((z.1,z.2.1),z.2.2.2)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  exact Measurable.ite
    (measurableSet_eq_fun (hturn.comp measurable_fst) measurable_const)
    (hC.comp measurable_fst) (hm.comp hp)

namespace MatrixProcess

def fineTurn (n : Nat) (h : History (FineRecord a b R) n) : Bool :=
  P.aliceTurn n (coarseHistory n h)

theorem fineTurn_measurable (n : Nat) : Measurable (P.fineTurn n) :=
  (P.turn_measurable n).comp (measurable_coarseHistory n)

def aliceRecovery (_P : MatrixProcess a b R) (C : PendingColumns a b R n)
    (h : History (FineRecord a b R) n) : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery a a :=
  QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField (Nat.pos_of_ne_zero (NeZero.ne a)) C.aliceColumn h

def bobRecovery (_P : MatrixProcess a b R) (C : PendingColumns a b R n)
    (h : History (FineRecord a b R) n) : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery b b :=
  QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField (Nat.pos_of_ne_zero (NeZero.ne b)) C.bobColumn h

def updateAlice (n : Nat) (C : PendingColumns a b R n)
    (z : History (FineRecord a b R) n × FineRecord a b R) : LocalMatrix a :=
  if P.fineTurn n z.1 = true then
    QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingKraus (P.alice n) (coarseHistory n) C.aliceColumn
      (z.1,z.2.1) z.2.2.1
  else C.aliceColumn z.1

def updateBob (n : Nat) (C : PendingColumns a b R n)
    (z : History (FineRecord a b R) n × FineRecord a b R) : LocalMatrix b :=
  if P.fineTurn n z.1 = true then C.bobColumn z.1
  else QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingKraus (P.bob n) (coarseHistory n) C.bobColumn
    (z.1,z.2.1) z.2.2.2

theorem updateAlice_measurable (n : Nat) (C : PendingColumns a b R n) :
    Measurable (P.updateAlice n C) := by
  exact measurable_alice_column_update (P.fineTurn n) (P.fineTurn_measurable n)
    (QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingKraus (P.alice n) (coarseHistory n) C.aliceColumn)
    (QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.measurable_pendingKraus (P.alice n)
      (coarseHistory n) (measurable_coarseHistory n) C.aliceColumn C.alice_measurable)
    C.aliceColumn C.alice_measurable

theorem updateBob_measurable (n : Nat) (C : PendingColumns a b R n) :
    Measurable (P.updateBob n C) := by
  exact measurable_bob_column_update (P.fineTurn n) (P.fineTurn_measurable n)
    (QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingKraus (P.bob n) (coarseHistory n) C.bobColumn)
    (QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.measurable_pendingKraus (P.bob n)
      (coarseHistory n) (measurable_coarseHistory n) C.bobColumn C.bob_measurable)
    C.bobColumn C.bob_measurable

def nextColumns (n : Nat) (C : PendingColumns a b R n) : PendingColumns a b R (n+1) where
  aliceColumn h := P.updateAlice n C ((appendHistory (R := FineRecord a b R) n).symm h)
  bobColumn h := P.updateBob n C ((appendHistory (R := FineRecord a b R) n).symm h)
  alice_measurable := (P.updateAlice_measurable n C).comp
    (appendHistory (R := FineRecord a b R) n).symm.measurable
  bob_measurable := (P.updateBob_measurable n C).comp
    (appendHistory (R := FineRecord a b R) n).symm.measurable

def pendingColumns (P : MatrixProcess a b R) : (n : Nat) → PendingColumns a b R n
  | 0 => initialColumns
  | n+1 => P.nextColumns n (P.pendingColumns n)

def fineKernel (n : Nat) : Kernel (History (FineRecord a b R) n) (FineRecord a b R) :=
  (P.physicalKernel n).comap (coarseHistory n) (measurable_coarseHistory n) ×ₖ
    Kernel.const (History (FineRecord a b R) n)
      (PMF.uniformOfFintype (HiddenRecord a b)).toMeasure

theorem fineKernel_markov (n : Nat) : IsMarkovKernel (P.fineKernel n) := by
  letI := P.physicalKernel_markov n
  unfold fineKernel
  infer_instance

def aliceFineFilter (n : Nat) (C : PendingColumns a b R n)
    (z : History (FineRecord a b R) n × FineRecord a b R) : LocalMatrix a :=
  QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.alice n)
    (coarseHistory n) C.aliceColumn (z.1,(z.2.1,z.2.2.1))

def bobFineFilter (n : Nat) (C : PendingColumns a b R n)
    (z : History (FineRecord a b R) n × FineRecord a b R) : LocalMatrix b :=
  QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.bob n)
    (coarseHistory n) C.bobColumn (z.1,(z.2.1,z.2.2.2))

theorem aliceFineFilter_measurable (n : Nat) (C : PendingColumns a b R n) :
    Measurable (P.aliceFineFilter n C) :=
  (QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.measurable_pendingRefinedSquare (P.alice n)
    (coarseHistory n) (measurable_coarseHistory n) C.aliceColumn C.alice_measurable).comp
    (by fun_prop)

theorem bobFineFilter_measurable (n : Nat) (C : PendingColumns a b R n) :
    Measurable (P.bobFineFilter n C) :=
  (QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.measurable_pendingRefinedSquare (P.bob n)
    (coarseHistory n) (measurable_coarseHistory n) C.bobColumn C.bob_measurable).comp
    (by fun_prop)

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

variable {A Q T E : Type*} [MeasurableSpace A] [MeasurableSpace Q] [MeasurableSpace T]
variable [Fintype Q] [Nonempty Q] [MeasurableSingletonClass Q]
variable [Fintype T] [Nonempty T] [MeasurableSingletonClass T]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem integrable_common_hidden_left (μ : Measure A) [SFinite μ]
    (f : A × Q → E) (hf : ∀ q, Integrable (fun a => f (a,q)) μ) :
    Integrable (fun z : A × (Q×T) => f (z.1,z.2.1))
      (μ.prod (PMF.uniformOfFintype (Q×T)).toMeasure) :=
  QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.integrable_prod_uniform_columns μ _ (fun q => hf q.1)

 theorem integrable_common_hidden_right (μ : Measure A) [SFinite μ]
    (f : A × T → E) (hf : ∀ q, Integrable (fun a => f (a,q)) μ) :
    Integrable (fun z : A × (Q×T) => f (z.1,z.2.2))
      (μ.prod (PMF.uniformOfFintype (Q×T)).toMeasure) :=
  QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.integrable_prod_uniform_columns μ _ (fun q => hf q.2)

 theorem integral_common_hidden_left (μ : Measure A) [SFinite μ]
    (f : A × Q → E) (hf : ∀ q, Integrable (fun a => f (a,q)) μ) :
    (∫ z : A × (Q×T), f (z.1,z.2.1)
      ∂μ.prod (PMF.uniformOfFintype (Q×T)).toMeasure) =
      ∫ z, f z ∂μ.prod (PMF.uniformOfFintype Q).toMeasure := by
  classical
  have ht : (Fintype.card T : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := T)).ne'
  have hsum (a : A) : (∑ q : Q×T, f (a,q.1)) =
      (Fintype.card T : ℝ) • ∑ q : Q, f (a,q) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ]
    simp_rw [← Nat.cast_smul_eq_nsmul ℝ]
    rw [← Finset.smul_sum]
  rw [QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.integral_prod_uniform_columns μ _ (fun q => hf q.1),
    QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.integral_prod_uniform_columns μ f hf]
  simp_rw [hsum]
  rw [integral_smul, smul_smul]
  congr 1
  simp only [Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  calc
    _ = (Fintype.card Q : ℝ)⁻¹ *
      ((Fintype.card T : ℝ)⁻¹ * (Fintype.card T : ℝ)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ ht, mul_one]

 theorem integral_common_hidden_right (μ : Measure A) [SFinite μ]
    (f : A × T → E) (hf : ∀ q, Integrable (fun a => f (a,q)) μ) :
    (∫ z : A × (Q×T), f (z.1,z.2.2)
      ∂μ.prod (PMF.uniformOfFintype (Q×T)).toMeasure) =
      ∫ z, f z ∂μ.prod (PMF.uniformOfFintype T).toMeasure := by
  classical
  have hq : (Fintype.card Q : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Q)).ne'
  have hsum (a : A) : (∑ q : Q×T, f (a,q.2)) =
      (Fintype.card Q : ℝ) • ∑ q : T, f (a,q) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℝ]
  rw [QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.integral_prod_uniform_columns μ _ (fun q => hf q.2),
    QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.integral_prod_uniform_columns μ f hf]
  simp_rw [hsum]
  rw [integral_smul, smul_smul]
  congr 1
  simp only [Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  calc
    _ = (Fintype.card T : ℝ)⁻¹ *
      ((Fintype.card Q : ℝ)⁻¹ * (Fintype.card Q : ℝ)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hq, mul_one]

end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator
universe u
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : Nat} [NeZero a] [NeZero b]
namespace MatrixProcess
variable (P : MatrixProcess a b R)

 theorem fineKernel_apply_of_alice (n : Nat) (h : History (FineRecord a b R) n)
    (ht : P.fineTurn n h = true) :
    P.fineKernel n h = ((P.alice n).measureKernel (coarseHistory n h)).prod
      (PMF.uniformOfFintype (HiddenRecord a b)).toMeasure := by
  change P.aliceTurn n (coarseHistory n h) = true at ht
  simp only [fineKernel, Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply,
    physicalKernel, Kernel.piecewise_apply, Set.mem_setOf_eq, if_pos ht]

 theorem fineKernel_apply_of_bob (n : Nat) (h : History (FineRecord a b R) n)
    (ht : P.fineTurn n h ≠ true) :
    P.fineKernel n h = ((P.bob n).measureKernel (coarseHistory n h)).prod
      (PMF.uniformOfFintype (HiddenRecord a b)).toMeasure := by
  change P.aliceTurn n (coarseHistory n h) ≠ true at ht
  simp only [fineKernel, Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply,
    physicalKernel, Kernel.piecewise_apply, Set.mem_setOf_eq, if_neg ht]

 theorem aliceFineGram_slice_integrable (n : Nat) (C : PendingColumns a b R n)
    (h : History (FineRecord a b R) n) (q : AliceColumn a) :
    Integrable (fun r =>
      (QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.alice n)
        (coarseHistory n) C.aliceColumn (h,(r,q)))ᴴ *
      QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.alice n)
        (coarseHistory n) C.aliceColumn (h,(r,q)))
      ((P.alice n).measureKernel (coarseHistory n h)) := by
  simp_rw [QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare_gram]
  exact Integrable.smul (Fintype.card (AliceColumn a) : ℝ)
    (QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.integrable_pendingKraus_gram (P.alice n)
      (coarseHistory n) (measurable_coarseHistory n) C.aliceColumn C.alice_measurable h q)

 theorem bobFineGram_slice_integrable (n : Nat) (C : PendingColumns a b R n)
    (h : History (FineRecord a b R) n) (q : BobColumn b) :
    Integrable (fun r =>
      (QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.bob n)
        (coarseHistory n) C.bobColumn (h,(r,q)))ᴴ *
      QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.bob n)
        (coarseHistory n) C.bobColumn (h,(r,q)))
      ((P.bob n).measureKernel (coarseHistory n h)) := by
  simp_rw [QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare_gram]
  exact Integrable.smul (Fintype.card (BobColumn b) : ℝ)
    (QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.integrable_pendingKraus_gram (P.bob n)
      (coarseHistory n) (measurable_coarseHistory n) C.bobColumn C.bob_measurable h q)

 theorem aliceFineGram_integrable (n : Nat) (C : PendingColumns a b R n)
    (h : History (FineRecord a b R) n) (ht : P.fineTurn n h = true) :
    Integrable (fun r => (P.aliceFineFilter n C (h,r))ᴴ * P.aliceFineFilter n C (h,r))
      (P.fineKernel n h) := by
  rw [P.fineKernel_apply_of_alice n h ht]
  let G : R × AliceColumn a → LocalMatrix a := fun z =>
    (QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.alice n)
      (coarseHistory n) C.aliceColumn (h,z))ᴴ *
    QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.alice n)
      (coarseHistory n) C.aliceColumn (h,z)
  change Integrable (fun z : R × (AliceColumn a × BobColumn b) => G (z.1,z.2.1))
    (((P.alice n).measureKernel (coarseHistory n h)).prod
      (PMF.uniformOfFintype (AliceColumn a × BobColumn b)).toMeasure)
  exact integrable_common_hidden_left (Q := AliceColumn a) (T := BobColumn b)
    ((P.alice n).measureKernel (coarseHistory n h)) G
    (P.aliceFineGram_slice_integrable n C h)

 theorem bobFineGram_integrable (n : Nat) (C : PendingColumns a b R n)
    (h : History (FineRecord a b R) n) (ht : P.fineTurn n h ≠ true) :
    Integrable (fun r => (P.bobFineFilter n C (h,r))ᴴ * P.bobFineFilter n C (h,r))
      (P.fineKernel n h) := by
  rw [P.fineKernel_apply_of_bob n h ht]
  let G : R × BobColumn b → LocalMatrix b := fun z =>
    (QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.bob n)
      (coarseHistory n) C.bobColumn (h,z))ᴴ *
    QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.bob n)
      (coarseHistory n) C.bobColumn (h,z)
  change Integrable (fun z : R × (AliceColumn a × BobColumn b) => G (z.1,z.2.2))
    (((P.bob n).measureKernel (coarseHistory n h)).prod
      (PMF.uniformOfFintype (AliceColumn a × BobColumn b)).toMeasure)
  exact integrable_common_hidden_right (Q := AliceColumn a) (T := BobColumn b)
    ((P.bob n).measureKernel (coarseHistory n h)) G
    (P.bobFineGram_slice_integrable n C h)

 theorem aliceFineGram_integral (n : Nat) (C : PendingColumns a b R n)
    (h : History (FineRecord a b R) n) (ht : P.fineTurn n h = true) :
    (∫ r, (P.aliceFineFilter n C (h,r))ᴴ * P.aliceFineFilter n C (h,r)
      ∂P.fineKernel n h) = 1 := by
  rw [P.fineKernel_apply_of_alice n h ht]
  let G : R × AliceColumn a → LocalMatrix a := fun z =>
    (QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.alice n)
      (coarseHistory n) C.aliceColumn (h,z))ᴴ *
    QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.alice n)
      (coarseHistory n) C.aliceColumn (h,z)
  change (∫ z : R × (AliceColumn a × BobColumn b), G (z.1,z.2.1)
    ∂((P.alice n).measureKernel (coarseHistory n h)).prod
      (PMF.uniformOfFintype (AliceColumn a × BobColumn b)).toMeasure) = 1
  rw [integral_common_hidden_left (Q := AliceColumn a) (T := BobColumn b)
    ((P.alice n).measureKernel (coarseHistory n h)) G
    (P.aliceFineGram_slice_integrable n C h)]
  simpa only [G, QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedKernel_apply] using
    QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pending_refined_integral_squareGram (P.alice n)
      (coarseHistory n) (measurable_coarseHistory n) C.aliceColumn C.alice_measurable h

 theorem bobFineGram_integral (n : Nat) (C : PendingColumns a b R n)
    (h : History (FineRecord a b R) n) (ht : P.fineTurn n h ≠ true) :
    (∫ r, (P.bobFineFilter n C (h,r))ᴴ * P.bobFineFilter n C (h,r)
      ∂P.fineKernel n h) = 1 := by
  rw [P.fineKernel_apply_of_bob n h ht]
  let G : R × BobColumn b → LocalMatrix b := fun z =>
    (QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.bob n)
      (coarseHistory n) C.bobColumn (h,z))ᴴ *
    QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.bob n)
      (coarseHistory n) C.bobColumn (h,z)
  change (∫ z : R × (AliceColumn a × BobColumn b), G (z.1,z.2.2)
    ∂((P.bob n).measureKernel (coarseHistory n h)).prod
      (PMF.uniformOfFintype (AliceColumn a × BobColumn b)).toMeasure) = 1
  rw [integral_common_hidden_right (Q := AliceColumn a) (T := BobColumn b)
    ((P.bob n).measureKernel (coarseHistory n h)) G
    (P.bobFineGram_slice_integrable n C h)]
  simpa only [G, QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedKernel_apply] using
    QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pending_refined_integral_squareGram (P.bob n)
      (coarseHistory n) (measurable_coarseHistory n) C.bobColumn C.bob_measurable h

def compiledSquare : SquareProcess a b (FineRecord a b R) where
  kernel := P.fineKernel
  markov := P.fineKernel_markov
  aliceTurn := P.fineTurn
  turn_measurable := P.fineTurn_measurable
  aliceK n h r := P.aliceFineFilter n (P.pendingColumns n) (h,r)
  bobK n h r := P.bobFineFilter n (P.pendingColumns n) (h,r)
  alice_measurable n := P.aliceFineFilter_measurable n (P.pendingColumns n)
  bob_measurable n := P.bobFineFilter_measurable n (P.pendingColumns n)
  alice_integrable n h ht := P.aliceFineGram_integrable n (P.pendingColumns n) h ht
  bob_integrable n h ht := P.bobFineGram_integrable n (P.pendingColumns n) h ht
  alice_complete n h ht := P.aliceFineGram_integral n (P.pendingColumns n) h ht
  bob_complete n h ht := P.bobFineGram_integral n (P.pendingColumns n) h ht

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ComplexConjugate Matrix Kronecker Matrix.Norms.L2Operator

 theorem measurable_leftApplication_apply {Z : Type*} [MeasurableSpace Z]
    {m p n : Nat} (Φ : Z → (LocalMatrix m →ₗ[ℂ] LocalMatrix p))
    (hΦ : QuantumProver.ElegantJointMeasurement.CP.MatrixUnitMeasurable Φ) (X : Z → JointMatrix m n)
    (hX : Measurable X) :
    Measurable (fun z => QuantumProver.ElegantJointMeasurement.CP.leftApplication (Φ z) (X z)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  let B : Z → LocalMatrix m := fun z => Matrix.of (fun x y => X z (x,i.2) (y,j.2))
  have hB : Measurable B := by
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    exact (measurable_pi_apply (y,j.2)).comp
      ((measurable_pi_apply (x,i.2)).comp hX)
  have hm := QuantumProver.ElegantJointMeasurement.CP.measurable_matrixMap_apply Φ hΦ B hB
  exact (measurable_pi_apply j.1).comp ((measurable_pi_apply i.1).comp hm)

 theorem measurable_rightApplication_apply {Z : Type*} [MeasurableSpace Z]
    {m p n : Nat} (Φ : Z → (LocalMatrix n →ₗ[ℂ] LocalMatrix p))
    (hΦ : QuantumProver.ElegantJointMeasurement.CP.MatrixUnitMeasurable Φ) (X : Z → JointMatrix m n)
    (hX : Measurable X) :
    Measurable (fun z => QuantumProver.ElegantJointMeasurement.CP.rightApplication (Φ z) (X z)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  let B : Z → LocalMatrix n := fun z => Matrix.of (fun x y => X z (i.1,x) (j.1,y))
  have hB : Measurable B := by
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    exact (measurable_pi_apply (j.1,y)).comp
      ((measurable_pi_apply (i.1,x)).comp hX)
  have hm := QuantumProver.ElegantJointMeasurement.CP.measurable_matrixMap_apply Φ hΦ B hB
  exact (measurable_pi_apply j.2).comp ((measurable_pi_apply i.2).comp hm)

universe u
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : Nat} [NeZero a] [NeZero b]
namespace MatrixProcess
variable (P : MatrixProcess a b R)

 theorem record_nonempty (P : MatrixProcess a b R) : Nonempty R := by
  letI := P.physicalKernel_markov 0
  exact nonempty_of_isProbabilityMeasure (P.physicalKernel 0 PUnit.unit)

 theorem measurable_pending_apply (n : Nat) (C : PendingColumns a b R n)
    (X : History (FineRecord a b R) n → JointMatrix a b) (hX : Measurable X) :
    Measurable (fun h => QuantumProver.ElegantJointMeasurement.CP.pendingApplication
      (P.aliceRecovery C h) (P.bobRecovery C h) (X h)) := by
  have hA := QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField_matrixUnitMeasurable
    (Nat.pos_of_ne_zero (NeZero.ne a)) C.aliceColumn C.alice_measurable
  have hB := QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField_matrixUnitMeasurable
    (Nat.pos_of_ne_zero (NeZero.ne b)) C.bobColumn C.bob_measurable
  exact measurable_rightApplication_apply _ hB _
    (measurable_leftApplication_apply _ hA X hX)

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator

universe u
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : Nat} [NeZero a] [NeZero b]

namespace MatrixProcess
variable (P : MatrixProcess a b R)

def compiledAction (P : MatrixProcess a b R) : (n : Nat) → History (FineRecord a b R) n →
    JointMatrix a b → JointMatrix a b
  | 0, _, X => X
  | n+1, h, X =>
      let z := (appendHistory (R := FineRecord a b R) n).symm h
      if P.fineTurn n z.1 = true then
        QuantumProver.ElegantJointMeasurement.CP.leftKrausApplication (P.aliceFineFilter n (P.pendingColumns n) z)
          (P.compiledAction n z.1 X)
      else QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication (P.bobFineFilter n (P.pendingColumns n) z)
          (P.compiledAction n z.1 X)

def recoveredCompiledAction (n : Nat) (h : History (FineRecord a b R) n)
    (X : JointMatrix a b) : JointMatrix a b :=
  QuantumProver.ElegantJointMeasurement.CP.pendingApplication
    (P.aliceRecovery (P.pendingColumns n) h)
    (P.bobRecovery (P.pendingColumns n) h)
    (P.compiledAction n h X)

 theorem compiledAction_append (n : Nat)
    (h : History (FineRecord a b R) n) (r : FineRecord a b R)
    (X : JointMatrix a b) :
    P.compiledAction (n+1) (appendHistory n (h,r)) X =
      if P.fineTurn n h = true then
        QuantumProver.ElegantJointMeasurement.CP.leftKrausApplication
          (P.aliceFineFilter n (P.pendingColumns n) (h,r)) (P.compiledAction n h X)
      else QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication
          (P.bobFineFilter n (P.pendingColumns n) (h,r)) (P.compiledAction n h X) := by
  simp only [compiledAction, MeasurableEquiv.symm_apply_apply]

 theorem aliceRecovery_append_of_alice (n : Nat)
    (C : PendingColumns a b R n) (h : History (FineRecord a b R) n)
    (r : R) (q : HiddenRecord a b) (ht : P.fineTurn n h = true) :
    P.aliceRecovery (P.nextColumns n C) (appendHistory n (h,(r,q))) =
      QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedRecovery (P.alice n)
        (coarseHistory n) C.aliceColumn (h,(r,q.1)) := by
  simpa only [aliceRecovery, QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField, nextColumns,
    updateAlice, MeasurableEquiv.symm_apply_apply, if_pos ht,
    QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedRecovery, QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRecovery]

 theorem bobRecovery_append_of_alice (n : Nat)
    (C : PendingColumns a b R n) (h : History (FineRecord a b R) n)
    (r : R) (q : HiddenRecord a b) (ht : P.fineTurn n h = true) :
    P.bobRecovery (P.nextColumns n C) (appendHistory n (h,(r,q))) =
      P.bobRecovery C h := by
  simp only [bobRecovery, QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField, nextColumns,
    updateBob, MeasurableEquiv.symm_apply_apply, if_pos ht]

 theorem aliceRecovery_append_of_bob (n : Nat)
    (C : PendingColumns a b R n) (h : History (FineRecord a b R) n)
    (r : R) (q : HiddenRecord a b) (ht : P.fineTurn n h ≠ true) :
    P.aliceRecovery (P.nextColumns n C) (appendHistory n (h,(r,q))) =
      P.aliceRecovery C h := by
  simp only [aliceRecovery, QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField, nextColumns,
    updateAlice, MeasurableEquiv.symm_apply_apply, if_neg ht]

 theorem bobRecovery_append_of_bob (n : Nat)
    (C : PendingColumns a b R n) (h : History (FineRecord a b R) n)
    (r : R) (q : HiddenRecord a b) (ht : P.fineTurn n h ≠ true) :
    P.bobRecovery (P.nextColumns n C) (appendHistory n (h,(r,q))) =
      QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedRecovery (P.bob n)
        (coarseHistory n) C.bobColumn (h,(r,q.2)) := by
  simpa only [bobRecovery, QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField, nextColumns,
    updateBob, MeasurableEquiv.symm_apply_apply, if_neg ht,
    QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedRecovery, QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRecovery]

 theorem physicalAction_append (n : Nat) (h : History R n) (r : R)
    (X : JointMatrix a b) :
    P.physicalAction (n+1) (appendHistory n (h,r)) X =
      P.physicalLocalDensity n h r (P.physicalAction n h X) := by
  simp only [physicalAction, MeasurableEquiv.symm_apply_apply, LinearMap.comp_apply]

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator

 theorem sum_prod_ignore_right {Q T E : Type*} [Fintype Q] [Fintype T]
    [AddCommMonoid E] [Module ℝ E] (f : Q → E) :
    (∑ q : Q×T, f q.1) = (Fintype.card T : ℝ) • ∑ q : Q, f q := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ]
  simp_rw [← Nat.cast_smul_eq_nsmul ℝ]
  rw [← Finset.smul_sum]

 theorem sum_prod_ignore_left {Q T E : Type*} [Fintype Q] [Fintype T]
    [AddCommMonoid E] [Module ℝ E] (f : T → E) :
    (∑ q : Q×T, f q.2) = (Fintype.card Q : ℝ) • ∑ q : T, f q := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ]

universe u
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : Nat} [NeZero a] [NeZero b]
namespace MatrixProcess
variable (P : MatrixProcess a b R)

 theorem oneStep_hidden_sum (n : Nat) (h : History (FineRecord a b R) n)
    (r : R) (X : JointMatrix a b) :
    (∑ q : HiddenRecord a b,
      P.recoveredCompiledAction (n+1) (appendHistory n (h,(r,q))) X) =
      (Fintype.card (HiddenRecord a b) : ℝ) •
        P.physicalLocalDensity n (coarseHistory n h) r
          (P.recoveredCompiledAction n h X) := by
  classical
  let C := P.pendingColumns n
  let RA := P.aliceRecovery C h
  let RB := P.bobRecovery C h
  by_cases ht : P.fineTurn n h = true
  · let S (q : AliceColumn a) :=
      QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.alice n)
        (coarseHistory n) C.aliceColumn (h,(r,q))
    let Rq (q : AliceColumn a) :=
      QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedRecovery (P.alice n)
        (coarseHistory n) C.aliceColumn (h,(r,q))
    have hbranch (q : HiddenRecord a b) :
        P.recoveredCompiledAction (n+1) (appendHistory n (h,(r,q))) X =
          QuantumProver.ElegantJointMeasurement.CP.pendingApplication (Rq q.1) RB
            (QuantumProver.ElegantJointMeasurement.CP.leftKrausApplication (S q.1) (P.compiledAction n h X)) := by
      rw [recoveredCompiledAction, compiledAction_append, if_pos ht]
      change QuantumProver.ElegantJointMeasurement.CP.pendingApplication
        (P.aliceRecovery (P.nextColumns n C) (appendHistory n (h,(r,q))))
        (P.bobRecovery (P.nextColumns n C) (appendHistory n (h,(r,q))))
        (QuantumProver.ElegantJointMeasurement.CP.leftKrausApplication (S q.1) (P.compiledAction n h X)) = _
      rw [P.aliceRecovery_append_of_alice n C h r q ht,
        P.bobRecovery_append_of_alice n C h r q ht]
    have hlocal (Y : LocalMatrix a) :
        (∑ q, (Rq q).map (S q * Y * (S q)ᴴ)) =
          (Fintype.card (AliceColumn a) : ℝ) •
            (P.alice n).cpDensity (coarseHistory n h) r (RA.map Y) := by
      simpa only [S, Rq, RA, aliceRecovery] using
        QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pending_refined_sum_action (P.alice n)
          (coarseHistory n) C.aliceColumn h r Y
    have hs := left_pending_finite_sum RA RB
      ((P.alice n).cpDensity (coarseHistory n h) r)
      ((P.alice n).cpDensity_completelyPositive (coarseHistory n h) r)
      S Rq (Fintype.card (AliceColumn a)) hlocal (P.compiledAction n h X)
    simp_rw [hbranch]
    rw [sum_prod_ignore_right (T := BobColumn b)
      (fun q : AliceColumn a => QuantumProver.ElegantJointMeasurement.CP.pendingApplication (Rq q) RB
        (QuantumProver.ElegantJointMeasurement.CP.leftKrausApplication (S q) (P.compiledAction n h X))), hs]
    change P.aliceTurn n (coarseHistory n h) = true at ht
    simp only [physicalLocalDensity, if_pos ht, recoveredCompiledAction,
      Fintype.card_prod, Nat.cast_mul, smul_smul]
    congr 1
    exact mul_comm _ _
  · let S (q : BobColumn b) :=
      QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedSquare (P.bob n)
        (coarseHistory n) C.bobColumn (h,(r,q))
    let Rq (q : BobColumn b) :=
      QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRefinedRecovery (P.bob n)
        (coarseHistory n) C.bobColumn (h,(r,q))
    have hbranch (q : HiddenRecord a b) :
        P.recoveredCompiledAction (n+1) (appendHistory n (h,(r,q))) X =
          QuantumProver.ElegantJointMeasurement.CP.pendingApplication RA (Rq q.2)
            (QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication (S q.2) (P.compiledAction n h X)) := by
      rw [recoveredCompiledAction, compiledAction_append, if_neg ht]
      change QuantumProver.ElegantJointMeasurement.CP.pendingApplication
        (P.aliceRecovery (P.nextColumns n C) (appendHistory n (h,(r,q))))
        (P.bobRecovery (P.nextColumns n C) (appendHistory n (h,(r,q))))
        (QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication (S q.2) (P.compiledAction n h X)) = _
      rw [P.aliceRecovery_append_of_bob n C h r q ht,
        P.bobRecovery_append_of_bob n C h r q ht]
    have hlocal (Y : LocalMatrix b) :
        (∑ q, (Rq q).map (S q * Y * (S q)ᴴ)) =
          (Fintype.card (BobColumn b) : ℝ) •
            (P.bob n).cpDensity (coarseHistory n h) r (RB.map Y) := by
      simpa only [S, Rq, RB, bobRecovery] using
        QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pending_refined_sum_action (P.bob n)
          (coarseHistory n) C.bobColumn h r Y
    have hs := right_pending_finite_sum RA RB
      ((P.bob n).cpDensity (coarseHistory n h) r)
      ((P.bob n).cpDensity_completelyPositive (coarseHistory n h) r)
      S Rq (Fintype.card (BobColumn b)) hlocal (P.compiledAction n h X)
    simp_rw [hbranch]
    rw [sum_prod_ignore_left (Q := AliceColumn a)
      (fun q : BobColumn b => QuantumProver.ElegantJointMeasurement.CP.pendingApplication RA (Rq q)
        (QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication (S q) (P.compiledAction n h X))), hs]
    change P.aliceTurn n (coarseHistory n h) ≠ true at ht
    simp only [physicalLocalDensity, if_neg ht, recoveredCompiledAction,
      Fintype.card_prod, Nat.cast_mul, smul_smul]
    rfl

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator
universe u
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : Nat} [NeZero a] [NeZero b]
namespace MatrixProcess
variable (P : MatrixProcess a b R)

 theorem recoveredCompiledAction_zero (X : JointMatrix a b) :
    P.recoveredCompiledAction 0 PUnit.unit X = X := by
  have hA (Y : LocalMatrix a) :
      (P.aliceRecovery (initialColumns (a := a) (b := b) (R := R)) PUnit.unit).map Y = Y := by
    simpa only [aliceRecovery, initialColumns] using
      QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRecovery_identity PUnit.unit Y
  have hB (Y : LocalMatrix b) :
      (P.bobRecovery (initialColumns (a := a) (b := b) (R := R)) PUnit.unit).map Y = Y := by
    simpa only [bobRecovery, initialColumns] using
      QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.pendingRecovery_identity PUnit.unit Y
  have hLA (Y : JointMatrix a b) :
      QuantumProver.ElegantJointMeasurement.CP.leftApplication
        (P.aliceRecovery (initialColumns (a := a) (b := b) (R := R)) PUnit.unit).map Y = Y := by
    ext i j
    change (P.aliceRecovery initialColumns PUnit.unit).map
      (Matrix.of (fun x y => Y (x,i.2) (y,j.2))) i.1 j.1 = _
    rw [hA]
    rfl
  have hRB (Y : JointMatrix a b) :
      QuantumProver.ElegantJointMeasurement.CP.rightApplication
        (P.bobRecovery (initialColumns (a := a) (b := b) (R := R)) PUnit.unit).map Y = Y := by
    ext i j
    change (P.bobRecovery initialColumns PUnit.unit).map
      (Matrix.of (fun x y => Y (i.1,x) (j.1,y))) i.2 j.2 = _
    rw [hB]
    rfl
  change QuantumProver.ElegantJointMeasurement.CP.rightApplication
    (P.bobRecovery initialColumns PUnit.unit).map
    (QuantumProver.ElegantJointMeasurement.CP.leftApplication (P.aliceRecovery initialColumns PUnit.unit).map X) = X
  rw [hLA, hRB]

 theorem sum_recoveredCompiledAction (n : Nat) (h : History R n)
    (X : JointMatrix a b) :
    (∑ t : History (HiddenRecord a b) n,
      P.recoveredCompiledAction n (historyPairEquiv n (h,t)) X) =
      (Fintype.card (History (HiddenRecord a b) n) : ℝ) •
        P.physicalAction n h X := by
  induction n with
  | zero =>
      cases h
      simpa only [historyPairEquiv, Fintype.sum_unique, Fintype.card_unique,
        Nat.cast_one, one_smul, physicalAction, LinearMap.id_apply] using
        P.recoveredCompiledAction_zero X
  | succ n ih =>
      obtain ⟨⟨h,r⟩,rfl⟩ := (appendHistory (R := R) n).surjective h
      rw [sum_appended_history n (fun t : History (HiddenRecord a b) (n+1) =>
        P.recoveredCompiledAction (n+1)
          (historyPairEquiv (n+1) (appendHistory (R := R) n (h,r),t)) X)]
      calc
        _ = ∑ t : History (HiddenRecord a b) n, ∑ q : HiddenRecord a b,
            P.recoveredCompiledAction (n+1)
              (appendHistory (R := FineRecord a b R) n
                (historyPairEquiv n (h,t),(r,q))) X := by
          apply Finset.sum_congr rfl
          intro t _
          apply Finset.sum_congr rfl
          intro q _
          exact congrArg (fun w => P.recoveredCompiledAction (n+1) w X)
            (historyPair_append (R := R) (Q := HiddenRecord a b) n h t r q)
        _ = ∑ t : History (HiddenRecord a b) n,
            (Fintype.card (HiddenRecord a b) : ℝ) •
              P.physicalLocalDensity n h r
                (P.recoveredCompiledAction n (historyPairEquiv n (h,t)) X) := by
          apply Finset.sum_congr rfl
          intro t _
          simpa only [coarseHistory_pair] using
            P.oneStep_hidden_sum n (historyPairEquiv n (h,t)) r X
        _ = (Fintype.card (HiddenRecord a b) : ℝ) •
            P.physicalLocalDensity n h r
              (∑ t : History (HiddenRecord a b) n,
                P.recoveredCompiledAction n (historyPairEquiv n (h,t)) X) := by
          rw [← Finset.smul_sum, ← map_sum]
        _ = (Fintype.card (HiddenRecord a b) : ℝ) •
            ((Fintype.card (History (HiddenRecord a b) n) : ℝ) •
              P.physicalLocalDensity n h r (P.physicalAction n h X)) := by
          rw [ih, LinearMap.map_smul_of_tower]
        _ = _ := by
          rw [smul_smul, history_card_succ, Nat.cast_mul, physicalAction_append]
          congr 1
          exact mul_comm _ _

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ComplexConjugate Matrix Kronecker Matrix.Norms.L2Operator
universe u
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : Nat} [NeZero a] [NeZero b]
namespace MatrixProcess
variable (P : MatrixProcess a b R)

 theorem physicalLocalDensity_measurable_apply (n : Nat)
    (X : History R n × R → JointMatrix a b) (hX : Measurable X) :
    Measurable (fun z => P.physicalLocalDensity n z.1 z.2 (X z)) := by
  have heq : (fun z : History R n×R => P.physicalLocalDensity n z.1 z.2 (X z)) =
      (fun z : History R n×R => if P.aliceTurn n z.1 = true then
        QuantumProver.ElegantJointMeasurement.CP.leftApplication ((P.alice n).cpDensity z.1 z.2) (X z)
        else QuantumProver.ElegantJointMeasurement.CP.rightApplication ((P.bob n).cpDensity z.1 z.2) (X z)) := by
    funext z
    unfold physicalLocalDensity
    split_ifs <;> rfl
  rw [heq]
  apply Measurable.ite
  · exact measurableSet_eq_fun ((P.turn_measurable n).comp measurable_fst)
      (measurable_const (a := true))
  · exact measurable_leftApplication_apply _
      (fun i j c d => (P.alice n).cpDensity_joint_coordinate_measurable i j c d) X hX
  · exact measurable_rightApplication_apply _
      (fun i j c d => (P.bob n).cpDensity_joint_coordinate_measurable i j c d) X hX

 theorem physicalAction_measurable (n : Nat) (X : JointMatrix a b) :
    Measurable (fun h => P.physicalAction n h X) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hm := P.physicalLocalDensity_measurable_apply n
        (fun z => P.physicalAction n z.1 X) (ih.comp measurable_fst)
      convert hm.comp (appendHistory (R := R) n).symm.measurable using 1 <;> rfl

 theorem compiledAction_measurable (n : Nat) (X : JointMatrix a b) :
    Measurable (fun h => P.compiledAction n h X) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hY : Measurable (fun z : History (FineRecord a b R) n × FineRecord a b R =>
          P.compiledAction n z.1 X) := ih.comp measurable_fst
      have hA : Measurable (fun z : History (FineRecord a b R) n × FineRecord a b R =>
          P.aliceFineFilter n (P.pendingColumns n) z ⊗ₖ (1 : LocalMatrix b)) :=
        (tensorLeft a b).continuous.measurable.comp
          (P.aliceFineFilter_measurable n (P.pendingColumns n))
      have hB : Measurable (fun z : History (FineRecord a b R) n × FineRecord a b R =>
          (1 : LocalMatrix a) ⊗ₖ P.bobFineFilter n (P.pendingColumns n) z) :=
        (tensorRight a b).continuous.measurable.comp
          (P.bobFineFilter_measurable n (P.pendingColumns n))
      have hm : Measurable (fun z : History (FineRecord a b R) n × FineRecord a b R =>
          if P.fineTurn n z.1 = true then
            QuantumProver.ElegantJointMeasurement.CP.leftKrausApplication (P.aliceFineFilter n (P.pendingColumns n) z)
              (P.compiledAction n z.1 X)
          else QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication (P.bobFineFilter n (P.pendingColumns n) z)
              (P.compiledAction n z.1 X)) := by
        apply Measurable.ite
        · exact measurableSet_eq_fun ((P.fineTurn_measurable n).comp measurable_fst)
            (measurable_const (a := true))
        · exact (hA.mul hY).mul (continuous_star.measurable.comp hA)
        · exact (hB.mul hY).mul (continuous_star.measurable.comp hB)
      exact hm.comp (appendHistory (R := FineRecord a b R) n).symm.measurable

 theorem recoveredCompiledAction_measurable (n : Nat) (X : JointMatrix a b) :
    Measurable (fun h => P.recoveredCompiledAction n h X) :=
  P.measurable_pending_apply n (P.pendingColumns n) _ (P.compiledAction_measurable n X)

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator
universe u
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : Nat} [NeZero a] [NeZero b]
namespace MatrixProcess
variable (P : MatrixProcess a b R)

def compiledPathOp (P : MatrixProcess a b R) : (n : Nat) →
    History (FineRecord a b R) n → JointMatrix a b
  | 0, _ => 1
  | n+1, h =>
      let z := (appendHistory (R := FineRecord a b R) n).symm h
      P.compiledSquare.localOp n z.1 z.2 * P.compiledPathOp n z.1

 theorem compiledSquare_localOp (n : Nat)
    (h : History (FineRecord a b R) n) (r : FineRecord a b R) :
    P.compiledSquare.localOp n h r =
      if P.fineTurn n h = true then
        P.aliceFineFilter n (P.pendingColumns n) (h,r) ⊗ₖ (1 : LocalMatrix b)
      else (1 : LocalMatrix a) ⊗ₖ P.bobFineFilter n (P.pendingColumns n) (h,r) := rfl

 theorem compiledAction_eq_sandwich (n : Nat) (h : History (FineRecord a b R) n)
    (X : JointMatrix a b) :
    P.compiledAction n h X = P.compiledPathOp n h * X * (P.compiledPathOp n h)ᴴ := by
  induction n with
  | zero => simp only [compiledAction, compiledPathOp, Matrix.one_mul,
      Matrix.conjTranspose_one, Matrix.mul_one]
  | succ n ih =>
      let z := (appendHistory (R := FineRecord a b R) n).symm h
      change (if P.fineTurn n z.1 = true then
          QuantumProver.ElegantJointMeasurement.CP.leftKrausApplication (P.aliceFineFilter n (P.pendingColumns n) z)
            (P.compiledAction n z.1 X)
        else QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication (P.bobFineFilter n (P.pendingColumns n) z)
            (P.compiledAction n z.1 X)) =
        (P.compiledSquare.localOp n z.1 z.2 * P.compiledPathOp n z.1) * X *
          (P.compiledSquare.localOp n z.1 z.2 * P.compiledPathOp n z.1)ᴴ
      rw [ih z.1, P.compiledSquare_localOp]
      by_cases ht : P.fineTurn n z.1 = true
      · simp only [if_pos ht, QuantumProver.ElegantJointMeasurement.CP.leftKrausApplication,
          Matrix.conjTranspose_mul, Matrix.mul_assoc]
      · simp only [if_neg ht, QuantumProver.ElegantJointMeasurement.CP.rightKrausApplication,
          Matrix.conjTranspose_mul, Matrix.mul_assoc]

 theorem compiledPathOp_eq_squarePath (N : Nat) (h : Prefix (FineRecord a b R) N) :
    P.compiledPathOp (N+1) h = P.compiledSquare.pathOp N h := by
  induction N with
  | zero =>
      change P.compiledSquare.localOp 0 PUnit.unit (firstRecordEquiv.symm h) * 1 =
        P.compiledSquare.localOp 0 PUnit.unit (firstRecordEquiv.symm h)
      exact Matrix.mul_one _
  | succ N ih =>
      change P.compiledSquare.localOp (N+1)
          ((prefixStepEquiv N).symm h).1 ((prefixStepEquiv N).symm h).2 *
          P.compiledPathOp (N+1) ((prefixStepEquiv N).symm h).1 = _
      rw [ih]
      rfl

 theorem compiledAction_eq_squarePath (N : Nat) (h : Prefix (FineRecord a b R) N)
    (X : JointMatrix a b) :
    P.compiledAction (N+1) h X = P.compiledSquare.pathOp N h * X *
      (P.compiledSquare.pathOp N h)ᴴ := by
  rw [P.compiledAction_eq_sandwich, P.compiledPathOp_eq_squarePath]

 theorem norm_joint_sandwich_le_gram (V X : JointMatrix a b) :
    ‖V * X * Vᴴ‖ ≤ ‖X‖ * ‖Vᴴ * V‖ := by
  calc
    ‖V * X * Vᴴ‖ ≤ ‖V * X‖ * ‖Vᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖V‖ * ‖X‖) * ‖Vᴴ‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul V X) (norm_nonneg _)
    _ = _ := by
      rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose_mul_self]
      ring

 theorem compiledAction_integrable (N : Nat) (X : JointMatrix a b) :
    Integrable (fun h => P.compiledAction (N+1) h X) (P.compiledSquare.prefixMeasure N) := by
  have hV := P.compiledSquare.measurable_pathOp N
  have hm : Measurable (fun h => P.compiledSquare.pathOp N h * X *
      (P.compiledSquare.pathOp N h)ᴴ) :=
    (hV.mul measurable_const).mul (continuous_star.measurable.comp hV)
  simp_rw [P.compiledAction_eq_squarePath]
  apply ((P.compiledSquare.pathGram_integrable N).norm.const_mul ‖X‖).mono'
  · exact hm.stronglyMeasurable.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun h => norm_joint_sandwich_le_gram _ X

 theorem recoveredCompiledAction_integrable (N : Nat) (X : JointMatrix a b) :
    Integrable (fun h => P.recoveredCompiledAction (N+1) h X)
      (P.compiledSquare.prefixMeasure N) := by
  apply ((P.compiledAction_integrable N X).norm.const_mul ((a*b : Nat) : ℝ)).mono'
  · exact (P.recoveredCompiledAction_measurable (N+1) X).stronglyMeasurable.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun h =>
      QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare.norm_pendingApplication_apply_le _ _ _

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators

variable {Q T : Type*} [MeasurableSpace Q] [MeasurableSpace T]
variable [Fintype Q] [Fintype T] [Nonempty Q] [Nonempty T]
variable [MeasurableSingletonClass Q] [MeasurableSingletonClass T]

 theorem uniform_product_measure :
    (PMF.uniformOfFintype (Q×T)).toMeasure =
      (PMF.uniformOfFintype Q).toMeasure.prod (PMF.uniformOfFintype T).toMeasure := by
  apply Measure.ext_of_singleton
  intro z
  have hp : ((PMF.uniformOfFintype Q).toMeasure.prod
      (PMF.uniformOfFintype T).toMeasure) {z} =
      (PMF.uniformOfFintype Q).toMeasure {z.1} *
        (PMF.uniformOfFintype T).toMeasure {z.2} := by
    rw [show ({z} : Set (Q×T)) = {z.1} ×ˢ {z.2} by ext x; simp,
      Measure.prod_prod]
  rw [hp,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.uniformOfFintype_apply,
    Fintype.card_prod, Nat.cast_mul]
  exact ENNReal.mul_inv (by right; simp) (by left; simp)

 theorem uniform_measure_map_equiv (e : Q ≃ᵐ T) :
    (PMF.uniformOfFintype Q).toMeasure.map e = (PMF.uniformOfFintype T).toMeasure := by
  apply Measure.ext_of_singleton
  intro t
  rw [Measure.map_apply e.measurable (measurableSet_singleton t)]
  have hp : e ⁻¹' ({t} : Set T) = {e.symm t} := by
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact e.apply_eq_iff_eq_symm_apply
  rw [hp,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [PMF.uniformOfFintype_apply,
    Fintype.card_congr e.toEquiv]

instance historyNonempty (n : Nat) :
    Nonempty (History Q n) :=
  match n with
  | 0 => inferInstanceAs (Nonempty PUnit)
  | n+1 => inferInstanceAs (Nonempty (Prefix Q n))

instance historyMeasurableSingleton (n : Nat) : MeasurableSingletonClass (History Q n) :=
  match n with
  | 0 => inferInstanceAs (MeasurableSingletonClass PUnit)
  | n+1 => inferInstanceAs (MeasurableSingletonClass (Prefix Q n))

 theorem uniform_history_successor (n : Nat) :
    ((PMF.uniformOfFintype (History Q n)).toMeasure.prod
      (PMF.uniformOfFintype Q).toMeasure).map (appendHistory (R := Q) n) =
      (PMF.uniformOfFintype (History Q (n+1))).toMeasure := by
  rw [← uniform_product_measure]
  exact uniform_measure_map_equiv (appendHistory (R := Q) n)

end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
open MeasureTheory ProbabilityTheory Set Function

def recordShuffle {A T R Q : Type*}
    [MeasurableSpace A] [MeasurableSpace T] [MeasurableSpace R] [MeasurableSpace Q] :
    ((A×T)×(R×Q)) ≃ᵐ ((A×R)×(T×Q)) where
  toEquiv :=
    { toFun := fun z => ((z.1.1,z.2.1),(z.1.2,z.2.2))
      invFun := fun z => ((z.1.1,z.2.1),(z.1.2,z.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  measurable_toFun := by
    change Measurable (fun z : ((A×T)×(R×Q)) => ((z.1.1,z.2.1),(z.1.2,z.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ((A×R)×(T×Q)) => ((z.1.1,z.2.1),(z.1.2,z.2.2)))
    fun_prop

theorem compProd_independent_shuffle {A T R Q : Type*}
    [MeasurableSpace A] [MeasurableSpace T] [MeasurableSpace R] [MeasurableSpace Q]
    (μ : Measure A) (ν : Measure T) (ζ : Measure Q)
    [SFinite μ] [SFinite ν] [SFinite ζ]
    (κ : Kernel A R) [IsSFiniteKernel κ] :
    ((μ.prod ν).compProd
      ((κ.comap Prod.fst measurable_fst) ×ₖ Kernel.const (A×T) ζ)).map recordShuffle =
      (μ.compProd κ).prod (ν.prod ζ) := by
  let K : Kernel (A×T) (R×Q) :=
    (κ.comap Prod.fst measurable_fst) ×ₖ Kernel.const (A×T) ζ
  apply Measure.ext_of_lintegral
  intro f hf
  have hg : Measurable (fun z : (A×T)×(R×Q) => f (recordShuffle z)) :=
    hf.comp recordShuffle.measurable
  have houter : Measurable (fun ht : A×T => ∫⁻ rq, f (recordShuffle (ht,rq)) ∂K ht) :=
    hg.lintegral_kernel_prod_right'
  rw [lintegral_map_equiv f recordShuffle, Measure.lintegral_compProd hg,
    lintegral_prod _ houter.aemeasurable]
  have hslice (ht : A×T) : Measurable (fun rq : R×Q => f ((ht.1,rq.1),(ht.2,rq.2))) :=
    hf.comp (by fun_prop)
  simp only [K, Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply]
  change (∫⁻ h, ∫⁻ t, ∫⁻ rq, f ((h,rq.1),(t,rq.2)) ∂(κ h).prod ζ ∂ν ∂μ) = _
  have hprod (h : A) (t : T) :
      (∫⁻ rq, f ((h,rq.1),(t,rq.2)) ∂(κ h).prod ζ) =
        ∫⁻ r, ∫⁻ q, f ((h,r),(t,q)) ∂ζ ∂κ h :=
    lintegral_prod _ (hslice (h,t)).aemeasurable
  simp_rw [hprod]
  have hright : Measurable (fun ar : A×R =>
      ∫⁻ tq, f (ar,tq) ∂ν.prod ζ) := hf.lintegral_prod_right'
  rw [lintegral_prod _ hf.aemeasurable, Measure.lintegral_compProd hright]
  apply lintegral_congr
  intro h
  have hq : Measurable (fun tr : T×R => ∫⁻ q, f ((h,tr.2),(tr.1,q)) ∂ζ) :=
    (hf.comp (show Measurable (fun z : (T×R)×Q =>
      ((h,z.1.2),(z.1.1,z.2))) by fun_prop)).lintegral_prod_right'
  rw [lintegral_lintegral_swap hq.aemeasurable]
  apply lintegral_congr
  intro r
  exact (lintegral_prod _ ((hf.comp (measurable_const.prodMk measurable_id)).aemeasurable)).symm

end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators

theorem compProd_map_left_equiv {A B R : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace R]
    (μ : Measure A) [SFinite μ] (e : A ≃ᵐ B)
    (κ : Kernel B R) [IsSFiniteKernel κ] :
    (μ.map e).compProd κ =
      (μ.compProd (κ.comap e e.measurable)).map
        (e.prodCongr (MeasurableEquiv.refl R)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_compProd hf, lintegral_map_equiv _ e,
    lintegral_map_equiv f (e.prodCongr (MeasurableEquiv.refl R))]
  have hmeas : Measurable (fun z : A×R => f ((e.prodCongr (MeasurableEquiv.refl R)) z)) :=
    hf.comp (e.prodCongr (MeasurableEquiv.refl R)).measurable
  rw [Measure.lintegral_compProd hmeas]
  rfl

universe u
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : Nat} [NeZero a] [NeZero b]
namespace MatrixProcess
variable (P : MatrixProcess a b R)

def finePrefixMeasure (P : MatrixProcess a b R) : (n : Nat) →
    Measure (History (FineRecord a b R) n)
  | 0 => Measure.dirac PUnit.unit
  | n+1 => ((P.finePrefixMeasure n).compProd (P.fineKernel n)).map
      (appendHistory (R := FineRecord a b R) n)

theorem finePrefixMeasure_probability (n : Nat) :
    IsProbabilityMeasure (P.finePrefixMeasure n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ n ih =>
      letI := ih
      letI := P.fineKernel_markov n
      constructor
      rw [finePrefixMeasure,
        Measure.map_apply (appendHistory (R := FineRecord a b R) n).measurable
          MeasurableSet.univ]
      simp

theorem finePrefixMeasure_eq_square (N : Nat) :
    P.finePrefixMeasure (N+1) = P.compiledSquare.prefixMeasure N := by
  induction N with
  | zero =>
      letI := P.fineKernel_markov 0
      change ((Measure.dirac PUnit.unit).compProd (P.fineKernel 0)).map
        (appendHistory (R := FineRecord a b R) 0) = _
      apply Measure.ext_of_lintegral
      intro f hf
      rw [lintegral_map_equiv f (appendHistory 0)]
      have hmeas : Measurable (fun z : History (FineRecord a b R) 0 × FineRecord a b R =>
          f ((appendHistory 0) z)) := hf.comp (appendHistory 0).measurable
      rw [Measure.lintegral_compProd hmeas,
        lintegral_dirac' _ hmeas.lintegral_kernel_prod_right']
      change (∫⁻ r, f (firstRecordEquiv r) ∂P.fineKernel 0 PUnit.unit) =
        ∫⁻ h, f h ∂(P.fineKernel 0 PUnit.unit).map firstRecordEquiv
      exact (lintegral_map_equiv f firstRecordEquiv).symm
  | succ N ih =>
      change ((P.finePrefixMeasure (N+1)).compProd (P.fineKernel (N+1))).map
          (appendHistory (N+1)) = _
      rw [ih]
      rfl

theorem finePrefixMeasure_factorization (n : Nat) :
    P.finePrefixMeasure n =
      ((P.represented_physicalPrefixMeasure n).prod
        (PMF.uniformOfFintype (History (HiddenRecord a b) n)).toMeasure).map
          (historyPairEquiv n) := by
  induction n with
  | zero =>
      have hu : (PMF.uniformOfFintype (History (HiddenRecord a b) 0)).toMeasure =
          Measure.dirac PUnit.unit := by
        apply Measure.ext_of_singleton
        intro t
        cases t
        rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
        simp only [PMF.uniformOfFintype_apply,
          Fintype.card_unique, Nat.cast_one, inv_one, Measure.dirac_apply_of_mem
            (Set.mem_singleton PUnit.unit)]
      simp only [finePrefixMeasure, represented_physicalPrefixMeasure, hu,
        Measure.dirac_prod_dirac, Measure.map_dirac' (historyPairEquiv 0).measurable]
  | succ n ih =>
      let μ := P.represented_physicalPrefixMeasure n
      let ν := (PMF.uniformOfFintype (History (HiddenRecord a b) n)).toMeasure
      let ζ := (PMF.uniformOfFintype (HiddenRecord a b)).toMeasure
      let κ := P.physicalKernel n
      letI := P.represented_physicalPrefixMeasure_probability n
      letI := P.physicalKernel_markov n
      letI := P.fineKernel_markov n
      have hk : (P.fineKernel n).comap (historyPairEquiv n) (historyPairEquiv n).measurable =
          (κ.comap Prod.fst measurable_fst) ×ₖ
            Kernel.const (History R n×History (HiddenRecord a b) n) ζ := by
        ext ht : 1
        rcases ht with ⟨h,t⟩
        simp only [Kernel.comap_apply, fineKernel, Kernel.prod_apply, Kernel.const_apply]
        change ((P.physicalKernel n) (coarseHistory n (historyPairEquiv n (h,t)))).prod ζ =
          (κ h).prod ζ
        rw [coarseHistory_pair]
      let H := (historyPairEquiv (n+1)) ∘
        (Prod.map (appendHistory (R := R) n) (appendHistory (R := HiddenRecord a b) n))
      have hmH : Measurable H := (historyPairEquiv (n+1)).measurable.comp
        ((appendHistory (R := R) n).measurable.prodMap
          (appendHistory (R := HiddenRecord a b) n).measurable)
      have hF : (appendHistory (R := FineRecord a b R) n) ∘
          (historyPairEquiv n).prodCongr (MeasurableEquiv.refl (FineRecord a b R)) =
          H ∘ recordShuffle := by
        funext z
        exact (historyPair_append n z.1.1 z.1.2 z.2.1 z.2.2).symm
      rw [finePrefixMeasure, ih, compProd_map_left_equiv, hk,
        Measure.map_map (appendHistory (R := FineRecord a b R) n).measurable
          ((historyPairEquiv n).prodCongr (MeasurableEquiv.refl (FineRecord a b R))).measurable,
        hF, ← Measure.map_map hmH recordShuffle.measurable,
        compProd_independent_shuffle μ ν ζ κ]
      rw [show H = (historyPairEquiv (n+1)) ∘
        Prod.map (appendHistory (R := R) n) (appendHistory (R := HiddenRecord a b) n) from rfl,
        ← Measure.map_map (historyPairEquiv (n+1)).measurable
          ((appendHistory (R := R) n).measurable.prodMap
            (appendHistory (R := HiddenRecord a b) n).measurable),
        ← Measure.map_prod_map _ _ (appendHistory (R := R) n).measurable
          (appendHistory (R := HiddenRecord a b) n).measurable,
        uniform_history_successor]
      rfl

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator
universe u
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : Nat} [NeZero a] [NeZero b]
namespace MatrixProcess
variable (P : MatrixProcess a b R)

theorem integral_hidden_recovered_action (n : Nat) (h : History R n)
    (X : JointMatrix a b) :
    (∫ t, P.recoveredCompiledAction n (historyPairEquiv n (h,t)) X
      ∂(PMF.uniformOfFintype (History (HiddenRecord a b) n)).toMeasure) =
      P.physicalAction n h X := by
  classical
  have hc : (Fintype.card (History (HiddenRecord a b) n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  simp only [PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← Finset.smul_sum, P.sum_recoveredCompiledAction, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

theorem physicalAction_integrable (N : Nat) (X : JointMatrix a b) :
    Integrable (fun h => P.physicalAction (N+1) h X) (P.represented_physicalPrefixMeasure (N+1)) := by
  have hi := P.recoveredCompiledAction_integrable N X
  rw [← P.finePrefixMeasure_eq_square N, P.finePrefixMeasure_factorization] at hi
  have hp := (integrable_map_equiv (historyPairEquiv (N+1))
    (fun h => P.recoveredCompiledAction (N+1) h X)).mp hi
  have ha := hp.integral_prod_left
  simpa only [Function.comp_apply, P.integral_hidden_recovered_action] using ha

theorem physicalPrefixAction_eq_recoveredCompiledAction (N : Nat)
    (B : Set (Prefix R N)) (hB : MeasurableSet B) (X : JointMatrix a b) :
    P.represented_physicalPrefixAction (N+1) B X =
      ∫ h in (coarseHistory (N+1)) ⁻¹' B,
        P.recoveredCompiledAction (N+1) h X ∂P.compiledSquare.prefixMeasure N := by
  letI := P.represented_physicalPrefixMeasure_probability (N+1)
  let D : Set (Prefix (FineRecord a b R) N) := (coarseHistory (a := a) (b := b) (N+1)) ⁻¹' B
  have hD : MeasurableSet D := hB.preimage (measurable_coarseHistory (N+1))
  have hi := (P.recoveredCompiledAction_integrable N X).indicator hD
  rw [← P.finePrefixMeasure_eq_square N, P.finePrefixMeasure_factorization] at hi
  have hp := (integrable_map_equiv (historyPairEquiv (N+1))
    (D.indicator (fun h => P.recoveredCompiledAction (N+1) h X))).mp hi
  rw [represented_physicalPrefixAction, ← integral_indicator hB, ← integral_indicator hD,
    ← P.finePrefixMeasure_eq_square N, P.finePrefixMeasure_factorization,
    integral_map_equiv]
  rw [integral_prod (fun z : History R (N+1) × History (HiddenRecord a b) (N+1) =>
    D.indicator (fun h => P.recoveredCompiledAction (N+1) h X)
      (historyPairEquiv (N+1) z)) hp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun h => by
    by_cases hb : h ∈ B
    · have hd (t : History (HiddenRecord a b) (N+1)) : historyPairEquiv (N+1) (h,t) ∈ D := by
        change h ∈ B
        exact hb
      simp_rw [Set.indicator_of_mem hb, Set.indicator_of_mem (hd _)]
      exact (P.integral_hidden_recovered_action (N+1) h X).symm
    · have hd (t : History (HiddenRecord a b) (N+1)) : historyPairEquiv (N+1) (h,t) ∉ D := by
        change h ∉ B
        exact hb
      simp only [Set.indicator_of_notMem hb, Set.indicator_of_notMem (hd _), integral_zero]

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
open MeasureTheory ProbabilityTheory Set Function Preorder
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator
universe u
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : Nat} [NeZero a] [NeZero b]

def traceComplexCLM (a b : Nat) : JointMatrix a b →L[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin a×Fin b) ℂ ℂ : JointMatrix a b →ₗ[ℂ] ℂ).toContinuousLinearMap

namespace MatrixProcess
variable (P : MatrixProcess a b R)

def represented_physicalCylinderEffect (N : Nat) (B : Set (Prefix R N)) : JointMatrix a b :=
  fun i j => (P.represented_physicalPrefixAction (N+1) B (Matrix.single j i (1:ℂ))).trace

theorem physicalCylinderEffect_eq_compiled (N : Nat)
    (B : Set (Prefix R N)) (hB : MeasurableSet B) :
    P.represented_physicalCylinderEffect N B =
      P.compiledSquare.cylinderEffect N ((coarseHistory (N+1)) ⁻¹' B) := by
  classical
  let D : Set (Prefix (FineRecord a b R) N) := (coarseHistory (a := a) (b := b) (N+1)) ⁻¹' B
  ext i j
  change (P.represented_physicalPrefixAction (N+1) B (Matrix.single j i (1:ℂ))).trace = _
  rw [P.physicalPrefixAction_eq_recoveredCompiledAction N B hB]
  have hi := (P.recoveredCompiledAction_integrable N (Matrix.single j i (1:ℂ))).integrableOn
    (s := D)
  change traceComplexCLM a b
    (∫ h in D, P.recoveredCompiledAction (N+1) h (Matrix.single j i (1:ℂ))
      ∂P.compiledSquare.prefixMeasure N) =
    SquareProcess.entryCLM i j (∫ h in D, P.compiledSquare.pathGram N h
      ∂P.compiledSquare.prefixMeasure N)
  rw [← (traceComplexCLM a b).integral_comp_comm hi]
  have hpoint (h : Prefix (FineRecord a b R) N) :
      traceComplexCLM a b
        (P.recoveredCompiledAction (N+1) h (Matrix.single j i (1:ℂ))) =
      P.compiledSquare.pathGram N h i j := by
    change (QuantumProver.ElegantJointMeasurement.CP.pendingApplication _ _
      (P.compiledAction (N+1) h (Matrix.single j i (1:ℂ)))).trace = _
    rw [QuantumProver.ElegantJointMeasurement.CP.pendingApplication_trace, P.compiledAction_eq_squarePath]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_single]
    simp [SquareProcess.pathGram]
  simp_rw [hpoint]
  change (∫ h in D, SquareProcess.entryCLM i j (P.compiledSquare.pathGram N h)
      ∂P.compiledSquare.prefixMeasure N) =
    SquareProcess.entryCLM i j (∫ h in D, P.compiledSquare.pathGram N h ∂P.compiledSquare.prefixMeasure N)
  exact (SquareProcess.entryCLM i j).integral_comp_comm
    (P.compiledSquare.pathGram_integrable N).integrableOn

def represented_physicalCylinderPOVM : QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.ConsistentCylinderPOVM R (Fin a×Fin b) where
  effect := P.represented_physicalCylinderEffect
  empty := by intro n; ext i j; simp [represented_physicalCylinderEffect, represented_physicalPrefixAction]
  positive := by
    intro n B hB
    rw [P.physicalCylinderEffect_eq_compiled n B hB]
    exact P.compiledSquare.cylinderEffect_posSemidef n _
  total := by
    intro n
    rw [P.physicalCylinderEffect_eq_compiled n univ MeasurableSet.univ]
    simpa using P.compiledSquare.cylinderEffect_univ n
  coordinate_additive := by
    intro n B hB hd i j
    simp_rw [P.physicalCylinderEffect_eq_compiled n _ (hB _)]
    rw [P.physicalCylinderEffect_eq_compiled n _ (MeasurableSet.iUnion hB), Set.preimage_iUnion]
    exact P.compiledSquare.cylinderEffect_coordinate_additive n _
      (fun k => (hB k).preimage (measurable_coarseHistory (n+1)))
      (hd.mono fun _ _ => Disjoint.preimage _) i j
  consistent := by
    intro n m hnm B hB
    have hpre : (coarseHistory (m+1)) ⁻¹'
        ((frestrictLe₂ (π := fun _ => R) hnm) ⁻¹' B) =
      (frestrictLe₂ (π := fun _ => FineRecord a b R) hnm) ⁻¹'
        ((coarseHistory (n+1)) ⁻¹' B) := rfl
    rw [P.physicalCylinderEffect_eq_compiled m _
      (hB.preimage (SquareProcess.measurable_prefixRestrict hnm)),
      P.physicalCylinderEffect_eq_compiled n B hB, hpre]
    exact P.compiledSquare.cylinderEffect_consistent n m hnm _
      (hB.preimage (measurable_coarseHistory (n+1)))

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator

def leftBlockEmbed (a b : Nat) (s t : Fin b) : LocalMatrix a →L[ℂ] JointMatrix a b :=
  ({ toFun := fun Y => Y ⊗ₖ Matrix.single s t (1:ℂ)
     map_add' := by intro Y Z; simp [Matrix.add_kronecker]
     map_smul' := by
       intro r Y
       ext i j
       simp only [Matrix.kronecker_apply, Matrix.smul_apply]
       simp [mul_assoc] } : LocalMatrix a →ₗ[ℂ] JointMatrix a b).toContinuousLinearMap

def rightBlockEmbed (a b : Nat) (s t : Fin a) : LocalMatrix b →L[ℂ] JointMatrix a b :=
  ({ toFun := fun Y => Matrix.single s t (1:ℂ) ⊗ₖ Y
     map_add' := by intro Y Z; simp [Matrix.kronecker_add]
     map_smul' := by
       intro r Y
       ext i j
       simp only [Matrix.kronecker_apply, Matrix.smul_apply]
       simp [mul_left_comm, mul_assoc] } : LocalMatrix b →ₗ[ℂ] JointMatrix a b).toContinuousLinearMap

theorem leftApplication_eq_blocks {a b : Nat}
    (Φ : LocalMatrix a →ₗ[ℂ] LocalMatrix a) (X : JointMatrix a b) :
    QuantumProver.ElegantJointMeasurement.CP.leftApplication Φ X = ∑ st : Fin b×Fin b,
      leftBlockEmbed a b st.1 st.2
        (Φ (Matrix.of (fun i j => X (i,st.1) (j,st.2)))) := by
  classical
  ext i j
  change Φ (Matrix.of (fun x y => X (x,i.2) (y,j.2))) i.1 j.1 =
    (∑ st : Fin b×Fin b, (Φ (Matrix.of (fun x y => X (x,st.1) (y,st.2)))) ⊗ₖ
      Matrix.single st.1 st.2 (1:ℂ)) i j
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Matrix.single, Fintype.sum_prod_type, mul_ite, ite_and]

theorem rightApplication_eq_blocks {a b : Nat}
    (Φ : LocalMatrix b →ₗ[ℂ] LocalMatrix b) (X : JointMatrix a b) :
    QuantumProver.ElegantJointMeasurement.CP.rightApplication Φ X = ∑ st : Fin a×Fin a,
      rightBlockEmbed a b st.1 st.2
        (Φ (Matrix.of (fun i j => X (st.1,i) (st.2,j)))) := by
  classical
  ext i j
  change Φ (Matrix.of (fun x y => X (i.1,x) (j.1,y))) i.2 j.2 =
    (∑ st : Fin a×Fin a, Matrix.single st.1 st.2 (1:ℂ) ⊗ₖ
      (Φ (Matrix.of (fun x y => X (st.1,x) (st.2,y))))) i j
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Matrix.single, Fintype.sum_prod_type, ite_mul, ite_and]

section LiftIntegral
variable {Ω : Type*} [MeasurableSpace Ω] {a b : Nat}
variable (μ : Measure Ω)

theorem integrable_leftApplication_field
    (Φ : Ω → (LocalMatrix a →ₗ[ℂ] LocalMatrix a))
    (hΦ : ∀ Y, Integrable (fun r => Φ r Y) μ) (X : JointMatrix a b) :
    Integrable (fun r => QuantumProver.ElegantJointMeasurement.CP.leftApplication (Φ r) X) μ := by
  classical
  simp_rw [leftApplication_eq_blocks]
  exact integrable_finsetSum Finset.univ (fun st _ =>
    (leftBlockEmbed a b st.1 st.2).integrable_comp (hΦ _))

theorem integrable_rightApplication_field
    (Φ : Ω → (LocalMatrix b →ₗ[ℂ] LocalMatrix b))
    (hΦ : ∀ Y, Integrable (fun r => Φ r Y) μ) (X : JointMatrix a b) :
    Integrable (fun r => QuantumProver.ElegantJointMeasurement.CP.rightApplication (Φ r) X) μ := by
  classical
  simp_rw [rightApplication_eq_blocks]
  exact integrable_finsetSum Finset.univ (fun st _ =>
    (rightBlockEmbed a b st.1 st.2).integrable_comp (hΦ _))

theorem integral_leftApplication_field
    (Φ : Ω → (LocalMatrix a →ₗ[ℂ] LocalMatrix a))
    (hΦ : ∀ Y, Integrable (fun r => Φ r Y) μ)
    (Ψ : LocalMatrix a →ₗ[ℂ] LocalMatrix a)
    (hInt : ∀ Y, (∫ r, Φ r Y ∂μ) = Ψ Y) (X : JointMatrix a b) :
    (∫ r, QuantumProver.ElegantJointMeasurement.CP.leftApplication (Φ r) X ∂μ) = QuantumProver.ElegantJointMeasurement.CP.leftApplication Ψ X := by
  classical
  simp_rw [leftApplication_eq_blocks]
  rw [integral_finsetSum _ (fun st _ =>
    (leftBlockEmbed a b st.1 st.2).integrable_comp (hΦ _))]
  apply Finset.sum_congr rfl
  intro st _
  let Y : LocalMatrix a := Matrix.of (fun i j => X (i,st.1) (j,st.2))
  change (∫ r, leftBlockEmbed a b st.1 st.2 (Φ r Y) ∂μ) =
    leftBlockEmbed a b st.1 st.2 (Ψ Y)
  exact ((leftBlockEmbed a b st.1 st.2).integral_comp_comm (hΦ Y)).trans
    (congrArg (leftBlockEmbed a b st.1 st.2) (hInt Y))

theorem integral_rightApplication_field
    (Φ : Ω → (LocalMatrix b →ₗ[ℂ] LocalMatrix b))
    (hΦ : ∀ Y, Integrable (fun r => Φ r Y) μ)
    (Ψ : LocalMatrix b →ₗ[ℂ] LocalMatrix b)
    (hInt : ∀ Y, (∫ r, Φ r Y ∂μ) = Ψ Y) (X : JointMatrix a b) :
    (∫ r, QuantumProver.ElegantJointMeasurement.CP.rightApplication (Φ r) X ∂μ) = QuantumProver.ElegantJointMeasurement.CP.rightApplication Ψ X := by
  classical
  simp_rw [rightApplication_eq_blocks]
  rw [integral_finsetSum _ (fun st _ =>
    (rightBlockEmbed a b st.1 st.2).integrable_comp (hΦ _))]
  apply Finset.sum_congr rfl
  intro st _
  let Y : LocalMatrix b := Matrix.of (fun i j => X (st.1,i) (st.2,j))
  change (∫ r, rightBlockEmbed a b st.1 st.2 (Φ r Y) ∂μ) =
    rightBlockEmbed a b st.1 st.2 (Ψ Y)
  exact ((rightBlockEmbed a b st.1 st.2).integral_comp_comm (hΦ Y)).trans
    (congrArg (rightBlockEmbed a b st.1 st.2) (hInt Y))

end LiftIntegral

universe u
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : Nat} [NeZero a] [NeZero b]
namespace MatrixProcess
variable (P : MatrixProcess a b R)

theorem physicalLocalDensity_setIntegral (n : Nat) (h : History R n)
    (B : Set R) (hB : MeasurableSet B) (X : JointMatrix a b) :
    (∫ r in B, P.physicalLocalDensity n h r X ∂P.physicalKernel n h) =
      if P.aliceTurn n h = true then QuantumProver.ElegantJointMeasurement.CP.leftApplication ((P.alice n).map h B) X
      else QuantumProver.ElegantJointMeasurement.CP.rightApplication ((P.bob n).map h B) X := by
  classical
  by_cases ht : P.aliceTurn n h = true
  · simp only [physicalLocalDensity, if_pos ht, physicalKernel,
      Kernel.piecewise_apply, Set.mem_setOf_eq, if_pos ht]
    exact integral_leftApplication_field _ _
      (fun Y => ((P.alice n).cpDensity_integrable h Y).integrableOn)
      ((P.alice n).map h B) ((P.alice n).cpDensity_setIntegral h B hB) X
  · simp only [physicalLocalDensity, if_neg ht, physicalKernel,
      Kernel.piecewise_apply, Set.mem_setOf_eq, if_neg ht]
    exact integral_rightApplication_field _ _
      (fun Y => ((P.bob n).cpDensity_integrable h Y).integrableOn)
      ((P.bob n).map h B) ((P.bob n).cpDensity_setIntegral h B hB) X

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess

namespace QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
open MeasureTheory ProbabilityTheory Set Function Preorder
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
  Matrix.Norms.L2Operator
universe u
variable {R : Type u} [MeasurableSpace R] [StandardBorelSpace R]
variable {a b : Nat} [NeZero a] [NeZero b]
namespace MatrixProcess
variable (P : MatrixProcess a b R)

theorem physicalPrefixAction_trace (N : Nat)
    (B : Set (Prefix R N)) (hB : MeasurableSet B) (X : JointMatrix a b) :
    (P.represented_physicalPrefixAction (N+1) B X).trace =
      (P.represented_physicalCylinderEffect N B * X).trace := by
  classical
  let D : Set (Prefix (FineRecord a b R) N) :=
    (coarseHistory (a := a) (b := b) (N+1)) ⁻¹' B
  let T : JointMatrix a b →L[ℂ] ℂ :=
    (QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.MatrixProbe.bornComplexLinear X).toContinuousLinearMap
  rw [P.physicalPrefixAction_eq_recoveredCompiledAction N B hB,
    P.physicalCylinderEffect_eq_compiled N B hB]
  have hi := (P.recoveredCompiledAction_integrable N X).integrableOn (s := D)
  change traceComplexCLM a b
    (∫ h in D, P.recoveredCompiledAction (N+1) h X
      ∂P.compiledSquare.prefixMeasure N) =
    T (∫ h in D, P.compiledSquare.pathGram N h
      ∂P.compiledSquare.prefixMeasure N)
  rw [← (traceComplexCLM a b).integral_comp_comm hi]
  have hpoint (h : Prefix (FineRecord a b R) N) :
      traceComplexCLM a b (P.recoveredCompiledAction (N+1) h X) =
        T (P.compiledSquare.pathGram N h) := by
    change (QuantumProver.ElegantJointMeasurement.CP.pendingApplication _ _ (P.compiledAction (N+1) h X)).trace =
      (P.compiledSquare.pathGram N h * X).trace
    rw [QuantumProver.ElegantJointMeasurement.CP.pendingApplication_trace, P.compiledAction_eq_squarePath,
      Matrix.trace_mul_cycle]
    rfl
  simp_rw [hpoint]
  exact T.integral_comp_comm (P.compiledSquare.pathGram_integrable N).integrableOn

theorem physicalPrefixAction_trace_re (N : Nat)
    (B : Set (Prefix R N)) (hB : MeasurableSet B) (X : JointMatrix a b) :
    (P.represented_physicalPrefixAction (N+1) B X).trace.re =
      QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.MatrixProbe.bornScalar X (P.represented_physicalCylinderEffect N B) := by
  exact congrArg Complex.re (P.physicalPrefixAction_trace N B hB X)

def represented_physicalBornMeasure (ρ : JointMatrix a b) (hρ : ρ.PosSemidef) :
    Measure (QuantumProver.ElegantJointMeasurement.HilbertTranscriptPOVM.Transcript R) := by
  letI := P.record_nonempty
  exact P.represented_physicalCylinderPOVM.fullBornMeasure ρ hρ

theorem physicalBornMeasure_prefix
    (ρ : JointMatrix a b) (hρ : ρ.PosSemidef)
    (N : Nat) (B : Set (Prefix R N)) (hB : MeasurableSet B) :
    P.represented_physicalBornMeasure ρ hρ
        ((frestrictLe (π := fun _ => R) N) ⁻¹' B) =
      ENNReal.ofReal (P.represented_physicalPrefixAction (N+1) B ρ).trace.re := by
  letI := P.record_nonempty
  rw [represented_physicalBornMeasure, P.represented_physicalCylinderPOVM.fullBornMeasure_prefix ρ hρ N B hB]
  exact congrArg ENNReal.ofReal (P.physicalPrefixAction_trace_re N B hB ρ).symm

end MatrixProcess
end QuantumProver.ElegantJointMeasurement.HilbertSquareProcess.RawInstrumentProcess
