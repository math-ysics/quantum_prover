import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.HilbertPolar
import QuantumProver.InformationTheory.ElegantJointMeasurement.NormalCPInstruments
import QuantumProver.InformationTheory.ElegantJointMeasurement.SeparableHilbertEmbedding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory InnerProductSpace Filter QuantumProver.ElegantJointMeasurement.HilbertPolar
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Topology Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.HilbertRecovery

open QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.NuclearOperator QuantumProver.HilbertNuclearCompression

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance sourceComplete : CompleteSpace (Source I) :=
  PiLp.completeSpace 2 (fun _ : I => ℂ)

local instance sourceEndomorphismComplete : CompleteSpace (Source I →L[ℂ] Source I) :=
  ContinuousLinearMap.instCompleteSpace

def reset (φ : E) (i : I) : Source I →L[ℂ] E :=
  rankOne ℂ φ (EuclideanSpace.basisFun I ℂ i)

theorem reset_gram (φ : E) (hφ : ‖φ‖ = 1) (i : I) :
    (reset φ i).adjoint ∘L reset φ i =
      rankOne ℂ (EuclideanSpace.basisFun I ℂ i) (EuclideanSpace.basisFun I ℂ i) := by
  rw [reset, adjoint_rankOne, rankOne_comp_rankOne, inner_self_eq_norm_sq_to_K, hφ]
  simp

theorem sum_reset_gram (φ : E) (hφ : ‖φ‖ = 1) :
    ∑ i : I, (reset φ i).adjoint ∘L reset φ i = 1 := by
  simp_rw [reset_gram φ hφ]
  simpa only [ContinuousLinearMap.one_def] using (EuclideanSpace.basisFun I ℂ).sum_rankOne_eq_id

def recoveryKraus (φ : E) (K : Source I →L[ℂ] E) : Unit ⊕ I → Source I →L[ℂ] E
  | .inl _ => polar K
  | .inr i => reset φ i ∘L complement K

theorem recoveryKraus_complete (φ : E) (hφ : ‖φ‖ = 1) (K : Source I →L[ℂ] E) :
    ∑ q, (recoveryKraus φ K q).adjoint ∘L recoveryKraus φ K q = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [recoveryKraus, Fintype.sum_unique, polar_gram]
  have hs : (∑ i, (reset φ i ∘L complement K).adjoint ∘L
      (reset φ i ∘L complement K)) = complement K := by
    calc
      _ = complement K ∘L (∑ i, (reset φ i).adjoint ∘L reset φ i) ∘L complement K := by
        ext x
        simp only [sum_apply, ContinuousLinearMap.comp_apply, map_sum,
          ContinuousLinearMap.adjoint_comp, complement_selfAdjoint]
      _ = complement K := by
        rw [sum_reset_gram φ hφ, ContinuousLinearMap.one_def,
          ContinuousLinearMap.id_comp, complement_square]
  rw [hs, complement]
  abel

theorem recoveryKraus_comp_positiveInput (φ : E) (K : Source I →L[ℂ] E) (q : Unit ⊕ I) :
    recoveryKraus φ K q ∘L positiveInput K =
      match q with | .inl _ => K | .inr _ => 0 := by
  cases q with
  | inl u => exact polar_comp_positiveInput K
  | inr i => simp only [recoveryKraus, ContinuousLinearMap.comp_assoc,
      complement_comp_positiveInput, ContinuousLinearMap.comp_zero]

local instance sourceMapMeasurableRecovery : MeasurableSpace (Source I →L[ℂ] E) :=
  borel (Source I →L[ℂ] E)
local instance sourceMapBorelRecovery : BorelSpace (Source I →L[ℂ] E) := ⟨rfl⟩
local instance sourceEndomorphismMeasurableRecovery : MeasurableSpace (Source I →L[ℂ] Source I) :=
  borel (Source I →L[ℂ] Source I)
local instance sourceEndomorphismBorelRecovery : BorelSpace (Source I →L[ℂ] Source I) := ⟨rfl⟩

theorem measurable_recoveryKraus (φ : E) (q : Unit ⊕ I) :
    Measurable (fun K : Source I →L[ℂ] E => recoveryKraus φ K q) := by
  cases q with
  | inl u => exact measurable_polar
  | inr i =>
      exact (continuous_const.clm_comp continuous_id :
        Continuous (fun C : Source I →L[ℂ] Source I => reset φ i ∘L C)).measurable.comp
          measurable_complement

abbrev NuclearSource := QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (Source I)
abbrev NuclearChannel := NuclearSource (I := I) →L[ℂ] QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear E

local instance channelNormedGroup : NormedAddCommGroup (NuclearChannel (I := I) (E := E)) :=
  inferInstance
local instance channelNormedSpace : NormedSpace ℂ (NuclearChannel (I := I) (E := E)) :=
  inferInstance
local instance rightMapNormedSpace : NormedSpace ℂ (E →L[ℂ] Source I) := inferInstance
local instance rightComposeNormedGroup :
    NormedAddCommGroup ((E →L[ℂ] Source I) →L[ℂ] NuclearChannel (I := I) (E := E)) :=
  inferInstance

theorem norm_compose_le (L : Source I →L[ℂ] E) (R : E →L[ℂ] Source I) :
    ‖compose L R‖ ≤ ‖L‖ * ‖R‖ :=
  (compose L R).opNorm_le_bound (mul_nonneg (norm_nonneg L) (norm_nonneg R))
    (norm_compose_apply_le L R)

def rightComposeLinear (L : Source I →L[ℂ] E) :
    (E →L[ℂ] Source I) →ₗ[ℂ] NuclearChannel (I := I) (E := E) where
  toFun R := compose L R
  map_add' R S := by
    ext T
    apply toOperator_injective
    simp only [sum_apply, ContinuousLinearMap.add_apply, map_add, toOperator_compose,
      ContinuousLinearMap.comp_add]
  map_smul' a R := by
    ext T
    apply toOperator_injective
    simp only [ContinuousLinearMap.smul_apply, map_smul, toOperator_compose,
      ContinuousLinearMap.comp_smul, RingHom.id_apply]

def rightCompose (L : Source I →L[ℂ] E) :
    (E →L[ℂ] Source I) →L[ℂ] NuclearChannel (I := I) (E := E) := by
  refine ⟨rightComposeLinear L, ?_⟩
  exact AddMonoidHomClass.continuous_of_bound (rightComposeLinear L) ‖L‖
    (fun R => norm_compose_le L R)

@[simp] theorem rightCompose_apply (L : Source I →L[ℂ] E) (R : E →L[ℂ] Source I) :
    rightCompose L R = compose L R := rfl

theorem norm_rightCompose_le (L : Source I →L[ℂ] E) : ‖rightCompose L‖ ≤ ‖L‖ :=
  (rightCompose L).opNorm_le_bound (norm_nonneg L) (fun R => norm_compose_le L R)

def composeBilinearLinear : (Source I →L[ℂ] E) →ₗ[ℂ]
    (E →L[ℂ] Source I) →L[ℂ] NuclearChannel (I := I) (E := E) where
  toFun L := rightCompose L
  map_add' L M := by
    ext R T
    apply toOperator_injective
    simp only [ContinuousLinearMap.add_apply, map_add, rightCompose_apply, toOperator_compose,
      ContinuousLinearMap.add_comp]
  map_smul' a L := by
    ext R T
    apply toOperator_injective
    simp only [ContinuousLinearMap.smul_apply, map_smul, rightCompose_apply, toOperator_compose,
      ContinuousLinearMap.smul_comp, RingHom.id_apply]

def composeBilinear : (Source I →L[ℂ] E) →L[ℂ]
    (E →L[ℂ] Source I) →L[ℂ] NuclearChannel (I := I) (E := E) := by
  refine ⟨composeBilinearLinear, ?_⟩
  exact AddMonoidHomClass.continuous_of_bound
    (composeBilinearLinear (I := I) (E := E)) 1
    (fun L => by
      change ‖rightCompose L‖ ≤ 1 * ‖L‖
      simpa only [one_mul] using norm_rightCompose_le L)

@[simp] theorem composeBilinear_apply (L : Source I →L[ℂ] E) (R : E →L[ℂ] Source I) :
    composeBilinear L R = compose L R := rfl

def nuclearSandwich (U : Source I →L[ℂ] E) : NuclearChannel (I := I) (E := E) :=
  compose U U.adjoint

theorem continuous_nuclearSandwich : Continuous (nuclearSandwich (I := I) (E := E)) := by
  have hadj : Continuous (fun U : Source I →L[ℂ] E => U.adjoint) :=
    ContinuousLinearMap.adjoint.continuous
  change Continuous (fun U : Source I →L[ℂ] E => composeBilinear U U.adjoint)
  exact (composeBilinear (I := I) (E := E)).continuous.clm_apply hadj

def nuclearRecovery (φ : E) (K : Source I →L[ℂ] E) : NuclearChannel (I := I) (E := E) :=
  ∑ q, nuclearSandwich (recoveryKraus φ K q)

theorem toOperator_nuclearRecovery (φ : E) (K : Source I →L[ℂ] E)
    (T : NuclearSource (I := I)) :
    toOperator (nuclearRecovery φ K T) =
      ∑ q, recoveryKraus φ K q ∘L toOperator T ∘L (recoveryKraus φ K q).adjoint := by
  simp only [nuclearRecovery, nuclearSandwich, composeBilinear_apply, sum_apply, map_sum,
    toOperator_compose]

theorem nuclearRecovery_isPositive (φ : E) (K : Source I →L[ℂ] E)
    (T : NuclearSource (I := I)) (hT : (toOperator T).IsPositive) :
    (toOperator (nuclearRecovery φ K T)).IsPositive := by
  rw [toOperator_nuclearRecovery]
  simpa using ContinuousLinearMap.isPositive_sum Finset.univ
    (fun q _ => hT.conj_adjoint (recoveryKraus φ K q))

theorem trace_nuclearRecovery (φ : E) (hφ : ‖φ‖ = 1) (K : Source I →L[ℂ] E)
    (T : NuclearSource (I := I)) :
    QuantumProver.HilbertNuclearTrace.trace (nuclearRecovery φ K T) = QuantumProver.HilbertNuclearTrace.trace T := by
  simp only [nuclearRecovery, nuclearSandwich, composeBilinear_apply, sum_apply, map_sum]
  have hcycle :
      (∑ q, QuantumProver.HilbertNuclearTrace.trace
        (compose (recoveryKraus φ K q) (recoveryKraus φ K q).adjoint T)) =
      ∑ q, QuantumProver.HilbertNuclearTrace.trace
        (compose (ContinuousLinearMap.id ℂ (Source I))
          ((recoveryKraus φ K q).adjoint ∘L recoveryKraus φ K q) T) := by
    apply Finset.sum_congr rfl
    intro q _
    exact QuantumProver.ElegantJointMeasurement.NormalCPInstruments.trace_compose_cycle _ _ T
  rw [hcycle]
  have hs : compose (ContinuousLinearMap.id ℂ (Source I))
      (∑ q, (recoveryKraus φ K q).adjoint ∘L recoveryKraus φ K q) T =
      ∑ q, compose (ContinuousLinearMap.id ℂ (Source I))
        ((recoveryKraus φ K q).adjoint ∘L recoveryKraus φ K q) T := by
    apply toOperator_injective
    simp only [toOperator_compose, map_sum, ContinuousLinearMap.id_comp]
    ext x
    simp only [ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  rw [← map_sum, ← hs, recoveryKraus_complete φ hφ]
  congr 1
  apply toOperator_injective
  simp only [toOperator_compose, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]

theorem nuclearRecovery_square (φ : E) (K : Source I →L[ℂ] E)
    (T : NuclearSource (I := I)) :
    nuclearRecovery φ K (compose (positiveInput K) (positiveInput K) T) =
      compose K K.adjoint T := by
  apply toOperator_injective
  rw [toOperator_nuclearRecovery, toOperator_compose, toOperator_compose]
  have hterm (q : Unit ⊕ I) : recoveryKraus φ K q ∘L
      (positiveInput K ∘L toOperator T ∘L positiveInput K) ∘L (recoveryKraus φ K q).adjoint =
      (recoveryKraus φ K q ∘L positiveInput K) ∘L toOperator T ∘L
        (recoveryKraus φ K q ∘L positiveInput K).adjoint := by
    simp only [ContinuousLinearMap.adjoint_comp, positiveInput_selfAdjoint,
      ContinuousLinearMap.comp_assoc]
  simp_rw [hterm, recoveryKraus_comp_positiveInput]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, map_zero, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero, Finset.sum_const_zero, add_zero]

local instance nuclearChannelMeasurable : MeasurableSpace (NuclearChannel (I := I) (E := E)) :=
  borel (NuclearChannel (I := I) (E := E))
local instance nuclearChannelBorel : BorelSpace (NuclearChannel (I := I) (E := E)) := ⟨rfl⟩

theorem measurable_nuclearRecovery (φ : E) :
    Measurable (nuclearRecovery (I := I) (E := E) φ) := by
  let channelFromPolar (Q : Source I →L[ℂ] E) : NuclearChannel (I := I) (E := E) :=
    nuclearSandwich Q + ∑ i : I, nuclearSandwich (reset φ i ∘L (1 - Q.adjoint ∘L Q))
  have hc : Continuous channelFromPolar := by
    have hadj : Continuous (fun Q : Source I →L[ℂ] E => Q.adjoint) :=
      ContinuousLinearMap.adjoint.continuous
    apply Continuous.add continuous_nuclearSandwich
    apply continuous_finset_sum
    intro i _
    apply continuous_nuclearSandwich.comp
    exact continuous_const.clm_comp
      (continuous_const.sub (hadj.clm_comp continuous_id))
  have heq : nuclearRecovery (I := I) (E := E) φ =
      fun K => channelFromPolar (polar K) := by
    funext K
    simp only [nuclearRecovery, Fintype.sum_sum_type, recoveryKraus, Fintype.sum_unique,
      channelFromPolar, polar_gram, complement]
  rw [heq]
  exact hc.measurable.comp measurable_polar

open QuantumProver.ElegantJointMeasurement.HilbertChoi

variable {R : Type} [Fintype R] [DecidableEq R]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

abbrev blockLift (U : F →L[ℂ] E) : BlockSpace R F →L[ℂ] BlockSpace R E :=
  QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.blockLift U

theorem blockLift_apply (U : F →L[ℂ] E) (x : BlockSpace R F) (r : R) :
    blockLift U x r = U (x r) := rfl

theorem blockLift_comp_insert (U : F →L[ℂ] E) (r : R) :
    blockLift U ∘L QuantumProver.ElegantJointMeasurement.HilbertChoi.insert r =
      QuantumProver.ElegantJointMeasurement.HilbertChoi.insert r ∘L U := by
  ext x s
  by_cases h : s = r
  simp [ContinuousLinearMap.comp_apply, blockLift_apply,
    QuantumProver.ElegantJointMeasurement.HilbertChoi.insert_apply_apply, h]
  simp [ContinuousLinearMap.comp_apply, blockLift_apply,
    QuantumProver.ElegantJointMeasurement.HilbertChoi.insert_apply_apply, h]

theorem blockLift_adjoint (U : F →L[ℂ] E) :
    (blockLift (R := R) U).adjoint = blockLift U.adjoint :=
  QuantumProver.ElegantJointMeasurement.SeparableHilbertEmbedding.blockLift_adjoint U

def amplifiedRecovery (φ : E) (K : Source I →L[ℂ] E) :
    QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (BlockSpace R (Source I)) →L[ℂ]
      QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (BlockSpace R E) :=
  ∑ q, compose (blockLift (R := R) (recoveryKraus φ K q))
    (blockLift (R := R) (recoveryKraus φ K q)).adjoint

theorem toOperator_amplifiedRecovery (φ : E) (K : Source I →L[ℂ] E)
    (T : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (BlockSpace R (Source I))) :
    toOperator (amplifiedRecovery φ K T) =
      ∑ q, blockLift (R := R) (recoveryKraus φ K q) ∘L toOperator T ∘L
        (blockLift (R := R) (recoveryKraus φ K q)).adjoint := by
  simp only [amplifiedRecovery, sum_apply, map_sum, toOperator_compose]

theorem amplifiedRecovery_isPositive (φ : E) (K : Source I →L[ℂ] E)
    (T : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (BlockSpace R (Source I))) (hT : (toOperator T).IsPositive) :
    (toOperator (amplifiedRecovery φ K T)).IsPositive := by
  rw [toOperator_amplifiedRecovery]
  simpa using ContinuousLinearMap.isPositive_sum Finset.univ
    (fun q _ => hT.conj_adjoint (blockLift (R := R) (recoveryKraus φ K q)))

theorem amplifiedRecovery_block (φ : E) (K : Source I →L[ℂ] E)
    (T : QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (BlockSpace R (Source I))) (r s : R) :
    compose (PiLp.proj 2 (fun _ : R => E) r) (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := E) s)
      (amplifiedRecovery φ K T) =
      nuclearRecovery φ K
        (compose (PiLp.proj 2 (fun _ : R => Source I) r)
          (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := Source I) s) T) := by
  apply toOperator_injective
  rw [toOperator_compose, toOperator_amplifiedRecovery, toOperator_nuclearRecovery,
    toOperator_compose]
  ext x
  simp only [ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [blockLift_adjoint]
  change (blockLift (recoveryKraus φ K q)
      (toOperator T (blockLift (recoveryKraus φ K q).adjoint
        (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert s x)))) r = _
  rw [blockLift_apply]
  have harg : blockLift (R := R) (recoveryKraus φ K q).adjoint
      (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert s x) =
      QuantumProver.ElegantJointMeasurement.HilbertChoi.insert s ((recoveryKraus φ K q).adjoint x) :=
    congrArg (fun C => C x) (blockLift_comp_insert (recoveryKraus φ K q).adjoint s)
  rw [harg]
  rfl

end QuantumProver.ElegantJointMeasurement.HilbertRecovery

namespace QuantumProver.ElegantJointMeasurement.HilbertRecovery

open QuantumProver.ElegantJointMeasurement.HilbertPolar QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.NuclearOperator QuantumProver.HilbertNuclearCompression

variable {I : Type} [Fintype I] [DecidableEq I]

local instance finiteSourceComplete : CompleteSpace (Source I) :=
  PiLp.completeSpace 2 (fun _ : I => ℂ)

def nuclearMatrixLinear : Matrix I I ℂ →ₗ[ℂ] NuclearSource (I := I) where
  toFun X := ∑ i, ∑ j, X i j •
    QuantumProver.NuclearOperator.rankOne (innerSL ℂ (EuclideanSpace.basisFun I ℂ j))
      (EuclideanSpace.basisFun I ℂ i)
  map_add' X Y := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a X := by
    simp only [Matrix.smul_apply, Pi.smul_apply, smul_smul, Finset.smul_sum,
      RingHom.id_apply, smul_eq_mul]

def nuclearMatrix : Matrix I I ℂ →L[ℂ] NuclearSource (I := I) :=
  nuclearMatrixLinear.toContinuousLinearMap

theorem toOperator_nuclearMatrix (X : Matrix I I ℂ) :
    QuantumProver.NuclearOperator.toOperator (nuclearMatrix X) =
      QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator X := by
  change QuantumProver.NuclearOperator.toOperator (∑ p, ∑ j, X p j •
    QuantumProver.NuclearOperator.rankOne (innerSL ℂ (EuclideanSpace.basisFun I ℂ j))
      (EuclideanSpace.basisFun I ℂ p)) = _
  ext x i
  simp only [map_sum, map_smul,
    QuantumProver.NuclearOperator.toOperator_rankOne, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, EuclideanSpace.basisFun_inner,
    sum_apply, smul_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  change (∑ p, ∑ j, X p j * (x j * (EuclideanSpace.basisFun I ℂ p) i)) =
    ∑ j, X i j * x j
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply]

theorem trace_nuclearMatrix (X : Matrix I I ℂ) :
    QuantumProver.HilbertNuclearTrace.trace (nuclearMatrix X) = Matrix.trace X := by
  change QuantumProver.HilbertNuclearTrace.trace (∑ i, ∑ j, X i j •
    QuantumProver.NuclearOperator.rankOne (innerSL ℂ (EuclideanSpace.basisFun I ℂ j))
      (EuclideanSpace.basisFun I ℂ i)) = _
  simp only [map_sum, map_smul,
    QuantumProver.HilbertNuclearTrace.trace_rankOne, innerSL_apply_apply,
    (EuclideanSpace.basisFun I ℂ).inner_eq_ite]
  simp [Matrix.trace, Matrix.diag]

theorem nuclearMatrix_isPositive (X : Matrix I I ℂ) (hX : X.PosSemidef) :
    (QuantumProver.NuclearOperator.toOperator (nuclearMatrix X)).IsPositive := by
  rw [toOperator_nuclearMatrix]
  exact ContinuousLinearMap.nonneg_iff_isPositive.mp
    (map_nonneg (QuantumProver.ElegantJointMeasurement.HilbertPolar.matrixOperator (I := I)) hX.nonneg)

variable {R : Type} [Fintype R] [DecidableEq R]

local instance referenceSourceNormedGroup :
    NormedAddCommGroup (QuantumProver.ElegantJointMeasurement.HilbertChoi.BlockSpace R (Source I)) := inferInstance
local instance referenceSourceNormedSpace :
    NormedSpace ℂ (QuantumProver.ElegantJointMeasurement.HilbertChoi.BlockSpace R (Source I)) := inferInstance
local instance referenceSourceComplete :
    CompleteSpace (QuantumProver.ElegantJointMeasurement.HilbertChoi.BlockSpace R (Source I)) :=
  PiLp.completeSpace 2 (fun _ : R => Source I)

def sourceCurryLinear : Source (R × I) →ₗ[ℂ] QuantumProver.ElegantJointMeasurement.HilbertChoi.BlockSpace R (Source I) where
  toFun x := WithLp.toLp 2 (fun r => WithLp.toLp 2 (fun i => x (r, i)))
  map_add' x y := rfl
  map_smul' a x := rfl

def sourceCurry : Source (R × I) →L[ℂ] QuantumProver.ElegantJointMeasurement.HilbertChoi.BlockSpace R (Source I) := by
  refine ⟨sourceCurryLinear, ?_⟩
  change Continuous (fun x : Source (R × I) =>
    WithLp.toLp 2 (fun r => WithLp.toLp 2 (fun i => x (r, i))))
  apply (PiLp.continuous_toLp 2 (fun _ : R => Source I)).comp
  apply continuous_pi
  intro r
  apply (PiLp.continuous_toLp 2 (fun _ : I => ℂ)).comp
  apply continuous_pi
  intro i
  exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : R × I => ℂ) (r, i)).continuous

theorem sourceCurry_apply (x : Source (R × I)) (r : R) (i : I) :
    sourceCurry x r i = x (r, i) := rfl

theorem sourceCurry_adjoint_apply (x : QuantumProver.ElegantJointMeasurement.HilbertChoi.BlockSpace R (Source I))
    (r : R) (i : I) : sourceCurry.adjoint x (r, i) = x r i := by
  have hunit : sourceCurry (EuclideanSpace.basisFun (R × I) ℂ (r, i)) =
      QuantumProver.ElegantJointMeasurement.HilbertChoi.insert r (EuclideanSpace.basisFun I ℂ i) := by
    ext s j
    by_cases hs : s = r <;> by_cases hj : j = i <;>
      simp [sourceCurry_apply, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply,
        QuantumProver.ElegantJointMeasurement.HilbertChoi.insert_apply_apply, hs, hj, Prod.mk.injEq]
  have h := ContinuousLinearMap.adjoint_inner_right (sourceCurry (R := R) (I := I))
    (EuclideanSpace.basisFun (R × I) ℂ (r, i)) x
  rw [EuclideanSpace.basisFun_inner, hunit] at h
  have hrow : inner ℂ (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert r (EuclideanSpace.basisFun I ℂ i)) x =
      inner ℂ (EuclideanSpace.basisFun I ℂ i) (x r) := by
    rw [PiLp.inner_apply]
    have hterm (s : R) :
        inner ℂ (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert r (EuclideanSpace.basisFun I ℂ i) s) (x s) =
          if s = r then inner ℂ (EuclideanSpace.basisFun I ℂ i) (x r) else 0 := by
      by_cases hs : s = r
      · subst s
        simp [QuantumProver.ElegantJointMeasurement.HilbertChoi.insert_apply_apply]
      · simp [QuantumProver.ElegantJointMeasurement.HilbertChoi.insert_apply_apply, hs]
    simp_rw [hterm]
    simp
  rw [hrow, EuclideanSpace.basisFun_inner] at h
  exact h

def blockNuclearMatrix : Matrix (R × I) (R × I) ℂ →L[ℂ]
    QuantumProver.ElegantJointMeasurement.NuclearChoi.Nuclear (QuantumProver.ElegantJointMeasurement.HilbertChoi.BlockSpace R (Source I)) :=
  (compose (sourceCurry (R := R) (I := I)) sourceCurry.adjoint).comp nuclearMatrix

theorem blockNuclearMatrix_isPositive (X : Matrix (R × I) (R × I) ℂ)
    (hX : X.PosSemidef) :
    (QuantumProver.NuclearOperator.toOperator (blockNuclearMatrix X)).IsPositive := by
  rw [blockNuclearMatrix, ContinuousLinearMap.comp_apply, toOperator_compose]
  exact (nuclearMatrix_isPositive X hX).conj_adjoint sourceCurry

theorem toOperator_blockNuclearMatrix (X : Matrix (R × I) (R × I) ℂ)
    (x : QuantumProver.ElegantJointMeasurement.HilbertChoi.BlockSpace R (Source I)) (r : R) (i : I) :
    QuantumProver.NuclearOperator.toOperator (blockNuclearMatrix X) x r i =
      ∑ s, ∑ j, X (r, i) (s, j) * x s j := by
  rw [blockNuclearMatrix, ContinuousLinearMap.comp_apply, toOperator_compose,
    toOperator_nuclearMatrix]
  simp only [ContinuousLinearMap.comp_apply, sourceCurry_apply]
  change (∑ q : R × I, X (r, i) q * (sourceCurry.adjoint x) q) = _
  simp only [Fintype.sum_prod_type, sourceCurry_adjoint_apply]

theorem blockNuclearMatrix_block (X : Matrix (R × I) (R × I) ℂ) (r s : R) :
    compose (PiLp.proj 2 (fun _ : R => Source I) r)
      (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert (E := Source I) s) (blockNuclearMatrix X) =
      nuclearMatrix (I := I) (fun i j : I => X (r, i) (s, j)) := by
  let B : Matrix I I ℂ := fun i j => X (r, i) (s, j)
  have hB := toOperator_nuclearMatrix B
  apply QuantumProver.NuclearOperator.toOperator_injective
  rw [toOperator_compose]
  change _ = QuantumProver.NuclearOperator.toOperator (nuclearMatrix B)
  rw [hB]
  ext x i
  simp only [ContinuousLinearMap.comp_apply]
  change QuantumProver.NuclearOperator.toOperator (blockNuclearMatrix X)
      (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert s x) r i = ∑ j, X (r, i) (s, j) * x j
  rw [toOperator_blockNuclearMatrix]
  calc
    _ = ∑ j, X (r, i) (s, j) * (QuantumProver.ElegantJointMeasurement.HilbertChoi.insert s x s) j :=
      Finset.sum_eq_single s
        (fun t _ ht => by simp [QuantumProver.ElegantJointMeasurement.HilbertChoi.insert_apply_apply, ht])
        (by simp)
    _ = _ := by simp [QuantumProver.ElegantJointMeasurement.HilbertChoi.insert_apply_apply]

end QuantumProver.ElegantJointMeasurement.HilbertRecovery

namespace QuantumProver.ElegantJointMeasurement.HilbertRecovery

open QuantumProver.ElegantJointMeasurement.HilbertPolar QuantumProver.ElegantJointMeasurement.HilbertChoi QuantumProver.ElegantJointMeasurement.NuclearChoi
open QuantumProver.NuclearOperator (toOperator)
open QuantumProver.HilbertNuclearCompression

variable {I : Type} [Fintype I] [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance matrixRecoverySourceComplete : CompleteSpace (Source I) :=
  PiLp.completeSpace 2 (fun _ : I => ℂ)

def matrixRecovery (φ : E) (K : Source I →L[ℂ] E) :
    QuantumProver.ElegantJointMeasurement.NormalCPInstruments.PhysicalOperation I E :=
  (nuclearRecovery φ K).comp (nuclearMatrix (I := I))

theorem trace_matrixRecovery (φ : E) (hφ : ‖φ‖ = 1) (K : Source I →L[ℂ] E)
    (X : Matrix I I ℂ) :
    QuantumProver.HilbertNuclearTrace.trace (matrixRecovery φ K X) = Matrix.trace X := by
  rw [matrixRecovery, ContinuousLinearMap.comp_apply, trace_nuclearRecovery φ hφ,
    trace_nuclearMatrix]

variable {R : Type} [Fintype R] [DecidableEq R]

theorem matrixRecovery_amplification (φ : E) (K : Source I →L[ℂ] E)
    (X : Matrix (R × I) (R × I) ℂ) :
    toOperator (amplifiedRecovery φ K (blockNuclearMatrix X)) =
      amplification (operationOperator (matrixRecovery φ K).toLinearMap) X := by
  let A := toOperator (amplifiedRecovery φ K (blockNuclearMatrix X))
  have hb (r s : R) :
      (PiLp.proj 2 (fun _ : R => E) r) ∘L A ∘L insert s =
        toOperator (matrixRecovery φ K (fun i j : I => X (r, i) (s, j))) := by
    change (PiLp.proj 2 (fun _ : R => E) r) ∘L
      toOperator (amplifiedRecovery φ K (blockNuclearMatrix X)) ∘L insert s =
        toOperator (nuclearRecovery φ K
          (nuclearMatrix (I := I) (fun i j : I => X (r, i) (s, j))))
    have h := congrArg (toOperator (𝕜 := ℂ) (E := E) (F := E))
      (amplifiedRecovery_block φ K (blockNuclearMatrix X) r s)
    simpa only [toOperator_compose, blockNuclearMatrix_block] using h
  ext x r
  have hx : (∑ s : R, insert s (x s)) = x := by
    ext t
    simp [insert_apply_apply]
  change A x r = _
  calc
    A x r = ∑ s : R, A (insert s (x s)) r := by
      conv_lhs => rw [← hx, map_sum]
      simp only [WithLp.ofLp_sum, Finset.sum_apply]
    _ = ∑ s : R, toOperator (matrixRecovery φ K
        (fun i j : I => X (r, i) (s, j))) (x s) := by
      apply Finset.sum_congr rfl
      intro s _
      exact congrArg (fun L : E →L[ℂ] E => L (x s)) (hb r s)
    _ = _ := by
      rw [amplification, blockOperator_apply]
      apply Finset.sum_congr rfl
      intro s _
      let B : Matrix I I ℂ := fun i j => X (r, i) (s, j)
      change toOperator (matrixRecovery φ K B) (x s) = _
      rw [matrix_decomposition B]
      simp only [map_sum, map_smul, sum_apply, smul_apply, operationOperator_apply,
        ContinuousLinearMap.coe_coe, B]

theorem matrixRecovery_completelyPositive (φ : E) (K : Source I →L[ℂ] E) :
    CompletelyPositive (operationOperator (matrixRecovery φ K).toLinearMap) := by
  intro R _ _ X hX
  rw [← matrixRecovery_amplification]
  exact amplifiedRecovery_isPositive φ K _ (blockNuclearMatrix_isPositive X hX)

local instance matrixRecoveryMeasurable :
    MeasurableSpace (QuantumProver.ElegantJointMeasurement.NormalCPInstruments.PhysicalOperation I E) := borel _
local instance matrixRecoveryBorel :
    BorelSpace (QuantumProver.ElegantJointMeasurement.NormalCPInstruments.PhysicalOperation I E) := ⟨rfl⟩
local instance matrixRecoveryChannelMeasurable :
    MeasurableSpace (NuclearChannel (I := I) (E := E)) := borel _
local instance matrixRecoveryChannelBorel :
    BorelSpace (NuclearChannel (I := I) (E := E)) := ⟨rfl⟩

theorem measurable_matrixRecovery (φ : E) :
    Measurable (matrixRecovery (I := I) (E := E) φ) := by
  have hc : Continuous (fun ρ : NuclearChannel (I := I) (E := E) =>
      ρ.comp (nuclearMatrix (I := I))) := continuous_id.clm_comp continuous_const
  exact hc.measurable.comp (measurable_nuclearRecovery φ)

end QuantumProver.ElegantJointMeasurement.HilbertRecovery
