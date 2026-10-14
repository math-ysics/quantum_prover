import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.Definitions
import QuantumProver.InformationTheory.SuperchannelDiscrimination.PetzSmoothing
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYMeasurement
import QuantumProver.InformationTheory.QuantumEntropy.PartialTraceKraus

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Matrix
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator
open QuantumProver.SuperchannelDiscrimination

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYTestComposition

variable {A B E K I : Type*}
  [Fintype A] [Fintype B] [Fintype E] [Fintype K] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq E] [DecidableEq K] [DecidableEq I]

def acceptedEffect (M : K → QMatrix A) (N : K → QMatrix B) : QMatrix (A × B) :=
  ∑ k, M k ⊗ₖ N k

omit [DecidableEq K] in

theorem acceptedEffect_isEffect (M : K → QMatrix A) (N : K → QMatrix B)
    (hM : ∀ k, FlaggedStates.IsEffect (M k)) (hN : ∀ k, (N k).PosSemidef)
    (hComplete : (1 - ∑ k, N k).PosSemidef) :
    FlaggedStates.IsEffect (acceptedEffect M N) := by
  constructor
  · exact Matrix.posSemidef_sum _ (fun k _ => (hM k).1.kronecker (hN k))
  · have heq : 1 - acceptedEffect M N =
        (1 : QMatrix A) ⊗ₖ (1 - ∑ k, N k) + ∑ k, (1 - M k) ⊗ₖ N k := by
      ext i j
      simp only [acceptedEffect, Matrix.sub_apply, Matrix.add_apply,
        Matrix.sum_apply, Matrix.kroneckerMap_apply]
      simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hOne : (1 : QMatrix (A × B)) i j =
          (1 : QMatrix A) i.1 j.1 * (1 : QMatrix B) i.2 j.2 := by
        simpa only [Matrix.kroneckerMap_apply] using
          congrArg (fun X : QMatrix (A × B) => X i j) Matrix.one_kronecker_one.symm
      rw [hOne]
      ring
    rw [heq]
    exact (Matrix.PosSemidef.one.kronecker hComplete).add
      (Matrix.posSemidef_sum _ (fun k _ => (hM k).2.kronecker (hN k)))

theorem tensor_identity_isEffect {M : QMatrix A} (hM : FlaggedStates.IsEffect M) :
    FlaggedStates.IsEffect (M ⊗ₖ (1 : QMatrix E)) := by
  have h := acceptedEffect_isEffect (fun _ : Unit => M)
    (fun _ : Unit => (1 : QMatrix E)) (fun _ => hM)
    (fun _ => Matrix.PosSemidef.one) (by simpa using (Matrix.PosSemidef.zero :
      (0 : QMatrix E).PosSemidef))
  simpa only [acceptedEffect, Fintype.sum_unique] using h

theorem sandwich_isEffect (L : QMatrix I) {G Q : QMatrix I}
    (hG : FlaggedStates.IsEffect G) (hQ : FlaggedStates.IsEffect Q)
    (hGram : L * Lᴴ = G) : FlaggedStates.IsEffect (L * Q * Lᴴ) := by
  refine ⟨hQ.1.mul_mul_conjTranspose_same L, ?_⟩
  have heq : 1 - L * Q * Lᴴ = (1 - G) + L * (1 - Q) * Lᴴ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hGram]
    abel
  rw [heq]
  exact hG.2.add (hQ.2.mul_mul_conjTranspose_same L)

def aliceRoot (M : QMatrix A) : QMatrix (A × E) :=
  CFC.sqrt M ⊗ₖ (1 : QMatrix E)

theorem aliceRoot_gram {M : QMatrix A} (hM : M.PosSemidef) :
    aliceRoot (E := E) M * (aliceRoot (E := E) M)ᴴ = M ⊗ₖ (1 : QMatrix E) := by
  rw [aliceRoot, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    (CFC.sqrt_nonneg M).posSemidef.1.eq, ← Matrix.mul_kronecker_mul,
    CFC.sqrt_mul_sqrt_self M hM.nonneg, Matrix.one_mul]

def composedEffect (M : K → QMatrix A) (N : K → QMatrix B)
    (Q : QMatrix (A × E)) : QMatrix ((A × E) × B) :=
  ∑ k, (aliceRoot (M k) * Q * (aliceRoot (M k))ᴴ) ⊗ₖ N k

omit [DecidableEq K] in
theorem composedEffect_isEffect (M : K → QMatrix A) (N : K → QMatrix B)
    (hM : ∀ k, FlaggedStates.IsEffect (M k)) (hN : ∀ k, (N k).PosSemidef)
    (hComplete : (1 - ∑ k, N k).PosSemidef) {Q : QMatrix (A × E)}
    (hQ : FlaggedStates.IsEffect Q) : FlaggedStates.IsEffect (composedEffect M N Q) :=
  acceptedEffect_isEffect _ N
    (fun k => sandwich_isEffect _ (tensor_identity_isEffect (hM k)) hQ
      (aliceRoot_gram (hM k).1)) hN hComplete

theorem squareRoot_defect_le {R : QMatrix I} (hR : FlaggedStates.IsEffect R) :
    (1 - R - (1 - CFC.sqrt R) * (1 - CFC.sqrt R)).PosSemidef := by
  have hR1 : R ≤ 1 := Matrix.le_iff.mpr hR.2
  have hn : ‖R‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg R hR.1.nonneg).mpr hR1
  have hle : R ≤ CFC.sqrt R :=
    CStarAlgebra.self_le_sqrt_of_nonneg_of_norm_le_one hR.1.nonneg hn
  have hp := (Matrix.le_iff.mp hle).smul (by norm_num : (0 : ℝ) ≤ 2)
  have heq : 1 - R - (1 - CFC.sqrt R) * (1 - CFC.sqrt R) =
      (2 : ℝ) • (CFC.sqrt R - R) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      CFC.sqrt_mul_sqrt_self R hR.1.nonneg, two_smul]
    abel
  rw [heq]
  exact hp

theorem gentle_squareRoot_traceNorm {ρ R : QMatrix I}
    (hρ : FlaggedStates.IsDensity ρ) (hR : FlaggedStates.IsEffect R) :
    EffectPerturbation.traceNorm (ρ - CFC.sqrt R * ρ * CFC.sqrt R) ≤
      2 * Real.sqrt (1 - (ρ * R).trace.re) := by
  let L := CFC.sqrt R
  let D := ρ - L * ρ * L
  have hL : L.IsHermitian := (CFC.sqrt_nonneg R).posSemidef.1
  have hCrop : (L * ρ * L).PosSemidef := by
    simpa only [hL.eq] using hρ.1.mul_mul_conjTranspose_same L
  have hD : D.IsHermitian := hρ.1.1.sub hCrop.1
  let P := EffectPerturbation.positiveSupport D
  have hP : PetzSmoothing.IsProjection P :=
    ⟨(EffectPerturbation.positiveSupport_isEffect hD).1.1,
      EffectPerturbation.positiveSupport_idempotent D⟩
  let H := PetzSmoothing.reflection P
  have hH : H.IsHermitian := PetzSmoothing.reflection_isHermitian hP.selfAdjoint
  have hHsq : H * H = 1 := PetzSmoothing.reflection_sq hP.idempotent
  let U := 1 - L
  have hU : U.IsHermitian := Matrix.isHermitian_one.sub hL
  have htraceU : (U * ρ * Uᴴ).trace.re ≤ 1 - (ρ * R).trace.re := by
    have hp := FlaggedStates.trace_mul_re_nonneg hρ.1 (squareRoot_defect_le hR)
    have hu : (U * ρ * Uᴴ).trace = (ρ * (U * U)).trace := by
      rw [hU.eq, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
    rw [hu]
    change 0 ≤ (ρ * ((1 - R) - U * U)).trace.re at hp
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hp
    have hrej : (ρ * (1 - R)).trace.re = 1 - (ρ * R).trace.re := by
      simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub,
        Complex.sub_re, hρ.2, Complex.one_re]
    rw [hrej] at hp
    exact sub_nonneg.mp hp
  have htraceL : (L * ρ * Lᴴ).trace.re ≤ 1 := by
    have he : (L * ρ * Lᴴ).trace = (ρ * R).trace := by
      rw [hL.eq, Matrix.trace_mul_cycle]
      dsimp only [L]
      rw [CFC.sqrt_mul_sqrt_self R hR.1.nonneg, Matrix.trace_mul_comm]
    rw [he]
    exact (FlaggedStates.acceptanceProbability_bounds hρ hR).2
  have hReflect (Z : QMatrix I) :
      ((H * Z) * ρ * (H * Z)ᴴ).trace = (Z * ρ * Zᴴ).trace := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = (H * (Z * ρ * Zᴴ) * Hᴴ).trace := by simp only [Matrix.mul_assoc]
      _ = _ := PetzSmoothing.trace_reflection_sandwich hH hHsq _
  have h1 := PetzSmoothing.weighted_trace_cauchySchwarz hρ.1 (1 : QMatrix I) (H * U)
  simp only [Matrix.conjTranspose_one, Matrix.mul_one,
    hρ.2, Complex.one_re, Real.sqrt_one, one_mul, hReflect] at h1
  have h1' : ‖(H * U * ρ).trace‖ ≤ Real.sqrt (1 - (ρ * R).trace.re) :=
    h1.trans (Real.sqrt_le_sqrt htraceU)
  have h2 := PetzSmoothing.weighted_trace_cauchySchwarz hρ.1 U (H * L)
  rw [hReflect] at h2
  have h2' : ‖(H * L * ρ * U).trace‖ ≤ Real.sqrt (1 - (ρ * R).trace.re) := by
    calc
      _ ≤ Real.sqrt (U * ρ * Uᴴ).trace.re * Real.sqrt (L * ρ * Lᴴ).trace.re := by
        simpa only [hU.eq] using h2
      _ ≤ Real.sqrt (1 - (ρ * R).trace.re) * 1 := mul_le_mul
        (Real.sqrt_le_sqrt htraceU) (by simpa using Real.sqrt_le_sqrt htraceL)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  have heq : H * D = H * U * ρ + H * L * ρ * U := by
    dsimp only [D, U]
    noncomm_ring
  calc
    EffectPerturbation.traceNorm D = (H * D).trace.re :=
      PetzSmoothing.reflection_traceNorm_witness hD
    _ ≤ ‖(H * D).trace‖ := Complex.re_le_norm _
    _ ≤ 2 * Real.sqrt (1 - (ρ * R).trace.re) := by
      rw [heq, Matrix.trace_add]
      exact (norm_add_le _ _).trans (by linarith)

theorem gentle_effect_acceptance {ρ R Q : QMatrix I}
    (hρ : FlaggedStates.IsDensity ρ) (hR : FlaggedStates.IsEffect R)
    (hQ : FlaggedStates.IsEffect Q) :
    (Q * ρ).trace.re - 2 * Real.sqrt (1 - (ρ * R).trace.re) ≤
      (Q * (CFC.sqrt R * ρ * CFC.sqrt R)).trace.re := by
  have hL : (CFC.sqrt R).IsHermitian := (CFC.sqrt_nonneg R).posSemidef.1
  have hCrop : (CFC.sqrt R * ρ * CFC.sqrt R).PosSemidef := by
    simpa only [hL.eq] using hρ.1.mul_mul_conjTranspose_same (CFC.sqrt R)
  have hp := EffectPerturbation.effectValue_abs_le_traceNorm hQ (hρ.1.1.sub hCrop.1)
  have hg := gentle_squareRoot_traceNorm hρ hR
  simp only [EffectPerturbation.effectValue, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re] at hp
  linarith [le_abs_self ((Q * ρ).trace.re -
    (Q * (CFC.sqrt R * ρ * CFC.sqrt R)).trace.re)]

theorem blockDiagonal_posSemidef (X : K → QMatrix I) (hX : ∀ k, (X k).PosSemidef) :
    (Matrix.blockDiagonal X).PosSemidef := by
  let L : K → QMatrix I := fun k => CFC.sqrt (X k)
  have heq : (Matrix.blockDiagonal L)ᴴ * Matrix.blockDiagonal L = Matrix.blockDiagonal X := by
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    congr 1
    funext k
    dsimp only [L]
    rw [(CFC.sqrt_nonneg (X k)).posSemidef.1.eq,
      CFC.sqrt_mul_sqrt_self (X k) (hX k).nonneg]
  rw [← heq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem blockDiagonal_isEffect (M : K → QMatrix I)
    (hM : ∀ k, FlaggedStates.IsEffect (M k)) :
    FlaggedStates.IsEffect (Matrix.blockDiagonal M) := by
  refine ⟨blockDiagonal_posSemidef M (fun k => (hM k).1), ?_⟩
  have heq : 1 - Matrix.blockDiagonal M = Matrix.blockDiagonal (fun k => 1 - M k) := by
    rw [← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_sub]
    rfl
  rw [heq]
  exact blockDiagonal_posSemidef _ (fun k => (hM k).2)

theorem sqrt_blockDiagonal (M : K → QMatrix I) (hM : ∀ k, (M k).PosSemidef) :
    CFC.sqrt (Matrix.blockDiagonal M) = Matrix.blockDiagonal (fun k => CFC.sqrt (M k)) := by
  apply CFC.sqrt_unique
  · rw [← Matrix.blockDiagonal_mul]
    congr 1
    funext k
    exact CFC.sqrt_mul_sqrt_self (M k) (hM k).nonneg
  · exact (blockDiagonal_posSemidef _ (fun k => (CFC.sqrt_nonneg (M k)).posSemidef)).nonneg

theorem gentle_finite_branches (X M : K → QMatrix I)
    (hX : ∀ k, (X k).PosSemidef) (hMass : (∑ k, (X k).trace) = 1)
    (hM : ∀ k, FlaggedStates.IsEffect (M k)) {Q : QMatrix I}
    (hQ : FlaggedStates.IsEffect Q) :
    (∑ k, (Q * X k).trace.re) -
      2 * Real.sqrt (1 - ∑ k, (X k * M k).trace.re) ≤
      ∑ k, (Q * (CFC.sqrt (M k) * X k * CFC.sqrt (M k))).trace.re := by
  have hFlag : FlaggedStates.IsDensity (Matrix.blockDiagonal X) :=
    ⟨blockDiagonal_posSemidef X hX, (Matrix.trace_blockDiagonal X).trans hMass⟩
  have h := gentle_effect_acceptance hFlag (blockDiagonal_isEffect M hM)
    (blockDiagonal_isEffect (fun _ : K => Q) (fun _ => hQ))
  simpa only [sqrt_blockDiagonal M (fun k => (hM k).1),
    ← Matrix.blockDiagonal_mul, Matrix.trace_blockDiagonal, Complex.re_sum,
    Pi.mul_apply] using h

def bobMarginal (ρ : QMatrix (A × B)) (N : QMatrix B) : QMatrix A :=
  partialTraceRight (ρ * ((1 : QMatrix A) ⊗ₖ N))

omit [DecidableEq B] in
theorem bobMarginal_add (ρ : QMatrix (A × B)) (N L : QMatrix B) :
    bobMarginal ρ (N + L) = bobMarginal ρ N + bobMarginal ρ L := by
  ext i j
  simp only [bobMarginal, partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft,
    Matrix.kronecker_add, Matrix.mul_add, Matrix.add_apply, Finset.sum_add_distrib]

omit [DecidableEq B] in
theorem bobMarginal_smul (ρ : QMatrix (A × B)) (c : ℂ) (N : QMatrix B) :
    bobMarginal ρ (c • N) = c • bobMarginal ρ N := by
  ext i j
  simp only [bobMarginal, partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft,
    Matrix.kronecker_smul, Matrix.mul_smul, Matrix.smul_apply, Finset.smul_sum]

def bobMarginalLinearMap (ρ : QMatrix (A × B)) : QMatrix B →ₗ[ℂ] QMatrix A where
  toFun := bobMarginal ρ
  map_add' := bobMarginal_add ρ
  map_smul' := bobMarginal_smul ρ

omit [DecidableEq B] [DecidableEq K] in
theorem bobMarginal_sum (ρ : QMatrix (A × B)) (N : K → QMatrix B) :
    (∑ k, bobMarginal ρ (N k)) = bobMarginal ρ (∑ k, N k) :=
  (map_sum (bobMarginalLinearMap ρ) N Finset.univ).symm

theorem bobMarginal_one (ρ : QMatrix (A × B)) :
    bobMarginal ρ 1 = partialTraceRight ρ := by
  simp only [bobMarginal, Matrix.one_kronecker_one, Matrix.mul_one]

omit [DecidableEq K] in

theorem bobMarginal_complete (ρ : QMatrix (A × B)) (N : K → QMatrix B)
    (hComplete : (∑ k, N k) = 1) :
    (∑ k, bobMarginal ρ (N k)) = partialTraceRight ρ := by
  rw [bobMarginal_sum, hComplete, bobMarginal_one]

omit [DecidableEq B] in
theorem partialTraceRight_bob_cyclic (ρ : QMatrix (A × B)) (L : QMatrix B) :
    partialTraceRight (((1 : QMatrix A) ⊗ₖ L) * ρ) =
      partialTraceRight (ρ * ((1 : QMatrix A) ⊗ₖ L)) := by
  ext i j
  simp only [partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    ite_mul, mul_ite, one_mul, zero_mul, mul_zero, Finset.sum_const_zero, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  exact mul_comm _ _

theorem bobMarginal_eq_local_instrument (ρ : QMatrix (A × B)) {N : QMatrix B}
    (hN : N.PosSemidef) :
    bobMarginal ρ N = partialTraceRight
      (((1 : QMatrix A) ⊗ₖ CFC.sqrt N) * ρ *
        ((1 : QMatrix A) ⊗ₖ CFC.sqrt N)ᴴ) := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    (CFC.sqrt_nonneg N).posSemidef.1.eq]
  rw [Matrix.mul_assoc, partialTraceRight_bob_cyclic, Matrix.mul_assoc,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    CFC.sqrt_mul_sqrt_self N hN.nonneg]
  rfl

theorem bobMarginal_posSemidef {ρ : QMatrix (A × B)} (hρ : ρ.PosSemidef)
    {N : QMatrix B} (hN : N.PosSemidef) : (bobMarginal ρ N).PosSemidef := by
  rw [bobMarginal_eq_local_instrument ρ hN]
  exact partialTraceRight_positive (hρ.mul_mul_conjTranspose_same _)

omit [Fintype E] in
theorem aliceRoot_isHermitian (M : QMatrix A) :
    (aliceRoot (E := E) M).IsHermitian := by
  change (aliceRoot (E := E) M)ᴴ = aliceRoot (E := E) M
  rw [aliceRoot, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    (CFC.sqrt_nonneg M).posSemidef.1.eq]

theorem aliceRoot_eq_sqrt {M : QMatrix A} (hM : M.PosSemidef) :
    aliceRoot (E := E) M = CFC.sqrt (M ⊗ₖ (1 : QMatrix E)) := by
  symm
  apply CFC.sqrt_unique
  · simpa only [(aliceRoot_isHermitian M).eq] using aliceRoot_gram (E := E) hM
  · exact ((CFC.sqrt_nonneg M).posSemidef.kronecker Matrix.PosSemidef.one).nonneg

def bobFirstEffect (N : K → QMatrix B) : Option K → QMatrix B
  | none => 1 - ∑ k, N k
  | some k => N k

def aliceAccepted (M : K → QMatrix A) : Option K → QMatrix A
  | none => 0
  | some k => M k

def bobFirstBinaryPOVM (M : K → QMatrix A) (N : K → QMatrix B)
    (hM : ∀ k, FlaggedStates.IsEffect (M k)) (hN : ∀ k, (N k).PosSemidef)
    (hComplete : (1 - ∑ k, N k).PosSemidef) : OneWayPOVM B A (Option K) Bool where
  alice := bobFirstEffect N
  alice_positive := by
    intro z
    cases z with
    | none => exact hComplete
    | some k => exact hN k
  alice_complete := by
    rw [Fintype.sum_option]
    dsimp only [bobFirstEffect]
    abel
  bob := fun z b => if b then aliceAccepted M z else 1 - aliceAccepted M z
  bob_positive := by
    intro z b
    cases z with
    | none => cases b <;> simp only [aliceAccepted, Bool.false_eq_true,
        ite_false, ite_true, sub_zero] <;> first | exact Matrix.PosSemidef.one |
        exact Matrix.PosSemidef.zero
    | some k => cases b <;> simp only [aliceAccepted, Bool.false_eq_true,
        ite_false, ite_true] <;> first | exact (hM k).1 | exact (hM k).2
  bob_complete := by
    intro z
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    abel

omit [DecidableEq K] in

theorem bobFirstBinaryPOVM_accepted (M : K → QMatrix A) (N : K → QMatrix B)
    (hM : ∀ k, FlaggedStates.IsEffect (M k)) (hN : ∀ k, (N k).PosSemidef)
    (hComplete : (1 - ∑ k, N k).PosSemidef) :
    (∑ z, (bobFirstBinaryPOVM M N hM hN hComplete).alice z ⊗ₖ
      (bobFirstBinaryPOVM M N hM hN hComplete).bob z true).submatrix
        Prod.swap Prod.swap = acceptedEffect M N := by
  rw [Fintype.sum_option]
  ext i j
  simp only [bobFirstBinaryPOVM, bobFirstEffect, aliceAccepted, ite_true,
    Matrix.kronecker_zero, zero_add, Matrix.submatrix_apply, Matrix.sum_apply,
    acceptedEffect, Matrix.kroneckerMap_apply, Prod.swap]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

def bobFirstExtendedPOVM (M : K → QMatrix A) (N : K → QMatrix B)
    (hM : ∀ k, FlaggedStates.IsEffect (M k)) (hN : ∀ k, (N k).PosSemidef)
    (hComplete : (1 - ∑ k, N k).PosSemidef) :
    OneWayPOVM B (A × E) (Option K) Bool :=
  bobFirstBinaryPOVM (fun k => M k ⊗ₖ (1 : QMatrix E)) N
    (fun k => tensor_identity_isEffect (hM k)) hN hComplete

theorem bobMarginal_trace_pair (ρ : QMatrix (A × B)) (N : QMatrix B)
    (Q : QMatrix A) :
    (Q * bobMarginal ρ N).trace = ((Q ⊗ₖ N) * ρ).trace := by
  calc
    _ = (bobMarginal ρ N * Q).trace := Matrix.trace_mul_comm _ _
    _ = ((ρ * ((1 : QMatrix A) ⊗ₖ N)) *
        (Q ⊗ₖ (1 : QMatrix B))).trace :=
      (QuantumProver.QuantumEntropy.partialTrace_right_mul_trace _ Q).symm
    _ = (ρ * (Q ⊗ₖ N)).trace := by
      rw [Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    _ = _ := Matrix.trace_mul_comm _ _

def postselectedAE (M : K → QMatrix A) (N : K → QMatrix B)
    (ρ : QMatrix ((A × E) × B)) : QMatrix (A × E) :=
  ∑ k, aliceRoot (M k) * bobMarginal ρ (N k) * (aliceRoot (M k))ᴴ

omit [DecidableEq K] in
theorem postselectedAE_posSemidef (M : K → QMatrix A) (N : K → QMatrix B)
    {ρ : QMatrix ((A × E) × B)} (hρ : ρ.PosSemidef)
    (hN : ∀ k, (N k).PosSemidef) : (postselectedAE M N ρ).PosSemidef :=
  Matrix.posSemidef_sum _ (fun k _ =>
    (bobMarginal_posSemidef hρ (hN k)).mul_mul_conjTranspose_same _)

omit [DecidableEq K] in

theorem composedEffect_trace (M : K → QMatrix A) (N : K → QMatrix B)
    (Q : QMatrix (A × E)) (ρ : QMatrix ((A × E) × B)) :
    (composedEffect M N Q * ρ).trace = (Q * postselectedAE M N ρ).trace := by
  simp only [composedEffect, postselectedAE, Matrix.sum_mul, Matrix.mul_sum,
    Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k _
  let L : QMatrix (A × E) := aliceRoot (M k)
  have hL : L.IsHermitian := aliceRoot_isHermitian (M k)
  change (((L * Q * Lᴴ) ⊗ₖ N k) * ρ).trace =
    (Q * (L * bobMarginal ρ (N k) * Lᴴ)).trace
  rw [hL.eq]
  calc
    _ = ((L * Q * L) * bobMarginal ρ (N k)).trace :=
      (bobMarginal_trace_pair ρ (N k) (L * Q * L)).symm
    _ = (L * (Q * L * bobMarginal ρ (N k))).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((Q * L * bobMarginal ρ (N k)) * L).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

omit [DecidableEq K] in
theorem postselectedAE_trace (M : K → QMatrix A) (N : K → QMatrix B)
    (hM : ∀ k, (M k).PosSemidef) (ρ : QMatrix ((A × E) × B)) :
    (postselectedAE M N ρ).trace =
      (acceptedEffect (fun k => M k ⊗ₖ (1 : QMatrix E)) N * ρ).trace := by
  have heq : composedEffect (E := E) M N 1 =
      acceptedEffect (fun k => M k ⊗ₖ (1 : QMatrix E)) N := by
    simp only [composedEffect, acceptedEffect, Matrix.mul_one, aliceRoot_gram (hM _)]
  rw [← heq, composedEffect_trace, Matrix.one_mul]

theorem composedEffect_typeI_complete (M : K → QMatrix A) (N : K → QMatrix B)
    (hM : ∀ k, FlaggedStates.IsEffect (M k)) (hN : ∀ k, (N k).PosSemidef)
    (hComplete : (∑ k, N k) = 1) {Q : QMatrix (A × E)}
    (hQ : FlaggedStates.IsEffect Q) {ρ : QMatrix ((A × E) × B)}
    (hρ : FlaggedStates.IsDensity ρ) :
    (Q * partialTraceRight ρ).trace.re -
      2 * Real.sqrt (1 -
        (acceptedEffect (fun k => M k ⊗ₖ (1 : QMatrix E)) N * ρ).trace.re) ≤
      (composedEffect M N Q * ρ).trace.re := by
  have hMass : (∑ k, (bobMarginal ρ (N k)).trace) = 1 := by
    rw [← Matrix.trace_sum, bobMarginal_complete ρ N hComplete,
      partialTraceRight_trace, hρ.2]
  have hg := gentle_finite_branches (fun k => bobMarginal ρ (N k))
    (fun k => M k ⊗ₖ (1 : QMatrix E))
    (fun k => bobMarginal_posSemidef hρ.1 (hN k)) hMass
    (fun k => tensor_identity_isEffect (hM k)) hQ
  have hBefore : (∑ k, (Q * bobMarginal ρ (N k)).trace.re) =
      (Q * partialTraceRight ρ).trace.re := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum,
      bobMarginal_complete ρ N hComplete]
  have hAccept : (∑ k, (bobMarginal ρ (N k) *
      (M k ⊗ₖ (1 : QMatrix E))).trace.re) =
      (acceptedEffect (fun k => M k ⊗ₖ (1 : QMatrix E)) N * ρ).trace.re := by
    simp only [acceptedEffect, Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.trace_mul_comm, bobMarginal_trace_pair]
  have hAfter : (∑ k, (Q * (CFC.sqrt (M k ⊗ₖ (1 : QMatrix E)) *
      bobMarginal ρ (N k) * CFC.sqrt (M k ⊗ₖ (1 : QMatrix E)))).trace.re) =
      (composedEffect M N Q * ρ).trace.re := by
    rw [composedEffect_trace]
    simp only [postselectedAE, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum,
      ← aliceRoot_eq_sqrt (hM _).1, (aliceRoot_isHermitian (M _)).eq]
  rwa [hBefore, hAccept, hAfter] at hg

theorem composedEffect_typeI (M : K → QMatrix A) (N : K → QMatrix B)
    (hM : ∀ k, FlaggedStates.IsEffect (M k)) (hN : ∀ k, (N k).PosSemidef)
    (hComplete : (1 - ∑ k, N k).PosSemidef) {Q : QMatrix (A × E)}
    (hQ : FlaggedStates.IsEffect Q) {ρ : QMatrix ((A × E) × B)}
    (hρ : FlaggedStates.IsDensity ρ) :
    (Q * partialTraceRight ρ).trace.re -
      2 * Real.sqrt (1 -
        (acceptedEffect (fun k => M k ⊗ₖ (1 : QMatrix E)) N * ρ).trace.re) ≤
      (composedEffect M N Q * ρ).trace.re := by
  have hM' : ∀ z, FlaggedStates.IsEffect (aliceAccepted M z) := by
    intro z
    cases z with
    | none => exact ⟨Matrix.PosSemidef.zero, by simpa only [aliceAccepted, sub_zero] using
        (Matrix.PosSemidef.one : (1 : QMatrix A).PosSemidef)⟩
    | some k => exact hM k
  have hg := composedEffect_typeI_complete (aliceAccepted M) (bobFirstEffect N) hM'
    (bobFirstBinaryPOVM M N hM hN hComplete).alice_positive
    (bobFirstBinaryPOVM M N hM hN hComplete).alice_complete hQ hρ
  simpa only [acceptedEffect, composedEffect, Fintype.sum_option, aliceAccepted,
    bobFirstEffect, aliceRoot, CFC.sqrt_zero, Matrix.zero_kronecker,
    Matrix.zero_mul, Matrix.mul_zero, Matrix.conjTranspose_zero, zero_add] using hg

def aeGrouping : ((A × E) × B) ≃ (A × (E × B)) where
  toFun x := (x.1.1, (x.1.2, x.2))
  invFun x := ((x.1, x.2.1), x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def regroupAE (ρ : QMatrix (A × (E × B))) : QMatrix ((A × E) × B) :=
  ρ.submatrix aeGrouping aeGrouping

omit [DecidableEq B] in
theorem bobMarginal_apply (ρ : QMatrix (A × B)) (N : QMatrix B) (i j : A) :
    bobMarginal ρ N i j = ∑ b, ∑ c, ρ (i, b) (j, c) * N c b := by
  simp only [bobMarginal, partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft,
    Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_const_zero,
    Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

omit [DecidableEq B] in
theorem bobMarginal_regroup_product (a : QMatrix A) (b : QMatrix (E × B))
    (N : QMatrix B) :
    bobMarginal (regroupAE (a ⊗ₖ b)) N = a ⊗ₖ bobMarginal b N := by
  ext i j
  simp only [bobMarginal_apply, regroupAE, Matrix.submatrix_apply, aeGrouping,
    Equiv.coe_fn_mk, Matrix.kroneckerMap_apply, Finset.mul_sum, mul_assoc]

def bobBranchLinearMap (N : QMatrix B) : QMatrix (A × B) →ₗ[ℂ] QMatrix A where
  toFun := fun ρ => bobMarginal ρ N
  map_add' := by
    intro ρ σ
    ext i j
    simp only [bobMarginal_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c ρ
    ext i j
    simp only [bobMarginal_apply, Matrix.smul_apply, smul_mul_assoc, Finset.smul_sum,
      RingHom.id_apply]

def postselectedLinearMap (M : K → QMatrix A) (N : K → QMatrix B) :
    QMatrix ((A × E) × B) →ₗ[ℂ] QMatrix (A × E) where
  toFun := postselectedAE M N
  map_add' := by
    intro ρ σ
    have hb (k : K) : bobMarginal (ρ + σ) (N k) =
        bobMarginal ρ (N k) + bobMarginal σ (N k) :=
      (bobBranchLinearMap (N k)).map_add ρ σ
    simp only [postselectedAE, hb, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c ρ
    have hb (k : K) : bobMarginal (c • ρ) (N k) = c • bobMarginal ρ (N k) :=
      (bobBranchLinearMap (N k)).map_smul c ρ
    simp only [postselectedAE, hb, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum,
      RingHom.id_apply]

def regroupLinearMap : QMatrix (A × (E × B)) →ₗ[ℂ] QMatrix ((A × E) × B) where
  toFun := regroupAE
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def conditionalAELinearMap (M : K → QMatrix A) (N : K → QMatrix B) :
    QMatrix (A × (E × B)) →ₗ[ℂ] QMatrix (A × E) :=
  (postselectedLinearMap M N).comp regroupLinearMap

omit [DecidableEq K] [DecidableEq B] in
theorem postselectedAE_regroup_product (M : K → QMatrix A) (N : K → QMatrix B)
    (a : QMatrix A) (b : QMatrix (E × B)) :
    postselectedAE M N (regroupAE (a ⊗ₖ b)) =
      ∑ k, (CFC.sqrt (M k) * a * (CFC.sqrt (M k))ᴴ) ⊗ₖ bobMarginal b (N k) := by
  simp only [postselectedAE, bobMarginal_regroup_product, aliceRoot,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

omit [DecidableEq K] in

theorem postselectedAE_mem_cone (M : K → QMatrix A) (N : K → QMatrix B)
    (hN : ∀ k, (N k).PosSemidef) {ρ : QMatrix (A × (E × B))}
    (hρ : ρ ∈ BCYMeasurement.separableCone A (E × B)) :
    postselectedAE M N (regroupAE ρ) ∈ BCYMeasurement.separableCone A E := by
  classical
  obtain ⟨w, hw, hw0, heq⟩ := PointedCone.mem_hull_set.mp hρ
  change (∑ S ∈ w.support, w S • S) = ρ at heq
  change conditionalAELinearMap M N ρ ∈ BCYMeasurement.separableCone A E
  rw [← heq, map_sum]
  apply (BCYMeasurement.separableCone A E).sum_mem
  intro S hS
  rw [LinearMap.map_smul_of_tower]
  apply PointedCone.smul_mem _ (hw0 _)
  obtain ⟨a, b, rfl⟩ := hw hS
  change postselectedAE M N (regroupAE (a.matrix ⊗ₖ b.matrix)) ∈ _
  rw [postselectedAE_regroup_product]
  apply (BCYMeasurement.separableCone A E).sum_mem
  intro k _
  exact BCYMeasurement.product_mem_cone
    (a.positive.mul_mul_conjTranspose_same _) (bobMarginal_posSemidef b.positive (hN k))

def abGrouping : ((A × B) × E) ≃ ((A × E) × B) where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def abMarginal (ρ : QMatrix ((A × E) × B)) : QMatrix (A × B) :=
  partialTraceRight (ρ.submatrix abGrouping abGrouping)

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq E] in
theorem abMarginal_apply (ρ : QMatrix ((A × E) × B)) (i j : A × B) :
    abMarginal ρ i j = ∑ e, ρ ((i.1, e), i.2) ((j.1, e), j.2) := rfl

omit [DecidableEq A] [DecidableEq B] [DecidableEq E] in
theorem abMarginal_posSemidef {ρ : QMatrix ((A × E) × B)} (hρ : ρ.PosSemidef) :
    (abMarginal ρ).PosSemidef := partialTraceRight_positive (hρ.submatrix _)

omit [DecidableEq A] [DecidableEq B] [DecidableEq E] in
theorem abMarginal_trace (ρ : QMatrix ((A × E) × B)) :
    (abMarginal ρ).trace = ρ.trace := by
  rw [abMarginal, partialTraceRight_trace]
  exact abGrouping.sum_comp (fun i => ρ i i)

def abDensity (ρ : Density ((A × E) × B)) : Density (A × B) where
  matrix := abMarginal ρ.matrix
  positive := abMarginal_posSemidef ρ.positive
  trace_one := (abMarginal_trace ρ.matrix).trans ρ.trace_one

def abMarginalLinearMap : QMatrix ((A × E) × B) →ₗ[ℂ] QMatrix (A × B) where
  toFun := abMarginal
  map_add' := by
    intro ρ σ
    ext i j
    simp only [abMarginal_apply, Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' := by
    intro c ρ
    ext i j
    simp only [abMarginal_apply, Matrix.smul_apply, Finset.smul_sum, RingHom.id_apply]

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq E] in
theorem abMarginal_regroup_product (a : QMatrix A) (b : QMatrix (E × B)) :
    abMarginal (regroupAE (a ⊗ₖ b)) = a ⊗ₖ partialTraceLeft b := by
  ext i j
  simp only [abMarginal_apply, regroupAE, Matrix.submatrix_apply, aeGrouping,
    Equiv.coe_fn_mk, Matrix.kroneckerMap_apply, partialTraceLeft,
    QuantumProver.WernerEndpoint.partialTraceRight, Finset.mul_sum]

theorem abMarginal_mem_cone {ρ : QMatrix (A × (E × B))}
    (hρ : ρ ∈ BCYMeasurement.separableCone A (E × B)) :
    abMarginal (regroupAE ρ) ∈ BCYMeasurement.separableCone A B := by
  classical
  let L := (abMarginalLinearMap (A := A) (B := B) (E := E)).comp regroupLinearMap
  obtain ⟨w, hw, hw0, heq⟩ := PointedCone.mem_hull_set.mp hρ
  change (∑ S ∈ w.support, w S • S) = ρ at heq
  change L ρ ∈ BCYMeasurement.separableCone A B
  rw [← heq, map_sum]
  apply (BCYMeasurement.separableCone A B).sum_mem
  intro S hS
  rw [LinearMap.map_smul_of_tower]
  apply PointedCone.smul_mem _ (hw0 _)
  obtain ⟨a, b, rfl⟩ := hw hS
  change abMarginal (regroupAE (a.matrix ⊗ₖ b.matrix)) ∈ _
  rw [abMarginal_regroup_product]
  exact BCYMeasurement.product_mem_cone a.positive (partialTraceLeft_positive b.positive)

theorem abMarginal_isSeparable {ρ : QMatrix (A × (E × B))}
    (hρ : FlaggedStates.IsDensity ρ) (hsep : IsSeparable ρ) :
    IsSeparable (abMarginal (regroupAE ρ)) := by
  have ht : (abMarginal (regroupAE ρ)).trace = 1 := by
    rw [abMarginal_trace]
    exact (aeGrouping.sum_comp (fun i => ρ i i)).trans hρ.2
  have hc := BCYMeasurement.normalize_cone_isSeparable
    (abMarginal_mem_cone (BCYMeasurement.isSeparable_mem_cone hsep))
    (by rw [ht]; norm_num)
  simpa only [ht, Complex.one_re, inv_one, one_smul] using hc

omit [DecidableEq K] in
theorem acceptedEffect_abMarginal_trace (M : K → QMatrix A) (N : K → QMatrix B)
    (ρ : QMatrix ((A × E) × B)) :
    (acceptedEffect (fun k => M k ⊗ₖ (1 : QMatrix E)) N * ρ).trace =
      (acceptedEffect M N * abMarginal ρ).trace := by
  let L := acceptedEffect (fun k => M k ⊗ₖ (1 : QMatrix E)) N
  have heq : L.submatrix abGrouping abGrouping =
      acceptedEffect M N ⊗ₖ (1 : QMatrix E) := by
    ext i j
    simp only [L, acceptedEffect, Matrix.submatrix_apply, Matrix.sum_apply,
      abGrouping, Equiv.coe_fn_mk, Matrix.kroneckerMap_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    _ = ((L * ρ).submatrix abGrouping abGrouping).trace :=
      (abGrouping.sum_comp (fun i => (L * ρ) i i)).symm
    _ = ((acceptedEffect M N ⊗ₖ (1 : QMatrix E)) *
        ρ.submatrix abGrouping abGrouping).trace := by
      rw [← Matrix.submatrix_mul_equiv L ρ abGrouping abGrouping abGrouping, heq]
    _ = (ρ.submatrix abGrouping abGrouping *
        (acceptedEffect M N ⊗ₖ (1 : QMatrix E))).trace := Matrix.trace_mul_comm _ _
    _ = (abMarginal ρ * acceptedEffect M N).trace :=
      QuantumProver.QuantumEntropy.partialTrace_right_mul_trace _ _
    _ = _ := Matrix.trace_mul_comm _ _

section SeparatorBound

theorem cone_effect_bound {X : QMatrix (A × E)}
    (hX : X ∈ BCYMeasurement.separableCone A E) (Q : QMatrix (A × E)) {α : ℝ}
    (hQsep : ∀ σ : Density (A × E), IsSeparable σ.matrix →
      (Q * σ.matrix).trace.re ≤ α) :
    (Q * X).trace.re ≤ α * X.trace.re := by
  have hp := BCYMeasurement.cone_posSemidef hX
  have ht : 0 ≤ X.trace.re := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  by_cases hz : X.trace.re = 0
  · have hzero : X = 0 := hp.trace_eq_zero_iff.mp (by
      apply Complex.ext
      · exact hz
      · exact (Complex.nonneg_iff.mp hp.trace_nonneg).2.symm)
    simp only [hzero, Matrix.trace_zero, Complex.zero_re, mul_zero,
      le_refl]
  · have hpos : 0 < X.trace.re := lt_of_le_of_ne ht (Ne.symm hz)
    have h := hQsep (BCYMeasurement.normalizedDensity X hp hpos)
      (BCYMeasurement.normalize_cone_isSeparable hX hpos)
    simp only [BCYMeasurement.normalizedDensity, Matrix.mul_smul, Matrix.trace_smul,
      Complex.smul_re, smul_eq_mul] at h
    have hm := mul_le_mul_of_nonneg_left h ht
    rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul] at hm
    simpa only [mul_comm] using hm

omit [DecidableEq K] in

theorem composedEffect_separable_bound (M : K → QMatrix A) (N : K → QMatrix B)
    (hM : ∀ k, (M k).PosSemidef) (hN : ∀ k, (N k).PosSemidef)
    (Q : QMatrix (A × E)) {α β : ℝ} (hα : 0 ≤ α)
    (hQsep : ∀ σ : Density (A × E), IsSeparable σ.matrix →
      (Q * σ.matrix).trace.re ≤ α)
    (hSsep : ∀ σ : Density (A × B), IsSeparable σ.matrix →
      (acceptedEffect M N * σ.matrix).trace.re ≤ β)
    (ρ : Density (A × (E × B))) (hρ : IsSeparable ρ.matrix) :
    (composedEffect M N Q * regroupAE ρ.matrix).trace.re ≤ α * β := by
  have hc := postselectedAE_mem_cone M N hN (BCYMeasurement.isSeparable_mem_cone hρ)
  have hb := cone_effect_bound hc Q hQsep
  have hp : (postselectedAE M N (regroupAE ρ.matrix)).trace.re =
      (acceptedEffect M N * abMarginal (regroupAE ρ.matrix)).trace.re := by
    rw [postselectedAE_trace M N hM, acceptedEffect_abMarginal_trace]
  have hd : FlaggedStates.IsDensity ρ.matrix := ⟨ρ.positive, ρ.trace_one⟩
  let σ : Density (A × B) :=
    { matrix := abMarginal (regroupAE ρ.matrix)
      positive := abMarginal_posSemidef (ρ.positive.submatrix _)
      trace_one := (abMarginal_trace _).trans
        ((aeGrouping.sum_comp (fun i => ρ.matrix i i)).trans ρ.trace_one) }
  have hs := hSsep σ (abMarginal_isSeparable hd hρ)
  rw [hp] at hb
  rw [composedEffect_trace]
  exact hb.trans (mul_le_mul_of_nonneg_left hs hα)

end SeparatorBound

def composedBinaryPOVM (M : K → QMatrix A) (N : K → QMatrix B)
    (hM : ∀ k, FlaggedStates.IsEffect (M k)) (hN : ∀ k, (N k).PosSemidef)
    (hComplete : (1 - ∑ k, N k).PosSemidef) {Q : QMatrix (A × E)}
    (hQ : FlaggedStates.IsEffect Q) : OneWayPOVM B (A × E) (Option K) Bool :=
  bobFirstBinaryPOVM (fun k => aliceRoot (M k) * Q * (aliceRoot (M k))ᴴ) N
    (fun k => sandwich_isEffect _ (tensor_identity_isEffect (hM k)) hQ
      (aliceRoot_gram (hM k).1)) hN hComplete

omit [DecidableEq K] in
theorem composedBinaryPOVM_accepted (M : K → QMatrix A) (N : K → QMatrix B)
    (hM : ∀ k, FlaggedStates.IsEffect (M k)) (hN : ∀ k, (N k).PosSemidef)
    (hComplete : (1 - ∑ k, N k).PosSemidef) {Q : QMatrix (A × E)}
    (hQ : FlaggedStates.IsEffect Q) :
    (∑ z, (composedBinaryPOVM M N hM hN hComplete hQ).alice z ⊗ₖ
      (composedBinaryPOVM M N hM hN hComplete hQ).bob z true).submatrix
        Prod.swap Prod.swap = composedEffect M N Q :=
  bobFirstBinaryPOVM_accepted _ _ _ _ _

omit [DecidableEq A] in
theorem partialTraceRight_lift_left (ρ : QMatrix (A × B)) (L : QMatrix A) :
    partialTraceRight ((L ⊗ₖ (1 : QMatrix B)) * ρ) = L * partialTraceRight ρ := by
  ext i j
  simp only [partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.mul_sum]
  exact Finset.sum_comm

omit [DecidableEq A] in
theorem partialTraceRight_lift_right (ρ : QMatrix (A × B)) (L : QMatrix A) :
    partialTraceRight (ρ * (L ⊗ₖ (1 : QMatrix B))) = partialTraceRight ρ * L := by
  ext i j
  calc
    _ = ∑ b, ∑ a, ρ (i, b) (a, b) * L a j := by
      simp [partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft, Matrix.mul_apply,
        Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, mul_ite]
    _ = ∑ a, ∑ b, ρ (i, b) (a, b) * L a j := Finset.sum_comm
    _ = _ := by
      simp only [Matrix.mul_apply, partialTraceRight, QuantumProver.WernerEndpoint.partialTraceLeft,
        Finset.sum_mul]

theorem local_branch_output (ρ : QMatrix (A × B)) (L : QMatrix A) {N : QMatrix B}
    (hN : N.PosSemidef) :
    partialTraceRight ((L ⊗ₖ CFC.sqrt N) * ρ * (L ⊗ₖ CFC.sqrt N)ᴴ) =
      L * bobMarginal ρ N * Lᴴ := by
  have heq : (L ⊗ₖ CFC.sqrt N) * ρ * (L ⊗ₖ CFC.sqrt N)ᴴ =
      (L ⊗ₖ (1 : QMatrix B)) *
        (((1 : QMatrix A) ⊗ₖ CFC.sqrt N) * ρ *
          ((1 : QMatrix A) ⊗ₖ CFC.sqrt N)ᴴ) *
        (Lᴴ ⊗ₖ (1 : QMatrix B)) := by
    have hf : L ⊗ₖ CFC.sqrt N =
        (L ⊗ₖ (1 : QMatrix B)) * ((1 : QMatrix A) ⊗ₖ CFC.sqrt N) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    rw [hf, Matrix.conjTranspose_mul]
    simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Matrix.mul_assoc]
  rw [heq, partialTraceRight_lift_right, partialTraceRight_lift_left,
    ← bobMarginal_eq_local_instrument ρ hN]

omit [DecidableEq K] in
theorem postselectedAE_eq_local_instrument (M : K → QMatrix A) (N : K → QMatrix B)
    (hN : ∀ k, (N k).PosSemidef) (ρ : QMatrix ((A × E) × B)) :
    postselectedAE M N ρ = ∑ k, partialTraceRight
      ((aliceRoot (M k) ⊗ₖ CFC.sqrt (N k)) * ρ *
        (aliceRoot (M k) ⊗ₖ CFC.sqrt (N k))ᴴ) := by
  simp only [local_branch_output ρ _ (hN _), postselectedAE]

omit [DecidableEq K] in
theorem bobFirstExtendedPOVM_fineKraus (M : K → QMatrix A) (N : K → QMatrix B)
    (hM : ∀ k, FlaggedStates.IsEffect (M k)) (hN : ∀ k, (N k).PosSemidef)
    (hComplete : (1 - ∑ k, N k).PosSemidef) (k : K) :
    (BCYMeasurement.fineKraus (bobFirstExtendedPOVM (E := E) M N hM hN hComplete)
      (some k, true)).submatrix Prod.swap Prod.swap =
      aliceRoot (M k) ⊗ₖ CFC.sqrt (N k) := by
  simp only [BCYMeasurement.fineKraus, bobFirstExtendedPOVM, bobFirstBinaryPOVM,
    bobFirstEffect, aliceAccepted, ite_true, ← aliceRoot_eq_sqrt (hM k).1]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Prod.swap]
  exact mul_comm _ _

theorem composedEffect_typeI_tendsto
    {Aₙ Bₙ Eₙ Kₙ : ℕ → Type*}
    [∀ n, Fintype (Aₙ n)] [∀ n, Fintype (Bₙ n)]
    [∀ n, Fintype (Eₙ n)] [∀ n, Fintype (Kₙ n)]
    [∀ n, DecidableEq (Aₙ n)] [∀ n, DecidableEq (Bₙ n)]
    [∀ n, DecidableEq (Eₙ n)] [∀ n, DecidableEq (Kₙ n)]
    (M : ∀ n, Kₙ n → QMatrix (Aₙ n)) (N : ∀ n, Kₙ n → QMatrix (Bₙ n))
    (hM : ∀ n k, FlaggedStates.IsEffect (M n k))
    (hN : ∀ n k, (N n k).PosSemidef)
    (hComplete : ∀ n, (1 - ∑ k, N n k).PosSemidef)
    (Q : ∀ n, QMatrix (Aₙ n × Eₙ n)) (hQ : ∀ n, FlaggedStates.IsEffect (Q n))
    (ρ : ∀ n, Density ((Aₙ n × Eₙ n) × Bₙ n))
    (hQlim : Filter.Tendsto (fun n => (Q n * partialTraceRight (ρ n).matrix).trace.re)
      Filter.atTop (𝓝 1))
    (hSlim : Filter.Tendsto
      (fun n => (acceptedEffect (M n) (N n) * abMarginal (ρ n).matrix).trace.re)
      Filter.atTop (𝓝 1)) :
    Filter.Tendsto
      (fun n => (composedEffect (M n) (N n) (Q n) * (ρ n).matrix).trace.re)
      Filter.atTop (𝓝 1) := by
  have hroot : Filter.Tendsto
      (fun n => Real.sqrt (1 -
        (acceptedEffect (M n) (N n) * abMarginal (ρ n).matrix).trace.re))
      Filter.atTop (𝓝 0) := by
    have hsub := (tendsto_const_nhds (x := (1 : ℝ))).sub hSlim
    simpa only [sub_self, Real.sqrt_zero, Function.comp_def] using
      (Real.continuous_sqrt.tendsto (1 - (1 : ℝ))).comp hsub
  have hLower : Filter.Tendsto
      (fun n => (Q n * partialTraceRight (ρ n).matrix).trace.re -
        2 * Real.sqrt (1 -
          (acceptedEffect (M n) (N n) * abMarginal (ρ n).matrix).trace.re))
      Filter.atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using
      hQlim.sub ((tendsto_const_nhds (x := (2 : ℝ))).mul hroot)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hLower tendsto_const_nhds
  · intro n
    have h := composedEffect_typeI (M n) (N n) (hM n) (hN n) (hComplete n)
      (hQ n) ⟨(ρ n).positive, (ρ n).trace_one⟩
    rwa [acceptedEffect_abMarginal_trace] at h
  · intro n
    have h := (FlaggedStates.acceptanceProbability_bounds
      (A := (ρ n).matrix) ⟨(ρ n).positive, (ρ n).trace_one⟩
      (composedEffect_isEffect (M n) (N n) (hM n) (hN n) (hComplete n) (hQ n))).2
    change ((ρ n).matrix * composedEffect (M n) (N n) (Q n)).trace.re ≤ 1 at h
    rwa [Matrix.trace_mul_comm] at h

theorem finite_test_composition (M : K → QMatrix A) (N : K → QMatrix B)
    (hM : ∀ k, FlaggedStates.IsEffect (M k)) (hN : ∀ k, (N k).PosSemidef)
    (hComplete : (1 - ∑ k, N k).PosSemidef) {Q : QMatrix (A × E)}
    (hQ : FlaggedStates.IsEffect Q) {α β : ℝ} (hα : 0 ≤ α)
    (hQsep : ∀ σ : Density (A × E), IsSeparable σ.matrix →
      (Q * σ.matrix).trace.re ≤ α)
    (hSsep : ∀ σ : Density (A × B), IsSeparable σ.matrix →
      (acceptedEffect M N * σ.matrix).trace.re ≤ β) :
    FlaggedStates.IsEffect (composedEffect M N Q) ∧
    (∃ P : OneWayPOVM B (A × E) (Option K) Bool,
      (∑ z, P.alice z ⊗ₖ P.bob z true).submatrix Prod.swap Prod.swap =
        composedEffect M N Q) ∧
    (∀ ρ : Density (A × (E × B)), IsSeparable ρ.matrix →
      (composedEffect M N Q * regroupAE ρ.matrix).trace.re ≤ α * β) ∧
    (∀ ρ : Density ((A × E) × B),
      (Q * partialTraceRight ρ.matrix).trace.re -
        2 * Real.sqrt (1 - (acceptedEffect M N * abMarginal ρ.matrix).trace.re) ≤
        (composedEffect M N Q * ρ.matrix).trace.re) := by
  refine ⟨composedEffect_isEffect M N hM hN hComplete hQ,
    ⟨composedBinaryPOVM M N hM hN hComplete hQ,
      composedBinaryPOVM_accepted M N hM hN hComplete hQ⟩,
    composedEffect_separable_bound M N (fun k => (hM k).1) hN Q hα hQsep hSsep, ?_⟩
  intro ρ
  have h := composedEffect_typeI M N hM hN hComplete hQ ⟨ρ.positive, ρ.trace_one⟩
  rwa [acceptedEffect_abMarginal_trace] at h

end QuantumProver.DepolarizingSquashedEntanglement.BCYTestComposition
