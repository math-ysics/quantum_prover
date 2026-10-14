import QuantumProver.InformationTheory.SuperchannelDiscrimination.CommonWrapperRegularization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace QuantumProver.SuperchannelDiscrimination.ChannelChoiSupport

open Matrix KrausCompletion CPWrappers FlaggedStates TensorEntropy ChannelRegularization
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.L2Operator

variable {I O J : Type*} [Fintype I] [Fintype O] [Fintype J]
  [DecidableEq I] [DecidableEq O] [DecidableEq J]

def entangledVector (I : Type*) [DecidableEq I] : I × I → ℂ :=
  fun x => if x.1 = x.2 then 1 else 0

def entangledMatrix (I : Type*) [DecidableEq I] : Matrix (I × I) (I × I) ℂ :=
  Matrix.vecMulVec (entangledVector I) (star (entangledVector I))

def normalization (I : Type*) [Fintype I] : ℂ := ((Fintype.card I : ℝ)⁻¹ : ℝ)

def maximallyEntangledInput (I : Type*) [Fintype I] [DecidableEq I] :
    Matrix (I × I) (I × I) ℂ := normalization I • entangledMatrix I

theorem entangledMatrix_posSemidef : (entangledMatrix I).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem entangledMatrix_trace : (entangledMatrix I).trace = (Fintype.card I : ℂ) := by
  simp [entangledMatrix, entangledVector, Matrix.trace, Matrix.diag,
    Matrix.vecMulVec, Fintype.sum_prod_type]

theorem normalization_nonneg : 0 ≤ normalization I := by
  exact Complex.nonneg_iff.mpr ⟨inv_nonneg.mpr (Nat.cast_nonneg _), by simp [normalization]⟩

theorem normalization_ne_zero [Nonempty I] : normalization I ≠ 0 := by
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa [normalization] using inv_ne_zero hc

theorem maximallyEntangledInput_isDensity [Nonempty I] :
    IsDensity (maximallyEntangledInput I) := by
  refine ⟨entangledMatrix_posSemidef.smul normalization_nonneg, ?_⟩
  have hc : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [maximallyEntangledInput, Matrix.trace_smul, entangledMatrix_trace,
    normalization, smul_eq_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
  exact inv_mul_cancel₀ hc

def normalizedChoi (Φ : FiniteCPTP I O) : Matrix (I × O) (I × O) ℂ :=
  normalization I • CPTPKraus.choi Φ.map

theorem maximallyEntangledInput_output (Φ : FiniteCPTP I O) :
    Matrix.reindex (Equiv.prodComm O I) (Equiv.prodComm O I)
        (amplify Φ.map I (maximallyEntangledInput I)) = normalizedChoi Φ := by
  ext ⟨i, o⟩ ⟨j, p⟩
  have hs : (fun a b => maximallyEntangledInput I (a, i) (b, j)) =
      normalization I • Matrix.single i j (1 : ℂ) := by
    ext a b
    by_cases ha : a = i
    · subst a
      by_cases hb : b = j
      · subst b
        simp [maximallyEntangledInput, entangledMatrix, entangledVector,
          Matrix.vecMulVec, Matrix.single_apply]
      · simp [maximallyEntangledInput, entangledMatrix, entangledVector,
          Matrix.vecMulVec, Matrix.single_apply, hb, Ne.symm hb]
    · simp [maximallyEntangledInput, entangledMatrix, entangledVector,
        Matrix.vecMulVec, Matrix.single_apply, ha, Ne.symm ha]
  change Φ.map (fun a b => maximallyEntangledInput I (a, i) (b, j)) o p = _
  rw [hs, map_smul]
  rfl

theorem normalizedChoi_isDensity (Φ : FiniteCPTP I O) [Nonempty I] :
    IsDensity (normalizedChoi Φ) := by
  rw [← maximallyEntangledInput_output]
  have h := channel_density (amplifiedChannel Φ I)
    maximallyEntangledInput_isDensity.1 maximallyEntangledInput_isDensity.2
  exact channel_density (reindexChannel (Equiv.prodComm O I)) h.1 h.2

def oneIndex (A : Type*) : TensorIndex A 1 ≃ A where
  toFun x := x.2
  invFun a := (PUnit.unit, a)
  left_inv x := by apply Prod.ext; exact Subsingleton.elim _ _; rfl
  right_inv _ := rfl

theorem channelPower_one_intertwine (Φ : FiniteCPTP I O)
    (X : Matrix (TensorIndex I 1) (TensorIndex I 1) ℂ) :
    Φ.map (Matrix.reindex (oneIndex I) (oneIndex I) X) =
      Matrix.reindex (oneIndex O) (oneIndex O)
        ((channelPower Φ 1).map X) := by
  have hmap : (reindexMap (oneIndex O)).comp (channelPower Φ 1).map =
      Φ.map.comp (reindexMap (oneIndex I)) := by
    apply matrixMap_ext_units
    intro ⟨u, i⟩ ⟨v, j⟩
    cases u
    cases v
    simp only [LinearMap.comp_apply, reindexMap_apply, reindex_single,
      channelPower_map_single]
    ext o p
    change (1 : ℂ) * Φ.map (Matrix.single i j 1) o p = Φ.map (Matrix.single i j 1) o p
    exact one_mul _
  exact (congrArg (fun F : Matrix (TensorIndex I 1) (TensorIndex I 1) ℂ →ₗ[ℂ]
    Matrix O O ℂ => F X) hmap).symm

theorem powerValue_one_eq_stabilized (Φ Ψ : FiniteCPTP I O) :
    powerValue Φ Ψ 1 = stabilizedRelativeEntropyBits Φ Ψ :=
  stabilizedRelativeEntropyBits_eq_of_intertwine (oneIndex I)
    (oneIndex O) _ _ Φ Ψ (channelPower_one_intertwine Φ)
      (channelPower_one_intertwine Ψ)

theorem stabilizedRelativeEntropyBits_le_regularized (Φ Ψ : FiniteCPTP I O) :
    stabilizedRelativeEntropyBits Φ Ψ ≤ regularizedRelativeEntropyBits Φ Ψ := by
  have h := normalizedPowerValue_le_regularized Φ Ψ Nat.zero_lt_one
  simpa only [normalizedPowerValue, ExtendedFekete.normalized, Nat.cast_one,
    inv_one, EReal.coe_one, one_mul, powerValue_one_eq_stabilized] using h

theorem normalizedChoi_entropy_le_regularized (Φ Ψ : FiniteCPTP I O) [Nonempty I] :
    relativeEntropyBits (normalizedChoi Φ) (normalizedChoi Ψ) ≤
      regularizedRelativeEntropyBits Φ Ψ := by
  have hΦ : IsDensity (amplify Φ.map I (maximallyEntangledInput I)) :=
    channel_density (amplifiedChannel Φ I)
    maximallyEntangledInput_isDensity.1 maximallyEntangledInput_isDensity.2
  have hΨ : IsDensity (amplify Ψ.map I (maximallyEntangledInput I)) :=
    channel_density (amplifiedChannel Ψ I)
    maximallyEntangledInput_isDensity.1 maximallyEntangledInput_isDensity.2
  rw [← maximallyEntangledInput_output, ← maximallyEntangledInput_output,
    relativeEntropyBits_reindex (Equiv.prodComm O I) hΦ.1 hΨ.1]
  exact (stabilizedRelativeEntropyBits_witness_le Φ Ψ I
    maximallyEntangledInput_isDensity).trans
      (stabilizedRelativeEntropyBits_le_regularized Φ Ψ)

theorem hasSupportIn_smul_iff {A B : Matrix J J ℂ} {c : ℂ} (hc : c ≠ 0) :
    HasSupportIn (c • A) (c • B) ↔ HasSupportIn A B := by
  constructor
  · intro h v hv
    have hv' : (c • B) *ᵥ v = 0 := by rw [Matrix.smul_mulVec, hv, smul_zero]
    have hA := h v hv'
    rw [Matrix.smul_mulVec] at hA
    exact (smul_eq_zero.mp hA).resolve_left hc
  · intro h v hv
    rw [Matrix.smul_mulVec] at hv
    have hB := (smul_eq_zero.mp hv).resolve_left hc
    rw [Matrix.smul_mulVec, h v hB, smul_zero]

theorem choi_support_of_regularized_le_real (Φ Ψ : FiniteCPTP I O)
    [Nonempty I] {B : ℝ} (hB : regularizedRelativeEntropyBits Φ Ψ ≤ (B : EReal)) :
    HasSupportIn (CPTPKraus.choi Φ.map) (CPTPKraus.choi Ψ.map) := by
  have hs := hasSupportIn_of_relativeEntropyBits_le_real
    ((normalizedChoi_entropy_le_regularized Φ Ψ).trans hB)
  exact (hasSupportIn_smul_iff normalization_ne_zero).mp hs

theorem exists_pos_smul_bound_of_posDef {A B : Matrix J J ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ((c : ℂ) • B - A).PosSemidef := by
  let U := CFC.sqrt B
  have hU : U.PosSemidef := (CFC.sqrt_nonneg B).posSemidef
  have hUunit : IsUnit U := hB.isStrictlyPositive.isUnit_cfcSqrt B
  have hUinv : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U
    ((Matrix.isUnit_iff_isUnit_det U).mp hUunit)
  have hInvU : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U
    ((Matrix.isUnit_iff_isUnit_det U).mp hUunit)
  have hUU : U * U = B := CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg
  let T := U⁻¹ * A * U⁻¹
  have hT : T.PosSemidef := by
    simpa only [(hU.inv).isHermitian.eq] using hA.mul_mul_conjTranspose_same U⁻¹
  have ht : (‖T‖ • (1 : Matrix J J ℂ) - T).PosSemidef := by
    apply Matrix.le_iff.mp
    simpa only [Algebra.algebraMap_eq_smul_one] using
      IsSelfAdjoint.le_algebraMap_norm_self T hT.isHermitian.isSelfAdjoint
  have hrec : U * T * U = A := by
    calc
      U * T * U = (U * U⁻¹) * A * (U⁻¹ * U) := by dsimp [T]; noncomm_ring
      _ = A := by rw [hUinv, hInvU, Matrix.one_mul, Matrix.mul_one]
  have hcong : U * (‖T‖ • (1 : Matrix J J ℂ) - T) * Uᴴ = ‖T‖ • B - A := by
    rw [hU.isHermitian.eq, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU, hrec]
  have hb : (‖T‖ • B - A).PosSemidef := by
    rw [← hcong]
    exact ht.mul_mul_conjTranspose_same U
  refine ⟨‖T‖ + 1, by positivity, ?_⟩
  have heq : ((‖T‖ + 1 : ℝ) : ℂ) • B - A = (‖T‖ • B - A) + B := by
    ext i j
    simp [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_add]
    ring
  rw [heq]
  exact hb.add hB.posSemidef

theorem exists_pos_smul_bound_of_support {A B : Matrix J J ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hs : HasSupportIn A B) :
    ∃ c : ℝ, 0 < c ∧ ((c : ℂ) • B - A).PosSemidef := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_smul_bound_of_posDef
    (InputSupport.compress_posSemidef hB hA) (InputSupport.compress_comparator_posDef hB)
  refine ⟨c, hc, ?_⟩
  have heq : (c : ℂ) • B - A =
      ZeroExtension.extend (OutputSupport.supportIsometry hB)
        ((c : ℂ) • InputSupport.compress hB B - InputSupport.compress hB A) := by
    conv_lhs => rw [InputSupport.reconstruct_comparator hB,
      InputSupport.reconstruct_of_hasSupportIn hA.isHermitian hB hs]
    simp only [ZeroExtension.extend, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  rw [heq]
  exact ZeroExtension.extend_posSemidef _ hbound

theorem exists_pos_cpDom_of_regularized_le_real (Φ Ψ : FiniteCPTP I O)
    [Nonempty I] {B : ℝ} (hB : regularizedRelativeEntropyBits Φ Ψ ≤ (B : EReal)) :
    ∃ c : ℝ, 0 < c ∧ CPTPKraus.CPDom Φ.map Ψ.map c := by
  have hΦ := (CPTPKraus.choi_posSemidef_iff_completelyPositive Φ.map).mpr
    ((AbstractDPI.completelyPositive_iff _).mp Φ.completelyPositive)
  have hΨ := (CPTPKraus.choi_posSemidef_iff_completelyPositive Ψ.map).mpr
    ((AbstractDPI.completelyPositive_iff _).mp Ψ.completelyPositive)
  obtain ⟨c, hc, horder⟩ := exists_pos_smul_bound_of_support hΦ hΨ
    (choi_support_of_regularized_le_real Φ Ψ hB)
  exact ⟨c, hc, (CPTPKraus.choi_cp_order_iff Φ.map Ψ.map c).mp horder⟩

theorem choi_support_of_regularized_ne_top (Φ Ψ : FiniteCPTP I O)
    [Nonempty I] (hfinite : regularizedRelativeEntropyBits Φ Ψ ≠ ⊤) :
    HasSupportIn (CPTPKraus.choi Φ.map) (CPTPKraus.choi Ψ.map) := by
  exact choi_support_of_regularized_le_real Φ Ψ
    (le_of_eq (EReal.coe_toReal hfinite (regularizedRelativeEntropyBits_ne_bot Φ Ψ)).symm)

theorem exists_pos_cpDom_of_regularized_ne_top (Φ Ψ : FiniteCPTP I O)
    [Nonempty I] (hfinite : regularizedRelativeEntropyBits Φ Ψ ≠ ⊤) :
    ∃ c : ℝ, 0 < c ∧ CPTPKraus.CPDom Φ.map Ψ.map c := by
  exact exists_pos_cpDom_of_regularized_le_real Φ Ψ
    (le_of_eq (EReal.coe_toReal hfinite (regularizedRelativeEntropyBits_ne_bot Φ Ψ)).symm)

theorem cpDom_mono (Φ Ψ : FiniteCPTP I O) {c d : ℝ}
    (hdom : CPTPKraus.CPDom Φ.map Ψ.map c) (hcd : c ≤ d) :
    CPTPKraus.CPDom Φ.map Ψ.map d := by
  apply (CPTPKraus.choi_cp_order_iff Φ.map Ψ.map d).mp
  have hbase := (CPTPKraus.choi_cp_order_iff Φ.map Ψ.map c).mpr hdom
  have hΨ := (CPTPKraus.choi_posSemidef_iff_completelyPositive Ψ.map).mpr
    ((AbstractDPI.completelyPositive_iff _).mp Ψ.completelyPositive)
  have hdiff : (0 : ℂ) ≤ ((d - c : ℝ) : ℂ) :=
    Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr hcd, by simp⟩
  have h := hbase.add (hΨ.smul hdiff)
  have heq : ((c : ℂ) • CPTPKraus.choi Ψ.map - CPTPKraus.choi Φ.map) +
      ((d - c : ℝ) : ℂ) • CPTPKraus.choi Ψ.map =
      (d : ℂ) • CPTPKraus.choi Ψ.map - CPTPKraus.choi Φ.map := by
    ext i j
    simp [Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sub]
    ring
  rwa [heq] at h

theorem exists_twoPower_cpDom_of_regularized_ne_top (Φ Ψ : FiniteCPTP I O)
    [Nonempty I] (hfinite : regularizedRelativeEntropyBits Φ Ψ ≠ ⊤) :
    ∃ L : ℝ, regularizedRelativeEntropyBits Φ Ψ ≤ (L : EReal) ∧
      CPTPKraus.CPDom Φ.map Ψ.map ((2 : ℝ) ^ L) := by
  obtain ⟨c, hc, hdom⟩ := exists_pos_cpDom_of_regularized_ne_top Φ Ψ hfinite
  let L := max (Real.logb 2 c) (regularizedRelativeEntropyBits Φ Ψ).toReal
  have hreg := EReal.coe_toReal hfinite (regularizedRelativeEntropyBits_ne_bot Φ Ψ)
  have hpow : (2 : ℝ) ^ Real.logb 2 c = c :=
    Real.rpow_logb (by norm_num) (by norm_num) hc
  have hcL : c ≤ (2 : ℝ) ^ L := by
    rw [← hpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_max_left _ _)
  refine ⟨L, ?_, cpDom_mono Φ Ψ hdom hcL⟩
  rw [← hreg]
  exact EReal.coe_le_coe_iff.mpr (le_max_right _ _)

end QuantumProver.SuperchannelDiscrimination.ChannelChoiSupport
