import Mathlib
import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelUniformApproximation
import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelTestingPrimal
import QuantumProver.InformationTheory.SuperchannelDiscrimination.ChannelTestingPhysical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator Matrix Kronecker

namespace QuantumProver.SuperchannelDiscrimination.ChannelTestingDual

abbrev Hermitian (J : Type*) [Fintype J] [DecidableEq J] :=
  ↥(selfAdjoint.submodule ℝ (Matrix J J ℂ))

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem hermitian_val (X : Hermitian J) : (X : Matrix J J ℂ).IsHermitian := X.property

def tracePair : LinearMap.BilinForm ℝ (Hermitian J) where
  toFun X :=
    { toFun := fun Y => ((X : Matrix J J ℂ) * (Y : Matrix J J ℂ)).trace.re
      map_add' Y Z := by
        simp only [Submodule.coe_add, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
      map_smul' r Y := by
        simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re,
          smul_eq_mul, RingHom.id_apply] }
  map_add' X Y := by
    ext Z
    change (((X : Matrix J J ℂ) + (Y : Matrix J J ℂ)) * (Z : Matrix J J ℂ)).trace.re =
      ((X : Matrix J J ℂ) * (Z : Matrix J J ℂ)).trace.re +
        ((Y : Matrix J J ℂ) * (Z : Matrix J J ℂ)).trace.re
    simp only [Submodule.coe_add, Matrix.add_mul, Matrix.trace_add, Complex.add_re,
      LinearMap.add_apply]
  map_smul' r X := by
    ext Y
    change ((r • (X : Matrix J J ℂ)) * (Y : Matrix J J ℂ)).trace.re =
      r * ((X : Matrix J J ℂ) * (Y : Matrix J J ℂ)).trace.re
    simp only [Submodule.coe_smul, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re,
      LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem tracePair_self_eq_zero {X : Hermitian J} (hX : tracePair X X = 0) : X = 0 := by
  change ((X : Matrix J J ℂ) * (X : Matrix J J ℂ)).trace.re = 0 at hX
  have hg := Matrix.posSemidef_conjTranspose_mul_self (X : Matrix J J ℂ)
  have hr : (((X : Matrix J J ℂ)ᴴ * (X : Matrix J J ℂ)).trace).re = 0 := by
    simpa only [(hermitian_val X).eq, tracePair] using hX
  have ht : ((X : Matrix J J ℂ)ᴴ * (X : Matrix J J ℂ)).trace = 0 := by
    apply Complex.ext
    · simpa using hr
    · simpa using (Complex.nonneg_iff.mp hg.trace_nonneg).2.symm
  exact Subtype.ext (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp ht)

theorem tracePair_nondegenerate : (tracePair (J := J)).Nondegenerate := by
  constructor
  · intro X hX
    exact tracePair_self_eq_zero (hX X)
  · intro X hX
    exact tracePair_self_eq_zero (hX X)

theorem exists_tracePair_representation (f : Hermitian J →ₗ[ℝ] ℝ) :
    ∃ A : Hermitian J, ∀ X, tracePair A X = f X := by
  refine ⟨(tracePair.toDual tracePair_nondegenerate).symm f, ?_⟩
  intro X
  exact LinearMap.BilinForm.apply_toDual_symm_apply f X

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

def PrimalFeasible (rho : Matrix I I ℂ) (T : Matrix (I × O) (I × O) ℂ) : Prop :=
  FlaggedStates.IsDensity rho ∧ T.PosSemidef ∧ (rho ⊗ₖ (1 : Matrix O O ℂ) - T).PosSemidef

def primalValue (H : Matrix (I × O) (I × O) ℂ) : EReal :=
  ⨆ (rho : Matrix I I ℂ) (T : Matrix (I × O) (I × O) ℂ)
    (_h : PrimalFeasible rho T), (((H * T).trace.re : ℝ) : EReal)

def DualFeasible (H Z : Matrix (I × O) (I × O) ℂ) : Prop :=
  Z.PosSemidef ∧ (Z - H).PosSemidef

theorem traceOutput_pairing (Z : Matrix (I × O) (I × O) ℂ) (rho : Matrix I I ℂ) :
    (Z * (rho ⊗ₖ (1 : Matrix O O ℂ))).trace =
      (ChannelUniformApproximation.traceOutput Z * rho).trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_zero, mul_one,
    ChannelUniformApproximation.traceOutput,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem primal_objective_le_dual_objective
    {H Z : Matrix (I × O) (I × O) ℂ} {rho : Matrix I I ℂ}
    {T : Matrix (I × O) (I × O) ℂ} (hP : PrimalFeasible rho T) (hD : DualFeasible H Z) :
    (H * T).trace.re ≤ ChannelUniformApproximation.globalDualObjective Z := by
  have h1 := FlaggedStates.trace_mul_re_nonneg hD.2 hP.2.1
  have h2 := FlaggedStates.trace_mul_re_nonneg hD.1 hP.2.2
  have h3 := ChannelUniformApproximation.density_trace_pairing_abs_le_opNorm hP.1
    (ChannelUniformApproximation.traceOutput_posSemidef hD.1).isHermitian
  rw [Matrix.trace_mul_comm rho (ChannelUniformApproximation.traceOutput Z)] at h3
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at h1
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, traceOutput_pairing] at h2
  exact (by linarith : (H * T).trace.re ≤
    (ChannelUniformApproximation.traceOutput Z * rho).trace.re).trans
      ((le_abs_self _).trans h3)

theorem primalValue_le_dual_objective {H Z : Matrix (I × O) (I × O) ℂ}
    (hD : DualFeasible H Z) : primalValue H ≤ (ChannelUniformApproximation.globalDualObjective Z : EReal) := by
  refine iSup_le fun rho => iSup_le fun T => iSup_le fun hP => ?_
  exact EReal.coe_le_coe_iff.mpr (primal_objective_le_dual_objective hP hD)

theorem posSemidef_of_tracePair_nonneg {M : Matrix J J ℂ} (hM : M.IsHermitian)
    (h : ∀ W : Matrix J J ℂ, W.PosSemidef → 0 ≤ (M * W).trace.re) : M.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM
  intro x
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hM.im_star_dotProduct_mulVec_self x).symm⟩
  have hp := h (Matrix.vecMulVec x (star x)) (Matrix.posSemidef_vecMulVec_self_star x)
  simpa only [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] using hp

theorem realTrace_continuous : Continuous (fun M : Matrix J J ℂ => M.trace.re) :=
  Complex.continuous_re.comp (Matrix.traceLinearMap J ℂ ℂ).continuous_of_finiteDimensional

abbrev ConeSpace (I O : Type*) [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O] :=
  Hermitian (I × O) × Hermitian I

def certificateConeSet : Set (ConeSpace I O) :=
  {p | ∃ Z : Matrix (I × O) (I × O) ℂ, Z.PosSemidef ∧
    (Z - (p.1 : Matrix (I × O) (I × O) ℂ)).PosSemidef ∧
    ((p.2 : Matrix I I ℂ) - ChannelUniformApproximation.traceOutput Z).PosSemidef}

theorem certificateConeSet_closed : IsClosed (certificateConeSet (I := I) (O := O)) := by
  apply IsSeqClosed.isClosed
  intro p q hp hq
  choose Z hZ0 hZ1 hZ2 using hp
  have ht : Tendsto (fun n => ((p n).2 : Matrix I I ℂ).trace.re) atTop
      (𝓝 (q.2 : Matrix I I ℂ).trace.re) :=
    (realTrace_continuous.comp (continuous_subtype_val.comp continuous_snd)).tendsto q |>.comp hq
  obtain ⟨M, hM⟩ := ht.bddAbove_range
  have hbound (n : ℕ) : ‖Z n‖ ≤ M := by
    have htr := (Complex.nonneg_iff.mp (hZ2 n).trace_nonneg).1
    rw [Matrix.trace_sub, Complex.sub_re, ChannelUniformApproximation.traceOutput_trace] at htr
    exact (ChannelUniformApproximation.posSemidef_opNorm_le_trace (hZ0 n)).trans
      ((by linarith : (Z n).trace.re ≤ ((p n).2 : Matrix I I ℂ).trace.re).trans
        (hM (mem_range_self n)))
  obtain ⟨W, _hWball, phi, hphi, hW⟩ :=
    (isCompact_closedBall (0 : Matrix (I × O) (I × O) ℂ) M).tendsto_subseq
      (fun n => by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound n)
  have hp' := hq.comp hphi.tendsto_atTop
  have hp1 : Tendsto (fun n => ((p (phi n)).1 : Matrix (I × O) (I × O) ℂ)) atTop
      (𝓝 (q.1 : Matrix (I × O) (I × O) ℂ)) :=
    (continuous_subtype_val.comp continuous_fst).tendsto q |>.comp hp'
  have hp2 : Tendsto (fun n => ((p (phi n)).2 : Matrix I I ℂ)) atTop
      (𝓝 (q.2 : Matrix I I ℂ)) :=
    (continuous_subtype_val.comp continuous_snd).tendsto q |>.comp hp'
  have hz0 : W.PosSemidef := by
    exact Matrix.posSemidef_is_closed.mem_of_tendsto hW
      (Eventually.of_forall (fun n => hZ0 (phi n)))
  have hz1 : (W - (q.1 : Matrix (I × O) (I × O) ℂ)).PosSemidef := by
    exact Matrix.posSemidef_is_closed.mem_of_tendsto (hW.sub hp1)
      (Eventually.of_forall (fun n => hZ1 (phi n)))
  have hz2 : ((q.2 : Matrix I I ℂ) - ChannelUniformApproximation.traceOutput W).PosSemidef := by
    exact Matrix.posSemidef_is_closed.mem_of_tendsto
      (hp2.sub (ChannelUniformApproximation.traceOutput_continuous.tendsto W |>.comp hW))
      (Eventually.of_forall (fun n => hZ2 (phi n)))
  exact ⟨W, hz0, hz1, hz2⟩

def certificateCone : ProperCone ℝ (ConeSpace I O) where
  carrier := certificateConeSet
  zero_mem' := by
    refine ⟨0, Matrix.PosSemidef.zero, ?_, ?_⟩
    · change ((0 : Matrix (I × O) (I × O) ℂ) - 0).PosSemidef
      simpa only [sub_zero] using (Matrix.PosSemidef.zero (n := I × O) (R := ℂ))
    · change ((0 : Matrix I I ℂ) - ChannelUniformApproximation.traceOutput
        (0 : Matrix (I × O) (I × O) ℂ)).PosSemidef
      have h0 := (ChannelUniformApproximation.traceOutputLinear (I := I) (O := O)).map_zero
      change ChannelUniformApproximation.traceOutput (0 : Matrix (I × O) (I × O) ℂ) = 0 at h0
      simpa only [h0, sub_zero] using (Matrix.PosSemidef.zero (n := I) (R := ℂ))
  add_mem' := by
    rintro p q ⟨Z, hZ0, hZ1, hZ2⟩ ⟨W, hW0, hW1, hW2⟩
    refine ⟨Z + W, hZ0.add hW0, ?_, ?_⟩
    · convert hZ1.add hW1 using 1 <;> simp only [Prod.fst_add, Submodule.coe_add] <;> abel
    · have hlin := (ChannelUniformApproximation.traceOutputLinear (I := I) (O := O)).map_add Z W
      change ChannelUniformApproximation.traceOutput (Z + W) =
        ChannelUniformApproximation.traceOutput Z + ChannelUniformApproximation.traceOutput W at hlin
      simpa only [Prod.snd_add, Submodule.coe_add, hlin, add_sub_add_comm] using hZ2.add hW2
  smul_mem' := by
    rintro c p ⟨Z, hZ0, hZ1, hZ2⟩
    refine ⟨(c : ℝ) • Z, hZ0.smul c.property, ?_, ?_⟩
    · change (((c : ℝ) • Z) - (c : ℝ) • (p.1 : Matrix (I × O) (I × O) ℂ)).PosSemidef
      simpa only [smul_sub] using
        hZ1.smul c.property
    · have hlin : ChannelUniformApproximation.traceOutput ((c : ℝ) • Z) =
          (c : ℝ) • ChannelUniformApproximation.traceOutput Z := by
        ext i j
        simp [ChannelUniformApproximation.traceOutput, Finset.smul_sum]
      change ((c : ℝ) • (p.2 : Matrix I I ℂ) -
        ChannelUniformApproximation.traceOutput ((c : ℝ) • Z)).PosSemidef
      simpa only [hlin, smul_sub] using
        hZ2.smul c.property
  isClosed' := certificateConeSet_closed

theorem exists_product_tracePair_representation (f : StrongDual ℝ (ConeSpace I O)) :
    ∃ D : Hermitian (I × O), ∃ R : Hermitian I,
      ∀ X Y, f (X, Y) = tracePair D X + tracePair R Y := by
  obtain ⟨D, hD⟩ := exists_tracePair_representation
    (f.toLinearMap.comp (LinearMap.inl ℝ (Hermitian (I × O)) (Hermitian I)))
  obtain ⟨R, hR⟩ := exists_tracePair_representation
    (f.toLinearMap.comp (LinearMap.inr ℝ (Hermitian (I × O)) (Hermitian I)))
  refine ⟨D, R, ?_⟩
  intro X Y
  have hd := hD X
  have hr := hR Y
  change tracePair D X = f (X, 0) at hd
  change tracePair R Y = f (0, Y) at hr
  rw [hd, hr]
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using (f.map_add (X, 0) (0, Y))

theorem certificateCone_mem_neg_first (X : Hermitian (I × O))
    (hX : (X : Matrix (I × O) (I × O) ℂ).PosSemidef) :
    (-X, 0) ∈ certificateCone (I := I) (O := O) := by
  refine ⟨0, Matrix.PosSemidef.zero, ?_, ?_⟩
  · change ((0 : Matrix (I × O) (I × O) ℂ) - -(X : Matrix (I × O) (I × O) ℂ)).PosSemidef
    simpa only [zero_sub, neg_neg] using hX
  · change ((0 : Matrix I I ℂ) - ChannelUniformApproximation.traceOutput
      (0 : Matrix (I × O) (I × O) ℂ)).PosSemidef
    have h0 := (ChannelUniformApproximation.traceOutputLinear (I := I) (O := O)).map_zero
    change ChannelUniformApproximation.traceOutput (0 : Matrix (I × O) (I × O) ℂ) = 0 at h0
    simpa only [h0, sub_zero] using (Matrix.PosSemidef.zero (n := I) (R := ℂ))

theorem certificateCone_mem_pos_second (R : Hermitian I)
    (hR : (R : Matrix I I ℂ).PosSemidef) :
    (0, R) ∈ certificateCone (I := I) (O := O) := by
  refine ⟨0, Matrix.PosSemidef.zero, ?_, ?_⟩
  · change ((0 : Matrix (I × O) (I × O) ℂ) - 0).PosSemidef
    simpa only [sub_zero] using (Matrix.PosSemidef.zero (n := I × O) (R := ℂ))
  · change ((R : Matrix I I ℂ) - ChannelUniformApproximation.traceOutput
      (0 : Matrix (I × O) (I × O) ℂ)).PosSemidef
    have h0 := (ChannelUniformApproximation.traceOutputLinear (I := I) (O := O)).map_zero
    change ChannelUniformApproximation.traceOutput (0 : Matrix (I × O) (I × O) ℂ) = 0 at h0
    simpa only [h0, sub_zero] using hR

theorem certificateCone_mem_marginal (Z : Matrix (I × O) (I × O) ℂ)
    (hZ : Z.PosSemidef) :
    ((⟨Z, hZ.isHermitian⟩ : Hermitian (I × O)),
      (⟨ChannelUniformApproximation.traceOutput Z,
        (ChannelUniformApproximation.traceOutput_posSemidef hZ).isHermitian⟩ : Hermitian I)) ∈
      certificateCone (I := I) (O := O) := by
  refine ⟨Z, hZ, ?_, ?_⟩
  · change (Z - Z).PosSemidef
    simpa only [sub_self] using (Matrix.PosSemidef.zero (n := I × O) (R := ℂ))
  · change (ChannelUniformApproximation.traceOutput Z - ChannelUniformApproximation.traceOutput Z).PosSemidef
    simpa only [sub_self] using (Matrix.PosSemidef.zero (n := I) (R := ℂ))

theorem separator_matrices
    (f : StrongDual ℝ (ConeSpace I O))
    (hf : ∀ p ∈ certificateCone (I := I) (O := O), 0 ≤ f p) :
    ∃ U : Matrix (I × O) (I × O) ℂ, ∃ R : Matrix I I ℂ,
      U.PosSemidef ∧ R.PosSemidef ∧ (R ⊗ₖ (1 : Matrix O O ℂ) - U).PosSemidef ∧
        ∀ X Y, f (X, Y) = -((U * (X : Matrix (I × O) (I × O) ℂ)).trace.re) +
          (R * (Y : Matrix I I ℂ)).trace.re := by
  obtain ⟨D, R, hrep⟩ := exists_product_tracePair_representation f
  let U : Matrix (I × O) (I × O) ℂ := -(D : Matrix (I × O) (I × O) ℂ)
  have hU : U.PosSemidef := by
    apply posSemidef_of_tracePair_nonneg (hermitian_val D).neg
    intro W hW
    have hh := hf (-((⟨W, hW.isHermitian⟩ : Hermitian (I × O))), 0)
      (certificateCone_mem_neg_first _ hW)
    rw [hrep] at hh
    change 0 ≤ ((D : Matrix (I × O) (I × O) ℂ) * -W).trace.re +
      ((R : Matrix I I ℂ) * 0).trace.re at hh
    simpa only [U, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re,
      Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, add_zero] using hh
  have hR : (R : Matrix I I ℂ).PosSemidef := by
    apply posSemidef_of_tracePair_nonneg (hermitian_val R)
    intro W hW
    have hh := hf (0, (⟨W, hW.isHermitian⟩ : Hermitian I))
      (certificateCone_mem_pos_second _ hW)
    rw [hrep] at hh
    change 0 ≤ ((D : Matrix (I × O) (I × O) ℂ) * 0).trace.re +
      ((R : Matrix I I ℂ) * W).trace.re at hh
    simpa only [Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, zero_add] using hh
  have hcap : ((R : Matrix I I ℂ) ⊗ₖ (1 : Matrix O O ℂ) - U).PosSemidef := by
    apply posSemidef_of_tracePair_nonneg
      ((hR.kronecker Matrix.PosSemidef.one).isHermitian.sub hU.isHermitian)
    intro W hW
    have hh := hf _ (certificateCone_mem_marginal W hW)
    rw [hrep] at hh
    change 0 ≤ ((D : Matrix (I × O) (I × O) ℂ) * W).trace.re +
      ((R : Matrix I I ℂ) * ChannelUniformApproximation.traceOutput W).trace.re at hh
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re,
      Matrix.trace_mul_comm ((R : Matrix I I ℂ) ⊗ₖ (1 : Matrix O O ℂ)) W,
      traceOutput_pairing, Matrix.trace_mul_comm (ChannelUniformApproximation.traceOutput W)]
    simpa only [U, Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re, sub_neg_eq_add,
      add_comm] using hh
  refine ⟨U, R, hU, hR, hcap, ?_⟩
  intro X Y
  rw [hrep]
  change ((D : Matrix (I × O) (I × O) ℂ) * (X : Matrix (I × O) (I × O) ℂ)).trace.re +
    ((R : Matrix I I ℂ) * (Y : Matrix I I ℂ)).trace.re = _
  simp only [U, Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re, neg_neg]

theorem exists_certificate_of_primal_bound (H : Hermitian (I × O)) (lambda : ℝ)
    (hbound : ∀ rho T, PrimalFeasible rho T →
      ((H : Matrix (I × O) (I × O) ℂ) * T).trace.re ≤ lambda) :
    (H, (⟨lambda • (1 : Matrix I I ℂ), Matrix.isHermitian_one.smul (IsSelfAdjoint.all lambda)⟩ : Hermitian I)) ∈
      certificateCone (I := I) (O := O) := by
  by_contra hnot
  obtain ⟨f, hf, hneg⟩ := (certificateCone (I := I) (O := O)).hyperplane_separation_point hnot
  obtain ⟨U, R, hU, hR, hcap, hrep⟩ := separator_matrices f hf
  rw [hrep] at hneg
  change -(U * (H : Matrix (I × O) (I × O) ℂ)).trace.re +
    (R * (lambda • (1 : Matrix I I ℂ))).trace.re < 0 at hneg
  rw [Matrix.trace_mul_comm U, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul] at hneg
  have hc : 0 < R.trace.re := by
    have hc0 := (Complex.nonneg_iff.mp hR.trace_nonneg).1
    by_contra hn
    have hz : R.trace.re = 0 := le_antisymm (le_of_not_gt hn) hc0
    have hR0 := (DiamondControl.posSemidef_trace_re_eq_zero_iff hR).mp hz
    have hnegU : (-U).PosSemidef := by simpa only [hR0, Matrix.zero_kronecker, zero_sub] using hcap
    have hU0 : U = 0 := le_antisymm (neg_nonneg.mp hnegU.nonneg) hU.nonneg
    simp only [hU0, hR0, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re,
      neg_zero, mul_zero, add_zero, lt_self_iff_false] at hneg
  have hP : PrimalFeasible (R.trace.re⁻¹ • R) (R.trace.re⁻¹ • U) := by
    refine ⟨⟨hR.smul (inv_pos.mpr hc).le, ?_⟩, hU.smul (inv_pos.mpr hc).le, ?_⟩
    · apply Complex.ext
      · simp only [Matrix.trace_smul, Complex.smul_re, smul_eq_mul, Complex.one_re]
        exact inv_mul_cancel₀ hc.ne'
      · simp only [Matrix.trace_smul, Complex.smul_im, smul_eq_mul, Complex.one_im,
          (Complex.nonneg_iff.mp hR.trace_nonneg).2.symm, mul_zero]
    · simpa only [Matrix.smul_kronecker, smul_sub] using hcap.smul (inv_pos.mpr hc).le
  have hb := hbound _ _ hP
  rw [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at hb
  have hm := mul_le_mul_of_nonneg_left hb hc.le
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at hm
  linarith

theorem exists_dual_of_primal_bound (H : Matrix (I × O) (I × O) ℂ)
    (hH : H.IsHermitian) {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (hbound : ∀ rho T, PrimalFeasible rho T → (H * T).trace.re ≤ lambda) :
    ∃ Z : Matrix (I × O) (I × O) ℂ, DualFeasible H Z ∧
      ChannelUniformApproximation.globalDualObjective Z ≤ lambda := by
  obtain ⟨Z, hZ, hdom, hmarg⟩ := exists_certificate_of_primal_bound ⟨H, hH⟩ lambda hbound
  refine ⟨Z, ⟨hZ, hdom⟩, ?_⟩
  apply (CStarAlgebra.norm_le_iff_le_algebraMap
    (ChannelUniformApproximation.traceOutput Z) hlambda
    (ChannelUniformApproximation.traceOutput_posSemidef hZ).nonneg).mpr
  rw [Algebra.algebraMap_eq_smul_one]
  exact Matrix.le_iff.mpr hmarg

theorem primalValue_eq_choiTestingValue (H : Matrix (I × O) (I × O) ℂ) :
    primalValue H = ChannelTestingPhysical.choiTestingValue H := rfl

theorem primalValue_nonneg [Nonempty I] (H : Matrix (I × O) (I × O) ℂ) :
    0 ≤ primalValue H := by
  let rho : Matrix I I ℂ := (Fintype.card I : ℝ)⁻¹ • 1
  have hc : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  have hR : FlaggedStates.IsDensity rho := by
    refine ⟨Matrix.PosSemidef.one.smul (inv_pos.mpr hc).le, ?_⟩
    apply Complex.ext
    · simp only [rho, Matrix.trace_smul, Matrix.trace_one, Complex.smul_re,
        Complex.natCast_re, Complex.one_re, smul_eq_mul]
      exact inv_mul_cancel₀ hc.ne'
    · simp only [rho, Matrix.trace_smul, Matrix.trace_one, Complex.smul_im,
        Complex.natCast_im, Complex.one_im, smul_eq_mul, mul_zero]
  have hP : PrimalFeasible rho 0 :=
    ⟨hR, Matrix.PosSemidef.zero, by
      simpa only [sub_zero] using hR.1.kronecker
        (Matrix.PosSemidef.one : (1 : Matrix O O ℂ).PosSemidef)⟩
  have h : (((H * 0).trace.re : ℝ) : EReal) ≤ primalValue H :=
    le_iSup_of_le rho (le_iSup_of_le (0 : Matrix (I × O) (I × O) ℂ)
    (le_iSup_of_le hP le_rfl))
  simpa only [Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, EReal.coe_zero]
    using h

theorem exists_dualFeasible (H : Matrix (I × O) (I × O) ℂ) (hH : H.IsHermitian) :
    ∃ Z, DualFeasible H Z := by
  refine ⟨‖H‖ • (1 : Matrix (I × O) (I × O) ℂ),
    Matrix.PosSemidef.one.smul (norm_nonneg H), ?_⟩
  have h := hH.isSelfAdjoint.le_algebraMap_norm_self
  change (algebraMap ℝ (Matrix (I × O) (I × O) ℂ) ‖H‖ - H).PosSemidef at h
  simpa only [Algebra.algebraMap_eq_smul_one] using h

theorem primalValue_ne_top (H : Matrix (I × O) (I × O) ℂ) (hH : H.IsHermitian) :
    primalValue H ≠ ⊤ := by
  obtain ⟨Z, hZ⟩ := exists_dualFeasible H hH
  exact ne_of_lt ((primalValue_le_dual_objective hZ).trans_lt
    (EReal.coe_lt_top (ChannelUniformApproximation.globalDualObjective Z)))

theorem primalValue_ne_bot [Nonempty I] (H : Matrix (I × O) (I × O) ℂ) :
    primalValue H ≠ ⊥ := by
  exact ne_of_gt ((EReal.bot_lt_coe 0).trans_le (primalValue_nonneg H))

theorem exists_dual_attaining_primalValue [Nonempty I]
    (H : Matrix (I × O) (I × O) ℂ) (hH : H.IsHermitian) :
    ∃ Z : Matrix (I × O) (I × O) ℂ, DualFeasible H Z ∧
      (ChannelUniformApproximation.globalDualObjective Z : EReal) = primalValue H := by
  have heq := EReal.coe_toReal (primalValue_ne_top H hH) (primalValue_ne_bot H)
  obtain ⟨Z, hZ, hsmall⟩ := exists_dual_of_primal_bound H hH
    (EReal.toReal_nonneg (primalValue_nonneg H)) (by
      intro rho T hP
      apply EReal.coe_le_coe_iff.mp
      rw [heq]
      exact le_iSup_of_le rho (le_iSup_of_le T (le_iSup_of_le hP le_rfl)))
  refine ⟨Z, hZ, le_antisymm ?_ (primalValue_le_dual_objective hZ)⟩
  rw [← heq]
  exact EReal.coe_le_coe_iff.mpr hsmall

def dualValue (H : Matrix (I × O) (I × O) ℂ) : EReal :=
  ⨅ (Z : Matrix (I × O) (I × O) ℂ) (_h : DualFeasible H Z),
    (ChannelUniformApproximation.globalDualObjective Z : EReal)

theorem primalValue_eq_dualValue [Nonempty I]
    (H : Matrix (I × O) (I × O) ℂ) (hH : H.IsHermitian) :
    primalValue H = dualValue H := by
  apply le_antisymm
  · exact le_iInf fun Z => le_iInf fun hZ => primalValue_le_dual_objective hZ
  · obtain ⟨Z, hZ, hval⟩ := exists_dual_attaining_primalValue H hH
    have hle : dualValue H ≤ (ChannelUniformApproximation.globalDualObjective Z : EReal) := by
      exact iInf_le_of_le Z (iInf_le_of_le hZ le_rfl)
    exact hle.trans hval.le

theorem exists_channelPower_global_dual_dyadic_bound
    (Phi Psi : KrausCompletion.FiniteCPTP I O) [Nonempty I]
    {n : ℕ} (hn : 0 < n) {r B : ℝ} (hr : 0 < r)
    (hReg : ChannelRegularization.regularizedRelativeEntropyBits Phi Psi ≤ (B : EReal)) :
    ∃ Z : Matrix (TensorEntropy.TensorIndex I n × TensorEntropy.TensorIndex O n)
        (TensorEntropy.TensorIndex I n × TensorEntropy.TensorIndex O n) ℂ,
      Z.PosSemidef ∧
      (((2 : ℝ) ^ ((n : ℝ) * r)) • CPTPKraus.choi (ChannelRegularization.channelPower Psi n).map + Z -
        CPTPKraus.choi (ChannelRegularization.channelPower Phi n).map).PosSemidef ∧
      ‖ChannelUniformApproximation.traceOutput Z‖ ≤
        min 1 (((n : ℝ) * B + 1) / ((n : ℝ) * r)) := by
  let H := CPTPKraus.choi (ChannelRegularization.channelPower Phi n).map -
    ((2 : ℝ) ^ ((n : ℝ) * r)) • CPTPKraus.choi (ChannelRegularization.channelPower Psi n).map
  have hPhi := (CPTPKraus.choi_posSemidef_iff_completelyPositive _).mpr
    (ChannelRegularization.channelPower Phi n).completelyPositive
  have hPsi := (CPTPKraus.choi_posSemidef_iff_completelyPositive _).mpr
    (ChannelRegularization.channelPower Psi n).completelyPositive
  have hH : H.IsHermitian :=
    hPhi.isHermitian.sub (hPsi.isHermitian.smul (IsSelfAdjoint.all _))
  have hB : 0 ≤ B := EReal.coe_nonneg.mp
    ((ChannelRegularization.regularizedRelativeEntropyBits_nonneg Phi Psi).trans hReg)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnonneg : 0 ≤ min 1 (((n : ℝ) * B + 1) / ((n : ℝ) * r)) := by positivity
  have hbound := ChannelTestingPhysical.channelPower_choiTestingValue_dyadic_le Phi Psi hn hr hReg
  obtain ⟨Z, hZ, hsmall⟩ := exists_dual_of_primal_bound H hH hnonneg (by
    intro rho T hP
    apply EReal.coe_le_coe_iff.mp
    have htest : ((H * T).trace.re : EReal) ≤ primalValue H :=
      le_iSup_of_le rho (le_iSup_of_le T (le_iSup_of_le hP le_rfl))
    exact htest.trans (by simpa only [primalValue_eq_choiTestingValue, H] using hbound))
  refine ⟨Z, hZ.1, ?_, hsmall⟩
  convert hZ.2 using 1
  dsimp only [H]
  abel

theorem eventually_exists_channelPower_global_dual
    (Phi Psi : KrausCompletion.FiniteCPTP I O) [Nonempty I]
    {B r delta : ℝ} (hr : 0 < r)
    (hReg : ChannelRegularization.regularizedRelativeEntropyBits Phi Psi ≤ (B : EReal))
    (hgap : B < r * delta ^ 2) :
    ∀ᶠ n : ℕ in atTop,
      ∃ Z : Matrix (TensorEntropy.TensorIndex I n × TensorEntropy.TensorIndex O n)
          (TensorEntropy.TensorIndex I n × TensorEntropy.TensorIndex O n) ℂ,
        Z.PosSemidef ∧
        (((2 : ℝ) ^ ((n : ℝ) * r)) • CPTPKraus.choi (ChannelRegularization.channelPower Psi n).map + Z -
          CPTPKraus.choi (ChannelRegularization.channelPower Phi n).map).PosSemidef ∧
        ‖ChannelUniformApproximation.traceOutput Z‖ ≤ delta ^ 2 := by
  have hd : 0 < r * delta ^ 2 - B := sub_pos.mpr hgap
  have hlarge : ∀ᶠ n : ℕ in atTop, (r * delta ^ 2 - B)⁻¹ < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  filter_upwards [hlarge, eventually_gt_atTop 0] with n hlarge hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmul : 1 < (n : ℝ) * (r * delta ^ 2 - B) := by
    have h := mul_lt_mul_of_pos_right hlarge hd
    simpa only [inv_mul_cancel₀ hd.ne'] using h
  have hsmall : ((n : ℝ) * B + 1) / ((n : ℝ) * r) ≤ delta ^ 2 := by
    apply (div_le_iff₀ (mul_pos hnR hr)).mpr
    nlinarith
  obtain ⟨Z, hZ, hdom, hobj⟩ := exists_channelPower_global_dual_dyadic_bound Phi Psi hn hr hReg
  exact ⟨Z, hZ, hdom, hobj.trans ((min_le_right _ _).trans hsmall)⟩

variable {E F : Type*} [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]

theorem exists_channelPower_dyadic_kraus_approximation
    (Phi Psi : KrausCompletion.FiniteCPTP I O) [Nonempty I]
    {n : ℕ} (hn : 0 < n) {r budget : ℝ} (hr : 0 < r)
    (hReg : ChannelRegularization.regularizedRelativeEntropyBits Phi Psi ≤ (budget : EReal))
    (K : E → Matrix (TensorEntropy.TensorIndex O n) (TensorEntropy.TensorIndex I n) ℂ)
    (L : F → Matrix (TensorEntropy.TensorIndex O n) (TensorEntropy.TensorIndex I n) ℂ)
    (hK : QuantumProver.ElegantJointMeasurement.CP.krausMap K = (ChannelRegularization.channelPower Phi n).map)
    (hL : QuantumProver.ElegantJointMeasurement.CP.krausMap L = (ChannelRegularization.channelPower Psi n).map) :
    ∃ C : Matrix E F ℂ,
      ‖C‖ ≤ (2 : ℝ) ^ ((n : ℝ) * r / 2) ∧
      CPTPKraus.CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.krausMap (ChannelUniformApproximation.mixEnvironment C L)) ∧
      CPTPKraus.CPDom (QuantumProver.ElegantJointMeasurement.CP.krausMap (ChannelUniformApproximation.mixEnvironment C L))
        (ChannelRegularization.channelPower Psi n).map ((2 : ℝ) ^ ((n : ℝ) * r)) ∧
      ‖ChannelUniformApproximation.stackKraus K -
        ChannelUniformApproximation.stackKraus (ChannelUniformApproximation.mixEnvironment C L)‖ ^ 2 ≤
          min 1 (((n : ℝ) * budget + 1) / ((n : ℝ) * r)) := by
  obtain ⟨Z, hZ, hdom, hsmall⟩ :=
    exists_channelPower_global_dual_dyadic_bound Phi Psi hn hr hReg
  rw [← hK, ← hL] at hdom
  obtain ⟨C, hC, hcp, hcpdom, _, hres⟩ :=
    ChannelUniformApproximation.exists_global_dominated_kraus_approximation K L hZ
      ((2 : ℝ) ^ ((n : ℝ) * r)) (Real.rpow_pos_of_pos (by norm_num) _).le hdom
  have hhalf : 0 ≤ (2 : ℝ) ^ ((n : ℝ) * r / 2) := Real.rpow_nonneg (by norm_num) _
  have hC' : ‖C‖ ≤ (2 : ℝ) ^ ((n : ℝ) * r / 2) := by
    rw [← ChannelUniformApproximation.dyadic_half_sq ((n : ℝ) * r)] at hC
    nlinarith [norm_nonneg C]
  rw [ChannelUniformApproximation.global_dual_marginal_norm_transpose hZ] at hres
  exact ⟨C, hC', hcp, by simpa only [hL] using hcpdom, hres.trans hsmall⟩

theorem exists_channelPower_weak_kraus_approximation
    (Phi Psi : KrausCompletion.FiniteCPTP I O) [Nonempty I]
    {n : ℕ} (hn : 0 < n) {r budget delta : ℝ} (hr : 0 < r) (hdelta : 0 ≤ delta)
    (hReg : ChannelRegularization.regularizedRelativeEntropyBits Phi Psi ≤ (budget : EReal))
    (hsmall : ((n : ℝ) * budget + 1) / ((n : ℝ) * r) ≤ delta ^ 2)
    (K : E → Matrix (TensorEntropy.TensorIndex O n) (TensorEntropy.TensorIndex I n) ℂ)
    (L : F → Matrix (TensorEntropy.TensorIndex O n) (TensorEntropy.TensorIndex I n) ℂ)
    (hK : QuantumProver.ElegantJointMeasurement.CP.krausMap K = (ChannelRegularization.channelPower Phi n).map)
    (hL : QuantumProver.ElegantJointMeasurement.CP.krausMap L = (ChannelRegularization.channelPower Psi n).map) :
    ∃ C : Matrix E F ℂ,
      ‖C‖ ≤ (2 : ℝ) ^ ((n : ℝ) * r / 2) ∧
      CPTPKraus.CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.krausMap (ChannelUniformApproximation.mixEnvironment C L)) ∧
      CPTPKraus.CPDom (QuantumProver.ElegantJointMeasurement.CP.krausMap (ChannelUniformApproximation.mixEnvironment C L))
        (ChannelRegularization.channelPower Psi n).map ((2 : ℝ) ^ ((n : ℝ) * r)) ∧
      ‖ChannelUniformApproximation.stackKraus K -
        ChannelUniformApproximation.stackKraus (ChannelUniformApproximation.mixEnvironment C L)‖ ≤ delta := by
  obtain ⟨C, hC, hcp, hdom, hres⟩ :=
    exists_channelPower_dyadic_kraus_approximation Phi Psi hn hr hReg K L hK hL
  refine ⟨C, hC, hcp, hdom, ?_⟩
  have h := hres.trans ((min_le_right _ _).trans hsmall)
  nlinarith [norm_nonneg (ChannelUniformApproximation.stackKraus K -
    ChannelUniformApproximation.stackKraus (ChannelUniformApproximation.mixEnvironment C L))]

theorem exists_channelPower_global_weak_kraus_family
    (Phi Psi : KrausCompletion.FiniteCPTP I O) [Nonempty I]
    {budget r delta : ℝ} (hr : 0 < r) (hdelta : 0 ≤ delta)
    (hReg : ChannelRegularization.regularizedRelativeEntropyBits Phi Psi ≤ (budget : EReal))
    (hgap : budget < r * delta ^ 2)
    (EnvK EnvL : ℕ → Type*) [∀ n, Fintype (EnvK n)] [∀ n, Fintype (EnvL n)]
    [∀ n, DecidableEq (EnvK n)] [∀ n, DecidableEq (EnvL n)]
    (K : (n : ℕ) → EnvK n →
      Matrix (TensorEntropy.TensorIndex O n) (TensorEntropy.TensorIndex I n) ℂ)
    (L : (n : ℕ) → EnvL n →
      Matrix (TensorEntropy.TensorIndex O n) (TensorEntropy.TensorIndex I n) ℂ)
    (hK : ∀ n, QuantumProver.ElegantJointMeasurement.CP.krausMap (K n) = (ChannelRegularization.channelPower Phi n).map)
    (hL : ∀ n, QuantumProver.ElegantJointMeasurement.CP.krausMap (L n) = (ChannelRegularization.channelPower Psi n).map) :
    ∃ C : (n : ℕ) → Matrix (EnvK n) (EnvL n) ℂ,
      ∀ᶠ n : ℕ in atTop,
        ‖C n‖ ≤ (2 : ℝ) ^ ((n : ℝ) * r / 2) ∧
        CPTPKraus.CompletelyPositive
          (QuantumProver.ElegantJointMeasurement.CP.krausMap (ChannelUniformApproximation.mixEnvironment (C n) (L n))) ∧
        CPTPKraus.CPDom
          (QuantumProver.ElegantJointMeasurement.CP.krausMap (ChannelUniformApproximation.mixEnvironment (C n) (L n)))
          (ChannelRegularization.channelPower Psi n).map ((2 : ℝ) ^ ((n : ℝ) * r)) ∧
        ‖ChannelUniformApproximation.stackKraus (K n) -
          ChannelUniformApproximation.stackKraus
            (ChannelUniformApproximation.mixEnvironment (C n) (L n))‖ ≤ delta := by
  have hex (n : ℕ) : ∃ C : Matrix (EnvK n) (EnvL n) ℂ,
      (0 < n ∧ ((n : ℝ) * budget + 1) / ((n : ℝ) * r) ≤ delta ^ 2) →
      ‖C‖ ≤ (2 : ℝ) ^ ((n : ℝ) * r / 2) ∧
      CPTPKraus.CompletelyPositive
        (QuantumProver.ElegantJointMeasurement.CP.krausMap (ChannelUniformApproximation.mixEnvironment C (L n))) ∧
      CPTPKraus.CPDom
        (QuantumProver.ElegantJointMeasurement.CP.krausMap (ChannelUniformApproximation.mixEnvironment C (L n)))
        (ChannelRegularization.channelPower Psi n).map ((2 : ℝ) ^ ((n : ℝ) * r)) ∧
      ‖ChannelUniformApproximation.stackKraus (K n) -
        ChannelUniformApproximation.stackKraus
          (ChannelUniformApproximation.mixEnvironment C (L n))‖ ≤ delta := by
    by_cases h : 0 < n ∧ ((n : ℝ) * budget + 1) / ((n : ℝ) * r) ≤ delta ^ 2
    · obtain ⟨C, hC⟩ := exists_channelPower_weak_kraus_approximation
        Phi Psi h.1 hr hdelta hReg h.2 (K n) (L n) (hK n) (hL n)
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h' => False.elim (h h')⟩
  choose C hC using hex
  refine ⟨C, ?_⟩
  have hd : 0 < r * delta ^ 2 - budget := sub_pos.mpr hgap
  have hlarge : ∀ᶠ n : ℕ in atTop, (r * delta ^ 2 - budget)⁻¹ < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  filter_upwards [hlarge, eventually_gt_atTop 0] with n hlarge hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmul : 1 < (n : ℝ) * (r * delta ^ 2 - budget) := by
    have h := mul_lt_mul_of_pos_right hlarge hd
    simpa only [inv_mul_cancel₀ hd.ne'] using h
  apply hC n
  refine ⟨hn, (div_le_iff₀ (mul_pos hnR hr)).mpr ?_⟩
  nlinarith

end QuantumProver.SuperchannelDiscrimination.ChannelTestingDual
