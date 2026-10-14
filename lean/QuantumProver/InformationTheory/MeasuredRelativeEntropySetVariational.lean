import QuantumProver.InformationTheory.MeasuredRelativeEntropyVariational
import QuantumProver.InformationTheory.MeasuredRenyiVariational
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import QuantumProver.InformationTheory.Equipartition.MeasuredRenyiTensorization
import QuantumProver.InformationTheory.Equipartition.MeasuredRenyiSuperadditivity

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Kronecker Topology
open Filter
open QuantumProver.Equipartition.FiniteModel
open QuantumProver.Equipartition.FiniteModel.Testing
open QuantumProver.Equipartition.FiniteModel.PolarTensor

namespace QuantumProver.MeasuredRelativeEntropySetVariational

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def toSharedPOVM {L : ℕ} (M : FinitePOVM ι L) : QuantumProver.MeasuredRelativeEntropyVariational.POVM ι (Fin L) where
  effect := M.outcome
  positive := M.positive
  normalized := M.sum_outcome

def fromSharedPOVM {L : ℕ} (M : QuantumProver.MeasuredRelativeEntropyVariational.POVM ι (Fin L)) : FinitePOVM ι L where
  outcome := M.effect
  positive := M.positive
  sum_outcome := M.normalized

theorem classicalUmegaki_eq_shared {L : ℕ} (p q : Fin L → ℝ)
    (hp : ∀ i, 0 ≤ p i) :
    classicalUmegaki p q = QuantumProver.MeasuredRelativeEntropyVariational.classicalRelativeEntropyBits p q := by
  classical
  by_cases hs : classicalSupportLE p q
  · have hs' : ∀ i, p i ≠ 0 → q i ≠ 0 := by
      intro i hi hq
      exact hi (hs i hq)
    rw [classicalUmegaki, if_pos hs, QuantumProver.MeasuredRelativeEntropyVariational.classicalRelativeEntropyBits_finite_of_support p q hs']
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [logTwo]
    ring
  · obtain ⟨i, hqi, hpi⟩ : ∃ i, q i = 0 ∧ p i ≠ 0 := by
      have hh : ∃ i, ∃ (_ : q i = 0), p i ≠ 0 := by
        simpa only [classicalSupportLE, not_forall, not_imp] using hs
      obtain ⟨i, hqi, hpi⟩ := hh
      exact ⟨i, hqi, hpi⟩
    have hpos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hpi)
    rw [classicalUmegaki, if_neg hs,
      QuantumProver.MeasuredRelativeEntropyVariational.classicalRelativeEntropyBits_eq_top_of_zero_reference_event p q i hpos hqi]

theorem measuredDivergence_one_eq_shared {ρ σ : CMat ι} (hρ : IsState ρ) :
    measuredDivergence ρ σ 1 = QuantumProver.MeasuredRelativeEntropyVariational.measuredRelativeEntropyBits ρ σ := by
  classical
  unfold measuredDivergence QuantumProver.MeasuredRelativeEntropyVariational.measuredRelativeEntropyBits
  congr 1
  ext z
  constructor
  · rintro ⟨L, M, rfl⟩
    have hL : 0 < L := by
      by_contra hn
      have hz : L = 0 := Nat.eq_zero_of_not_pos hn
      subst L
      have hh := measurementMass_sum M hρ
      simpa using hh
    refine ⟨L, hL, toSharedPOVM M, ?_⟩
    simp only [classicalRenyiDivergence, if_pos rfl]
    exact classicalUmegaki_eq_shared _ _ (measurementMass_nonneg M hρ.1)
  · rintro ⟨L, _, M, rfl⟩
    refine ⟨L, fromSharedPOVM M, ?_⟩
    simp only [classicalRenyiDivergence, if_pos rfl]
    exact (classicalUmegaki_eq_shared _ _
      (measurementMass_nonneg (fromSharedPOVM M) hρ.1)).symm

def orderOneObjective (X : CMat ι × CMat ι) (W : CMat ι) : ℝ :=
  (tracePair X.1 (matrixLog W) + 1 - tracePair X.2 W) / Real.log 2

def setMeasuredDivergenceOn (S T : Set (CMat ι)) (α : ℝ) : EReal :=
  sInf {z | ∃ ρ ∈ S, ∃ σ ∈ T, z = measuredDivergence ρ σ α}

theorem setMeasuredDivergenceOn_eq_iInf (S T : Set (CMat ι)) (α : ℝ) :
    setMeasuredDivergenceOn S T α =
      ⨅ X ∈ S ×ˢ T, measuredDivergence X.1 X.2 α := by
  apply le_antisymm
  · apply le_iInf₂
    rintro ⟨ρ, σ⟩ ⟨hρ, hσ⟩
    exact sInf_le ⟨ρ, hρ, σ, hσ, rfl⟩
  · apply le_sInf
    rintro z ⟨ρ, hρ, σ, hσ, rfl⟩
    exact iInf₂_le_of_le (ρ, σ) ⟨hρ, hσ⟩ le_rfl

theorem measuredDivergence_one_variational {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) :
    measuredDivergence ρ σ 1 =
      ⨆ W : CMat ι, ⨆ (_ : W.PosDef), (orderOneObjective (ρ, σ) W : EReal) := by
  rw [measuredDivergence_one_eq_shared hρ,
    QuantumProver.MeasuredRelativeEntropyVariational.measuredRelativeEntropyBits_variational ρ σ hρ hσ]
  apply le_antisymm
  · apply sSup_le
    rintro z ⟨W, hW, rfl⟩
    exact le_iSup₂_of_le W hW le_rfl
  · apply iSup₂_le
    intro W hW
    exact le_sSup ⟨W, hW, rfl⟩

theorem continuous_orderOneObjective_left (W : CMat ι) :
    Continuous (fun X => orderOneObjective X W) := by
  unfold orderOneObjective tracePair Matrix.trace
  fun_prop

theorem continuousOn_matrixLog :
    ContinuousOn (matrixLog : CMat ι → CMat ι) {W | W.PosDef} := by
  exact CFC.continuousOn_log.mono (fun W hW =>
    ⟨hW.isStrictlyPositive.isSelfAdjoint, hW.isStrictlyPositive.isUnit⟩)

theorem continuousOn_orderOneObjective_right (X : CMat ι × CMat ι) :
    ContinuousOn (orderOneObjective X) {W | W.PosDef} := by
  have hc : Continuous (fun V : CMat ι => tracePair X.1 V) := by
    unfold tracePair Matrix.trace
    fun_prop
  have hd : Continuous (fun W : CMat ι => tracePair X.2 W) := by
    unfold tracePair Matrix.trace
    fun_prop
  exact ((hc.continuousOn.comp continuousOn_matrixLog (fun _ _ => Set.mem_univ _)).add
    continuousOn_const |>.sub hd.continuousOn).div_const (Real.log 2)

theorem concaveOn_matrixLog :
    ConcaveOn ℝ {W : CMat ι | W.PosDef} matrixLog := by
  refine ⟨?_, ?_⟩
  · intro W hW V hV a b ha hb hab
    exact Matrix.isStrictlyPositive_iff_posDef.mp
      ((CFC.concaveOn_log (A := CMat ι)).1
        hW.isStrictlyPositive hV.isStrictlyPositive ha hb hab)
  · intro W hW V hV a b ha hb hab
    have hh := (CFC.concaveOn_log (A := CMat ι)).2
      hW.isStrictlyPositive hV.isStrictlyPositive ha hb hab
    simpa only [CFC.log, matrixLog] using hh

theorem orderOneObjective_affine (X Y : CMat ι × CMat ι)
    (a b : ℝ) (hab : a + b = 1) (W : CMat ι) :
    orderOneObjective (a • X + b • Y) W =
      a * orderOneObjective X W + b * orderOneObjective Y W := by
  simp only [orderOneObjective, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, tracePair, Matrix.add_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
  have hh : 1 = a + b := hab.symm
  conv_lhs => rw [hh]
  ring

theorem convexOn_orderOneObjective_left (S T : Set (CMat ι))
    (hSv : Convex ℝ S) (hTv : Convex ℝ T) (W : CMat ι) :
    ConvexOn ℝ (S ×ˢ T) (fun X => orderOneObjective X W) := by
  refine ⟨hSv.prod hTv, ?_⟩
  intro X _ Y _ a b _ _ hab
  exact (orderOneObjective_affine X Y a b hab W).le

theorem concaveOn_orderOneObjective_right {X : CMat ι × CMat ι}
    (hρ : X.1.PosSemidef) :
    ConcaveOn ℝ {W : CMat ι | W.PosDef} (orderOneObjective X) := by
  refine ⟨concaveOn_matrixLog.1, ?_⟩
  intro W hW V hV a b ha hb hab
  have hm := concaveOn_matrixLog.2 hW hV ha hb hab
  have ht := tracePair_mono_of_loewner hρ (Matrix.nonneg_iff_posSemidef.mp
    (sub_nonneg.mpr hm))
  have htrace : tracePair X.1 (a • matrixLog W + b • matrixLog V) =
      a * tracePair X.1 (matrixLog W) + b * tracePair X.1 (matrixLog V) := by
    simp [tracePair, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
      Matrix.trace_smul, Complex.smul_re]
  have href : tracePair X.2 (a • W + b • V) =
      a * tracePair X.2 W + b * tracePair X.2 V := by
    simp [tracePair, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
      Matrix.trace_smul, Complex.smul_re]
  rw [htrace] at ht
  change a * orderOneObjective X W + b * orderOneObjective X V ≤ _
  unfold orderOneObjective
  rw [href]
  have he : a * ((tracePair X.1 (matrixLog W) + 1 - tracePair X.2 W) / Real.log 2) +
      b * ((tracePair X.1 (matrixLog V) + 1 - tracePair X.2 V) / Real.log 2) =
      (a * tracePair X.1 (matrixLog W) + b * tracePair X.1 (matrixLog V) + 1 -
        (a * tracePair X.2 W + b * tracePair X.2 V)) / Real.log 2 := by
    have hh : 1 = a + b := hab.symm
    conv_rhs => rw [hh]
    ring
  rw [he]
  exact div_le_div_of_nonneg_right (by linarith) QuantumProver.MeasuredRelativeEntropyVariational.log_two_pos.le

theorem orderOneObjective_minimax (S T : Set (CMat ι))
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (hSv : Convex ℝ S) (hTv : Convex ℝ T)
    (hSp : ∀ ρ ∈ S, ρ.PosSemidef) :
    (⨅ X ∈ S ×ˢ T, ⨆ W : CMat ι, ⨆ (_ : W.PosDef),
      (orderOneObjective X W : EReal)) =
      ⨆ W : CMat ι, ⨆ (_ : W.PosDef), ⨅ X ∈ S ×ˢ T,
        (orderOneObjective X W : EReal) := by
  let f (X : CMat ι × CMat ι) (W : CMat ι) : EReal := orderOneObjective X W
  have hc := concaveOn_matrixLog (ι := ι)
  exact Sion.minimax' (X := S ×ˢ T) (Y := {W : CMat ι | W.PosDef}) (f := f)
    (hSn.prod hTn) (hSv.prod hTv) (hSc.prod hTc)
    (fun W _ => (continuous_coe_real_ereal.comp
      (continuous_orderOneObjective_left W)).continuousOn.lowerSemicontinuousOn)
    (fun W _ => by
      have hq := (convexOn_orderOneObjective_left S T hSv hTv W).quasiconvexOn
      have hqe := hq.monotone_comp EReal.orderEmbedding.monotone
      exact hqe)
    hc.1
    (fun X _ => (continuous_coe_real_ereal.continuousOn.comp
      (continuousOn_orderOneObjective_right X) (fun _ _ => Set.mem_univ _)).upperSemicontinuousOn)
    (fun X hX => by
      have hq := (concaveOn_orderOneObjective_right (hSp X.1 hX.1)).quasiconcaveOn
      have hqe := hq.monotone_comp EReal.orderEmbedding.monotone
      exact hqe)

def negativeLogSupport (S : Set (CMat ι)) (W : CMat ι) : ℝ :=
  -supportFunction S (-matrixLog W)

def supportObjective (S T : Set (CMat ι)) (W : CMat ι) : ℝ :=
  (negativeLogSupport S W + 1 - supportFunction T W) / Real.log 2

theorem iInf_orderOneObjective (S T : Set (CMat ι))
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (W : CMat ι) :
    (⨅ X ∈ S ×ˢ T, (orderOneObjective X W : EReal)) =
      (supportObjective S T W : EReal) := by
  have hneg (ρ : CMat ι) : tracePair ρ (-matrixLog W) = -tracePair ρ (matrixLog W) := by
    simp [tracePair, Matrix.mul_neg, Matrix.trace_neg]
  apply le_antisymm
  · obtain ⟨ρ, hρ, heρ⟩ := supportFunction_attained hSn hSc (-matrixLog W)
    obtain ⟨σ, hσ, heσ⟩ := supportFunction_attained hTn hTc W
    have he : orderOneObjective (ρ, σ) W = supportObjective S T W := by
      rw [hneg] at heρ
      dsimp [orderOneObjective, supportObjective, negativeLogSupport]
      rw [← heρ, ← heσ]
      simp
    rw [← he]
    exact iInf₂_le_of_le (ρ, σ) ⟨hρ, hσ⟩ le_rfl
  · apply le_iInf₂
    rintro ⟨ρ, σ⟩ ⟨hρ, hσ⟩
    have hs := tracePair_le_supportFunction hSc hρ (-matrixLog W)
    have ht := tracePair_le_supportFunction hTc hσ W
    rw [hneg] at hs
    apply EReal.coe_le_coe_iff.mpr
    apply div_le_div_of_nonneg_right _ QuantumProver.MeasuredRelativeEntropyVariational.log_two_pos.le
    dsimp [negativeLogSupport]
    linarith

theorem setMeasuredDivergenceOn_one_support (S T : Set (CMat ι))
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (hSv : Convex ℝ S) (hTv : Convex ℝ T)
    (hSs : ∀ ρ ∈ S, IsState ρ) (hTp : ∀ σ ∈ T, σ.PosSemidef) :
    setMeasuredDivergenceOn S T 1 =
      ⨆ W : CMat ι, ⨆ (_ : W.PosDef), (supportObjective S T W : EReal) := by
  rw [setMeasuredDivergenceOn_eq_iInf]
  have he : (⨅ X ∈ S ×ˢ T, measuredDivergence X.1 X.2 1) =
      ⨅ X ∈ S ×ˢ T, ⨆ W : CMat ι, ⨆ (_ : W.PosDef),
        (orderOneObjective X W : EReal) := by
    apply iInf_congr
    intro X
    apply iInf_congr
    intro hX
    exact measuredDivergence_one_variational (hSs X.1 hX.1) (hTp X.2 hX.2)
  rw [he, orderOneObjective_minimax S T hSn hTn hSc hTc hSv hTv
    (fun ρ hρ => (hSs ρ hρ).1)]
  simp_rw [iInf_orderOneObjective S T hSn hTn hSc hTc]

theorem posDef_smul_real {W : CMat ι} (hW : W.PosDef) {c : ℝ} (hc : 0 < c) :
    (c • W).PosDef := by
  exact Matrix.isStrictlyPositive_iff_posDef.mp (hW.isStrictlyPositive.smul hc)

theorem matrixLog_smul_real {W : CMat ι} (hW : W.PosDef) {c : ℝ} (hc : 0 < c) :
    matrixLog (c • W) = (Real.log c) • (1 : CMat ι) + matrixLog W := by
  simpa only [CFC.log, matrixLog, Algebra.algebraMap_eq_smul_one] using
    CFC.log_smul' W hc hW.isStrictlyPositive

theorem supportFunction_add_identity (S : Set (CMat ι))
    (hSn : S.Nonempty) (hSc : IsCompact S) (hSs : ∀ ρ ∈ S, IsState ρ)
    (V : CMat ι) (c : ℝ) :
    supportFunction S (V + c • (1 : CMat ι)) = supportFunction S V + c := by
  have ht (ρ : CMat ι) (hρ : ρ ∈ S) :
      tracePair ρ (V + c • (1 : CMat ι)) = tracePair ρ V + c := by
    simp only [tracePair, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    change tracePair ρ V + tracePair ρ (c • (1 : CMat ι)) = _
    rw [PolarTensor.tracePair_smul_right, tracePair_one_right, (hSs ρ hρ).trace_real, mul_one]
    rfl
  apply le_antisymm
  · apply supportFunction_le_of_bounds hSn
    intro ρ hρ
    rw [ht ρ hρ]
    linarith [tracePair_le_supportFunction hSc hρ V]
  · obtain ⟨ρ, hρ, heρ⟩ := supportFunction_attained hSn hSc V
    rw [← heρ, ← ht ρ hρ]
    exact tracePair_le_supportFunction hSc hρ _

theorem negativeLogSupport_smul (S : Set (CMat ι))
    (hSn : S.Nonempty) (hSc : IsCompact S) (hSs : ∀ ρ ∈ S, IsState ρ)
    {W : CMat ι} (hW : W.PosDef) {c : ℝ} (hc : 0 < c) :
    negativeLogSupport S (c • W) = negativeLogSupport S W + Real.log c := by
  rw [negativeLogSupport, matrixLog_smul_real hW hc]
  have he : -((Real.log c) • (1 : CMat ι) + matrixLog W) =
      -matrixLog W + (-Real.log c) • (1 : CMat ι) := by
    simp only [neg_add_rev, neg_smul]
  rw [he, supportFunction_add_identity S hSn hSc hSs]
  simp only [negativeLogSupport]
  ring

theorem setMeasuredDivergenceOn_one_polar (S T : Set (CMat ι))
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (hSv : Convex ℝ S) (hTv : Convex ℝ T)
    (hSs : ∀ ρ ∈ S, IsState ρ) (hTp : ∀ σ ∈ T, σ.PosSemidef) :
    setMeasuredDivergenceOn S T 1 =
      ⨆ W : CMat ι, ⨆ (_ : W.PosDef ∧ W ∈ positivePolar T),
        ((negativeLogSupport S W / Real.log 2 : ℝ) : EReal) := by
  rw [setMeasuredDivergenceOn_one_support S T hSn hTn hSc hTc hSv hTv hSs hTp]
  apply le_antisymm
  · apply iSup₂_le
    intro W hW
    have hq := supportFunction_nonneg hTn hTc hTp hW.posSemidef
    by_cases hqz : supportFunction T W = 0
    · let V := Real.exp 1 • W
      have hV : V.PosDef := posDef_smul_real hW (Real.exp_pos 1)
      have hVpolar : V ∈ positivePolar T := by
        apply (positivePolar_iff_supportFunction_le hTn hTc).2
        refine ⟨hV.posSemidef, ?_⟩
        rw [supportFunction_smul hTn hTc W (Real.exp_pos 1).le, hqz, mul_zero]
        norm_num
      have he : supportObjective S T W = negativeLogSupport S V / Real.log 2 := by
        rw [negativeLogSupport_smul S hSn hSc hSs hW (Real.exp_pos 1), Real.log_exp]
        simp only [supportObjective, hqz, sub_zero]
      rw [he]
      exact le_iSup₂_of_le V ⟨hV, hVpolar⟩ le_rfl
    · have hqp : 0 < supportFunction T W := lt_of_le_of_ne hq (Ne.symm hqz)
      let V := (supportFunction T W)⁻¹ • W
      have hV : V.PosDef := posDef_smul_real hW (inv_pos.mpr hqp)
      have hVpolar : V ∈ positivePolar T :=
        normalized_mem_positivePolar hTc hW.posSemidef hqp le_rfl
      have hbound : supportObjective S T W ≤ negativeLogSupport S V / Real.log 2 := by
        rw [negativeLogSupport_smul S hSn hSc hSs hW (inv_pos.mpr hqp), Real.log_inv]
        apply div_le_div_of_nonneg_right _ QuantumProver.MeasuredRelativeEntropyVariational.log_two_pos.le
        linarith [Real.log_le_sub_one_of_pos hqp]
      exact (EReal.coe_le_coe_iff.mpr hbound).trans
        (le_iSup₂_of_le V ⟨hV, hVpolar⟩ le_rfl)
  · apply iSup₂_le
    rintro W ⟨hW, hWp⟩
    have hp := ((positivePolar_iff_supportFunction_le hTn hTc).mp hWp).2
    apply le_iSup₂_of_le W hW
    apply EReal.coe_le_coe_iff.mpr
    apply div_le_div_of_nonneg_right _ QuantumProver.MeasuredRelativeEntropyVariational.log_two_pos.le
    linarith

theorem continuous_supportFunction {S : Set (CMat ι)} (hSc : IsCompact S) :
    Continuous (supportFunction S) := by
  change Continuous (fun W : CMat ι => sSup (supportValues S W))
  simp_rw [supportValues_eq_image]
  apply hSc.continuous_sSup
  change Continuous (fun X : CMat ι × CMat ι => tracePair X.2 X.1)
  unfold tracePair Matrix.trace
  fun_prop

theorem scalar_neg_rpow_slope_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun t : ℝ => t⁻¹ * (x ^ (-t) - 1)) (𝓝[>] 0) (𝓝 (-Real.log x)) := by
  have hd : HasDerivAt (fun t : ℝ => Real.exp (-t * Real.log x)) (-Real.log x) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).neg.mul_const (Real.log x)).exp using 1 <;> simp
  simpa only [zero_add, Real.exp_zero, neg_zero, zero_mul,
    Real.rpow_def_of_pos hx, mul_comm, smul_eq_mul] using hd.tendsto_slope_zero_right

theorem matrixRpow_neg_slope_tendsto {W : CMat ι} (hW : W.PosDef) :
    Tendsto (fun t : ℝ => t⁻¹ • (matrixRpow W (-t) - 1))
      (𝓝[>] 0) (𝓝 (-matrixLog W)) := by
  classical
  let P := spectralPinchingProjection hW.1
  have hEig (k : SpectralLabels hW.1) : 0 < (k : ℝ) := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp k.property
    rw [← hj]
    exact hW.eigenvalues_pos j
  have hsum : ∑ k, P k = 1 := sum_spectralPinchingProjection hW.1
  have hpow (t : ℝ) : matrixRpow W (-t) =
      ∑ k : SpectralLabels hW.1, (((k : ℝ) ^ (-t) : ℝ) : ℂ) • P k := by
    simpa only [matrixRpow, Real.rpow_eq_pow] using
      cfc_eq_sum_of_eigenmatrix_resolution hW.1 P (fun k => (k : ℝ))
        hsum (spectralPinchingProjection_mul_left hW.1) (fun x : ℝ => x ^ (-t))
  have hlog : matrixLog W = ∑ k : SpectralLabels hW.1, (Real.log (k : ℝ) : ℂ) • P k :=
    cfc_eq_sum_of_eigenmatrix_resolution hW.1 P (fun k => (k : ℝ))
      hsum (spectralPinchingProjection_mul_left hW.1) _
  have he (t : ℝ) : t⁻¹ • (matrixRpow W (-t) - 1) =
      ∑ k : SpectralLabels hW.1, ((t⁻¹ * ((k : ℝ) ^ (-t) - 1) : ℝ) : ℂ) • P k := by
    rw [hpow t, ← hsum, ← Finset.sum_sub_distrib, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  have ht (k : SpectralLabels hW.1) :
      Tendsto (fun t : ℝ => ((t⁻¹ * ((k : ℝ) ^ (-t) - 1) : ℝ) : ℂ) • P k)
        (𝓝[>] 0) (𝓝 (((-Real.log (k : ℝ) : ℝ) : ℂ) • P k)) :=
    ((Complex.continuous_ofReal.tendsto _).comp (scalar_neg_rpow_slope_tendsto (hEig k))).smul
      tendsto_const_nhds
  have hh := tendsto_finset_sum Finset.univ (fun k _ => ht k)
  simpa only [← he, hlog, Finset.sum_neg_distrib, Complex.ofReal_neg, neg_smul] using hh

def powerDifference (W : CMat ι) (t : ℝ) : CMat ι :=
  t⁻¹ • (matrixRpow W (-t) - 1)

def nearOneOrder (t : ℝ) : ℝ := (1 + t)⁻¹

def nearOneSupportValue (S T : Set (CMat ι)) (W : CMat ι) (t : ℝ) : ℝ :=
  nearOneOrder t * supportFunction S (matrixRpow W (-t)) +
    (1 - nearOneOrder t) * supportFunction T W

def nearOneSupportTest (S T : Set (CMat ι)) (W : CMat ι) (t : ℝ) : ℝ :=
  logTwo (nearOneSupportValue S T W t) / (nearOneOrder t - 1)

theorem nearOneOrder_bounds {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (1 / 2 : ℝ) ≤ nearOneOrder t ∧ nearOneOrder t < 1 := by
  constructor
  · dsimp [nearOneOrder]
    have hd : 0 < 1 + t := by linarith
    rw [← one_div]
    apply (one_div_le_one_div (by norm_num : (0 : ℝ) < 2) hd).2
    linarith
  · dsimp [nearOneOrder]
    exact inv_lt_one_of_one_lt₀ (by linarith)

theorem nearOneOrder_exponent {t : ℝ} (ht : 0 < t) :
    (nearOneOrder t - 1) / nearOneOrder t = -t := by
  unfold nearOneOrder
  field_simp [show 1 + t ≠ 0 by linarith]
  ring

theorem supportFunction_matrixRpow_neg (S : Set (CMat ι))
    (hSn : S.Nonempty) (hSc : IsCompact S) (hSs : ∀ ρ ∈ S, IsState ρ)
    (W : CMat ι) {t : ℝ} (ht : 0 < t) :
    supportFunction S (matrixRpow W (-t)) =
      1 + t * supportFunction S (powerDifference W t) := by
  have he : t • powerDifference W t + (1 : CMat ι) = matrixRpow W (-t) := by
    rw [powerDifference, smul_smul, mul_inv_cancel₀ ht.ne', one_smul, sub_add_cancel]
  have hs := supportFunction_add_identity S hSn hSc hSs (t • powerDifference W t) 1
  simp only [one_smul] at hs
  rw [← he, hs,
    supportFunction_smul hSn hSc (powerDifference W t) ht.le]
  ring

theorem nearOneSupportValue_eq (S T : Set (CMat ι))
    (hSn : S.Nonempty) (hSc : IsCompact S) (hSs : ∀ ρ ∈ S, IsState ρ)
    (W : CMat ι) {t : ℝ} (ht : 0 < t) :
    nearOneSupportValue S T W t = 1 + (t / (1 + t)) *
      (supportFunction S (powerDifference W t) + supportFunction T W - 1) := by
  rw [nearOneSupportValue, supportFunction_matrixRpow_neg S hSn hSc hSs W ht]
  unfold nearOneOrder
  field_simp [show 1 + t ≠ 0 by linarith]
  ring

theorem nearOneSupportTest_tendsto (S T : Set (CMat ι))
    (hSn : S.Nonempty) (hSc : IsCompact S) (hSs : ∀ ρ ∈ S, IsState ρ)
    {W : CMat ι} (hW : W.PosDef) :
    Tendsto (nearOneSupportTest S T W) (𝓝[>] 0) (𝓝 (supportObjective S T W)) := by
  let c (t : ℝ) := supportFunction S (powerDifference W t) + supportFunction T W - 1
  let c₀ := supportFunction S (-matrixLog W) + supportFunction T W - 1
  have hc : Tendsto c (𝓝[>] 0) (𝓝 c₀) :=
    ((continuous_supportFunction hSc).tendsto _ |>.comp
      (matrixRpow_neg_slope_tendsto hW)).add_const _ |>.sub_const 1
  have hδ : Tendsto (fun t : ℝ => t / (1 + t)) (𝓝[>] 0) (𝓝 0) := by
    have hh : ContinuousAt (fun t : ℝ => t / (1 + t)) 0 :=
      continuousAt_id.div (continuousAt_const.add continuousAt_id) (by norm_num)
    simpa using hh.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hK : Tendsto (nearOneSupportValue S T W) (𝓝[>] 0) (𝓝 1) := by
    have hh := (hδ.mul hc).const_add 1
    simp only [zero_mul, add_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (nearOneSupportValue_eq S T hSn hSc hSs W ht).symm
  have hd : HasDerivAt Real.log (1 : ℝ) 1 := by
    simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hds : Tendsto (fun t => dslope Real.log 1 (nearOneSupportValue S T W t))
      (𝓝[>] 0) (𝓝 1) := by
    have hh := (continuousAt_dslope_same.mpr hd.differentiableAt).tendsto.comp hK
    simpa only [dslope_same, hd.deriv, Function.comp_def] using hh
  have he (t : ℝ) (ht : 0 < t) : nearOneSupportTest S T W t =
      -c t * dslope Real.log 1 (nearOneSupportValue S T W t) / Real.log 2 := by
    have hs := sub_smul_dslope Real.log 1 (nearOneSupportValue S T W t)
    simp only [smul_eq_mul, Real.log_one, sub_zero] at hs
    unfold nearOneSupportTest logTwo
    rw [← hs, nearOneSupportValue_eq S T hSn hSc hSs W ht]
    dsimp [nearOneOrder, c]
    field_simp [ht.ne', show 1 + t ≠ 0 by linarith,
      QuantumProver.MeasuredRelativeEntropyVariational.log_two_pos.ne']
    ring
  have hh := (hc.neg.mul hds).div_const (Real.log 2)
  have he₀ : -c₀ * 1 / Real.log 2 = supportObjective S T W := by
    dsimp [c₀, supportObjective, negativeLogSupport]
    ring
  rw [he₀] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (he t ht).symm

theorem classicalRenyiDivergence_le_one {L : ℕ} (p q : Fin L → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hsum : ∑ i, p i = 1)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    classicalRenyiDivergence p q α ≤ classicalRenyiDivergence p q 1 := by
  classical
  simp only [classicalRenyiDivergence, if_pos rfl]
  by_cases hs : classicalSupportLE p q
  · let d := ∑ i, p i * (Real.log (p i) - Real.log (q i))
    have he (i : Fin L) : p i * Real.exp ((α - 1) * (Real.log (p i) - Real.log (q i))) =
        (p i) ^ α * (q i) ^ (1 - α) := by
      by_cases hz : p i = 0
      · simp [hz, Real.zero_rpow hα.ne']
      · have hpp : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hz)
        have hqp : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm (fun hh => hz (hs i hh)))
        nth_rw 1 [← Real.exp_log hpp]
        rw [Real.rpow_def_of_pos hpp, Real.rpow_def_of_pos hqp,
          ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    have hj := convexOn_exp.map_sum_le (t := Finset.univ)
      (w := p) (p := fun i => (α - 1) * (Real.log (p i) - Real.log (q i)))
      (fun i _ => hp i) hsum (fun _ _ => Set.mem_univ _)
    have hleft : (∑ i, p i * ((α - 1) * (Real.log (p i) - Real.log (q i)))) =
        (α - 1) * d := by
      dsimp [d]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hright : (∑ i, p i * Real.exp ((α - 1) * (Real.log (p i) - Real.log (q i)))) =
        classicalRenyiTrace p q α := by
      simp only [classicalRenyiTrace, Real.rpow_eq_pow, he]
    simp only [smul_eq_mul, hleft, hright] at hj
    have hQ : 0 < classicalRenyiTrace p q α := (Real.exp_pos _).trans_le hj
    have hl := Real.log_le_log (Real.exp_pos _) hj
    rw [Real.log_exp] at hl
    have hdiv : Real.log (classicalRenyiTrace p q α) / (α - 1) ≤ d :=
      (div_le_iff_of_neg (sub_neg.mpr hα1)).2 (by nlinarith)
    have hbits : ∑ i, p i * (logTwo (p i) - logTwo (q i)) = d / Real.log 2 := by
      dsimp [d]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      unfold logTwo
      ring
    rw [if_neg (ne_of_lt hα1), if_neg (by simp [not_lt_of_ge hα1.le]), if_neg hQ.ne',
      classicalUmegaki, if_pos hs, hbits]
    apply EReal.coe_le_coe_iff.mpr
    unfold logTwo
    calc
      _ = (Real.log (classicalRenyiTrace p q α) / (α - 1)) / Real.log 2 := by ring
      _ ≤ d / Real.log 2 := div_le_div_of_nonneg_right hdiv
        QuantumProver.MeasuredRelativeEntropyVariational.log_two_pos.le
  · rw [classicalUmegaki, if_neg hs]
    exact le_top

theorem measuredDivergence_le_one {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    measuredDivergence ρ σ α ≤ measuredDivergence ρ σ 1 := by
  apply sSup_le
  rintro z ⟨L, M, rfl⟩
  have hM : classicalRenyiDivergence (measurementMass M ρ) (measurementMass M σ) 1 ≤
      measuredDivergence ρ σ 1 := le_sSup ⟨L, M, rfl⟩
  exact (classicalRenyiDivergence_le_one _ _ (measurementMass_nonneg M hρ.1)
    (measurementMass_nonneg M hσ) (measurementMass_sum M hρ) hα hα1).trans
      hM

theorem setMeasuredDivergenceOn_le_one (S T : Set (CMat ι))
    (hSs : ∀ ρ ∈ S, IsState ρ) (hTp : ∀ σ ∈ T, σ.PosSemidef)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    setMeasuredDivergenceOn S T α ≤ setMeasuredDivergenceOn S T 1 := by
  apply le_sInf
  rintro z ⟨ρ, hρ, σ, hσ, rfl⟩
  have hp : setMeasuredDivergenceOn S T α ≤ measuredDivergence ρ σ α :=
    sInf_le ⟨ρ, hρ, σ, hσ, rfl⟩
  exact hp.trans
    (measuredDivergence_le_one (hSs ρ hρ) (hTp σ hσ) hα hα1)

theorem nearOneSupportTest_le_setMeasuredDivergenceOn (S T : Set (CMat ι))
    (hSc : IsCompact S) (hTc : IsCompact T)
    (hSs : ∀ ρ ∈ S, IsState ρ) (hTp : ∀ σ ∈ T, σ.PosSemidef)
    {W : CMat ι} (hW : W.PosDef) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (nearOneSupportTest S T W t : EReal) ≤ setMeasuredDivergenceOn S T (nearOneOrder t) := by
  obtain ⟨hα, hα1⟩ := nearOneOrder_bounds ht ht1
  have hα0 : 0 < nearOneOrder t := by linarith
  apply le_sInf
  rintro z ⟨ρ, hρ, σ, hσ, rfl⟩
  have hm : QuantumProver.MeasuredRenyiVariational.matrixObjective (nearOneOrder t) ρ σ W ≤
      nearOneSupportValue S T W t := by
    unfold QuantumProver.MeasuredRenyiVariational.matrixObjective
      QuantumProver.MeasuredRenyiVariational.renyiExponent nearOneSupportValue
    rw [nearOneOrder_exponent ht]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (tracePair_le_supportFunction hSc hρ _) hα0.le)
      (mul_le_mul_of_nonneg_left (tracePair_le_supportFunction hTc hσ W) (by linarith))
  have hpos := QuantumProver.MeasuredRenyiVariational.matrixObjective_pos (hSs ρ hρ) (hTp σ hσ)
    hW hα0 hα1
  have hK := hpos.trans_le hm
  have he : (nearOneSupportTest S T W t : EReal) =
      QuantumProver.MeasuredRenyiVariational.logRenyiBits (nearOneOrder t) (nearOneSupportValue S T W t) := by
    rw [QuantumProver.MeasuredRenyiVariational.logRenyiBits, if_neg hK.ne']
    rfl
  rw [he, QuantumProver.MeasuredRenyiVariational.measuredDivergence_variational
    (hSs ρ hρ) (hTp σ hσ) hα hα1]
  exact (QuantumProver.MeasuredRenyiVariational.logRenyiBits_antitone hα1 hpos.le hm).trans
    (le_sSup ⟨W, hW, rfl⟩)

theorem setMeasuredDivergenceOn_nearOne_tendsto (S T : Set (CMat ι))
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (hSv : Convex ℝ S) (hTv : Convex ℝ T)
    (hSs : ∀ ρ ∈ S, IsState ρ) (hTp : ∀ σ ∈ T, σ.PosSemidef) :
    Tendsto (fun t => setMeasuredDivergenceOn S T (nearOneOrder t))
      (𝓝[>] 0) (𝓝 (setMeasuredDivergenceOn S T 1)) := by
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ≤ 1 := by
    exact ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono inf_le_left).mono
      (fun _ h => h.le)
  rw [tendsto_order]
  constructor
  · intro y hy
    obtain ⟨b, hyb, hb⟩ := EReal.exists_between_coe_real hy
    rw [setMeasuredDivergenceOn_one_support S T hSn hTn hSc hTc hSv hTv hSs hTp] at hb
    obtain ⟨W, hbW⟩ := lt_iSup_iff.mp hb
    obtain ⟨hW, hbtest⟩ := lt_iSup_iff.mp hbW
    have hbtest' : b < supportObjective S T W := EReal.coe_lt_coe_iff.mp hbtest
    have htest := (tendsto_order.mp (nearOneSupportTest_tendsto S T hSn hSc hSs hW)).1 b hbtest'
    filter_upwards [self_mem_nhdsWithin, hsmall, htest] with t ht ht1 hbnow
    exact hyb.trans ((EReal.coe_lt_coe_iff.mpr hbnow).trans_le
      (nearOneSupportTest_le_setMeasuredDivergenceOn S T hSc hTc hSs hTp hW ht ht1))
  · intro y hy
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht1
    obtain ⟨hα, hα1⟩ := nearOneOrder_bounds ht ht1
    exact (setMeasuredDivergenceOn_le_one S T hSs hTp (by linarith) hα1).trans_lt hy

theorem setMeasuredDivergenceOn_one_eq_sup_below_one (S T : Set (CMat ι))
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (hSv : Convex ℝ S) (hTv : Convex ℝ T)
    (hSs : ∀ ρ ∈ S, IsState ρ) (hTp : ∀ σ ∈ T, σ.PosSemidef) :
    setMeasuredDivergenceOn S T 1 = sSup
      {z : EReal | ∃ α : ℝ, (1 / 2 : ℝ) ≤ α ∧ α < 1 ∧ z = setMeasuredDivergenceOn S T α} := by
  apply le_antisymm
  · apply le_of_tendsto_of_tendsto
      (setMeasuredDivergenceOn_nearOne_tendsto S T hSn hTn hSc hTc hSv hTv hSs hTp)
      tendsto_const_nhds
    have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ≤ 1 :=
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono inf_le_left).mono
        (fun _ h => h.le)
    filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht1
    obtain ⟨hα, hα1⟩ := nearOneOrder_bounds ht ht1
    exact le_sSup ⟨nearOneOrder t, hα, hα1, rfl⟩
  · apply sSup_le
    rintro z ⟨α, hα, hα1, rfl⟩
    exact setMeasuredDivergenceOn_le_one S T hSs hTp (by linarith) hα1

theorem setMeasuredDivergenceOn_tendsto_one_from_below (S T : Set (CMat ι))
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (hSv : Convex ℝ S) (hTv : Convex ℝ T)
    (hSs : ∀ ρ ∈ S, IsState ρ) (hTp : ∀ σ ∈ T, σ.PosSemidef) :
    Tendsto (setMeasuredDivergenceOn S T) (𝓝[<] 1)
      (𝓝 (setMeasuredDivergenceOn S T 1)) := by
  have hpos : ∀ᶠ α : ℝ in 𝓝[<] 1, 0 < α :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono inf_le_left
  have hc : ContinuousAt (fun α : ℝ => (1 - α) / α) 1 :=
    (continuousAt_const.sub continuousAt_id).div continuousAt_id (by norm_num)
  have ht : Tendsto (fun α : ℝ => (1 - α) / α) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using hc.tendsto.mono_left (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from inf_le_left)
    · filter_upwards [self_mem_nhdsWithin, hpos] with α hα1 hα
      exact div_pos (sub_pos.mpr hα1) hα
  have hh := (setMeasuredDivergenceOn_nearOne_tendsto S T hSn hTn hSc hTc
    hSv hTv hSs hTp).comp ht
  apply hh.congr'
  filter_upwards [hpos] with α hα
  have he : nearOneOrder ((1 - α) / α) = α := by
    unfold nearOneOrder
    field_simp [hα.ne']
    ring
  simp only [Function.comp_def, he]

theorem setMeasuredDivergenceOn_one_ne_bot (S T : Set (CMat ι))
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (hSv : Convex ℝ S) (hTv : Convex ℝ T)
    (hSs : ∀ ρ ∈ S, IsState ρ) (hTp : ∀ σ ∈ T, σ.PosSemidef) :
    setMeasuredDivergenceOn S T 1 ≠ ⊥ := by
  rw [setMeasuredDivergenceOn_one_support S T hSn hTn hSc hTc hSv hTv hSs hTp]
  apply ne_of_gt
  exact (EReal.bot_lt_coe (supportObjective S T 1)).trans_le
    (le_iSup₂_of_le (1 : CMat ι) Matrix.PosDef.one le_rfl)

section Tensor

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem matrixRpow_kronecker_of_posSemidef {A : CMat ι} {B : CMat κ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (p : ℝ) :
    matrixRpow (A ⊗ₖ B) p = matrixRpow A p ⊗ₖ matrixRpow B p := by
  have hd : Matrix.diagonal (fun x : ι × κ =>
      (Real.rpow (hA.1.eigenvalues x.1 * hB.1.eigenvalues x.2) p : ℂ)) =
      Matrix.diagonal (fun i => (Real.rpow (hA.1.eigenvalues i) p : ℂ)) ⊗ₖ
        Matrix.diagonal (fun j => (Real.rpow (hB.1.eigenvalues j) p : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal]
    congr 1
    funext x
    simpa only [Real.rpow_eq_pow, Complex.ofReal_mul] using
      congrArg (fun z : ℝ => (z : ℂ))
        (Real.mul_rpow (hA.eigenvalues_nonneg x.1) (hB.eigenvalues_nonneg x.2) (z := p))
  unfold matrixRpow
  rw [QuantumProver.SuperchannelDiscrimination.TensorEntropy.cfc_kronecker_spectral _ hA.1 hB.1, hd,
    QuantumProver.SuperchannelDiscrimination.TensorEntropy.unitaryKronecker_conjugate]
  exact congrArg₂ Matrix.kronecker
    (QuantumProver.SuperchannelDiscrimination.TensorEntropy.cfc_spectral (fun x => Real.rpow x p) hA.1).symm
    (QuantumProver.SuperchannelDiscrimination.TensorEntropy.cfc_spectral (fun x => Real.rpow x p) hB.1).symm

theorem setMeasuredDivergenceOn_one_tensor_superadditive
    (S₁ B₁ : Set (CMat ι)) (S₂ B₂ : Set (CMat κ))
    (S₁₂ B₁₂ : Set (CMat (ι × κ)))
    (hS₁n : S₁.Nonempty) (hS₂n : S₂.Nonempty) (hS₁₂n : S₁₂.Nonempty)
    (hB₁n : B₁.Nonempty) (hB₂n : B₂.Nonempty) (hB₁₂n : B₁₂.Nonempty)
    (hS₁c : IsCompact S₁) (hS₂c : IsCompact S₂) (hS₁₂c : IsCompact S₁₂)
    (hB₁c : IsCompact B₁) (hB₂c : IsCompact B₂) (hB₁₂c : IsCompact B₁₂)
    (hS₁v : Convex ℝ S₁) (hS₂v : Convex ℝ S₂) (hS₁₂v : Convex ℝ S₁₂)
    (hB₁v : Convex ℝ B₁) (hB₂v : Convex ℝ B₂) (hB₁₂v : Convex ℝ B₁₂)
    (hS₁s : ∀ ρ ∈ S₁, IsState ρ) (hS₂s : ∀ ρ ∈ S₂, IsState ρ)
    (hS₁₂s : ∀ ρ ∈ S₁₂, IsState ρ)
    (hB₁p : ∀ σ ∈ B₁, σ.PosSemidef) (hB₂p : ∀ σ ∈ B₂, σ.PosSemidef)
    (hB₁₂p : ∀ σ ∈ B₁₂, σ.PosSemidef)
    (hSpolar : ∀ A ∈ positivePolar S₁, ∀ B ∈ positivePolar S₂,
      A ⊗ₖ B ∈ positivePolar S₁₂)
    (hBpolar : ∀ A ∈ positivePolar B₁, ∀ B ∈ positivePolar B₂,
      A ⊗ₖ B ∈ positivePolar B₁₂) :
    setMeasuredDivergenceOn S₁ B₁ 1 + setMeasuredDivergenceOn S₂ B₂ 1 ≤
      setMeasuredDivergenceOn S₁₂ B₁₂ 1 := by
  have h₁ := setMeasuredDivergenceOn_nearOne_tendsto S₁ B₁ hS₁n hB₁n hS₁c hB₁c
    hS₁v hB₁v hS₁s hB₁p
  have h₂ := setMeasuredDivergenceOn_nearOne_tendsto S₂ B₂ hS₂n hB₂n hS₂c hB₂c
    hS₂v hB₂v hS₂s hB₂p
  have h₁₂ := setMeasuredDivergenceOn_nearOne_tendsto S₁₂ B₁₂ hS₁₂n hB₁₂n hS₁₂c hB₁₂c
    hS₁₂v hB₁₂v hS₁₂s hB₁₂p
  have h₁b := setMeasuredDivergenceOn_one_ne_bot S₁ B₁ hS₁n hB₁n hS₁c hB₁c
    hS₁v hB₁v hS₁s hB₁p
  have h₂b := setMeasuredDivergenceOn_one_ne_bot S₂ B₂ hS₂n hB₂n hS₂c hB₂c
    hS₂v hB₂v hS₂s hB₂p
  have hsum := (EReal.continuousAt_add (.inr h₂b) (.inl h₁b)).tendsto.comp
    (h₁.prodMk_nhds h₂)
  apply le_of_tendsto_of_tendsto hsum h₁₂
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono inf_le_left).mono
      (fun _ h => h.le)
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht1
  obtain ⟨hα, hα1⟩ := nearOneOrder_bounds ht ht1
  exact matrixSetMeasuredDivergence_tensor_superadditive S₁ B₁ S₂ B₂ S₁₂ B₁₂
    hS₁n hS₂n hS₁₂n hB₁n hB₂n hB₁₂n hS₁c hS₂c hS₁₂c hB₁c hB₂c hB₁₂c
    hS₁v hS₂v hS₁₂v hB₁v hB₂v hB₁₂v hS₁s hS₂s hS₁₂s hB₁p hB₂p hB₁₂p
    hSpolar hBpolar hα hα1
    (fun A hA B hB => matrixRpow_kronecker_of_posSemidef hA.posSemidef hB.posSemidef _)

end Tensor

theorem setMeasuredDivergence_eq_on {d : ℕ} (F : QuantumFamilies d) (n : ℕ) (α : ℝ) :
    setMeasuredDivergence F n α = setMeasuredDivergenceOn (F.null n) (F.alternative n) α := rfl

end QuantumProver.MeasuredRelativeEntropySetVariational
