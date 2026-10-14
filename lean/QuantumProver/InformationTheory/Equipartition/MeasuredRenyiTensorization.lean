import QuantumProver.InformationTheory.Equipartition.Definitions
import QuantumProver.InformationTheory.Equipartition.RenyiBounds
import QuantumProver.InformationTheory.Equipartition.FamilyIdentities

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Kronecker Topology
open Filter

namespace QuantumProver.Equipartition.FiniteModel.PolarTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def supportValues (S : Set (CMat ι)) (X : CMat ι) : Set ℝ :=
  {z | ∃ ρ ∈ S, z = tracePair ρ X}

def supportFunction (S : Set (CMat ι)) (X : CMat ι) : ℝ := sSup (supportValues S X)

theorem continuous_tracePair_left (X : CMat ι) :
    Continuous (fun ρ : CMat ι => tracePair ρ X) := by
  unfold tracePair Matrix.trace
  fun_prop

theorem supportValues_eq_image (S : Set (CMat ι)) (X : CMat ι) :
    supportValues S X = (fun ρ => tracePair ρ X) '' S := by
  ext z
  simp [supportValues, eq_comm]

theorem supportValues_nonempty {S : Set (CMat ι)} (hS : S.Nonempty) (X : CMat ι) :
    (supportValues S X).Nonempty := by
  obtain ⟨ρ, hρ⟩ := hS
  exact ⟨tracePair ρ X, ρ, hρ, rfl⟩

theorem supportValues_bddAbove {S : Set (CMat ι)} (hS : IsCompact S) (X : CMat ι) :
    BddAbove (supportValues S X) := by
  rw [supportValues_eq_image]
  exact hS.bddAbove_image (continuous_tracePair_left X).continuousOn

theorem tracePair_le_supportFunction {S : Set (CMat ι)} (hS : IsCompact S)
    {ρ : CMat ι} (hρ : ρ ∈ S) (X : CMat ι) :
    tracePair ρ X ≤ supportFunction S X :=
  le_csSup (supportValues_bddAbove hS X) ⟨ρ, hρ, rfl⟩

theorem supportFunction_le_of_bounds {S : Set (CMat ι)} (hS : S.Nonempty)
    (X : CMat ι) {b : ℝ} (hb : ∀ ρ ∈ S, tracePair ρ X ≤ b) :
    supportFunction S X ≤ b := by
  apply csSup_le (supportValues_nonempty hS X)
  rintro z ⟨ρ, hρ, rfl⟩
  exact hb ρ hρ

theorem supportFunction_nonneg {S : Set (CMat ι)} (hS : S.Nonempty)
    (hcompact : IsCompact S) (hpositive : ∀ ρ ∈ S, ρ.PosSemidef)
    {X : CMat ι} (hX : X.PosSemidef) : 0 ≤ supportFunction S X := by
  obtain ⟨ρ, hρ⟩ := hS
  exact (operator_trace_mul_nonneg (hpositive ρ hρ) hX).trans
    (tracePair_le_supportFunction hcompact hρ X)

theorem tracePair_smul_right (ρ X : CMat ι) (a : ℝ) :
    tracePair ρ (a • X) = a * tracePair ρ X := by
  simp only [tracePair, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re,
    smul_eq_mul]

theorem positivePolar_iff_supportFunction_le {S : Set (CMat ι)}
    (hS : S.Nonempty) (hcompact : IsCompact S) {X : CMat ι} :
    X ∈ positivePolar S ↔ X.PosSemidef ∧ supportFunction S X ≤ 1 := by
  constructor
  · intro hX
    exact ⟨hX.1, supportFunction_le_of_bounds hS X hX.2⟩
  · rintro ⟨hX, hbound⟩
    exact ⟨hX, fun ρ hρ => (tracePair_le_supportFunction hcompact hρ X).trans hbound⟩

theorem normalized_mem_positivePolar {S : Set (CMat ι)} (hcompact : IsCompact S)
    {X : CMat ι} (hX : X.PosSemidef) {a : ℝ} (ha : 0 < a)
    (hbound : supportFunction S X ≤ a) : a⁻¹ • X ∈ positivePolar S := by
  refine ⟨Matrix.nonneg_iff_posSemidef.mp
    (smul_nonneg (inv_nonneg.mpr ha.le) hX.nonneg), ?_⟩
  intro ρ hρ
  rw [tracePair_smul_right]
  calc
    a⁻¹ * tracePair ρ X ≤ a⁻¹ * a :=
      mul_le_mul_of_nonneg_left
        ((tracePair_le_supportFunction hcompact hρ X).trans hbound)
        (inv_nonneg.mpr ha.le)
    _ = 1 := inv_mul_cancel₀ ha.ne'

section Tensor

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem supportFunction_kronecker_le_of_positivePolar_tensor
    (S : Set (CMat ι)) (T : Set (CMat κ)) (R : Set (CMat (ι × κ)))
    (hS : S.Nonempty) (hT : T.Nonempty) (hR : R.Nonempty)
    (hSc : IsCompact S) (hTc : IsCompact T)
    (hSp : ∀ ρ ∈ S, ρ.PosSemidef) (hTp : ∀ σ ∈ T, σ.PosSemidef)
    (hpolar : ∀ X ∈ positivePolar S, ∀ Y ∈ positivePolar T,
      X ⊗ₖ Y ∈ positivePolar R)
    {X : CMat ι} {Y : CMat κ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    supportFunction R (X ⊗ₖ Y) ≤ supportFunction S X * supportFunction T Y := by
  have hs := supportFunction_nonneg hS hSc hSp hX
  have ht := supportFunction_nonneg hT hTc hTp hY
  apply supportFunction_le_of_bounds hR
  intro ρ hρ
  have happrox (ε : ℝ) (hε : 0 < ε) :
      tracePair ρ (X ⊗ₖ Y) ≤
        (supportFunction S X + ε) * (supportFunction T Y + ε) := by
    let a := supportFunction S X + ε
    let b := supportFunction T Y + ε
    have ha : 0 < a := by dsimp [a]; linarith
    have hb : 0 < b := by dsimp [b]; linarith
    have hXp : a⁻¹ • X ∈ positivePolar S :=
      normalized_mem_positivePolar hSc hX ha (by dsimp [a]; linarith)
    have hYp : b⁻¹ • Y ∈ positivePolar T :=
      normalized_mem_positivePolar hTc hY hb (by dsimp [b]; linarith)
    have hn := (hpolar _ hXp _ hYp).2 ρ hρ
    rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
      tracePair_smul_right] at hn
    have hd : tracePair ρ (X ⊗ₖ Y) / (a * b) ≤ 1 := by
      simpa only [div_eq_mul_inv, mul_inv, mul_comm, mul_left_comm, mul_assoc] using hn
    simpa only [one_mul] using (div_le_iff₀ (mul_pos ha hb)).mp hd
  have hlim : Tendsto (fun ε : ℝ =>
      (supportFunction S X + ε) * (supportFunction T Y + ε))
      (𝓝[>] 0) (𝓝 (supportFunction S X * supportFunction T Y)) := by
    have hc : Continuous (fun ε : ℝ =>
        (supportFunction S X + ε) * (supportFunction T Y + ε)) := by fun_prop
    simpa only [add_zero] using hc.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (by filter_upwards [self_mem_nhdsWithin] with ε hε; exact happrox ε hε)

end Tensor

section PolarEquivalence

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem positivePolar_kronecker_of_supportFunction_le
    (S : Set (CMat ι)) (T : Set (CMat κ)) (R : Set (CMat (ι × κ)))
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hSc : IsCompact S) (hTc : IsCompact T) (hRc : IsCompact R)
    (hSp : ∀ ρ ∈ S, ρ.PosSemidef) (hTp : ∀ σ ∈ T, σ.PosSemidef)
    (hbound : ∀ X : CMat ι, X.PosSemidef → ∀ Y : CMat κ, Y.PosSemidef →
      supportFunction R (X ⊗ₖ Y) ≤ supportFunction S X * supportFunction T Y)
    {X : CMat ι} {Y : CMat κ} (hX : X ∈ positivePolar S)
    (hY : Y ∈ positivePolar T) : X ⊗ₖ Y ∈ positivePolar R := by
  have hx := (positivePolar_iff_supportFunction_le hS hSc).mp hX
  have hy := (positivePolar_iff_supportFunction_le hT hTc).mp hY
  refine ⟨hX.1.kronecker hY.1, ?_⟩
  intro ρ hρ
  calc
    tracePair ρ (X ⊗ₖ Y) ≤ supportFunction R (X ⊗ₖ Y) :=
      tracePair_le_supportFunction hRc hρ _
    _ ≤ supportFunction S X * supportFunction T Y := hbound X hX.1 Y hY.1
    _ ≤ 1 := by
      have ht := supportFunction_nonneg hT hTc hTp hY.1
      simpa only [one_mul] using mul_le_mul hx.2 hy.2 ht (by norm_num : (0 : ℝ) ≤ 1)

theorem positivePolar_tensor_iff_supportFunction_submultiplicative
    (S : Set (CMat ι)) (T : Set (CMat κ)) (R : Set (CMat (ι × κ)))
    (hS : S.Nonempty) (hT : T.Nonempty) (hR : R.Nonempty)
    (hSc : IsCompact S) (hTc : IsCompact T) (hRc : IsCompact R)
    (hSp : ∀ ρ ∈ S, ρ.PosSemidef) (hTp : ∀ σ ∈ T, σ.PosSemidef) :
    (∀ X ∈ positivePolar S, ∀ Y ∈ positivePolar T, X ⊗ₖ Y ∈ positivePolar R) ↔
      (∀ X : CMat ι, X.PosSemidef → ∀ Y : CMat κ, Y.PosSemidef →
        supportFunction R (X ⊗ₖ Y) ≤ supportFunction S X * supportFunction T Y) := by
  constructor
  · intro hpolar X hX Y hY
    exact supportFunction_kronecker_le_of_positivePolar_tensor S T R hS hT hR
      hSc hTc hSp hTp hpolar hX hY
  · intro hbound X hX Y hY
    exact positivePolar_kronecker_of_supportFunction_le S T R hS hT hSc hTc hRc
      hSp hTp hbound hX hY

end PolarEquivalence

section NegativePowerEpigraph

theorem convexOn_cfcRpow_negative {p : ℝ} (hp : -1 ≤ p) (hp0 : p < 0) :
    ConvexOn ℝ {A : CMat ι | IsStrictlyPositive A} (fun A => CFC.rpow A p) := by
  let q : ℝ := -p
  have hq : q ∈ Set.Icc 0 1 := by dsimp [q]; constructor <;> linarith
  have hq0 : q ≠ 0 := by dsimp [q]; linarith
  have hinv := CStarAlgebra.convexOn_ringInverse (A := CMat ι)
  have he (A : CMat ι) (hA : IsStrictlyPositive A) :
      Ring.inverse (CFC.rpow A q) = CFC.rpow A p := by
    simp only [CFC.rpow_eq_pow]
    rw [CFC.inverse_rpow A q hq0 hA]
    simp only [q, neg_neg]
  refine ⟨hinv.1, ?_⟩
  intro A hA B hB a b ha hb hab
  have hC : IsStrictlyPositive (a • A + b • B) := hinv.1 hA hB ha hb hab
  have hAq : IsStrictlyPositive (CFC.rpow A q) := IsStrictlyPositive.rpow A q hA
  have hBq : IsStrictlyPositive (CFC.rpow B q) := IsStrictlyPositive.rpow B q hB
  have hD : IsStrictlyPositive (a • CFC.rpow A q + b • CFC.rpow B q) :=
    hinv.1 hAq hBq ha hb hab
  have hCq : IsStrictlyPositive (CFC.rpow (a • A + b • B) q) :=
    IsStrictlyPositive.rpow _ q hC
  have hconc := (CFC.concaveOn_rpow (A := CMat ι) hq).2
    hA.nonneg hB.nonneg ha hb hab
  have hanti := CStarAlgebra.rpow_neg_one_le_rpow_neg_one hconc hD
  calc
    CFC.rpow (a • A + b • B) p =
        Ring.inverse (CFC.rpow (a • A + b • B) q) := (he _ hC).symm
    _ ≤ Ring.inverse (a • CFC.rpow A q + b • CFC.rpow B q) := by
      rw [CFC.inverse_eq_rpow_neg_one hCq, CFC.inverse_eq_rpow_neg_one hD]
      exact hanti
    _ ≤ a • Ring.inverse (CFC.rpow A q) + b • Ring.inverse (CFC.rpow B q) :=
      hinv.2 hAq hBq ha hb hab
    _ = a • CFC.rpow A p + b • CFC.rpow B p := by rw [he A hA, he B hB]

theorem convexOn_matrixRpow_negative {p : ℝ} (hp : -1 ≤ p) (hp0 : p < 0) :
    ConvexOn ℝ {A : CMat ι | A.PosDef} (fun A => matrixRpow A p) := by
  have hc := (convexOn_cfcRpow_negative (ι := ι) hp hp0).congr
    (fun A hA => (show CFC.rpow A p = matrixRpow A p from
      CFC.rpow_eq_cfc_real hA.nonneg))
  simpa only [Matrix.isStrictlyPositive_iff_posDef] using hc

def renyiEpigraph (α : ℝ) : Set (CMat ι × CMat ι) :=
  {z | z.1.PosDef ∧ LoewnerLE (matrixRpow z.1 ((α - 1) / α)) z.2}

theorem renyiExponent_mem {α : ℝ} (hα : (1 / 2 : ℝ) ≤ α) (hα1 : α < 1) :
    (α - 1) / α ∈ Set.Ico (-1) 0 := by
  have ha : 0 < α := by linarith
  constructor
  · apply (le_div_iff₀ ha).mpr
    linarith
  · exact div_neg_of_neg_of_pos (by linarith) ha

theorem convex_renyiEpigraph {α : ℝ} (hα : (1 / 2 : ℝ) ≤ α) (hα1 : α < 1) :
    Convex ℝ (renyiEpigraph (ι := ι) α) := by
  have hp := renyiExponent_mem hα hα1
  have hc := convexOn_matrixRpow_negative (ι := ι) hp.1 hp.2
  intro X hX Y hY a b ha hb hab
  refine ⟨hc.1 hX.1 hY.1 ha hb hab, ?_⟩
  apply Matrix.nonneg_iff_posSemidef.mp
  change 0 ≤ a • X.2 + b • Y.2 -
    matrixRpow (a • X.1 + b • Y.1) ((α - 1) / α)
  apply sub_nonneg.mpr
  calc
    matrixRpow (a • X.1 + b • Y.1) ((α - 1) / α) ≤
        a • matrixRpow X.1 ((α - 1) / α) +
          b • matrixRpow Y.1 ((α - 1) / α) := hc.2 hX.1 hY.1 ha hb hab
    _ ≤ a • X.2 + b • Y.2 := by
      have hx : matrixRpow X.1 ((α - 1) / α) ≤ X.2 :=
        sub_nonneg.mp hX.2.nonneg
      have hy : matrixRpow Y.1 ((α - 1) / α) ≤ Y.2 :=
        sub_nonneg.mp hY.2.nonneg
      gcongr

end NegativePowerEpigraph

section MatrixSion

def renyiLinearObjective (α : ℝ) (X Z : CMat ι × CMat ι) : ℝ :=
  α * tracePair X.1 Z.2 + (1 - α) * tracePair X.2 Z.1

def tracePairLeftMap (V : CMat ι) : CMat ι →ₗ[ℝ] ℝ where
  toFun A := tracePair A V
  map_add' A B := by simp [tracePair, Matrix.add_mul, Matrix.trace_add]
  map_smul' a A := by
    simp [tracePair, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re]

def tracePairRightMap (A : CMat ι) : CMat ι →ₗ[ℝ] ℝ where
  toFun V := tracePair A V
  map_add' V W := by simp [tracePair, Matrix.mul_add, Matrix.trace_add]
  map_smul' a V := by simpa only [smul_eq_mul, RingHom.id_apply] using tracePair_smul_right A V a

def renyiLinearLeftMap (α : ℝ) (Z : CMat ι × CMat ι) :
    (CMat ι × CMat ι) →ₗ[ℝ] ℝ :=
  α • (tracePairLeftMap Z.2).comp (LinearMap.fst ℝ (CMat ι) (CMat ι)) +
    (1 - α) • (tracePairLeftMap Z.1).comp (LinearMap.snd ℝ (CMat ι) (CMat ι))

def renyiLinearRightMap (α : ℝ) (X : CMat ι × CMat ι) :
    (CMat ι × CMat ι) →ₗ[ℝ] ℝ :=
  α • (tracePairRightMap X.1).comp (LinearMap.snd ℝ (CMat ι) (CMat ι)) +
    (1 - α) • (tracePairRightMap X.2).comp (LinearMap.fst ℝ (CMat ι) (CMat ι))

theorem renyiLinearLeftMap_apply (α : ℝ) (X Z : CMat ι × CMat ι) :
    renyiLinearLeftMap α Z X = renyiLinearObjective α X Z := rfl

theorem renyiLinearRightMap_apply (α : ℝ) (X Z : CMat ι × CMat ι) :
    renyiLinearRightMap α X Z = renyiLinearObjective α X Z := rfl

theorem continuous_renyiLinearObjective_left (α : ℝ) (Z : CMat ι × CMat ι) :
    Continuous (fun X => renyiLinearObjective α X Z) := by
  unfold renyiLinearObjective tracePair Matrix.trace
  fun_prop

theorem continuous_renyiLinearObjective_right (α : ℝ) (X : CMat ι × CMat ι) :
    Continuous (fun Z => renyiLinearObjective α X Z) := by
  unfold renyiLinearObjective tracePair Matrix.trace
  fun_prop

theorem renyiLinearObjective_minimax (S T : Set (CMat ι))
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (hSv : Convex ℝ S) (hTv : Convex ℝ T)
    {α : ℝ} (hα : (1 / 2 : ℝ) ≤ α) (hα1 : α < 1) :
    (⨆ X ∈ S ×ˢ T, ⨅ Z ∈ renyiEpigraph (ι := ι) α,
      (renyiLinearObjective α X Z : EReal)) =
    ⨅ Z ∈ renyiEpigraph (ι := ι) α, ⨆ X ∈ S ×ˢ T,
      (renyiLinearObjective α X Z : EReal) := by
  let f (X Z : CMat ι × CMat ι) : OrderDual EReal :=
    OrderDual.toDual (renyiLinearObjective α X Z : EReal)
  have hc := convex_renyiEpigraph (ι := ι) hα hα1
  have hleft (Z : CMat ι × CMat ι) : Continuous (fun X => f X Z) :=
    continuous_toDual.comp (continuous_coe_real_ereal.comp
      (continuous_renyiLinearObjective_left α Z))
  have hright (X : CMat ι × CMat ι) : Continuous (fun Z => f X Z) :=
    continuous_toDual.comp (continuous_coe_real_ereal.comp
      (continuous_renyiLinearObjective_right α X))
  have hleftq (Z : CMat ι × CMat ι) :
      QuasiconvexOn ℝ (S ×ˢ T) (fun X => f X Z) := by
    have hq := ((renyiLinearLeftMap α Z).concaveOn (hSv.prod hTv)).quasiconcaveOn
    have hqe := hq.monotone_comp EReal.orderEmbedding.monotone
    exact hqe.dual
  have hrightq (X : CMat ι × CMat ι) :
      QuasiconcaveOn ℝ (renyiEpigraph (ι := ι) α) (fun Z => f X Z) := by
    have hq := ((renyiLinearRightMap α X).convexOn hc).quasiconvexOn
    have hqe := hq.monotone_comp EReal.orderEmbedding.monotone
    exact hqe.dual
  exact Sion.minimax' (X := S ×ˢ T) (Y := renyiEpigraph (ι := ι) α) (f := f)
    (hSn.prod hTn) (hSv.prod hTv) (hSc.prod hTc)
    (fun Z _ => (hleft Z).continuousOn.lowerSemicontinuousOn) (fun Z _ => hleftq Z) hc
    (fun X _ => (hright X).continuousOn.upperSemicontinuousOn) (fun X _ => hrightq X)

end MatrixSion

section SupportObjective

theorem supportFunction_attained {S : Set (CMat ι)} (hSn : S.Nonempty)
    (hSc : IsCompact S) (V : CMat ι) :
    ∃ ρ ∈ S, tracePair ρ V = supportFunction S V := by
  have hcompact : IsCompact (supportValues S V) := by
    rw [supportValues_eq_image]
    exact hSc.image (continuous_tracePair_left V)
  obtain ⟨ρ, hρ, he⟩ := hcompact.sSup_mem (supportValues_nonempty hSn V)
  exact ⟨ρ, hρ, he.symm⟩

theorem supportFunction_smul {S : Set (CMat ι)} (hSn : S.Nonempty)
    (hSc : IsCompact S) (V : CMat ι) {a : ℝ} (ha : 0 ≤ a) :
    supportFunction S (a • V) = a * supportFunction S V := by
  apply le_antisymm
  · apply supportFunction_le_of_bounds hSn
    intro ρ hρ
    rw [tracePair_smul_right]
    exact mul_le_mul_of_nonneg_left (tracePair_le_supportFunction hSc hρ V) ha
  · obtain ⟨ρ, hρ, he⟩ := supportFunction_attained hSn hSc V
    calc
      a * supportFunction S V = tracePair ρ (a • V) := by rw [tracePair_smul_right, he]
      _ ≤ supportFunction S (a • V) := tracePair_le_supportFunction hSc hρ _

theorem tracePair_mono_of_loewner {ρ V W : CMat ι} (hρ : ρ.PosSemidef)
    (hVW : LoewnerLE V W) : tracePair ρ V ≤ tracePair ρ W := by
  have h := operator_trace_mul_nonneg hρ hVW
  change 0 ≤ tracePair ρ (W - V) at h
  have he : tracePair ρ (W - V) = tracePair ρ W - tracePair ρ V := by
    simp [tracePair, Matrix.mul_sub, Matrix.trace_sub]
  rw [he] at h
  linarith

theorem supportFunction_mono_of_loewner {S : Set (CMat ι)} (hSn : S.Nonempty)
    (hSc : IsCompact S) (hSp : ∀ ρ ∈ S, ρ.PosSemidef)
    {V W : CMat ι} (hVW : LoewnerLE V W) :
    supportFunction S V ≤ supportFunction S W := by
  apply supportFunction_le_of_bounds hSn
  intro ρ hρ
  exact (tracePair_mono_of_loewner (hSp ρ hρ) hVW).trans
    (tracePair_le_supportFunction hSc hρ W)

theorem iSup_renyiLinearObjective (S T : Set (CMat ι))
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (Z : CMat ι × CMat ι) :
    (⨆ X ∈ S ×ˢ T, (renyiLinearObjective α X Z : EReal)) =
      ((α * supportFunction S Z.2 + (1 - α) * supportFunction T Z.1 : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup₂_le
    rintro ⟨ρ, σ⟩ ⟨hρ, hσ⟩
    apply EReal.coe_le_coe_iff.mpr
    exact add_le_add
      (mul_le_mul_of_nonneg_left (tracePair_le_supportFunction hSc hρ Z.2) hα)
      (mul_le_mul_of_nonneg_left (tracePair_le_supportFunction hTc hσ Z.1)
        (sub_nonneg.mpr hα1))
  · obtain ⟨ρ, hρ, heρ⟩ := supportFunction_attained hSn hSc Z.2
    obtain ⟨σ, hσ, heσ⟩ := supportFunction_attained hTn hTc Z.1
    have he : renyiLinearObjective α (ρ, σ) Z =
        α * supportFunction S Z.2 + (1 - α) * supportFunction T Z.1 := by
      simp only [renyiLinearObjective, heρ, heσ]
    rw [← he]
    exact le_iSup₂_of_le (ρ, σ) ⟨hρ, hσ⟩ le_rfl

theorem renyi_support_minimax (S T : Set (CMat ι))
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (hSv : Convex ℝ S) (hTv : Convex ℝ T)
    {α : ℝ} (hα : (1 / 2 : ℝ) ≤ α) (hα1 : α < 1) :
    (⨆ X ∈ S ×ˢ T, ⨅ Z ∈ renyiEpigraph (ι := ι) α,
      (renyiLinearObjective α X Z : EReal)) =
    ⨅ Z ∈ renyiEpigraph (ι := ι) α,
      ((α * supportFunction S Z.2 + (1 - α) * supportFunction T Z.1 : ℝ) : EReal) := by
  rw [renyiLinearObjective_minimax S T hSn hTn hSc hTc hSv hTv hα hα1]
  have ha : 0 ≤ α := by linarith
  simp_rw [iSup_renyiLinearObjective S T hSn hTn hSc hTc ha hα1.le]

end SupportObjective

section CompressionJensen

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem mulVec_injective_of_isometry {V : Matrix κ ι ℂ} (hV : Vᴴ * V = 1) :
    Function.Injective V.mulVec := by
  intro x y h
  have hh := congrArg (fun z => Vᴴ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec] using hh

theorem cfc_compression_of_intertwining {B : CMat κ} {W : CMat ι}
    (hB : B.IsHermitian) (hW : W.IsHermitian) {V : Matrix κ ι ℂ}
    (hV : Vᴴ * V = 1) (hBV : B * V = V * W) (f : ℝ → ℝ) :
    Vᴴ * cfc f B * V = cfc f W := by
  classical
  let P := Testing.spectralPinchingProjection hW
  have hAP (k : Testing.SpectralLabels hW) :
      B * (V * P k * Vᴴ) = ((k : ℝ) : ℂ) • (V * P k * Vᴴ) := by
    calc
      _ = (B * V) * P k * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * (W * P k) * Vᴴ := by rw [hBV]; simp only [Matrix.mul_assoc]
      _ = ((k : ℝ) : ℂ) • (V * P k * Vᴴ) := by
        rw [Testing.spectralPinchingProjection_mul_left, Matrix.mul_smul, Matrix.smul_mul]
  have hCP (k : Testing.SpectralLabels hW) :
      (Vᴴ * cfc f B * V) * P k = (f (k : ℝ) : ℂ) • P k := by
    have hh := congrArg (fun A : CMat κ => Vᴴ * A * V)
      (Testing.cfc_mul_of_eigenmatrix hB (hAP k) f)
    have hleft : Vᴴ * (cfc f B * (V * P k * Vᴴ)) * V =
        (Vᴴ * cfc f B * V) * P k := by
      simp only [Matrix.mul_assoc, hV, Matrix.mul_one]
    have hright : Vᴴ * ((f (k : ℝ) : ℂ) • (V * P k * Vᴴ)) * V =
        (f (k : ℝ) : ℂ) • P k := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      calc
        Vᴴ * (V * P k * Vᴴ) * V = (Vᴴ * V) * P k * (Vᴴ * V) := by
          simp only [Matrix.mul_assoc]
        _ = P k := by rw [hV, Matrix.one_mul, Matrix.mul_one]
    rwa [hleft, hright] at hh
  calc
    Vᴴ * cfc f B * V = (Vᴴ * cfc f B * V) * (∑ k, P k) := by
      rw [Testing.sum_spectralPinchingProjection, Matrix.mul_one]
    _ = ∑ k : Testing.SpectralLabels hW, (f (k : ℝ) : ℂ) • P k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => hCP k
    _ = cfc f W := (Testing.cfc_eq_sum_of_eigenmatrix_resolution hW P
      (fun k => (k : ℝ)) (Testing.sum_spectralPinchingProjection hW)
      (Testing.spectralPinchingProjection_mul_left hW) f).symm

theorem matrixRpow_compression_jensen {D : CMat κ} (hD : D.PosDef)
    {V : Matrix κ ι ℂ} (hV : Vᴴ * V = 1) {p : ℝ} (hp : -1 ≤ p) (hp0 : p < 0) :
    LoewnerLE (matrixRpow (Vᴴ * D * V) p) (Vᴴ * matrixRpow D p * V) := by
  classical
  let P : CMat κ := V * Vᴴ
  let J : CMat κ := P + P - 1
  let W : CMat ι := Vᴴ * D * V
  let B : CMat κ := (1 / 2 : ℝ) • D + (1 / 2 : ℝ) • (J * D * J)
  have hPV : P * V = V := by
    dsimp [P]
    rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  have hPP : P * P = P := by
    dsimp [P]
    calc
      (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  have hPstar : Pᴴ = P := by simp [P]
  have hJstar : Jᴴ = J := by simp [J, hPstar]
  have hJV : J * V = V := by simp [J, Matrix.add_mul, Matrix.sub_mul, hPV]
  have hVJ : Vᴴ * J = Vᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJstar] using
      congrArg Matrix.conjTranspose hJV
  have hJJ : J * J = 1 := by
    calc
      J * J = P * P + P * P + P * P + P * P - P - P - P - P + 1 := by
        dsimp [J]
        noncomm_ring
      _ = 1 := by rw [hPP]; abel
  have hJinj : Function.Injective J.mulVec := by
    intro x y h
    have hh := congrArg (fun z => J *ᵥ z) h
    simpa only [Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec] using hh
  have hJD : (J * D * J).PosDef := by
    simpa only [hJstar] using hD.conjTranspose_mul_mul_same hJinj
  have hc := convexOn_matrixRpow_negative (ι := κ) hp hp0
  have hB : B.PosDef := hc.1 hD hJD (by norm_num) (by norm_num) (by norm_num)
  have hW : W.PosDef := hD.conjTranspose_mul_mul_same (mulVec_injective_of_isometry hV)
  have hBV : B * V = V * W := by
    dsimp [B]
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hJV]
    dsimp [J, P, W]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    module
  have hcomp : Vᴴ * matrixRpow B p * V = matrixRpow W p :=
    cfc_compression_of_intertwining hB.1 hW.1 hV hBV (fun x => Real.rpow x p)
  let U : Matrix.unitaryGroup κ ℂ := ⟨J, Matrix.mem_unitaryGroup_iff.mpr
    (by rw [Matrix.star_eq_conjTranspose, hJstar, hJJ])⟩
  have hpowJ : matrixRpow (J * D * J) p = J * matrixRpow D p * J := by
    have hh := matrixRpow_unitary_conjugate U hD.posSemidef p
    change matrixRpow (J * D * Jᴴ) p = J * matrixRpow D p * Jᴴ at hh
    simpa only [hJstar] using hh
  have hbound : matrixRpow B p ≤
      (1 / 2 : ℝ) • matrixRpow D p + (1 / 2 : ℝ) • matrixRpow (J * D * J) p :=
    hc.2 hD hJD (by norm_num) (by norm_num) (by norm_num)
  have he : Vᴴ * ((1 / 2 : ℝ) • matrixRpow D p +
      (1 / 2 : ℝ) • matrixRpow (J * D * J) p) * V = Vᴴ * matrixRpow D p * V := by
    rw [hpowJ]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    have hj : Vᴴ * (J * matrixRpow D p * J) * V = Vᴴ * matrixRpow D p * V := by
      calc
        _ = (Vᴴ * J) * matrixRpow D p * (J * V) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hVJ, hJV]
    rw [hj]
    module
  have hs := (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hbound)).conjTranspose_mul_mul_same V
  simp only [Matrix.mul_sub, Matrix.sub_mul, he, hcomp] at hs
  exact hs

end CompressionJensen

section PhysicalPOVMJensen

variable {L : ℕ}

def povmWeightedObservable (M : FinitePOVM ι L) (r : Fin L → ℝ) : CMat ι :=
  ∑ j, (r j : ℂ) • M.outcome j

def povmIsometry (M : FinitePOVM ι L) : Matrix (Fin L × ι) ι ℂ :=
  fun z k => (CFC.sqrt (M.outcome z.1)) z.2 k

def povmDilationDiagonal (r : Fin L → ℝ) : CMat (Fin L × ι) :=
  Matrix.diagonal (fun z => (r z.1 : ℂ))

theorem sqrt_outcome_mul (M : FinitePOVM ι L) (j : Fin L) :
    (CFC.sqrt (M.outcome j))ᴴ * CFC.sqrt (M.outcome j) = M.outcome j := by
  have hs := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M.outcome j))).1.eq
  rw [hs, ← pow_two, CFC.sq_sqrt (M.outcome j) (M.positive j).nonneg]

theorem povmIsometry_isometry (M : FinitePOVM ι L) :
    (povmIsometry M)ᴴ * povmIsometry M = 1 := by
  have he : (povmIsometry M)ᴴ * povmIsometry M =
      ∑ j, (CFC.sqrt (M.outcome j))ᴴ * CFC.sqrt (M.outcome j) := by
    ext x y
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, povmIsometry,
      Matrix.sum_apply, Fintype.sum_prod_type]
  rw [he]
  simpa only [sqrt_outcome_mul] using M.sum_outcome

theorem povmDilationDiagonal_posDef (r : Fin L → ℝ) (hr : ∀ j, 0 < r j) :
    (povmDilationDiagonal (ι := ι) r).PosDef := by
  apply Matrix.PosDef.diagonal
  intro z
  exact Complex.zero_lt_real.mpr (hr z.1)

theorem povmIsometry_diagonal_compression (M : FinitePOVM ι L) (r : Fin L → ℝ) :
    (povmIsometry M)ᴴ * povmDilationDiagonal (ι := ι) r * povmIsometry M =
      povmWeightedObservable M r := by
  have he : (povmIsometry M)ᴴ * povmDilationDiagonal (ι := ι) r * povmIsometry M =
      ∑ j, (r j : ℂ) • ((CFC.sqrt (M.outcome j))ᴴ * CFC.sqrt (M.outcome j)) := by
    ext x y
    rw [Matrix.mul_assoc]
    simp only [povmDilationDiagonal]
    rw [Matrix.mul_apply]
    simp only [Matrix.diagonal_mul]
    simp only [Matrix.mul_apply,
      Matrix.conjTranspose_apply, povmIsometry, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  simp only [sqrt_outcome_mul, povmWeightedObservable]

theorem cfc_diagonal_pos_real {κ : Type*} [Fintype κ] [DecidableEq κ]
    (r : κ → ℝ) (hr : ∀ j, 0 < r j) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun j => (r j : ℂ))) =
      Matrix.diagonal (fun j => (f (r j) : ℂ)) := by
  classical
  let P := Testing.diagonalSelector (id : κ → κ)
  have hD : (Matrix.diagonal (fun j => (r j : ℂ))).PosDef :=
    Matrix.PosDef.diagonal (fun j => Complex.zero_lt_real.mpr (hr j))
  have hAP (k : κ) : Matrix.diagonal (fun j => (r j : ℂ)) * P k =
      (r k : ℂ) • P k := by
    ext x y
    by_cases hxy : x = y
    · subst y
      by_cases hxk : x = k
      · subst k
        simp [P, Testing.diagonalSelector, Matrix.diagonal_mul_diagonal]
      · simp [P, Testing.diagonalSelector, Matrix.diagonal_mul_diagonal, hxk]
    · simp [P, Testing.diagonalSelector, Matrix.diagonal_mul_diagonal, hxy]
  rw [Testing.cfc_eq_sum_of_eigenmatrix_resolution hD.1 P r
    (Testing.sum_diagonalSelector (id : κ → κ)) hAP f]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [P, Testing.diagonalSelector, Matrix.sum_apply, Matrix.smul_apply]
  · simp [P, Testing.diagonalSelector, Matrix.sum_apply, Matrix.smul_apply, hxy]

theorem matrixRpow_povmDilationDiagonal (r : Fin L → ℝ) (hr : ∀ j, 0 < r j) (p : ℝ) :
    matrixRpow (povmDilationDiagonal (ι := ι) r) p =
      povmDilationDiagonal (ι := ι) (fun j => Real.rpow (r j) p) :=
  cfc_diagonal_pos_real (fun z : Fin L × ι => r z.1) (fun z => hr z.1) _

theorem povmWeightedObservable_posDef (M : FinitePOVM ι L) (r : Fin L → ℝ)
    (hr : ∀ j, 0 < r j) : (povmWeightedObservable M r).PosDef := by
  rw [← povmIsometry_diagonal_compression]
  exact (povmDilationDiagonal_posDef (ι := ι) r hr).conjTranspose_mul_mul_same
    (mulVec_injective_of_isometry (povmIsometry_isometry M))

theorem matrixRpow_povmWeightedObservable_le (M : FinitePOVM ι L)
    (r : Fin L → ℝ) (hr : ∀ j, 0 < r j) {p : ℝ} (hp : -1 ≤ p) (hp0 : p < 0) :
    LoewnerLE (matrixRpow (povmWeightedObservable M r) p)
      (povmWeightedObservable M (fun j => Real.rpow (r j) p)) := by
  have hj := matrixRpow_compression_jensen (povmDilationDiagonal_posDef (ι := ι) r hr)
    (povmIsometry_isometry M) hp hp0
  rw [povmIsometry_diagonal_compression, matrixRpow_povmDilationDiagonal r hr,
    povmIsometry_diagonal_compression] at hj
  exact hj

end PhysicalPOVMJensen

end QuantumProver.Equipartition.FiniteModel.PolarTensor
