import QuantumProver.InformationTheory.Equipartition.MeasuredRenyiTensorization
import QuantumProver.InformationTheory.MeasuredRenyiVariational

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Kronecker Topology
open Filter

namespace QuantumProver.Equipartition.FiniteModel.PolarTensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixRpow_posDef_variational {W : CMat ι} (hW : W.PosDef) (p : ℝ) :
    (matrixRpow W p).PosDef := by
  have he : CFC.rpow W p = matrixRpow W p :=
    CFC.rpow_eq_cfc_real hW.posSemidef.nonneg
  rw [← he]
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.rpow W p hW.isStrictlyPositive)

theorem renyiEpigraph_second_posDef {α : ℝ} {Z : CMat ι × CMat ι}
    (hZ : Z ∈ renyiEpigraph α) : Z.2.PosDef := by
  apply Matrix.isStrictlyPositive_iff_posDef.mp
  exact (matrixRpow_posDef_variational hZ.1 ((α - 1) / α)).isStrictlyPositive.of_le
    (sub_nonneg.mp hZ.2.nonneg)

def renyiPolarFeasible (T : Set (CMat ι)) (α : ℝ) : Set (CMat ι × CMat ι) :=
  {Z | Z ∈ renyiEpigraph α ∧ Z.1 ∈ positivePolar T}

theorem renyiEpigraph_scale {α a : ℝ} (ha : 0 < a) {Z : CMat ι × CMat ι}
    (hZ : Z ∈ renyiEpigraph α) :
    (a • Z.1, Real.rpow a ((α - 1) / α) • Z.2) ∈ renyiEpigraph α := by
  refine ⟨hZ.1.smul ha, ?_⟩
  change (Real.rpow a ((α - 1) / α) • Z.2 -
    matrixRpow (a • Z.1) ((α - 1) / α)).PosSemidef
  rw [matrixRpow_smul Z.1 hZ.1.posSemidef _ ha, ← smul_sub]
  exact hZ.2.smul (Real.rpow_pos_of_pos ha _).le

theorem renyiPolarFeasible_normalize {T : Set (CMat ι)} (hTc : IsCompact T)
    {α b : ℝ} (hb : 0 < b) {Z : CMat ι × CMat ι}
    (hZ : Z ∈ renyiEpigraph α) (hbound : supportFunction T Z.1 ≤ b) :
    (b⁻¹ • Z.1, Real.rpow b⁻¹ ((α - 1) / α) • Z.2) ∈ renyiPolarFeasible T α :=
  ⟨renyiEpigraph_scale (inv_pos.mpr hb) hZ,
    normalized_mem_positivePolar hTc hZ.1.posSemidef hb hbound⟩

section Tensor

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem loewnerLE_kronecker {A V : CMat ι} {B W : CMat κ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAV : LoewnerLE A V) (hBW : LoewnerLE B W) :
    LoewnerLE (A ⊗ₖ B) (V ⊗ₖ W) := by
  have hW : W.PosSemidef := by
    have hh := hB.add hBW
    simpa only [add_sub_cancel] using hh
  have hp := (hAV.kronecker hW).add (hA.kronecker hBW)
  have he : (V - A) ⊗ₖ W + A ⊗ₖ (W - B) = V ⊗ₖ W - A ⊗ₖ B := by
    ext x y
    simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply]
    ring
  change (V ⊗ₖ W - A ⊗ₖ B).PosSemidef
  rw [← he]
  exact hp

theorem renyiPolarFeasible_kronecker
    (T : Set (CMat ι)) (U : Set (CMat κ)) (R : Set (CMat (ι × κ)))
    (hpolar : ∀ W ∈ positivePolar T, ∀ V ∈ positivePolar U,
      W ⊗ₖ V ∈ positivePolar R)
    {α : ℝ} {X : CMat ι × CMat ι} {Y : CMat κ × CMat κ}
    (hX : X ∈ renyiPolarFeasible T α) (hY : Y ∈ renyiPolarFeasible U α)
    (hpow : matrixRpow (X.1 ⊗ₖ Y.1) ((α - 1) / α) =
      matrixRpow X.1 ((α - 1) / α) ⊗ₖ matrixRpow Y.1 ((α - 1) / α)) :
    (X.1 ⊗ₖ Y.1, X.2 ⊗ₖ Y.2) ∈ renyiPolarFeasible R α := by
  refine ⟨⟨hX.1.1.kronecker hY.1.1, ?_⟩, hpolar _ hX.2 _ hY.2⟩
  change LoewnerLE (matrixRpow (X.1 ⊗ₖ Y.1) ((α - 1) / α)) (X.2 ⊗ₖ Y.2)
  rw [hpow]
  exact loewnerLE_kronecker
    (matrixRpow_posDef_variational hX.1.1 _).posSemidef
    (matrixRpow_posDef_variational hY.1.1 _).posSemidef hX.1.2 hY.1.2

theorem renyi_tensor_support_bound
    (S : Set (CMat ι)) (T : Set (CMat κ)) (R : Set (CMat (ι × κ)))
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hRn : R.Nonempty)
    (hSc : IsCompact S) (hTc : IsCompact T)
    (hSp : ∀ ρ ∈ S, ρ.PosSemidef) (hTp : ∀ σ ∈ T, σ.PosSemidef)
    (hpolar : ∀ A ∈ positivePolar S, ∀ B ∈ positivePolar T,
      A ⊗ₖ B ∈ positivePolar R)
    {α : ℝ} {X : CMat ι × CMat ι} {Y : CMat κ × CMat κ}
    (hX : X ∈ renyiEpigraph α) (hY : Y ∈ renyiEpigraph α) :
    supportFunction R (X.2 ⊗ₖ Y.2) ≤ supportFunction S X.2 * supportFunction T Y.2 :=
  supportFunction_kronecker_le_of_positivePolar_tensor S T R hSn hTn hRn
    hSc hTc hSp hTp hpolar
    (renyiEpigraph_second_posDef hX).posSemidef
    (renyiEpigraph_second_posDef hY).posSemidef

end Tensor

section PolarProgram

def renyiPolarValues (S T : Set (CMat ι)) (α : ℝ) : Set ℝ :=
  {x | ∃ Z ∈ renyiPolarFeasible T α, x = supportFunction S Z.2}

def renyiPolarValue (S T : Set (CMat ι)) (α : ℝ) : ℝ :=
  sInf (renyiPolarValues S T α)

theorem renyiPolarFeasible_nonempty (T : Set (CMat ι)) (hTc : IsCompact T) (α : ℝ) :
    (renyiPolarFeasible T α).Nonempty := by
  let Z : CMat ι × CMat ι := (1, matrixRpow 1 ((α - 1) / α))
  have hZ : Z ∈ renyiEpigraph α := by
    refine ⟨Matrix.PosDef.one, ?_⟩
    change (matrixRpow 1 ((α - 1) / α) - matrixRpow 1 ((α - 1) / α)).PosSemidef
    simpa only [sub_self] using (Matrix.PosSemidef.zero : (0 : CMat ι).PosSemidef)
  let b : ℝ := max 1 (supportFunction T Z.1)
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact ⟨(b⁻¹ • Z.1, Real.rpow b⁻¹ ((α - 1) / α) • Z.2),
    renyiPolarFeasible_normalize hTc hb hZ (le_max_right _ _)⟩

theorem renyiPolarValues_nonempty (S T : Set (CMat ι))
    (hTc : IsCompact T) (α : ℝ) : (renyiPolarValues S T α).Nonempty := by
  obtain ⟨Z, hZ⟩ := renyiPolarFeasible_nonempty T hTc α
  exact ⟨supportFunction S Z.2, Z, hZ, rfl⟩

theorem renyiPolarValues_bddBelow {S T : Set (CMat ι)}
    (hSn : S.Nonempty) (hSc : IsCompact S) (hSp : ∀ ρ ∈ S, ρ.PosSemidef)
    (α : ℝ) : BddBelow (renyiPolarValues S T α) := by
  refine ⟨0, ?_⟩
  rintro x ⟨Z, hZ, rfl⟩
  exact supportFunction_nonneg hSn hSc hSp (renyiEpigraph_second_posDef hZ.1).posSemidef

theorem renyiPolarValue_nonneg {S T : Set (CMat ι)}
    (hSn : S.Nonempty) (hSc : IsCompact S) (hSp : ∀ ρ ∈ S, ρ.PosSemidef)
    (hTc : IsCompact T) (α : ℝ) : 0 ≤ renyiPolarValue S T α := by
  apply le_csInf (renyiPolarValues_nonempty S T hTc α)
  rintro x ⟨Z, hZ, rfl⟩
  exact supportFunction_nonneg hSn hSc hSp (renyiEpigraph_second_posDef hZ.1).posSemidef

theorem renyiPolarValue_le {S T : Set (CMat ι)}
    (hSn : S.Nonempty) (hSc : IsCompact S) (hSp : ∀ ρ ∈ S, ρ.PosSemidef)
    {α : ℝ} {Z : CMat ι × CMat ι} (hZ : Z ∈ renyiPolarFeasible T α) :
    renyiPolarValue S T α ≤ supportFunction S Z.2 :=
  csInf_le (renyiPolarValues_bddBelow hSn hSc hSp α) ⟨Z, hZ, rfl⟩

theorem renyiEpigraph_support_scale {S T : Set (CMat ι)}
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (Z : CMat ι × CMat ι) {α a : ℝ} (ha : 0 < a) :
    α * supportFunction S (Real.rpow a ((α - 1) / α) • Z.2) +
        (1 - α) * supportFunction T (a • Z.1) =
      α * supportFunction S Z.2 * Real.rpow a ((α - 1) / α) +
        (1 - α) * supportFunction T Z.1 * a := by
  have he := supportFunction_smul (a := Real.rpow a ((α - 1) / α))
    hSn hSc Z.2 (Real.rpow_pos_of_pos ha _).le
  rw [he,
    supportFunction_smul hTn hTc _ ha.le]
  ring

section TensorValue

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 400000 in

theorem renyiPolarValue_tensor_le
    (S₁ B₁ : Set (CMat ι)) (S₂ B₂ : Set (CMat κ))
    (S₁₂ B₁₂ : Set (CMat (ι × κ)))
    (hS₁n : S₁.Nonempty) (hS₂n : S₂.Nonempty) (hS₁₂n : S₁₂.Nonempty)
    (hS₁c : IsCompact S₁) (hS₂c : IsCompact S₂) (hS₁₂c : IsCompact S₁₂)
    (hB₁c : IsCompact B₁) (hB₂c : IsCompact B₂)
    (hS₁p : ∀ ρ ∈ S₁, ρ.PosSemidef) (hS₂p : ∀ ρ ∈ S₂, ρ.PosSemidef)
    (hS₁₂p : ∀ ρ ∈ S₁₂, ρ.PosSemidef)
    (hSpolar : ∀ A ∈ positivePolar S₁, ∀ B ∈ positivePolar S₂,
      A ⊗ₖ B ∈ positivePolar S₁₂)
    (hBpolar : ∀ A ∈ positivePolar B₁, ∀ B ∈ positivePolar B₂,
      A ⊗ₖ B ∈ positivePolar B₁₂)
    (α : ℝ)
    (hpow : ∀ A : CMat ι, A.PosDef → ∀ B : CMat κ, B.PosDef →
      matrixRpow (A ⊗ₖ B) ((α - 1) / α) =
        matrixRpow A ((α - 1) / α) ⊗ₖ matrixRpow B ((α - 1) / α)) :
    renyiPolarValue S₁₂ B₁₂ α ≤
      renyiPolarValue S₁ B₁ α * renyiPolarValue S₂ B₂ α := by
  have hx0 := renyiPolarValue_nonneg hS₁n hS₁c hS₁p hB₁c α
  have hy0 := renyiPolarValue_nonneg hS₂n hS₂c hS₂p hB₂c α
  have heps (ε : ℝ) (hε : 0 < ε) :
      renyiPolarValue S₁₂ B₁₂ α ≤
        (renyiPolarValue S₁ B₁ α + ε) * (renyiPolarValue S₂ B₂ α + ε) := by
    obtain ⟨x, ⟨X, hX, rfl⟩, hx⟩ := exists_lt_of_csInf_lt
      (renyiPolarValues_nonempty S₁ B₁ hB₁c α)
      (show renyiPolarValue S₁ B₁ α < renyiPolarValue S₁ B₁ α + ε by linarith)
    obtain ⟨y, ⟨Y, hY, rfl⟩, hy⟩ := exists_lt_of_csInf_lt
      (renyiPolarValues_nonempty S₂ B₂ hB₂c α)
      (show renyiPolarValue S₂ B₂ α < renyiPolarValue S₂ B₂ α + ε by linarith)
    have hXY := renyiPolarFeasible_kronecker B₁ B₂ B₁₂ hBpolar hX hY
      (hpow X.1 hX.1.1 Y.1 hY.1.1)
    have hY0 := supportFunction_nonneg hS₂n hS₂c hS₂p
      (renyiEpigraph_second_posDef hY.1).posSemidef
    calc
      renyiPolarValue S₁₂ B₁₂ α ≤ supportFunction S₁₂ (X.2 ⊗ₖ Y.2) :=
        renyiPolarValue_le (S := S₁₂) (T := B₁₂) (α := α)
          (Z := (X.1 ⊗ₖ Y.1, X.2 ⊗ₖ Y.2)) hS₁₂n hS₁₂c hS₁₂p hXY
      _ ≤ supportFunction S₁ X.2 * supportFunction S₂ Y.2 :=
        renyi_tensor_support_bound S₁ S₂ S₁₂ hS₁n hS₂n hS₁₂n hS₁c hS₂c
          hS₁p hS₂p hSpolar hX.1 hY.1
      _ ≤ (renyiPolarValue S₁ B₁ α + ε) * (renyiPolarValue S₂ B₂ α + ε) :=
        mul_le_mul hx.le hy.le hY0 (by linarith)
  have hlim : Tendsto (fun ε : ℝ =>
      (renyiPolarValue S₁ B₁ α + ε) * (renyiPolarValue S₂ B₂ α + ε))
      (𝓝[>] 0) (𝓝 (renyiPolarValue S₁ B₁ α * renyiPolarValue S₂ B₂ α)) := by
    have hc : Continuous (fun ε : ℝ =>
      (renyiPolarValue S₁ B₁ α + ε) * (renyiPolarValue S₂ B₂ α + ε)) := by fun_prop
    simpa only [add_zero] using hc.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (by filter_upwards [self_mem_nhdsWithin] with ε hε; exact heps ε hε)

end TensorValue

section ScalarNormalization

open QuantumProver.MeasuredRenyiVariational

def renyiSupportInf (S T : Set (CMat ι)) (α : ℝ) : EReal :=
  ⨅ Z ∈ renyiEpigraph (ι := ι) α,
    ((α * supportFunction S Z.2 + (1 - α) * supportFunction T Z.1 : ℝ) : EReal)

theorem supportFunction_normalize_rpow {S : Set (CMat ι)}
    (hSn : S.Nonempty) (hSc : IsCompact S) (V : CMat ι)
    (hx : 0 ≤ supportFunction S V) {α b : ℝ} (hα : 0 < α) (hb : 0 < b) :
    (supportFunction S (Real.rpow b⁻¹ ((α - 1) / α) • V)) ^ α =
      (supportFunction S V) ^ α * b ^ (1 - α) := by
  have he := supportFunction_smul (a := Real.rpow b⁻¹ ((α - 1) / α))
    hSn hSc V (Real.rpow_pos_of_pos (inv_pos.mpr hb) _).le
  rw [he]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (Real.rpow_nonneg (inv_nonneg.mpr hb.le) _) hx]
  have hpow : ((b⁻¹) ^ ((α - 1) / α)) ^ α = b ^ (1 - α) := by
    rw [← Real.rpow_mul (inv_nonneg.mpr hb.le), ← Real.rpow_neg_eq_inv_rpow]
    congr 1
    field_simp [hα.ne']
    ring
  rw [hpow]
  ring

theorem renyiPolarValue_rpow_le_supportProduct {S T : Set (CMat ι)}
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (hSp : ∀ ρ ∈ S, ρ.PosSemidef) (hTp : ∀ σ ∈ T, σ.PosSemidef)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {Z : CMat ι × CMat ι}
    (hZ : Z ∈ renyiEpigraph α) :
    (renyiPolarValue S T α) ^ α ≤
      (supportFunction S Z.2) ^ α * (supportFunction T Z.1) ^ (1 - α) := by
  have hx := supportFunction_nonneg hSn hSc hSp
    (renyiEpigraph_second_posDef hZ).posSemidef
  have hy := supportFunction_nonneg hTn hTc hTp hZ.1.posSemidef
  have hp := renyiPolarValue_nonneg hSn hSc hSp hTc α
  have heps (ε : ℝ) (hε : 0 < ε) :
      (renyiPolarValue S T α) ^ α ≤
        (supportFunction S Z.2) ^ α * (supportFunction T Z.1 + ε) ^ (1 - α) := by
    have hb : 0 < supportFunction T Z.1 + ε := by linarith
    have hf := renyiPolarFeasible_normalize hTc hb hZ (by linarith)
    have hv := renyiPolarValue_le (S := S) (T := T) (α := α)
      (Z := ((supportFunction T Z.1 + ε)⁻¹ • Z.1,
        Real.rpow (supportFunction T Z.1 + ε)⁻¹ ((α - 1) / α) • Z.2)) hSn hSc hSp hf
    exact (Real.rpow_le_rpow hp hv hα.le).trans_eq
      (supportFunction_normalize_rpow hSn hSc Z.2 hx hα hb)
  have hc : Continuous (fun ε : ℝ =>
      (supportFunction S Z.2) ^ α * (supportFunction T Z.1 + ε) ^ (1 - α)) :=
    continuous_const.mul ((Real.continuous_rpow_const (sub_nonneg.mpr hα1.le)).comp
      (continuous_const.add continuous_id))
  have ht := hc.continuousAt.tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa only [add_zero] using ht)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact heps ε hε

theorem renyiSupportInf_le_supportProduct {S T : Set (CMat ι)}
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (hSp : ∀ ρ ∈ S, ρ.PosSemidef) (hTp : ∀ σ ∈ T, σ.PosSemidef)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {Z : CMat ι × CMat ι}
    (hZ : Z ∈ renyiEpigraph α) :
    renyiSupportInf S T α ≤
      (((supportFunction S Z.2) ^ α * (supportFunction T Z.1) ^ (1 - α) : ℝ) : EReal) := by
  have hx := supportFunction_nonneg hSn hSc hSp
    (renyiEpigraph_second_posDef hZ).posSemidef
  have hy := supportFunction_nonneg hTn hTc hTp hZ.1.posSemidef
  have hscale (a : ℝ) (ha : 0 < a) : renyiSupportInf S T α ≤
      (scalarObjective α (supportFunction S Z.2) (supportFunction T Z.1) a : EReal) := by
    have hs := renyiEpigraph_scale ha hZ
    have hi : renyiSupportInf S T α ≤
        ((α * supportFunction S (Real.rpow a ((α - 1) / α) • Z.2) +
          (1 - α) * supportFunction T (a • Z.1) : ℝ) : EReal) :=
      iInf_le_of_le (a • Z.1, Real.rpow a ((α - 1) / α) • Z.2)
        (iInf_le_of_le hs le_rfl)
    rw [renyiEpigraph_support_scale hSn hTn hSc hTc Z ha] at hi
    simpa only [scalarObjective, renyiExponent, Real.rpow_eq_pow] using hi
  have ht := epsilonTest_objective_tendsto hα hα1 hx hy
  have hte := continuous_coe_real_ereal.continuousAt.tendsto.comp ht
  change renyiSupportInf S T α ≤ (scalarTrace α (supportFunction S Z.2) (supportFunction T Z.1) : EReal)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hte
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hscale _ (epsilonTest_pos hx hy hε)

theorem renyi_support_polar_formula {S T : Set (CMat ι)}
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (hSp : ∀ ρ ∈ S, ρ.PosSemidef) (hTp : ∀ σ ∈ T, σ.PosSemidef)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    renyiSupportInf S T α = (((renyiPolarValue S T α) ^ α : ℝ) : EReal) := by
  have hp := renyiPolarValue_nonneg hSn hSc hSp hTc α
  apply le_antisymm
  · have heps (ε : ℝ) (hε : 0 < ε) : renyiSupportInf S T α ≤
        (((renyiPolarValue S T α + ε) ^ α : ℝ) : EReal) := by
      obtain ⟨x, ⟨Z, hZ, rfl⟩, hxlt⟩ := exists_lt_of_csInf_lt
        (renyiPolarValues_nonempty S T hTc α)
        (show renyiPolarValue S T α < renyiPolarValue S T α + ε by linarith)
      have hx := supportFunction_nonneg hSn hSc hSp
        (renyiEpigraph_second_posDef hZ.1).posSemidef
      have hy := supportFunction_nonneg hTn hTc hTp hZ.1.1.posSemidef
      have hy1 := (positivePolar_iff_supportFunction_le hTn hTc).mp hZ.2
      have hyPow : (supportFunction T Z.1) ^ (1 - α) ≤ 1 := by
        simpa only [Real.one_rpow] using
          Real.rpow_le_rpow hy hy1.2 (sub_nonneg.mpr hα1.le)
      calc
        renyiSupportInf S T α ≤
            (((supportFunction S Z.2) ^ α * (supportFunction T Z.1) ^ (1 - α) : ℝ) : EReal) :=
          renyiSupportInf_le_supportProduct hSn hTn hSc hTc hSp hTp hα hα1 hZ.1
        _ ≤ (((supportFunction S Z.2) ^ α : ℝ) : EReal) := by
          apply EReal.coe_le_coe_iff.mpr
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hyPow (Real.rpow_nonneg hx α)
        _ ≤ (((renyiPolarValue S T α + ε) ^ α : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (Real.rpow_le_rpow hx hxlt.le hα.le)
    have hc : Continuous (fun ε : ℝ => ((renyiPolarValue S T α + ε) ^ α : ℝ)) :=
      (Real.continuous_rpow_const hα.le).comp (continuous_const.add continuous_id)
    have ht := continuous_coe_real_ereal.continuousAt.tendsto.comp
      (hc.continuousAt.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left))
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa only [add_zero] using ht)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact heps ε hε
  · apply le_iInf₂
    intro Z hZ
    have hx := supportFunction_nonneg hSn hSc hSp
      (renyiEpigraph_second_posDef hZ).posSemidef
    have hy := supportFunction_nonneg hTn hTc hTp hZ.1.posSemidef
    have hgeom := scalarTrace_le_objective hα hα1 hx hy zero_lt_one
    simp only [scalarTrace, scalarObjective, Real.one_rpow, mul_one] at hgeom
    exact EReal.coe_le_coe_iff.mpr
      ((renyiPolarValue_rpow_le_supportProduct hSn hTn hSc hTc hSp hTp hα hα1 hZ).trans hgeom)

end ScalarNormalization

section MatrixMeasuredTrace

open QuantumProver.MeasuredRenyiVariational

theorem variationalRenyiTrace_eq_iInf_epigraph {ρ σ : CMat ι}
    (hρ : ρ.PosSemidef) {α : ℝ} (hα : 0 ≤ α) :
    variationalRenyiTrace α ρ σ =
      ⨅ Z ∈ renyiEpigraph (ι := ι) α, (renyiLinearObjective α (ρ, σ) Z : EReal) := by
  apply le_antisymm
  · apply le_iInf₂
    intro Z hZ
    calc
      variationalRenyiTrace α ρ σ ≤ (matrixObjective α ρ σ Z.1 : EReal) :=
        sInf_le ⟨Z.1, hZ.1, rfl⟩
      _ ≤ (renyiLinearObjective α (ρ, σ) Z : EReal) := by
        apply EReal.coe_le_coe_iff.mpr
        change α * tracePair ρ (matrixRpow Z.1 ((α - 1) / α)) +
            (1 - α) * tracePair σ Z.1 ≤
          α * tracePair ρ Z.2 + (1 - α) * tracePair σ Z.1
        exact add_le_add
          (mul_le_mul_of_nonneg_left (tracePair_mono_of_loewner hρ hZ.2) hα) le_rfl
  · apply le_sInf
    rintro z ⟨W, hW, rfl⟩
    have hZ : (W, matrixRpow W ((α - 1) / α)) ∈ renyiEpigraph α := by
      refine ⟨hW, ?_⟩
      change (matrixRpow W ((α - 1) / α) - matrixRpow W ((α - 1) / α)).PosSemidef
      simpa only [sub_self] using (Matrix.PosSemidef.zero : (0 : CMat ι).PosSemidef)
    have hi : (⨅ Z ∈ renyiEpigraph (ι := ι) α,
        (renyiLinearObjective α (ρ, σ) Z : EReal)) ≤
        (renyiLinearObjective α (ρ, σ) (W, matrixRpow W ((α - 1) / α)) : EReal) :=
      iInf_le_of_le (W, matrixRpow W ((α - 1) / α)) (iInf_le_of_le hZ le_rfl)
    simpa only [renyiLinearObjective, matrixObjective, renyiExponent] using hi

theorem measuredRenyiTrace_sup_eq_polar {S T : Set (CMat ι)}
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (hSv : Convex ℝ S) (hTv : Convex ℝ T)
    (hSp : ∀ ρ ∈ S, ρ.PosSemidef) (hTp : ∀ σ ∈ T, σ.PosSemidef)
    {α : ℝ} (hα : (1 / 2 : ℝ) ≤ α) (hα1 : α < 1) :
    (⨆ X ∈ S ×ˢ T, measuredRenyiTrace α X.1 X.2) =
      (((renyiPolarValue S T α) ^ α : ℝ) : EReal) := by
  have he : (⨆ X ∈ S ×ˢ T, measuredRenyiTrace α X.1 X.2) =
      (⨆ X ∈ S ×ˢ T, ⨅ Z ∈ renyiEpigraph (ι := ι) α,
        (renyiLinearObjective α X Z : EReal)) := by
    apply iSup_congr
    intro X
    apply iSup_congr
    intro hX
    rw [measuredRenyiTrace_variational (hSp X.1 hX.1) (hTp X.2 hX.2) hα hα1,
      variationalRenyiTrace_eq_iInf_epigraph (hSp X.1 hX.1) (by linarith : 0 ≤ α)]
  rw [he, renyi_support_minimax S T hSn hTn hSc hTc hSv hTv hα hα1]
  exact renyi_support_polar_formula hSn hTn hSc hTc hSp hTp (by linarith) hα1

def matrixSetMeasuredDivergence (S T : Set (CMat ι)) (α : ℝ) : EReal :=
  sInf {z | ∃ ρ ∈ S, ∃ σ ∈ T, z = measuredDivergence ρ σ α}

theorem matrixSetMeasuredDivergence_eq_log_polar {S T : Set (CMat ι)}
    (hSn : S.Nonempty) (hTn : T.Nonempty) (hSc : IsCompact S) (hTc : IsCompact T)
    (hSv : Convex ℝ S) (hTv : Convex ℝ T)
    (hSs : ∀ ρ ∈ S, IsState ρ) (hTp : ∀ σ ∈ T, σ.PosSemidef)
    {α : ℝ} (hα : (1 / 2 : ℝ) ≤ α) (hα1 : α < 1) :
    matrixSetMeasuredDivergence S T α =
      logRenyiBits α ((renyiPolarValue S T α) ^ α) := by
  have hα0 : 0 < α := by linarith
  have hSp : ∀ ρ ∈ S, ρ.PosSemidef := fun ρ hρ => (hSs ρ hρ).1
  let q : ℝ := (renyiPolarValue S T α) ^ α
  have hq0 : 0 ≤ q := Real.rpow_nonneg (renyiPolarValue_nonneg hSn hSc hSp hTc α) α
  have hsup : (⨆ X ∈ S ×ˢ T, measuredRenyiTrace α X.1 X.2) = (q : EReal) :=
    measuredRenyiTrace_sup_eq_polar hSn hTn hSc hTc hSv hTv hSp hTp hα hα1
  have hfinite (X : CMat ι × CMat ι) (hX : X ∈ S ×ˢ T) :
      0 ≤ measuredRenyiTrace α X.1 X.2 ∧ measuredRenyiTrace α X.1 X.2 ≠ ⊤ ∧
        measuredRenyiTrace α X.1 X.2 ≠ ⊥ := by
    rw [measuredRenyiTrace_variational (hSp X.1 hX.1) (hTp X.2 hX.2) hα hα1]
    exact variationalRenyiTrace_finite_nonneg (hSs X.1 hX.1) (hTp X.2 hX.2) hα0 hα1
  apply le_antisymm
  · by_cases hqz : q = 0
    · change matrixSetMeasuredDivergence S T α ≤ logRenyiBits α q
      simp only [logRenyiBits, hqz, ite_true, le_top]
    by_contra hn
    obtain ⟨b, hl, hb⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
    have hqp : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
    let threshold := Real.exp (b * (α - 1) * Real.log 2)
    have hsmall : threshold < q := by
      change logRenyiBits α q < (b : EReal) at hl
      rw [logRenyiBits, if_neg hqz] at hl
      have hd := (div_lt_iff_of_neg (sub_neg.mpr hα1)).mp (EReal.coe_lt_coe_iff.mp hl)
      have hlog : b * (α - 1) * Real.log 2 < Real.log q :=
        (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp hd
      simpa only [Real.exp_log hqp] using Real.exp_lt_exp.mpr hlog
    have hstrict : (threshold : EReal) <
        (⨆ X ∈ S ×ˢ T, measuredRenyiTrace α X.1 X.2) := by
      rw [hsup]
      exact EReal.coe_lt_coe_iff.mpr hsmall
    have hex : ∃ X ∈ S ×ˢ T, (threshold : EReal) < measuredRenyiTrace α X.1 X.2 := by
      by_contra hnone
      have hbound : (⨆ X ∈ S ×ˢ T, measuredRenyiTrace α X.1 X.2) ≤ (threshold : EReal) := by
        apply iSup₂_le
        intro X hX
        exact le_of_not_gt (fun hh => hnone ⟨X, hX, hh⟩)
      exact not_le_of_gt hstrict hbound
    obtain ⟨X, hX, hlarge⟩ := hex
    obtain ⟨_, hXt, hXb⟩ := hfinite X hX
    let x := (measuredRenyiTrace α X.1 X.2).toReal
    have hxid : (x : EReal) = measuredRenyiTrace α X.1 X.2 := EReal.coe_toReal hXt hXb
    have htx : threshold < x := by
      rw [← hxid] at hlarge
      exact EReal.coe_lt_coe_iff.mp hlarge
    have hxp : 0 < x := (Real.exp_pos _).trans htx
    have hlog : b * (α - 1) * Real.log 2 < Real.log x := by
      have hh := Real.log_lt_log (Real.exp_pos _) htx
      simpa only [threshold, Real.log_exp] using hh
    have hdiv : logTwo x / (α - 1) < b := by
      apply (div_lt_iff_of_neg (sub_neg.mpr hα1)).mpr
      exact (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog
    have hd : measuredDivergence X.1 X.2 α < (b : EReal) := by
      rw [measuredDivergence_eq_log_measuredRenyiTrace (hSs X.1 hX.1) (hTp X.2 hX.2) hα hα1]
      change logRenyiBits α x < (b : EReal)
      rw [logRenyiBits, if_neg hxp.ne']
      exact EReal.coe_lt_coe_iff.mpr hdiv
    have hi : matrixSetMeasuredDivergence S T α ≤ measuredDivergence X.1 X.2 α :=
      sInf_le ⟨X.1, hX.1, X.2, hX.2, rfl⟩
    exact not_lt_of_ge hi (hd.trans hb)
  · apply le_sInf
    rintro z ⟨ρ, hρ, σ, hσ, rfl⟩
    let X : CMat ι × CMat ι := (ρ, σ)
    have hX : X ∈ S ×ˢ T := ⟨hρ, hσ⟩
    obtain ⟨hX0, hXt, hXb⟩ := hfinite X hX
    have hxid : ((measuredRenyiTrace α ρ σ).toReal : EReal) = measuredRenyiTrace α ρ σ :=
      EReal.coe_toReal hXt hXb
    have hx0 : 0 ≤ (measuredRenyiTrace α ρ σ).toReal := by
      rw [← hxid] at hX0
      exact EReal.coe_le_coe_iff.mp hX0
    have hxq : (measuredRenyiTrace α ρ σ).toReal ≤ q := by
      apply EReal.coe_le_coe_iff.mp
      rw [hxid, ← hsup]
      exact le_iSup₂_of_le X hX le_rfl
    rw [measuredDivergence_eq_log_measuredRenyiTrace (hSs ρ hρ) (hTp σ hσ) hα hα1]
    exact logRenyiBits_antitone hα1 hx0 hxq

theorem logRenyiBits_mul {α x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    logRenyiBits α (x * y) = logRenyiBits α x + logRenyiBits α y := by
  by_cases hx0 : x = 0
  · by_cases hy0 : y = 0 <;> simp [logRenyiBits, hx0, hy0]
  by_cases hy0 : y = 0
  · simp [logRenyiBits, hx0, hy0]
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  simp only [logRenyiBits, hx0, hy0, mul_ne_zero hx0 hy0, ite_false]
  rw [← EReal.coe_add]
  apply congrArg (fun z : ℝ => (z : EReal))
  rw [Testing.logTwo_mul_pos hxp hyp]
  ring

section MatrixTensor

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem matrixSetMeasuredDivergence_tensor_superadditive
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
      A ⊗ₖ B ∈ positivePolar B₁₂)
    {α : ℝ} (hα : (1 / 2 : ℝ) ≤ α) (hα1 : α < 1)
    (hpow : ∀ A : CMat ι, A.PosDef → ∀ B : CMat κ, B.PosDef →
      matrixRpow (A ⊗ₖ B) ((α - 1) / α) =
        matrixRpow A ((α - 1) / α) ⊗ₖ matrixRpow B ((α - 1) / α)) :
    matrixSetMeasuredDivergence S₁ B₁ α + matrixSetMeasuredDivergence S₂ B₂ α ≤
      matrixSetMeasuredDivergence S₁₂ B₁₂ α := by
  have hS₁p : ∀ ρ ∈ S₁, ρ.PosSemidef := fun ρ hρ => (hS₁s ρ hρ).1
  have hS₂p : ∀ ρ ∈ S₂, ρ.PosSemidef := fun ρ hρ => (hS₂s ρ hρ).1
  have hS₁₂p : ∀ ρ ∈ S₁₂, ρ.PosSemidef := fun ρ hρ => (hS₁₂s ρ hρ).1
  have hp₁ := renyiPolarValue_nonneg hS₁n hS₁c hS₁p hB₁c α
  have hp₂ := renyiPolarValue_nonneg hS₂n hS₂c hS₂p hB₂c α
  have hp₁₂ := renyiPolarValue_nonneg hS₁₂n hS₁₂c hS₁₂p hB₁₂c α
  have ht := renyiPolarValue_tensor_le S₁ B₁ S₂ B₂ S₁₂ B₁₂ hS₁n hS₂n hS₁₂n
    hS₁c hS₂c hS₁₂c hB₁c hB₂c hS₁p hS₂p hS₁₂p hSpolar hBpolar α hpow
  have htrace := Real.rpow_le_rpow hp₁₂ ht (by linarith : 0 ≤ α)
  rw [Real.mul_rpow hp₁ hp₂] at htrace
  rw [matrixSetMeasuredDivergence_eq_log_polar hS₁n hB₁n hS₁c hB₁c hS₁v hB₁v hS₁s hB₁p hα hα1,
    matrixSetMeasuredDivergence_eq_log_polar hS₂n hB₂n hS₂c hB₂c hS₂v hB₂v hS₂s hB₂p hα hα1,
    matrixSetMeasuredDivergence_eq_log_polar hS₁₂n hB₁₂n hS₁₂c hB₁₂c hS₁₂v hB₁₂v hS₁₂s hB₁₂p hα hα1,
    ← logRenyiBits_mul (Real.rpow_nonneg hp₁ α) (Real.rpow_nonneg hp₂ α)]
  exact logRenyiBits_antitone hα1 (Real.rpow_nonneg hp₁₂ α) htrace

end MatrixTensor
end MatrixMeasuredTrace
end PolarProgram

end QuantumProver.Equipartition.FiniteModel.PolarTensor
