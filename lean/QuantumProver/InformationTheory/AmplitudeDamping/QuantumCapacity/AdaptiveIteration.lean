import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.AdaptiveConverse
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.BlockChannels

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

theorem matrixPhysicalBlockOutput_supportLE_phaseA (n : ℕ) (p : ℝ) (a b : ℕ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : BipartiteMatrix (doubleDimB n a) b}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ) :
    SupportLE (matrixPhysicalBlockOutput n p a b ρ) (matrixPhaseBlockOutput n p a b σ) := by
  let eI := matrixBlockInputEquiv n a b
  let eO := matrixBlockOutputEquiv n a b
  let eF := (finiteIndexB (Fin a)).prodCongr (finiteIndexB (Finset (Fin n) × Fin b))
  have h := physicalOutput_supportLE_recoveredPhaseA n p (Fin a) (Fin b) hp0 hp1
    (hρ.submatrix eI.symm) (hσ.submatrix eI.symm) (hs.submatrix_equiv eI.symm)
  rw [labTransferOutput_eq_transferLabC, recoveredPhaseOutputC_eq_krausSum] at h
  have hRaw := h.submatrix_equiv eF.symm
  have hCancel (M : Matrix (Fin a × (Finset (Fin n) × Fin b))
      (Fin a × (Finset (Fin n) × Fin b)) ℂ) :
      (M.submatrix eF eF).submatrix eF.symm eF.symm = M := by
    ext x y
    simp
  rw [hCancel, hCancel] at hRaw
  rw [matrixPhysicalBlockOutput_eq_raw, matrixPhaseBlockOutput_eq_raw]
  exact hRaw.submatrix_equiv eO

theorem matrixPhysicalBlockOutput_sandwichedTrace_phase_leA
    (n : ℕ) (p : ℝ) (a b : ℕ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : BipartiteMatrix (doubleDimB n a) b}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 1 < α) :
    sandwichedTrace α (matrixPhysicalBlockOutput n p a b ρ) (matrixPhaseBlockOutput n p a b σ) ≤
      physicalBlockQFactorA n p α * sandwichedTrace α ρ σ := by
  by_cases ha : 0 < a
  · by_cases hb : 0 < b
    · let eI := matrixBlockInputEquiv n a b
      have hρr := hρ.submatrix eI.symm
      have hσr := hσ.submatrix eI.symm
      have hN := krausSumB_posSemidef
        (transferLabKrausC (A := Fin a) (B := Fin b) (tensorDampingKrausB n p)) hρr
      have hT := krausSumB_posSemidef (recoveredPhaseLabKrausC n p (Fin a) (Fin b)) hσr
      have h := physicalOutput_sandwichedTrace_recoveredPhase_le n p (Fin a) (Fin b)
        (by simpa using ha) (by simpa using hb) hp0 hp1 hρr hσr
        (hs.submatrix_equiv eI.symm) hα
      rw [labTransferOutput_eq_transferLabC, recoveredPhaseOutputC_eq_krausSum,
        TensorPower.sandwichedTrace_submatrix_equiv hN hT,
        TensorPower.sandwichedTrace_submatrix_equiv hρ hσ] at h
      rw [matrixPhysicalBlockOutput_eq_raw, matrixPhaseBlockOutput_eq_raw,
        TensorPower.sandwichedTrace_submatrix_equiv hN hT]
      exact h
    · have hb0 : b = 0 := Nat.eq_zero_of_not_pos hb
      subst b
      have hzero : ρ = 0 := by
        ext x y
        exact Fin.elim0 x.2
      rw [hzero]
      simp [matrixPhysicalBlockOutput, krausSumB, sandwichedTrace_zero_input _
        (by linarith : 0 < α)]
  · have ha0 : a = 0 := Nat.eq_zero_of_not_pos ha
    subst a
    have hzero : ρ = 0 := by
      ext x y
      exact Fin.elim0 ((matrixBlockInputAliceEquiv n 0) x.1).1
    rw [hzero]
    simp [matrixPhysicalBlockOutput, krausSumB, sandwichedTrace_zero_input _
      (by linarith : 0 < α)]

def FiniteBlockProtocolB.phaseOutput {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (σ : BipartiteMatrix a b) :
    BipartiteMatrix af bf :=
  match P with
  | .done _ _ => σ
  | .alice K next => ∑ j, (next j).phaseOutput
      (aliceOperator (b := b) (K.operator j) * σ *
        (aliceOperator (b := b) (K.operator j))ᴴ)
  | .bob K next => ∑ j, (next j).phaseOutput
      (bobOperator (a := a) (K.operator j) * σ *
        (bobOperator (a := a) (K.operator j))ᴴ)
  | .blockCall (a := a₀) (b := b₀) next =>
      next.phaseOutput (matrixPhaseBlockOutput n p a₀ b₀ σ)

theorem FiniteBlockProtocolB.output_posSemidefA {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) {ρ : BipartiteMatrix a b}
    (hρ : ρ.PosSemidef) : (P.output ρ).PosSemidef := by
  rw [← P.toMatrix_output]
  exact P.represented_toMatrix.output_posSemidef ρ hρ

theorem FiniteBlockProtocolB.output_traceA {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : BipartiteMatrix a b) : (P.output ρ).trace = ρ.trace := by
  rw [← P.toMatrix_output]
  exact P.represented_toMatrix.output_trace hp0 hp1 ρ

theorem FiniteBlockProtocolB.phaseOutput_posSemidef {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) {σ : BipartiteMatrix a b}
    (hσ : σ.PosSemidef) : (P.phaseOutput σ).PosSemidef := by
  induction P with
  | done a b => exact hσ
  | alice K next ih =>
    exact Matrix.posSemidef_sum _ fun j _ =>
      ih j (hσ.mul_mul_conjTranspose_same _)
  | bob K next ih =>
    exact Matrix.posSemidef_sum _ fun j _ =>
      ih j (hσ.mul_mul_conjTranspose_same _)
  | blockCall next ih =>
    exact ih (matrixPhaseBlockOutput_posSemidef _ _ _ _ hσ)

theorem FiniteBlockProtocolB.phaseOutput_trace {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : BipartiteMatrix a b) : (P.phaseOutput σ).trace = σ.trace := by
  induction P with
  | done a b => rfl
  | alice K next ih =>
    rw [FiniteBlockProtocolB.phaseOutput, Matrix.trace_sum]
    simp_rw [ih]
    simpa only [Matrix.trace_sum] using krausSum_trace _ (aliceOperator_gram K) σ
  | bob K next ih =>
    rw [FiniteBlockProtocolB.phaseOutput, Matrix.trace_sum]
    simp_rw [ih]
    simpa only [Matrix.trace_sum] using krausSum_trace _ (bobOperator_gram K) σ
  | blockCall next ih =>
    rw [FiniteBlockProtocolB.phaseOutput, ih,
      matrixPhaseBlockOutput_trace _ _ _ _ hp0 hp1]

theorem FiniteBlockProtocolB.phaseOutput_sepPositive {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) {σ : BipartiteMatrix a b}
    (hσ : SepPositive σ) : SepPositive (P.phaseOutput σ) := by
  induction P with
  | done a b => exact hσ
  | alice K next ih =>
    exact SepPositive.sum _ fun j => ih j (hσ.local_conjugation (K.operator j) 1)
  | bob K next ih =>
    exact SepPositive.sum _ fun j => ih j (hσ.local_conjugation 1 (K.operator j))
  | blockCall next ih => exact ih (matrixPhaseBlockOutput_sepPositive _ _ _ _ hσ)

theorem FiniteBlockProtocolB.phaseOutput_isDensity {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : BipartiteMatrix a b} (hσ : IsDensity σ) : IsDensity (P.phaseOutput σ) :=
  ⟨P.phaseOutput_posSemidef hσ.1, (P.phaseOutput_trace hp0 hp1 σ).trans hσ.2⟩

theorem FiniteBlockProtocolB.phaseOutput_isSeparable {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {σ : BipartiteMatrix a b} (hσ : IsSeparable a b σ) :
    IsSeparable af bf (P.phaseOutput σ) :=
  (P.phaseOutput_sepPositive hσ.sepPositive).isSeparable
    ((P.phaseOutput_trace hp0 hp1 σ).trans hσ.isDensity.2)

theorem FiniteBlockProtocolB.output_supportLE_phase {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : BipartiteMatrix a b} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : SupportLE ρ σ) : SupportLE (P.output ρ) (P.phaseOutput σ) := by
  induction P with
  | done a b => exact hs
  | alice K next ih =>
    apply supportLE_sumA
    · intro j; exact (next j).output_posSemidefA (hρ.mul_mul_conjTranspose_same _)
    · intro j; exact (next j).phaseOutput_posSemidef (hσ.mul_mul_conjTranspose_same _)
    · intro j
      exact ih j (hρ.mul_mul_conjTranspose_same _) (hσ.mul_mul_conjTranspose_same _)
        (supportLE_conjugationA _ hρ hσ hs)
  | bob K next ih =>
    apply supportLE_sumA
    · intro j; exact (next j).output_posSemidefA (hρ.mul_mul_conjTranspose_same _)
    · intro j; exact (next j).phaseOutput_posSemidef (hσ.mul_mul_conjTranspose_same _)
    · intro j
      exact ih j (hρ.mul_mul_conjTranspose_same _) (hσ.mul_mul_conjTranspose_same _)
        (supportLE_conjugationA _ hρ hσ hs)
  | blockCall next ih =>
    rw [FiniteBlockProtocolB.output, FiniteBlockProtocolB.phaseOutput,
      sequentialCallsKrausB_output_eq_matrix_block]
    exact ih (matrixPhysicalBlockOutput_posSemidef _ _ _ _ hρ)
      (matrixPhaseBlockOutput_posSemidef _ _ _ _ hσ)
      (matrixPhysicalBlockOutput_supportLE_phaseA _ _ _ _ hp0 hp1 hρ hσ hs)

theorem FiniteBlockProtocolB.sandwichedTrace_output_phase_le {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ρ σ : BipartiteMatrix a b} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hs : SupportLE ρ σ) {α : ℝ} (hα : 1 < α) :
    sandwichedTrace α (P.output ρ) (P.phaseOutput σ) ≤
      physicalBlockQFactorA n p α ^ P.calls * sandwichedTrace α ρ σ := by
  have hF : 1 ≤ physicalBlockQFactorA n p α := one_le_physicalBlockQFactorA n p (by linarith)
  have hF0 : 0 ≤ physicalBlockQFactorA n p α := zero_le_one.trans hF
  induction P with
  | done a b => simp [FiniteBlockProtocolB.output, FiniteBlockProtocolB.phaseOutput,
      FiniteBlockProtocolB.calls]
  | @alice a b ao af bf k K next ih =>
    let R := fun j => aliceOperator (b := b) (K.operator j)
    have hRρ (j : Fin k) := hρ.mul_mul_conjTranspose_same (R j)
    have hRσ (j : Fin k) := hσ.mul_mul_conjTranspose_same (R j)
    have hRs (j : Fin k) := supportLE_conjugationA (R j) hρ hσ hs
    have hBranch := sandwichedTrace_branch_sum_le R (aliceOperator_gram K) hρ hσ hs hα
    change sandwichedTrace α (∑ j, (next j).output (R j * ρ * (R j)ᴴ))
      (∑ j, (next j).phaseOutput (R j * σ * (R j)ᴴ)) ≤ _
    calc
      _ ≤ ∑ j, sandwichedTrace α ((next j).output (R j * ρ * (R j)ᴴ))
          ((next j).phaseOutput (R j * σ * (R j)ᴴ)) :=
        sandwichedTrace_sum_leA _ _
          (fun j => (next j).output_posSemidefA (hRρ j))
          (fun j => (next j).phaseOutput_posSemidef (hRσ j))
          (fun j => (next j).output_supportLE_phase hp0 hp1 (hRρ j) (hRσ j) (hRs j)) hα
      _ ≤ ∑ j, physicalBlockQFactorA n p α ^ (Finset.univ.sup fun j => (next j).calls) *
          sandwichedTrace α (R j * ρ * (R j)ᴴ) (R j * σ * (R j)ᴴ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (ih j (hRρ j) (hRσ j) (hRs j)).trans
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hF (Finset.le_sup (f := fun j => (next j).calls) hj))
            (sandwichedTrace_nonneg (hRρ j) α))
      _ = physicalBlockQFactorA n p α ^ (Finset.univ.sup fun j => (next j).calls) *
          (∑ j, sandwichedTrace α (R j * ρ * (R j)ᴴ) (R j * σ * (R j)ᴴ)) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hBranch (pow_nonneg hF0 _)
  | @bob a b bo af bf k K next ih =>
    let R := fun j => bobOperator (a := a) (K.operator j)
    have hRρ (j : Fin k) := hρ.mul_mul_conjTranspose_same (R j)
    have hRσ (j : Fin k) := hσ.mul_mul_conjTranspose_same (R j)
    have hRs (j : Fin k) := supportLE_conjugationA (R j) hρ hσ hs
    have hBranch := sandwichedTrace_branch_sum_le R (bobOperator_gram K) hρ hσ hs hα
    change sandwichedTrace α (∑ j, (next j).output (R j * ρ * (R j)ᴴ))
      (∑ j, (next j).phaseOutput (R j * σ * (R j)ᴴ)) ≤ _
    calc
      _ ≤ ∑ j, sandwichedTrace α ((next j).output (R j * ρ * (R j)ᴴ))
          ((next j).phaseOutput (R j * σ * (R j)ᴴ)) :=
        sandwichedTrace_sum_leA _ _
          (fun j => (next j).output_posSemidefA (hRρ j))
          (fun j => (next j).phaseOutput_posSemidef (hRσ j))
          (fun j => (next j).output_supportLE_phase hp0 hp1 (hRρ j) (hRσ j) (hRs j)) hα
      _ ≤ ∑ j, physicalBlockQFactorA n p α ^ (Finset.univ.sup fun j => (next j).calls) *
          sandwichedTrace α (R j * ρ * (R j)ᴴ) (R j * σ * (R j)ᴴ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (ih j (hRρ j) (hRσ j) (hRs j)).trans
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hF (Finset.le_sup (f := fun j => (next j).calls) hj))
            (sandwichedTrace_nonneg (hRρ j) α))
      _ = physicalBlockQFactorA n p α ^ (Finset.univ.sup fun j => (next j).calls) *
          (∑ j, sandwichedTrace α (R j * ρ * (R j)ᴴ) (R j * σ * (R j)ᴴ)) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hBranch (pow_nonneg hF0 _)
  | @blockCall a b af bf next ih =>
    rw [FiniteBlockProtocolB.output, FiniteBlockProtocolB.phaseOutput,
      sequentialCallsKrausB_output_eq_matrix_block, FiniteBlockProtocolB.calls]
    calc
      _ ≤ physicalBlockQFactorA n p α ^ next.calls *
          sandwichedTrace α (matrixPhysicalBlockOutput n p a b ρ) (matrixPhaseBlockOutput n p a b σ) :=
        ih (matrixPhysicalBlockOutput_posSemidef _ _ _ _ hρ)
          (matrixPhaseBlockOutput_posSemidef _ _ _ _ hσ)
          (matrixPhysicalBlockOutput_supportLE_phaseA _ _ _ _ hp0 hp1 hρ hσ hs)
      _ ≤ physicalBlockQFactorA n p α ^ next.calls *
          (physicalBlockQFactorA n p α * sandwichedTrace α ρ σ) :=
        mul_le_mul_of_nonneg_left
          (matrixPhysicalBlockOutput_sandwichedTrace_phase_leA n p a b hp0 hp1 hρ hσ hs hα)
          (pow_nonneg hF0 _)
      _ = _ := by rw [pow_succ]; ring

theorem physicalBlockLogChargeA_nonneg (n : ℕ) (p : ℝ) {α : ℝ} (hα : 1 < α) :
    0 ≤ physicalBlockLogChargeA n p (α - 1) := by
  rw [← log_physicalBlockQFactorA n p hα]
  exact div_nonneg
    (div_nonneg (Real.log_nonneg (one_le_physicalBlockQFactorA n p (by linarith)))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
    (sub_pos.mpr hα).le

theorem FiniteBlockProtocolB.sandwichedDivergence_output_phase_le
    {p : ℝ} {n a b af bf : ℕ} (P : FiniteBlockProtocolB p n a b af bf)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {ρ σ : BipartiteMatrix a b}
    (hρ : IsDensity ρ) (hσ : IsDensity σ) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 1 < α) :
    sandwichedDivergence α (P.output ρ) (P.phaseOutput σ) ≤ sandwichedDivergence α ρ σ +
      (((P.calls : ℝ) * physicalBlockLogChargeA n p (α - 1) : ℝ) : EReal) := by
  have hF : 0 < physicalBlockQFactorA n p α :=
    zero_lt_one.trans_le (one_le_physicalBlockQFactorA n p (by linarith))
  have h := sandwichedDivergence_le_of_Q_factorA hρ hσ
    ⟨P.output_posSemidefA hρ.1, (P.output_traceA hp0 hp1 ρ).trans hρ.2⟩
    (P.phaseOutput_isDensity hp0 hp1 hσ) hs
    (P.output_supportLE_phase hp0 hp1 hρ.1 hσ.1 hs) hα (pow_pos hF P.calls)
    (P.sandwichedTrace_output_phase_le hp0 hp1 hρ.1 hσ.1 hs hα)
  have hlog : logTwo (physicalBlockQFactorA n p α ^ P.calls) / (α - 1) =
      (P.calls : ℝ) * physicalBlockLogChargeA n p (α - 1) := by
    calc
      _ = (P.calls : ℝ) * (logTwo (physicalBlockQFactorA n p α) / (α - 1)) := by
        unfold logTwo
        rw [Real.log_pow]
        ring
      _ = _ := by rw [log_physicalBlockQFactorA n p hα]
  rwa [hlog] at h

theorem FiniteBlockProtocolB.sandwichedEntanglement_output_le_of_le
    {p : ℝ} {n a b af bf : ℕ} (P : FiniteBlockProtocolB p n a b af bf)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {ρ : BipartiteMatrix a b} (hρ : IsDensity ρ)
    {α e : ℝ} (hα : 1 < α) (hE : sandwichedEntanglement α a b ρ ≤ (e : EReal)) :
    sandwichedEntanglement α af bf (P.output ρ) ≤
      ((e + (P.calls : ℝ) * physicalBlockLogChargeA n p (α - 1) : ℝ) : EReal) := by
  apply EReal.le_of_forall_lt_iff_le.mp
  intro z hz
  have hzR : e + (P.calls : ℝ) * physicalBlockLogChargeA n p (α - 1) < z :=
    EReal.coe_lt_coe_iff.mp hz
  let ε := z - (e + (P.calls : ℝ) * physicalBlockLogChargeA n p (α - 1))
  have hε : 0 < ε := sub_pos.mpr hzR
  have hElt : sandwichedEntanglement α a b ρ < ((e + ε : ℝ) : EReal) :=
    hE.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨σ, hσ, hsep, hs, hD⟩ := exists_separable_comparison_divergence_lt ρ hElt
  calc
    _ ≤ sandwichedDivergence α (P.output ρ) (P.phaseOutput σ) :=
      sandwichedEntanglement_le_comparison _ (P.phaseOutput_isDensity hp0 hp1 hσ)
        (P.phaseOutput_isSeparable hp0 hp1 hsep) α
    _ ≤ sandwichedDivergence α ρ σ +
        (((P.calls : ℝ) * physicalBlockLogChargeA n p (α - 1) : ℝ) : EReal) :=
      P.sandwichedDivergence_output_phase_le hp0 hp1 hρ hσ hs hα
    _ ≤ ((e + ε : ℝ) : EReal) +
        (((P.calls : ℝ) * physicalBlockLogChargeA n p (α - 1) : ℝ) : EReal) :=
      _root_.add_le_add hD.le le_rfl
    _ = (z : EReal) := by
      rw [← EReal.coe_add]
      congr 1
      dsimp only [ε]
      ring

theorem FiniteBlockProtocolB.sandwichedEntanglement_output_le_of_calls_le
    {p : ℝ} {n a b af bf m : ℕ} (P : FiniteBlockProtocolB p n a b af bf)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hP : P.calls ≤ m)
    {ρ : BipartiteMatrix a b} (hρ : IsDensity ρ) {α e : ℝ} (hα : 1 < α)
    (hE : sandwichedEntanglement α a b ρ ≤ (e : EReal)) :
    sandwichedEntanglement α af bf (P.output ρ) ≤
      ((e + (m : ℝ) * physicalBlockLogChargeA n p (α - 1) : ℝ) : EReal) := by
  apply (P.sandwichedEntanglement_output_le_of_le hp0 hp1 hρ hα hE).trans
  apply EReal.coe_le_coe_iff.mpr
  exact _root_.add_le_add le_rfl
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hP) (physicalBlockLogChargeA_nonneg n p hα))

theorem tendsto_record_overheadA :
    Filter.Tendsto (fun n : ℕ => logTwo ((n : ℝ) + 2) / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) := by
  have hraw : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2) / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    convert (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 (by norm_num)).comp
      ((tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
        Filter.atTop Filter.atTop).comp (Filter.tendsto_add_atTop_nat 2)) using 1
    ext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat, pow_one, one_mul]
    congr 1
    ring
  convert hraw.div_const (Real.log 2) using 1
  · ext n
    unfold logTwo
    ring
  · simp

theorem FiniteProtocol.bell_log_bound_of_resourceA {p s e : ℝ} {a b d m : ℕ}
    (P : FiniteProtocol p a b d d) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hP : P.calls ≤ m)
    {ρ : BipartiteMatrix a b} (hρ : IsDensity ρ)
    (hE : sandwichedEntanglement (1 + s) a b ρ ≤ (e : EReal))
    (hG : 0 < bellOverlap d (P.output ρ)) :
    logTwo (d : ℝ) + ((1 + s) / s) * logTwo (bellOverlap d (P.output ρ)) ≤
      e + (m : ℝ) * converseBudget p s := by
  have hα : 1 < 1 + s := by linarith
  have hout := P.output_isDensity hp0 hp1 hρ
  have hEach (n : ℕ) :
      logTwo (d : ℝ) + ((1 + s) / s) * logTwo (bellOverlap d (P.output ρ)) ≤
        e + (m : ℝ) * converseBudget p s +
          ((m : ℝ) * ((2 + s) / s)) * (logTwo ((n : ℝ) + 2) / ((n : ℝ) + 1)) := by
    obtain ⟨R, hRC, _, _, hRO⟩ := P.exists_independent_lanesB m hP n
    have hEin := lanePowerMatrixB_entanglement_le hρ hα hE n
    have hEr := R.sandwichedEntanglement_output_le_of_calls_le hp0 hp1 hRC
      (lanePowerMatrixB_isDensity hρ n) hα hEin
    rw [hRO ρ, show (1 + s) - 1 = s by ring] at hEr
    have hlane := lanePowerMatrixB_isDensity hout n
    have hGt : 0 < bellOverlap (lanePowerDimB n d) (lanePowerMatrixB (P.output ρ) n) := by
      rw [lanePowerMatrixB_bellOverlap hout n]
      exact pow_pos hG _
    have hLower := bell_sandwichedEntanglement_log_bound hlane.laboratory_dimensions_pos.1
      hlane.1 hGt hα
    have hlogG : logTwo ((bellOverlap d (P.output ρ)) ^ (n + 1)) =
        ((n + 1 : ℕ) : ℝ) * logTwo (bellOverlap d (P.output ρ)) := by
      unfold logTwo
      rw [Real.log_pow]
      ring
    rw [lanePowerMatrixB_bellOverlap hout n, logTwo_lanePowerDimB, hlogG,
      show (1 + s) - 1 = s by ring] at hLower
    have hScalar := EReal.coe_le_coe_iff.mp (hLower.trans hEr)
    have hc := physicalBlockLogChargeA_le_full_parameters (n + 1)
      (Nat.zero_lt_succ n) hp0 hp1 hs0 hs1
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcM := mul_le_mul_of_nonneg_left hc hm
    push_cast at hScalar hcM
    have hScaled : ((n : ℝ) + 1) *
        (logTwo (d : ℝ) + ((1 + s) / s) * logTwo (bellOverlap d (P.output ρ))) ≤
        ((n : ℝ) + 1) * (e + (m : ℝ) * converseBudget p s) +
          ((m : ℝ) * ((2 + s) / s)) * logTwo ((n : ℝ) + 2) := by
      have hArg : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
      rw [hArg] at hcM
      nlinarith [hScalar, hcM]
    apply (mul_le_mul_iff_of_pos_left hn).mp
    convert hScaled using 1
    field_simp [hn.ne']
  have hLimit : Filter.Tendsto (fun n : ℕ => e + (m : ℝ) * converseBudget p s +
      ((m : ℝ) * ((2 + s) / s)) * (logTwo ((n : ℝ) + 2) / ((n : ℝ) + 1)))
      Filter.atTop (nhds (e + (m : ℝ) * converseBudget p s)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_record_overheadA.const_mul ((m : ℝ) * ((2 + s) / s)))
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hLimit (Filter.Eventually.of_forall hEach)

theorem FiniteProtocol.bellConverse_of_resourceA {p s e : ℝ} {a b d m : ℕ}
    (P : FiniteProtocol p a b d d) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hd : 2 ≤ d) (hP : P.calls ≤ m)
    {ρ : BipartiteMatrix a b} (hρ : IsDensity ρ)
    (hE : sandwichedEntanglement (1 + s) a b ρ ≤ (e : EReal)) :
    bellOverlap d (P.output ρ) ≤ bellConverseBound p s m d e := by
  have hout := P.output_isDensity hp0 hp1 hρ
  have hd0 : 0 < d := by omega
  unfold bellConverseBound
  refine le_min (bellOverlap_le_one hd0 hout) ?_
  by_cases hG : 0 < bellOverlap d (P.output ρ)
  · have hLog := P.bell_log_bound_of_resourceA hp0 hp1 hs0 hs1 hP hρ hE hG
    have hα : 0 < 1 + s := by linarith
    have hTest : logTwo (bellOverlap d (P.output ρ)) ≤
        -(s / (1 + s)) * (logTwo (d : ℝ) - e - (m : ℝ) * converseBudget p s) := by
      apply (mul_le_mul_iff_of_pos_left (div_pos hα hs0)).mp
      have hCancel : ((1 + s) / s) *
          (-(s / (1 + s)) * (logTwo (d : ℝ) - e - (m : ℝ) * converseBudget p s)) =
          e + (m : ℝ) * converseBudget p s - logTwo (d : ℝ) := by
        field_simp [hs0.ne', hα.ne']
        ring
      rw [hCancel]
      linarith
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hExp := Real.exp_le_exp.mpr ((div_le_iff₀ h2).mp hTest)
    rw [Real.exp_log hG] at hExp
    simpa only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm] using hExp
  · exact (le_of_not_gt hG).trans (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)

theorem finiteAdaptiveStrongConverse : FiniteAdaptiveStrongConverse := by
  apply finiteAdaptiveStrongConverse_iff_finite.mpr
  intro p s m d e hp0 hp1 hs0 hs1 hd σ hσ
  obtain ⟨a, b, ρ, P, hρ, hP, hE, rfl⟩ := hσ
  exact P.bellConverse_of_resourceA hp0 hp1 hs0 hs1 hd hP hρ hE

end QuantumProver.AmplitudeDamping.FiniteModel
