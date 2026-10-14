import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.BlockComparison
import QuantumProver.LinearAlgebra.SandwichedDPI.Interpolation

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

open QuantumProver.SuperchannelDiscrimination.KrausCompletion

section MatrixDPI

variable {I O Z : Type*} [Fintype I] [Fintype O] [Fintype Z]
  [DecidableEq I] [DecidableEq O]

omit [Fintype O] [DecidableEq I] [DecidableEq O] in

theorem krausSumB_eq_krausAction (K : Z → Matrix O I ℂ) (ρ : Matrix I I ℂ) :
    krausSumB K ρ = krausAction K ρ := rfl

theorem sandwichedTrace_krausSumB_le (K : Z → Matrix O I ℂ)
    (hK : ∑ z, (K z)ᴴ * K z = 1) {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 1 < α) :
    sandwichedTrace α (krausSumB K ρ) (krausSumB K σ) ≤ sandwichedTrace α ρ σ :=
  QuantumProver.SandwichedDPI.sandwichedTrace_krausAction_le K hK hρ hσ hs hα

theorem sandwichedDivergence_krausSumB_le (K : Z → Matrix O I ℂ)
    (hK : ∑ z, (K z)ᴴ * K z = 1) {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {α : ℝ} (hα : 1 < α) :
    sandwichedDivergence α (krausSumB K ρ) (krausSumB K σ) ≤
      sandwichedDivergence α ρ σ :=
  QuantumProver.SandwichedDPI.sandwichedDivergence_krausAction_le K hK hρ hσ hα

end MatrixDPI

theorem sandwichedEntanglement_local_kraus_le {a b ao bo : ℕ}
    {Z : Type*} [Fintype Z]
    (K : Z → Matrix (Fin ao) (Fin a) ℂ)
    (L : Z → Matrix (Fin bo) (Fin b) ℂ)
    (hKL : ∑ z, (K z ⊗ₖ L z)ᴴ * (K z ⊗ₖ L z) = 1)
    {ρ : BipartiteMatrix a b} (hρ : ρ.PosSemidef) {α : ℝ} (hα : 1 < α) :
    sandwichedEntanglement α ao bo (krausSumB (fun z => K z ⊗ₖ L z) ρ) ≤
      sandwichedEntanglement α a b ρ := by
  unfold sandwichedEntanglement
  apply le_sInf
  rintro x ⟨σ, ⟨hσ, hsep⟩, rfl⟩
  have htrace : (∑ z, (K z ⊗ₖ L z) * σ * (K z ⊗ₖ L z)ᴴ).trace = 1 := by
    rw [krausSum_trace _ hKL, hσ.2]
  have houtsep := hsep.local_kraus_of_trace K L htrace
  exact (sandwichedEntanglement_le_comparison
      (krausSumB (fun z => K z ⊗ₖ L z) ρ) houtsep.isDensity houtsep α).trans
    (sandwichedDivergence_krausSumB_le _ hKL hρ hσ.1 hα)

theorem sandwichedEntanglement_alice_instrument_le {a b ao k : ℕ}
    (K : KrausInstrument a ao k) {ρ : BipartiteMatrix a b}
    (hρ : ρ.PosSemidef) {α : ℝ} (hα : 1 < α) :
    sandwichedEntanglement α ao b
      (∑ z, aliceOperator (b := b) (K.operator z) * ρ *
        (aliceOperator (b := b) (K.operator z))ᴴ) ≤
      sandwichedEntanglement α a b ρ :=
  sandwichedEntanglement_local_kraus_le K.operator (fun _ => 1)
    (aliceOperator_gram (b := b) K) hρ hα

theorem sandwichedEntanglement_bob_instrument_le {a b bo k : ℕ}
    (K : KrausInstrument b bo k) {ρ : BipartiteMatrix a b}
    (hρ : ρ.PosSemidef) {α : ℝ} (hα : 1 < α) :
    sandwichedEntanglement α a bo
      (∑ z, bobOperator (a := a) (K.operator z) * ρ *
        (bobOperator (a := a) (K.operator z))ᴴ) ≤
      sandwichedEntanglement α a b ρ :=
  sandwichedEntanglement_local_kraus_le (fun _ => 1) K.operator
    (bobOperator_gram (a := a) K) hρ hα

section MatrixTransferDPI

variable {I O Z A B : Type*} [Fintype I] [Fintype O] [Fintype Z]
  [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq O]
  [DecidableEq A] [DecidableEq B]

theorem labTransferKraus_complete (K : Z → Matrix O I ℂ)
    (hK : ∑ z, (K z)ᴴ * K z = 1) :
    ∑ z, (labTransferKraus (A := A) (B := B) K z)ᴴ *
      labTransferKraus (A := A) (B := B) K z = 1 := by
  apply krausSumB_complete_of_trace
  intro ρ
  change (labTransferOutput K ρ).trace = ρ.trace
  rw [labTransferOutput_eq_reference, TensorPower.trace_submatrix_equiv,
    krausSumB_trace_preserving _ (referenceKrausB_complete K hK (A × B)),
    TensorPower.trace_submatrix_equiv]

theorem labTransferOutput_sandwichedTrace_le (K : Z → Matrix O I ℂ)
    (hK : ∑ z, (K z)ᴴ * K z = 1)
    {ρ σ : Matrix ((A × I) × B) ((A × I) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 1 < α) :
    sandwichedTrace α (labTransferOutput K ρ) (labTransferOutput K σ) ≤
      sandwichedTrace α ρ σ :=
  sandwichedTrace_krausSumB_le _ (labTransferKraus_complete K hK) hρ hσ hs hα

theorem labTransferOutput_sandwichedDivergence_le (K : Z → Matrix O I ℂ)
    (hK : ∑ z, (K z)ᴴ * K z = 1)
    {ρ σ : Matrix ((A × I) × B) ((A × I) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {α : ℝ} (hα : 1 < α) :
    sandwichedDivergence α (labTransferOutput K ρ) (labTransferOutput K σ) ≤
      sandwichedDivergence α ρ σ :=
  sandwichedDivergence_krausSumB_le _ (labTransferKraus_complete K hK) hρ hσ hα

end MatrixTransferDPI

theorem fixedWeight_divergence_le_input_divergence (n w r : ℕ)
    (hrw : r ≤ w) (hrn : r ≤ n)
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {ρ σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hρ : IsDensity ρ) (hσ : SepPositive σ) (htrace : σ.trace = 1)
    (hs : SupportLE ρ σ) {α : ℝ} (hα : 1 < α) :
    sandwichedDivergence α (labTransferOutput (lossKrausB n w r) ρ)
      (labTransferOutput (measurePhaseKrausB n w r) σ) ≤
        sandwichedDivergence α ρ σ + (logTwo (phaseComparisonConstantB n w r) : EReal) := by
  have hρN := labTransferOutput_isDensity (lossKrausB n w r) (lossKrausB_complete n w r hrw) hρ
  have hσN := labTransferOutput_isDensity (lossKrausB n w r) (lossKrausB_complete n w r hrw)
    (show IsDensity σ from ⟨hσ.posSemidef, htrace⟩)
  have hσS := (labTransferOutput_phase_isSeparable n w r hrn A B hσ htrace).isDensity
  have hsN := labTransferOutput_supportLE (lossKrausB n w r) hρ.1 hσ.posSemidef hs
  have hc := phaseComparisonConstantB_pos n w r hrw hrn
  have horder := labTransferOutput_loss_phase_domination n w r hrw hrn A B hσ.posSemidef
  exact (sandwichedDivergence_comparison_order hρN hσN hσS hsN hc horder hα).trans
    (_root_.add_le_add_left (labTransferOutput_sandwichedDivergence_le (lossKrausB n w r)
      (lossKrausB_complete n w r hrw) hρ.1 hσ.posSemidef hα) _)

theorem fixedWeight_entanglement_le_input_divergence (n w r : ℕ)
    (hrw : r ≤ w) (hrn : r ≤ n)
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {ρ σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hρ : IsDensity ρ) (hσ : SepPositive σ) (htrace : σ.trace = 1)
    (hs : SupportLE ρ σ) {α : ℝ} (hα : 1 < α) :
    sandwichedEntanglement α (Fintype.card A) (Fintype.card (Finset (Fin n) × B))
      (labTransferOutput (lossKrausB n w r) ρ) ≤
        sandwichedDivergence α ρ σ + (logTwo (phaseComparisonConstantB n w r) : EReal) :=
  (sandwichedEntanglement_le_comparison (labTransferOutput (lossKrausB n w r) ρ)
    (labTransferOutput_phase_isSeparable n w r hrn A B hσ htrace).isDensity
    (labTransferOutput_phase_isSeparable n w r hrn A B hσ htrace) α).trans
      (fixedWeight_divergence_le_input_divergence n w r hrw hrn A B hρ hσ htrace hs hα)

theorem fixedWeight_sandwichedTrace_phase_le_input (n w r : ℕ)
    (hrw : r ≤ w) (hrn : r ≤ n)
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {ρ σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hρ : IsDensity ρ) (hσ : SepPositive σ) (htrace : σ.trace = 1)
    (hs : SupportLE ρ σ) {α : ℝ} (hα : 1 < α) :
    sandwichedTrace α (labTransferOutput (lossKrausB n w r) ρ)
      (labTransferOutput (measurePhaseKrausB n w r) σ) ≤
        (phaseComparisonConstantB n w r) ^ (α - 1) * sandwichedTrace α ρ σ :=
  (fixedWeight_sandwichedTrace_phase_le_loss n w r hrw hrn A B hρ hσ htrace hs hα).trans
    (mul_le_mul_of_nonneg_left (labTransferOutput_sandwichedTrace_le (lossKrausB n w r)
      (lossKrausB_complete n w r hrw) hρ.1 hσ.posSemidef hs hα)
        (Real.rpow_nonneg (phaseComparisonConstantB_pos n w r hrw hrn).le _))

theorem FiniteProtocol.exists_output_kraus {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) :
    ∃ (k : ℕ) (K : Fin k → Matrix (Fin af × Fin bf) (Fin a × Fin b) ℂ),
      ∀ ρ : BipartiteMatrix a b, P.output ρ = krausSumB K ρ := by
  classical
  induction P with
  | done a b =>
      refine ⟨1, fun _ => 1, ?_⟩
      intro ρ
      simp [FiniteProtocol.output, krausSumB]
  | @alice a b ao af bf k M next ih =>
      choose c C hC using ih
      let Z := Σ z : Fin k, Fin (c z)
      let K : Z → Matrix (Fin af × Fin bf) (Fin a × Fin b) ℂ :=
        fun z => C z.1 z.2 * aliceOperator (b := b) (M.operator z.1)
      refine ⟨Fintype.card Z, fun j => K (finiteIndexB Z j), ?_⟩
      intro ρ
      rw [krausSumB_outcome_equiv (finiteIndexB Z) K ρ]
      simp only [FiniteProtocol.output, hC]
      simp_rw [← krausSumB_rectangular_precompose]
      simp only [krausSumB, K, Z, Fintype.sum_sigma]
  | @bob a b bo af bf k M next ih =>
      choose c C hC using ih
      let Z := Σ z : Fin k, Fin (c z)
      let K : Z → Matrix (Fin af × Fin bf) (Fin a × Fin b) ℂ :=
        fun z => C z.1 z.2 * bobOperator (a := a) (M.operator z.1)
      refine ⟨Fintype.card Z, fun j => K (finiteIndexB Z j), ?_⟩
      intro ρ
      rw [krausSumB_outcome_equiv (finiteIndexB Z) K ρ]
      simp only [FiniteProtocol.output, hC]
      simp_rw [← krausSumB_rectangular_precompose]
      simp only [krausSumB, K, Z, Fintype.sum_sigma]
  | @call a b af bf next ih =>
      obtain ⟨k, K, hK⟩ := ih
      let Z := Fin k × Qubit
      let C : Z → Matrix (Fin af × Fin bf) (Fin (2 * a) × Fin b) ℂ :=
        fun z => K z.1 * callOperator p a b z.2
      refine ⟨Fintype.card Z, fun j => C (finiteIndexB Z j), ?_⟩
      intro ρ
      rw [FiniteProtocol.output, hK]
      change krausSumB K (krausSumB (callOperator p a b) ρ) = _
      rw [krausSumB_compose, krausSumB_outcome_equiv (finiteIndexB Z) C ρ]

theorem FiniteProtocol.exists_complete_output_kraus {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) :
    ∃ (k : ℕ) (K : Fin k → Matrix (Fin af × Fin bf) (Fin a × Fin b) ℂ),
      (∑ z, (K z)ᴴ * K z = 1) ∧
      ∀ ρ : BipartiteMatrix a b, P.output ρ = krausSumB K ρ := by
  obtain ⟨k, K, hK⟩ := P.exists_output_kraus
  refine ⟨k, K, ?_, hK⟩
  apply krausSumB_complete_of_trace
  intro ρ
  rw [← hK ρ]
  exact P.output_trace hp0 hp1 ρ

theorem FiniteProtocol.sandwichedDivergence_output_le {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) {ρ σ : BipartiteMatrix a b}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {α : ℝ} (hα : 1 < α) :
    sandwichedDivergence α (P.output ρ) (P.output σ) ≤ sandwichedDivergence α ρ σ := by
  obtain ⟨k, K, hcomplete, hK⟩ := P.exists_complete_output_kraus hp0 hp1
  rw [hK ρ, hK σ]
  exact sandwichedDivergence_krausSumB_le K hcomplete hρ hσ hα

theorem FiniteProtocol.sandwichedEntanglement_output_le_of_calls_zero {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) (hc : P.calls = 0)
    {ρ : BipartiteMatrix a b} (hρ : ρ.PosSemidef) {α : ℝ} (hα : 1 < α) :
    sandwichedEntanglement α af bf (P.output ρ) ≤ sandwichedEntanglement α a b ρ := by
  unfold sandwichedEntanglement
  apply le_sInf
  rintro x ⟨σ, ⟨hσ, hsep⟩, rfl⟩
  have houtsep := P.output_isSeparable_of_calls_zero hp0 hp1 hc hsep
  exact (sandwichedEntanglement_le_comparison (P.output ρ) houtsep.isDensity houtsep α).trans
    (P.sandwichedDivergence_output_le hp0 hp1 hρ hσ.1 hα)

section UnnormalizedSector

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem fixedWeight_sandwichedTrace_phase_le_input_of_posSemidef
    (n w r : ℕ) (hrw : r ≤ w) (hrn : r ≤ n)
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    {ρ σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 1 < α) :
    sandwichedTrace α (labTransferOutput (lossKrausB n w r) ρ)
      (labTransferOutput (measurePhaseKrausB n w r) σ) ≤
        (phaseComparisonConstantB n w r) ^ (α - 1) * sandwichedTrace α ρ σ := by
  have hc := phaseComparisonConstantB_pos n w r hrw hrn
  have hρN : (labTransferOutput (lossKrausB n w r) ρ).PosSemidef := krausSumB_posSemidef _ hρ
  have hσN : (labTransferOutput (lossKrausB n w r) σ).PosSemidef := krausSumB_posSemidef _ hσ
  have hσS : (labTransferOutput (measurePhaseKrausB n w r) σ).PosSemidef := krausSumB_posSemidef _ hσ
  have hsN := labTransferOutput_supportLE (lossKrausB n w r) hρ hσ hs
  have horder := labTransferOutput_loss_phase_domination n w r hrw hrn A B hσ
  have hBout : 0 < Fintype.card (Finset (Fin n) × B) := by
    rw [Fintype.card_prod]
    exact Nat.mul_pos Fintype.card_pos hB
  have hQ := sandwichedTrace_antitone_comparison_of_support hρN hσN (hσS.smul hc.le)
    horder hsN hA hBout hα.le
  rw [sandwichedTrace_smul_comparison hρN hσS hc hα.le] at hQ
  have hcancel : (phaseComparisonConstantB n w r) ^ (α - 1) *
      (phaseComparisonConstantB n w r) ^ (1 - α) = 1 := by
    rw [← Real.rpow_add hc]
    simp
  have hscale := mul_le_mul_of_nonneg_left hQ
    (Real.rpow_nonneg hc.le (α - 1))
  have hcomp : sandwichedTrace α (labTransferOutput (lossKrausB n w r) ρ)
      (labTransferOutput (measurePhaseKrausB n w r) σ) ≤
      (phaseComparisonConstantB n w r) ^ (α - 1) *
        sandwichedTrace α (labTransferOutput (lossKrausB n w r) ρ)
          (labTransferOutput (lossKrausB n w r) σ) := by
    simpa only [← mul_assoc, hcancel, one_mul] using hscale
  exact hcomp.trans (mul_le_mul_of_nonneg_left
    (labTransferOutput_sandwichedTrace_le (lossKrausB n w r)
      (lossKrausB_complete n w r hrw) hρ hσ hs hα)
        (Real.rpow_nonneg hc.le (α - 1)))

end UnnormalizedSector

theorem labTransferOutput_phase_sepPositive (n w r : ℕ)
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hσ : SepPositive σ) : SepPositive (labTransferOutput (measurePhaseKrausB n w r) σ) := by
  let χ := phaseInputVectorB n w
  let v := phaseOutputVectorB n r
  have hcone := (hσ.measurePrepareTransfer χ v).submatrix_local_equiv
    (finiteIndexB A) (finiteIndexB (Finset (Fin n) × B))
  rw [measurePrepareTransfer_output_eq_reference] at hcone
  have hfamily : measurePhaseKrausB n w r =
      fun z => QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus (χ z) (v z) :=
    funext (measurePhaseKrausB_rankOne n w r)
  rw [hfamily, labTransferOutput_eq_reference]
  simpa only [Matrix.submatrix_submatrix, labTransferOutputEquiv, Equiv.coe_trans] using hcone

theorem labFlagComparator_sepPositive {f g a b : ℕ}
    (t : Fin f × Fin g → ℝ) (σ : Fin f × Fin g → BipartiteMatrix a b)
    (ht : ∀ z, 0 ≤ t z) (hσ : ∀ z, SepPositive (σ z)) :
    SepPositive (labFlagComparator t σ) := by
  apply SepPositive.sum
  intro z
  rw [Complex.coe_smul]
  exact ((hσ z).local_conjugation (appendFlagKraus z.1) (appendFlagKraus z.2)).smul (ht z)

theorem labFlagComparator_trace {f g a b : ℕ}
    (t : Fin f × Fin g → ℝ) (σ : Fin f × Fin g → BipartiteMatrix a b) :
    (labFlagComparator t σ).trace = ∑ z, (t z : ℂ) * (σ z).trace := by
  rw [labFlagComparator, Matrix.trace_sum]
  simp only [Matrix.trace_smul, labFlagBlock_trace, smul_eq_mul]

theorem labFlagComparator_isSeparable_of_trace {f g a b : ℕ}
    (t : Fin f × Fin g → ℝ) (σ : Fin f × Fin g → BipartiteMatrix a b)
    (ht : ∀ z, 0 ≤ t z) (hσ : ∀ z, SepPositive (σ z))
    (htrace : ∑ z, (t z : ℂ) * (σ z).trace = 1) :
    IsSeparable (f * a) (g * b) (labFlagComparator t σ) :=
  (labFlagComparator_sepPositive t σ ht hσ).isSeparable
    ((labFlagComparator_trace t σ).trans htrace)

theorem labFlagComparator_sandwichedTrace_same_weights {f g a b : ℕ}
    (t : Fin f × Fin g → ℝ) (ρ σ : Fin f × Fin g → BipartiteMatrix a b)
    (ht : ∀ z, 0 ≤ t z) (hρ : ∀ z, (ρ z).PosSemidef) (hσ : ∀ z, (σ z).PosSemidef)
    {α : ℝ} (hα : 1 ≤ α) :
    sandwichedTrace α (labFlagComparator t ρ) (labFlagComparator t σ) =
      ∑ z, t z * sandwichedTrace α (ρ z) (σ z) := by
  simpa only [mul_one, Real.one_rpow] using
    labFlagComparator_sandwichedTrace_matched t (fun _ => 1) (fun _ => 1) ρ σ ht
      (fun _ => zero_le_one) (fun _ => zero_le_one) (fun _ h => (one_ne_zero h).elim)
      hρ hσ hα

theorem physical_phase_moment_eq_survivorMoment (n w : ℕ) (p s : ℝ) :
    (∑ r : Fin (w + 1), physicalPhaseLawB p w r *
      (phaseComparisonConstantB n w r.val) ^ s) = Scalar.survivorMoment n w p s := by
  unfold physicalPhaseLawB Scalar.survivorMoment
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => physicalSurvivorProbabilityB p w r *
    (phaseComparisonConstantB n w r) ^ s) (w + 1)]
  simp only [Scalar.survivorTerm, Scalar.binomialTerm, physicalSurvivorProbabilityB,
    phaseComparisonConstantB, sub_sub_cancel]

theorem fixedWeight_flagged_sandwichedTrace_moment (n w : ℕ) (hwn : w ≤ n)
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    {ρ σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {p α : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hα : 1 < α) :
    sandwichedTrace α
      (labFlagComparator (fun z : Fin 1 × Fin (w + 1) => physicalPhaseLawB p w z.2)
        (fun z => labTransferOutput (lossKrausB n w z.2.val) ρ))
      (labFlagComparator (fun z : Fin 1 × Fin (w + 1) => physicalPhaseLawB p w z.2)
        (fun z => labTransferOutput (measurePhaseKrausB n w z.2.val) σ)) ≤
      Scalar.survivorMoment n w p (α - 1) * sandwichedTrace α ρ σ := by
  rw [labFlagComparator_sandwichedTrace_same_weights
    (fun z : Fin 1 × Fin (w + 1) => physicalPhaseLawB p w z.2)
    (fun z => labTransferOutput (lossKrausB n w z.2.val) ρ)
    (fun z => labTransferOutput (measurePhaseKrausB n w z.2.val) σ)
    (fun z => physicalPhaseLawB_nonneg p hp0 hp1 w z.2)
    (fun z => krausSumB_posSemidef _ hρ) (fun z => krausSumB_posSemidef _ hσ) hα.le]
  calc
    _ ≤ ∑ z : Fin 1 × Fin (w + 1), physicalPhaseLawB p w z.2 *
        ((phaseComparisonConstantB n w z.2.val) ^ (α - 1) * sandwichedTrace α ρ σ) := by
      apply Finset.sum_le_sum
      intro z _
      have hrw : z.2.val ≤ w := Nat.le_of_lt_succ z.2.isLt
      exact mul_le_mul_of_nonneg_left
        (fixedWeight_sandwichedTrace_phase_le_input_of_posSemidef n w z.2.val hrw
          (hrw.trans hwn) hA hB hρ hσ hs hα)
        (physicalPhaseLawB_nonneg p hp0 hp1 w z.2)
    _ = _ := by
      simp only [Fintype.sum_prod_type, Fin.sum_univ_one, ← mul_assoc, ← Finset.sum_mul]
      rw [physical_phase_moment_eq_survivorMoment]

end QuantumProver.AmplitudeDamping.FiniteModel
