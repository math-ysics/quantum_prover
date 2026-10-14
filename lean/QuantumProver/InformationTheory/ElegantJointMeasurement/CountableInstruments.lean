import Mathlib
import QuantumProver.InformationTheory.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix
open scoped Matrix.Norms.L2Operator

namespace QuantumProver.ElegantJointMeasurement.CountableInstruments

noncomputable section

set_option maxHeartbeats 600000

variable {σ : Type*} {input out : ℕ}

def residual (K : σ → Matrix (Fin out) (Fin input) ℂ) (S : Finset σ) :
    Matrix (Fin input) (Fin input) ℂ :=
  1 - ∑ s ∈ S, (K s)ᴴ * K s

theorem residual_posSemidef (K : σ → Matrix (Fin out) (Fin input) ℂ)
    (hs : Summable (fun s => (K s)ᴴ * K s))
    (hcomplete : (∑' s, (K s)ᴴ * K s) = 1) (S : Finset σ) :
    (residual K S).PosSemidef := by
  have hle := hs.sum_le_tsum S
    (fun s _ => (Matrix.posSemidef_conjTranspose_mul_self (K s)).nonneg)
  rw [hcomplete] at hle
  exact hle

def abortKraus (R : Matrix (Fin input) (Fin input) ℂ) (b0 : Fin out)
    (t : Fin input) : Matrix (Fin out) (Fin input) ℂ :=
  fun a i => if a = b0 then (CFC.sqrt R) t i else 0

theorem abortKraus_gram (R : Matrix (Fin input) (Fin input) ℂ)
    (b0 : Fin out) (t : Fin input) :
    (abortKraus R b0 t)ᴴ * abortKraus R b0 t =
      Matrix.vecMulVec (fun i => conj ((CFC.sqrt R) t i))
        (fun j => (CFC.sqrt R) t j) := by
  ext i j
  simp [abortKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply]

theorem abortKraus_sum_gram (R : Matrix (Fin input) (Fin input) ℂ)
    (hR : R.PosSemidef) (b0 : Fin out) :
    (∑ t, (abortKraus R b0 t)ᴴ * abortKraus R b0 t) = R := by
  have hfactor : (CFC.sqrt R)ᴴ * CFC.sqrt R = R := by
    have hstar : (CFC.sqrt R)ᴴ = CFC.sqrt R :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg R)).isHermitian
    rw [hstar, ← pow_two]
    exact CFC.sq_sqrt R hR.nonneg
  calc
    (∑ t, (abortKraus R b0 t)ᴴ * abortKraus R b0 t) = (CFC.sqrt R)ᴴ * CFC.sqrt R := by
      ext i j
      simp only [Matrix.sum_apply, abortKraus_gram, Matrix.vecMulVec_apply,
        Matrix.mul_apply, Matrix.conjTranspose_apply]
      rfl
    _ = R := hfactor

def cutoffKraus (K : σ → Matrix (Fin out) (Fin input) ℂ) (S : Finset σ)
    (b0 : Fin out) : (S ⊕ Fin input) → Matrix (Fin out) (Fin input) ℂ
  | .inl s => K s
  | .inr t => abortKraus (residual K S) b0 t

@[simp] theorem cutoffKraus_retained (K : σ → Matrix (Fin out) (Fin input) ℂ)
    (S : Finset σ) (b0 : Fin out) (s : S) :
    cutoffKraus K S b0 (.inl s) = K s := rfl

theorem cutoffKraus_complete (K : σ → Matrix (Fin out) (Fin input) ℂ)
    (hs : Summable (fun s => (K s)ᴴ * K s))
    (hcomplete : (∑' s, (K s)ᴴ * K s) = 1) (S : Finset σ) (b0 : Fin out) :
    (∑ q, (cutoffKraus K S b0 q)ᴴ * cutoffKraus K S b0 q) = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [cutoffKraus]
  rw [show (∑ s : S, (K s)ᴴ * K s) = ∑ s ∈ S, (K s)ᴴ * K s from
    Finset.sum_coe_sort S (fun s => (K s)ᴴ * K s)]
  rw [abortKraus_sum_gram _ (residual_posSemidef K hs hcomplete S)]
  simp only [residual]
  abel

def cutoffLabelEquiv (S : Finset σ) : (S ⊕ Fin input) ≃ Fin (S.card + input) :=
  Fintype.equivFinOfCardEq (by simp)

def finiteCutoffKraus (K : σ → Matrix (Fin out) (Fin input) ℂ) (S : Finset σ)
    (b0 : Fin out) (q : Fin (S.card + input)) : Matrix (Fin out) (Fin input) ℂ :=
  cutoffKraus K S b0 ((cutoffLabelEquiv S).symm q)

def retainedLabel (S : Finset σ) (s : S) : Fin (S.card + input) :=
  cutoffLabelEquiv S (.inl s)

def abortLabel (S : Finset σ) (t : Fin input) : Fin (S.card + input) :=
  cutoffLabelEquiv S (.inr t)

@[simp] theorem finiteCutoffKraus_retained
    (K : σ → Matrix (Fin out) (Fin input) ℂ) (S : Finset σ) (b0 : Fin out) (s : S) :
    finiteCutoffKraus K S b0 (retainedLabel S s) = K s := by
  simp [finiteCutoffKraus, retainedLabel, cutoffKraus]

@[simp] theorem finiteCutoffKraus_abort
    (K : σ → Matrix (Fin out) (Fin input) ℂ) (S : Finset σ) (b0 : Fin out) (t : Fin input) :
    finiteCutoffKraus K S b0 (abortLabel S t) = abortKraus (residual K S) b0 t := by
  simp [finiteCutoffKraus, abortLabel, cutoffKraus]

theorem finiteCutoffKraus_complete (K : σ → Matrix (Fin out) (Fin input) ℂ)
    (hs : Summable (fun s => (K s)ᴴ * K s))
    (hcomplete : (∑' s, (K s)ᴴ * K s) = 1) (S : Finset σ) (b0 : Fin out) :
    (∑ q, (finiteCutoffKraus K S b0 q)ᴴ * finiteCutoffKraus K S b0 q) = 1 := by
  exact ((cutoffLabelEquiv S).symm.sum_comp
    (fun q => (cutoffKraus K S b0 q)ᴴ * cutoffKraus K S b0 q)).trans
      (cutoffKraus_complete K hs hcomplete S b0)

theorem finiteCutoffKraus_retained_action
    (K : σ → Matrix (Fin out) (Fin input) ℂ) (S : Finset σ) (b0 : Fin out) (s : S)
    (X : Matrix (Fin input) (Fin input) ℂ) :
    finiteCutoffKraus K S b0 (retainedLabel S s) * X *
      (finiteCutoffKraus K S b0 (retainedLabel S s))ᴴ = K s * X * (K s)ᴴ := by
  simp only [finiteCutoffKraus_retained]

theorem abortKraus_trace (R : Matrix (Fin input) (Fin input) ℂ)
    (hR : R.PosSemidef) (b0 : Fin out) (X : Matrix (Fin input) (Fin input) ℂ) :
    (∑ t, Matrix.trace (abortKraus R b0 t * X * (abortKraus R b0 t)ᴴ)) =
      Matrix.trace (R * X) := by
  have ht (t : Fin input) :
      Matrix.trace (abortKraus R b0 t * X * (abortKraus R b0 t)ᴴ) =
        Matrix.trace (((abortKraus R b0 t)ᴴ * abortKraus R b0 t) * X) :=
    Matrix.trace_mul_cycle _ _ _
  simp only [ht]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, abortKraus_sum_gram R hR b0]

theorem residual_tendsto_zero (K : σ → Matrix (Fin out) (Fin input) ℂ)
    (hs : Summable (fun s => (K s)ᴴ * K s))
    (hcomplete : (∑' s, (K s)ᴴ * K s) = 1) :
    Filter.Tendsto (residual K) Filter.atTop (nhds 0) := by
  have hsum := hs.hasSum
  rw [hcomplete] at hsum
  have hconst : Filter.Tendsto (fun _ : Finset σ =>
      (1 : Matrix (Fin input) (Fin input) ℂ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  have h := hconst.sub hsum
  change Filter.Tendsto (fun S => 1 - ∑ s ∈ S, (K s)ᴴ * K s) Filter.atTop (nhds 0)
  simpa only [sub_self] using h

theorem residual_norm_tendsto_zero (K : σ → Matrix (Fin out) (Fin input) ℂ)
    (hs : Summable (fun s => (K s)ᴴ * K s))
    (hcomplete : (∑' s, (K s)ᴴ * K s) = 1) :
    Filter.Tendsto (fun S => ‖residual K S‖) Filter.atTop (nhds 0) := by
  simpa only [Function.comp_def, norm_zero] using (continuous_norm.tendsto 0).comp
    (residual_tendsto_zero K hs hcomplete)

theorem residual_trace_tendsto_zero (K : σ → Matrix (Fin out) (Fin input) ℂ)
    (hs : Summable (fun s => (K s)ᴴ * K s))
    (hcomplete : (∑' s, (K s)ᴴ * K s) = 1) :
    Filter.Tendsto (fun S => (residual K S).trace.re) Filter.atTop (nhds 0) := by
  have hc : Continuous (fun R : Matrix (Fin input) (Fin input) ℂ => R.trace.re) := by
    fun_prop
  simpa only [Function.comp_def, Matrix.trace_zero, Complex.zero_re] using
    (hc.tendsto 0).comp (residual_tendsto_zero K hs hcomplete)

theorem residual_tendsto_zero_of_exhausts {δ : Type*} {l : Filter δ}
    (K : σ → Matrix (Fin out) (Fin input) ℂ)
    (hs : Summable (fun s => (K s)ᴴ * K s))
    (hcomplete : (∑' s, (K s)ᴴ * K s) = 1)
    (S : δ → Finset σ) (hS : Filter.Tendsto S l Filter.atTop) :
    Filter.Tendsto (fun a => residual K (S a)) l (nhds 0) :=
  (residual_tendsto_zero K hs hcomplete).comp hS

theorem residual_eq_tsum_omitted (K : σ → Matrix (Fin out) (Fin input) ℂ)
    (hs : Summable (fun s => (K s)ᴴ * K s))
    (hcomplete : (∑' s, (K s)ᴴ * K s) = 1) (S : Finset σ) :
    residual K S = ∑' s : {s // s ∉ S}, (K s)ᴴ * K s := by
  have h := hs.sum_add_tsum_subtype_compl S
  rw [hcomplete] at h
  exact (eq_sub_of_add_eq' h).symm

theorem finiteCutoffKraus_trace_preserving
    (K : σ → Matrix (Fin out) (Fin input) ℂ)
    (hs : Summable (fun s => (K s)ᴴ * K s))
    (hcomplete : (∑' s, (K s)ᴴ * K s) = 1) (S : Finset σ) (b0 : Fin out)
    (X : Matrix (Fin input) (Fin input) ℂ) :
    (∑ q, Matrix.trace (finiteCutoffKraus K S b0 q * X *
      (finiteCutoffKraus K S b0 q)ᴴ)) = Matrix.trace X := by
  have ht (q : Fin (S.card + input)) :
      Matrix.trace (finiteCutoffKraus K S b0 q * X * (finiteCutoffKraus K S b0 q)ᴴ) =
        Matrix.trace (((finiteCutoffKraus K S b0 q)ᴴ * finiteCutoffKraus K S b0 q) * X) :=
    Matrix.trace_mul_cycle _ _ _
  simp only [ht]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, finiteCutoffKraus_complete K hs hcomplete S b0,
    Matrix.one_mul]

theorem exists_exhausting_cutoffs [Countable σ] :
    ∃ S : ℕ → Finset σ, Monotone S ∧ Filter.Tendsto S Filter.atTop Filter.atTop :=
  Filter.exists_seq_monotone_tendsto_atTop_atTop (Finset σ)

theorem exists_countable_complete_cutoffs [Countable σ]
    (K : σ → Matrix (Fin out) (Fin input) ℂ)
    (hs : Summable (fun s => (K s)ᴴ * K s))
    (hcomplete : (∑' s, (K s)ᴴ * K s) = 1) (b0 : Fin out) :
    ∃ S : ℕ → Finset σ, Monotone S ∧
      Filter.Tendsto S Filter.atTop Filter.atTop ∧
      (∀ n, (∑ q, (finiteCutoffKraus K (S n) b0 q)ᴴ *
        finiteCutoffKraus K (S n) b0 q) = 1) ∧
      Filter.Tendsto (fun n => residual K (S n)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => ‖residual K (S n)‖) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => (residual K (S n)).trace.re) Filter.atTop (nhds 0) := by
  obtain ⟨S, hmono, hS⟩ := exists_exhausting_cutoffs (σ := σ)
  refine ⟨S, hmono, hS, fun n => finiteCutoffKraus_complete K hs hcomplete (S n) b0,
    residual_tendsto_zero_of_exhausts K hs hcomplete S hS, ?_, ?_⟩
  · exact (residual_norm_tendsto_zero K hs hcomplete).comp hS
  · exact (residual_trace_tendsto_zero K hs hcomplete).comp hS

theorem residual_range_tendsto_zero
    (K : ℕ → Matrix (Fin out) (Fin input) ℂ)
    (hs : Summable (fun s => (K s)ᴴ * K s))
    (hcomplete : (∑' s, (K s)ᴴ * K s) = 1) :
    Filter.Tendsto (fun n => residual K (Finset.range n)) Filter.atTop (nhds 0) := by
  have hsum := hs.hasSum.tendsto_sum_nat
  rw [hcomplete] at hsum
  have hconst : Filter.Tendsto (fun _ : ℕ =>
      (1 : Matrix (Fin input) (Fin input) ℂ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  have h := hconst.sub hsum
  change Filter.Tendsto (fun n => 1 - ∑ s ∈ Finset.range n, (K s)ᴴ * K s)
    Filter.atTop (nhds 0)
  simpa only [sub_self] using h

end

end QuantumProver.ElegantJointMeasurement.CountableInstruments

namespace QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open QuantumProver.ElegantJointMeasurement.ContinuousInstrumentRadonNikodym QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments QuantumProver.ElegantJointMeasurement.CP
open scoped NNReal ENNReal Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option maxHeartbeats 800000

variable {H Ω : Type*} [MeasurableSpace H] [MeasurableSpace Ω]
variable [MeasurableSpace.CountableOrCountablyGenerated H Ω]
variable {m p : ℕ} [NeZero m] [NeZero p]

abbrev MatrixInstrument :=
  MatrixCPInstrument (H := H) (Ω := Ω) (I := Fin m) (O := Fin p)

variable (P : MatrixInstrument (H := H) (Ω := Ω) (m := m) (p := p))

instance measureKernel_isMarkov : IsMarkovKernel P.measureKernel := P.measureKernel_isMarkov

def matrixKraus (z : H × Ω) (q : Fin m × Fin p) : Matrix (Fin p) (Fin m) ℂ :=
  QuantumProver.ElegantJointMeasurement.CP.krausOperator (P.cpDensity z.1 z.2) q

def matrixSquare (z : H × Ω) (q : Fin m × Fin p) : Matrix (Fin m) (Fin m) ℂ :=
  QuantumProver.ElegantJointMeasurement.CP.positiveInputKraus (matrixKraus P z q)

def represented_matrixRecovery (z : H × Ω) (q : Fin m × Fin p) : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery m p :=
  QuantumProver.ElegantJointMeasurement.CP.LocalRecovery.rectangular (Nat.pos_of_ne_zero (NeZero.ne p)) (matrixKraus P z q)

theorem cpDensity_jointCoordinateMeasurable :
    CoordinateMeasurable (fun z : H × Ω => P.cpDensity z.1 z.2) :=
  P.cpDensity_joint_coordinate_measurable

theorem measurable_matrixKraus (q : Fin m × Fin p) :
    Measurable (fun z : H × Ω => matrixKraus P z q) :=
  QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.measurable_canonicalKraus _
    (cpDensity_jointCoordinateMeasurable P) q

theorem measurable_matrixSquare (q : Fin m × Fin p) :
    Measurable (fun z : H × Ω => matrixSquare P z q) :=
  QuantumProver.ElegantJointMeasurement.CP.measurable_positiveInputKraus.comp (measurable_matrixKraus P q)

theorem matrixSquare_positive (z : H × Ω) (q : Fin m × Fin p) :
    (matrixSquare P z q).PosSemidef := QuantumProver.ElegantJointMeasurement.CP.positiveInputKraus_posSemidef _

theorem matrixSquare_gram (z : H × Ω) (q : Fin m × Fin p) :
    (matrixSquare P z q)ᴴ * matrixSquare P z q =
      (matrixKraus P z q)ᴴ * matrixKraus P z q := QuantumProver.ElegantJointMeasurement.CP.positiveInputKraus_gram _

theorem matrixRecovery_matrixUnitMeasurable (q : Fin m × Fin p) :
    QuantumProver.ElegantJointMeasurement.CP.MatrixUnitMeasurable (fun z : H × Ω => (represented_matrixRecovery P z q).map) :=
  QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField_matrixUnitMeasurable (Nat.pos_of_ne_zero (NeZero.ne p))
    (fun z => matrixKraus P z q) (measurable_matrixKraus P q)

theorem measurable_matrixRecoveryKraus (q : Fin m × Fin p) (t : Unit ⊕ Fin m) :
    Measurable (fun z : H × Ω => QuantumProver.ElegantJointMeasurement.CP.rectangularRecoveryKraus
      (Nat.pos_of_ne_zero (NeZero.ne p)) (matrixKraus P z q) t) :=
  (QuantumProver.ElegantJointMeasurement.CP.measurable_rectangularRecoveryKraus (Nat.pos_of_ne_zero (NeZero.ne p)) t).comp
    (measurable_matrixKraus P q)

theorem matrixRecovery_square_action (z : H × Ω) (q : Fin m × Fin p)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    (represented_matrixRecovery P z q).map (matrixSquare P z q * X * (matrixSquare P z q)ᴴ) =
      matrixKraus P z q * X * (matrixKraus P z q)ᴴ :=
  QuantumProver.ElegantJointMeasurement.CP.rectangularRecovery_apply (Nat.pos_of_ne_zero (NeZero.ne p)) _ X

theorem matrix_recovered_action (z : H × Ω) (X : Matrix (Fin m) (Fin m) ℂ) :
    (∑ q, (represented_matrixRecovery P z q).map
      (matrixSquare P z q * X * (matrixSquare P z q)ᴴ)) = P.cpDensity z.1 z.2 X := by
  calc
    _ = ∑ q, matrixKraus P z q * X * (matrixKraus P z q)ᴴ :=
      Finset.sum_congr rfl (fun q _ => matrixRecovery_square_action P z q X)
    _ = P.cpDensity z.1 z.2 X :=
      (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus_matrix_action
        (fun z : H × Ω => P.cpDensity z.1 z.2)
        (fun z => P.cpDensity_completelyPositive z.1 z.2) z X).symm

theorem matrix_setIntegral_recovered (h : H) (B : Set Ω) (hB : MeasurableSet B)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    (∫ ω in B, ∑ q, (represented_matrixRecovery P (h, ω) q).map
      (matrixSquare P (h, ω) q * X * (matrixSquare P (h, ω) q)ᴴ) ∂P.measureKernel h) =
      P.map h B X := by
  simp_rw [matrix_recovered_action]
  exact P.cpDensity_setIntegral h B hB X

theorem matrix_report_setIntegral_recovered (h : H) (J : H × Ω → Fin 4)
    (hJ : Measurable J) (j : Fin 4) (X : Matrix (Fin m) (Fin m) ℂ) :
    (∫ ω in {ω | J (h, ω) = j}, ∑ q, (represented_matrixRecovery P (h, ω) q).map
      (matrixSquare P (h, ω) q * X * (matrixSquare P (h, ω) q)ᴴ) ∂P.measureKernel h) =
      P.map h {ω | J (h, ω) = j} X :=
  matrix_setIntegral_recovered P h _
    ((measurableSet_singleton j).preimage (hJ.comp (measurable_const.prodMk measurable_id))) X

theorem integrable_matrixSquare_gram_sum (h : H) :
    Integrable (fun ω => ∑ q, (matrixSquare P (h, ω) q)ᴴ * matrixSquare P (h, ω) q)
      (P.measureKernel h) := by
  simp_rw [matrixSquare_gram]
  exact QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.integrable_canonicalGram _ _
    (P.cpDensity_coordinateMeasurable h) (P.cpDensity_completelyPositive h)
    (P.cpDensity_matrixTraceComplete h)

theorem matrix_integral_squareGram (h : H) :
    (∫ ω, ∑ q, (matrixSquare P (h, ω) q)ᴴ * matrixSquare P (h, ω) q ∂P.measureKernel h) = 1 := by
  simp_rw [matrixSquare_gram]
  exact QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.integral_canonicalGram_eq_one _ _
    (P.cpDensity_coordinateMeasurable h) (P.cpDensity_completelyPositive h)
    (P.cpDensity_matrixTraceComplete h)

private theorem norm_rectangular_sandwich_le
    (K : Matrix (Fin p) (Fin m) ℂ) (X : Matrix (Fin m) (Fin m) ℂ) :
    ‖K * X * Kᴴ‖ ≤ ‖X‖ * ‖Kᴴ * K‖ := by
  calc
    ‖K * X * Kᴴ‖ ≤ ‖K * X‖ * ‖Kᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖K‖ * ‖X‖) * ‖Kᴴ‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul K X) (norm_nonneg _)
    _ = ‖X‖ * ‖Kᴴ * K‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose_mul_self]
      ring

theorem integrable_matrixKraus_action (h : H) (q : Fin m × Fin p)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    Integrable (fun ω => matrixKraus P (h, ω) q * X * (matrixKraus P (h, ω) q)ᴴ)
      (P.measureKernel h) := by
  have hi := QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.integrable_canonicalKraus_gram _ _
    (P.cpDensity_coordinateMeasurable h) (P.cpDensity_completelyPositive h)
    (P.cpDensity_matrixTraceComplete h) q
  have hm : Measurable (fun ω => matrixKraus P (h, ω) q) :=
    (measurable_matrixKraus P q).comp (measurable_const.prodMk measurable_id)
  have haction : Measurable (fun K : Matrix (Fin p) (Fin m) ℂ => K * X * Kᴴ) :=
    ((continuous_id.matrix_mul continuous_const).matrix_mul
      continuous_id.matrix_conjTranspose).measurable
  apply (hi.norm.const_mul ‖X‖).mono'
  · exact (haction.comp hm).stronglyMeasurable.aestronglyMeasurable
  · exact Eventually.of_forall fun ω => norm_rectangular_sandwich_le _ X

section UniformColumns

variable {A Q E : Type*} [MeasurableSpace A] [MeasurableSpace Q]
variable [Fintype Q] [Nonempty Q] [MeasurableSingletonClass Q]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integrable_prod_uniform_columns (μ : Measure A) [SFinite μ]
    (f : A × Q → E) (hf : ∀ q, Integrable (fun a => f (a, q)) μ) :
    Integrable f (μ.prod (PMF.uniformOfFintype Q).toMeasure) := by
  classical
  have hi (q : Q) : Integrable
      ({z : A × Q | z.2 = q}.indicator (fun z => f (z.1, q)))
      (μ.prod (PMF.uniformOfFintype Q).toMeasure) :=
    ((hf q).comp_fst _).indicator ((measurableSet_singleton q).preimage measurable_snd)
  have hs := integrable_finsetSum Finset.univ (fun q _ => hi q)
  convert hs using 1
  funext z
  simp [Set.indicator, eq_comm]

theorem integral_prod_uniform_columns (μ : Measure A) [SFinite μ]
    (f : A × Q → E) (hf : ∀ q, Integrable (fun a => f (a, q)) μ) :
    (∫ z, f z ∂μ.prod (PMF.uniformOfFintype Q).toMeasure) =
      (Fintype.card Q : ℝ)⁻¹ • (∫ a, ∑ q, f (a, q) ∂μ) := by
  classical
  rw [integral_prod _ (integrable_prod_uniform_columns μ f hf)]
  simp_rw [PMF.integral_eq_sum, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ← Finset.smul_sum]
  rw [integral_smul]

end UniformColumns

def refinedKernel : Kernel H (Ω × (Fin m × Fin p)) :=
  P.measureKernel ×ₖ Kernel.const H (PMF.uniformOfFintype (Fin m × Fin p)).toMeasure

instance refinedKernel_isMarkov : IsMarkovKernel (refinedKernel P) := by
  unfold refinedKernel
  infer_instance

theorem refinedKernel_apply (h : H) :
    refinedKernel P h = (P.measureKernel h).prod
      (PMF.uniformOfFintype (Fin m × Fin p)).toMeasure := by
  rw [refinedKernel, Kernel.prod_apply, Kernel.const_apply]

def refinedSquare (z : H × (Ω × (Fin m × Fin p))) : Matrix (Fin m) (Fin m) ℂ :=
  QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus
    (Fintype.card (Fin m × Fin p)) (matrixSquare P (z.1, z.2.1) z.2.2)

def refinedRecovery (z : H × (Ω × (Fin m × Fin p))) : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery m p :=
  represented_matrixRecovery P (z.1, z.2.1) z.2.2

theorem measurable_refinedSquare : Measurable (refinedSquare P) := by
  have hm : Measurable (fun z : (H × Ω) × (Fin m × Fin p) => matrixSquare P z.1 z.2) :=
    measurable_from_prod_countable_left (measurable_matrixSquare P)
  have ha : Measurable (fun z : H × (Ω × (Fin m × Fin p)) => ((z.1, z.2.1), z.2.2)) := by
    exact (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  exact (hm.comp ha).const_smul (Real.sqrt (Fintype.card (Fin m × Fin p) : ℝ))

theorem refinedSquare_positive (z : H × (Ω × (Fin m × Fin p))) :
    (refinedSquare P z).PosSemidef := by
  change ((Real.sqrt (Fintype.card (Fin m × Fin p) : ℝ)) •
    matrixSquare P (z.1, z.2.1) z.2.2).PosSemidef
  exact Matrix.PosSemidef.smul (α := ℝ) (matrixSquare_positive P _ _)
    (Real.sqrt_nonneg _)

theorem refinedRecovery_matrixUnitMeasurable :
    QuantumProver.ElegantJointMeasurement.CP.MatrixUnitMeasurable (fun z => (refinedRecovery P z).map) := by
  intro i j b c
  have hm : Measurable (fun z : (H × Ω) × (Fin m × Fin p) => matrixKraus P z.1 z.2) :=
    measurable_from_prod_countable_left (measurable_matrixKraus P)
  have ha : Measurable (fun z : H × (Ω × (Fin m × Fin p)) => ((z.1, z.2.1), z.2.2)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  have he := (QuantumProver.ElegantJointMeasurement.CP.measurable_rectangularRecovery_application
    (Nat.pos_of_ne_zero (NeZero.ne p))).comp
    ((hm.comp ha).prodMk (measurable_const (a := Matrix.single i j (1 : ℂ))))
  exact (measurable_pi_apply c).comp ((measurable_pi_apply b).comp he)

theorem refinedSquare_gram (z : H × (Ω × (Fin m × Fin p))) :
    (refinedSquare P z)ᴴ * refinedSquare P z =
      (Fintype.card (Fin m × Fin p) : ℝ) •
        ((matrixKraus P (z.1, z.2.1) z.2.2)ᴴ * matrixKraus P (z.1, z.2.1) z.2.2) := by
  rw [refinedSquare, QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus_gram _ _ (by positivity),
    matrixSquare_gram]

theorem refinedRecovery_square_action (z : H × (Ω × (Fin m × Fin p)))
    (X : Matrix (Fin m) (Fin m) ℂ) :
    (refinedRecovery P z).map (refinedSquare P z * X * (refinedSquare P z)ᴴ) =
      (Fintype.card (Fin m × Fin p) : ℝ) •
        (matrixKraus P (z.1, z.2.1) z.2.2 * X *
          (matrixKraus P (z.1, z.2.1) z.2.2)ᴴ) := by
  have hs : refinedSquare P z * X * (refinedSquare P z)ᴴ =
      (Fintype.card (Fin m × Fin p) : ℝ) •
        (matrixSquare P (z.1, z.2.1) z.2.2 * X *
          (matrixSquare P (z.1, z.2.1) z.2.2)ᴴ) := by
    simp only [refinedSquare, QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus,
      Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Real.mul_self_sqrt (show 0 ≤ (Fintype.card (Fin m × Fin p) : ℝ) by positivity)]
  rw [hs, LinearMap.map_smul_of_tower]
  exact congrArg ((Fintype.card (Fin m × Fin p) : ℝ) • ·)
    (matrixRecovery_square_action P _ _ X)

theorem integrable_refinedSquare_gram (h : H) :
    Integrable (fun r => (refinedSquare P (h, r))ᴴ * refinedSquare P (h, r))
      (refinedKernel P h) := by
  rw [refinedKernel_apply]
  apply integrable_prod_uniform_columns
  intro q
  simp_rw [refinedSquare_gram]
  exact Integrable.smul (Fintype.card (Fin m × Fin p) : ℝ)
    (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.integrable_canonicalKraus_gram _ _
      (P.cpDensity_coordinateMeasurable h) (P.cpDensity_completelyPositive h)
      (P.cpDensity_matrixTraceComplete h) q)

theorem integrable_refinedRecovery_action (h : H) (X : Matrix (Fin m) (Fin m) ℂ) :
    Integrable (fun r => (refinedRecovery P (h, r)).map
      (refinedSquare P (h, r) * X * (refinedSquare P (h, r))ᴴ))
      (refinedKernel P h) := by
  rw [refinedKernel_apply]
  apply integrable_prod_uniform_columns
  intro q
  simp_rw [refinedRecovery_square_action]
  exact Integrable.smul (Fintype.card (Fin m × Fin p) : ℝ)
    (integrable_matrixKraus_action P h q X)

theorem refined_integral_squareGram (h : H) :
    (∫ r, (refinedSquare P (h, r))ᴴ * refinedSquare P (h, r) ∂refinedKernel P h) = 1 := by
  have hc : (Fintype.card (Fin m × Fin p) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Fin m × Fin p)).ne'
  have hi (q : Fin m × Fin p) : Integrable (fun ω =>
      (refinedSquare P (h, (ω, q)))ᴴ * refinedSquare P (h, (ω, q))) (P.measureKernel h) := by
    simp_rw [refinedSquare_gram]
    exact Integrable.smul (Fintype.card (Fin m × Fin p) : ℝ)
      (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.integrable_canonicalKraus_gram _ _
      (P.cpDensity_coordinateMeasurable h) (P.cpDensity_completelyPositive h)
      (P.cpDensity_matrixTraceComplete h) q)
  rw [refinedKernel_apply, integral_prod_uniform_columns _ _ hi]
  simp_rw [refinedSquare_gram, ← Finset.smul_sum]
  rw [integral_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  simpa only [matrixSquare_gram] using matrix_integral_squareGram P h

theorem refined_setIntegral_recovered (h : H) (B : Set Ω) (hB : MeasurableSet B)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    (∫ r in B ×ˢ (Set.univ : Set (Fin m × Fin p)),
      (refinedRecovery P (h, r)).map
        (refinedSquare P (h, r) * X * (refinedSquare P (h, r))ᴴ) ∂refinedKernel P h) =
      P.map h B X := by
  have hc : (Fintype.card (Fin m × Fin p) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Fin m × Fin p)).ne'
  have hi (q : Fin m × Fin p) : Integrable (fun ω =>
      (refinedRecovery P (h, (ω, q))).map
        (refinedSquare P (h, (ω, q)) * X * (refinedSquare P (h, (ω, q)))ᴴ))
      ((P.measureKernel h).restrict B) := by
    simp_rw [refinedRecovery_square_action]
    exact Integrable.smul (Fintype.card (Fin m × Fin p) : ℝ)
      ((integrable_matrixKraus_action P h q X).integrableOn (s := B))
  rw [refinedKernel_apply, ← Measure.prod_restrict B Set.univ, Measure.restrict_univ,
    integral_prod_uniform_columns _ _ hi]
  simp_rw [refinedRecovery_square_action, ← Finset.smul_sum]
  rw [integral_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  simpa only [matrixRecovery_square_action] using matrix_setIntegral_recovered P h B hB X

theorem matrix_coordinate_additive_all_complex (h : H) (s : ℕ → Set Ω)
    (hs : ∀ n, MeasurableSet (s n)) (hdisj : Pairwise (fun i j => Disjoint (s i) (s j)))
    (X : Matrix (Fin m) (Fin m) ℂ) (b c : Fin p) :
    HasSum (fun n => P.map h (s n) X b c) (P.map h (⋃ n, s n) X b c) := by
  have heq (B : Set Ω) : P.map h B X b c =
      ∑ i : Fin m, ∑ j : Fin m, X i j * P.map h B (Matrix.single i j 1) b c := by
    rw [QuantumProver.ElegantJointMeasurement.CP.matrixMap_apply_eq_sum_matrix_units]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  have hsum := hasSum_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ =>
    hasSum_sum (s := (Finset.univ : Finset (Fin m))) (fun j _ =>
      (P.coordinate_additive h s hs hdisj i j b c).mul_left (X i j)))
  have hf : (fun n => P.map h (s n) X b c) =
      (fun n => ∑ i : Fin m, ∑ j : Fin m,
        X i j * P.map h (s n) (Matrix.single i j 1) b c) := funext (fun n => heq (s n))
  rw [hf, heq]
  exact hsum

omit [NeZero p] [MeasurableSpace.CountableOrCountablyGenerated H Ω] in

theorem output_dimension_pos_of_traceComplete {out : ℕ}
    (Q : MatrixCPInstrument (H := H) (Ω := Ω) (I := Fin m) (O := Fin out)) (h : H) :
    0 < out := by
  by_contra hn
  have hz : out = 0 := Nat.eq_zero_of_not_pos hn
  subst out
  have ht := Q.traceComplete h (Matrix.single (0 : Fin m) (0 : Fin m) (1 : ℂ))
  simpa [Matrix.trace, Matrix.single_apply] using ht

def absorbPending {a : ℕ} (K₀ : H → Matrix (Fin m) (Fin a) ℂ) (hK₀ : Measurable K₀) :
    MatrixCPInstrument (H := H) (Ω := Ω) (I := Fin a) (O := Fin p) where
  map := QuantumProver.ElegantJointMeasurement.CP.setwiseRecoveryAbsorbedField (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ P.map
  empty h := by
    ext X
    simp [QuantumProver.ElegantJointMeasurement.CP.setwiseRecoveryAbsorbedField, P.empty]
  completelyPositive h B hB :=
    QuantumProver.ElegantJointMeasurement.CP.setwiseRecoveryAbsorbedField_completelyPositive
      (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ P.map P.completelyPositive h B hB
  measurable_entry B hB :=
    QuantumProver.ElegantJointMeasurement.CP.setwiseRecoveryAbsorbedField_matrixUnitMeasurable
      (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ hK₀ P.map P.measurable_entry B hB
  coordinate_additive h s hs hdisj i j b c :=
    matrix_coordinate_additive_all_complex P h s hs hdisj
      ((QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ h).map
        (Matrix.single i j 1)) b c
  traceComplete h X := QuantumProver.ElegantJointMeasurement.CP.setwiseRecoveryAbsorbedField_matrixTraceComplete
    (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ P.map P.traceComplete h X

theorem pendingRecovery_identity (h : H) (X : Matrix (Fin m) (Fin m) ℂ) :
    (QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField (Nat.pos_of_ne_zero (NeZero.ne m))
      (fun _ : H => (1 : Matrix (Fin m) (Fin m) ℂ)) h).map X = X := by
  have he := QuantumProver.ElegantJointMeasurement.CP.rectangularRecovery_apply (Nat.pos_of_ne_zero (NeZero.ne m))
    (1 : Matrix (Fin m) (Fin m) ℂ) X
  simpa only [QuantumProver.ElegantJointMeasurement.CP.positiveInputKraus, Matrix.conjTranspose_one, Matrix.one_mul,
    Matrix.mul_one, CFC.sqrt_one, QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField, QuantumProver.ElegantJointMeasurement.CP.LocalRecovery.rectangular] using he

theorem absorbed_refined_setIntegral {a : ℕ} [NeZero a]
    (K₀ : H → Matrix (Fin m) (Fin a) ℂ) (hK₀ : Measurable K₀)
    (h : H) (B : Set Ω) (hB : MeasurableSet B) (X : Matrix (Fin a) (Fin a) ℂ) :
    (∫ r in B ×ˢ (Set.univ : Set (Fin a × Fin p)),
      (refinedRecovery (absorbPending P K₀ hK₀) (h, r)).map
        (refinedSquare (absorbPending P K₀ hK₀) (h, r) * X *
          (refinedSquare (absorbPending P K₀ hK₀) (h, r))ᴴ)
      ∂refinedKernel (absorbPending P K₀ hK₀) h) =
      P.map h B ((QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField
        (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ h).map X) :=
  refined_setIntegral_recovered (absorbPending P K₀ hK₀) h B hB X

theorem absorbed_refined_integral_squareGram {a : ℕ} [NeZero a]
    (K₀ : H → Matrix (Fin m) (Fin a) ℂ) (hK₀ : Measurable K₀) (h : H) :
    (∫ r, (refinedSquare (absorbPending P K₀ hK₀) (h, r))ᴴ *
      refinedSquare (absorbPending P K₀ hK₀) (h, r)
      ∂refinedKernel (absorbPending P K₀ hK₀) h) = 1 :=
  refined_integral_squareGram (absorbPending P K₀ hK₀) h

section TwoMatrixSteps

variable {Δ : Type*} [MeasurableSpace Δ]
variable [MeasurableSpace.CountableOrCountablyGenerated H Δ]
variable [MeasurableSpace.CountableOrCountablyGenerated (H × Δ) Ω]
variable {a : ℕ} [NeZero a]

def absorbPreviousMatrixColumn
    (Prev : MatrixInstrument (H := H) (Ω := Δ) (m := a) (p := m))
    (Next : MatrixInstrument (H := H × Δ) (Ω := Ω) (m := m) (p := p))
    (q : Fin a × Fin m) : MatrixInstrument (H := H × Δ) (Ω := Ω) (m := a) (p := p) :=
  absorbPending Next (fun z => matrixKraus Prev z q) (measurable_matrixKraus Prev q)

theorem two_matrix_steps_same_physical_action
    (Prev : MatrixInstrument (H := H) (Ω := Δ) (m := a) (p := m))
    (Next : MatrixInstrument (H := H × Δ) (Ω := Ω) (m := m) (p := p))
    (q : Fin a × Fin m) (z : H × Δ) (B : Set Ω) (hB : MeasurableSet B)
    (X : Matrix (Fin a) (Fin a) ℂ) :
    (∫ r in B ×ˢ (Set.univ : Set (Fin a × Fin p)),
      (refinedRecovery (absorbPreviousMatrixColumn Prev Next q) (z, r)).map
        (refinedSquare (absorbPreviousMatrixColumn Prev Next q) (z, r) *
          (matrixSquare Prev z q * X * (matrixSquare Prev z q)ᴴ) *
          (refinedSquare (absorbPreviousMatrixColumn Prev Next q) (z, r))ᴴ)
      ∂refinedKernel (absorbPreviousMatrixColumn Prev Next q) z) =
      Next.map z B (matrixKraus Prev z q * X * (matrixKraus Prev z q)ᴴ) := by
  have h := absorbed_refined_setIntegral Next (fun z => matrixKraus Prev z q)
    (measurable_matrixKraus Prev q) z B hB (matrixSquare Prev z q * X * (matrixSquare Prev z q)ᴴ)
  change _ = Next.map z B ((represented_matrixRecovery Prev z q).map
    (matrixSquare Prev z q * X * (matrixSquare Prev z q)ᴴ)) at h
  rw [matrixRecovery_square_action] at h
  exact h

end TwoMatrixSteps

section PhysicalReferenceAbsorption

variable {H' : Type*} [MeasurableSpace H'] {a : ℕ} [NeZero a]

theorem matrixUnitMeasurable_comp {Z Z' I O : Type*}
    [MeasurableSpace Z] [MeasurableSpace Z'] [DecidableEq I]
    (Φ : Z → (Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ))
    (hΦ : QuantumProver.ElegantJointMeasurement.CP.MatrixUnitMeasurable Φ) (g : Z' → Z) (hg : Measurable g) :
    QuantumProver.ElegantJointMeasurement.CP.MatrixUnitMeasurable (fun z => Φ (g z)) := by
  intro i j b c
  exact (hΦ i j b c).comp hg

def pendingDensity (f : H' → H) (K₀ : H' → Matrix (Fin m) (Fin a) ℂ)
    (z : H' × Ω) : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ :=
  QuantumProver.ElegantJointMeasurement.CP.recoveryAbsorbedField (Nat.pos_of_ne_zero (NeZero.ne m)) K₀
    (fun z : H' × Ω => P.cpDensity (f z.1) z.2) z

theorem pendingDensity_coordinateMeasurable (f : H' → H) (hf : Measurable f)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (hK₀ : Measurable K₀) :
    CoordinateMeasurable (pendingDensity P f K₀) := by
  have hproj : Measurable (fun z : H' × Ω => (f z.1, z.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  have hΦ := matrixUnitMeasurable_comp
    (fun z : H × Ω => P.cpDensity z.1 z.2)
    (cpDensity_jointCoordinateMeasurable P)
    (fun z : H' × Ω => (f z.1, z.2)) hproj
  exact QuantumProver.ElegantJointMeasurement.CP.recoveryAbsorbedField_matrixUnitMeasurable
    (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ hK₀
    (fun z : H' × Ω => P.cpDensity (f z.1) z.2) hΦ

theorem pendingDensity_completelyPositive (f : H' → H)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (z : H' × Ω) :
    QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (pendingDensity P f K₀ z) :=
  QuantumProver.ElegantJointMeasurement.CP.recoveryAbsorbedField_completelyPositive _ K₀ _
    (fun z => P.cpDensity_completelyPositive (f z.1) z.2) z

theorem pendingDensity_matrixTraceComplete (f : H' → H)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (h : H') :
    MatrixTraceComplete (P.measureKernel (f h)) (fun ω => pendingDensity P f K₀ (h, ω)) := by
  intro X
  change (∫ ω, (P.cpDensity (f h) ω
    ((QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ h).map X)).trace
    ∂P.measureKernel (f h)) = X.trace
  exact (P.cpDensity_matrixTraceComplete (f h) _).trans
    ((QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ h).trace_preserving X)

theorem pendingDensity_setIntegral (f : H' → H)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (h : H') (B : Set Ω) (hB : MeasurableSet B)
    (X : Matrix (Fin a) (Fin a) ℂ) :
    (∫ ω in B, pendingDensity P f K₀ (h, ω) X ∂P.measureKernel (f h)) =
      P.map (f h) B ((QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField
        (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ h).map X) := by
  change (∫ ω in B, P.cpDensity (f h) ω
    ((QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ h).map X)
    ∂P.measureKernel (f h)) = _
  exact P.cpDensity_setIntegral (f h) B hB
    ((QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ h).map X)

def pendingKraus (f : H' → H) (K₀ : H' → Matrix (Fin m) (Fin a) ℂ)
    (z : H' × Ω) (q : Fin a × Fin p) : Matrix (Fin p) (Fin a) ℂ :=
  QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus (pendingDensity P f K₀) z q

def pendingSquare (f : H' → H) (K₀ : H' → Matrix (Fin m) (Fin a) ℂ)
    (z : H' × Ω) (q : Fin a × Fin p) : Matrix (Fin a) (Fin a) ℂ :=
  QuantumProver.ElegantJointMeasurement.CP.positiveInputKraus (pendingKraus P f K₀ z q)

def pendingRecovery (f : H' → H) (K₀ : H' → Matrix (Fin m) (Fin a) ℂ)
    (z : H' × Ω) (q : Fin a × Fin p) : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery a p :=
  QuantumProver.ElegantJointMeasurement.CP.LocalRecovery.rectangular (Nat.pos_of_ne_zero (NeZero.ne p))
    (pendingKraus P f K₀ z q)

theorem measurable_pendingKraus (f : H' → H) (hf : Measurable f)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (hK₀ : Measurable K₀) (q : Fin a × Fin p) :
    Measurable (fun z => pendingKraus P f K₀ z q) :=
  QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.measurable_canonicalKraus _
    (pendingDensity_coordinateMeasurable P f hf K₀ hK₀) q

theorem measurable_pendingSquare (f : H' → H) (hf : Measurable f)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (hK₀ : Measurable K₀) (q : Fin a × Fin p) :
    Measurable (fun z => pendingSquare P f K₀ z q) :=
  QuantumProver.ElegantJointMeasurement.CP.measurable_positiveInputKraus.comp (measurable_pendingKraus P f hf K₀ hK₀ q)

theorem pendingSquare_gram (f : H' → H) (K₀ : H' → Matrix (Fin m) (Fin a) ℂ)
    (z : H' × Ω) (q : Fin a × Fin p) :
    (pendingSquare P f K₀ z q)ᴴ * pendingSquare P f K₀ z q =
      (pendingKraus P f K₀ z q)ᴴ * pendingKraus P f K₀ z q :=
  QuantumProver.ElegantJointMeasurement.CP.positiveInputKraus_gram _

theorem pendingRecovery_square_action (f : H' → H)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (z : H' × Ω) (q : Fin a × Fin p)
    (X : Matrix (Fin a) (Fin a) ℂ) :
    (pendingRecovery P f K₀ z q).map
      (pendingSquare P f K₀ z q * X * (pendingSquare P f K₀ z q)ᴴ) =
      pendingKraus P f K₀ z q * X * (pendingKraus P f K₀ z q)ᴴ :=
  QuantumProver.ElegantJointMeasurement.CP.rectangularRecovery_apply _ _ X

theorem pending_recovered_action (f : H' → H) (K₀ : H' → Matrix (Fin m) (Fin a) ℂ)
    (z : H' × Ω) (X : Matrix (Fin a) (Fin a) ℂ) :
    (∑ q, (pendingRecovery P f K₀ z q).map
      (pendingSquare P f K₀ z q * X * (pendingSquare P f K₀ z q)ᴴ)) =
      P.cpDensity (f z.1) z.2
        ((QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ z.1).map X) := by
  simp_rw [pendingRecovery_square_action]
  exact (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus_matrix_action _
    (pendingDensity_completelyPositive P f K₀) z X).symm

def pendingRefinedKernel (f : H' → H) (hf : Measurable f)
    (_K₀ : H' → Matrix (Fin m) (Fin a) ℂ) : Kernel H' (Ω × (Fin a × Fin p)) :=
  (P.measureKernel.comap f hf) ×ₖ
    Kernel.const H' (PMF.uniformOfFintype (Fin a × Fin p)).toMeasure

instance pendingRefinedKernel_isMarkov (f : H' → H) (hf : Measurable f)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) :
    IsMarkovKernel (pendingRefinedKernel P f hf K₀) := by
  unfold pendingRefinedKernel
  infer_instance

theorem pendingRefinedKernel_apply (f : H' → H) (hf : Measurable f)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (h : H') :
    pendingRefinedKernel P f hf K₀ h = (P.measureKernel (f h)).prod
      (PMF.uniformOfFintype (Fin a × Fin p)).toMeasure := by
  rw [pendingRefinedKernel, Kernel.prod_apply, Kernel.comap_apply, Kernel.const_apply]

def pendingRefinedSquare (f : H' → H) (K₀ : H' → Matrix (Fin m) (Fin a) ℂ)
    (z : H' × (Ω × (Fin a × Fin p))) : Matrix (Fin a) (Fin a) ℂ :=
  QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus (Fintype.card (Fin a × Fin p))
    (pendingSquare P f K₀ (z.1, z.2.1) z.2.2)

def pendingRefinedRecovery (f : H' → H) (K₀ : H' → Matrix (Fin m) (Fin a) ℂ)
    (z : H' × (Ω × (Fin a × Fin p))) : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery a p :=
  pendingRecovery P f K₀ (z.1, z.2.1) z.2.2

theorem measurable_pendingRefinedSquare (f : H' → H) (hf : Measurable f)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (hK₀ : Measurable K₀) :
    Measurable (pendingRefinedSquare P f K₀) := by
  have hm : Measurable (fun z : (H' × Ω) × (Fin a × Fin p) => pendingSquare P f K₀ z.1 z.2) :=
    measurable_from_prod_countable_left (measurable_pendingSquare P f hf K₀ hK₀)
  have ha : Measurable (fun z : H' × (Ω × (Fin a × Fin p)) => ((z.1, z.2.1), z.2.2)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  exact (hm.comp ha).const_smul (Real.sqrt (Fintype.card (Fin a × Fin p) : ℝ))

theorem pendingRefinedSquare_positive (f : H' → H)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (z : H' × (Ω × (Fin a × Fin p))) :
    (pendingRefinedSquare P f K₀ z).PosSemidef := by
  change ((Real.sqrt (Fintype.card (Fin a × Fin p) : ℝ)) •
    QuantumProver.ElegantJointMeasurement.CP.positiveInputKraus (pendingKraus P f K₀ (z.1, z.2.1) z.2.2)).PosSemidef
  exact Matrix.PosSemidef.smul (α := ℝ) (QuantumProver.ElegantJointMeasurement.CP.positiveInputKraus_posSemidef _)
    (Real.sqrt_nonneg _)

theorem pendingRefinedRecovery_matrixUnitMeasurable (f : H' → H) (hf : Measurable f)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (hK₀ : Measurable K₀) :
    QuantumProver.ElegantJointMeasurement.CP.MatrixUnitMeasurable (fun z => (pendingRefinedRecovery P f K₀ z).map) := by
  intro i j b c
  have hm : Measurable (fun z : (H' × Ω) × (Fin a × Fin p) => pendingKraus P f K₀ z.1 z.2) :=
    measurable_from_prod_countable_left (measurable_pendingKraus P f hf K₀ hK₀)
  have ha : Measurable (fun z : H' × (Ω × (Fin a × Fin p)) => ((z.1, z.2.1), z.2.2)) :=
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd)
  have he := (QuantumProver.ElegantJointMeasurement.CP.measurable_rectangularRecovery_application
    (Nat.pos_of_ne_zero (NeZero.ne p))).comp
    ((hm.comp ha).prodMk (measurable_const (a := Matrix.single i j (1 : ℂ))))
  exact (measurable_pi_apply c).comp ((measurable_pi_apply b).comp he)

theorem pendingRefinedSquare_gram (f : H' → H)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (z : H' × (Ω × (Fin a × Fin p))) :
    (pendingRefinedSquare P f K₀ z)ᴴ * pendingRefinedSquare P f K₀ z =
      (Fintype.card (Fin a × Fin p) : ℝ) •
        ((pendingKraus P f K₀ (z.1, z.2.1) z.2.2)ᴴ *
          pendingKraus P f K₀ (z.1, z.2.1) z.2.2) := by
  rw [pendingRefinedSquare, QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus_gram _ _
    (by positivity), pendingSquare_gram]

theorem pendingRefinedRecovery_square_action (f : H' → H)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (z : H' × (Ω × (Fin a × Fin p)))
    (X : Matrix (Fin a) (Fin a) ℂ) :
    (pendingRefinedRecovery P f K₀ z).map
      (pendingRefinedSquare P f K₀ z * X * (pendingRefinedSquare P f K₀ z)ᴴ) =
      (Fintype.card (Fin a × Fin p) : ℝ) •
        (pendingKraus P f K₀ (z.1, z.2.1) z.2.2 * X *
          (pendingKraus P f K₀ (z.1, z.2.1) z.2.2)ᴴ) := by
  have hs : pendingRefinedSquare P f K₀ z * X * (pendingRefinedSquare P f K₀ z)ᴴ =
      (Fintype.card (Fin a × Fin p) : ℝ) •
        (pendingSquare P f K₀ (z.1, z.2.1) z.2.2 * X *
          (pendingSquare P f K₀ (z.1, z.2.1) z.2.2)ᴴ) := by
    simp only [pendingRefinedSquare, QuantumProver.ElegantJointMeasurement.ContinuousInstrumentQuadrature.weightedKraus,
      Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Real.mul_self_sqrt (show 0 ≤ (Fintype.card (Fin a × Fin p) : ℝ) by positivity)]
  rw [hs, LinearMap.map_smul_of_tower]
  exact congrArg ((Fintype.card (Fin a × Fin p) : ℝ) • ·)
    (pendingRecovery_square_action P f K₀ _ _ X)

theorem pending_refined_sum_action (f : H' → H)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (h : H') (ω : Ω)
    (X : Matrix (Fin a) (Fin a) ℂ) :
    (∑ q, (pendingRefinedRecovery P f K₀ (h, (ω, q))).map
      (pendingRefinedSquare P f K₀ (h, (ω, q)) * X *
        (pendingRefinedSquare P f K₀ (h, (ω, q)))ᴴ)) =
      (Fintype.card (Fin a × Fin p) : ℝ) •
        P.cpDensity (f h) ω ((QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField
          (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ h).map X) := by
  simp_rw [pendingRefinedRecovery_square_action, ← Finset.smul_sum]
  exact congrArg ((Fintype.card (Fin a × Fin p) : ℝ) • ·)
    (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus_matrix_action _
      (pendingDensity_completelyPositive P f K₀) (h, ω) X).symm

theorem integrable_pendingKraus_gram (f : H' → H) (hf : Measurable f)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (hK₀ : Measurable K₀)
    (h : H') (q : Fin a × Fin p) :
    Integrable (fun ω => (pendingKraus P f K₀ (h, ω) q)ᴴ * pendingKraus P f K₀ (h, ω) q)
      (P.measureKernel (f h)) := by
  have hm : CoordinateMeasurable (fun ω => pendingDensity P f K₀ (h, ω)) :=
    fun i j b c => (pendingDensity_coordinateMeasurable P f hf K₀ hK₀ i j b c).comp
      (measurable_const.prodMk measurable_id)
  exact QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.integrable_canonicalKraus_gram _ _ hm
    (fun ω => pendingDensity_completelyPositive P f K₀ (h, ω))
    (pendingDensity_matrixTraceComplete P f K₀ h) q

theorem integrable_pendingKraus_action (f : H' → H) (hf : Measurable f)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (hK₀ : Measurable K₀)
    (h : H') (q : Fin a × Fin p) (X : Matrix (Fin a) (Fin a) ℂ) :
    Integrable (fun ω => pendingKraus P f K₀ (h, ω) q * X *
      (pendingKraus P f K₀ (h, ω) q)ᴴ) (P.measureKernel (f h)) := by
  have hm : Measurable (fun ω => pendingKraus P f K₀ (h, ω) q) :=
    (measurable_pendingKraus P f hf K₀ hK₀ q).comp (measurable_const.prodMk measurable_id)
  have haction : Measurable (fun K : Matrix (Fin p) (Fin a) ℂ => K * X * Kᴴ) :=
    ((continuous_id.matrix_mul continuous_const).matrix_mul
      continuous_id.matrix_conjTranspose).measurable
  apply ((integrable_pendingKraus_gram P f hf K₀ hK₀ h q).norm.const_mul ‖X‖).mono'
  · exact (haction.comp hm).stronglyMeasurable.aestronglyMeasurable
  · exact Eventually.of_forall fun ω => norm_rectangular_sandwich_le _ X

theorem integrable_pendingRefinedSquare_gram (f : H' → H) (hf : Measurable f)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (hK₀ : Measurable K₀) (h : H') :
    Integrable (fun r => (pendingRefinedSquare P f K₀ (h, r))ᴴ *
      pendingRefinedSquare P f K₀ (h, r)) (pendingRefinedKernel P f hf K₀ h) := by
  rw [pendingRefinedKernel_apply]
  apply integrable_prod_uniform_columns
  intro q
  simp_rw [pendingRefinedSquare_gram]
  exact Integrable.smul (Fintype.card (Fin a × Fin p) : ℝ)
    (integrable_pendingKraus_gram P f hf K₀ hK₀ h q)

theorem integrable_pendingRefinedRecovery_action (f : H' → H) (hf : Measurable f)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (hK₀ : Measurable K₀) (h : H')
    (X : Matrix (Fin a) (Fin a) ℂ) :
    Integrable (fun r => (pendingRefinedRecovery P f K₀ (h, r)).map
      (pendingRefinedSquare P f K₀ (h, r) * X * (pendingRefinedSquare P f K₀ (h, r))ᴴ))
      (pendingRefinedKernel P f hf K₀ h) := by
  rw [pendingRefinedKernel_apply]
  apply integrable_prod_uniform_columns
  intro q
  simp_rw [pendingRefinedRecovery_square_action]
  exact Integrable.smul (Fintype.card (Fin a × Fin p) : ℝ)
    (integrable_pendingKraus_action P f hf K₀ hK₀ h q X)

theorem pending_refined_integral_squareGram (f : H' → H) (hf : Measurable f)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (hK₀ : Measurable K₀) (h : H') :
    (∫ r, (pendingRefinedSquare P f K₀ (h, r))ᴴ * pendingRefinedSquare P f K₀ (h, r)
      ∂pendingRefinedKernel P f hf K₀ h) = 1 := by
  have hc : (Fintype.card (Fin a × Fin p) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Fin a × Fin p)).ne'
  have hi (q : Fin a × Fin p) : Integrable (fun ω =>
      (pendingRefinedSquare P f K₀ (h, (ω, q)))ᴴ * pendingRefinedSquare P f K₀ (h, (ω, q)))
      (P.measureKernel (f h)) := by
    simp_rw [pendingRefinedSquare_gram]
    exact Integrable.smul (Fintype.card (Fin a × Fin p) : ℝ)
      (integrable_pendingKraus_gram P f hf K₀ hK₀ h q)
  rw [pendingRefinedKernel_apply, integral_prod_uniform_columns _ _ hi]
  simp_rw [pendingRefinedSquare_gram, ← Finset.smul_sum]
  rw [integral_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hm : CoordinateMeasurable (fun ω => pendingDensity P f K₀ (h, ω)) :=
    fun i j b c => (pendingDensity_coordinateMeasurable P f hf K₀ hK₀ i j b c).comp
      (measurable_const.prodMk measurable_id)
  exact QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.integral_canonicalGram_eq_one _ _ hm
    (fun ω => pendingDensity_completelyPositive P f K₀ (h, ω))
    (pendingDensity_matrixTraceComplete P f K₀ h)

theorem pending_refined_setIntegral_recovered (f : H' → H) (hf : Measurable f)
    (K₀ : H' → Matrix (Fin m) (Fin a) ℂ) (hK₀ : Measurable K₀)
    (h : H') (B : Set Ω) (hB : MeasurableSet B) (X : Matrix (Fin a) (Fin a) ℂ) :
    (∫ r in B ×ˢ (Set.univ : Set (Fin a × Fin p)),
      (pendingRefinedRecovery P f K₀ (h, r)).map
        (pendingRefinedSquare P f K₀ (h, r) * X * (pendingRefinedSquare P f K₀ (h, r))ᴴ)
      ∂pendingRefinedKernel P f hf K₀ h) =
      P.map (f h) B ((QuantumProver.ElegantJointMeasurement.CP.pendingRecoveryField
        (Nat.pos_of_ne_zero (NeZero.ne m)) K₀ h).map X) := by
  have hc : (Fintype.card (Fin a × Fin p) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Fin a × Fin p)).ne'
  have hi (q : Fin a × Fin p) : Integrable (fun ω =>
      (pendingRefinedRecovery P f K₀ (h, (ω, q))).map
        (pendingRefinedSquare P f K₀ (h, (ω, q)) * X *
          (pendingRefinedSquare P f K₀ (h, (ω, q)))ᴴ))
      ((P.measureKernel (f h)).restrict B) := by
    simp_rw [pendingRefinedRecovery_square_action]
    exact Integrable.smul (Fintype.card (Fin a × Fin p) : ℝ)
      ((integrable_pendingKraus_action P f hf K₀ hK₀ h q X).integrableOn (s := B))
  rw [pendingRefinedKernel_apply, ← Measure.prod_restrict B Set.univ, Measure.restrict_univ,
    integral_prod_uniform_columns _ _ hi]
  simp_rw [pendingRefinedRecovery_square_action, ← Finset.smul_sum]
  rw [integral_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have he : (fun ω => ∑ q, pendingKraus P f K₀ (h, ω) q * X *
      (pendingKraus P f K₀ (h, ω) q)ᴴ) = (fun ω => pendingDensity P f K₀ (h, ω) X) :=
    funext (fun ω => (QuantumProver.ElegantJointMeasurement.ContinuousCPInstruments.canonicalKraus_matrix_action _
      (pendingDensity_completelyPositive P f K₀) (h, ω) X).symm)
  rw [he]
  exact pendingDensity_setIntegral P f K₀ h B hB X

end PhysicalReferenceAbsorption

section RecoveryNormBound

open scoped Kronecker

private theorem norm_sandwich_le_gram {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (K : Matrix O I ℂ) (X : Matrix I I ℂ) :
    ‖K * X * Kᴴ‖ ≤ ‖X‖ * ‖Kᴴ * K‖ := by
  calc
    ‖K * X * Kᴴ‖ ≤ ‖K * X‖ * ‖Kᴴ‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖K‖ * ‖X‖) * ‖Kᴴ‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul K X) (norm_nonneg _)
    _ = ‖X‖ * ‖Kᴴ * K‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose_mul_self]
      ring

theorem norm_cp_tp_apply_le_card {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O]
    (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) (hΦ : QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive Φ)
    (hTP : ∀ X, (Φ X).trace = X.trace) (X : Matrix I I ℂ) :
    ‖Φ X‖ ≤ (Fintype.card I : ℝ) * ‖X‖ := by
  have hcomplete : (∑ q : I × O, (QuantumProver.ElegantJointMeasurement.CP.krausOperator Φ q)ᴴ * QuantumProver.ElegantJointMeasurement.CP.krausOperator Φ q) = 1 := by
    apply (QuantumProver.ElegantJointMeasurement.CP.krausMap_trace_preserving_iff _).mp
    intro Y
    rw [← QuantumProver.ElegantJointMeasurement.CP.completelyPositive_eq_krausMap Φ hΦ]
    exact hTP Y
  have ht : (∑ q : I × O,
      ((QuantumProver.ElegantJointMeasurement.CP.krausOperator Φ q)ᴴ * QuantumProver.ElegantJointMeasurement.CP.krausOperator Φ q).trace.re) =
      (Fintype.card I : ℝ) := by
    have he := congrArg (fun Y : Matrix I I ℂ => Y.trace.re) hcomplete
    simpa [Matrix.trace_sum] using he
  rw [QuantumProver.ElegantJointMeasurement.CP.completelyPositive_apply_eq_sum Φ hΦ X]
  calc
    ‖∑ q : I × O, QuantumProver.ElegantJointMeasurement.CP.krausOperator Φ q * X * (QuantumProver.ElegantJointMeasurement.CP.krausOperator Φ q)ᴴ‖ ≤
        ∑ q : I × O, ‖QuantumProver.ElegantJointMeasurement.CP.krausOperator Φ q * X * (QuantumProver.ElegantJointMeasurement.CP.krausOperator Φ q)ᴴ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q : I × O, ‖X‖ *
        ((QuantumProver.ElegantJointMeasurement.CP.krausOperator Φ q)ᴴ * QuantumProver.ElegantJointMeasurement.CP.krausOperator Φ q).trace.re := by
      apply Finset.sum_le_sum
      intro q _
      exact (norm_sandwich_le_gram _ X).trans
        (mul_le_mul_of_nonneg_left (QuantumProver.ElegantJointMeasurement.CP.posSemidef_norm_le_trace _
          (Matrix.posSemidef_conjTranspose_mul_self _)) (norm_nonneg X))
    _ = (Fintype.card I : ℝ) * ‖X‖ := by
      rw [← Finset.mul_sum, ht, mul_comm]

theorem norm_localRecovery_apply_le (R : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery m p)
    (X : Matrix (Fin m) (Fin m) ℂ) : ‖R.map X‖ ≤ (m : ℝ) * ‖X‖ := by
  simpa using norm_cp_tp_apply_le_card R.map R.completelyPositive R.trace_preserving X

theorem leftApplication_completelyPositive {i o r : ℕ}
    (Φ : Matrix (Fin i) (Fin i) ℂ →ₗ[ℂ] Matrix (Fin o) (Fin o) ℂ)
    (hΦ : QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive Φ) :
    QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.leftApplication (n := r) Φ) := by
  have he : QuantumProver.ElegantJointMeasurement.CP.leftApplication (n := r) Φ =
      QuantumProver.ElegantJointMeasurement.CP.krausMap (fun q : Fin i × Fin o =>
        QuantumProver.ElegantJointMeasurement.CP.krausOperator Φ q ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)) := by
    apply LinearMap.ext
    intro X
    exact QuantumProver.ElegantJointMeasurement.CP.leftApplication_eq_kraus Φ hΦ X
  rw [he]
  exact QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive _

theorem rightApplication_completelyPositive {i o r : ℕ}
    (Φ : Matrix (Fin i) (Fin i) ℂ →ₗ[ℂ] Matrix (Fin o) (Fin o) ℂ)
    (hΦ : QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive Φ) :
    QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.rightApplication (m := r) Φ) := by
  have he : QuantumProver.ElegantJointMeasurement.CP.rightApplication (m := r) Φ =
      QuantumProver.ElegantJointMeasurement.CP.krausMap (fun q : Fin i × Fin o =>
        (1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ QuantumProver.ElegantJointMeasurement.CP.krausOperator Φ q) := by
    apply LinearMap.ext
    intro X
    exact QuantumProver.ElegantJointMeasurement.CP.rightApplication_eq_kraus Φ hΦ X
  rw [he]
  exact QuantumProver.ElegantJointMeasurement.CP.krausMap_completelyPositive _

theorem pendingApplication_completelyPositive {a b c d : ℕ}
    (RA : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery a c) (RB : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery b d) :
    QuantumProver.ElegantJointMeasurement.CP.CompletelyPositive (QuantumProver.ElegantJointMeasurement.CP.pendingApplication RA RB) :=
  (rightApplication_completelyPositive RB.map RB.completelyPositive).comp
    (leftApplication_completelyPositive RA.map RA.completelyPositive)

theorem norm_pendingApplication_apply_le {a b c d : ℕ}
    (RA : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery a c) (RB : QuantumProver.ElegantJointMeasurement.CP.LocalRecovery b d)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    ‖QuantumProver.ElegantJointMeasurement.CP.pendingApplication RA RB X‖ ≤ ((a * b : ℕ) : ℝ) * ‖X‖ := by
  simpa using norm_cp_tp_apply_le_card (QuantumProver.ElegantJointMeasurement.CP.pendingApplication RA RB)
    (pendingApplication_completelyPositive RA RB) (QuantumProver.ElegantJointMeasurement.CP.pendingApplication_trace RA RB) X

theorem integrable_recoveryField_action {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (R : Z → QuantumProver.ElegantJointMeasurement.CP.LocalRecovery m p)
    (hR : QuantumProver.ElegantJointMeasurement.CP.MatrixUnitMeasurable (fun z => (R z).map))
    (X : Z → Matrix (Fin m) (Fin m) ℂ) (hX : Measurable X) (hiX : Integrable X μ) :
    Integrable (fun z => (R z).map (X z)) μ := by
  apply (hiX.norm.const_mul (m : ℝ)).mono'
  · exact (QuantumProver.ElegantJointMeasurement.CP.measurable_matrixMap_apply _ hR X hX).stronglyMeasurable.aestronglyMeasurable
  · exact Eventually.of_forall fun z => norm_localRecovery_apply_le (R z) (X z)

end RecoveryNormBound

end

end QuantumProver.ElegantJointMeasurement.HilbertInstrumentSquare
