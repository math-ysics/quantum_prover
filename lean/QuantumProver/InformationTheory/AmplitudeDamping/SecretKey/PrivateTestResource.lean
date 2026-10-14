import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ProtocolReadout
import QuantumProver.LinearAlgebra.SandwichedDPI.Interpolation
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.BlockIncrement

set_option autoImplicit false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.AmplitudeDamping.SecretKey.PrivateTestResource

open QuantumProver.AmplitudeDamping.FiniteModel (SupportLE sandwichedTrace sandwichedDivergence)

variable {I O J : Type*} [Fintype I] [Fintype O] [Fintype J]
  [DecidableEq I] [DecidableEq O]

theorem channel_divergence_le (C : KrausChannel I O J) (ρ σ : Density I)
    {α : ℝ} (hα : 1 < α) :
    sandwichedDivergence α (C.onDensity ρ).mat (C.onDensity σ).mat ≤
      sandwichedDivergence α ρ.mat σ.mat :=
  QuantumProver.SandwichedDPI.sandwichedDivergence_krausAction_le C.op C.complete
    ρ.positive σ.positive hα

theorem channel_trace_le (C : KrausChannel I O J) (ρ σ : Density I)
    (hs : SupportLE ρ.mat σ.mat) {α : ℝ} (hα : 1 < α) :
    sandwichedTrace α (C.onDensity ρ).mat (C.onDensity σ).mat ≤
      sandwichedTrace α ρ.mat σ.mat :=
  QuantumProver.SandwichedDPI.sandwichedTrace_krausAction_le C.op C.complete
    ρ.positive σ.positive hs hα

section Diagonal

variable {K : Type*} [Fintype K] [DecidableEq K]

theorem diagonal_real_posSemidef (a : K → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (Matrix.diagonal (fun i => (a i : ℂ))).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  exact Complex.nonneg_iff.mpr ⟨ha i, by simp⟩

theorem rpow_diagonal_real (a : K → ℝ) (ha : ∀ i, 0 ≤ a i) (t : ℝ) :
    CFC.rpow (Matrix.diagonal (fun i => (a i : ℂ))) t =
      Matrix.diagonal (fun i => ((a i ^ t : ℝ) : ℂ)) := by
  have heq : CFC.rpow (Matrix.diagonal (fun i => (a i : ℂ))) t =
      cfc (fun x : ℝ => x ^ t) (Matrix.diagonal (fun i => (a i : ℂ))) :=
    CFC.rpow_eq_cfc_real (A := Matrix K K ℂ)
      (a := Matrix.diagonal (fun i => (a i : ℂ))) (y := t)
      (diagonal_real_posSemidef a ha).nonneg
  exact heq.trans (QuantumProver.AmplitudeDamping.TensorPower.cfc_diagonal_real
    (fun x => x ^ t) a)

theorem diagonal_sandwich (a b : K → ℝ) (t : ℝ) :
    Matrix.diagonal (fun i => ((b i ^ t : ℝ) : ℂ)) * Matrix.diagonal (fun i => (a i : ℂ)) *
      Matrix.diagonal (fun i => ((b i ^ t : ℝ) : ℂ)) =
      Matrix.diagonal (fun i => ((b i ^ t * a i * b i ^ t : ℝ) : ℂ)) := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  push_cast
  rfl

theorem sandwichedTrace_diagonal (a b : K → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (α : ℝ) :
    sandwichedTrace α (Matrix.diagonal (fun i => (a i : ℂ)))
      (Matrix.diagonal (fun i => (b i : ℂ))) =
      ∑ i, (b i ^ ((1 - α) / (2 * α)) * a i * b i ^ ((1 - α) / (2 * α))) ^ α := by
  unfold sandwichedTrace
  rw [rpow_diagonal_real b hb]
  dsimp only
  rw [diagonal_sandwich]
  rw [rpow_diagonal_real _ (fun i =>
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (hb i) _) (ha i))
      (Real.rpow_nonneg (hb i) _))]
  simp only [Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re]

theorem scalar_sandwich_power {a b α : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hα : 1 < α) :
    (b ^ ((1 - α) / (2 * α)) * a * b ^ ((1 - α) / (2 * α))) ^ α =
      a ^ α * b ^ (1 - α) := by
  let t := (1 - α) / (2 * α)
  have hα0 : α ≠ 0 := by linarith
  calc
    _ = (a * (b ^ t * b ^ t)) ^ α := by congr 1; ring
    _ = (a * b ^ (t + t)) ^ α := by rw [← Real.rpow_add hb]
    _ = a ^ α * b ^ ((t + t) * α) := by
      rw [Real.mul_rpow ha (Real.rpow_nonneg hb.le _), ← Real.rpow_mul hb.le]
    _ = _ := by
      congr 2
      dsimp only [t]
      field_simp
      ring

end Diagonal

section PrivateBinary

variable {d : ℕ} {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

open PrivateTest

def binaryWeights (a : ℝ) : Fin 2 → ℝ := fun i => if i = 0 then a else 1 - a

theorem binaryWeights_nonneg {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    ∀ i, 0 ≤ binaryWeights a i := by
  intro i
  unfold binaryWeights
  split_ifs <;> linarith [ha.1, ha.2]

theorem privacyBinaryChannel_diagonal_real
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ : Density ((Fin d × A) × (Fin d × B))) :
    ((privacyBinaryChannel U hd).onDensity ρ).mat =
      Matrix.diagonal (fun i => (binaryWeights (privacyAcceptance U ρ.mat) i : ℂ)) := by
  let T := (privacyBinaryChannel U hd).onDensity ρ
  have hdiag : T.mat = Matrix.diagonal (fun i => T.mat i i) := by
    change (privacyBinaryChannel U hd).eval ρ.mat =
      Matrix.diagonal (fun i => ((privacyBinaryChannel U hd).eval ρ.mat) i i)
    simp only [privacyBinaryChannel_eval, Matrix.diagonal_apply_eq]
  have hzero : (T.mat 0 0).re = privacyAcceptance U ρ.mat := privacyBinaryChannel_pass U hd ρ.mat
  have hsum : T.mat 0 0 + T.mat 1 1 = 1 := by
    simpa only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] using T.normalized
  rw [hdiag]
  congr 1
  funext i
  apply Complex.ext
  · fin_cases i
    · change (T.mat 0 0).re = privacyAcceptance U ρ.mat
      exact hzero
    · have hr := congrArg Complex.re hsum
      simp only [Complex.add_re, Complex.one_re, hzero] at hr
      change (T.mat 1 1).re = 1 - privacyAcceptance U ρ.mat
      linarith
  · simpa only [Complex.ofReal_im] using
      (Complex.nonneg_iff.mp (T.positive.diag_nonneg (i := i))).2.symm

theorem supported_binary_pass_positive {a b : ℝ}
    (hs : SupportLE (Matrix.diagonal (fun i => (binaryWeights a i : ℂ)))
      (Matrix.diagonal (fun i => (binaryWeights b i : ℂ))))
    (hb : 0 ≤ b) (ha : 0 < a) : 0 < b := by
  by_contra hn
  have hb0 : b = 0 := le_antisymm (le_of_not_gt hn) hb
  obtain ⟨F, hF⟩ := hs.exists_right_factor
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hF
  simp [Matrix.diagonal_mul, binaryWeights, hb0] at h
  have ha0 : a = 0 := by exact_mod_cast h
  linarith

theorem binary_pass_trace_bound {a b α : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hs : SupportLE (Matrix.diagonal (fun i => (binaryWeights a i : ℂ)))
      (Matrix.diagonal (fun i => (binaryWeights b i : ℂ)))) (hα : 1 < α) :
    a ^ α ≤ b ^ (α - 1) * sandwichedTrace α
      (Matrix.diagonal (fun i => (binaryWeights a i : ℂ)))
      (Matrix.diagonal (fun i => (binaryWeights b i : ℂ))) := by
  have hnonneg : 0 ≤ sandwichedTrace α
      (Matrix.diagonal (fun i => (binaryWeights a i : ℂ)))
      (Matrix.diagonal (fun i => (binaryWeights b i : ℂ))) := by
    rw [sandwichedTrace_diagonal _ _ (binaryWeights_nonneg ha) (binaryWeights_nonneg hb)]
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg (binaryWeights_nonneg hb i) _)
        (binaryWeights_nonneg ha i)) (Real.rpow_nonneg (binaryWeights_nonneg hb i) _)) _
  by_cases ha0 : a = 0
  · subst a
    rw [Real.zero_rpow (by linarith : α ≠ 0)]
    exact mul_nonneg (Real.rpow_nonneg hb.1 _) hnonneg
  · have hap : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
    have hbp := supported_binary_pass_positive hs hb.1 hap
    have hQ : a ^ α * b ^ (1 - α) ≤ sandwichedTrace α
        (Matrix.diagonal (fun i => (binaryWeights a i : ℂ)))
        (Matrix.diagonal (fun i => (binaryWeights b i : ℂ))) := by
      rw [sandwichedTrace_diagonal _ _ (binaryWeights_nonneg ha) (binaryWeights_nonneg hb),
        Fin.sum_univ_two]
      simp only [binaryWeights, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
      rw [scalar_sandwich_power ha.1 hbp hα]
      exact le_add_of_nonneg_right (Real.rpow_nonneg
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg (binaryWeights_nonneg hb 1) _)
          (binaryWeights_nonneg ha 1)) (Real.rpow_nonneg (binaryWeights_nonneg hb 1) _)) _)
    have hcancel : b ^ (α - 1) * b ^ (1 - α) = 1 := by
      rw [← Real.rpow_add hbp]
      simp
    calc
      a ^ α = b ^ (α - 1) * (a ^ α * b ^ (1 - α)) := by rw [mul_left_comm, hcancel, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hQ (Real.rpow_nonneg hb.1 _)

theorem privacy_separable_trace_bound
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ σ : Density ((Fin d × A) × (Fin d × B)))
    (hσ : IsSeparable σ) (hs : SupportLE ρ.mat σ.mat) {α : ℝ} (hα : 1 < α) :
    (d : ℝ) ^ (α - 1) * privacyAcceptance U ρ.mat ^ α ≤ sandwichedTrace α ρ.mat σ.mat := by
  let C := privacyBinaryChannel U hd
  have hr := privacyAcceptance_density_mem_Icc U hd ρ
  have hq := privacyAcceptance_density_mem_Icc U hd σ
  have hsout : SupportLE (C.onDensity ρ).mat (C.onDensity σ).mat :=
    QuantumProver.SandwichedDPI.supportLE_krausAction C.op ρ.positive σ.positive hs
  rw [privacyBinaryChannel_diagonal_real U hd ρ,
    privacyBinaryChannel_diagonal_real U hd σ] at hsout
  have htest := binary_pass_trace_bound hr hq hsout hα
  rw [← privacyBinaryChannel_diagonal_real U hd ρ,
    ← privacyBinaryChannel_diagonal_real U hd σ] at htest
  have hQ := channel_trace_le C ρ σ hs hα
  have hnonneg := QuantumProver.SandwichedDPI.sandwichedTrace_pos_of_supportLE
    ρ.positive σ.positive hs (by
      intro hz
      have ht := ρ.normalized
      rw [hz, Matrix.trace_zero] at ht
      exact zero_ne_one ht) hα
  have hqpow : privacyAcceptance U σ.mat ^ (α - 1) ≤ (1 / (d : ℝ)) ^ (α - 1) :=
    Real.rpow_le_rpow hq.1 (privacyAcceptance_separable_le U σ hσ) (by linarith)
  have ht : privacyAcceptance U ρ.mat ^ α ≤
      (1 / (d : ℝ)) ^ (α - 1) * sandwichedTrace α ρ.mat σ.mat :=
    htest.trans ((mul_le_mul_of_nonneg_left hQ (Real.rpow_nonneg hq.1 _)).trans
      (mul_le_mul_of_nonneg_right hqpow hnonneg.le))
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hcancel : (d : ℝ) ^ (α - 1) * (1 / (d : ℝ)) ^ (α - 1) = 1 := by
    rw [one_div, Real.inv_rpow hdR.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hdR _).ne']
  calc
    _ ≤ (d : ℝ) ^ (α - 1) *
        ((1 / (d : ℝ)) ^ (α - 1) * sandwichedTrace α ρ.mat σ.mat) :=
      mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hdR.le _)
    _ = _ := by rw [← mul_assoc, hcancel, one_mul]

end PrivateBinary

section NormalizedSEP

variable {A B A' B' Z : Type*}
  [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] [Fintype Z]
  [DecidableEq A] [DecidableEq B] [DecidableEq A'] [DecidableEq B']

def normalizedSEPEntanglement (α : ℝ) (ρ : Density (A × B)) : EReal :=
  sInf ((fun σ : Density (A × B) => sandwichedDivergence α ρ.mat σ.mat) ''
    {σ : Density (A × B) | IsSeparable σ})

theorem normalizedSEPEntanglement_le_comparison (α : ℝ) (ρ σ : Density (A × B))
    (hσ : IsSeparable σ) :
    normalizedSEPEntanglement α ρ ≤ sandwichedDivergence α ρ.mat σ.mat :=
  sInf_le ⟨σ, hσ, rfl⟩

def localProductChannel (K : Z → Matrix A' A ℂ) (L : Z → Matrix B' B ℂ)
    (hKL : ∑ z, (K z ⊗ₖ L z)ᴴ * (K z ⊗ₖ L z) = 1) :
    KrausChannel (A × B) (A' × B') Z where
  op z := K z ⊗ₖ L z
  complete := hKL

theorem localProductChannel_separable (K : Z → Matrix A' A ℂ)
    (L : Z → Matrix B' B ℂ)
    (hKL : ∑ z, (K z ⊗ₖ L z)ᴴ * (K z ⊗ₖ L z) = 1)
    (σ : Density (A × B)) (hσ : IsSeparable σ) :
    IsSeparable ((localProductChannel K L hKL).onDensity σ) := by
  change InSeparableCone (∑ z, (K z ⊗ₖ L z) * σ.mat * (K z ⊗ₖ L z)ᴴ)
  exact separableCone_finite_sum_B _ (fun z => separableCone_local_product_B (K z) (L z) hσ)

theorem normalizedSEPEntanglement_localProductChannel_le
    (K : Z → Matrix A' A ℂ) (L : Z → Matrix B' B ℂ)
    (hKL : ∑ z, (K z ⊗ₖ L z)ᴴ * (K z ⊗ₖ L z) = 1)
    (ρ : Density (A × B)) {α : ℝ} (hα : 1 < α) :
    normalizedSEPEntanglement α ((localProductChannel K L hKL).onDensity ρ) ≤
      normalizedSEPEntanglement α ρ := by
  unfold normalizedSEPEntanglement
  apply le_sInf
  rintro x ⟨σ, hσ, rfl⟩
  exact (normalizedSEPEntanglement_le_comparison α
    ((localProductChannel K L hKL).onDensity ρ) ((localProductChannel K L hKL).onDensity σ)
    (localProductChannel_separable K L hKL σ hσ)).trans
      (channel_divergence_le _ ρ σ hα)

theorem quantumSEP_mem_matrixCone {a b : ℕ}
    {σ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ}
    (hσ : QuantumProver.AmplitudeDamping.FiniteModel.IsSeparable a b σ) : InSeparableCone σ := by
  obtain ⟨k, t, X, Y, ht, _htrace, hXY, hσ⟩ := hσ
  refine ⟨k, (fun j => (t j) • X j), Y,
    (fun j => ((hXY j).1.1).smul (ht j)), (fun j => (hXY j).2.1), ?_⟩
  rw [hσ]
  apply Finset.sum_congr rfl
  intro j _
  ext x y
  simp [Matrix.kroneckerMap_apply, Matrix.smul_apply, Complex.real_smul,
    smul_eq_mul, mul_assoc]

theorem normalizedSEPEntanglement_le_quantum {a b : ℕ}
    (ρ : Density (Fin a × Fin b)) (α : ℝ) :
    normalizedSEPEntanglement α ρ ≤
      QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement α a b ρ.mat := by
  unfold QuantumProver.AmplitudeDamping.FiniteModel.sandwichedEntanglement
  apply le_sInf
  rintro x ⟨σ, ⟨hσdensity, hσsep⟩, rfl⟩
  exact normalizedSEPEntanglement_le_comparison α ρ
    ⟨σ, hσdensity.1, hσdensity.2⟩ (quantumSEP_mem_matrixCone hσsep)

end NormalizedSEP

section LocalPrivateLift

open PhysicalPurification PrivateTest

variable {A B R E : Type*} [Fintype A] [Fintype B] [Fintype R] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq R] [DecidableEq E]
  {d : ℕ}

theorem partialTraceRight_eval_withRightMemory
    {I O J : Type*} [Fintype I] [Fintype O] [Fintype J]
    [DecidableEq I] [DecidableEq O]
    (C : KrausChannel I O J) (ρ : Matrix (I × E) (I × E) ℂ) :
    partialTraceRight ((C.withRightMemory E).eval ρ) = C.eval (partialTraceRight ρ) := by
  have hsum : partialTraceRight ρ = ∑ e : E, Matrix.of (fun i j => ρ (i,e) (j,e)) := by
    ext i j
    simp only [partialTraceRight, Matrix.sum_apply, Matrix.of_apply]
  rw [hsum, C.eval_finite_sum_B]
  ext o o'
  simp only [partialTraceRight, Matrix.sum_apply, eval_withRightMemory_apply]
  rfl

theorem honestMarginal_onDensity_withRightMemory
    {I O J : Type*} [Fintype I] [Fintype O] [Fintype J]
    [DecidableEq I] [DecidableEq O]
    (C : KrausChannel I O J) (ρ : Density (I × E)) :
    honestMarginal ((C.withRightMemory E).onDensity ρ) = C.onDensity (honestMarginal ρ) := by
  apply Density.eq_of_mat_eq
  exact partialTraceRight_eval_withRightMemory C ρ.mat

theorem normalizedSEPEntanglement_keyRecording_le
    (labelA : A → Fin d) (labelB : B → Fin d) (ρ : Density (A × B))
    {α : ℝ} (hα : 1 < α) :
    normalizedSEPEntanglement α ((keyRecordingChannel labelA labelB).onDensity ρ) ≤
      normalizedSEPEntanglement α ρ :=
  normalizedSEPEntanglement_localProductChannel_le
    (fun _ : Unit => labelRecordingMatrix labelA)
    (fun _ : Unit => labelRecordingMatrix labelB)
    (keyRecordingChannel labelA labelB).complete ρ hα

theorem normalizedSEPEntanglement_keyPadding_le
    (ρ : Density ((Fin d × A) × (Fin d × B))) {α : ℝ} (hα : 1 < α) :
    normalizedSEPEntanglement α
      ((keyPaddingChannel (E := R) (d := d) (A := A) (B := B)).onDensity ρ) ≤
      normalizedSEPEntanglement α ρ :=
  normalizedSEPEntanglement_localProductChannel_le
    (fun z : Unit => ((paddingChannel (S := A) (E := R)).withMemory (Fin d)).op z)
    (fun _ : Unit => (1 : Matrix (Fin d × B) (Fin d × B) ℂ))
    (keyPaddingChannel (E := R) (d := d) (A := A) (B := B)).complete ρ hα

end LocalPrivateLift

section RetainedPrivateLift

open PhysicalProtocol PhysicalPurification PrivateTest

variable {p : ℝ} {a b af bf d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

theorem retainedPrivateLift_honest_eq
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (ρ : Density ((Fin a × Fin b) × E)) :
    honestMarginal
      ((P.retainedProtocolPrivateLiftChannel (E := E) hp0 hp1 labelA labelB).onDensity ρ) =
      (keyPaddingChannel (E := P.Environment × E)).onDensity
        ((keyRecordingChannel
          (fun x : P.comparisonPublicHistory_B × Fin af => labelA x.2)
          (fun x : P.comparisonPublicHistory_B × Fin bf => labelB x.2)).onDensity
          (honestMarginal ((PublicHistory.wholeRetainedChannelWithEve_B hp0 hp1 P E).onDensity ρ))) := by
  apply Density.eq_of_mat_eq
  change partialTraceRight
    ((P.retainedProtocolPrivateLiftChannel (E := E) hp0 hp1 labelA labelB).eval ρ.mat) = _
  rw [FiniteKeyProtocol.retainedProtocolPrivateLiftChannel, KrausChannel.eval_compose,
    KrausChannel.eval_compose, partialTraceRight_eval_withRightMemory,
    partialTraceRight_eval_withRightMemory]
  rfl

theorem retainedPrivateLift_resource_le
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (ρ : Density ((Fin a × Fin b) × E)) {α : ℝ} (hα : 1 < α) :
    normalizedSEPEntanglement α (honestMarginal
      ((P.retainedProtocolPrivateLiftChannel (E := E) hp0 hp1 labelA labelB).onDensity ρ)) ≤
      normalizedSEPEntanglement α
        (honestMarginal ((PublicHistory.wholeRetainedChannelWithEve_B hp0 hp1 P E).onDensity ρ)) := by
  rw [retainedPrivateLift_honest_eq]
  exact (normalizedSEPEntanglement_keyPadding_le _ hα).trans
    (normalizedSEPEntanglement_keyRecording_le _ _ _ hα)

end RetainedPrivateLift

section PrivateResource

variable {d : ℕ} {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

open PrivateTest

theorem privacy_separable_divergence_log_bound
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ σ : Density ((Fin d × A) × (Fin d × B)))
    (hσ : IsSeparable σ) (hF : 0 < privacyAcceptance U ρ.mat)
    {α : ℝ} (hα : 1 < α) :
    ((log2 (d : ℝ) + (α / (α - 1)) * log2 (privacyAcceptance U ρ.mat) : ℝ) : EReal) ≤
      sandwichedDivergence α ρ.mat σ.mat := by
  classical
  unfold sandwichedDivergence
  split_ifs with hs
  · apply EReal.coe_le_coe_iff.mpr
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
    have hα1 : 0 < α - 1 := sub_pos.mpr hα
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
    have hpowD : 0 < (d : ℝ) ^ (α - 1) := Real.rpow_pos_of_pos hdR _
    have hpowF : 0 < privacyAcceptance U ρ.mat ^ α := Real.rpow_pos_of_pos hF _
    have hbound := privacy_separable_trace_bound U hd ρ σ hσ hs hα
    have hlog := Real.log_le_log (mul_pos hpowD hpowF) hbound
    rw [Real.log_mul hpowD.ne' hpowF.ne', Real.log_rpow hdR (α - 1),
      Real.log_rpow hF α] at hlog
    calc
      log2 (d : ℝ) + (α / (α - 1)) * log2 (privacyAcceptance U ρ.mat) =
          ((α - 1) * Real.log (d : ℝ) + α * Real.log (privacyAcceptance U ρ.mat)) /
            ((α - 1) * Real.log 2) := by
        unfold log2
        field_simp [hα1.ne', h2.ne']
      _ ≤ Real.log (sandwichedTrace α ρ.mat σ.mat) / ((α - 1) * Real.log 2) :=
        (div_le_div_iff_of_pos_right (mul_pos hα1 h2)).mpr hlog
  · exact le_top

theorem privacy_normalizedSEP_log_bound
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ : Density ((Fin d × A) × (Fin d × B)))
    (hF : 0 < privacyAcceptance U ρ.mat) {α : ℝ} (hα : 1 < α) :
    ((log2 (d : ℝ) + (α / (α - 1)) * log2 (privacyAcceptance U ρ.mat) : ℝ) : EReal) ≤
      normalizedSEPEntanglement α ρ := by
  unfold normalizedSEPEntanglement
  apply le_sInf
  rintro x ⟨σ, hσ, rfl⟩
  exact privacy_separable_divergence_log_bound U hd ρ σ hσ hF hα

theorem privacyAcceptance_le_of_resource_le
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (ρ : Density ((Fin d × A) × (Fin d × B))) {α e : ℝ}
    (hα : 1 < α) (hE : normalizedSEPEntanglement α ρ ≤ (e : EReal)) :
    privacyAcceptance U ρ.mat ≤ min 1 (2 ^ (((α - 1) / α) * (e - log2 (d : ℝ)))) := by
  refine le_min (privacyAcceptance_density_mem_Icc U hd ρ).2 ?_
  by_cases hF : 0 < privacyAcceptance U ρ.mat
  · have hα0 : 0 < α := by linarith
    have hα1 : 0 < α - 1 := sub_pos.mpr hα
    have hlog : log2 (d : ℝ) + (α / (α - 1)) * log2 (privacyAcceptance U ρ.mat) ≤ e :=
      EReal.coe_le_coe_iff.mp ((privacy_normalizedSEP_log_bound U hd ρ hF hα).trans hE)
    have hlogF : log2 (privacyAcceptance U ρ.mat) ≤
        ((α - 1) / α) * (e - log2 (d : ℝ)) := by
      apply (mul_le_mul_iff_of_pos_left (div_pos hα0 hα1)).mp
      have hcancel : (α / (α - 1)) * (((α - 1) / α) * (e - log2 (d : ℝ))) =
          e - log2 (d : ℝ) := by
        field_simp [hα0.ne', hα1.ne']
      rw [hcancel]
      linarith
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num : 1 < (2 : ℝ))
    have hlogF' : Real.log (privacyAcceptance U ρ.mat) ≤
        (((α - 1) / α) * (e - log2 (d : ℝ))) * Real.log 2 :=
      (div_le_iff₀ h2).mp hlogF
    calc
      privacyAcceptance U ρ.mat = Real.exp (Real.log (privacyAcceptance U ρ.mat)) :=
        (Real.exp_log hF).symm
      _ ≤ Real.exp ((((α - 1) / α) * (e - log2 (d : ℝ))) * Real.log 2) :=
        Real.exp_le_exp.mpr hlogF'
      _ = 2 ^ (((α - 1) / α) * (e - log2 (d : ℝ))) := by
        rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ)), mul_comm]
  · exact (le_of_not_gt hF).trans (Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) _)

end PrivateResource

section ProtocolEndpoint

open PhysicalProtocol PhysicalPurification PrivateTest

variable {p : ℝ} {a b af bf d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]

theorem protocol_candidate_le_of_privateLift_resource_le
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1)
    (hd : 0 < d) (xi : Density (P.Environment × E)) {α e : ℝ} (hα : 1 < α)
    (hE : normalizedSEPEntanglement α (honestMarginal
      ((P.retainedProtocolPrivateLiftChannel (E := E) hp0 hp1 labelA labelB).onDensity
        (density C hC))) ≤ (e : EReal)) :
    squaredFidelity
      (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC))
      (idealKeyStateAgainst d hd xi) ≤
      min 1 (2 ^ (((α - 1) / α) * (e - log2 (d : ℝ)))) := by
  obtain ⟨U, hU⟩ := P.exists_private_test_of_protocol_candidate_channel
    hp0 hp1 labelA labelB C hC hd xi
  exact hU.trans (privacyAcceptance_le_of_resource_le U hd _ hα hE)

theorem protocol_keyG_le_of_privateLift_resource_le
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1)
    (hd : 0 < d) {α e : ℝ} (hα : 1 < α)
    (hE : normalizedSEPEntanglement α (honestMarginal
      ((P.retainedProtocolPrivateLiftChannel (E := E) hp0 hp1 labelA labelB).onDensity
        (density C hC))) ≤ (e : EReal)) :
    optimalWholeKeySquaredFidelity d hd
      (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC)) ≤
      min 1 (2 ^ (((α - 1) / α) * (e - log2 (d : ℝ)))) := by
  unfold optimalWholeKeySquaredFidelity
  apply csSup_le
  · exact ⟨_, ⟨(P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC)).marginalRight,
      rfl⟩⟩
  · rintro x ⟨xi, rfl⟩
    exact protocol_candidate_le_of_privateLift_resource_le hp0 hp1 P labelA labelB C hC hd xi hα hE

theorem protocol_keyG_le_of_retained_resource_le
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1)
    (hd : 0 < d) {α e : ℝ} (hα : 1 < α)
    (hE : normalizedSEPEntanglement α
      (honestMarginal ((PublicHistory.wholeRetainedChannelWithEve_B hp0 hp1 P E).onDensity
        (density C hC))) ≤
        (e : EReal)) :
    optimalWholeKeySquaredFidelity d hd
      (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC)) ≤
      min 1 (2 ^ (((α - 1) / α) * (e - log2 (d : ℝ)))) :=
  protocol_keyG_le_of_privateLift_resource_le hp0 hp1 P labelA labelB C hC hd hα
    ((retainedPrivateLift_resource_le hp0 hp1 P labelA labelB _ hα).trans hE)

theorem protocol_keyG_strong_bound_of_retained_resource_le
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (P : FiniteKeyProtocol p a b af bf)
    (labelA : Fin af → Fin d) (labelB : Fin bf → Fin d)
    (C : Matrix (Fin a × Fin b) E ℂ) (hC : (Cᴴ * C).trace = 1)
    (hd : 0 < d) (m : ℕ) (k z : ℝ) (hz0 : 0 < z) (hz1 : z < 1)
    (hE : normalizedSEPEntanglement (1 / (1 - z))
      (honestMarginal ((PublicHistory.wholeRetainedChannelWithEve_B hp0 hp1 P E).onDensity
        (density C hC))) ≤ ((k + (m : ℝ) * channelBz p z : ℝ) : EReal)) :
    optimalWholeKeySquaredFidelity d hd
      (P.finalKeyStateWithPriorEveLabels hp0 hp1 labelA labelB E (density C hC)) ≤
      min 1 ((2 : ℝ) ^ (-z * (log2 (d : ℝ) - k - (m : ℝ) * channelBz p z))) := by
  have hden : 0 < 1 - z := sub_pos.mpr hz1
  have hα : 1 < 1 / (1 - z) := (lt_div_iff₀ hden).mpr (by linarith)
  have hratio : ((1 / (1 - z) - 1) / (1 / (1 - z))) = z := by
    field_simp [hden.ne']
    ring
  have hexp : ((1 / (1 - z) - 1) / (1 / (1 - z))) *
      (k + (m : ℝ) * channelBz p z - log2 (d : ℝ)) =
      -z * (log2 (d : ℝ) - k - (m : ℝ) * channelBz p z) := by
    rw [hratio]
    ring
  simpa only [hexp] using
    protocol_keyG_le_of_retained_resource_le hp0 hp1 P labelA labelB C hC hd hα hE

end ProtocolEndpoint

end QuantumProver.AmplitudeDamping.SecretKey.PrivateTestResource
