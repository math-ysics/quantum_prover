import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.PrivateTestResource
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingConsequences
import QuantumProver.InformationTheory.PetzMeasurementDPI

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable section

open Matrix Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker Topology

namespace QuantumProver.AmplitudeDamping.SecretKey.WeakResourceOrder

open PrivateTestResource
open QuantumProver.AmplitudeDamping.FiniteModel (SupportLE sandwichedTrace sandwichedDivergence)
open QuantumProver.SuperchannelDiscrimination

variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]

theorem weighted_exp_log_renyi (w q : K → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, 0 < q i) (hsum : ∑ i, w i = 1)
    {α : ℝ} (hα : 1 < α) :
    Real.exp ((α - 1) * ∑ i, w i * (Real.log (w i) - Real.log (q i))) ≤
      ∑ i, (w i) ^ α * (q i) ^ (1 - α) := by
  let x : K → ℝ := fun i => (α - 1) * (Real.log (w i) - Real.log (q i))
  have hJ := convexOn_exp.map_sum_le
    (t := Finset.univ) (w := w) (p := x) (fun i _ => hw i) hsum
    (fun i _ => Set.mem_univ (x i))
  have he : (∑ i, w i * x i) =
      (α - 1) * ∑ i, w i * (Real.log (w i) - Real.log (q i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [x]
    ring
  have hterm (i : K) : w i * Real.exp (x i) = (w i) ^ α * (q i) ^ (1 - α) := by
    by_cases hi : w i = 0
    · simp [hi, Real.zero_rpow (by linarith : α ≠ 0)]
    · have hip : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hi)
      rw [Real.rpow_def_of_pos hip, Real.rpow_def_of_pos (hq i)]
      calc
        _ = Real.exp (Real.log (w i) + x i) := by
          rw [Real.exp_add, Real.exp_log hip]
        _ = Real.exp (α * Real.log (w i) + (1 - α) * Real.log (q i)) := by
          congr 1
          dsimp [x]
          ring
        _ = _ := by rw [Real.exp_add]; congr 2 <;> ring
  calc
    _ = Real.exp (∑ i, w i * x i) := congrArg Real.exp he.symm
    _ ≤ ∑ i, w i * Real.exp (x i) := by simpa only [smul_eq_mul] using hJ
    _ = _ := Finset.sum_congr rfl (fun i _ => hterm i)

theorem weighted_log_le_renyi (w q : K → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, 0 < q i) (hsum : ∑ i, w i = 1)
    {α : ℝ} (hα : 1 < α) :
    (∑ i, w i * (Real.log (w i) - Real.log (q i))) / Real.log 2 ≤
      Real.log (∑ i, (w i) ^ α * (q i) ^ (1 - α)) / ((α - 1) * Real.log 2) := by
  have hr : 0 < α - 1 := sub_pos.mpr hα
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := Real.log_le_log (Real.exp_pos _)
    (weighted_exp_log_renyi w q hw hq hsum hα)
  rw [Real.log_exp] at h
  calc
    _ = ((α - 1) * ∑ i, w i * (Real.log (w i) - Real.log (q i))) /
        ((α - 1) * Real.log 2) := by field_simp [hr.ne', h2.ne']
    _ ≤ _ := (div_le_div_iff_of_pos_right (mul_pos hr h2)).mpr h

theorem binary_relativeEntropy_le_log_moment {a b α : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb0 : 0 < b) (hb1 : b < 1) (hα : 1 < α) :
    binaryRelativeEntropyBits a b ≤
      Real.log (∑ i : Fin 2, (binaryWeights a i) ^ α * (binaryWeights b i) ^ (1 - α)) /
        ((α - 1) * Real.log 2) := by
  have hq (i : Fin 2) : 0 < binaryWeights b i := by
    fin_cases i <;> simp [binaryWeights] <;> linarith
  have hsum : ∑ i : Fin 2, binaryWeights a i = 1 := by
    simp [Fin.sum_univ_two, binaryWeights]
  have h := weighted_log_le_renyi (binaryWeights a) (binaryWeights b)
    (binaryWeights_nonneg ha) hq hsum hα
  have he : (∑ i : Fin 2, binaryWeights a i *
      (Real.log (binaryWeights a i) - Real.log (binaryWeights b i))) / Real.log 2 =
      binaryRelativeEntropyBits a b := by
    rw [binaryRelativeEntropyBits, weighted_log_quotient a hb0.ne',
      weighted_log_quotient (1-a) (sub_pos.mpr hb1).ne']
    simp only [Fin.sum_univ_two, binaryWeights, ite_true,
      show (1 : Fin 2) ≠ 0 by decide, ite_false]
    ring
  exact he ▸ h

def binaryMatrix (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => (binaryWeights a i : ℂ))

theorem binary_sandwichedTrace_eq_moment {a b α : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb0 : 0 < b) (hb1 : b < 1) (hα : 1 < α) :
    sandwichedTrace α (binaryMatrix a) (binaryMatrix b) =
      ∑ i : Fin 2, (binaryWeights a i) ^ α * (binaryWeights b i) ^ (1 - α) := by
  rw [binaryMatrix, binaryMatrix,
    sandwichedTrace_diagonal _ _ (binaryWeights_nonneg ha)
      (binaryWeights_nonneg ⟨hb0.le,hb1.le⟩)]
  apply Finset.sum_congr rfl
  intro i _
  have hbi : 0 < binaryWeights b i := by
    fin_cases i <;> simp [binaryWeights] <;> linarith
  exact scalar_sandwich_power (binaryWeights_nonneg ha i) hbi hα

theorem binary_sandwichedTrace_self_endpoint {a α : ℝ}
    (ha : a = 0 ∨ a = 1) (hα : 1 < α) :
    sandwichedTrace α (binaryMatrix a) (binaryMatrix a) = 1 := by
  have hI : a ∈ Set.Icc (0 : ℝ) 1 := by rcases ha with rfl | rfl <;> norm_num
  simp only [binaryMatrix]
  rw [sandwichedTrace_diagonal _ _ (binaryWeights_nonneg hI) (binaryWeights_nonneg hI)]
  rcases ha with rfl | rfl <;>
    simp [Fin.sum_univ_two, binaryWeights, Real.zero_rpow (by linarith : α ≠ 0)]

theorem binary_relativeEntropy_le_sandwichedDivergence {a b α : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) (hα : 1 < α) :
    extendedBinaryRelativeEntropyBits a b ≤
      sandwichedDivergence α (binaryMatrix a) (binaryMatrix b) := by
  classical
  unfold sandwichedDivergence
  split_ifs with hs
  · by_cases hb0 : b = 0
    · have ha0 : a = 0 := by
        by_contra hna
        have hap : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm hna)
        have hbp := supported_binary_pass_positive hs hb.1 hap
        linarith
      subst a
      subst b
      rw [binary_sandwichedTrace_self_endpoint (Or.inl rfl) hα]
      simp [extendedBinaryRelativeEntropyBits]
    · by_cases hb1 : b = 1
      · have ha1 : a = 1 := by
          obtain ⟨F,hF⟩ := hs.exists_right_factor
          have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hF
          have hz : ((1-a : ℝ) : ℂ) = 0 := by
            simpa [binaryMatrix, Matrix.diagonal_mul, binaryWeights, hb1] using he
          have hr : 1-a = 0 := by exact_mod_cast hz
          linarith
        subst a
        subst b
        rw [binary_sandwichedTrace_self_endpoint (Or.inr rfl) hα]
        simp [extendedBinaryRelativeEntropyBits]
      · have hbp : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hb0)
        have hblt : b < 1 := lt_of_le_of_ne hb.2 hb1
        rw [extendedBinaryRelativeEntropyBits, ite_eq_right hb0, ite_eq_right hb1,
          binary_sandwichedTrace_eq_moment ha hbp hblt hα]
        exact EReal.coe_le_coe_iff.mpr (binary_relativeEntropy_le_log_moment ha hbp hblt hα)
  · exact le_top

def binaryEffectPOVM (E : Matrix I I ℂ) (hE : FlaggedStates.IsEffect E) :
    QuantumProver.Equipartition.FiniteModel.FinitePOVM I 2 where
  outcome i := if i = 0 then E else 1-E
  positive := by
    intro i
    by_cases hi : i = 0
    · simp only [ite_eq_left hi]; exact hE.1
    · simp only [ite_eq_right hi]; exact hE.2
  sum_outcome := by simp [Fin.sum_univ_two]

theorem binaryEffectPOVM_action {ρ E : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hE : FlaggedStates.IsEffect E) :
    KrausCompletion.krausAction
      (QuantumProver.PetzMeasurementDPI.measurementKraus (binaryEffectPOVM E hE)) ρ =
      binaryMatrix (FlaggedStates.acceptanceProbability ρ E) := by
  rw [QuantumProver.PetzMeasurementDPI.measurementKraus_action_psd _ hρ.1]
  unfold binaryMatrix
  congr 1
  funext i
  fin_cases i
  · rfl
  · change (((ρ * (1-E)).trace.re : ℝ) : ℂ) =
      ((1-(ρ*E).trace.re : ℝ) : ℂ)
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub,
      Complex.sub_re, hρ.2, Complex.one_re]

theorem effect_binary_relativeEntropy_le_sandwichedDivergence
    {ρ σ E : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ)
    (hσ : FlaggedStates.IsDensity σ) (hE : FlaggedStates.IsEffect E)
    {α : ℝ} (hα : 1 < α) :
    extendedBinaryRelativeEntropyBits (FlaggedStates.acceptanceProbability ρ E)
      (FlaggedStates.acceptanceProbability σ E) ≤ sandwichedDivergence α ρ σ := by
  have h := QuantumProver.SandwichedDPI.sandwichedDivergence_krausAction_le
    (QuantumProver.PetzMeasurementDPI.measurementKraus (binaryEffectPOVM E hE))
    (QuantumProver.PetzMeasurementDPI.measurementKraus_complete _) hρ.1 hσ.1 hα
  rw [binaryEffectPOVM_action hρ hE, binaryEffectPOVM_action hσ hE] at h
  exact (binary_relativeEntropy_le_sandwichedDivergence
    (FlaggedStates.acceptanceProbability_bounds hρ hE)
    (FlaggedStates.acceptanceProbability_bounds hσ hE) hα).trans h

theorem sandwichedDivergence_nonneg_of_density {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    {α : ℝ} (hα : 1 < α) : 0 ≤ sandwichedDivergence α ρ σ := by
  have hE : FlaggedStates.IsEffect (1 : Matrix I I ℂ) :=
    ⟨Matrix.PosSemidef.one, by rw [sub_self]; exact Matrix.PosSemidef.zero⟩
  have h := effect_binary_relativeEntropy_le_sandwichedDivergence hρ hσ hE hα
  simpa [FlaggedStates.acceptanceProbability, hρ.2, hσ.2,
    extendedBinaryRelativeEntropyBits] using h

open TensorPinching (RecursiveRows recursiveTensorPower)

theorem recursiveTensorPower_support {ρ σ : Matrix I I ℂ}
    (hs : SupportLE ρ σ) (n : ℕ) :
    SupportLE (recursiveTensorPower ρ n) (recursiveTensorPower σ n) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact QuantumProver.AmplitudeDamping.FiniteModel.SupportLE.kronecker ih hs

omit [DecidableEq I] in
theorem density_ne_zero {ρ : Matrix I I ℂ} (hρ : FlaggedStates.IsDensity ρ) : ρ ≠ 0 := by
  intro h
  have ht := hρ.2
  rw [h, Matrix.trace_zero] at ht
  exact zero_ne_one ht

theorem recursiveTensorPower_sandwichedDivergence {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    (hs : SupportLE ρ σ) {α B : ℝ} (hα : 1 < α)
    (hD : sandwichedDivergence α ρ σ = (B : EReal)) (n : ℕ) :
    sandwichedDivergence α (recursiveTensorPower ρ n) (recursiveTensorPower σ n) =
      (((n : ℝ) * B : ℝ) : EReal) := by
  induction n with
  | zero =>
      have hs0 : SupportLE (recursiveTensorPower ρ 0) (recursiveTensorPower σ 0) := le_rfl
      have hQ0 : sandwichedTrace α (recursiveTensorPower ρ 0)
          (recursiveTensorPower σ 0) = 1 := by
        simp only [recursiveTensorPower]
        have h1 : (1 : Matrix (RecursiveRows I 0) (RecursiveRows I 0) ℂ) =
            Matrix.diagonal (fun _ => ((1 : ℝ) : ℂ)) := by simp
        rw [h1, sandwichedTrace_diagonal _ _ (fun _ => zero_le_one) (fun _ => zero_le_one)]
        simp only [Real.one_rpow, one_mul]
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul, mul_one]
        let _ : Unique (RecursiveRows I 0) := inferInstanceAs (Unique PUnit)
        exact_mod_cast (Fintype.card_unique (α := RecursiveRows I 0))
      simp [sandwichedDivergence, hs0, hQ0]
  | succ n ih =>
      have hρn := PetzTensorTail.recursiveTensorPower_density hρ n
      have hσn := PetzTensorTail.recursiveTensorPower_density hσ n
      have hsn := recursiveTensorPower_support hs n
      have hQn := QuantumProver.SandwichedDPI.sandwichedTrace_pos_of_supportLE
        hρn.1 hσn.1 hsn (density_ne_zero hρn) hα
      have hQ := QuantumProver.SandwichedDPI.sandwichedTrace_pos_of_supportLE
        hρ.1 hσ.1 hs (density_ne_zero hρ) hα
      change sandwichedDivergence α (recursiveTensorPower ρ n ⊗ₖ ρ)
          (recursiveTensorPower σ n ⊗ₖ σ) = _
      rw [QuantumProver.AmplitudeDamping.TensorPower.sandwichedDivergence_kronecker_of_support
        hρn.1 hσn.1 hρ.1 hσ.1 hsn hs α hQn hQ, ih, hD, ← EReal.coe_add]
      congr 1
      push_cast
      ring

theorem iid_uniformBinaryConverse_sandwiched {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    (hs : SupportLE ρ σ) {α B : ℝ} (hα : 1 < α)
    (hD : sandwichedDivergence α ρ σ = (B : EReal)) :
    UniformBinaryConverse (QuantumSteinAchievability.iidStrategyFamily ρ σ hρ hσ) B := by
  intro n hn T hT
  rcases hT with ⟨⟨E,hE⟩,rfl⟩
  rw [QuantumSteinAchievability.binaryTestOfEffect_alpha,
    QuantumSteinAchievability.binaryTestOfEffect_beta,
    QuantumSteinAchievability.acceptanceProbability_complement
      (PetzTensorTail.recursiveTensorPower_density hρ n)]
  simp only [sub_sub_cancel]
  exact (effect_binary_relativeEntropy_le_sandwichedDivergence
    (PetzTensorTail.recursiveTensorPower_density hρ n)
    (PetzTensorTail.recursiveTensorPower_density hσ n) hE hα).trans_eq
      (recursiveTensorPower_sandwichedDivergence hρ hσ hs hα hD n)

theorem relativeEntropyBits_le_sandwichedDivergence {ρ σ : Matrix I I ℂ}
    (hρ : FlaggedStates.IsDensity ρ) (hσ : FlaggedStates.IsDensity σ)
    {α : ℝ} (hα : 1 < α) :
    FlaggedStates.relativeEntropyBits ρ σ ≤ sandwichedDivergence α ρ σ := by
  classical
  by_cases hs : SupportLE ρ σ
  · let B : ℝ := Real.log (sandwichedTrace α ρ σ) / ((α-1) * Real.log 2)
    have hD : sandwichedDivergence α ρ σ = (B : EReal) := by
      simp only [sandwichedDivergence, ite_eq_left hs]
      rfl
    have hB : 0 ≤ B := EReal.coe_nonneg.mp (by
      rw [← hD]
      exact sandwichedDivergence_nonneg_of_density hρ hσ hα)
    calc
      _ ≤ orderedSteinExponent (QuantumSteinAchievability.iidStrategyFamily ρ σ hρ hσ) :=
        Corollaries.relativeEntropyBits_le_iid_orderedSteinExponent ρ σ hρ hσ
      _ ≤ (B : EReal) := orderedSteinExponent_le_of_uniformBinaryConverse hB
        (iid_uniformBinaryConverse_sandwiched hρ hσ hs hα hD)
      _ = _ := hD.symm
  · simp only [sandwichedDivergence, ite_eq_right hs]
    exact le_top

theorem normalizedSEPUmegaki_le_normalizedSEPEntanglement
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (ρ : Density (A × B)) {α : ℝ} (hα : 1 < α) :
    sInf ((fun σ : Density (A × B) => FlaggedStates.relativeEntropyBits ρ.mat σ.mat) ''
      {σ : Density (A × B) | IsSeparable σ}) ≤ normalizedSEPEntanglement α ρ := by
  unfold normalizedSEPEntanglement
  apply le_sInf
  rintro x ⟨σ,hσ,rfl⟩
  exact (sInf_le (show FlaggedStates.relativeEntropyBits ρ.mat σ.mat ∈
    (fun σ : Density (A × B) => FlaggedStates.relativeEntropyBits ρ.mat σ.mat) ''
      {σ : Density (A × B) | IsSeparable σ} from ⟨σ,hσ,rfl⟩)).trans
    (relativeEntropyBits_le_sandwichedDivergence
      ⟨ρ.positive,ρ.normalized⟩ ⟨σ.positive,σ.normalized⟩ hα)

end QuantumProver.AmplitudeDamping.SecretKey.WeakResourceOrder
