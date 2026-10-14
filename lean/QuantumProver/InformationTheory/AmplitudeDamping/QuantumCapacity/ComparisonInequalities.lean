import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.SandwichedEntropyBounds
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.Definitions
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.LaneLimitBounds
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.KrausBounds
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.EntropyBounds

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Kronecker
open RCLike

namespace QuantumProver.AmplitudeDamping.FiniteModel

def boolQubitB (b : Bool) : Qubit := if b then 1 else 0

theorem physicalBitEntryB_eq_damping (p : ℝ) (lost out occupied : Bool) :
    physicalBitEntryB p lost out occupied =
      dampingKraus p (boolQubitB lost) (boolQubitB out) (boolQubitB occupied) := by
  cases lost <;> cases out <;> cases occupied <;>
    simp [physicalBitEntryB, boolQubitB, dampingKraus, dampingNoLoss, dampingLoss]

def tensorDampingKrausB (n : ℕ) (p : ℝ) (L : Finset (Fin n)) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ :=
  fun T S => ∏ i : Fin n, dampingKraus p
    (if i ∈ L then 1 else 0) (if i ∈ T then 1 else 0) (if i ∈ S then 1 else 0)

theorem physicalTensorKrausB_eq_damping (n : ℕ) (p : ℝ) (L : Finset (Fin n)) :
    physicalTensorKrausB n p L = tensorDampingKrausB n p L := by
  ext T S
  apply Finset.prod_congr rfl
  intro i _
  simpa [boolQubitB] using physicalBitEntryB_eq_damping p
    (decide (i ∈ L)) (decide (i ∈ T)) (decide (i ∈ S))

def tensorDampingSectorKrausB (n w : ℕ) (p : ℝ) (L : Finset (Fin n)) :
    Matrix (Finset (Fin n)) (WeightBasisB n w) ℂ :=
  fun T S => tensorDampingKrausB n p L T S.val

theorem tensorDampingSectorKrausB_eq_physical (n w : ℕ) (p : ℝ)
    (L : Finset (Fin n)) :
    tensorDampingSectorKrausB n w p L = physicalSectorKrausB n w p L := by
  ext T S
  exact congrArg (fun K : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ => K T S.val)
    (physicalTensorKrausB_eq_damping n p L).symm

theorem tensorDampingSectorChannelB_reference_eq (n w : ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    krausSumB (referenceKrausB (tensorDampingSectorKrausB n w p) R) ρ =
      ∑ r ∈ Finset.range (w + 1), physicalSurvivorProbabilityB p w r •
        krausSumB (referenceKrausB (lossKrausB n w r) R) ρ := by
  have hfamily : tensorDampingSectorKrausB n w p = physicalSectorKrausB n w p := by
    funext L
    exact tensorDampingSectorKrausB_eq_physical n w p L
  rw [hfamily]
  exact physicalSectorChannelB_reference_eq n w p hp0 hp1 R ρ

theorem lossKrausB_zero_row {n w r : ℕ} (hr : r ≤ w)
    (L T : Finset (Fin n)) (S : WeightBasisB n w) (hT : T.card ≠ r) :
    lossKrausB n w r L T S = 0 := by
  have hz : rawLossKrausB n w r L T S = 0 := by
    by_contra hne
    exact hT (rawLossKrausB_survivor_support hr L T S hne)
  simp [lossKrausB, Matrix.smul_apply, hz]

theorem lossChannelB_reference_entry_zero {n w r : ℕ} (hr : r ≤ w)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ)
    (T V : Finset (Fin n)) (u v : R) (hTV : T.card ≠ r ∨ V.card ≠ r) :
    krausSumB (referenceKrausB (lossKrausB n w r) R) ρ (T, u) (V, v) = 0 := by
  rcases hTV with hT | hV
  · have hK (L : Finset (Fin n)) (S : WeightBasisB n w × R) :
        referenceKrausB (lossKrausB n w r) R L (T, u) S = 0 := by
      rcases S with ⟨S, s⟩
      change lossKrausB n w r L T S * (1 : Matrix R R ℂ) u s = 0
      rw [lossKrausB_zero_row hr L T S hT, zero_mul]
    simp [krausSumB, Matrix.sum_apply, Matrix.mul_apply, hK]
  · have hK (L : Finset (Fin n)) (S : WeightBasisB n w × R) :
        referenceKrausB (lossKrausB n w r) R L (V, v) S = 0 := by
      rcases S with ⟨S, s⟩
      change lossKrausB n w r L V S * (1 : Matrix R R ℂ) v s = 0
      rw [lossKrausB_zero_row hr L V S hV, zero_mul]
    simp [krausSumB, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hK]

theorem tensorDampingSectorChannelB_reference_weight_block (n w : ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ)
    (T V : Finset (Fin n)) (u v : R) (hTV : T.card ≠ V.card) :
    krausSumB (referenceKrausB (tensorDampingSectorKrausB n w p) R) ρ (T, u) (V, v) = 0 := by
  rw [tensorDampingSectorChannelB_reference_eq n w p hp0 hp1]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  apply Finset.sum_eq_zero
  intro r hr
  have hrw : r ≤ w := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hr
  have hzero : T.card ≠ r ∨ V.card ≠ r := by
    by_cases hT : T.card = r
    · exact Or.inr (fun hV => hTV (hT.trans hV.symm))
    · exact Or.inl hT
  rw [lossChannelB_reference_entry_zero hrw R ρ T V u v hzero]
  exact smul_zero _

def positiveSignatureB {n : ℕ} (L : Finset (Fin n)) : Fin n → ZMod 3 :=
  fun i => if i ∈ L then 1 else 0

def phaseSignatureB {n : ℕ} (S T : Finset (Fin n)) : Fin n → ZMod 3 :=
  positiveSignatureB S - positiveSignatureB T

theorem positiveSignatureB_injective (n : ℕ) :
    Function.Injective (positiveSignatureB (n := n)) := by
  intro L M h
  ext i
  have hi := congrFun h i
  by_cases hL : i ∈ L <;> by_cases hM : i ∈ M <;>
    simp_all [positiveSignatureB]

theorem phaseSignatureB_input_injective {n : ℕ} (T : Finset (Fin n)) :
    Function.Injective (fun S => phaseSignatureB S T) := by
  intro S U h
  apply positiveSignatureB_injective n
  simpa [phaseSignatureB] using h

theorem sdiff_involutionB {n : ℕ} {S L : Finset (Fin n)} (hLS : L ⊆ S) :
    S \ (S \ L) = L := by
  ext i
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨hi, hnot⟩
    by_contra hL
    exact hnot ⟨hi, hL⟩
  · intro hi
    exact ⟨hLS hi, fun h => h.2 hi⟩

theorem phaseSignatureB_positive_iff {n : ℕ} (S T L : Finset (Fin n)) :
    phaseSignatureB S T = positiveSignatureB L ↔ T ⊆ S ∧ S \ T = L := by
  constructor
  · intro h
    have hTS : T ⊆ S := by
      intro i hi
      by_contra hS
      have he := congrFun h i
      by_cases hL : i ∈ L
      · have hbad : (-1 : ZMod 3) = 1 := by
          simpa [phaseSignatureB, positiveSignatureB, hi, hS, hL] using he
        exact (by decide : (-1 : ZMod 3) ≠ 1) hbad
      · have hbad : (-1 : ZMod 3) = 0 := by
          simpa [phaseSignatureB, positiveSignatureB, hi, hS, hL] using he
        exact (by decide : (-1 : ZMod 3) ≠ 0) hbad
    refine ⟨hTS, ?_⟩
    ext i
    have he := congrFun h i
    have himp : i ∈ T → i ∈ S := fun hi => hTS hi
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> by_cases hL : i ∈ L <;>
      simp_all [phaseSignatureB, positiveSignatureB, Finset.mem_sdiff]
  · rintro ⟨hTS, rfl⟩
    funext i
    have himp : i ∈ T → i ∈ S := fun hi => hTS hi
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
      simp_all [phaseSignatureB, positiveSignatureB, Finset.mem_sdiff]

theorem phaseSignatureB_loss_iff {n w r : ℕ} (S : WeightBasisB n w)
    (T L : Finset (Fin n)) (hT : T.card = r) :
    phaseSignatureB S.val T = positiveSignatureB L ↔
      L ∈ S.val.powersetCard (w - r) ∧ T = S.val \ L := by
  rw [phaseSignatureB_positive_iff]
  constructor
  · rintro ⟨hTS, hL⟩
    subst L
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset, ?_⟩, ?_⟩
    · rw [Finset.card_sdiff_of_subset hTS, S.property, hT]
    · exact (sdiff_involutionB hTS).symm
  · rintro ⟨hL, rfl⟩
    refine ⟨Finset.sdiff_subset, ?_⟩
    exact sdiff_involutionB (Finset.mem_powersetCard.mp hL).1

def rawPhaseKrausB (n w r : ℕ) (signature : Fin n → ZMod 3) :
    Matrix (Finset (Fin n)) (WeightBasisB n w) ℂ :=
  fun T S => if T.card = r ∧ phaseSignatureB S.val T = signature then 1 else 0

theorem sum_survivor_indicatorB (n r : ℕ) :
    (∑ T : Finset (Fin n), if T.card = r then (1 : ℂ) else 0) = (n.choose r : ℂ) := by
  classical
  have hfilter : (Finset.univ : Finset (Finset (Fin n))).filter
      (fun T => T.card = r) = (Finset.univ : Finset (Fin n)).powersetCard r := by
    ext T
    simp
  rw [Finset.sum_ite, hfilter]
  simp

theorem rawPhaseKrausB_gram (n w r : ℕ) :
    (∑ signature : Fin n → ZMod 3,
      (rawPhaseKrausB n w r signature)ᴴ * rawPhaseKrausB n w r signature) =
      (n.choose r : ℂ) • (1 : Matrix (WeightBasisB n w) (WeightBasisB n w) ℂ) := by
  classical
  ext S U
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  have hterm (T : Finset (Fin n)) :
      (∑ signature : Fin n → ZMod 3,
        star (rawPhaseKrausB n w r signature T S) *
          rawPhaseKrausB n w r signature T U) =
        if T.card = r ∧ S = U then 1 else 0 := by
    have hiff : phaseSignatureB S.val T = phaseSignatureB U.val T ↔ S = U := by
      constructor
      · intro h
        exact Subtype.ext (phaseSignatureB_input_injective T h)
      · rintro rfl
        rfl
    have hiff' : phaseSignatureB U.val T = phaseSignatureB S.val T ↔ S = U :=
      ⟨fun h => hiff.mp h.symm, fun h => (hiff.mpr h).symm⟩
    by_cases hT : T.card = r
    · simp [rawPhaseKrausB, hT, ite_mul, mul_ite, hiff, hiff']
    · simp [rawPhaseKrausB, hT]
  simp_rw [hterm]
  by_cases hSU : S = U
  · simp only [hSU, and_true, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      ite_true, mul_one]
    exact sum_survivor_indicatorB n r
  · simp [hSU, Matrix.smul_apply, Matrix.one_apply]

def phaseKrausB (n w r : ℕ) (signature : Fin n → ZMod 3) :
    Matrix (Finset (Fin n)) (WeightBasisB n w) ℂ :=
  lossNormalizerB n r • rawPhaseKrausB n w r signature

theorem phaseKrausB_complete (n w r : ℕ) (hr : r ≤ n) :
    ∑ signature : Fin n → ZMod 3,
      (phaseKrausB n w r signature)ᴴ * phaseKrausB n w r signature = 1 := by
  have hd : (n.choose r : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hr).ne'
  simp only [phaseKrausB, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ← Finset.smul_sum]
  rw [mul_comm (lossNormalizerB n r) (star (lossNormalizerB n r))]
  rw [lossNormalizerB_norm, rawPhaseKrausB_gram]
  simp [smul_smul, hd]

theorem phaseChannelB_reference_eq (n w r : ℕ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    krausSumB (referenceKrausB (phaseKrausB n w r) R) ρ =
      (n.choose r : ℝ)⁻¹ • krausSumB (referenceKrausB (rawPhaseKrausB n w r) R) ρ := by
  change krausSumB (referenceKrausB
    (fun signature => lossNormalizerB n r • rawPhaseKrausB n w r signature) R) ρ = _
  rw [krausSumB_reference_smul, lossNormalizerB_norm]
  have hcoeff : (n.choose r : ℂ)⁻¹ = Complex.ofReal ((n.choose r : ℝ)⁻¹) := by
    simp
  rw [hcoeff, Complex.coe_smul]

theorem rawPhaseKrausB_positive_class (n w r : ℕ) (hr : r ≤ w)
    (L : Finset (Fin n)) :
    rawPhaseKrausB n w r (positiveSignatureB L) = rawLossKrausB n w r L := by
  ext T S
  by_cases hT : T.card = r
  · simp only [rawPhaseKrausB, hT, true_and, rawLossKrausB,
      phaseSignatureB_loss_iff S T L hT]
  · have hzero : rawLossKrausB n w r L T S = 0 := by
      by_contra hne
      exact hT (rawLossKrausB_survivor_support hr L T S hne)
    simp [rawPhaseKrausB, hT, hzero]

def positiveClassesB (n : ℕ) : Finset (Fin n → ZMod 3) :=
  Finset.univ.image positiveSignatureB

theorem rawPhaseKrausB_positive_sum (n w r : ℕ) (hr : r ≤ w)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    (∑ signature ∈ positiveClassesB n,
      referenceKrausB (rawPhaseKrausB n w r) R signature * ρ *
        (referenceKrausB (rawPhaseKrausB n w r) R signature)ᴴ) =
      krausSumB (referenceKrausB (rawLossKrausB n w r) R) ρ := by
  rw [positiveClassesB, Finset.sum_image]
  · simp only [referenceKrausB, rawPhaseKrausB_positive_class n w r hr, krausSumB]
  · intro L _ M _ h
    exact positiveSignatureB_injective n h

theorem rawPhaseKrausB_reference_loss_residual (n w r : ℕ) (hr : r ≤ w)
    (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ}
    (hρ : ρ.PosSemidef) :
    (krausSumB (referenceKrausB (rawPhaseKrausB n w r) R) ρ -
      krausSumB (referenceKrausB (rawLossKrausB n w r) R) ρ).PosSemidef := by
  rw [← rawPhaseKrausB_positive_sum n w r hr R ρ]
  exact krausSumB_reference_subfamily_residual _ _ R hρ

def phaseComparisonConstantB (n w r : ℕ) : ℝ :=
  (n.choose r : ℝ) / (w.choose r : ℝ)

theorem phaseChannelB_reference_loss_domination (n w r : ℕ)
    (hrw : r ≤ w) (hrn : r ≤ n)
    (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ}
    (hρ : ρ.PosSemidef) :
    ((phaseComparisonConstantB n w r) •
      krausSumB (referenceKrausB (phaseKrausB n w r) R) ρ -
      krausSumB (referenceKrausB (lossKrausB n w r) R) ρ).PosSemidef := by
  have hdN : (n.choose r : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hrn).ne'
  have hscalar : phaseComparisonConstantB n w r * (n.choose r : ℝ)⁻¹ =
      (w.choose r : ℝ)⁻¹ := by
    simp only [phaseComparisonConstantB, div_eq_mul_inv]
    rw [mul_right_comm, mul_inv_cancel₀ hdN, one_mul]
  rw [phaseChannelB_reference_eq, lossChannelB_reference_eq,
    smul_smul, hscalar, ← smul_sub]
  exact (rawPhaseKrausB_reference_loss_residual n w r hrw R hρ).smul
    (inv_nonneg.mpr (Nat.cast_nonneg (w.choose r)))

open QuantumProver.AmplitudeDamping.SecretKey.Phase

theorem wordCharacterB_sub {n : ℕ} (a b z : Fin n → ZMod 3) :
    wordCharacter (a - b) z = wordCharacter a z * conj (wordCharacter b z) := by
  simp only [wordCharacter_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [AddChar.map_sub_eq_div, div_eq_mul_inv, AddChar.inv_apply_eq_conj]

def rawMeasurePhaseKrausB (n w r : ℕ) (z : Fin n → ZMod 3) :
    Matrix (Finset (Fin n)) (WeightBasisB n w) ℂ :=
  fun T S => if T.card = r then
    wordCharacter (positiveSignatureB T) z * conj (wordCharacter (positiveSignatureB S.val) z)
    else 0

theorem rawMeasurePhaseKrausB_signature (n w r : ℕ) (z : Fin n → ZMod 3)
    (T : Finset (Fin n)) (S : WeightBasisB n w) :
    rawMeasurePhaseKrausB n w r z T S =
      if T.card = r then conj (wordCharacter (phaseSignatureB S.val T) z) else 0 := by
  simp only [rawMeasurePhaseKrausB, phaseSignatureB, wordCharacterB_sub, map_mul,
    conj_conj]
  congr 1
  ring

theorem rawMeasurePhaseKrausB_rankOne (n w r : ℕ) (z : Fin n → ZMod 3) :
    rawMeasurePhaseKrausB n w r z = QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus
      (fun S : WeightBasisB n w => wordCharacter (positiveSignatureB S.val) z)
      (fun T : Finset (Fin n) => if T.card = r then wordCharacter (positiveSignatureB T) z else 0) := by
  ext T S
  simp [rawMeasurePhaseKrausB, QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus,
    Matrix.vecMulVec_apply, Pi.star_apply, ite_mul]

theorem rawMeasurePhaseKrausB_coefficients (n w r : ℕ)
    (T V : Finset (Fin n)) (S U : WeightBasisB n w) :
    (∑ z : Fin n → ZMod 3,
      rawMeasurePhaseKrausB n w r z T S * star (rawMeasurePhaseKrausB n w r z V U)) =
      (Fintype.card (Fin n → ZMod 3) : ℂ) *
        ∑ signature : Fin n → ZMod 3,
          rawPhaseKrausB n w r signature T S * star (rawPhaseKrausB n w r signature V U) := by
  classical
  simp only [rawMeasurePhaseKrausB_signature]
  by_cases hT : T.card = r
  · by_cases hV : V.card = r
    · simp only [hT, hV, ite_true, starRingEnd_apply, star_star]
      have horth := wordCharacter_sum_orthogonality
        (phaseSignatureB S.val T) (phaseSignatureB U.val V)
      simp only [starRingEnd_apply] at horth
      calc
        _ = if phaseSignatureB S.val T = phaseSignatureB U.val V then
            (Fintype.card (Fin n → ZMod 3) : ℂ) else 0 := horth
        _ = _ := by simp [rawPhaseKrausB, hT, hV, ite_mul, mul_ite, eq_comm]
    · simp [hT, hV, rawPhaseKrausB]
  · simp [hT, rawPhaseKrausB]

theorem rawMeasurePhaseChannelB_eq (n w r : ℕ)
    (ρ : Matrix (WeightBasisB n w) (WeightBasisB n w) ℂ) :
    krausSumB (rawMeasurePhaseKrausB n w r) ρ =
      (Fintype.card (Fin n → ZMod 3) : ℂ) • krausSumB (rawPhaseKrausB n w r) ρ := by
  ext T V
  simp only [krausSumB_entry, rawMeasurePhaseKrausB_coefficients,
    Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

def phaseSampleNormalizerB (n : ℕ) : ℂ :=
  (Real.sqrt (Fintype.card (Fin n → ZMod 3) : ℝ) : ℂ)⁻¹

theorem phaseSampleB_card (n : ℕ) : Fintype.card (Fin n → ZMod 3) = 3 ^ n := by
  simp

theorem phaseSampleNormalizerB_norm (n : ℕ) :
    star (phaseSampleNormalizerB n) * phaseSampleNormalizerB n =
      (Fintype.card (Fin n → ZMod 3) : ℂ)⁻¹ := by
  simp [phaseSampleNormalizerB, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Nat.cast_nonneg (Fintype.card (Fin n → ZMod 3)))]

def measurePhaseKrausB (n w r : ℕ) (z : Fin n → ZMod 3) :
    Matrix (Finset (Fin n)) (WeightBasisB n w) ℂ :=
  (phaseSampleNormalizerB n * lossNormalizerB n r) • rawMeasurePhaseKrausB n w r z

def phaseInputVectorB (n w : ℕ) (z : Fin n → ZMod 3) : WeightBasisB n w → ℂ :=
  fun S => phaseSampleNormalizerB n * wordCharacter (positiveSignatureB S.val) z

def phaseOutputVectorB (n r : ℕ) (z : Fin n → ZMod 3) : Finset (Fin n) → ℂ :=
  fun T => if T.card = r then lossNormalizerB n r * wordCharacter (positiveSignatureB T) z else 0

theorem star_phaseSampleNormalizerB (n : ℕ) :
    star (phaseSampleNormalizerB n) = phaseSampleNormalizerB n := by
  simp [phaseSampleNormalizerB]

theorem star_lossNormalizerB (w r : ℕ) : star (lossNormalizerB w r) = lossNormalizerB w r := by
  simp [lossNormalizerB]

theorem vecMulVecB_scaled {I : Type*} (v : I → ℂ) (a : ℂ) :
    Matrix.vecMulVec (fun i => a * v i) (star (fun i => a * v i)) =
      (star a * a) • Matrix.vecMulVec v (star v) := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, star_mul, Matrix.smul_apply,
    smul_eq_mul]
  ring

theorem phaseInputVectorB_complete (n w : ℕ) :
    ∑ z : Fin n → ZMod 3,
      Matrix.vecMulVec (phaseInputVectorB n w z) (star (phaseInputVectorB n w z)) =
        (1 : Matrix (WeightBasisB n w) (WeightBasisB n w) ℂ) := by
  have hinj : Function.Injective
      (fun S : WeightBasisB n w => positiveSignatureB S.val) := by
    intro S U h
    exact Subtype.ext (positiveSignatureB_injective n h)
  have hN : (Fintype.card (Fin n → ZMod 3) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ = (star (phaseSampleNormalizerB n) * phaseSampleNormalizerB n) •
        ∑ z : Fin n → ZMod 3,
          Matrix.vecMulVec (fun S : WeightBasisB n w =>
            wordCharacter (positiveSignatureB S.val) z)
            (star (fun S : WeightBasisB n w =>
              wordCharacter (positiveSignatureB S.val) z)) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro z _
      exact vecMulVecB_scaled (fun S : WeightBasisB n w =>
        wordCharacter (positiveSignatureB S.val) z) (phaseSampleNormalizerB n)
    _ = 1 := by
      rw [phaseSampleNormalizerB_norm, phaseVectors_gram _ hinj]
      simp [smul_smul, hN]

theorem wordCharacterB_unit (n : ℕ) (signature z : Fin n → ZMod 3) :
    star (wordCharacter signature z) * wordCharacter signature z = 1 := by
  have hnorm := AddChar.norm_apply (wordCharacter signature) z
  have hne : wordCharacter signature z ≠ 0 := by
    intro h
    simpa [h] using hnorm
  calc
    _ = (wordCharacter signature z)⁻¹ * wordCharacter signature z := by
      congr 1
      simpa only [starRingEnd_apply] using
        (AddChar.inv_apply_eq_conj (wordCharacter signature) z).symm
    _ = 1 := inv_mul_cancel₀ hne

theorem phaseOutputVectorB_normalized (n r : ℕ) (hr : r ≤ n)
    (z : Fin n → ZMod 3) :
    ∑ T : Finset (Fin n), star (phaseOutputVectorB n r z T) *
      phaseOutputVectorB n r z T = 1 := by
  have hd : (n.choose r : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hr).ne'
  have hterm (T : Finset (Fin n)) : star (phaseOutputVectorB n r z T) *
      phaseOutputVectorB n r z T = if T.card = r then (n.choose r : ℂ)⁻¹ else 0 := by
    by_cases hT : T.card = r
    · simp only [phaseOutputVectorB, hT, ite_true, star_mul]
      calc
        _ = (star (lossNormalizerB n r) * lossNormalizerB n r) *
            (star (wordCharacter (positiveSignatureB T) z) *
              wordCharacter (positiveSignatureB T) z) := by ring
        _ = _ := by rw [lossNormalizerB_norm, wordCharacterB_unit, mul_one]
    · simp [phaseOutputVectorB, hT]
  simp_rw [hterm]
  calc
    _ = (n.choose r : ℂ)⁻¹ *
        ∑ T : Finset (Fin n), if T.card = r then (1 : ℂ) else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T _
          by_cases hT : T.card = r <;> simp [hT]
    _ = 1 := by rw [sum_survivor_indicatorB, inv_mul_cancel₀ hd]

theorem measurePhaseKrausB_rankOne (n w r : ℕ) (z : Fin n → ZMod 3) :
    measurePhaseKrausB n w r z = QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus
      (phaseInputVectorB n w z) (phaseOutputVectorB n r z) := by
  ext T S
  by_cases hT : T.card = r
  · simp only [measurePhaseKrausB, Matrix.smul_apply, smul_eq_mul,
      rawMeasurePhaseKrausB, hT, ite_true, QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus,
      Matrix.vecMulVec_apply, phaseInputVectorB, phaseOutputVectorB,
      Pi.star_apply, star_mul, star_phaseSampleNormalizerB, starRingEnd_apply]
    ring
  · simp [measurePhaseKrausB, rawMeasurePhaseKrausB, hT,
      QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus, Matrix.vecMulVec_apply,
      phaseOutputVectorB]

theorem measurePhaseKrausB_complete (n w r : ℕ) (hr : r ≤ n) :
    ∑ z : Fin n → ZMod 3, (measurePhaseKrausB n w r z)ᴴ * measurePhaseKrausB n w r z = 1 := by
  simp_rw [measurePhaseKrausB_rankOne]
  exact QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus_complete _ _
    (phaseInputVectorB_complete n w) (phaseOutputVectorB_normalized n r hr)

theorem measurePhaseChannelB_eq (n w r : ℕ)
    (ρ : Matrix (WeightBasisB n w) (WeightBasisB n w) ℂ) :
    krausSumB (measurePhaseKrausB n w r) ρ = krausSumB (phaseKrausB n w r) ρ := by
  have hN : (Fintype.card (Fin n → ZMod 3) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hnorm : star (phaseSampleNormalizerB n * lossNormalizerB n r) *
      (phaseSampleNormalizerB n * lossNormalizerB n r) =
      (Fintype.card (Fin n → ZMod 3) : ℂ)⁻¹ * (n.choose r : ℂ)⁻¹ := by
    calc
      _ = (star (phaseSampleNormalizerB n) * phaseSampleNormalizerB n) *
          (star (lossNormalizerB n r) * lossNormalizerB n r) := by
            rw [star_mul]
            ring
      _ = _ := by rw [phaseSampleNormalizerB_norm, lossNormalizerB_norm]
  change krausSumB (fun z => (phaseSampleNormalizerB n * lossNormalizerB n r) •
    rawMeasurePhaseKrausB n w r z) ρ =
      krausSumB (fun signature => lossNormalizerB n r • rawPhaseKrausB n w r signature) ρ
  rw [krausSumB_smul, krausSumB_smul, hnorm, lossNormalizerB_norm,
    rawMeasurePhaseChannelB_eq, smul_smul]
  congr 1
  rw [mul_right_comm, inv_mul_cancel₀ hN, one_mul]

theorem measurePhaseChannelB_reference_eq (n w r : ℕ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    krausSumB (referenceKrausB (measurePhaseKrausB n w r) R) ρ =
      krausSumB (referenceKrausB (phaseKrausB n w r) R) ρ :=
  krausSumB_reference_congr _ _ (measurePhaseChannelB_eq n w r) R ρ

theorem measurePhaseChannelB_reference_loss_domination (n w r : ℕ)
    (hrw : r ≤ w) (hrn : r ≤ n)
    (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ}
    (hρ : ρ.PosSemidef) :
    ((phaseComparisonConstantB n w r) •
      krausSumB (referenceKrausB (measurePhaseKrausB n w r) R) ρ -
      krausSumB (referenceKrausB (lossKrausB n w r) R) ρ).PosSemidef := by
  rw [measurePhaseChannelB_reference_eq]
  exact phaseChannelB_reference_loss_domination n w r hrw hrn R hρ

theorem physicalSurvivorProbabilityB_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w r : ℕ) : 0 ≤ physicalSurvivorProbabilityB p w r := by
  unfold physicalSurvivorProbabilityB
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.mpr hp1) _))
    (pow_nonneg hp0 _)

theorem physicalSurvivorProbabilityB_sum (p : ℝ) (w : ℕ) :
    ∑ r ∈ Finset.range (w + 1), physicalSurvivorProbabilityB p w r = 1 := by
  calc
    _ = ∑ r ∈ Finset.range (w + 1),
        (1 - p) ^ r * p ^ (w - r) * (w.choose r : ℝ) := by
          apply Finset.sum_congr rfl
          intro r _
          unfold physicalSurvivorProbabilityB
          ring
    _ = ((1 - p) + p) ^ w := (add_pow (1 - p) p w).symm
    _ = 1 := by simp

theorem tensorDampingSectorChannelB_reference_trace_preserving (n w : ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    (krausSumB (referenceKrausB (tensorDampingSectorKrausB n w p) R) ρ).trace = ρ.trace := by
  rw [tensorDampingSectorChannelB_reference_eq n w p hp0 hp1]
  simp only [Matrix.trace_sum, Matrix.trace_smul]
  calc
    _ = ∑ r ∈ Finset.range (w + 1), physicalSurvivorProbabilityB p w r • ρ.trace := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrw : r ≤ w := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hr
      rw [lossChannelB_reference_trace_preserving n w r hrw R ρ]
    _ = (∑ r ∈ Finset.range (w + 1), physicalSurvivorProbabilityB p w r) • ρ.trace :=
      Finset.sum_smul.symm
    _ = ρ.trace := by rw [physicalSurvivorProbabilityB_sum, one_smul]

theorem physicalSurvivorChannelB_reference_phase_domination (n w r : ℕ)
    (hrw : r ≤ w) (hrn : r ≤ n) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ}
    (hρ : ρ.PosSemidef) :
    ((physicalSurvivorProbabilityB p w r * phaseComparisonConstantB n w r) •
      krausSumB (referenceKrausB (measurePhaseKrausB n w r) R) ρ -
      krausSumB (referenceKrausB (physicalSurvivorKrausB n w r p) R) ρ).PosSemidef := by
  rw [physicalSurvivorChannelB_reference_eq n w r hrw p hp0 hp1]
  have h := (measurePhaseChannelB_reference_loss_domination n w r hrw hrn R hρ).smul
    (physicalSurvivorProbabilityB_nonneg p hp0 hp1 w r)
  simpa only [smul_sub, smul_smul] using h

theorem tensorDampingSectorChannelB_reference_phase_domination (n w : ℕ)
    (hwn : w ≤ n) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (R : Type*) [Fintype R] [DecidableEq R]
    {ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ}
    (hρ : ρ.PosSemidef) :
    ((∑ r ∈ Finset.range (w + 1),
      (physicalSurvivorProbabilityB p w r * phaseComparisonConstantB n w r) •
        krausSumB (referenceKrausB (measurePhaseKrausB n w r) R) ρ) -
      krausSumB (referenceKrausB (tensorDampingSectorKrausB n w p) R) ρ).PosSemidef := by
  rw [tensorDampingSectorChannelB_reference_eq n w p hp0 hp1]
  rw [← Finset.sum_sub_distrib]
  exact Matrix.posSemidef_sum _ fun r hr => by
    have hrw : r ≤ w := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hr
    have h := physicalSurvivorChannelB_reference_phase_domination n w r hrw
      (hrw.trans hwn) p hp0 hp1 R hρ
    rw [physicalSurvivorChannelB_reference_eq n w r hrw p hp0 hp1] at h
    exact h

abbrev survivorPhaseLabelB (n w : ℕ) := Fin (w + 1) × (Fin n → ZMod 3)

def weightedPhaseInputVectorB (n w : ℕ) (mu : Fin (w + 1) → ℝ)
    (j : survivorPhaseLabelB n w) : WeightBasisB n w → ℂ :=
  fun S => (Real.sqrt (mu j.1) : ℂ) * phaseInputVectorB n w j.2 S

def weightedPhaseOutputVectorB (n w : ℕ)
    (j : survivorPhaseLabelB n w) : Finset (Fin n) → ℂ :=
  phaseOutputVectorB n j.1.val j.2

theorem weightedPhaseAmplitude_normB {w : ℕ} (mu : Fin (w + 1) → ℝ)
    (hmu : ∀ r, 0 ≤ mu r) (r : Fin (w + 1)) :
    star (Real.sqrt (mu r) : ℂ) * (Real.sqrt (mu r) : ℂ) = (mu r : ℂ) := by
  simp [← Complex.ofReal_mul, Real.mul_self_sqrt (hmu r)]

theorem weightedPhaseInputVectorB_complete (n w : ℕ) (mu : Fin (w + 1) → ℝ)
    (hmu : ∀ r, 0 ≤ mu r) (hsum : ∑ r, mu r = 1) :
    ∑ j : survivorPhaseLabelB n w,
      Matrix.vecMulVec (weightedPhaseInputVectorB n w mu j)
        (star (weightedPhaseInputVectorB n w mu j)) =
          (1 : Matrix (WeightBasisB n w) (WeightBasisB n w) ℂ) := by
  have hsumC : ∑ r : Fin (w + 1), (mu r : ℂ) = 1 := by exact_mod_cast hsum
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ r : Fin (w + 1), (mu r : ℂ) •
        (1 : Matrix (WeightBasisB n w) (WeightBasisB n w) ℂ) := by
      apply Finset.sum_congr rfl
      intro r _
      calc
        _ = (mu r : ℂ) • ∑ z : Fin n → ZMod 3,
            Matrix.vecMulVec (phaseInputVectorB n w z) (star (phaseInputVectorB n w z)) := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro z _
          have h := vecMulVecB_scaled (phaseInputVectorB n w z) (Real.sqrt (mu r) : ℂ)
          rw [weightedPhaseAmplitude_normB mu hmu r] at h
          exact h
        _ = _ := by rw [phaseInputVectorB_complete]
    _ = 1 := by rw [← Finset.sum_smul, hsumC, one_smul]

theorem weightedPhaseOutputVectorB_normalized (n w : ℕ) (hwn : w ≤ n)
    (j : survivorPhaseLabelB n w) :
    ∑ T : Finset (Fin n), star (weightedPhaseOutputVectorB n w j T) *
      weightedPhaseOutputVectorB n w j T = 1 := by
  exact phaseOutputVectorB_normalized n j.1.val
    ((Nat.le_of_lt_succ j.1.isLt).trans hwn) j.2

def weightedPhaseKrausB (n w : ℕ) (mu : Fin (w + 1) → ℝ)
    (j : survivorPhaseLabelB n w) : Matrix (Finset (Fin n)) (WeightBasisB n w) ℂ :=
  QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus
    (weightedPhaseInputVectorB n w mu j) (weightedPhaseOutputVectorB n w j)

theorem weightedPhaseKrausB_complete (n w : ℕ) (hwn : w ≤ n)
    (mu : Fin (w + 1) → ℝ) (hmu : ∀ r, 0 ≤ mu r) (hsum : ∑ r, mu r = 1) :
    ∑ j : survivorPhaseLabelB n w, (weightedPhaseKrausB n w mu j)ᴴ *
      weightedPhaseKrausB n w mu j = 1 :=
  QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus_complete _ _
    (weightedPhaseInputVectorB_complete n w mu hmu hsum)
    (weightedPhaseOutputVectorB_normalized n w hwn)

theorem weightedPhaseKrausB_eq_smul (n w : ℕ) (mu : Fin (w + 1) → ℝ)
    (j : survivorPhaseLabelB n w) :
    weightedPhaseKrausB n w mu j = (Real.sqrt (mu j.1) : ℂ) •
      measurePhaseKrausB n w j.1.val j.2 := by
  rw [measurePhaseKrausB_rankOne]
  ext T S
  have hstar : star (Real.sqrt (mu j.1) : ℂ) = (Real.sqrt (mu j.1) : ℂ) := by simp
  simp only [weightedPhaseKrausB, QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus,
    Matrix.vecMulVec_apply, Pi.star_apply, weightedPhaseInputVectorB,
    weightedPhaseOutputVectorB, Matrix.smul_apply, smul_eq_mul, star_mul, hstar]
  ring

theorem weightedPhaseChannelB_reference_eq (n w : ℕ) (mu : Fin (w + 1) → ℝ)
    (hmu : ∀ r, 0 ≤ mu r) (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    krausSumB (referenceKrausB (weightedPhaseKrausB n w mu) R) ρ =
      ∑ r : Fin (w + 1), mu r •
        krausSumB (referenceKrausB (measurePhaseKrausB n w r.val) R) ρ := by
  change (∑ j : Fin (w + 1) × (Fin n → ZMod 3),
    referenceKrausB (weightedPhaseKrausB n w mu) R j * ρ *
      (referenceKrausB (weightedPhaseKrausB n w mu) R j)ᴴ) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  change krausSumB (referenceKrausB (fun z => weightedPhaseKrausB n w mu (r, z)) R) ρ = _
  have hfamily : (fun z => weightedPhaseKrausB n w mu (r, z)) =
      fun z => (Real.sqrt (mu r) : ℂ) • measurePhaseKrausB n w r.val z := by
    funext z
    exact weightedPhaseKrausB_eq_smul n w mu (r, z)
  rw [hfamily, krausSumB_reference_smul, weightedPhaseAmplitude_normB mu hmu,
    Complex.coe_smul]

theorem weightedPhaseKrausB_reference_complete (n w : ℕ) (hwn : w ≤ n)
    (mu : Fin (w + 1) → ℝ) (hmu : ∀ r, 0 ≤ mu r) (hsum : ∑ r, mu r = 1)
    (R : Type*) [Fintype R] [DecidableEq R] :
    ∑ j : survivorPhaseLabelB n w,
      (referenceKrausB (weightedPhaseKrausB n w mu) R j)ᴴ *
        referenceKrausB (weightedPhaseKrausB n w mu) R j = 1 :=
  referenceKrausB_complete _ (weightedPhaseKrausB_complete n w hwn mu hmu hsum) R

theorem weightedPhaseChannelB_reference_trace_preserving (n w : ℕ) (hwn : w ≤ n)
    (mu : Fin (w + 1) → ℝ) (hmu : ∀ r, 0 ≤ mu r) (hsum : ∑ r, mu r = 1)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    (krausSumB (referenceKrausB (weightedPhaseKrausB n w mu) R) ρ).trace = ρ.trace :=
  krausSumB_trace_preserving _ (weightedPhaseKrausB_reference_complete n w hwn mu hmu hsum R) ρ

def physicalPhaseLawB (p : ℝ) (w : ℕ) (r : Fin (w + 1)) : ℝ :=
  physicalSurvivorProbabilityB p w r.val

theorem physicalPhaseLawB_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : ℕ) (r : Fin (w + 1)) : 0 ≤ physicalPhaseLawB p w r :=
  physicalSurvivorProbabilityB_nonneg p hp0 hp1 w r.val

theorem physicalPhaseLawB_sum (p : ℝ) (w : ℕ) :
    ∑ r : Fin (w + 1), physicalPhaseLawB p w r = 1 := by
  unfold physicalPhaseLawB
  rw [Fin.sum_univ_eq_sum_range]
  exact physicalSurvivorProbabilityB_sum p w

theorem phaseComparisonConstantB_pos (n w r : ℕ) (hrw : r ≤ w) (hrn : r ≤ n) :
    0 < phaseComparisonConstantB n w r :=
  div_pos (Nat.cast_pos.mpr (Nat.choose_pos hrn)) (Nat.cast_pos.mpr (Nat.choose_pos hrw))

def optimizedPhaseNumeratorB (n w : ℕ) (p z : ℝ) (r : Fin (w + 1)) : ℝ :=
  physicalPhaseLawB p w r * Real.rpow (phaseComparisonConstantB n w r.val) z

def optimizedPhaseLawB (n w : ℕ) (p z : ℝ) : Fin (w + 1) → ℝ :=
  QuantumProver.AmplitudeDamping.SecretKey.Scalar.normalizedFlags (optimizedPhaseNumeratorB n w p z)

theorem optimizedPhaseMomentB_pos (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℝ) :
    0 < ∑ r : Fin (w + 1), optimizedPhaseNumeratorB n w p z r := by
  exact QuantumProver.AmplitudeDamping.SecretKey.Scalar.channel_flag_moment_pos (physicalPhaseLawB p w)
    (fun r => phaseComparisonConstantB n w r.val) z
    (physicalPhaseLawB_nonneg p hp0 hp1 w) (physicalPhaseLawB_sum p w)
    (fun r => phaseComparisonConstantB_pos n w r.val (Nat.le_of_lt_succ r.isLt)
      ((Nat.le_of_lt_succ r.isLt).trans hwn))

theorem optimizedPhaseLawB_nonneg (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℝ) (r : Fin (w + 1)) :
    0 ≤ optimizedPhaseLawB n w p z r := by
  exact QuantumProver.AmplitudeDamping.SecretKey.Scalar.normalizedFlags_nonneg (optimizedPhaseNumeratorB n w p z)
    (fun j => mul_nonneg (physicalPhaseLawB_nonneg p hp0 hp1 w j)
      (Real.rpow_nonneg (phaseComparisonConstantB_pos n w j.val
        (Nat.le_of_lt_succ j.isLt) ((Nat.le_of_lt_succ j.isLt).trans hwn)).le z))
    (optimizedPhaseMomentB_pos n w hwn p hp0 hp1 z) r

theorem optimizedPhaseLawB_sum (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℝ) :
    ∑ r : Fin (w + 1), optimizedPhaseLawB n w p z r = 1 :=
  QuantumProver.AmplitudeDamping.SecretKey.Scalar.normalizedFlags_sum (optimizedPhaseNumeratorB n w p z)
    (optimizedPhaseMomentB_pos n w hwn p hp0 hp1 z)

theorem optimizedPhaseLawB_support (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℝ) (r : Fin (w + 1))
    (hr : optimizedPhaseLawB n w p z r = 0) : physicalPhaseLawB p w r = 0 := by
  have hb := QuantumProver.AmplitudeDamping.SecretKey.Scalar.normalizedFlags_support
    (optimizedPhaseNumeratorB n w p z) (optimizedPhaseMomentB_pos n w hwn p hp0 hp1 z) r hr
  have hc := Real.rpow_pos_of_pos (phaseComparisonConstantB_pos n w r.val
    (Nat.le_of_lt_succ r.isLt) ((Nat.le_of_lt_succ r.isLt).trans hwn)) z
  exact (mul_eq_zero.mp hb).resolve_right hc.ne'

def physicalPhaseKrausB (n w : ℕ) (p : ℝ) :
    survivorPhaseLabelB n w → Matrix (Finset (Fin n)) (WeightBasisB n w) ℂ :=
  weightedPhaseKrausB n w (physicalPhaseLawB p w)

def optimizedPhaseKrausB (n w : ℕ) (p z : ℝ) :
    survivorPhaseLabelB n w → Matrix (Finset (Fin n)) (WeightBasisB n w) ℂ :=
  weightedPhaseKrausB n w (optimizedPhaseLawB n w p z)

theorem physicalPhaseKrausB_complete (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ j : survivorPhaseLabelB n w, (physicalPhaseKrausB n w p j)ᴴ *
      physicalPhaseKrausB n w p j = 1 :=
  weightedPhaseKrausB_complete n w hwn (physicalPhaseLawB p w)
    (physicalPhaseLawB_nonneg p hp0 hp1 w) (physicalPhaseLawB_sum p w)

theorem optimizedPhaseKrausB_complete (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℝ) :
    ∑ j : survivorPhaseLabelB n w, (optimizedPhaseKrausB n w p z j)ᴴ *
      optimizedPhaseKrausB n w p z j = 1 :=
  weightedPhaseKrausB_complete n w hwn (optimizedPhaseLawB n w p z)
    (optimizedPhaseLawB_nonneg n w hwn p hp0 hp1 z)
    (optimizedPhaseLawB_sum n w hwn p hp0 hp1 z)

theorem physicalPhaseChannelB_reference_eq (n w : ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    krausSumB (referenceKrausB (physicalPhaseKrausB n w p) R) ρ =
      ∑ r : Fin (w + 1), physicalPhaseLawB p w r •
        krausSumB (referenceKrausB (measurePhaseKrausB n w r.val) R) ρ :=
  weightedPhaseChannelB_reference_eq n w (physicalPhaseLawB p w)
    (physicalPhaseLawB_nonneg p hp0 hp1 w) R ρ

theorem optimizedPhaseChannelB_reference_eq (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℝ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    krausSumB (referenceKrausB (optimizedPhaseKrausB n w p z) R) ρ =
      ∑ r : Fin (w + 1), optimizedPhaseLawB n w p z r •
        krausSumB (referenceKrausB (measurePhaseKrausB n w r.val) R) ρ :=
  weightedPhaseChannelB_reference_eq n w (optimizedPhaseLawB n w p z)
    (optimizedPhaseLawB_nonneg n w hwn p hp0 hp1 z) R ρ

theorem physicalPhaseChannelB_reference_trace_preserving (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    (krausSumB (referenceKrausB (physicalPhaseKrausB n w p) R) ρ).trace = ρ.trace :=
  weightedPhaseChannelB_reference_trace_preserving n w hwn (physicalPhaseLawB p w)
    (physicalPhaseLawB_nonneg p hp0 hp1 w) (physicalPhaseLawB_sum p w) R ρ

theorem optimizedPhaseChannelB_reference_trace_preserving (n w : ℕ) (hwn : w ≤ n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : ℝ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (WeightBasisB n w × R) (WeightBasisB n w × R) ℂ) :
    (krausSumB (referenceKrausB (optimizedPhaseKrausB n w p z) R) ρ).trace = ρ.trace :=
  weightedPhaseChannelB_reference_trace_preserving n w hwn (optimizedPhaseLawB n w p z)
    (optimizedPhaseLawB_nonneg n w hwn p hp0 hp1 z)
    (optimizedPhaseLawB_sum n w hwn p hp0 hp1 z) R ρ

def fullPhaseDiagonalB (n : ℕ) (z : Fin n → ZMod 3) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ :=
  Matrix.diagonal (fun S => wordCharacter (positiveSignatureB S) z)

theorem wordCharacterB_add {n : ℕ} (a b z : Fin n → ZMod 3) :
    wordCharacter (a + b) z = wordCharacter a z * wordCharacter b z := by
  simp only [wordCharacter_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  exact AddChar.map_add_eq_mul _ _ _

theorem positiveSignatureB_deletion {n : ℕ} (L S : Finset (Fin n)) (hLS : L ⊆ S) :
    positiveSignatureB S = positiveSignatureB L + positiveSignatureB (S \ L) := by
  funext i
  have himp : i ∈ L → i ∈ S := fun hi => hLS hi
  by_cases hiS : i ∈ S <;> by_cases hiL : i ∈ L <;>
    simp_all [positiveSignatureB, Finset.mem_sdiff]

theorem fullPhaseDiagonalB_conjTranspose_mul (n : ℕ) (z : Fin n → ZMod 3) :
    (fullPhaseDiagonalB n z)ᴴ * fullPhaseDiagonalB n z = 1 := by
  rw [fullPhaseDiagonalB, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  calc
    _ = Matrix.diagonal (fun _ : Finset (Fin n) => (1 : ℂ)) := by
      congr 1
      funext S
      exact wordCharacterB_unit n (positiveSignatureB S) z
    _ = 1 := Matrix.diagonal_one

theorem fullPhaseDiagonalB_mul_conjTranspose (n : ℕ) (z : Fin n → ZMod 3) :
    fullPhaseDiagonalB n z * (fullPhaseDiagonalB n z)ᴴ = 1 := by
  rw [fullPhaseDiagonalB, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  calc
    _ = Matrix.diagonal (fun _ : Finset (Fin n) => (1 : ℂ)) := by
      congr 1
      funext S
      simpa only [Pi.star_apply, mul_comm] using wordCharacterB_unit n (positiveSignatureB S) z
    _ = 1 := Matrix.diagonal_one

theorem physicalTensorKrausB_phase_intertwining (n : ℕ) (p : ℝ)
    (L : Finset (Fin n)) (z : Fin n → ZMod 3) :
    physicalTensorKrausB n p L * fullPhaseDiagonalB n z =
      wordCharacter (positiveSignatureB L) z •
        (fullPhaseDiagonalB n z * physicalTensorKrausB n p L) := by
  ext T S
  simp only [fullPhaseDiagonalB, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.smul_apply, smul_eq_mul, physicalTensorKrausB_entry]
  by_cases h : L ⊆ S ∧ T = S \ L
  · simp only [if_pos h]
    have hc : wordCharacter (positiveSignatureB S) z =
        wordCharacter (positiveSignatureB L) z * wordCharacter (positiveSignatureB T) z := by
      rw [positiveSignatureB_deletion L S h.1, wordCharacterB_add, ← h.2]
    rw [hc]
    ring
  · simp [h]

def fullPhaseReferenceB (n : ℕ) (z : Fin n → ZMod 3)
    (R : Type*) [DecidableEq R] :
    Matrix (Finset (Fin n) × R) (Finset (Fin n) × R) ℂ :=
  fullPhaseDiagonalB n z ⊗ₖ (1 : Matrix R R ℂ)

theorem fullPhaseReferenceB_conjTranspose_mul (n : ℕ) (z : Fin n → ZMod 3)
    (R : Type*) [Fintype R] [DecidableEq R] :
    (fullPhaseReferenceB n z R)ᴴ * fullPhaseReferenceB n z R = 1 := by
  simp only [fullPhaseReferenceB, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    fullPhaseDiagonalB_conjTranspose_mul, Matrix.one_kronecker_one]

theorem fullPhaseReferenceB_mul_conjTranspose (n : ℕ) (z : Fin n → ZMod 3)
    (R : Type*) [Fintype R] [DecidableEq R] :
    fullPhaseReferenceB n z R * (fullPhaseReferenceB n z R)ᴴ = 1 := by
  simp only [fullPhaseReferenceB, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    fullPhaseDiagonalB_mul_conjTranspose, Matrix.one_kronecker_one]

theorem physicalTensorKrausB_reference_phase_intertwining (n : ℕ) (p : ℝ)
    (L : Finset (Fin n)) (z : Fin n → ZMod 3)
    (R : Type*) [Fintype R] [DecidableEq R] :
    referenceKrausB (physicalTensorKrausB n p) R L * fullPhaseReferenceB n z R =
      wordCharacter (positiveSignatureB L) z •
        (fullPhaseReferenceB n z R * referenceKrausB (physicalTensorKrausB n p) R L) := by
  simp only [referenceKrausB, fullPhaseReferenceB, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul]
  rw [physicalTensorKrausB_phase_intertwining, Matrix.smul_kronecker]

theorem krausSumB_phase_covariance {I Z : Type*} [Fintype I] [DecidableEq I]
    [Fintype Z] (K : Z → Matrix I I ℂ) (D : Matrix I I ℂ) (χ : Z → ℂ)
    (hKD : ∀ a, K a * D = χ a • (D * K a))
    (hχ : ∀ a, star (χ a) * χ a = 1) (ρ : Matrix I I ℂ) :
    krausSumB K (D * ρ * Dᴴ) = D * krausSumB K ρ * Dᴴ := by
  have hterm (a : Z) : K a * (D * ρ * Dᴴ) * (K a)ᴴ =
      D * (K a * ρ * (K a)ᴴ) * Dᴴ := by
    have hAdj : Dᴴ * (K a)ᴴ = star (χ a) • ((K a)ᴴ * Dᴴ) := by
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul] using
        congrArg (fun M : Matrix I I ℂ => Mᴴ) (hKD a)
    calc
      _ = (K a * D) * ρ * (Dᴴ * (K a)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = (χ a • (D * K a)) * ρ * (star (χ a) • ((K a)ᴴ * Dᴴ)) := by
        rw [hKD a, hAdj]
      _ = (star (χ a) * χ a) • (D * (K a * ρ * (K a)ᴴ) * Dᴴ) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = D * (K a * ρ * (K a)ᴴ) * Dᴴ := by
        rw [hχ a, one_smul]
  unfold krausSumB
  calc
    _ = ∑ a, D * (K a * ρ * (K a)ᴴ) * Dᴴ := by
      apply Finset.sum_congr rfl
      intro a _
      exact hterm a
    _ = D * (∑ a, K a * ρ * (K a)ᴴ) * Dᴴ := by
      rw [Matrix.mul_sum, Matrix.sum_mul]

theorem physicalTensorChannelB_reference_phase_covariance (n : ℕ) (p : ℝ)
    (z : Fin n → ZMod 3) (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (Finset (Fin n) × R) (Finset (Fin n) × R) ℂ) :
    krausSumB (referenceKrausB (physicalTensorKrausB n p) R)
        (fullPhaseReferenceB n z R * ρ * (fullPhaseReferenceB n z R)ᴴ) =
      fullPhaseReferenceB n z R *
        krausSumB (referenceKrausB (physicalTensorKrausB n p) R) ρ *
          (fullPhaseReferenceB n z R)ᴴ :=
  krausSumB_phase_covariance _ _ (fun L => wordCharacter (positiveSignatureB L) z)
    (fun L => physicalTensorKrausB_reference_phase_intertwining n p L z R)
    (fun L => wordCharacterB_unit n (positiveSignatureB L) z) ρ

theorem tensorDampingChannelB_reference_phase_covariance (n : ℕ) (p : ℝ)
    (z : Fin n → ZMod 3) (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (Finset (Fin n) × R) (Finset (Fin n) × R) ℂ) :
    krausSumB (referenceKrausB (tensorDampingKrausB n p) R)
        (fullPhaseReferenceB n z R * ρ * (fullPhaseReferenceB n z R)ᴴ) =
      fullPhaseReferenceB n z R *
        krausSumB (referenceKrausB (tensorDampingKrausB n p) R) ρ *
          (fullPhaseReferenceB n z R)ᴴ := by
  have hfamily : tensorDampingKrausB n p = physicalTensorKrausB n p := by
    funext L
    exact (physicalTensorKrausB_eq_damping n p L).symm
  rw [hfamily]
  exact physicalTensorChannelB_reference_phase_covariance n p z R ρ

theorem krausSumB_complete_of_trace {I O Z : Type*} [Fintype I] [Fintype O]
    [Fintype Z] [DecidableEq I] [DecidableEq O] (K : Z → Matrix O I ℂ)
    (htrace : ∀ ρ : Matrix I I ℂ, (krausSumB K ρ).trace = ρ.trace) :
    ∑ a, (K a)ᴴ * K a = 1 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro ρ
  rw [← krausSumB_trace, htrace, Matrix.one_mul]

theorem physicalSectorKrausB_complete (n w : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ L, (physicalSectorKrausB n w p L)ᴴ * physicalSectorKrausB n w p L = 1 := by
  have hfamily : tensorDampingSectorKrausB n w p = physicalSectorKrausB n w p := by
    funext L
    exact tensorDampingSectorKrausB_eq_physical n w p L
  have href := krausSumB_complete_of_trace
    (referenceKrausB (physicalSectorKrausB n w p) Unit) (fun ρ => by
      rw [← hfamily]
      exact tensorDampingSectorChannelB_reference_trace_preserving n w p hp0 hp1 Unit ρ)
  rw [referenceKrausB_gram] at href
  ext S U
  have he := congrArg (fun M : Matrix (WeightBasisB n w × Unit)
      (WeightBasisB n w × Unit) ℂ => M (S, ()) (U, ())) href
  simpa [Matrix.kronecker_apply, Matrix.one_apply] using he

theorem physicalTensorKrausB_gram_term_zero (n : ℕ) (p : ℝ)
    (L T S U : Finset (Fin n)) (hne : S ≠ U) :
    star (physicalTensorKrausB n p L T S) * physicalTensorKrausB n p L T U = 0 := by
  by_cases hS : L ⊆ S ∧ T = S \ L
  · by_cases hU : L ⊆ U ∧ T = U \ L
    · have hd : S \ L = U \ L := hS.2.symm.trans hU.2
      have hSU : S = U := by
        apply Finset.ext
        intro i
        by_cases hiL : i ∈ L
        · exact ⟨fun _ => hU.1 hiL, fun _ => hS.1 hiL⟩
        · have hi : i ∈ S \ L ↔ i ∈ U \ L := by rw [hd]
          simpa [Finset.mem_sdiff, hiL] using hi
      exact False.elim (hne hSU)
    · rw [physicalTensorKrausB_entry n p L T U, if_neg hU, mul_zero]
  · rw [physicalTensorKrausB_entry n p L T S, if_neg hS, star_zero, zero_mul]

theorem physicalTensorKrausB_gram_entry_zero (n : ℕ) (p : ℝ)
    (S U : Finset (Fin n)) (hne : S ≠ U) :
    (∑ L, (physicalTensorKrausB n p L)ᴴ * physicalTensorKrausB n p L) S U = 0 := by
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_eq_zero
  intro L _
  apply Finset.sum_eq_zero
  intro T _
  exact physicalTensorKrausB_gram_term_zero n p L T S U hne

theorem physicalTensorKrausB_complete (n : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ L, (physicalTensorKrausB n p L)ᴴ * physicalTensorKrausB n p L = 1 := by
  ext S U
  by_cases h : S = U
  · subst U
    let S' : WeightBasisB n S.card := ⟨S, rfl⟩
    have he := congrArg (fun M : Matrix (WeightBasisB n S.card)
        (WeightBasisB n S.card) ℂ => M S' S')
      (physicalSectorKrausB_complete n S.card p hp0 hp1)
    simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      physicalSectorKrausB, Matrix.one_apply, S'] using he
  · simpa [Matrix.one_apply, h] using physicalTensorKrausB_gram_entry_zero n p S U h

def fullRecordPhaseVectorB (n : ℕ) (z : Fin n → ZMod 3) : Finset (Fin n) → ℂ :=
  fun S => phaseSampleNormalizerB n * wordCharacter (positiveSignatureB S) z

theorem fullRecordPhaseVectorB_complete (n : ℕ) :
    ∑ z : Fin n → ZMod 3, Matrix.vecMulVec (fullRecordPhaseVectorB n z)
      (star (fullRecordPhaseVectorB n z)) = 1 := by
  have hN : (Fintype.card (Fin n → ZMod 3) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ = (star (phaseSampleNormalizerB n) * phaseSampleNormalizerB n) •
        ∑ z : Fin n → ZMod 3,
          Matrix.vecMulVec (fun S : Finset (Fin n) => wordCharacter (positiveSignatureB S) z)
            (star (fun S : Finset (Fin n) => wordCharacter (positiveSignatureB S) z)) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro z _
      exact vecMulVecB_scaled (fun S : Finset (Fin n) =>
        wordCharacter (positiveSignatureB S) z) (phaseSampleNormalizerB n)
    _ = 1 := by
      rw [phaseSampleNormalizerB_norm, phaseVectors_gram _ (positiveSignatureB_injective n)]
      simp [smul_smul, hN]

def fullRecordPhaseProbabilityB (n : ℕ) : ℝ := ((3 ^ n : ℕ) : ℝ)⁻¹

theorem fullRecordPhaseProbabilityB_complex (n : ℕ) :
    (fullRecordPhaseProbabilityB n : ℂ) = (Fintype.card (Fin n → ZMod 3) : ℂ)⁻¹ := by
  simp [fullRecordPhaseProbabilityB, phaseSampleB_card]

theorem fullRecordPhaseProbabilityB_nonneg (n : ℕ) : 0 ≤ fullRecordPhaseProbabilityB n :=
  inv_nonneg.mpr (Nat.cast_nonneg _)

theorem fullRecordPhaseProbabilityB_sum (n : ℕ) :
    ∑ z : Fin n → ZMod 3, (fullRecordPhaseProbabilityB n : ℂ) = 1 := by
  simp only [fullRecordPhaseProbabilityB_complex, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem phaseSampleNormalizerB_star (n : ℕ) : star (phaseSampleNormalizerB n) =
    phaseSampleNormalizerB n := by
  simp [phaseSampleNormalizerB]

def fullRecordCopyB (n : ℕ) :
    Matrix (Finset (Fin n) × Finset (Fin n)) (Finset (Fin n)) ℂ :=
  fun j S => if j = (S, S) then 1 else 0

theorem fullRecordCopyB_complete (n : ℕ) :
    (fullRecordCopyB n)ᴴ * fullRecordCopyB n = 1 := by
  ext S U
  rw [Matrix.mul_apply, Finset.sum_eq_single (S, S)]
  · simp [fullRecordCopyB, Matrix.conjTranspose_apply, Matrix.one_apply]
  · intro j _ hne
    simp [fullRecordCopyB, Matrix.conjTranspose_apply, hne]
  · intro h
    exact False.elim (h (Finset.mem_univ (S, S)))

theorem fullRecordCopyB_mul_entry {O : Type*} (n : ℕ)
    (M : Matrix O (Finset (Fin n) × Finset (Fin n)) ℂ)
    (o : O) (S : Finset (Fin n)) :
    (M * fullRecordCopyB n) o S = M o (S, S) := by
  simp [Matrix.mul_apply, fullRecordCopyB, mul_ite]

def fullRecordMeasurementB (n : ℕ) (z : Fin n → ZMod 3) :
    Matrix (Finset (Fin n)) (Finset (Fin n) × Finset (Fin n)) ℂ :=
  fun T j => if T = j.2 then star (fullRecordPhaseVectorB n z j.1) else 0

theorem fullRecordMeasurementB_gram_entry (n : ℕ) (z : Fin n → ZMod 3)
    (a b c d : Finset (Fin n)) :
    ((fullRecordMeasurementB n z)ᴴ * fullRecordMeasurementB n z) (a, b) (c, d) =
      if b = d then fullRecordPhaseVectorB n z a * star (fullRecordPhaseVectorB n z c)
      else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · simp [fullRecordMeasurementB, Matrix.conjTranspose_apply, mul_ite]
  · intro T _ hne
    simp [fullRecordMeasurementB, Matrix.conjTranspose_apply, hne]
  · intro h
    exact False.elim (h (Finset.mem_univ b))

theorem fullRecordMeasurementB_complete (n : ℕ) :
    ∑ z : Fin n → ZMod 3,
      (fullRecordMeasurementB n z)ᴴ * fullRecordMeasurementB n z = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.sum_apply, fullRecordMeasurementB_gram_entry]
  by_cases h : b = d
  · subst d
    have he := congrArg (fun M : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ => M a c)
      (fullRecordPhaseVectorB_complete n)
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      Matrix.one_apply] using he
  · simp [h, Matrix.one_apply]

def fullRecordPhysicalKrausB (n : ℕ) (p : ℝ) (z : Fin n → ZMod 3)
    (L : Finset (Fin n)) : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ :=
  fullRecordMeasurementB n z *
    ((1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ) ⊗ₖ physicalTensorKrausB n p L) *
      fullRecordCopyB n

theorem fullRecordPhysicalKrausB_entry (n : ℕ) (p : ℝ) (z : Fin n → ZMod 3)
    (L T S : Finset (Fin n)) :
    fullRecordPhysicalKrausB n p z L T S =
      star (fullRecordPhaseVectorB n z S) * physicalTensorKrausB n p L T S := by
  rw [fullRecordPhysicalKrausB, fullRecordCopyB_mul_entry]
  simp [Matrix.mul_apply, Fintype.sum_prod_type, fullRecordMeasurementB,
    Matrix.kronecker_apply, Matrix.one_apply, mul_ite, ite_mul]

theorem fullRecordPhysicalKrausB_eq_phase (n : ℕ) (p : ℝ) (z : Fin n → ZMod 3)
    (L : Finset (Fin n)) :
    fullRecordPhysicalKrausB n p z L = phaseSampleNormalizerB n •
      (physicalTensorKrausB n p L * (fullPhaseDiagonalB n z)ᴴ) := by
  ext T S
  rw [fullRecordPhysicalKrausB_entry]
  simp only [fullRecordPhaseVectorB, star_mul, phaseSampleNormalizerB_star,
    fullPhaseDiagonalB, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Pi.star_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem fullRecordStateB_card (n : ℕ) : Fintype.card (Finset (Fin n)) = 2 ^ n := by
  simp

theorem krausSumB_precompose {I Z : Type*} [Fintype I] [DecidableEq I] [Fintype Z]
    (K : Z → Matrix I I ℂ) (D ρ : Matrix I I ℂ) :
    krausSumB (fun a => K a * D) ρ = krausSumB K (D * ρ * Dᴴ) := by
  simp only [krausSumB, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem krausSumB_postcompose {I Z : Type*} [Fintype I] [DecidableEq I] [Fintype Z]
    (K : Z → Matrix I I ℂ) (D ρ : Matrix I I ℂ) :
    krausSumB (fun a => D * K a) ρ = D * krausSumB K ρ * Dᴴ := by
  unfold krausSumB
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem fullRecordPhysicalKrausB_reference_eq_phase (n : ℕ) (p : ℝ)
    (z : Fin n → ZMod 3) (R : Type*) [Fintype R] [DecidableEq R]
    (L : Finset (Fin n)) :
    referenceKrausB (fullRecordPhysicalKrausB n p z) R L = phaseSampleNormalizerB n •
      (referenceKrausB (physicalTensorKrausB n p) R L * (fullPhaseReferenceB n z R)ᴴ) := by
  simp only [referenceKrausB, fullRecordPhysicalKrausB_eq_phase, fullPhaseReferenceB,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.smul_kronecker]

theorem fullRecordConditionalBranchB_reference_eq (n : ℕ) (p : ℝ)
    (z : Fin n → ZMod 3) (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (Finset (Fin n) × R) (Finset (Fin n) × R) ℂ) :
    krausSumB (referenceKrausB (fullRecordPhysicalKrausB n p z) R) ρ =
      (fullRecordPhaseProbabilityB n : ℂ) •
        krausSumB (referenceKrausB (physicalTensorKrausB n p) R)
          ((fullPhaseReferenceB n z R)ᴴ * ρ * fullPhaseReferenceB n z R) := by
  have hfamily : referenceKrausB (fullRecordPhysicalKrausB n p z) R =
      fun L => phaseSampleNormalizerB n •
        (referenceKrausB (physicalTensorKrausB n p) R L * (fullPhaseReferenceB n z R)ᴴ) := by
    funext L
    exact fullRecordPhysicalKrausB_reference_eq_phase n p z R L
  rw [hfamily, krausSumB_smul, krausSumB_precompose, phaseSampleNormalizerB_norm,
    fullRecordPhaseProbabilityB_complex]
  simp only [Matrix.conjTranspose_conjTranspose]

def fullRecordCorrectedKrausB (n : ℕ) (p : ℝ) (z : Fin n → ZMod 3)
    (L : Finset (Fin n)) : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ :=
  fullPhaseDiagonalB n z * fullRecordPhysicalKrausB n p z L

theorem fullRecordCorrectedKrausB_reference_eq (n : ℕ) (p : ℝ)
    (z : Fin n → ZMod 3) (R : Type*) [Fintype R] [DecidableEq R]
    (L : Finset (Fin n)) :
    referenceKrausB (fullRecordCorrectedKrausB n p z) R L =
      fullPhaseReferenceB n z R * referenceKrausB (fullRecordPhysicalKrausB n p z) R L := by
  simp only [referenceKrausB, fullRecordCorrectedKrausB, fullPhaseReferenceB,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]

theorem fullRecordCorrectedBranchB_reference_eq (n : ℕ) (p : ℝ)
    (z : Fin n → ZMod 3) (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (Finset (Fin n) × R) (Finset (Fin n) × R) ℂ) :
    krausSumB (referenceKrausB (fullRecordCorrectedKrausB n p z) R) ρ =
      (fullRecordPhaseProbabilityB n : ℂ) •
        krausSumB (referenceKrausB (physicalTensorKrausB n p) R) ρ := by
  have hfamily : referenceKrausB (fullRecordCorrectedKrausB n p z) R =
      fun L => fullPhaseReferenceB n z R *
        referenceKrausB (fullRecordPhysicalKrausB n p z) R L := by
    funext L
    exact fullRecordCorrectedKrausB_reference_eq n p z R L
  rw [hfamily, krausSumB_postcompose, fullRecordConditionalBranchB_reference_eq,
    Matrix.mul_smul, Matrix.smul_mul]
  have hrestore : fullPhaseReferenceB n z R *
      ((fullPhaseReferenceB n z R)ᴴ * ρ * fullPhaseReferenceB n z R) *
        (fullPhaseReferenceB n z R)ᴴ = ρ := by
    calc
      _ = (fullPhaseReferenceB n z R * (fullPhaseReferenceB n z R)ᴴ) * ρ *
          (fullPhaseReferenceB n z R * (fullPhaseReferenceB n z R)ᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = ρ := by rw [fullPhaseReferenceB_mul_conjTranspose]; simp
  have hc := physicalTensorChannelB_reference_phase_covariance n p z R
    ((fullPhaseReferenceB n z R)ᴴ * ρ * fullPhaseReferenceB n z R)
  rw [hrestore] at hc
  exact congrArg (fun M => (fullRecordPhaseProbabilityB n : ℂ) • M) hc.symm

def fullRecordRecoveredKrausB (n : ℕ) (p : ℝ) :
    ((Fin n → ZMod 3) × Finset (Fin n)) →
      Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ :=
  fun j => fullRecordCorrectedKrausB n p j.1 j.2

theorem fullRecordRecoveredChannelB_reference_eq (n : ℕ) (p : ℝ)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (Finset (Fin n) × R) (Finset (Fin n) × R) ℂ) :
    krausSumB (referenceKrausB (fullRecordRecoveredKrausB n p) R) ρ =
      krausSumB (referenceKrausB (physicalTensorKrausB n p) R) ρ := by
  calc
    _ = ∑ z : Fin n → ZMod 3,
        krausSumB (referenceKrausB (fullRecordCorrectedKrausB n p z) R) ρ := by
      simp only [krausSumB, fullRecordRecoveredKrausB, referenceKrausB,
        Fintype.sum_prod_type]
    _ = ∑ z : Fin n → ZMod 3, (fullRecordPhaseProbabilityB n : ℂ) •
        krausSumB (referenceKrausB (physicalTensorKrausB n p) R) ρ := by
      apply Finset.sum_congr rfl
      intro z _
      exact fullRecordCorrectedBranchB_reference_eq n p z R ρ
    _ = _ := by rw [← Finset.sum_smul, fullRecordPhaseProbabilityB_sum, one_smul]

theorem fullRecordRecoveredKrausB_complete (n : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ j, (fullRecordRecoveredKrausB n p j)ᴴ * fullRecordRecoveredKrausB n p j = 1 := by
  have hphysical := referenceKrausB_complete (physicalTensorKrausB n p)
    (physicalTensorKrausB_complete n p hp0 hp1) Unit
  have href := krausSumB_complete_of_trace
    (referenceKrausB (fullRecordRecoveredKrausB n p) Unit) (fun ρ => by
      rw [fullRecordRecoveredChannelB_reference_eq]
      exact krausSumB_trace_preserving _ hphysical ρ)
  rw [referenceKrausB_gram] at href
  ext S U
  have he := congrArg (fun M : Matrix (Finset (Fin n) × Unit)
      (Finset (Fin n) × Unit) ℂ => M (S, ()) (U, ())) href
  simpa [Matrix.kronecker_apply, Matrix.one_apply] using he

theorem fullRecordRecoveredKrausB_reference_complete (n : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (R : Type*) [Fintype R] [DecidableEq R] :
    ∑ j, (referenceKrausB (fullRecordRecoveredKrausB n p) R j)ᴴ *
      referenceKrausB (fullRecordRecoveredKrausB n p) R j = 1 :=
  referenceKrausB_complete _ (fullRecordRecoveredKrausB_complete n p hp0 hp1) R

theorem fullRecordCorrectedBranchB_reference_trace (n : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : Fin n → ZMod 3)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (Finset (Fin n) × R) (Finset (Fin n) × R) ℂ) :
    (krausSumB (referenceKrausB (fullRecordCorrectedKrausB n p z) R) ρ).trace =
      (fullRecordPhaseProbabilityB n : ℂ) * ρ.trace := by
  rw [fullRecordCorrectedBranchB_reference_eq, Matrix.trace_smul,
    krausSumB_trace_preserving _ (referenceKrausB_complete _
      (physicalTensorKrausB_complete n p hp0 hp1) R)]
  rfl

theorem fullRecordCorrectedBranchB_reference_uniform (n : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (z : Fin n → ZMod 3)
    (R : Type*) [Fintype R] [DecidableEq R]
    (ρ : Matrix (Finset (Fin n) × R) (Finset (Fin n) × R) ℂ) (htrace : ρ.trace = 1) :
    (krausSumB (referenceKrausB (fullRecordCorrectedKrausB n p z) R) ρ).trace =
      (fullRecordPhaseProbabilityB n : ℂ) := by
  rw [fullRecordCorrectedBranchB_reference_trace n p hp0 hp1, htrace, mul_one]

def finiteIndexB (I : Type*) [Fintype I] : Fin (Fintype.card I) ≃ I :=
  (Fintype.equivFin I).symm

def krausInstrumentOfEquivsB {I O Z : Type*}
    [Fintype I] [Fintype O] [Fintype Z] [DecidableEq I] [DecidableEq O]
    {i o k : ℕ} (eI : Fin i ≃ I) (eO : Fin o ≃ O) (eZ : Fin k ≃ Z)
    (K : Z → Matrix O I ℂ) (hK : ∑ z, (K z)ᴴ * K z = 1) :
    KrausInstrument i o k where
  operator z := (K (eZ z)).submatrix eO eI
  complete := by
    simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    have hs : (∑ z : Fin k, ((K (eZ z))ᴴ * K (eZ z)).submatrix eI eI) =
        (∑ z : Z, (K z)ᴴ * K z).submatrix eI eI := by
      ext x y
      simp only [Matrix.sum_apply, Matrix.submatrix_apply]
      exact eZ.sum_comp (fun z => ((K z)ᴴ * K z) (eI x) (eI y))
    rw [hs, hK, Matrix.submatrix_one_equiv]

def krausInstrumentOfTypesB {I O Z : Type*}
    [Fintype I] [Fintype O] [Fintype Z] [DecidableEq I] [DecidableEq O]
    (K : Z → Matrix O I ℂ) (hK : ∑ z, (K z)ᴴ * K z = 1) :
    KrausInstrument (Fintype.card I) (Fintype.card O) (Fintype.card Z) :=
  krausInstrumentOfEquivsB (finiteIndexB I) (finiteIndexB O) (finiteIndexB Z) K hK

theorem krausGramB_memory_left {I O Z A : Type*}
    [Fintype I] [Fintype O] [Fintype Z] [Fintype A]
    [DecidableEq I] [DecidableEq O] [DecidableEq A]
    (K : Z → Matrix O I ℂ) :
    (∑ z, ((1 : Matrix A A ℂ) ⊗ₖ K z)ᴴ * ((1 : Matrix A A ℂ) ⊗ₖ K z)) =
      (1 : Matrix A A ℂ) ⊗ₖ (∑ z, (K z)ᴴ * K z) := by
  simp only [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Finset.mul_sum]

def fullRecordBraB (n : ℕ) (z : Fin n → ZMod 3) :
    Matrix Unit (Finset (Fin n)) ℂ :=
  fun _ S => star (fullRecordPhaseVectorB n z S)

theorem fullRecordBraB_gram (n : ℕ) (z : Fin n → ZMod 3) :
    (fullRecordBraB n z)ᴴ * fullRecordBraB n z =
      Matrix.vecMulVec (fullRecordPhaseVectorB n z) (star (fullRecordPhaseVectorB n z)) := by
  ext S U
  simp [fullRecordBraB, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.vecMulVec_apply, Pi.star_apply]

theorem fullRecordBraB_complete (n : ℕ) :
    ∑ z, (fullRecordBraB n z)ᴴ * fullRecordBraB n z = 1 := by
  simp only [fullRecordBraB_gram]
  exact fullRecordPhaseVectorB_complete n

def fullRecordMemoryBraB (n : ℕ) (A : Type*) [Fintype A] [DecidableEq A]
    (z : Fin n → ZMod 3) : Matrix A (A × Finset (Fin n)) ℂ :=
  fun a j => if a = j.1 then star (fullRecordPhaseVectorB n z j.2) else 0

theorem fullRecordMemoryBraB_gram_entry (n : ℕ) (A : Type*)
    [Fintype A] [DecidableEq A] (z : Fin n → ZMod 3)
    (a b : A) (S U : Finset (Fin n)) :
    ((fullRecordMemoryBraB n A z)ᴴ * fullRecordMemoryBraB n A z) (a, S) (b, U) =
      if a = b then fullRecordPhaseVectorB n z S * star (fullRecordPhaseVectorB n z U)
      else 0 := by
  by_cases h : a = b
  · subst b
    simp [fullRecordMemoryBraB, Matrix.mul_apply, Matrix.conjTranspose_apply,
      mul_ite, ite_mul]
  · simp [fullRecordMemoryBraB, Matrix.mul_apply, Matrix.conjTranspose_apply,
      mul_ite, ite_mul, h, Ne.symm h]

theorem fullRecordMemoryBraB_complete (n : ℕ) (A : Type*)
    [Fintype A] [DecidableEq A] :
    ∑ z, (fullRecordMemoryBraB n A z)ᴴ * fullRecordMemoryBraB n A z = 1 := by
  ext ⟨a, S⟩ ⟨b, U⟩
  simp only [Matrix.sum_apply, fullRecordMemoryBraB_gram_entry]
  by_cases h : a = b
  · subst b
    have he := congrArg (fun M : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ => M S U)
      (fullRecordPhaseVectorB_complete n)
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      Matrix.one_apply] using he
  · simp [h, Matrix.one_apply]

def fullRecordCopyInstrumentB (n : ℕ) (A : Type*) [Fintype A] [DecidableEq A] :
    KrausInstrument (Fintype.card (A × Finset (Fin n)))
      (Fintype.card (A × (Finset (Fin n) × Finset (Fin n)))) 1 :=
  krausInstrumentOfEquivsB (finiteIndexB _) (finiteIndexB _) (Equiv.refl (Fin 1))
    (fun _ => (1 : Matrix A A ℂ) ⊗ₖ fullRecordCopyB n) (by
      simpa [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        ← Matrix.mul_kronecker_mul, fullRecordCopyB_complete] using
        (Matrix.one_kronecker_one (α := ℂ) (m := A) (n := Finset (Fin n))))

def fullRecordFrameInstrumentB (n : ℕ) (A : Type*) [Fintype A] [DecidableEq A] :
    KrausInstrument (Fintype.card (A × Finset (Fin n))) (Fintype.card A)
      (Fintype.card (Fin n → ZMod 3)) :=
  krausInstrumentOfTypesB (fullRecordMemoryBraB n A) (fullRecordMemoryBraB_complete n A)

def fullRecordBobInstrumentB (n : ℕ) (B : Type*) [Fintype B] [DecidableEq B]
    (z : Fin n → ZMod 3) :
    KrausInstrument (Fintype.card (Finset (Fin n) × B))
      (Fintype.card (Finset (Fin n) × B)) 1 :=
  krausInstrumentOfEquivsB (finiteIndexB _) (finiteIndexB _) (Equiv.refl (Fin 1))
    (fun _ => fullPhaseDiagonalB n z ⊗ₖ (1 : Matrix B B ℂ)) (by
      simp [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        ← Matrix.mul_kronecker_mul, fullPhaseDiagonalB_conjTranspose_mul,
        Matrix.one_kronecker_one])

theorem aliceOperator_ofEquivsB {I O B : Type*}
    [Fintype I] [Fintype O] [Fintype B] [DecidableEq B]
    {i o b : ℕ} (eI : Fin i ≃ I) (eO : Fin o ≃ O) (eB : Fin b ≃ B)
    (K : Matrix O I ℂ) :
    aliceOperator (b := b) (K.submatrix eO eI) =
      (K ⊗ₖ (1 : Matrix B B ℂ)).submatrix (eO.prodCongr eB) (eI.prodCongr eB) := by
  ext ⟨x, y⟩ ⟨u, v⟩
  simp [aliceOperator, Matrix.kronecker_apply, Matrix.submatrix_apply,
    Matrix.one_apply, eB.injective.eq_iff]

theorem bobOperator_ofEquivsB {A I O : Type*}
    [Fintype A] [Fintype I] [Fintype O] [DecidableEq A]
    {a i o : ℕ} (eA : Fin a ≃ A) (eI : Fin i ≃ I) (eO : Fin o ≃ O)
    (K : Matrix O I ℂ) :
    bobOperator (a := a) (K.submatrix eO eI) =
      ((1 : Matrix A A ℂ) ⊗ₖ K).submatrix (eA.prodCongr eO) (eA.prodCongr eI) := by
  ext ⟨x, y⟩ ⟨u, v⟩
  simp [bobOperator, Matrix.kronecker_apply, Matrix.submatrix_apply,
    Matrix.one_apply, eA.injective.eq_iff]

theorem fullRecordMeasurementB_eq_local_bra (n : ℕ) (z : Fin n → ZMod 3) :
    fullRecordMeasurementB n z =
      (fullRecordBraB n z ⊗ₖ (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ)).submatrix
        (fun T => ((), T)) id := by
  ext T ⟨S, U⟩
  simp [fullRecordMeasurementB, fullRecordBraB, Matrix.kronecker_apply,
    Matrix.submatrix_apply, Matrix.one_apply, mul_ite]

def fullRecordRecoveryProtocolB (p : ℝ) (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    FiniteProtocol p (Fintype.card (A × Finset (Fin n)))
      (Fintype.card (Finset (Fin n) × B)) (Fintype.card A)
      (Fintype.card (Finset (Fin n) × B)) :=
  .alice (fullRecordFrameInstrumentB n A) fun j =>
    .bob (fullRecordBobInstrumentB n B (finiteIndexB (Fin n → ZMod 3) j)) fun _ =>
      .done _ _

theorem fullRecordRecoveryProtocolB_calls (p : ℝ) (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    (fullRecordRecoveryProtocolB p n A B).calls = 0 := by
  simp [fullRecordRecoveryProtocolB, FiniteProtocol.calls]

theorem fullRecordRecoveryProtocolB_output (p : ℝ) (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (ρ : BipartiteMatrix (Fintype.card (A × Finset (Fin n)))
      (Fintype.card (Finset (Fin n) × B))) :
    (fullRecordRecoveryProtocolB p n A B).output ρ =
      krausSumB (fun j =>
        bobOperator (a := Fintype.card A)
          ((fullRecordBobInstrumentB n B (finiteIndexB (Fin n → ZMod 3) j)).operator 0) *
        aliceOperator (b := Fintype.card (Finset (Fin n) × B))
          ((fullRecordFrameInstrumentB n A).operator j)) ρ := by
  simp [fullRecordRecoveryProtocolB, FiniteProtocol.output, krausSumB,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem krausSumB_submatrix_equiv {I O Z I' O' Z' : Type*}
    [Fintype I] [Fintype O] [Fintype Z] [Fintype I'] [Fintype O'] [Fintype Z']
    [DecidableEq I] [DecidableEq O] [DecidableEq I'] [DecidableEq O']
    (eI : I' ≃ I) (eO : O' ≃ O) (eZ : Z' ≃ Z)
    (K : Z → Matrix O I ℂ) (ρ : Matrix I I ℂ) :
    krausSumB (fun j => (K (eZ j)).submatrix eO eI) (ρ.submatrix eI eI) =
      (krausSumB K ρ).submatrix eO eO := by
  simp only [krausSumB, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  ext x y
  simp only [Matrix.sum_apply, Matrix.submatrix_apply]
  exact eZ.sum_comp (fun j => (K j * ρ * (K j)ᴴ) (eO x) (eO y))

def fullRecordLabCorrectionB (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (z : Fin n → ZMod 3) :
    Matrix (A × (Finset (Fin n) × B)) ((A × Finset (Fin n)) × (Finset (Fin n) × B)) ℂ :=
  ((1 : Matrix A A ℂ) ⊗ₖ (fullPhaseDiagonalB n z ⊗ₖ (1 : Matrix B B ℂ))) *
    (fullRecordMemoryBraB n A z ⊗ₖ
      (1 : Matrix (Finset (Fin n) × B) (Finset (Fin n) × B) ℂ))

theorem fullRecordLabCorrectionB_matrix (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (j : Fin (Fintype.card (Fin n → ZMod 3))) :
    bobOperator (a := Fintype.card A)
      ((fullRecordBobInstrumentB n B (finiteIndexB (Fin n → ZMod 3) j)).operator 0) *
      aliceOperator (b := Fintype.card (Finset (Fin n) × B))
        ((fullRecordFrameInstrumentB n A).operator j) =
    (fullRecordLabCorrectionB n A B (finiteIndexB (Fin n → ZMod 3) j)).submatrix
      ((finiteIndexB A).prodCongr (finiteIndexB (Finset (Fin n) × B)))
      ((finiteIndexB (A × Finset (Fin n))).prodCongr (finiteIndexB (Finset (Fin n) × B))) := by
  change bobOperator
      ((fullPhaseDiagonalB n (finiteIndexB (Fin n → ZMod 3) j) ⊗ₖ
        (1 : Matrix B B ℂ)).submatrix (finiteIndexB _) (finiteIndexB _)) *
      aliceOperator ((fullRecordMemoryBraB n A (finiteIndexB (Fin n → ZMod 3) j)).submatrix
        (finiteIndexB _) (finiteIndexB _)) = _
  rw [bobOperator_ofEquivsB (finiteIndexB A),
    aliceOperator_ofEquivsB (finiteIndexB (A × Finset (Fin n))) (finiteIndexB A)
      (finiteIndexB (Finset (Fin n) × B)), Matrix.submatrix_mul_equiv]
  rfl

theorem fullRecordRecoveryProtocolB_output_reindex (p : ℝ) (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (Ω : Matrix ((A × Finset (Fin n)) × (Finset (Fin n) × B))
      ((A × Finset (Fin n)) × (Finset (Fin n) × B)) ℂ) :
    (fullRecordRecoveryProtocolB p n A B).output
      (Ω.submatrix
        ((finiteIndexB (A × Finset (Fin n))).prodCongr (finiteIndexB (Finset (Fin n) × B)))
        ((finiteIndexB (A × Finset (Fin n))).prodCongr (finiteIndexB (Finset (Fin n) × B)))) =
      (krausSumB (fullRecordLabCorrectionB n A B) Ω).submatrix
        ((finiteIndexB A).prodCongr (finiteIndexB (Finset (Fin n) × B)))
        ((finiteIndexB A).prodCongr (finiteIndexB (Finset (Fin n) × B))) := by
  rw [fullRecordRecoveryProtocolB_output]
  simp only [fullRecordLabCorrectionB_matrix]
  exact krausSumB_submatrix_equiv _ _ (finiteIndexB (Fin n → ZMod 3)) _ Ω

def relabelInstrumentB {i o : ℕ} (e : Fin o ≃ Fin i) : KrausInstrument i o 1 :=
  krausInstrumentOfEquivsB (Equiv.refl (Fin i)) e (Equiv.refl (Fin 1))
    (fun _ => (1 : Matrix (Fin i) (Fin i) ℂ)) (by simp)

def doubleDimB : ℕ → ℕ → ℕ
  | 0, d => d
  | n + 1, d => doubleDimB n (2 * d)

theorem doubleDimB_double (n d : ℕ) : doubleDimB n (2 * d) = 2 * doubleDimB n d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => exact ih (2 * d)

theorem doubleDimB_eq_pow (n d : ℕ) : doubleDimB n d = 2 ^ n * d := by
  induction n generalizing d with
  | zero => simp [doubleDimB]
  | succ n ih => rw [doubleDimB, ih, pow_succ]; ring

def sequentialCallsProtocolB (p : ℝ) : (n a b : ℕ) →
    FiniteProtocol p (doubleDimB n a) b a (doubleDimB n b)
  | 0, a, b => .done a b
  | n + 1, a, b =>
      .alice (relabelInstrumentB (finCongr (doubleDimB_double n a)).symm) fun _ =>
        .call (sequentialCallsProtocolB p n a (2 * b))

theorem sequentialCallsProtocolB_calls (p : ℝ) (n a b : ℕ) :
    (sequentialCallsProtocolB p n a b).calls = n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    change (Finset.univ.sup fun _ : Fin 1 =>
      (sequentialCallsProtocolB p n a (2 * b)).calls + 1) = n + 1
    simp only [Finset.univ_unique, Finset.sup_singleton]
    exact congrArg (fun k : ℕ => k + 1) (ih (2 * b))

def sequentialCallsKrausB (p : ℝ) : (n a b : ℕ) → (Fin n → Qubit) →
    Matrix (Fin a × Fin (doubleDimB n b)) (Fin (doubleDimB n a) × Fin b) ℂ
  | 0, a, b, _ => by
      change Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ
      exact 1
  | n + 1, a, b, h =>
      sequentialCallsKrausB p n a (2 * b) (Fin.tail h) *
        callOperator p (doubleDimB n a) b (h 0) *
          aliceOperator (b := b)
            ((relabelInstrumentB (finCongr (doubleDimB_double n a)).symm).operator 0)

theorem krausSumB_rectangular_precompose {I J O Z : Type*}
    [Fintype I] [Fintype J] [Fintype O] [Fintype Z]
    [DecidableEq I] [DecidableEq J] [DecidableEq O]
    (K : Z → Matrix O J ℂ) (D : Matrix J I ℂ) (ρ : Matrix I I ℂ) :
    krausSumB (fun h => K h * D) ρ = krausSumB K (D * ρ * Dᴴ) := by
  simp only [krausSumB, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem krausSumB_compose {I J O Z Y : Type*}
    [Fintype I] [Fintype J] [Fintype O] [Fintype Z] [Fintype Y]
    [DecidableEq I] [DecidableEq J] [DecidableEq O]
    (K : Z → Matrix O J ℂ) (M : Y → Matrix J I ℂ) (ρ : Matrix I I ℂ) :
    krausSumB K (krausSumB M ρ) =
      krausSumB (fun h : Z × Y => K h.1 * M h.2) ρ := by
  simp only [krausSumB, Matrix.mul_sum, Matrix.sum_mul, Fintype.sum_prod_type,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem krausSumB_outcome_equiv {I O Z Y : Type*}
    [Fintype I] [Fintype O] [Fintype Z] [Fintype Y]
    [DecidableEq I] [DecidableEq O]
    (e : Y ≃ Z) (K : Z → Matrix O I ℂ) (ρ : Matrix I I ℂ) :
    krausSumB (fun h => K (e h)) ρ = krausSumB K ρ := by
  unfold krausSumB
  exact e.sum_comp (fun h => K h * ρ * (K h)ᴴ)

theorem sequentialCallsProtocolB_output (p : ℝ) (n a b : ℕ)
    (ρ : BipartiteMatrix (doubleDimB n a) b) :
    (sequentialCallsProtocolB p n a b).output ρ =
      krausSumB (sequentialCallsKrausB p n a b) ρ := by
  induction n generalizing b with
  | zero =>
    change BipartiteMatrix a b at ρ
    change ρ = krausSumB (fun _ : Fin 0 → Qubit =>
      (1 : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)) ρ
    simp [krausSumB]
  | succ n ih =>
    change BipartiteMatrix (doubleDimB n (2 * a)) b at ρ
    let A : Matrix (Fin (2 * doubleDimB n a) × Fin b)
        (Fin (doubleDimB n (2 * a)) × Fin b) ℂ := aliceOperator (b := b)
      ((relabelInstrumentB (finCongr (doubleDimB_double n a)).symm).operator 0)
    let C := callOperator p (doubleDimB n a) b
    have hs : (sequentialCallsProtocolB p (n + 1) a b).output ρ =
        krausSumB (sequentialCallsKrausB p n a (2 * b)) (krausSumB C (A * ρ * Aᴴ)) := by
      change (∑ j : Fin 1, (sequentialCallsProtocolB p n a (2 * b)).output
        (∑ q : Qubit, C q *
          (aliceOperator (b := b)
              ((relabelInstrumentB (finCongr (doubleDimB_double n a)).symm).operator j) *
            ρ * (aliceOperator (b := b)
              ((relabelInstrumentB (finCongr (doubleDimB_double n a)).symm).operator j))ᴴ) *
            (C q)ᴴ)) = _
      rw [Fin.sum_univ_one]
      exact ih (2 * b) (krausSumB C (A * ρ * Aᴴ))
    rw [hs, ← krausSumB_rectangular_precompose C A ρ, krausSumB_compose]
    let F : ((Fin n → Qubit) × Qubit) →
        Matrix (Fin a × Fin (doubleDimB n (2 * b)))
          (Fin (doubleDimB n (2 * a)) × Fin b) ℂ :=
      fun j => sequentialCallsKrausB p n a (2 * b) j.1 * (C j.2 * A)
    let e : (Fin (n + 1) → Qubit) ≃ ((Fin n → Qubit) × Qubit) :=
      (Fin.consEquiv (fun _ : Fin (n + 1) => Qubit)).symm.trans (Equiv.prodComm _ _)
    have hfamily : sequentialCallsKrausB p (n + 1) a b = fun h => F (e h) := by
      funext h
      change (sequentialCallsKrausB p n a (2 * b) (Fin.tail h) * C (h 0)) * A =
        sequentialCallsKrausB p n a (2 * b) (Fin.tail h) * (C (h 0) * A)
      exact Matrix.mul_assoc _ _ _
    rw [hfamily]
    change krausSumB F ρ = krausSumB (fun h => F (e h)) ρ
    exact (krausSumB_outcome_equiv e F ρ).symm

def emptyQubitWordEquivB (a : ℕ) : Fin a ≃ ((Fin 0 → Qubit) × Fin a) where
  toFun x := (Fin.elim0, x)
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := by
    apply Prod.ext
    · funext i
      exact Fin.elim0 i
    · rfl

def inputQubitWordEquivB : (n a : ℕ) →
    Fin (doubleDimB n a) ≃ ((Fin n → Qubit) × Fin a)
  | 0, a => emptyQubitWordEquivB a
  | n + 1, a =>
      (finCongr (doubleDimB_double n a)).trans
        ((splitQubit (doubleDimB n a)).trans
          (((Equiv.refl Qubit).prodCongr (inputQubitWordEquivB n a)).trans
            ((Equiv.prodAssoc Qubit (Fin n → Qubit) (Fin a)).symm.trans
              ((Fin.consEquiv (fun _ : Fin (n + 1) => Qubit)).prodCongr (Equiv.refl (Fin a))))))

def outputQubitWordEquivB : (n b : ℕ) →
    Fin (doubleDimB n b) ≃ ((Fin n → Qubit) × Fin b)
  | 0, b => emptyQubitWordEquivB b
  | n + 1, b =>
      (outputQubitWordEquivB n (2 * b)).trans
        (((Equiv.refl (Fin n → Qubit)).prodCongr (splitQubit b)).trans
          ((Equiv.prodAssoc (Fin n → Qubit) Qubit (Fin b)).symm.trans
            (((Equiv.prodComm (Fin n → Qubit) Qubit).prodCongr (Equiv.refl (Fin b))).trans
              ((Fin.consEquiv (fun _ : Fin (n + 1) => Qubit)).prodCongr (Equiv.refl (Fin b))))))

theorem inputQubitWordEquivB_succ (n a : ℕ) (x : Fin (doubleDimB (n + 1) a)) :
    inputQubitWordEquivB (n + 1) a x =
      (Fin.cons ((splitQubit (doubleDimB n a)) ((finCongr (doubleDimB_double n a)) x)).1
        (inputQubitWordEquivB n a
          (((splitQubit (doubleDimB n a)) ((finCongr (doubleDimB_double n a)) x)).2)).1,
      (inputQubitWordEquivB n a
        (((splitQubit (doubleDimB n a)) ((finCongr (doubleDimB_double n a)) x)).2)).2) := rfl

theorem outputQubitWordEquivB_succ (n b : ℕ) (x : Fin (doubleDimB (n + 1) b)) :
    outputQubitWordEquivB (n + 1) b x =
      (Fin.cons (splitQubit b (outputQubitWordEquivB n (2 * b) x).2).1
        (outputQubitWordEquivB n (2 * b) x).1,
      (splitQubit b (outputQubitWordEquivB n (2 * b) x).2).2) := rfl

theorem aliceRelabelOperatorB {i o b : ℕ} (e : Fin o ≃ Fin i) :
    aliceOperator (b := b) ((relabelInstrumentB e).operator 0) =
      (1 : Matrix (Fin i × Fin b) (Fin i × Fin b) ℂ).submatrix
        (e.prodCongr (Equiv.refl (Fin b))) id := by
  ext ⟨a, c⟩ ⟨d, f⟩
  by_cases ha : e a = d <;> by_cases hb : c = f <;>
    simp [aliceOperator, relabelInstrumentB, krausInstrumentOfEquivsB,
      Matrix.submatrix_apply, Matrix.one_apply, ha, hb]

theorem callMemoryContractionB {I A : Type*} [Fintype I]
    [DecidableEq I] [DecidableEq A] (b : ℕ) (p : ℝ) (z q : Qubit)
    (f : I → ℂ) (g : I → A) (a : A) (u : I) (v : Fin (2 * b)) (j : Fin b) :
    (∑ t : I, ∑ s : Fin (2 * b),
      (f t * if a = g t ∧ v = s then 1 else 0) *
      (dampingKraus p z (splitQubit b s).1 q *
        if t = u ∧ (splitQubit b s).2 = j then 1 else 0)) =
      (f u * dampingKraus p z (splitQubit b v).1 q) *
        if a = g u ∧ (splitQubit b v).2 = j then 1 else 0 := by
  classical
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single v]
    · by_cases hA : a = g u <;> by_cases hB : (splitQubit b v).2 = j <;> simp [hA, hB]
    · intro s _ hs
      simp [hs, Ne.symm hs]
    · simp
  · intro t _ ht
    simp [ht]
  · simp

theorem sequentialCallsKrausB_entry (p : ℝ) (n a b : ℕ) (h : Fin n → Qubit)
    (x : Fin a × Fin (doubleDimB n b)) (y : Fin (doubleDimB n a) × Fin b) :
    sequentialCallsKrausB p n a b h x y =
      (∏ i : Fin n, dampingKraus p (h i)
        ((outputQubitWordEquivB n b x.2).1 i) ((inputQubitWordEquivB n a y.1).1 i)) *
        if x.1 = (inputQubitWordEquivB n a y.1).2 ∧
          (outputQubitWordEquivB n b x.2).2 = y.2 then 1 else 0 := by
  induction n generalizing b with
  | zero =>
    change Fin a × Fin b at x
    change Fin a × Fin b at y
    simp [sequentialCallsKrausB, inputQubitWordEquivB,
      outputQubitWordEquivB, emptyQubitWordEquivB, doubleDimB,
      Matrix.one_apply, Prod.ext_iff]
    rfl
  | succ n ih =>
    change Fin a × Fin (doubleDimB n (2 * b)) at x
    change Fin (doubleDimB n (2 * a)) × Fin b at y
    rw [sequentialCallsKrausB, aliceRelabelOperatorB, Matrix.mul_submatrix_one]
    change (sequentialCallsKrausB p n a (2 * b) (Fin.tail h) *
      callOperator p (doubleDimB n a) b (h 0)) x
        ((finCongr (doubleDimB_double n a)) y.1, y.2) = _
    rw [Matrix.mul_apply]
    simp only [Fintype.sum_prod_type, ih, callOperator]
    rw [callMemoryContractionB]
    simp only [inputQubitWordEquivB_succ, outputQubitWordEquivB_succ,
      Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
    ac_rfl

def subsetQubitWordEquivB (n : ℕ) : Finset (Fin n) ≃ (Fin n → Qubit) where
  toFun S := fun i => boolQubitB (decide (i ∈ S))
  invFun h := Finset.univ.filter (fun i => h i = 1)
  left_inv S := by
    ext i
    by_cases hi : i ∈ S <;> simp [boolQubitB, hi]
  right_inv h := by
    funext i
    have hi : h i = 0 ∨ h i = 1 := by
      have hlt := (h i).isLt
      change (h i).val < 2 at hlt
      have hv : (h i).val = 0 ∨ (h i).val = 1 := by omega
      rcases hv with hv | hv
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr (Fin.ext hv)
    rcases hi with hi | hi <;> simp [boolQubitB, hi]

def sequentialInputEquivB (n a b : ℕ) :
    (Fin (doubleDimB n a) × Fin b) ≃ (Finset (Fin n) × (Fin a × Fin b)) :=
  ((inputQubitWordEquivB n a).prodCongr (Equiv.refl (Fin b))).trans
    ((Equiv.prodAssoc (Fin n → Qubit) (Fin a) (Fin b)).trans
      ((subsetQubitWordEquivB n).symm.prodCongr (Equiv.refl (Fin a × Fin b))))

def sequentialOutputEquivB (n a b : ℕ) :
    (Fin a × Fin (doubleDimB n b)) ≃ (Finset (Fin n) × (Fin a × Fin b)) :=
  ((Equiv.refl (Fin a)).prodCongr (outputQubitWordEquivB n b)).trans
    ((Equiv.prodAssoc (Fin a) (Fin n → Qubit) (Fin b)).symm.trans
      (((Equiv.prodComm (Fin a) (Fin n → Qubit)).prodCongr (Equiv.refl (Fin b))).trans
        ((Equiv.prodAssoc (Fin n → Qubit) (Fin a) (Fin b)).trans
          ((subsetQubitWordEquivB n).symm.prodCongr (Equiv.refl (Fin a × Fin b))))))

theorem subsetQubitWordEquivB_apply (n : ℕ) (S : Finset (Fin n)) (i : Fin n) :
    subsetQubitWordEquivB n S i = boolQubitB (decide (i ∈ S)) := rfl

theorem subsetQubitWordEquivB_symm_apply (n : ℕ) (h : Fin n → Qubit) (i : Fin n) :
    boolQubitB (decide (i ∈ (subsetQubitWordEquivB n).symm h)) = h i := by
  exact congrArg (fun w : Fin n → Qubit => w i)
    ((subsetQubitWordEquivB n).apply_symm_apply h)

theorem sequentialCallsKrausB_eq_physical (p : ℝ) (n a b : ℕ)
    (L : Finset (Fin n)) :
    sequentialCallsKrausB p n a b (subsetQubitWordEquivB n L) =
      (referenceKrausB (physicalTensorKrausB n p) (Fin a × Fin b) L).submatrix
        (sequentialOutputEquivB n a b) (sequentialInputEquivB n a b) := by
  ext x y
  rw [sequentialCallsKrausB_entry]
  simp only [referenceKrausB, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, sequentialInputEquivB, sequentialOutputEquivB,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodAssoc_apply,
    Equiv.prodAssoc_symm_apply, Equiv.prodComm_apply, Equiv.refl_apply,
    Prod.map_apply, Prod.ext_iff,
    physicalTensorKrausB, physicalBitEntryB_eq_damping,
    subsetQubitWordEquivB_apply, subsetQubitWordEquivB_symm_apply]
  rfl

theorem sequentialCallsProtocolB_output_physical (p : ℝ) (n a b : ℕ)
    (ρ : Matrix (Finset (Fin n) × (Fin a × Fin b))
      (Finset (Fin n) × (Fin a × Fin b)) ℂ) :
    (sequentialCallsProtocolB p n a b).output
      (ρ.submatrix (sequentialInputEquivB n a b) (sequentialInputEquivB n a b)) =
      (krausSumB (referenceKrausB (physicalTensorKrausB n p) (Fin a × Fin b)) ρ).submatrix
        (sequentialOutputEquivB n a b) (sequentialOutputEquivB n a b) := by
  rw [sequentialCallsProtocolB_output]
  have hfamily : sequentialCallsKrausB p n a b = fun h =>
      (referenceKrausB (physicalTensorKrausB n p) (Fin a × Fin b)
        ((subsetQubitWordEquivB n).symm h)).submatrix
          (sequentialOutputEquivB n a b) (sequentialInputEquivB n a b) := by
    funext h
    simpa using sequentialCallsKrausB_eq_physical p n a b ((subsetQubitWordEquivB n).symm h)
  rw [hfamily]
  exact krausSumB_submatrix_equiv _ _ (subsetQubitWordEquivB n).symm _ ρ

def sequentialCallsThenB (p : ℝ) {af bf : ℕ} :
    (n a b : ℕ) → FiniteProtocol p a (doubleDimB n b) af bf →
      FiniteProtocol p (doubleDimB n a) b af bf
  | 0, _, _, Q => Q
  | n + 1, a, b, Q =>
      .alice (relabelInstrumentB (finCongr (doubleDimB_double n a)).symm) fun _ =>
        .call (sequentialCallsThenB p n a (2 * b) Q)

theorem sequentialCallsThenB_calls (p : ℝ) (n a b af bf : ℕ)
    (Q : FiniteProtocol p a (doubleDimB n b) af bf) :
    (sequentialCallsThenB p n a b Q).calls = Q.calls + n := by
  induction n generalizing b with
  | zero =>
    simp [sequentialCallsThenB]
    rfl
  | succ n ih =>
    change FiniteProtocol p a (doubleDimB n (2 * b)) af bf at Q
    change (Finset.univ.sup fun _ : Fin 1 =>
      (sequentialCallsThenB p n a (2 * b) Q).calls + 1) = Q.calls + (n + 1)
    simp only [Finset.univ_unique, Finset.sup_singleton]
    rw [ih]; omega

theorem sequentialCallsThenB_output (p : ℝ) (n a b af bf : ℕ)
    (Q : FiniteProtocol p a (doubleDimB n b) af bf)
    (ρ : BipartiteMatrix (doubleDimB n a) b) :
    (sequentialCallsThenB p n a b Q).output ρ =
      Q.output ((sequentialCallsProtocolB p n a b).output ρ) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    change FiniteProtocol p a (doubleDimB n (2 * b)) af bf at Q
    change BipartiteMatrix (doubleDimB n (2 * a)) b at ρ
    let K := relabelInstrumentB (finCongr (doubleDimB_double n a)).symm
    change (∑ j : Fin 1, (sequentialCallsThenB p n a (2 * b) Q).output
      (∑ q : Qubit, callOperator p (doubleDimB n a) b q *
        (aliceOperator (b := b) (K.operator j) * ρ *
          (aliceOperator (b := b) (K.operator j))ᴴ) *
        (callOperator p (doubleDimB n a) b q)ᴴ)) =
      Q.output (∑ j : Fin 1, (sequentialCallsProtocolB p n a (2 * b)).output
        (∑ q : Qubit, callOperator p (doubleDimB n a) b q *
          (aliceOperator (b := b) (K.operator j) * ρ *
            (aliceOperator (b := b) (K.operator j))ᴴ) *
          (callOperator p (doubleDimB n a) b q)ᴴ))
    rw [Fin.sum_univ_one, Fin.sum_univ_one]
    exact ih (2 * b) Q _

def copiedPortInputEquivB (n : ℕ) (A : Type*) [Fintype A] :
    Fin (doubleDimB n (Fintype.card (A × Finset (Fin n)))) ≃
      (A × (Finset (Fin n) × Finset (Fin n))) :=
  (inputQubitWordEquivB n (Fintype.card (A × Finset (Fin n)))).trans
    (((subsetQubitWordEquivB n).symm.prodCongr (finiteIndexB (A × Finset (Fin n)))).trans
      ((Equiv.prodAssoc (Finset (Fin n)) A (Finset (Fin n))).symm.trans
        (((Equiv.prodComm (Finset (Fin n)) A).prodCongr
          (Equiv.refl (Finset (Fin n)))).trans
            ((Equiv.prodAssoc A (Finset (Fin n)) (Finset (Fin n))).trans
              ((Equiv.refl A).prodCongr (Equiv.prodComm (Finset (Fin n)) (Finset (Fin n))))))))

def receivedPortOutputEquivB (n : ℕ) (B : Type*) [Fintype B] :
    Fin (doubleDimB n (Fintype.card B)) ≃ (Finset (Fin n) × B) :=
  (outputQubitWordEquivB n (Fintype.card B)).trans
    ((subsetQubitWordEquivB n).symm.prodCongr (finiteIndexB B))

def fullRecordMatrixProtocolB (p : ℝ) (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    FiniteProtocol p (Fintype.card (A × Finset (Fin n))) (Fintype.card B)
      (Fintype.card A) (Fintype.card (Finset (Fin n) × B)) :=
  .alice (fullRecordCopyInstrumentB n A) fun _ =>
    .alice (relabelInstrumentB ((copiedPortInputEquivB n A).trans
      (Fintype.equivFin (A × (Finset (Fin n) × Finset (Fin n)))))) fun _ =>
        sequentialCallsThenB p n (Fintype.card (A × Finset (Fin n))) (Fintype.card B)
          (.bob (relabelInstrumentB ((finiteIndexB (Finset (Fin n) × B)).trans
            (receivedPortOutputEquivB n B).symm)) fun _ =>
              fullRecordRecoveryProtocolB p n A B)

theorem fullRecordMatrixProtocolB_calls (p : ℝ) (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    (fullRecordMatrixProtocolB p n A B).calls = n := by
  change (Finset.univ.sup fun _ : Fin 1 => Finset.univ.sup fun _ : Fin 1 =>
    (sequentialCallsThenB p n (Fintype.card (A × Finset (Fin n))) (Fintype.card B)
      (.bob (relabelInstrumentB ((finiteIndexB (Finset (Fin n) × B)).trans
        (receivedPortOutputEquivB n B).symm)) fun _ =>
          fullRecordRecoveryProtocolB p n A B)).calls) = n
  simp only [Finset.univ_unique, Finset.sup_singleton, sequentialCallsThenB_calls]
  simp [FiniteProtocol.calls, fullRecordRecoveryProtocolB_calls]

def inputPortMemoryEquivB (X A B : Type*) : ((A × X) × B) ≃ (X × (A × B)) where
  toFun x := (x.1.2, (x.1.1, x.2))
  invFun x := ((x.2.1, x.1), x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def outputPortMemoryEquivB (X A B : Type*) : (A × (X × B)) ≃ (X × (A × B)) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def copyPortMemoryEquivB (X A B : Type*) :
    ((A × (X × X)) × B) ≃ ((X × X) × (A × B)) where
  toFun x := (x.1.2, (x.1.1, x.2))
  invFun x := ((x.2.1, x.1), x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def recordPortMemoryEquivB (X A B : Type*) :
    ((A × X) × (X × B)) ≃ ((X × X) × (A × B)) where
  toFun x := ((x.1.2, x.2.1), (x.1.1, x.2.2))
  invFun x := ((x.2.1, x.1.1), (x.1.2, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem labBobMatrixB_eq_reference {X A B : Type*}
    [Fintype X] [Fintype A] [Fintype B]
    [DecidableEq X] [DecidableEq A] [DecidableEq B] (D : Matrix X X ℂ) :
    (1 : Matrix A A ℂ) ⊗ₖ (D ⊗ₖ (1 : Matrix B B ℂ)) =
      (referenceKrausB (fun _ : Unit => D) (A × B) ()).submatrix
        (outputPortMemoryEquivB X A B) (outputPortMemoryEquivB X A B) := by
  ext ⟨a, ⟨T, b⟩⟩ ⟨c, ⟨U, d⟩⟩
  by_cases ha : a = c <;> by_cases hb : b = d <;>
    simp [referenceKrausB, outputPortMemoryEquivB, Matrix.submatrix_apply,
      Matrix.kronecker_apply, Matrix.one_apply, Prod.ext_iff, ha, hb]

theorem labRecordBraB_eq_reference (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (z : Fin n → ZMod 3) :
    fullRecordMemoryBraB n A z ⊗ₖ
      (1 : Matrix (Finset (Fin n) × B) (Finset (Fin n) × B) ℂ) =
      (referenceKrausB (fun _ : Unit => fullRecordMeasurementB n z) (A × B) ()).submatrix
        (outputPortMemoryEquivB (Finset (Fin n)) A B)
        (recordPortMemoryEquivB (Finset (Fin n)) A B) := by
  ext ⟨a, ⟨T, b⟩⟩ ⟨⟨c, S⟩, ⟨U, d⟩⟩
  by_cases ha : a = c <;> by_cases hb : b = d <;> by_cases ht : T = U <;>
    simp [referenceKrausB, outputPortMemoryEquivB, recordPortMemoryEquivB,
      fullRecordMemoryBraB, fullRecordMeasurementB, Matrix.submatrix_apply,
      Matrix.kronecker_apply, Matrix.one_apply, Prod.ext_iff, ha, hb, ht]

theorem labRecordCopyB_eq_reference (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    ((1 : Matrix A A ℂ) ⊗ₖ fullRecordCopyB n) ⊗ₖ (1 : Matrix B B ℂ) =
      (referenceKrausB (fun _ : Unit => fullRecordCopyB n) (A × B) ()).submatrix
        (copyPortMemoryEquivB (Finset (Fin n)) A B)
        (inputPortMemoryEquivB (Finset (Fin n)) A B) := by
  ext ⟨⟨a, ⟨T, U⟩⟩, b⟩ ⟨⟨c, S⟩, d⟩
  by_cases ha : a = c <;> by_cases hb : b = d <;>
    simp [referenceKrausB, copyPortMemoryEquivB, inputPortMemoryEquivB,
      fullRecordCopyB, Matrix.submatrix_apply, Matrix.kronecker_apply,
      Matrix.one_apply, Prod.ext_iff, ha, hb]

theorem fullRecordLabCorrectionB_eq_reference (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (z : Fin n → ZMod 3) :
    fullRecordLabCorrectionB n A B z =
      (referenceKrausB (fun _ : Unit => fullPhaseDiagonalB n z * fullRecordMeasurementB n z)
        (A × B) ()).submatrix (outputPortMemoryEquivB (Finset (Fin n)) A B)
          (recordPortMemoryEquivB (Finset (Fin n)) A B) := by
  rw [fullRecordLabCorrectionB, labBobMatrixB_eq_reference, labRecordBraB_eq_reference,
    Matrix.submatrix_mul_equiv]
  simp only [referenceKrausB, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

def fullRecordMatrixPrefixB (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    Matrix (Fin (doubleDimB n (Fintype.card (A × Finset (Fin n)))) × Fin (Fintype.card B))
      (Fin (Fintype.card (A × Finset (Fin n))) × Fin (Fintype.card B)) ℂ :=
  aliceOperator (b := Fintype.card B)
    ((relabelInstrumentB ((copiedPortInputEquivB n A).trans
      (Fintype.equivFin (A × (Finset (Fin n) × Finset (Fin n)))))).operator 0) *
    aliceOperator (b := Fintype.card B) ((fullRecordCopyInstrumentB n A).operator 0)

def fullRecordMatrixPostB (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    Matrix (Fin (Fintype.card (A × Finset (Fin n))) × Fin (Fintype.card (Finset (Fin n) × B)))
      (Fin (Fintype.card (A × Finset (Fin n))) × Fin (doubleDimB n (Fintype.card B))) ℂ :=
  bobOperator (a := Fintype.card (A × Finset (Fin n)))
    ((relabelInstrumentB ((finiteIndexB (Finset (Fin n) × B)).trans
      (receivedPortOutputEquivB n B).symm)).operator 0)

def fullRecordMatrixCorrectionB (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (j : Fin (Fintype.card (Fin n → ZMod 3))) :
    Matrix (Fin (Fintype.card A) × Fin (Fintype.card (Finset (Fin n) × B)))
      (Fin (Fintype.card (A × Finset (Fin n))) × Fin (Fintype.card (Finset (Fin n) × B))) ℂ :=
  bobOperator (a := Fintype.card A)
    ((fullRecordBobInstrumentB n B (finiteIndexB (Fin n → ZMod 3) j)).operator 0) *
    aliceOperator (b := Fintype.card (Finset (Fin n) × B))
      ((fullRecordFrameInstrumentB n A).operator j)

def fullRecordMatrixKrausB (p : ℝ) (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (jh : Fin (Fintype.card (Fin n → ZMod 3)) × (Fin n → Qubit)) :
    Matrix (Fin (Fintype.card A) × Fin (Fintype.card (Finset (Fin n) × B)))
      (Fin (Fintype.card (A × Finset (Fin n))) × Fin (Fintype.card B)) ℂ :=
  ((fullRecordMatrixCorrectionB n A B jh.1 * fullRecordMatrixPostB n A B) *
    sequentialCallsKrausB p n (Fintype.card (A × Finset (Fin n))) (Fintype.card B) jh.2) *
      fullRecordMatrixPrefixB n A B

theorem fullRecordMatrixKrausB_map (p : ℝ) (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (ρ : BipartiteMatrix (Fintype.card (A × Finset (Fin n))) (Fintype.card B)) :
    krausSumB (fullRecordMatrixKrausB p n A B) ρ =
      krausSumB (fullRecordMatrixCorrectionB n A B)
        (fullRecordMatrixPostB n A B *
          krausSumB (sequentialCallsKrausB p n (Fintype.card (A × Finset (Fin n)))
            (Fintype.card B))
            (fullRecordMatrixPrefixB n A B * ρ * (fullRecordMatrixPrefixB n A B)ᴴ) *
              (fullRecordMatrixPostB n A B)ᴴ) := by
  rw [← krausSumB_rectangular_precompose, krausSumB_compose,
    ← krausSumB_rectangular_precompose]
  rfl

def matrixRecordInputChartB (n : ℕ) (A B : Type*) [Fintype A] [Fintype B] :
    (Fin (Fintype.card (A × Finset (Fin n))) × Fin (Fintype.card B)) ≃
      (Finset (Fin n) × (A × B)) :=
  ((finiteIndexB (A × Finset (Fin n))).prodCongr (finiteIndexB B)).trans
    (inputPortMemoryEquivB (Finset (Fin n)) A B)

def matrixRecordCopiedChartB (n : ℕ) (A B : Type*) [Fintype A] [Fintype B] :
    (Fin (doubleDimB n (Fintype.card (A × Finset (Fin n)))) × Fin (Fintype.card B)) ≃
      ((Finset (Fin n) × Finset (Fin n)) × (A × B)) :=
  ((copiedPortInputEquivB n A).prodCongr (finiteIndexB B)).trans
    (copyPortMemoryEquivB (Finset (Fin n)) A B)

def matrixRecordReceivedChartB (n : ℕ) (A B : Type*) [Fintype A] [Fintype B] :
    (Fin (Fintype.card (A × Finset (Fin n))) × Fin (doubleDimB n (Fintype.card B))) ≃
      ((Finset (Fin n) × Finset (Fin n)) × (A × B)) :=
  ((finiteIndexB (A × Finset (Fin n))).prodCongr (receivedPortOutputEquivB n B)).trans
    (recordPortMemoryEquivB (Finset (Fin n)) A B)

def matrixRecordFrameChartB (n : ℕ) (A B : Type*) [Fintype A] [Fintype B] :
    (Fin (Fintype.card (A × Finset (Fin n))) ×
      Fin (Fintype.card (Finset (Fin n) × B))) ≃
        ((Finset (Fin n) × Finset (Fin n)) × (A × B)) :=
  ((finiteIndexB (A × Finset (Fin n))).prodCongr
    (finiteIndexB (Finset (Fin n) × B))).trans
      (recordPortMemoryEquivB (Finset (Fin n)) A B)

def matrixRecordOutputChartB (n : ℕ) (A B : Type*) [Fintype A] [Fintype B] :
    (Fin (Fintype.card A) × Fin (Fintype.card (Finset (Fin n) × B))) ≃
      (Finset (Fin n) × (A × B)) :=
  ((finiteIndexB A).prodCongr (finiteIndexB (Finset (Fin n) × B))).trans
    (outputPortMemoryEquivB (Finset (Fin n)) A B)

theorem aliceRelabel_mulB {i o b : ℕ} {J : Type*} (e : Fin o ≃ Fin i)
    (M : Matrix (Fin i × Fin b) J ℂ) :
    aliceOperator (b := b) ((relabelInstrumentB e).operator 0) * M =
      M.submatrix (e.prodCongr (Equiv.refl (Fin b))) id := by
  rw [aliceRelabelOperatorB]
  simpa only [Equiv.refl_symm, Equiv.coe_refl, Function.id_comp] using
    Matrix.one_submatrix_mul (e.prodCongr (Equiv.refl (Fin b)))
      (Equiv.refl (Fin i × Fin b)) M

theorem bobRelabelOperatorB {a i o : ℕ} (e : Fin o ≃ Fin i) :
    bobOperator (a := a) ((relabelInstrumentB e).operator 0) =
      (1 : Matrix (Fin a × Fin i) (Fin a × Fin i) ℂ).submatrix
        ((Equiv.refl (Fin a)).prodCongr e) id := by
  ext ⟨c, x⟩ ⟨d, y⟩
  by_cases ha : c = d <;> by_cases hb : e x = y <;>
    simp [bobOperator, relabelInstrumentB, krausInstrumentOfEquivsB,
      Matrix.submatrix_apply, Matrix.one_apply, ha, hb]

theorem fullRecordMatrixPrefixB_eq_reference (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    fullRecordMatrixPrefixB n A B =
      (referenceKrausB (fun _ : Unit => fullRecordCopyB n) (A × B) ()).submatrix
        (matrixRecordCopiedChartB n A B) (matrixRecordInputChartB n A B) := by
  unfold fullRecordMatrixPrefixB
  rw [aliceRelabel_mulB]
  change (aliceOperator (b := Fintype.card B)
    (((1 : Matrix A A ℂ) ⊗ₖ fullRecordCopyB n).submatrix
      (finiteIndexB (A × (Finset (Fin n) × Finset (Fin n))))
      (finiteIndexB (A × Finset (Fin n))))).submatrix _ id = _
  rw [aliceOperator_ofEquivsB (finiteIndexB (A × Finset (Fin n)))
    (finiteIndexB (A × (Finset (Fin n) × Finset (Fin n)))) (finiteIndexB B),
    labRecordCopyB_eq_reference]
  simp only [Matrix.submatrix_submatrix]
  ext ⟨xA, xB⟩ ⟨yA, yB⟩
  simp [matrixRecordCopiedChartB, matrixRecordInputChartB, finiteIndexB,
    Matrix.submatrix_apply, Function.comp_apply, Prod.map_apply]

theorem fullRecordMatrixPostB_eq_reference (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    fullRecordMatrixPostB n A B =
      (1 : Matrix ((Finset (Fin n) × Finset (Fin n)) × (A × B))
        ((Finset (Fin n) × Finset (Fin n)) × (A × B)) ℂ).submatrix
          (matrixRecordFrameChartB n A B) (matrixRecordReceivedChartB n A B) := by
  unfold fullRecordMatrixPostB
  rw [bobRelabelOperatorB]
  have hi : (1 : Matrix
      (Fin (Fintype.card (A × Finset (Fin n))) × Fin (doubleDimB n (Fintype.card B)))
      (Fin (Fintype.card (A × Finset (Fin n))) × Fin (doubleDimB n (Fintype.card B))) ℂ) =
      (1 : Matrix ((Finset (Fin n) × Finset (Fin n)) × (A × B))
        ((Finset (Fin n) × Finset (Fin n)) × (A × B)) ℂ).submatrix
          (matrixRecordReceivedChartB n A B) (matrixRecordReceivedChartB n A B) :=
    (Matrix.submatrix_one_equiv (matrixRecordReceivedChartB n A B)).symm
  rw [hi, Matrix.submatrix_submatrix]
  ext ⟨xA, xB⟩ ⟨yA, yB⟩
  change (1 : Matrix ((Finset (Fin n) × Finset (Fin n)) × (A × B))
      ((Finset (Fin n) × Finset (Fin n)) × (A × B)) ℂ)
      (recordPortMemoryEquivB (Finset (Fin n)) A B
        (finiteIndexB (A × Finset (Fin n)) xA,
          receivedPortOutputEquivB n B
            ((receivedPortOutputEquivB n B).symm (finiteIndexB (Finset (Fin n) × B) xB))))
      (matrixRecordReceivedChartB n A B (yA, yB)) =
    (1 : Matrix ((Finset (Fin n) × Finset (Fin n)) × (A × B))
      ((Finset (Fin n) × Finset (Fin n)) × (A × B)) ℂ)
      (recordPortMemoryEquivB (Finset (Fin n)) A B
        (finiteIndexB (A × Finset (Fin n)) xA, finiteIndexB (Finset (Fin n) × B) xB))
      (matrixRecordReceivedChartB n A B (yA, yB))
  rw [Equiv.apply_symm_apply]

theorem fullRecordMatrixCorrectionB_eq_reference (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (j : Fin (Fintype.card (Fin n → ZMod 3))) :
    fullRecordMatrixCorrectionB n A B j =
      (referenceKrausB (fun _ : Unit =>
        fullPhaseDiagonalB n (finiteIndexB (Fin n → ZMod 3) j) *
          fullRecordMeasurementB n (finiteIndexB (Fin n → ZMod 3) j)) (A × B) ()).submatrix
            (matrixRecordOutputChartB n A B) (matrixRecordFrameChartB n A B) := by
  rw [fullRecordMatrixCorrectionB, fullRecordLabCorrectionB_matrix,
    fullRecordLabCorrectionB_eq_reference]
  simp only [Matrix.submatrix_submatrix]
  rfl

theorem fullRecordSequentialKrausB_eq_reference (p : ℝ) (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (L : Finset (Fin n)) :
    sequentialCallsKrausB p n (Fintype.card (A × Finset (Fin n)))
      (Fintype.card B) (subsetQubitWordEquivB n L) =
        (referenceKrausB (fun _ : Unit =>
          (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) ℂ) ⊗ₖ physicalTensorKrausB n p L)
            (A × B) ()).submatrix
              (matrixRecordReceivedChartB n A B) (matrixRecordCopiedChartB n A B) := by
  ext x y
  rw [sequentialCallsKrausB_entry]
  have hm : x.1 = (inputQubitWordEquivB n (Fintype.card (A × Finset (Fin n))) y.1).2 ↔
      (finiteIndexB (A × Finset (Fin n)) x.1).1 =
        (finiteIndexB (A × Finset (Fin n))
          (inputQubitWordEquivB n (Fintype.card (A × Finset (Fin n))) y.1).2).1 ∧
      (finiteIndexB (A × Finset (Fin n)) x.1).2 =
        (finiteIndexB (A × Finset (Fin n))
          (inputQubitWordEquivB n (Fintype.card (A × Finset (Fin n))) y.1).2).2 :=
    (finiteIndexB (A × Finset (Fin n))).injective.eq_iff.symm.trans Prod.ext_iff
  have hb : (outputQubitWordEquivB n (Fintype.card B) x.2).2 = y.2 ↔
      finiteIndexB B (outputQubitWordEquivB n (Fintype.card B) x.2).2 = finiteIndexB B y.2 :=
    (finiteIndexB B).injective.eq_iff.symm
  by_cases hA : (finiteIndexB (A × Finset (Fin n)) x.1).1 =
      (finiteIndexB (A × Finset (Fin n))
        (inputQubitWordEquivB n (Fintype.card (A × Finset (Fin n))) y.1).2).1 <;>
    by_cases hR : (finiteIndexB (A × Finset (Fin n)) x.1).2 =
      (finiteIndexB (A × Finset (Fin n))
        (inputQubitWordEquivB n (Fintype.card (A × Finset (Fin n))) y.1).2).2 <;>
    by_cases hB : finiteIndexB B (outputQubitWordEquivB n (Fintype.card B) x.2).2 =
      finiteIndexB B y.2 <;>
    simp [matrixRecordReceivedChartB, matrixRecordCopiedChartB, copiedPortInputEquivB,
      receivedPortOutputEquivB, recordPortMemoryEquivB, copyPortMemoryEquivB,
      referenceKrausB, Matrix.submatrix_apply, Matrix.one_apply, Prod.ext_iff,
      physicalTensorKrausB, physicalBitEntryB_eq_damping, subsetQubitWordEquivB_apply,
      subsetQubitWordEquivB_symm_apply, hm, hb, hA, hR, hB]

theorem fullRecordMatrixKrausB_eq_reference (p : ℝ) (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (j : Fin (Fintype.card (Fin n → ZMod 3))) (L : Finset (Fin n)) :
    fullRecordMatrixKrausB p n A B (j, subsetQubitWordEquivB n L) =
      (referenceKrausB (fullRecordCorrectedKrausB n p
        (finiteIndexB (Fin n → ZMod 3) j)) (A × B) L).submatrix
          (matrixRecordOutputChartB n A B) (matrixRecordInputChartB n A B) := by
  rw [fullRecordMatrixKrausB, fullRecordMatrixCorrectionB_eq_reference,
    fullRecordMatrixPostB_eq_reference, Matrix.submatrix_mul_equiv, Matrix.mul_one,
    fullRecordSequentialKrausB_eq_reference, Matrix.submatrix_mul_equiv,
    fullRecordMatrixPrefixB_eq_reference, Matrix.submatrix_mul_equiv]
  simp only [referenceKrausB, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  simp only [fullRecordCorrectedKrausB, fullRecordPhysicalKrausB, Matrix.mul_assoc]

theorem fullRecordMatrixProtocolB_output (p : ℝ) (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (ρ : BipartiteMatrix (Fintype.card (A × Finset (Fin n))) (Fintype.card B)) :
    (fullRecordMatrixProtocolB p n A B).output ρ =
      krausSumB (fullRecordMatrixKrausB p n A B) ρ := by
  rw [fullRecordMatrixKrausB_map]
  simp only [fullRecordMatrixProtocolB, FiniteProtocol.output, Fin.sum_univ_one]
  rw [sequentialCallsThenB_output]
  simp only [FiniteProtocol.output, Fin.sum_univ_one]
  rw [sequentialCallsProtocolB_output, fullRecordRecoveryProtocolB_output]
  simp only [fullRecordMatrixPrefixB, fullRecordMatrixPostB, fullRecordMatrixCorrectionB,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rfl

theorem fullRecordMatrixProtocolB_output_physical (p : ℝ) (n : ℕ) (A B : Type*)
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (ρ : Matrix (Finset (Fin n) × (A × B)) (Finset (Fin n) × (A × B)) ℂ) :
    (fullRecordMatrixProtocolB p n A B).output
      (ρ.submatrix (matrixRecordInputChartB n A B) (matrixRecordInputChartB n A B)) =
        (krausSumB (referenceKrausB (physicalTensorKrausB n p) (A × B)) ρ).submatrix
          (matrixRecordOutputChartB n A B) (matrixRecordOutputChartB n A B) := by
  rw [fullRecordMatrixProtocolB_output]
  let e : (Fin (Fintype.card (Fin n → ZMod 3)) × (Fin n → Qubit)) ≃
      ((Fin n → ZMod 3) × Finset (Fin n)) :=
    (finiteIndexB (Fin n → ZMod 3)).prodCongr (subsetQubitWordEquivB n).symm
  have hf : fullRecordMatrixKrausB p n A B = fun jh =>
      (referenceKrausB (fullRecordRecoveredKrausB n p) (A × B) (e jh)).submatrix
        (matrixRecordOutputChartB n A B) (matrixRecordInputChartB n A B) := by
    funext jh
    rcases jh with ⟨j, h⟩
    simpa only [e, Equiv.prodCongr_apply, Prod.map_apply, fullRecordRecoveredKrausB,
      referenceKrausB, Equiv.apply_symm_apply] using
      fullRecordMatrixKrausB_eq_reference p n A B j ((subsetQubitWordEquivB n).symm h)
  rw [hf, krausSumB_submatrix_equiv]
  rw [fullRecordRecoveredChannelB_reference_eq]

def groundPrepareKrausB (a : ℕ) : Matrix (Qubit × Fin a) (Fin a) ℂ :=
  fun x y => if x.1 = 0 ∧ x.2 = y then 1 else 0

theorem groundPrepareKrausB_complete (a : ℕ) :
    (groundPrepareKrausB a)ᴴ * groundPrepareKrausB a = 1 := by
  ext i j
  by_cases hij : i = j <;>
    simp [groundPrepareKrausB, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, hij, eq_comm,
      mul_ite, ite_mul]

def groundPrepareInstrumentB (a : ℕ) : KrausInstrument a (2 * a) 1 :=
  krausInstrumentOfEquivsB (Equiv.refl (Fin a)) (splitQubit a) (Equiv.refl (Fin 1))
    (fun _ => groundPrepareKrausB a) (by
      simpa only [Fin.sum_univ_one] using groundPrepareKrausB_complete a)

def discardQubitKrausB (b : ℕ) (r : Qubit) : Matrix (Fin b) (Qubit × Fin b) ℂ :=
  fun x y => if y.1 = r ∧ x = y.2 then 1 else 0

theorem discardQubitKrausB_complete (b : ℕ) :
    ∑ r : Qubit, (discardQubitKrausB b r)ᴴ * discardQubitKrausB b r = 1 := by
  ext ⟨q, i⟩ ⟨r, j⟩
  fin_cases q <;> fin_cases r <;> by_cases hij : i = j <;>
    simp [discardQubitKrausB, Matrix.sum_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.one_apply,
      Prod.ext_iff, hij, eq_comm, mul_ite, ite_mul]

def discardQubitInstrumentB (b : ℕ) : KrausInstrument (2 * b) b 2 :=
  krausInstrumentOfEquivsB (splitQubit b) (Equiv.refl (Fin b)) (Equiv.refl Qubit)
    (discardQubitKrausB b) (discardQubitKrausB_complete b)

theorem discard_groundPrepareKrausB (b : ℕ) (r : Qubit) :
    discardQubitKrausB b r * groundPrepareKrausB b = if r = 0 then 1 else 0 := by
  ext i j
  fin_cases r <;> by_cases hij : i = j <;>
    simp [discardQubitKrausB, groundPrepareKrausB, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, hij, eq_comm,
      mul_ite, ite_mul]

theorem discard_groundPrepareInstrumentB (b : ℕ) (r : Qubit) :
    (discardQubitInstrumentB b).operator r * (groundPrepareInstrumentB b).operator 0 =
      if r = 0 then 1 else 0 := by
  change (discardQubitKrausB b r).submatrix (Equiv.refl (Fin b)) (splitQubit b) *
      (groundPrepareKrausB b).submatrix (splitQubit b) (Equiv.refl (Fin b)) = _
  rw [Matrix.submatrix_mul_equiv, discard_groundPrepareKrausB]
  by_cases hr : r = 0 <;> simp [hr, Matrix.submatrix_one_equiv]

theorem dampingKraus_ground_entryB (p : ℝ) (z q : Qubit) :
    dampingKraus p z q 0 = if z = 0 ∧ q = 0 then 1 else 0 := by
  fin_cases z <;> fin_cases q <;>
    simp [dampingKraus, dampingNoLoss, dampingLoss]

theorem callOperator_groundPrepareB (p : ℝ) (a b : ℕ) (z : Qubit) :
    callOperator p a b z * aliceOperator (b := b) ((groundPrepareInstrumentB a).operator 0) =
      if z = 0 then bobOperator (a := a) ((groundPrepareInstrumentB b).operator 0) else 0 := by
  ext ⟨xA, xB⟩ ⟨yA, yB⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [← (splitQubit a).symm.sum_comp (fun t : Fin (2 * a) =>
    ∑ u : Fin b, callOperator p a b z (xA, xB) (t, u) *
      aliceOperator (b := b) ((groundPrepareInstrumentB a).operator 0) (t, u) (yA, yB))]
  by_cases hz : z = 0 <;> by_cases ha : xA = yA <;>
    by_cases hq : (splitQubit b xB).1 = 0 <;>
    by_cases hb : (splitQubit b xB).2 = yB <;>
    simp [callOperator, aliceOperator, bobOperator, groundPrepareInstrumentB,
      krausInstrumentOfEquivsB, groundPrepareKrausB, Matrix.submatrix_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      dampingKraus_ground_entryB, hz, ha, hq, hb, ite_and, mul_ite, ite_mul]

def idleCallKrausB (p : ℝ) (a b : ℕ) (r z : Qubit) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
  bobOperator (a := a) ((discardQubitInstrumentB b).operator r) * callOperator p a b z *
    aliceOperator (b := b) ((groundPrepareInstrumentB a).operator 0)

theorem idleCallKrausB_eq_identity (p : ℝ) (a b : ℕ) (r z : Qubit) :
    idleCallKrausB p a b r z = if r = 0 ∧ z = 0 then 1 else 0 := by
  rw [idleCallKrausB, Matrix.mul_assoc, callOperator_groundPrepareB]
  by_cases hz : z = 0
  · subst z
    simp only [ite_true]
    change bobOperator (a := a) ((discardQubitInstrumentB b).operator r) *
      bobOperator (a := a) ((groundPrepareInstrumentB b).operator 0) = _
    rw [bobOperator, bobOperator, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
      discard_groundPrepareInstrumentB]
    by_cases hr : r = 0 <;> simp [hr, Matrix.one_kronecker_one]
  · simp [hz]

def idleCallThenB (p : ℝ) {a b af bf : ℕ} (Q : FiniteProtocol p a b af bf) :
    FiniteProtocol p a b af bf :=
  .alice (groundPrepareInstrumentB a) fun _ =>
    .call (.bob (discardQubitInstrumentB b) fun _ => Q)

theorem idleCallThenB_calls (p : ℝ) {a b af bf : ℕ} (Q : FiniteProtocol p a b af bf) :
    (idleCallThenB p Q).calls = Q.calls + 1 := by
  simp [idleCallThenB, FiniteProtocol.calls]
  exact Finset.sup_const Finset.univ_nonempty Q.calls

theorem idleCallThenB_output (p : ℝ) {a b af bf : ℕ} (Q : FiniteProtocol p a b af bf)
    (ρ : BipartiteMatrix a b) : (idleCallThenB p Q).output ρ = Q.output ρ := by
  have hb (r : Qubit) :
      bobOperator (a := a) ((discardQubitInstrumentB b).operator r) *
        (∑ z : Qubit, callOperator p a b z *
          (aliceOperator (b := b) ((groundPrepareInstrumentB a).operator 0) * ρ *
            (aliceOperator (b := b) ((groundPrepareInstrumentB a).operator 0))ᴴ) *
          (callOperator p a b z)ᴴ) *
        (bobOperator (a := a) ((discardQubitInstrumentB b).operator r))ᴴ =
          if r = 0 then ρ else 0 := by
    calc
      _ = krausSumB (idleCallKrausB p a b r) ρ := by
        simp only [krausSumB, idleCallKrausB, Matrix.mul_sum, Matrix.sum_mul,
          Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by
        fin_cases r <;> simp [krausSumB, idleCallKrausB_eq_identity, Fin.sum_univ_two]
  simp only [idleCallThenB, FiniteProtocol.output, Fin.sum_univ_one]
  simp only [hb]
  rw [Fin.sum_univ_two]
  simp

def idleCallsThenB (p : ℝ) {a b af bf : ℕ} :
    ℕ → FiniteProtocol p a b af bf → FiniteProtocol p a b af bf
  | 0, Q => Q
  | n + 1, Q => idleCallThenB p (idleCallsThenB p n Q)

theorem idleCallsThenB_calls (p : ℝ) {a b af bf : ℕ}
    (n : ℕ) (Q : FiniteProtocol p a b af bf) :
    (idleCallsThenB p n Q).calls = Q.calls + n := by
  induction n with
  | zero => simp [idleCallsThenB]
  | succ n ih => rw [idleCallsThenB, idleCallThenB_calls, ih]; omega

theorem idleCallsThenB_output (p : ℝ) {a b af bf : ℕ}
    (n : ℕ) (Q : FiniteProtocol p a b af bf) (ρ : BipartiteMatrix a b) :
    (idleCallsThenB p n Q).output ρ = Q.output ρ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [idleCallsThenB, idleCallThenB_output, ih]

def FiniteProtocol.UniformCallsB {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) (m : ℕ) : Prop :=
  match P with
  | .done _ _ => m = 0
  | .alice _ next => ∀ z, (next z).UniformCallsB m
  | .bob _ next => ∀ z, (next z).UniformCallsB m
  | .call next => ∃ k, m = k + 1 ∧ next.UniformCallsB k

theorem idleCallThenB_uniformCalls (p : ℝ) {a b af bf m : ℕ}
    {Q : FiniteProtocol p a b af bf} (hQ : Q.UniformCallsB m) :
    (idleCallThenB p Q).UniformCallsB (m + 1) := by
  change ∀ _ : Fin 1, ∃ k, m + 1 = k + 1 ∧ ∀ _ : Qubit, Q.UniformCallsB k
  intro _
  exact ⟨m, rfl, fun _ => hQ⟩

theorem idleCallsThenB_uniformCalls (p : ℝ) {a b af bf m : ℕ}
    (n : ℕ) {Q : FiniteProtocol p a b af bf} (hQ : Q.UniformCallsB m) :
    (idleCallsThenB p n Q).UniformCallsB (m + n) := by
  induction n with
  | zero => simpa only [idleCallsThenB, Nat.add_zero] using hQ
  | succ n ih =>
    simpa only [idleCallsThenB, Nat.add_succ] using idleCallThenB_uniformCalls p ih

theorem FiniteProtocol.exists_uniform_paddingB {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) :
    ∀ m, P.calls ≤ m → ∃ Q : FiniteProtocol p a b af bf,
      Q.calls ≤ m ∧ Q.UniformCallsB m ∧ ∀ ρ, Q.output ρ = P.output ρ := by
  induction P with
  | done a b =>
    intro m _
    refine ⟨idleCallsThenB p m (.done a b), ?_, ?_, ?_⟩
    · simp only [idleCallsThenB_calls, FiniteProtocol.calls, zero_add, le_refl]
    · simpa only [zero_add] using idleCallsThenB_uniformCalls p (m := 0) m
        (Q := FiniteProtocol.done (p := p) a b) rfl
    · intro ρ
      exact idleCallsThenB_output p m (.done a b) ρ
  | alice K next ih =>
    intro m hm
    have hn : ∀ j, (next j).calls ≤ m := by
      intro j
      exact (Finset.le_sup (Finset.mem_univ j)).trans hm
    choose Q hQ using fun j => ih j m (hn j)
    refine ⟨.alice K Q, ?_, ?_, ?_⟩
    · change (Finset.univ.sup fun j => (Q j).calls) ≤ m
      exact Finset.sup_le fun j _ => (hQ j).1
    · change ∀ j, (Q j).UniformCallsB m
      exact fun j => (hQ j).2.1
    · intro ρ
      simp only [FiniteProtocol.output]
      apply Finset.sum_congr rfl
      intro j _
      exact (hQ j).2.2 _
  | bob K next ih =>
    intro m hm
    have hn : ∀ j, (next j).calls ≤ m := by
      intro j
      exact (Finset.le_sup (Finset.mem_univ j)).trans hm
    choose Q hQ using fun j => ih j m (hn j)
    refine ⟨.bob K Q, ?_, ?_, ?_⟩
    · change (Finset.univ.sup fun j => (Q j).calls) ≤ m
      exact Finset.sup_le fun j _ => (hQ j).1
    · change ∀ j, (Q j).UniformCallsB m
      exact fun j => (hQ j).2.1
    · intro ρ
      simp only [FiniteProtocol.output]
      apply Finset.sum_congr rfl
      intro j _
      exact (hQ j).2.2 _
  | call next ih =>
    intro m hm
    change next.calls + 1 ≤ m at hm
    rcases ih (m - 1) (by omega) with ⟨Q, hC, hU, hO⟩
    refine ⟨.call Q, ?_, ?_, ?_⟩
    · change Q.calls + 1 ≤ m
      omega
    · change ∃ k, m = k + 1 ∧ Q.UniformCallsB k
      exact ⟨m - 1, by omega, hU⟩
    · intro ρ
      exact hO _

inductive FiniteBlockProtocolB (p : ℝ) (n : ℕ) : ℕ → ℕ → ℕ → ℕ → Type
  | done (a b : ℕ) : FiniteBlockProtocolB p n a b a b
  | alice {a b ao af bf k : ℕ} (K : KrausInstrument a ao k)
      (next : Fin k → FiniteBlockProtocolB p n ao b af bf) :
      FiniteBlockProtocolB p n a b af bf
  | bob {a b bo af bf k : ℕ} (K : KrausInstrument b bo k)
      (next : Fin k → FiniteBlockProtocolB p n a bo af bf) :
      FiniteBlockProtocolB p n a b af bf
  | blockCall {a b af bf : ℕ}
      (next : FiniteBlockProtocolB p n a (doubleDimB n b) af bf) :
      FiniteBlockProtocolB p n (doubleDimB n a) b af bf

def FiniteBlockProtocolB.calls {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) : ℕ :=
  match P with
  | .done _ _ => 0
  | .alice _ next => Finset.univ.sup fun j => (next j).calls
  | .bob _ next => Finset.univ.sup fun j => (next j).calls
  | .blockCall next => next.calls + 1

def FiniteBlockProtocolB.output {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (ρ : BipartiteMatrix a b) :
    BipartiteMatrix af bf :=
  match P with
  | .done _ _ => ρ
  | .alice K next => ∑ j, (next j).output
      (aliceOperator (b := b) (K.operator j) * ρ *
        (aliceOperator (b := b) (K.operator j))ᴴ)
  | .bob K next => ∑ j, (next j).output
      (bobOperator (a := a) (K.operator j) * ρ *
        (bobOperator (a := a) (K.operator j))ᴴ)
  | .blockCall (a := a₀) (b := b₀) next =>
      next.output (krausSumB (sequentialCallsKrausB p n a₀ b₀) ρ)

def FiniteBlockProtocolB.represented_toMatrix {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) : FiniteProtocol p a b af bf :=
  match P with
  | .done a b => .done a b
  | .alice K next => .alice K fun j => (next j).represented_toMatrix
  | .bob K next => .bob K fun j => (next j).represented_toMatrix
  | .blockCall (a := a₀) (b := b₀) next =>
      sequentialCallsThenB p n a₀ b₀ next.represented_toMatrix

theorem FiniteBlockProtocolB.toMatrix_output {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) :
    ∀ ρ, P.represented_toMatrix.output ρ = P.output ρ := by
  induction P with
  | done a b => intro ρ; rfl
  | alice K next ih =>
    intro ρ
    simp only [FiniteBlockProtocolB.represented_toMatrix, FiniteProtocol.output,
      FiniteBlockProtocolB.output]
    apply Finset.sum_congr rfl
    intro j _
    exact ih j _
  | bob K next ih =>
    intro ρ
    simp only [FiniteBlockProtocolB.represented_toMatrix, FiniteProtocol.output,
      FiniteBlockProtocolB.output]
    apply Finset.sum_congr rfl
    intro j _
    exact ih j _
  | blockCall next ih =>
    intro ρ
    rw [FiniteBlockProtocolB.represented_toMatrix, sequentialCallsThenB_output,
      sequentialCallsProtocolB_output]
    exact ih _

theorem FiniteBlockProtocolB.toMatrix_calls_le {p : ℝ} {n a b af bf : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) :
    P.represented_toMatrix.calls ≤ n * P.calls := by
  induction P with
  | done a b => simp [FiniteBlockProtocolB.represented_toMatrix, FiniteBlockProtocolB.calls,
      FiniteProtocol.calls]
  | alice K next ih =>
    change (Finset.univ.sup fun j => (next j).represented_toMatrix.calls) ≤
      n * (Finset.univ.sup fun j => (next j).calls)
    apply Finset.sup_le
    intro j _
    have hj : (next j).calls ≤ Finset.univ.sup (fun j => (next j).calls) :=
      Finset.le_sup (f := fun j => (next j).calls) (Finset.mem_univ j)
    exact (ih j).trans (Nat.mul_le_mul_left n hj)
  | bob K next ih =>
    change (Finset.univ.sup fun j => (next j).represented_toMatrix.calls) ≤
      n * (Finset.univ.sup fun j => (next j).calls)
    apply Finset.sup_le
    intro j _
    have hj : (next j).calls ≤ Finset.univ.sup (fun j => (next j).calls) :=
      Finset.le_sup (f := fun j => (next j).calls) (Finset.mem_univ j)
    exact (ih j).trans (Nat.mul_le_mul_left n hj)
  | blockCall next ih =>
    rw [FiniteBlockProtocolB.represented_toMatrix, sequentialCallsThenB_calls]
    change next.represented_toMatrix.calls + n ≤ n * (next.calls + 1)
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add_right ih n

theorem FiniteBlockProtocolB.toMatrix_calls_bound {p : ℝ} {n a b af bf m : ℕ}
    (P : FiniteBlockProtocolB p n a b af bf) (hP : P.calls ≤ m) :
    P.represented_toMatrix.calls ≤ n * m :=
  P.toMatrix_calls_le.trans (Nat.mul_le_mul_left n hP)

end QuantumProver.AmplitudeDamping.FiniteModel
