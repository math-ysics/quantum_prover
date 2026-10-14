import QuantumProver.InformationTheory.Equipartition.Definitions
import QuantumProver.InformationTheory.Equipartition.UniversalEntropyBounds
import QuantumProver.InformationTheory.Equipartition.TestingBounds
import QuantumProver.InformationTheory.Equipartition.PolarBounds
import QuantumProver.InformationTheory.Equipartition.FamilyIdentities
import QuantumProver.InformationTheory.Equipartition.PermutationMeasuredDPIC
import QuantumProver.InformationTheory.Equipartition.PinchingUmegaki
import QuantumProver.InformationTheory.Equipartition.EndpointMoment
import QuantumProver.InformationTheory.Equipartition.MeasuredRenyiSuperadditivity
import QuantumProver.InformationTheory.PetzMeasurementDPI
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems
import QuantumProver.InformationTheory.QuantumRelativeEntropyContinuity

noncomputable section

namespace QuantumProver.Equipartition.FiniteModel

open scoped BigOperators ComplexOrder Matrix
open Matrix

def wordSplitEquiv (d m n : ℕ) : Word d (m + n) ≃ Word d m × Word d n where
  toFun x := (fun i => x (Fin.castAdd n i), fun j => x (Fin.natAdd m j))
  invFun x := Fin.append x.1 x.2
  left_inv x := Fin.append_castAdd_natAdd
  right_inv x := by
    apply Prod.ext
    · funext i
      simp
    · funext j
      simp

theorem tensorMatrix_eq_kronecker {d m n : ℕ} (A : QMat d m) (B : QMat d n) :
    tensorMatrix A B =
      (Matrix.kronecker A B).submatrix (wordSplitEquiv d m n) (wordSplitEquiv d m n) :=
  rfl

theorem trace_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : CMat κ) : Matrix.trace (A.submatrix e e) = Matrix.trace A := by
  exact e.sum_comp (fun i => A i i)

theorem trace_tensorMatrix {d m n : ℕ} (A : QMat d m) (B : QMat d n) :
    Matrix.trace (tensorMatrix A B) = Matrix.trace A * Matrix.trace B := by
  rw [tensorMatrix_eq_kronecker, trace_submatrix_equiv]
  exact Matrix.trace_kronecker A B

theorem isState_tensorMatrix {d m n : ℕ} {A : QMat d m} {B : QMat d n}
    (hA : IsState A) (hB : IsState B) : IsState (tensorMatrix A B) := by
  constructor
  · rw [tensorMatrix_eq_kronecker]
    exact (hA.1.kronecker hB.1).submatrix _
  · rw [trace_tensorMatrix, hA.2, hB.2, one_mul]

theorem trace_partialTraceRight {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : CMat (ι × κ)) : Matrix.trace (partialTraceRight A) = Matrix.trace A := by
  simp [Matrix.trace, partialTraceRight, Fintype.sum_prod_type]

theorem partialTraceRight_eq_sum_submatrix {ι κ : Type*} [Fintype κ]
    (A : CMat (ι × κ)) :
    partialTraceRight A = ∑ k, A.submatrix (fun i => (i, k)) (fun i => (i, k)) := by
  ext i j
  simp [partialTraceRight, Matrix.sum_apply]

theorem partialTraceRight_posSemidef {ι κ : Type*} [Fintype κ]
    {A : CMat (ι × κ)} (hA : A.PosSemidef) : (partialTraceRight A).PosSemidef := by
  rw [partialTraceRight_eq_sum_submatrix]
  simpa using (Matrix.posSemidef_sum Finset.univ
    (fun k _ => hA.submatrix (fun i => (i, k))))

theorem isState_partialTraceRight {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {A : CMat (ι × κ)}
    (hA : IsState A) : IsState (partialTraceRight A) := by
  constructor
  · exact partialTraceRight_posSemidef hA.1
  · rw [trace_partialTraceRight, hA.2]

def wordPermuteEquiv {d n : ℕ} (p : Equiv.Perm (Fin n)) : Word d n ≃ Word d n where
  toFun x := fun i => x (p i)
  invFun x := fun i => x (p.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

theorem sitePermute_eq_submatrix {d n : ℕ} (p : Equiv.Perm (Fin n)) (A : QMat d n) :
    sitePermute p A = A.submatrix (wordPermuteEquiv p) (wordPermuteEquiv p) := rfl

theorem isState_sitePermute {d n : ℕ} (p : Equiv.Perm (Fin n)) {A : QMat d n}
    (hA : IsState A) : IsState (sitePermute p A) := by
  rw [sitePermute_eq_submatrix]
  exact ⟨hA.1.submatrix _, (trace_submatrix_equiv _ A).trans hA.2⟩

theorem setUmegaki_le_pair {d n : ℕ} (F : QuantumFamilies d)
    {ρ σ : QMat d n} (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n) :
    setUmegaki F n ≤ umegaki ρ σ :=
  sInf_le ⟨ρ, hρ, σ, hσ, rfl⟩

theorem physical_setUmegaki_ne_top {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {n : ℕ} (hn : 0 < n) : setUmegaki F n ≠ ⊤ := by
  obtain ⟨ρ, hρ⟩ := hF.null_nonempty n hn
  obtain ⟨σ, hσ⟩ := hF.alternative_nonempty n hn
  have hle := setUmegaki_le_pair F hρ hσ
  intro ht
  have hp : umegaki ρ σ = ⊤ := le_antisymm le_top (by simpa only [ht] using hle)
  exact (physical_pair_umegaki_finite hF hn hρ hσ).1 hp

theorem setUmegaki_ge_of_pair_lower {d n : ℕ} (F : QuantumFamilies d) (L : ℝ)
    (hL : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n, (L : EReal) ≤ umegaki ρ σ) :
    (L : EReal) ≤ setUmegaki F n := by
  apply le_sInf
  rintro a ⟨ρ, hρ, σ, hσ, rfl⟩
  exact hL ρ hρ σ hσ

theorem setUmegaki_ne_bot_of_pair_lower {d n : ℕ} (F : QuantumFamilies d) (L : ℝ)
    (hL : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n, (L : EReal) ≤ umegaki ρ σ) :
    setUmegaki F n ≠ ⊥ := by
  have hle := setUmegaki_ge_of_pair_lower F L hL
  intro hb
  have hp : (L : EReal) = ⊥ := le_antisymm (by simpa only [hb] using hle) bot_le
  exact EReal.coe_ne_bot L hp

theorem regularizedRate_le_block {d : ℕ} (F : QuantumFamilies d)
    (hb : BddBelow (entropyRates F)) {n : ℕ} (hn : 0 < n) :
    regularizedRate F ≤ (setUmegaki F n).toReal / (n : ℝ) :=
  csInf_le hb (entropyRate_mem F hn)

theorem regularizedRate_mul_le_block {d : ℕ} (F : QuantumFamilies d)
    (hb : BddBelow (entropyRates F)) {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * regularizedRate F ≤ (setUmegaki F n).toReal := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  simpa [mul_comm] using (le_div_iff₀ hnR).mp (regularizedRate_le_block F hb hn)

def LogarithmicTestingConclusion {d : ℕ} (F : QuantumFamilies d) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
    setTestingDivergence F n ε ≠ ⊤ ∧ setTestingDivergence F n ε ≠ ⊥ ∧
      |(setTestingDivergence F n ε).toReal - (n : ℝ) * regularizedRate F| ≤
        K * testingRemainder n

def OptimizerMomentConclusion {d : ℕ} (F : QuantumFamilies d) : Prop :=
  ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ n : ℕ, 0 < n →
    ∀ ρ σ : QMat d n, IsExactMinimizer F ρ σ →
      ∀ t : ℝ, 0 ≤ t → t ≤ c / (n : ℝ) →
        nsWeightedMoment ρ σ ((n : ℝ) * regularizedRate F) t ≤
          K * (n : ℝ) * (blockLog n) ^ 3

def UniversalLogarithmicConclusion {d : ℕ} (F : QuantumFamilies d) : Prop :=
  LogarithmicTestingConclusion F ∧ OptimizerMomentConclusion F

theorem logTwo_two : logTwo 2 = 1 := by
  unfold logTwo
  exact div_self (ne_of_gt (Real.log_pos (by norm_num)))

theorem blockLog_pos {n : ℕ} (hn : 0 < n) : 0 < blockLog n := by
  unfold blockLog logTwo
  apply div_pos
  · apply Real.log_pos
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  · exact Real.log_pos (by norm_num)

theorem testingRemainder_nonneg (n : ℕ) : 0 ≤ testingRemainder n := by
  unfold testingRemainder
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by
    unfold blockLog logTwo
    apply div_nonneg
    · apply Real.log_nonneg
      have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · exact le_of_lt (Real.log_pos (by norm_num))) _)

theorem testingRemainder_pos {n : ℕ} (hn : 0 < n) : 0 < testingRemainder n := by
  unfold testingRemainder
  exact mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hn))
    (Real.rpow_pos_of_pos (blockLog_pos hn) _)

theorem signed_bounds_iff_abs (x r a : ℝ) :
    (r - a ≤ x ∧ x ≤ r + a) ↔ |x - r| ≤ a := by
  rw [abs_le]
  constructor
  · intro h
    constructor <;> linarith [h.1, h.2]
  · intro h
    constructor <;> linarith [h.1, h.2]

section MatrixGrowth
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem loewnerLE_trans {A B C : CMat ι}
    (hAB : LoewnerLE A B) (hBC : LoewnerLE B C) : LoewnerLE A C := by
  have hsum := hBC.add hAB
  change (C - A).PosSemidef
  have hmat : C - A = (C - B) + (B - A) := by abel
  rw [hmat]
  exact hsum

theorem loewnerLE_real_smul_mono {σ : CMat ι} (hσ : σ.PosSemidef)
    {a b : ℝ} (hab : a ≤ b) : LoewnerLE ((a : ℂ) • σ) ((b : ℂ) • σ) := by
  have hs : 0 ≤ ((b - a : ℝ) : ℂ) := by exact_mod_cast (sub_nonneg.mpr hab)
  have hp : (((b - a : ℝ) : ℂ) • σ).PosSemidef := hσ.smul hs
  simpa only [LoewnerLE, Complex.ofReal_sub, sub_smul] using hp

def maxDivergence (ρ σ : CMat ι) : EReal :=
  sInf {v | ∃ a : ℝ, v = (a : EReal) ∧
    LoewnerLE ρ ((Real.rpow 2 a : ℂ) • σ)}

theorem maxDivergence_le_iff {ρ σ : CMat ι} (hσ : σ.PosSemidef) (c : ℝ) :
    maxDivergence ρ σ ≤ (c : EReal) ↔
      LoewnerLE ρ ((Real.rpow 2 c : ℂ) • σ) := by
  constructor
  · intro hmax
    have hcont : Continuous (fun a : ℝ => (Real.rpow 2 a : ℂ) • σ - ρ) :=
      ((Complex.continuous_ofReal.comp
        (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0))).smul
          continuous_const).sub continuous_const
    have hclosed : IsClosed {a : ℝ | LoewnerLE ρ ((Real.rpow 2 a : ℂ) • σ)} :=
      Matrix.posSemidef_is_closed.preimage hcont
    have hIoi : Set.Ioi c ⊆ {a : ℝ | LoewnerLE ρ ((Real.rpow 2 a : ℂ) • σ)} := by
      intro a ha
      have hlt : maxDivergence ρ σ < (a : EReal) :=
        lt_of_le_of_lt hmax (EReal.coe_lt_coe_iff.mpr ha)
      unfold maxDivergence at hlt
      rcases sInf_lt_iff.mp hlt with ⟨v, ⟨b, rfl, hb⟩, hba⟩
      exact loewnerLE_trans hb (loewnerLE_real_smul_mono hσ
        (Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (le_of_lt (EReal.coe_lt_coe_iff.mp hba))))
    have hc : c ∈ closure (Set.Ioi c) := by
      simpa only [closure_Ioi, Set.mem_Ici] using (le_refl c)
    exact (closure_minimal hIoi hclosed) hc
  · intro hc
    exact sInf_le ⟨c, rfl, hc⟩

theorem IsState.nonempty_index {ρ : CMat ι} (hρ : IsState ρ) : Nonempty ι := by
  by_contra h
  letI : IsEmpty ι := ⟨fun i => h ⟨i⟩⟩
  have ht := hρ.2
  simp [Matrix.trace] at ht
end MatrixGrowth

theorem physical_localDimension_pos {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : 0 < d := by
  obtain ⟨ρ, hρ⟩ := hF.null_nonempty 1 (by decide)
  obtain ⟨w⟩ := (hF.null_states 1 (by decide) ρ hρ).nonempty_index
  exact (Nat.zero_le (w (0 : Fin 1)).val).trans_lt (w (0 : Fin 1)).isLt

theorem physical_literal_linear_growth {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ C : ℝ, ∀ n, 0 < n →
      ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
        maxDivergence ρ σ ≤ (C * (n : ℝ) : EReal) ∧
          logTwo (Matrix.trace σ).re ≤ C * (n : ℝ) := by
  obtain ⟨C, hC⟩ := hF.linear_growth
  refine ⟨C, ?_⟩
  intro n hn ρ hρ σ hσ
  exact ⟨(maxDivergence_le_iff (hF.alternative_positive n hn σ hσ) _).mpr
    (hC n hn ρ hρ σ hσ).1, (hC n hn ρ hρ σ hσ).2⟩

section BasisBridge
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def basisChangeHom (e : ι ≃ κ) : CMat κ →⋆ₐ[ℝ] CMat ι :=
  { (Matrix.reindexAlgEquiv ℝ ℂ e.symm).toAlgHom with
    map_star' A := by
      change Aᴴ.submatrix e e = (A.submatrix e e)ᴴ
      rw [Matrix.conjTranspose_submatrix] }

theorem basisChangeHom_apply (e : ι ≃ κ) (A : CMat κ) :
    basisChangeHom e A = A.submatrix e e := rfl

theorem cfc_submatrix_equiv (e : ι ≃ κ) (f : ℝ → ℝ) {A : CMat κ}
    (hA : A.IsHermitian) :
    cfc f (A.submatrix e e) = (cfc f A).submatrix e e := by
  have hcont : Continuous (basisChangeHom e) := by
    change Continuous (fun A : CMat κ => A.submatrix e e)
    fun_prop
  exact ((basisChangeHom e).map_cfc f A
    (A.finite_real_spectrum.continuousOn _) hcont hA (hA.submatrix e)).symm

theorem supportLE_submatrix_equiv (e : ι ≃ κ) {ρ σ : CMat κ}
    (hs : SupportLE ρ σ) : SupportLE (ρ.submatrix e e) (σ.submatrix e e) := by
  intro v hv
  have hσv : σ *ᵥ (v ∘ e.symm) = 0 := by
    rw [Matrix.submatrix_mulVec_equiv] at hv
    funext j
    have hj := congrFun hv (e.symm j)
    simpa using hj
  rw [Matrix.submatrix_mulVec_equiv, hs _ hσv]
  rfl

theorem supportLE_submatrix_equiv_iff (e : ι ≃ κ) {ρ σ : CMat κ} :
    SupportLE (ρ.submatrix e e) (σ.submatrix e e) ↔ SupportLE ρ σ := by
  constructor
  · intro hs
    simpa using supportLE_submatrix_equiv e.symm hs
  · exact supportLE_submatrix_equiv e

theorem umegakiReal_submatrix_equiv (e : ι ≃ κ) {ρ σ : CMat κ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    umegakiReal (ρ.submatrix e e) (σ.submatrix e e) = umegakiReal ρ σ := by
  unfold umegakiReal tracePair matrixLog
  rw [cfc_submatrix_equiv e Real.log hρ, cfc_submatrix_equiv e Real.log hσ]
  have hsub : (cfc Real.log ρ).submatrix e e - (cfc Real.log σ).submatrix e e =
      (cfc Real.log ρ - cfc Real.log σ).submatrix e e := rfl
  rw [hsub, Matrix.submatrix_mul_equiv, trace_submatrix_equiv]

theorem umegaki_submatrix_equiv (e : ι ≃ κ) {ρ σ : CMat κ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    umegaki (ρ.submatrix e e) (σ.submatrix e e) = umegaki ρ σ := by
  unfold umegaki
  rw [supportLE_submatrix_equiv_iff e]
  split_ifs
  · rw [umegakiReal_submatrix_equiv e hρ hσ]
  · rfl
end BasisBridge

theorem umegaki_eq_shared_relativeEntropyBits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ σ : CMat ι) : umegaki ρ σ =
      QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits ρ σ := rfl

theorem umegaki_tensorMatrix {d m n : ℕ} {ρ σ : QMat d m} {τ υ : QMat d n}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hτ : IsState τ) (hυ : υ.PosSemidef) :
    umegaki (tensorMatrix ρ τ) (tensorMatrix σ υ) = umegaki ρ σ + umegaki τ υ := by
  rw [tensorMatrix_eq_kronecker, tensorMatrix_eq_kronecker]
  simp only [Matrix.kronecker]
  rw [umegaki_submatrix_equiv (wordSplitEquiv d m n) (hρ.1.kronecker hτ.1).1
    (hσ.kronecker hυ).1]
  exact QuantumProver.SuperchannelDiscrimination.TensorEntropy.relativeEntropyBits_kronecker
    hρ hσ hτ hυ

theorem physical_pair_supportLE {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {n : ℕ} (hn : 0 < n)
    {ρ σ : QMat d n} (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n) :
    SupportLE ρ σ := by
  obtain ⟨C, hC⟩ := hF.linear_growth
  exact supportLE_of_psd_domination (hF.null_states n hn ρ hρ).1
    (hC n hn ρ hρ σ hσ).1

def pairEntropyValues {d : ℕ} (F : QuantumFamilies d) (n : ℕ) : Set ℝ :=
  {x | ∃ ρ ∈ F.null n, ∃ σ ∈ F.alternative n, x = umegakiReal ρ σ}

theorem pairEntropyValues_nonempty {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {n : ℕ} (hn : 0 < n) :
    (pairEntropyValues F n).Nonempty := by
  obtain ⟨ρ, hρ⟩ := hF.null_nonempty n hn
  obtain ⟨σ, hσ⟩ := hF.alternative_nonempty n hn
  exact ⟨umegakiReal ρ σ, ρ, hρ, σ, hσ, rfl⟩

theorem setUmegaki_toReal_eq_inf_pairEntropy {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {n : ℕ} (hn : 0 < n) (L : ℝ)
    (hL : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n, L ≤ umegakiReal ρ σ) :
    (setUmegaki F n).toReal = sInf (pairEntropyValues F n) := by
  have hEL : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      (L : EReal) ≤ umegaki ρ σ := by
    intro ρ hρ σ hσ
    rw [umegaki_of_support (physical_pair_supportLE hF hn hρ hσ)]
    exact_mod_cast hL ρ hρ σ hσ
  have hbot := setUmegaki_ne_bot_of_pair_lower F L hEL
  have htop := physical_setUmegaki_ne_top hF hn
  have hnonempty := pairEntropyValues_nonempty hF hn
  have hbounded : BddBelow (pairEntropyValues F n) := by
    refine ⟨L, ?_⟩
    rintro x ⟨ρ, hρ, σ, hσ, rfl⟩
    exact hL ρ hρ σ hσ
  apply le_antisymm
  · apply le_csInf hnonempty
    rintro x ⟨ρ, hρ, σ, hσ, rfl⟩
    have h := EReal.toReal_le_toReal (setUmegaki_le_pair F hρ hσ) hbot
      (physical_pair_umegaki_finite hF hn hρ hσ).1
    simpa only [umegaki_of_support (physical_pair_supportLE hF hn hρ hσ),
      EReal.toReal_coe] using h
  · have hle : ((sInf (pairEntropyValues F n) : ℝ) : EReal) ≤ setUmegaki F n := by
      apply le_sInf
      rintro x ⟨ρ, hρ, σ, hσ, rfl⟩
      rw [umegaki_of_support (physical_pair_supportLE hF hn hρ hσ)]
      exact_mod_cast (csInf_le hbounded ⟨ρ, hρ, σ, hσ, rfl⟩)
    simpa only [EReal.toReal_coe] using
      EReal.toReal_le_toReal hle (EReal.coe_ne_bot _) htop

theorem setUmegaki_toReal_le_pair_of_lower {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {n : ℕ} (hn : 0 < n) (L : ℝ)
    (hL : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n, L ≤ umegakiReal ρ σ)
    {ρ σ : QMat d n} (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n) :
    (setUmegaki F n).toReal ≤ umegakiReal ρ σ := by
  rw [setUmegaki_toReal_eq_inf_pairEntropy hF hn L hL]
  apply csInf_le
  · refine ⟨L, ?_⟩
    rintro x ⟨τ, hτ, υ, hυ, rfl⟩
    exact hL τ hτ υ hυ
  · exact ⟨ρ, hρ, σ, hσ, rfl⟩

def LiteralLinearGrowth {d : ℕ} (F : QuantumFamilies d) : Prop :=
  ∃ C : ℝ, ∀ n, 0 < n → ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
    maxDivergence ρ σ ≤ (C * (n : ℝ) : EReal) ∧
      logTwo (Matrix.trace σ).re ≤ C * (n : ℝ)

def OrderLinearGrowth {d : ℕ} (F : QuantumFamilies d) : Prop :=
  ∃ C : ℝ, ∀ n, 0 < n → ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
    LoewnerLE ρ ((Real.rpow 2 (C * (n : ℝ)) : ℂ) • σ) ∧
      logTwo (Matrix.trace σ).re ≤ C * (n : ℝ)

theorem literalLinearGrowth_iff_order {d : ℕ} (F : QuantumFamilies d)
    (hpositive : ∀ n, 0 < n → ∀ σ ∈ F.alternative n, σ.PosSemidef) :
    LiteralLinearGrowth F ↔ OrderLinearGrowth F := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n hn ρ hρ σ hσ
    exact ⟨(maxDivergence_le_iff (hpositive n hn σ hσ) _).mp
      (hC n hn ρ hρ σ hσ).1, (hC n hn ρ hρ σ hσ).2⟩
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n hn ρ hρ σ hσ
    exact ⟨(maxDivergence_le_iff (hpositive n hn σ hσ) _).mpr
      (hC n hn ρ hρ σ hσ).1, (hC n hn ρ hρ σ hσ).2⟩

theorem physical_linear_growth_nonneg {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
        LoewnerLE ρ ((Real.rpow 2 (C * (n : ℝ)) : ℂ) • σ) ∧
          logTwo (Matrix.trace σ).re ≤ C * (n : ℝ) := by
  obtain ⟨C, hC⟩ := hF.linear_growth
  refine ⟨|C|, abs_nonneg C, ?_⟩
  intro n hn ρ hρ σ hσ
  have hCn : C * (n : ℝ) ≤ |C| * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (Nat.cast_nonneg n)
  refine ⟨loewnerLE_trans (hC n hn ρ hρ σ hσ).1 ?_,
    (hC n hn ρ hρ σ hσ).2.trans hCn⟩
  exact loewnerLE_real_smul_mono (hF.alternative_positive n hn σ hσ)
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hCn)

theorem physical_setUmegaki_subadditive_of_pair_lower {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (C : ℝ)
    (hlower : ∀ n, 0 < n → ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      -C * (n : ℝ) ≤ umegakiReal ρ σ)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (setUmegaki F (m + n)).toReal ≤
      (setUmegaki F m).toReal + (setUmegaki F n).toReal := by
  have hmn : 0 < m + n := by omega
  let D := (setUmegaki F (m + n)).toReal
  have hall : ∀ a ∈ pairEntropyValues F m, ∀ b ∈ pairEntropyValues F n, D ≤ a + b := by
    rintro a ⟨ρ, hρ, σ, hσ, rfl⟩ b ⟨τ, hτ, υ, hυ, rfl⟩
    have hρτ := hF.null_tensor m n hm hn ρ hρ τ hτ
    have hσυ := hF.alternative_tensor m n hm hn σ hσ υ hυ
    have hE := umegaki_tensorMatrix (hF.null_states m hm ρ hρ)
      (hF.alternative_positive m hm σ hσ) (hF.null_states n hn τ hτ)
      (hF.alternative_positive n hn υ hυ)
    rw [umegaki_of_support (physical_pair_supportLE hF hmn hρτ hσυ),
      umegaki_of_support (physical_pair_supportLE hF hm hρ hσ),
      umegaki_of_support (physical_pair_supportLE hF hn hτ hυ),
      ← EReal.coe_add] at hE
    have hR := EReal.coe_injective hE
    have hle := setUmegaki_toReal_le_pair_of_lower hF hmn (-C * ((m + n : ℕ) : ℝ))
      (hlower (m + n) hmn) hρτ hσυ
    dsimp [D]
    rwa [hR] at hle
  have hSm := pairEntropyValues_nonempty hF hm
  have hSn := pairEntropyValues_nonempty hF hn
  have hinner : ∀ a ∈ pairEntropyValues F m,
      D - a ≤ sInf (pairEntropyValues F n) := by
    intro a ha
    apply le_csInf hSn
    intro b hb
    linarith [hall a ha b hb]
  have houter : D - sInf (pairEntropyValues F n) ≤ sInf (pairEntropyValues F m) := by
    apply le_csInf hSm
    intro a ha
    linarith [hinner a ha]
  have hDm := setUmegaki_toReal_eq_inf_pairEntropy hF hm (-C * (m : ℝ)) (hlower m hm)
  have hDn := setUmegaki_toReal_eq_inf_pairEntropy hF hn (-C * (n : ℝ)) (hlower n hn)
  dsimp [D] at houter
  linarith

theorem entropyRates_bddBelow_of_real_pair_lower {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (C : ℝ)
    (hlower : ∀ n, 0 < n → ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      -C * (n : ℝ) ≤ umegakiReal ρ σ) : BddBelow (entropyRates F) := by
  refine ⟨-C, ?_⟩
  rintro x ⟨n, hn, rfl⟩
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  apply (le_div_iff₀ hnR).mpr
  have hEL : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      (-C * (n : ℝ) : EReal) ≤ umegaki ρ σ := by
    intro ρ hρ σ hσ
    rw [umegaki_of_support (physical_pair_supportLE hF hn hρ hσ)]
    exact EReal.coe_le_coe (hlower n hn ρ hρ σ hσ)
  have hle := setUmegaki_ge_of_pair_lower F (-C * (n : ℝ)) hEL
  simpa only [EReal.toReal_coe] using
    EReal.toReal_le_toReal hle (EReal.coe_ne_bot _) (physical_setUmegaki_ne_top hF hn)

section TraceResetEntropy
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open QuantumProver.SuperchannelDiscrimination.KrausCompletion

theorem complex_real_smul (a : ℝ) (A : CMat ι) :
    (a : ℂ) • A = a • A := by
  ext i j
  change (a : ℂ) * A i j = a • A i j
  simp only [Algebra.smul_def]
  rfl

theorem matrixLog_real_smul_one (t : ℝ) :
    matrixLog ((t : ℂ) • (1 : CMat ι)) = (Real.log t : ℂ) • (1 : CMat ι) := by
  have hin : (t : ℂ) • (1 : CMat ι) = algebraMap ℝ (CMat ι) t := by
    rw [complex_real_smul, Algebra.algebraMap_eq_smul_one]
  rw [matrixLog, hin, cfc_algebraMap, Algebra.algebraMap_eq_smul_one]
  exact (complex_real_smul _ _).symm

theorem matrixLog_one : matrixLog (1 : CMat ι) = 0 := by
  simp [matrixLog]

def traceResetKraus (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ι → Matrix Unit ι ℂ := resetKraus Unit.unit (1 : CMat ι)

theorem traceResetKraus_gram : krausGram (traceResetKraus ι) = 1 := by
  dsimp only [traceResetKraus]
  rw [resetKraus_gram]
  simp

theorem traceResetKraus_action (A : CMat ι) :
    krausAction (traceResetKraus ι) A = A.trace • (1 : CMat Unit) := by
  dsimp only [traceResetKraus]
  rw [resetKraus_action]
  simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  cases i
  cases j
  simp

theorem trace_re_pos_of_state_domination {ρ σ : CMat ι} (hρ : IsState ρ)
    {a : ℝ} (ha : 0 < a) (hdom : LoewnerLE ρ ((a : ℂ) • σ)) :
    0 < σ.trace.re := by
  have ht : 0 ≤ (((a : ℂ) • σ - ρ).trace) := hdom.trace_nonneg
  have hre : 0 ≤ a * σ.trace.re - 1 := by
    have h := (Complex.nonneg_iff.mp ht).1
    simpa only [Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
      Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hρ.2, Complex.one_re] using h
  have hprod : 0 < a * σ.trace.re := by linarith
  exact (mul_pos_iff_of_pos_left ha).mp hprod

theorem umegaki_scalar_trace (t : ℝ) (ht : 0 < t) :
    umegaki (1 : CMat Unit) ((t : ℂ) • (1 : CMat Unit)) = (-logTwo t : EReal) := by
  have htc : 0 < (t : ℂ) := by exact_mod_cast ht
  have hB : ((t : ℂ) • (1 : CMat Unit)).PosDef := Matrix.PosDef.one.smul htc
  rw [umegaki_eq_shared_relativeEntropyBits,
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.relativeEntropyBits_of_posDef _ hB]
  change ((umegakiReal (1 : CMat Unit) ((t : ℂ) • (1 : CMat Unit)) : ℝ) : EReal) = _
  congr 1
  unfold umegakiReal tracePair
  rw [matrixLog_one, matrixLog_real_smul_one]
  simp [logTwo, Matrix.trace_smul, Matrix.trace_one, neg_div]

theorem umegaki_ge_neg_log_trace {ρ σ : CMat ι} (hρ : IsState ρ)
    (hσ : σ.PosSemidef) (hT : 0 < σ.trace.re) :
    (-logTwo σ.trace.re : EReal) ≤ umegaki ρ σ := by
  have htr : σ.trace = (σ.trace.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (Complex.nonneg_iff.mp hσ.trace_nonneg).2.symm
  have h := QuantumProver.SuperchannelDiscrimination.InputSupport.relativeEntropyBits_kraus_dpi
    (traceResetKraus ι) traceResetKraus_gram hρ.1 hσ
  change umegaki (krausAction (traceResetKraus ι) ρ)
      (krausAction (traceResetKraus ι) σ) ≤ umegaki ρ σ at h
  rw [traceResetKraus_action, traceResetKraus_action, hρ.2, one_smul, htr,
    umegaki_scalar_trace _ hT] at h
  exact h

theorem umegakiReal_ge_neg_log_trace_via_trace {ρ σ : CMat ι} (hρ : IsState ρ)
    (hσ : σ.PosSemidef) (hT : 0 < σ.trace.re) (hs : SupportLE ρ σ) :
    -logTwo σ.trace.re ≤ umegakiReal ρ σ := by
  have h := umegaki_ge_neg_log_trace hρ hσ hT
  rw [umegaki_of_support hs] at h
  exact EReal.coe_le_coe_iff.mp h

end TraceResetEntropy

theorem physical_uniform_pair_entropy_lower {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
        -C * (n : ℝ) ≤ umegakiReal ρ σ := by
  obtain ⟨C, hC, hgrowth⟩ := physical_linear_growth_nonneg hF
  refine ⟨C, hC, ?_⟩
  intro n hn ρ hρ σ hσ
  have hρstate := hF.null_states n hn ρ hρ
  have hσpsd := hF.alternative_positive n hn σ hσ
  have hdom := (hgrowth n hn ρ hρ σ hσ).1
  have hT := trace_re_pos_of_state_domination hρstate
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hdom
  have hlower := umegakiReal_ge_neg_log_trace_via_trace hρstate hσpsd hT
    (physical_pair_supportLE hF hn hρ hσ)
  linarith [(hgrowth n hn ρ hρ σ hσ).2]

theorem physical_setUmegaki_finite {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {n : ℕ} (hn : 0 < n) :
    setUmegaki F n ≠ ⊤ ∧ setUmegaki F n ≠ ⊥ := by
  obtain ⟨C, _, hlower⟩ := physical_uniform_pair_entropy_lower hF
  refine ⟨physical_setUmegaki_ne_top hF hn,
    setUmegaki_ne_bot_of_pair_lower F (-C * (n : ℝ)) ?_⟩
  intro ρ hρ σ hσ
  rw [umegaki_of_support (physical_pair_supportLE hF hn hρ hσ)]
  exact EReal.coe_le_coe (hlower n hn ρ hρ σ hσ)

theorem physical_setUmegaki_subadditive {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (setUmegaki F (m + n)).toReal ≤
      (setUmegaki F m).toReal + (setUmegaki F n).toReal := by
  obtain ⟨C, _, hlower⟩ := physical_uniform_pair_entropy_lower hF
  exact physical_setUmegaki_subadditive_of_pair_lower hF C hlower hm hn

theorem physical_entropyRates_bddBelow {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : BddBelow (entropyRates F) := by
  obtain ⟨C, _, hlower⟩ := physical_uniform_pair_entropy_lower hF
  exact entropyRates_bddBelow_of_real_pair_lower hF C hlower

theorem physical_uniform_setUmegaki_lower {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      -C * (n : ℝ) ≤ (setUmegaki F n).toReal := by
  obtain ⟨C, hC, hlower⟩ := physical_uniform_pair_entropy_lower hF
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hEL : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      (-C * (n : ℝ) : EReal) ≤ umegaki ρ σ := by
    intro ρ hρ σ hσ
    rw [umegaki_of_support (physical_pair_supportLE hF hn hρ hσ)]
    exact EReal.coe_le_coe (hlower n hn ρ hρ σ hσ)
  simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal
    (setUmegaki_ge_of_pair_lower F (-C * (n : ℝ)) hEL)
    (EReal.coe_ne_bot _) (physical_setUmegaki_ne_top hF hn)

def FullRateConclusion {d : ℕ} (F : QuantumFamilies d) : Prop :=
  (∀ n : ℕ, 0 < n → setUmegaki F n ≠ ⊤ ∧ setUmegaki F n ≠ ⊥) ∧
    Filter.Tendsto (fun n : ℕ => (setUmegaki F n).toReal / (n : ℝ))
      Filter.atTop (nhds (regularizedRate F))

theorem physical_actual_full_rate {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : FullRateConclusion F := by
  constructor
  · intro n hn
    exact physical_setUmegaki_finite hF hn
  · obtain ⟨C, hC, hlower⟩ := physical_uniform_setUmegaki_lower hF
    have hsub : ∀ m n : ℕ, 0 < m → 0 < n →
        (setUmegaki F (m + n)).toReal ≤
          (setUmegaki F m).toReal + (setUmegaki F n).toReal := by
      intro m n hm hn
      exact physical_setUmegaki_subadditive hF hm hn
    exact ScalarRate.subadditive_full_limit (fun n => (setUmegaki F n).toReal)
      hsub hC hlower

theorem physical_pair_umegakiReal_tensor {d m n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hm : 0 < m) (hn : 0 < n)
    {ρ σ : QMat d m} {τ υ : QMat d n}
    (hρ : ρ ∈ F.null m) (hσ : σ ∈ F.alternative m)
    (hτ : τ ∈ F.null n) (hυ : υ ∈ F.alternative n) :
    umegakiReal (tensorMatrix ρ τ) (tensorMatrix σ υ) =
      umegakiReal ρ σ + umegakiReal τ υ := by
  have hρτ := hF.null_tensor m n hm hn ρ hρ τ hτ
  have hσυ := hF.alternative_tensor m n hm hn σ hσ υ hυ
  have hE := umegaki_tensorMatrix (hF.null_states m hm ρ hρ)
    (hF.alternative_positive m hm σ hσ) (hF.null_states n hn τ hτ)
    (hF.alternative_positive n hn υ hυ)
  rw [umegaki_of_support (physical_pair_supportLE hF (by omega) hρτ hσυ),
    umegaki_of_support (physical_pair_supportLE hF hm hρ hσ),
    umegaki_of_support (physical_pair_supportLE hF hn hτ hυ),
    ← EReal.coe_add] at hE
  exact EReal.coe_injective hE

theorem physical_pair_umegaki_repetition {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {ρ σ : QMat d n}
    (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n) (k : ℕ) (hk : 0 < k) :
    ∃ ρk σk : QMat d (k * n), ρk ∈ F.null (k * n) ∧
      σk ∈ F.alternative (k * n) ∧
        umegakiReal ρk σk = (k : ℝ) * umegakiReal ρ σ := by
  revert hk
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst k
      let P : ℕ → Prop := fun N => ∃ ρk σk : QMat d N,
        ρk ∈ F.null N ∧ σk ∈ F.alternative N ∧
          umegakiReal ρk σk = (1 : ℝ) * umegakiReal ρ σ
      have hb : P n := ⟨ρ, σ, hρ, hσ, by ring⟩
      have ht : P (1 * n) := Eq.mpr (congrArg P (Nat.one_mul n)) hb
      simpa only [P, Nat.zero_add, Nat.cast_one] using ht
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      obtain ⟨ρk, σk, hρk, hσk, hUk⟩ := ih hkpos
      have hkn : 0 < k * n := Nat.mul_pos hkpos hn
      rw [Nat.succ_mul]
      refine ⟨tensorMatrix ρk ρ, tensorMatrix σk σ,
        hF.null_tensor (k * n) n hkn hn ρk hρk ρ hρ,
        hF.alternative_tensor (k * n) n hkn hn σk hσk σ hσ, ?_⟩
      rw [physical_pair_umegakiReal_tensor hF hkn hn hρk hσk hρ hσ, hUk,
        Nat.cast_add, Nat.cast_one]
      ring

theorem physical_pair_mean_surplus_nonneg {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {ρ σ : QMat d n}
    (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n) :
    0 ≤ umegakiReal ρ σ - (n : ℝ) * regularizedRate F := by
  obtain ⟨C, _, hlower⟩ := physical_uniform_pair_entropy_lower hF
  have hr := regularizedRate_mul_le_block F (physical_entropyRates_bddBelow hF) hn
  have hp := setUmegaki_toReal_le_pair_of_lower hF hn (-C * (n : ℝ))
    (hlower n hn) hρ hσ
  exact sub_nonneg.mpr (hr.trans hp)

theorem physical_ns_mean_surplus_nonneg {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {ρ σ : QMat d n}
    (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n) :
    0 ≤ (nsLaw ρ σ (hF.null_states n hn ρ hρ)
      (hF.alternative_positive n hn σ hσ)).mean
        (fun z => nsLikelihood ρ σ z - (n : ℝ) * regularizedRate F) := by
  let P := nsLaw ρ σ (hF.null_states n hn ρ hρ) (hF.alternative_positive n hn σ hσ)
  change 0 ≤ P.expect (fun z => nsLikelihood ρ σ z - (n : ℝ) * regularizedRate F)
  rw [P.expect_sub, P.expect_const]
  have hmean : P.expect (nsLikelihood ρ σ) = umegakiReal ρ σ :=
    nsLaw_mean_eq_umegakiReal ρ σ (hF.null_states n hn ρ hρ)
      (hF.alternative_positive n hn σ hσ)
  rw [hmean]
  exact physical_pair_mean_surplus_nonneg hF hn hρ hσ

theorem physical_actual_rate_subsequence {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (f : ℕ → ℕ)
    (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun k => (setUmegaki F (f k)).toReal / (f k : ℝ))
      Filter.atTop (nhds (regularizedRate F)) :=
  (physical_actual_full_rate hF).2.comp hf

section MatrixNSConverse
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem converse_effect_square_le {Q : CMat ι} (hQ : IsEffect Q) :
    LoewnerLE (Q * Q) Q := by
  have hc : Commute Q (1 - Q) := by
    change Q * (1 - Q) = (1 - Q) * Q
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  have hp : (Q * (1 - Q)).PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (Commute.mul_nonneg hQ.1.nonneg hQ.2.nonneg hc)
  simpa only [LoewnerLE, Matrix.mul_sub, Matrix.mul_one] using hp

theorem converse_complement_isEffect {Q : CMat ι} (hQ : IsEffect Q) :
    IsEffect (1 - Q) := by
  refine ⟨hQ.2, ?_⟩
  have he : (1 : CMat ι) - (1 - Q) = Q := by abel
  rw [he]
  exact hQ.1

theorem converse_effect_square_pairing_le {A Q : CMat ι}
    (hA : A.PosSemidef) (hQ : IsEffect Q) : tracePair A (Q * Q) ≤ tracePair A Q := by
  have hp : (Q - Q * Q).PosSemidef := converse_effect_square_le hQ
  have h := QuantumProver.SuperchannelDiscrimination.KrausCompletion.trace_mul_nonneg_of_posSemidef hp hA
  rw [Matrix.sub_mul, Matrix.trace_sub] at h
  have hr := (Complex.nonneg_iff.mp h).1
  rw [Complex.sub_re, Matrix.trace_mul_comm Q A,
    Matrix.trace_mul_comm (Q * Q) A] at hr
  exact sub_nonneg.mp hr

theorem converse_trace_diagonal_mul_adjoint (p : ι → ℝ) (W : CMat ι) :
    (Matrix.diagonal (fun i => (p i : ℂ)) * (W * Wᴴ)).trace.re =
      ∑ i, ∑ j, p i * Complex.normSq (W i j) := by
  simp only [Matrix.trace, Matrix.diag]
  simp only [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum,
    Complex.re_sum, Complex.star_def, Complex.mul_conj,
    Complex.re_ofReal_mul, Complex.ofReal_re]

theorem converse_weighted_rows_normSq {ρ : CMat ι} (hρ : ρ.IsHermitian)
    (V : Matrix.unitaryGroup ι ℂ) (X : CMat ι) :
    (∑ i, ∑ j, hρ.eigenvalues i *
      Complex.normSq (((hρ.eigenvectorUnitary : CMat ι)ᴴ * X * (V : CMat ι)) i j)) =
        tracePair ρ (X * Xᴴ) := by
  let U : CMat ι := hρ.eigenvectorUnitary
  let D : CMat ι := Matrix.diagonal (fun i => (hρ.eigenvalues i : ℂ))
  let W : CMat ι := Uᴴ * X * (V : CMat ι)
  have hunitV : (V : CMat ι) * (V : CMat ι)ᴴ = 1 := Unitary.coe_mul_star_self V
  have hW : W * Wᴴ = Uᴴ * (X * Xᴴ) * U := by
    dsimp only [W]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc
      _ = Uᴴ * X * ((V : CMat ι) * (V : CMat ι)ᴴ) * Xᴴ * U := by noncomm_ring
      _ = _ := by rw [hunitV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hspec : ρ = U * D * Uᴴ := by
    simpa only [U, D, Unitary.conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, RCLike.ofReal_eq_complex_ofReal,
      Function.comp_def] using hρ.spectral_theorem
  have hcycle : ((U * D * Uᴴ) * (X * Xᴴ)).trace =
      (D * (Uᴴ * (X * Xᴴ) * U)).trace := by
    simpa only [Matrix.mul_assoc] using
      Matrix.trace_mul_comm U (D * (Uᴴ * (X * Xᴴ)))
  calc
    _ = (D * (W * Wᴴ)).trace.re :=
      (converse_trace_diagonal_mul_adjoint hρ.eigenvalues W).symm
    _ = tracePair ρ (X * Xᴴ) := by
      rw [hW]
      unfold tracePair
      rw [hspec, hcycle]

theorem converse_weighted_cols_normSq {ρ σ : CMat ι}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (X : CMat ι) :
    (∑ i, ∑ j, hσ.eigenvalues j *
      Complex.normSq (((hρ.eigenvectorUnitary : CMat ι)ᴴ * X *
        (hσ.eigenvectorUnitary : CMat ι)) i j)) = tracePair σ (Xᴴ * X) := by
  let W : CMat ι := (hρ.eigenvectorUnitary : CMat ι)ᴴ * X *
    (hσ.eigenvectorUnitary : CMat ι)
  have hrev : (hσ.eigenvectorUnitary : CMat ι)ᴴ * Xᴴ *
      (hρ.eigenvectorUnitary : CMat ι) = Wᴴ := by
    simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have h := converse_weighted_rows_normSq hσ hρ.eigenvectorUnitary Xᴴ
  rw [hrev, Matrix.conjTranspose_conjTranspose] at h
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj] at h
  rw [Finset.sum_comm] at h
  exact h

theorem converse_complex_normSq_add_young (z w : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Complex.normSq (z + w) ≤
      (1 + δ) * Complex.normSq z + (1 + δ⁻¹) * Complex.normSq w := by
  have hs : Complex.normSq (z + w) * δ ≤
      δ * (1 + δ) * Complex.normSq z + (δ + 1) * Complex.normSq w := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    nlinarith [sq_nonneg (δ * z.re - w.re), sq_nonneg (δ * z.im - w.im)]
  calc
    Complex.normSq (z + w) ≤
        (δ * (1 + δ) * Complex.normSq z + (δ + 1) * Complex.normSq w) / δ :=
      (le_div_iff₀ hδ).mpr hs
    _ = _ := by field_simp [ne_of_gt hδ] <;> ring

theorem converse_spectral_overlap_effect_split {ρ σ : CMat ι}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (Q : CMat ι) (i j : ι) :
    (Spectral.overlapUnitary hρ hσ : CMat ι) i j =
      ((hρ.eigenvectorUnitary : CMat ι)ᴴ * (1 - Q) *
        (hσ.eigenvectorUnitary : CMat ι)) i j +
      ((hρ.eigenvectorUnitary : CMat ι)ᴴ * Q *
        (hσ.eigenvectorUnitary : CMat ι)) i j := by
  change (((hρ.eigenvectorUnitary : CMat ι)ᴴ *
    (hσ.eigenvectorUnitary : CMat ι)) i j) = _
  have hm : (hρ.eigenvectorUnitary : CMat ι)ᴴ * (hσ.eigenvectorUnitary : CMat ι) =
      (hρ.eigenvectorUnitary : CMat ι)ᴴ * (1 - Q) * (hσ.eigenvectorUnitary : CMat ι) +
      (hρ.eigenvectorUnitary : CMat ι)ᴴ * Q * (hσ.eigenvectorUnitary : CMat ι) := by
    noncomm_ring
  exact congrArg (fun M : CMat ι => M i j) hm

theorem converse_tracePair_complement {ρ Q : CMat ι} (hρ : IsState ρ) :
    tracePair ρ (1 - Q) = 1 - tracePair ρ Q := by
  unfold tracePair
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, hρ.2,
    Complex.sub_re, Complex.one_re]

theorem converse_ns_spectral_event_mass_bound {ρ σ Q : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hQ : IsEffect Q)
    (S : Finset (ι × ι)) {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ)
    (hS : ∀ z ∈ S, hρ.1.1.eigenvalues z.1 ≤ A * hσ.1.eigenvalues z.2 ∨
      nsWeight ρ σ z = 0) :
    (nsLaw ρ σ hρ hσ).mass S ≤
      (1 + δ) * (1 - tracePair ρ Q) + (1 + δ⁻¹) * A * tracePair σ Q := by
  classical
  let p : ι × ι → ℝ := fun z => hρ.1.1.eigenvalues z.1
  let q : ι × ι → ℝ := fun z => hσ.1.eigenvalues z.2
  let R : ι × ι → ℂ := fun z =>
    ((hρ.1.1.eigenvectorUnitary : CMat ι)ᴴ * (1 - Q) *
      (hσ.1.eigenvectorUnitary : CMat ι)) z.1 z.2
  let K : ι × ι → ℂ := fun z =>
    ((hρ.1.1.eigenvectorUnitary : CMat ι)ᴴ * Q *
      (hσ.1.eigenvectorUnitary : CMat ι)) z.1 z.2
  let f : ι × ι → ℝ := fun z => (1 + δ) * p z * Complex.normSq (R z) +
    (1 + δ⁻¹) * A * q z * Complex.normSq (K z)
  have hp (z : ι × ι) : 0 ≤ p z := hρ.1.eigenvalues_nonneg z.1
  have hq (z : ι × ι) : 0 ≤ q z := hσ.eigenvalues_nonneg z.2
  have hf (z : ι × ι) : 0 ≤ f z := by
    dsimp only [f]
    have hpn := hp z
    have hqn := hq z
    have hRn := Complex.normSq_nonneg (R z)
    have hKn := Complex.normSq_nonneg (K z)
    positivity
  have hw (z : ι × ι) : nsWeight ρ σ z = p z * Complex.normSq (R z + K z) := by
    rcases z with ⟨i, j⟩
    rw [nsWeight_eq_overlap hρ.1.1 hσ.1, Spectral.overlapWeight,
      converse_spectral_overlap_effect_split hρ.1.1 hσ.1 Q i j]
  have hpoint (z : ι × ι) (hz : z ∈ S) : nsWeight ρ σ z ≤ f z := by
    rcases hS z hz with hcomp | hzero
    · have hy := mul_le_mul_of_nonneg_left
        (converse_complex_normSq_add_young (R z) (K z) hδ) (hp z)
      have hb := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcomp (Complex.normSq_nonneg (K z)))
        (by positivity : 0 ≤ 1 + δ⁻¹)
      rw [hw]
      dsimp only [f, p, q] at *
      nlinarith
    · rw [hzero]
      exact hf z
  have hR : (∑ z : ι × ι, p z * Complex.normSq (R z)) =
      tracePair ρ ((1 - Q) * (1 - Q)) := by
    rw [Fintype.sum_prod_type]
    simpa only [p, R, hQ.2.1.eq] using
      converse_weighted_rows_normSq hρ.1.1 hσ.1.eigenvectorUnitary (1 - Q)
  have hK : (∑ z : ι × ι, q z * Complex.normSq (K z)) = tracePair σ (Q * Q) := by
    rw [Fintype.sum_prod_type]
    simpa only [q, K, hQ.1.1.eq] using converse_weighted_cols_normSq hρ.1.1 hσ.1 Q
  change (∑ z ∈ S, nsWeight ρ σ z) ≤ _
  calc
    _ ≤ ∑ z ∈ S, f z := Finset.sum_le_sum hpoint
    _ ≤ ∑ z, f z := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun z _ _ => hf z)
    _ = (1 + δ) * tracePair ρ ((1 - Q) * (1 - Q)) +
        (1 + δ⁻¹) * A * tracePair σ (Q * Q) := by
      simp only [f, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      rw [hR, hK]
    _ ≤ (1 + δ) * tracePair ρ (1 - Q) + (1 + δ⁻¹) * A * tracePair σ Q := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (converse_effect_square_pairing_le hρ.1 (converse_complement_isEffect hQ))
          (by positivity))
        (mul_le_mul_of_nonneg_left (converse_effect_square_pairing_le hσ hQ)
          (by positivity))
    _ = _ := by rw [converse_tracePair_complement hρ]

theorem converse_ns_likelihood_comparison_or_zero {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {a : ℝ} {z : ι × ι} (hle : nsLikelihood ρ σ z ≤ a) :
    hρ.1.1.eigenvalues z.1 ≤ Real.rpow 2 a * hσ.1.eigenvalues z.2 ∨
      nsWeight ρ σ z = 0 := by
  by_cases hp0 : hρ.1.1.eigenvalues z.1 = 0
  · right
    rw [nsWeight_eq_overlap hρ.1.1 hσ.1, hp0, zero_mul]
  by_cases hq0 : hσ.1.eigenvalues z.2 = 0
  · right
    rw [nsWeight_eq_overlap hρ.1.1 hσ.1,
      overlapWeight_zero_of_alternative_kernel hρ.1.1 hσ.1 hs z.1 z.2 hp0 hq0,
      mul_zero]
  left
  have hp : 0 < hρ.1.1.eigenvalues z.1 :=
    lt_of_le_of_ne (hρ.1.eigenvalues_nonneg z.1) (Ne.symm hp0)
  have hq : 0 < hσ.1.eigenvalues z.2 :=
    lt_of_le_of_ne (hσ.eigenvalues_nonneg z.2) (Ne.symm hq0)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlike : nsLikelihood ρ σ z =
      (Real.log (hρ.1.1.eigenvalues z.1 / hσ.1.eigenvalues z.2)) / Real.log 2 := by
    simp only [nsLikelihood, spectrumValue_of_isHermitian hρ.1.1,
      spectrumValue_of_isHermitian hσ.1, logTwo,
      Real.log_div (ne_of_gt hp) (ne_of_gt hq), sub_div]
  rw [hlike] at hle
  have hratio := (Real.le_rpow_iff_log_le (div_pos hp hq)
    (by norm_num : (0 : ℝ) < 2)).mpr ((div_le_iff₀ hlog2).mp hle)
  exact (div_le_iff₀ hq).mp hratio

theorem converse_ns_lowLikelihood_mass_le {ρ σ Q : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    (hQ : IsEffect Q) (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (nsLaw ρ σ hρ hσ).mass
      (Finset.univ.filter (fun z => nsLikelihood ρ σ z ≤ a)) ≤
        (1 + δ) * (1 - tracePair ρ Q) +
          (1 + δ⁻¹) * Real.rpow 2 a * tracePair σ Q := by
  classical
  apply converse_ns_spectral_event_mass_bound hρ hσ hQ _
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) a) hδ
  intro z hz
  exact converse_ns_likelihood_comparison_or_zero hρ hσ hs (Finset.mem_filter.mp hz).2

theorem converse_feasible_cost_ge_nsLowMass {ρ σ Q : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    (hQ : IsEffect Q) {ε a δ : ℝ} (hδ : 0 < δ)
    (hacc : 1 - ε ≤ tracePair ρ Q) :
    ((nsLaw ρ σ hρ hσ).mass
      (Finset.univ.filter (fun z => nsLikelihood ρ σ z ≤ a)) - (1 + δ) * ε) /
        ((1 + δ⁻¹) * Real.rpow 2 a) ≤ tracePair σ Q := by
  classical
  have hden : 0 < (1 + δ⁻¹) * Real.rpow 2 a :=
    mul_pos (by positivity) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) a)
  apply (div_le_iff₀ hden).mpr
  have hmass := converse_ns_lowLikelihood_mass_le hρ hσ hs hQ a hδ
  have hrejection : 1 - tracePair ρ Q ≤ ε := by linarith
  have hscale := mul_le_mul_of_nonneg_left hrejection (by positivity : 0 ≤ 1 + δ)
  nlinarith

theorem converse_testingBeta_ge_nsLowMass {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {ε a δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) :
    ((nsLaw ρ σ hρ hσ).mass
      (Finset.univ.filter (fun z => nsLikelihood ρ σ z ≤ a)) - (1 + δ) * ε) /
        ((1 + δ⁻¹) * Real.rpow 2 a) ≤ testingBeta ε ρ σ := by
  classical
  unfold testingBeta
  apply le_csInf (testingCosts_nonempty hε hρ)
  rintro b ⟨Q, hQ, hacc, rfl⟩
  exact converse_feasible_cost_ge_nsLowMass hρ hσ hs hQ hδ hacc

theorem converse_logTwo_mono_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    logTwo a ≤ logTwo b := by
  unfold logTwo
  exact div_le_div_of_nonneg_right (Real.log_le_log ha hab)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem converse_testingDivergence_upper_of_nsLowMass {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {ε a δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hgap : (1 + δ) * ε < (nsLaw ρ σ hρ hσ).mass
      (Finset.univ.filter (fun z => nsLikelihood ρ σ z ≤ a))) :
    testingDivergence ε ρ σ ≤
      (-logTwo (((nsLaw ρ σ hρ hσ).mass
        (Finset.univ.filter (fun z => nsLikelihood ρ σ z ≤ a)) - (1 + δ) * ε) /
          ((1 + δ⁻¹) * Real.rpow 2 a)) : EReal) := by
  classical
  have hβ := converse_testingBeta_ge_nsLowMass hρ hσ hs hε hδ (a := a)
  have hpos : 0 < ((nsLaw ρ σ hρ hσ).mass
      (Finset.univ.filter (fun z => nsLikelihood ρ σ z ≤ a)) - (1 + δ) * ε) /
        ((1 + δ⁻¹) * Real.rpow 2 a) :=
    div_pos (sub_pos.mpr hgap)
      (mul_pos (by positivity) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) a))
  have hβpos := hpos.trans_le hβ
  simp only [testingDivergence, ne_of_gt hβpos, if_false]
  exact EReal.coe_le_coe (neg_le_neg (converse_logTwo_mono_pos hpos hβ))

theorem converse_finiteLaw_mass_partition (L : FiniteLaw ι) (Z : ι → ℝ) (a : ℝ) :
    L.mass (Finset.univ.filter (fun i => Z i ≤ a)) +
      L.mass (Finset.univ.filter (fun i => a < Z i)) = 1 := by
  classical
  simpa only [FiniteLaw.mass, not_le, L.sum_weight] using
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => Z i ≤ a) L.weight

theorem converse_finiteLaw_low_mass_ge_secondMoment (L : FiniteLaw ι)
    (Z : ι → ℝ) (c : ℝ) {h : ℝ} (hh : 0 < h) :
    1 - L.secondMoment Z c / h ^ 2 ≤
      L.mass (Finset.univ.filter (fun i => Z i ≤ c + h)) := by
  classical
  have htail := L.upperTail_mass_le Z c hh
  have hpart := converse_finiteLaw_mass_partition L Z (c + h)
  dsimp only [FiniteLaw.upperTail] at htail
  linarith

theorem converse_ns_secondMoment_eq_weighted_zero {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (c : ℝ) :
    (nsLaw ρ σ hρ hσ).secondMoment (nsLikelihood ρ σ) c =
      nsWeightedMoment ρ σ c 0 := by
  simp only [FiniteLaw.secondMoment, FiniteLaw.expect, nsLaw,
    nsWeightedMoment, nsExpectation, zero_mul, Real.exp_zero, mul_one]

theorem converse_testingDivergence_upper_of_nsMoment {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {ε c h η δ : ℝ} (hε : 0 ≤ ε) (hh : 0 < h) (hδ : 0 < δ)
    (hgap : (1 + δ) * ε < 1 - η)
    (hbudget : nsWeightedMoment ρ σ c 0 ≤ η * h ^ 2) :
    testingDivergence ε ρ σ ≤
      (-logTwo (((1 - η) - (1 + δ) * ε) /
        ((1 + δ⁻¹) * Real.rpow 2 (c + h))) : EReal) := by
  classical
  let P := nsLaw ρ σ hρ hσ
  have hsecond : P.secondMoment (nsLikelihood ρ σ) c ≤ η * h ^ 2 := by
    rw [converse_ns_secondMoment_eq_weighted_zero hρ hσ c]
    exact hbudget
  have hmass : 1 - η ≤ P.mass
      (Finset.univ.filter (fun z => nsLikelihood ρ σ z ≤ c + h)) := by
    have htail := converse_finiteLaw_low_mass_ge_secondMoment P (nsLikelihood ρ σ) c hh
    have hquot : P.secondMoment (nsLikelihood ρ σ) c / h ^ 2 ≤ η :=
      (div_le_iff₀ (sq_pos_of_pos hh)).mpr hsecond
    linarith
  have hactual := converse_testingBeta_ge_nsLowMass hρ hσ hs hε hδ (a := c + h)
  have hden : 0 < (1 + δ⁻¹) * Real.rpow 2 (c + h) :=
    mul_pos (by positivity) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (c + h))
  have hβ : ((1 - η) - (1 + δ) * ε) /
      ((1 + δ⁻¹) * Real.rpow 2 (c + h)) ≤ testingBeta ε ρ σ :=
    (div_le_div_of_nonneg_right (sub_le_sub_right hmass ((1 + δ) * ε)) hden.le).trans hactual
  have hpos : 0 < ((1 - η) - (1 + δ) * ε) /
      ((1 + δ⁻¹) * Real.rpow 2 (c + h)) := div_pos (sub_pos.mpr hgap) hden
  have hβpos := hpos.trans_le hβ
  simp only [testingDivergence, ne_of_gt hβpos, if_false]
  exact EReal.coe_le_coe (neg_le_neg (converse_logTwo_mono_pos hpos hβ))

theorem converse_error_parameters_gap {ε : ℝ} (hε1 : ε < 1) :
    0 < (1 - ε) / 2 ∧ 0 < (1 - ε) / 4 ∧
      (1 + (1 - ε) / 2) * ε < 1 - (1 - ε) / 4 := by
  have hs : 0 < 1 - ε := sub_pos.mpr hε1
  refine ⟨by positivity, by positivity, ?_⟩
  have hp : 0 < (1 - ε) * (3 / 4 - ε / 2) :=
    mul_pos hs (by linarith)
  nlinarith

theorem converse_testingRemainder_sq (n : ℕ) :
    (testingRemainder n) ^ 2 = (n : ℝ) * (blockLog n) ^ 3 := by
  have hlog : 0 ≤ blockLog n := by
    unfold blockLog logTwo
    apply div_nonneg
    · apply Real.log_nonneg
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hp : (Real.rpow (blockLog n) (3 / 2 : ℝ)) ^ 2 = (blockLog n) ^ 3 := by
    simp only [Real.rpow_eq_pow]
    calc
      _ = ((blockLog n) ^ (3 / 2 : ℝ)) ^ (2 : ℝ) := by
        simpa only [Nat.cast_ofNat] using
          (Real.rpow_natCast ((blockLog n) ^ (3 / 2 : ℝ)) 2).symm
      _ = (blockLog n) ^ ((3 / 2 : ℝ) * 2) :=
        (Real.rpow_mul hlog (3 / 2 : ℝ) (2 : ℝ)).symm
      _ = (blockLog n) ^ (3 : ℝ) := by norm_num
      _ = (blockLog n) ^ 3 := by
        simpa only [Nat.cast_ofNat] using Real.rpow_natCast (blockLog n) 3
  unfold testingRemainder
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), hp]

theorem converse_logCube_radius_budget {ρ σ : CMat ι} {K η c : ℝ}
    (hK : 0 < K) (hη : 0 < η) (n : ℕ)
    (hbudget : nsWeightedMoment ρ σ c 0 ≤ K * (n : ℝ) * (blockLog n) ^ 3) :
    nsWeightedMoment ρ σ c 0 ≤
      η * (Real.sqrt (K / η) * testingRemainder n) ^ 2 := by
  have he : η * (Real.sqrt (K / η) * testingRemainder n) ^ 2 =
      K * (n : ℝ) * (blockLog n) ^ 3 := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hK.le hη.le), converse_testingRemainder_sq]
    field_simp [ne_of_gt hη] <;> ring
  rwa [he]

theorem converse_logTwo_two_rpow (x : ℝ) : logTwo (Real.rpow 2 x) = x := by
  unfold logTwo
  rw [Real.rpow_eq_pow, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

theorem converse_logTwo_div_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    logTwo (a / b) = logTwo a - logTwo b := by
  unfold logTwo
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)]
  ring

theorem converse_neg_logTwo_div_two_rpow {b a : ℝ} (hb : 0 < b) :
    -logTwo (b / Real.rpow 2 a) = a - logTwo b := by
  have hp : logTwo ((2 : ℝ) ^ a) = a := by
    simpa only [Real.rpow_eq_pow] using converse_logTwo_two_rpow a
  rw [Real.rpow_eq_pow, converse_logTwo_div_pos hb
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) a), hp]
  ring

theorem converse_testingDivergence_upper_of_logCubeMoment {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {ε K c : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hK : 0 < K)
    {n : ℕ} (hn : 0 < n)
    (hbudget : nsWeightedMoment ρ σ c 0 ≤ K * (n : ℝ) * (blockLog n) ^ 3) :
    let η := (1 - ε) / 4
    let δ := (1 - ε) / 2
    testingDivergence ε ρ σ ≤
      (c + Real.sqrt (K / η) * testingRemainder n -
        logTwo (((1 - η) - (1 + δ) * ε) / (1 + δ⁻¹)) : EReal) := by
  let η := (1 - ε) / 4
  let δ := (1 - ε) / 2
  obtain ⟨hδ, hη, hgap⟩ := converse_error_parameters_gap hε1
  have hh : 0 < Real.sqrt (K / η) * testingRemainder n :=
    mul_pos (Real.sqrt_pos.mpr (div_pos hK hη)) (testingRemainder_pos hn)
  have hu := converse_testingDivergence_upper_of_nsMoment hρ hσ hs hε0 hh hδ hgap
    (converse_logCube_radius_budget hK hη n hbudget)
  have hb : 0 < ((1 - η) - (1 + δ) * ε) / (1 + δ⁻¹) :=
    div_pos (sub_pos.mpr hgap) (by positivity)
  dsimp only [η, δ] at hb
  rw [← EReal.coe_neg, ← div_div, converse_neg_logTwo_div_two_rpow hb] at hu
  exact hu

end MatrixNSConverse

theorem physical_setTestingDivergence_upper_of_pair_nsMoment {d n : ℕ}
    {F : QuantumFamilies d} (hF : PhysicalAssumptions F) (hn : 0 < n)
    {ρ σ : QMat d n} (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n)
    {ε K : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hK : 0 < K)
    (hbudget : nsWeightedMoment ρ σ ((n : ℝ) * regularizedRate F) 0 ≤
      K * (n : ℝ) * (blockLog n) ^ 3) :
    let η := (1 - ε) / 4
    let δ := (1 - ε) / 2
    setTestingDivergence F n ε ≤
      ((n : ℝ) * regularizedRate F + Real.sqrt (K / η) * testingRemainder n -
        logTwo (((1 - η) - (1 + δ) * ε) / (1 + δ⁻¹)) : EReal) := by
  have hpair := converse_testingDivergence_upper_of_logCubeMoment
    (hF.null_states n hn ρ hρ) (hF.alternative_positive n hn σ hσ)
    (physical_pair_supportLE hF hn hρ hσ) hε0 hε1 hK hn hbudget
  have hset : setTestingDivergence F n ε ≤ testingDivergence ε ρ σ := by
    unfold setTestingDivergence
    exact sInf_le ⟨ρ, hρ, σ, hσ, rfl⟩
  exact hset.trans hpair

theorem represented_logTwo_div_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    logTwo (a / b) = logTwo a - logTwo b := by
  unfold logTwo
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)]
  ring

theorem logTwo_div_two_rpow {a c : ℝ} (ha : 0 < a) :
    -logTwo (a / Real.rpow 2 c) = c - logTwo a := by
  have hp : logTwo ((2 : ℝ) ^ c) = c := by
    simpa only [Real.rpow_eq_pow] using Testing.logTwo_rpow_two c
  rw [Real.rpow_eq_pow, represented_logTwo_div_pos ha
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) c), hp]
  ring

theorem testingDivergence_linear_bounds_of_domination_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {ε c : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hdom : LoewnerLE ρ ((Real.rpow 2 c : ℂ) • σ))
    (hlog : logTwo σ.trace.re ≤ c) :
    (-c : EReal) ≤ testingDivergence ε ρ σ ∧
      testingDivergence ε ρ σ ≤ (c - logTwo (1 - ε) : EReal) := by
  have hscale : 0 < Real.rpow 2 c :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) c
  have hT := trace_re_pos_of_state_domination hρ hscale hdom
  constructor
  · have hacc : 1 - ε ≤ tracePair ρ 1 := by
      rw [tracePair_one_right, hρ.trace_real]
      linarith
    have hl := Testing.testingDivergence_lower_of_cost hε0 hT hρ hσ
      isEffect_one hacc (by rw [tracePair_one_right])
    exact (EReal.coe_le_coe (neg_le_neg hlog)).trans hl
  · have hb : 0 < (1 - ε) / Real.rpow 2 c := div_pos (sub_pos.mpr hε1) hscale
    have hu := Testing.testingDivergence_upper_of_all_costs hε0 hb hρ
      (fun Q hQ hacc => Testing.feasible_cost_ge_of_domination hscale hdom hQ hacc)
    rw [← EReal.coe_neg, logTwo_div_two_rpow (sub_pos.mpr hε1)] at hu
    exact hu

theorem physical_linear_setTestingDivergence_bounds {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      ∀ ε : ℝ, 0 ≤ ε → ε < 1 →
        (-C * (n : ℝ) : EReal) ≤ setTestingDivergence F n ε ∧
          setTestingDivergence F n ε ≤ (C * (n : ℝ) - logTwo (1 - ε) : EReal) := by
  obtain ⟨C, hC, hgrowth⟩ := physical_linear_growth_nonneg hF
  refine ⟨C, hC, ?_⟩
  intro n hn ε hε0 hε1
  have hp : ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      (-(C * (n : ℝ)) : EReal) ≤ testingDivergence ε ρ σ ∧
        testingDivergence ε ρ σ ≤ (C * (n : ℝ) - logTwo (1 - ε) : EReal) := by
    intro ρ hρ σ hσ
    exact testingDivergence_linear_bounds_of_domination_trace
      (hF.null_states n hn ρ hρ) (hF.alternative_positive n hn σ hσ)
      hε0 hε1 (hgrowth n hn ρ hρ σ hσ).1 (hgrowth n hn ρ hρ σ hσ).2
  constructor
  · simpa only [neg_mul] using Testing.setTestingDivergence_lower_of_pairwise F ε
      (fun ρ hρ σ hσ => (hp ρ hρ σ hσ).1)
  · obtain ⟨ρ, hρ⟩ := hF.null_nonempty n hn
    obtain ⟨σ, hσ⟩ := hF.alternative_nonempty n hn
    exact Testing.setTestingDivergence_upper_of_pair F ε hρ hσ (hp ρ hρ σ hσ).2

theorem physical_setTestingDivergence_finite {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    setTestingDivergence F n ε ≠ ⊤ ∧ setTestingDivergence F n ε ≠ ⊥ := by
  obtain ⟨C, _, hC⟩ := physical_linear_setTestingDivergence_bounds hF
  have hl := (hC n hn ε hε0 hε1).1
  have hu := (hC n hn ε hε0 hε1).2
  constructor
  · intro ht
    have hc : (C * (n : ℝ) - logTwo (1 - ε) : EReal) = ⊤ :=
      le_antisymm le_top (by simpa only [ht] using hu)
    exact EReal.coe_ne_top _ hc
  · intro hb
    have hc : (-C * (n : ℝ) : EReal) = ⊥ :=
      le_antisymm (by simpa only [hb] using hl) bot_le
    exact EReal.coe_ne_bot _ hc

theorem physical_testing_linear_remainder {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |(setTestingDivergence F n ε).toReal - (n : ℝ) * regularizedRate F| ≤ K * (n : ℝ) := by
  obtain ⟨C, hC, hgrowth⟩ := physical_linear_setTestingDivergence_bounds hF
  let L : ℝ := -logTwo (1 - ε)
  have hL : 0 ≤ L := by
    have hlog := Testing.logTwo_mono_pos (sub_pos.mpr hε1)
      (by linarith : 1 - ε ≤ 1)
    dsimp only [L]
    exact neg_nonneg.mpr (by simpa [logTwo] using hlog)
  let K : ℝ := C + |regularizedRate F| + L + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro n hn
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hf := physical_setTestingDivergence_finite hF hn hε0 hε1
  have hbounds := hgrowth n hn ε hε0 hε1
  have hl : -C * (n : ℝ) ≤ (setTestingDivergence F n ε).toReal := by
    simpa only [← EReal.coe_neg, ← EReal.coe_mul, EReal.toReal_coe] using EReal.toReal_le_toReal
      hbounds.1 (EReal.coe_ne_bot _) hf.1
  have hu : (setTestingDivergence F n ε).toReal ≤ C * (n : ℝ) + L := by
    simpa only [← EReal.coe_mul, ← EReal.coe_neg, ← EReal.coe_add,
      EReal.toReal_coe, sub_eq_add_neg, L] using EReal.toReal_le_toReal
      hbounds.2 hf.2 (EReal.coe_ne_top _)
  have hrlo := mul_le_mul_of_nonneg_right (neg_abs_le (regularizedRate F)) hn0
  have hrhi := mul_le_mul_of_nonneg_right (le_abs_self (regularizedRate F)) hn0
  have hLn : L ≤ L * (n : ℝ) := by nlinarith
  rw [abs_le]
  dsimp [K]
  constructor <;> nlinarith

theorem testingRemainder_ge_one {n : ℕ} (hn : 0 < n) :
    1 ≤ testingRemainder n := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := by simpa using Real.sqrt_le_sqrt hnR
  have hlog : 1 ≤ blockLog n := by
    unfold blockLog logTwo
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    simpa only [one_mul] using Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by linarith : (2 : ℝ) ≤ (n : ℝ) + 1)
  have hpow := Real.one_le_rpow hlog (by norm_num : (0 : ℝ) ≤ 3 / 2)
  unfold testingRemainder
  simpa only [one_mul, Real.rpow_eq_pow] using mul_le_mul hsqrt hpow
    (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg (n : ℝ))

theorem physical_testing_finite_base {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (N : ℕ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) : ∃ K : ℝ, 0 < K ∧
      ∀ n : ℕ, 0 < n → n ≤ N →
        |(setTestingDivergence F n ε).toReal - (n : ℝ) * regularizedRate F| ≤
          K * testingRemainder n := by
  obtain ⟨L, hL, hlinear⟩ := physical_testing_linear_remainder hF hε0 hε1
  have hK : 0 < L * (N : ℝ) + 1 := by positivity
  refine ⟨L * (N : ℝ) + 1, hK, ?_⟩
  intro n hn hN
  have hNr : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  calc
    _ ≤ L * (n : ℝ) := hlinear n hn
    _ ≤ L * (N : ℝ) := mul_le_mul_of_nonneg_left hNr hL.le
    _ ≤ L * (N : ℝ) + 1 := by linarith
    _ ≤ (L * (N : ℝ) + 1) * testingRemainder n := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (testingRemainder_ge_one hn) hK.le

section MatrixPetzTensor

open QuantumProver.SuperchannelDiscrimination.TensorEntropy
open scoped Kronecker

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem matrixRpow_kronecker {A : CMat ι} {B : CMat κ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (α : ℝ) :
    matrixRpow (A ⊗ₖ B) α = matrixRpow A α ⊗ₖ matrixRpow B α := by
  have hd : Matrix.diagonal (fun x : ι × κ =>
      (Real.rpow (hA.1.eigenvalues x.1 * hB.1.eigenvalues x.2) α : ℂ)) =
      Matrix.diagonal (fun i => (Real.rpow (hA.1.eigenvalues i) α : ℂ)) ⊗ₖ
        Matrix.diagonal (fun j => (Real.rpow (hB.1.eigenvalues j) α : ℂ)) := by
    rw [Matrix.diagonal_kronecker_diagonal]
    congr 1
    funext x
    simpa only [Real.rpow_eq_pow, Complex.ofReal_mul] using
      congrArg (fun z : ℝ => (z : ℂ))
        (Real.mul_rpow (hA.eigenvalues_nonneg x.1) (hB.eigenvalues_nonneg x.2) (z := α))
  unfold matrixRpow
  rw [cfc_kronecker_spectral _ hA.1 hB.1, hd, unitaryKronecker_conjugate]
  exact congrArg₂ Matrix.kronecker
    (cfc_spectral (fun x => Real.rpow x α) hA.1).symm
    (cfc_spectral (fun x => Real.rpow x α) hB.1).symm

theorem matrixRpow_isHermitian (A : CMat ι) (α : ℝ) :
    (matrixRpow A α).IsHermitian :=
  cfc_predicate (p := IsSelfAdjoint) (fun x : ℝ => Real.rpow x α) A

theorem trace_mul_im_eq_zero_of_isHermitian {A B : CMat ι}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A * B)).im = 0 := by
  have hs : star (Matrix.trace (A * B)) = Matrix.trace (A * B) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hB.eq, hA.eq]
    exact Matrix.trace_mul_comm B A
  have hi := congrArg Complex.im hs
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

theorem petzTrace_kronecker {ρ σ : CMat ι} {τ υ : CMat κ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hτ : τ.PosSemidef) (hυ : υ.PosSemidef) (α : ℝ) :
    petzTrace (ρ ⊗ₖ τ) (σ ⊗ₖ υ) α = petzTrace ρ σ α * petzTrace τ υ α := by
  unfold petzTrace tracePair
  rw [matrixRpow_kronecker hρ hτ, matrixRpow_kronecker hσ hυ,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, Complex.mul_re,
    trace_mul_im_eq_zero_of_isHermitian (matrixRpow_isHermitian ρ α)
      (matrixRpow_isHermitian σ (1 - α)), zero_mul, sub_zero]

theorem petzTrace_submatrix_equiv (e : ι ≃ κ) {ρ σ : CMat κ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (α : ℝ) :
    petzTrace (ρ.submatrix e e) (σ.submatrix e e) α = petzTrace ρ σ α := by
  unfold petzTrace tracePair matrixRpow
  rw [cfc_submatrix_equiv e _ hρ, cfc_submatrix_equiv e _ hσ,
    Matrix.submatrix_mul_equiv, trace_submatrix_equiv]

theorem petzTrace_tensorMatrix {d m n : ℕ} {ρ σ : QMat d m} {τ υ : QMat d n}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (hτ : τ.PosSemidef) (hυ : υ.PosSemidef) (α : ℝ) :
    petzTrace (tensorMatrix ρ τ) (tensorMatrix σ υ) α =
      petzTrace ρ σ α * petzTrace τ υ α := by
  rw [tensorMatrix_eq_kronecker, tensorMatrix_eq_kronecker]
  simp only [Matrix.kronecker]
  rw [petzTrace_submatrix_equiv (wordSplitEquiv d m n) (hρ.kronecker hτ).1
      (hσ.kronecker hυ).1]
  exact petzTrace_kronecker hρ hσ hτ hυ α

theorem represented_logTwo_mul_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    logTwo (a * b) = logTwo a + logTwo b := by
  unfold logTwo
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hb)]
  ring

theorem petzDivergence_real_of_support (ρ σ : CMat ι)
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) :
    petzDivergence ρ σ α =
      ((logTwo (petzTrace ρ σ α) / (α - 1) : ℝ) : EReal) := by
  have hp := petzDivergence_of_support ρ σ hρ hσ hs hα hα1
  rw [← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_div] at hp
  exact hp

theorem physical_pair_petz_tensor {d m n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hm : 0 < m) (hn : 0 < n)
    {ρ σ : QMat d m} {τ υ : QMat d n}
    (hρ : ρ ∈ F.null m) (hσ : σ ∈ F.alternative m)
    (hτ : τ ∈ F.null n) (hυ : υ ∈ F.alternative n)
    {α : ℝ} (hα : 0 < α) :
    petzDivergence (tensorMatrix ρ τ) (tensorMatrix σ υ) α =
      petzDivergence ρ σ α + petzDivergence τ υ α := by
  have hr := hF.null_states m hm ρ hρ
  have hs := hF.alternative_positive m hm σ hσ
  have ht := hF.null_states n hn τ hτ
  have hu := hF.alternative_positive n hn υ hυ
  by_cases hα1 : α = 1
  · subst α
    simpa [petzDivergence] using umegaki_tensorMatrix hr hs ht hu
  have hρτ := hF.null_tensor m n hm hn ρ hρ τ hτ
  have hσυ := hF.alternative_tensor m n hm hn σ hσ υ hυ
  rw [petzDivergence_real_of_support _ _ (isState_tensorMatrix hr ht)
      (hF.alternative_positive (m + n) (by omega) _ hσυ)
      (physical_pair_supportLE hF (by omega) hρτ hσυ) hα hα1,
    petzDivergence_real_of_support ρ σ hr hs (physical_pair_supportLE hF hm hρ hσ) hα hα1,
    petzDivergence_real_of_support τ υ ht hu (physical_pair_supportLE hF hn hτ hυ) hα hα1,
    petzTrace_tensorMatrix hr.1 hs ht.1 hu,
    represented_logTwo_mul_pos (petzTrace_pos_of_support ρ σ hr hs
      (physical_pair_supportLE hF hm hρ hσ) hα)
      (petzTrace_pos_of_support τ υ ht hu (physical_pair_supportLE hF hn hτ hυ) hα)]
  simp only [← EReal.coe_add]
  congr 1
  ring

end MatrixPetzTensor

theorem physical_pair_petz_repetition {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {ρ σ : QMat d n}
    (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) (k : ℕ) (hk : 0 < k) :
    ∃ ρk σk : QMat d (k * n), ρk ∈ F.null (k * n) ∧
      σk ∈ F.alternative (k * n) ∧ petzDivergence ρk σk α =
        (((k : ℝ) * (logTwo (petzTrace ρ σ α) / (α - 1)) : ℝ) : EReal) := by
  have hp := petzDivergence_real_of_support ρ σ (hF.null_states n hn ρ hρ)
    (hF.alternative_positive n hn σ hσ) (physical_pair_supportLE hF hn hρ hσ) hα hα1
  revert hk
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst k
      let P : ℕ → Prop := fun N => ∃ ρk σk : QMat d N,
        ρk ∈ F.null N ∧ σk ∈ F.alternative N ∧ petzDivergence ρk σk α =
          ((1 * (logTwo (petzTrace ρ σ α) / (α - 1)) : ℝ) : EReal)
      have hb : P n := ⟨ρ, σ, hρ, hσ, by simpa only [one_mul] using hp⟩
      have ht : P (1 * n) := Eq.mpr (congrArg P (Nat.one_mul n)) hb
      simpa only [P, Nat.zero_add, Nat.cast_one] using ht
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      obtain ⟨ρk, σk, hρk, hσk, hPk⟩ := ih hkpos
      have hkn : 0 < k * n := Nat.mul_pos hkpos hn
      rw [Nat.succ_mul]
      refine ⟨tensorMatrix ρk ρ, tensorMatrix σk σ,
        hF.null_tensor (k * n) n hkn hn ρk hρk ρ hρ,
        hF.alternative_tensor (k * n) n hkn hn σk hσk σ hσ, ?_⟩
      rw [physical_pair_petz_tensor hF hkn hn hρk hσk hρ hσ hα, hPk, hp,
        ← EReal.coe_add]
      congr 1
      simp only [Nat.cast_add, Nat.cast_one]
      ring

theorem physical_set_entropy_bounds_of_pair_bounds {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (C : ℝ)
    (hp : ∀ n, 0 < n → ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      -(C * (n : ℝ)) ≤ umegakiReal ρ σ ∧ umegakiReal ρ σ ≤ C * (n : ℝ))
    {n : ℕ} (hn : 0 < n) :
    -(C * (n : ℝ)) ≤ (setUmegaki F n).toReal ∧
      (setUmegaki F n).toReal ≤ C * (n : ℝ) := by
  constructor
  · have hl : ((-(C * (n : ℝ)) : ℝ) : EReal) ≤ setUmegaki F n := by
      apply setUmegaki_ge_of_pair_lower
      intro ρ hρ σ hσ
      rw [umegaki_of_support (physical_pair_supportLE hF hn hρ hσ)]
      exact EReal.coe_le_coe (hp n hn ρ hρ σ hσ).1
    simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal hl
      (EReal.coe_ne_bot _) (physical_setUmegaki_ne_top hF hn)
  · obtain ⟨ρ, hρ⟩ := hF.null_nonempty n hn
    obtain ⟨σ, hσ⟩ := hF.alternative_nonempty n hn
    exact (setUmegaki_toReal_le_pair_of_lower hF hn (-(C * (n : ℝ)))
      (fun ρ hρ σ hσ => (hp n hn ρ hρ σ hσ).1) hρ hσ).trans (hp n hn ρ hρ σ hσ).2

theorem physical_rate_abs_le_of_pair_entropy_bounds {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (C : ℝ)
    (hp : ∀ n, 0 < n → ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      -(C * (n : ℝ)) ≤ umegakiReal ρ σ ∧ umegakiReal ρ σ ≤ C * (n : ℝ)) :
    |regularizedRate F| ≤ C := by
  have hlim := (physical_actual_full_rate hF).2
  have he : ∀ᶠ n : ℕ in Filter.atTop,
      -C ≤ (setUmegaki F n).toReal / (n : ℝ) ∧
        (setUmegaki F n).toReal / (n : ℝ) ≤ C := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hb := physical_set_entropy_bounds_of_pair_bounds hF C hp hnpos
    constructor
    · apply (le_div_iff₀ hnR).mpr
      simpa only [neg_mul] using hb.1
    · exact (div_le_iff₀ hnR).mpr hb.2
  exact abs_le.mpr ⟨ge_of_tendsto hlim (he.mono fun n h => h.1),
    le_of_tendsto hlim (he.mono fun n h => h.2)⟩

theorem physical_fixed_growth_entropy_rate_bounds {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ C : ℝ, 0 ≤ C ∧ |regularizedRate F| ≤ C ∧
      ∀ n : ℕ, 0 < n → ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
        LoewnerLE ρ ((Real.rpow 2 (C * (n : ℝ)) : ℂ) • σ) ∧
          logTwo (Matrix.trace σ).re ≤ C * (n : ℝ) ∧
            |umegakiReal ρ σ| ≤ C * (n : ℝ) := by
  obtain ⟨C, hC, hgrowth⟩ := physical_linear_growth_nonneg hF
  have hp : ∀ n, 0 < n → ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      -(C * (n : ℝ)) ≤ umegakiReal ρ σ ∧ umegakiReal ρ σ ≤ C * (n : ℝ) := by
    intro n hn ρ hρ σ hσ
    have hr := hF.null_states n hn ρ hρ
    have hs := hF.alternative_positive n hn σ hσ
    have ha : 0 < Real.rpow 2 (C * (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have hd := (hgrowth n hn ρ hρ σ hσ).1
    have hT := trace_re_pos_of_state_domination hr ha hd
    constructor
    · exact (neg_le_neg (hgrowth n hn ρ hρ σ hσ).2).trans
        (umegakiReal_ge_neg_log_trace_via_trace hr hs hT
          (physical_pair_supportLE hF hn hρ hσ))
    · have hdr : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ) := by
        simpa only [complex_real_smul] using hd
      simpa only [converse_logTwo_two_rpow] using umegakiReal_le_log_of_domination hr hs ha hdr
  refine ⟨C, hC, physical_rate_abs_le_of_pair_entropy_bounds hF C hp, ?_⟩
  intro n hn ρ hρ σ hσ
  exact ⟨(hgrowth n hn ρ hρ σ hσ).1, (hgrowth n hn ρ hρ σ hσ).2,
    abs_le.mpr (hp n hn ρ hρ σ hσ)⟩

theorem le_two_rpow_of_logTwo_le {a c : ℝ} (ha : 0 < a)
    (hlog : logTwo a ≤ c) : a ≤ Real.rpow 2 c := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log a ≤ c * Real.log 2 := (div_le_iff₀ hlog2).mp hlog
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_log ha] at he
  simpa only [Real.rpow_eq_pow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    mul_comm] using he

theorem represented_blockLog_ge_one {n : ℕ} (hn : 0 < n) : 1 ≤ blockLog n := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
  unfold blockLog logTwo
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  simpa only [one_mul] using Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (by linarith : (2 : ℝ) ≤ (n : ℝ) + 1)

theorem physical_quantum_moment_finite_base {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (N : ℕ) : ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ n : ℕ, 0 < n → n ≤ N → ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
        ∀ t : ℝ, 0 ≤ t → t ≤ c / (n : ℝ) →
          nsWeightedMoment ρ σ ((n : ℝ) * regularizedRate F) t ≤
            K * (n : ℝ) * (blockLog n) ^ 3 := by
  obtain ⟨C, hC, _, hgrowth⟩ := physical_fixed_growth_entropy_rate_bounds hF
  let β : ℝ := Real.log 2 / 2
  let A : ℝ := (16 / β ^ 2) * Real.sqrt (Real.rpow 2 (C * (N : ℝ))) *
    Real.exp (β * ((N : ℝ) * |regularizedRate F|))
  let K : ℝ := A + 1
  let c : ℝ := Real.log 2 / 4
  have hβ : 0 < β := by dsimp [β]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 < K := by dsimp [K]; linarith
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨K, c, hK, hc, ?_⟩
  intro n hn hN ρ hρ σ hσ t ht0 ht
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hNR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hr := hF.null_states n hn ρ hρ
  have hs := hF.alternative_positive n hn σ hσ
  obtain ⟨hd, hl, _⟩ := hgrowth n hn ρ hρ σ hσ
  have ha : 0 < Real.rpow 2 (C * (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hT := trace_re_pos_of_state_domination hr ha hd
  have hdr : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ) := by
    simpa only [complex_real_smul] using hd
  have htrace := le_two_rpow_of_logTwo_le hT hl
  have hcn : c / (n : ℝ) ≤ c := (div_le_iff₀ hnR).mpr (by nlinarith)
  have htconst : t ≤ Real.log 2 / 4 := ht.trans hcn
  have hm := nsWeightedMoment_crude_bound hr hs ha hdr htrace
    ((n : ℝ) * regularizedRate F) htconst
  have hpow : Real.rpow 2 (C * (n : ℝ)) ≤ Real.rpow 2 (C * (N : ℝ)) := by
    simpa only [Real.rpow_eq_pow] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (mul_le_mul_of_nonneg_left hNR hC)
  have hsqrt : Real.sqrt (Real.rpow 2 (C * (n : ℝ))) ≤
      Real.sqrt (Real.rpow 2 (C * (N : ℝ))) := Real.sqrt_le_sqrt hpow
  have hcentre : |(n : ℝ) * regularizedRate F| ≤ (N : ℝ) * |regularizedRate F| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    exact mul_le_mul_of_nonneg_right hNR (abs_nonneg _)
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcentre hβ.le)
  have hAupper : (16 / (Real.log 2 / 2) ^ 2) * Real.sqrt (Real.rpow 2 (C * (n : ℝ))) *
      Real.exp ((Real.log 2 / 2) * |(n : ℝ) * regularizedRate F|) ≤ A := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by positivity)) hexp
      (Real.exp_pos _).le (by dsimp [β]; positivity)
  have hlog : 1 ≤ (blockLog n) ^ 3 := one_le_pow₀ (represented_blockLog_ge_one hn)
  have hpoly : 1 ≤ (n : ℝ) * (blockLog n) ^ 3 := by
    simpa only [one_mul] using mul_le_mul hn1 hlog
      (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg n)
  calc
    _ ≤ A := hm.trans hAupper
    _ ≤ K := by dsimp [K]; linarith
    _ ≤ K * ((n : ℝ) * (blockLog n) ^ 3) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpoly hK.le
    _ = _ := by ring

section MatrixLowerLaplace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nsLaw_log_laplace_eq_petzReal {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) (hs : SupportLE ρ σ)
    (c : ℝ) {t : ℝ} (ht : 0 < t) (hα : 0 < 1 - t / Real.log 2) :
    Real.log ((nsLaw ρ σ hρ hσ).expect
      (fun z => Real.exp (-t * (nsLikelihood ρ σ z - c)))) =
        t * (c - logTwo (petzTrace ρ σ (1 - t / Real.log 2)) /
          ((1 - t / Real.log 2) - 1)) := by
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hp := petzTrace_pos_of_support ρ σ hρ hσ hs hα
  have hd : Real.log (petzTrace ρ σ (1 - t / Real.log 2)) =
      -t * (logTwo (petzTrace ρ σ (1 - t / Real.log 2)) /
        ((1 - t / Real.log 2) - 1)) := by
    have hden : (1 - t / Real.log 2) - 1 = -t / Real.log 2 := by ring
    rw [hden]
    unfold logTwo
    field_simp [hlog2, ht.ne']
    <;> ring
  rw [nsLaw_laplace_centered ρ σ hρ hσ hs c t hα,
    Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hp), Real.log_exp, hd]
  ring

end MatrixLowerLaplace

theorem physical_ns_laplace_le_of_petz_lower {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {ρ σ : QMat d n}
    (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n)
    {t L : ℝ} (ht : 0 < t) (hα : 0 < 1 - t / Real.log 2)
    (hL : ((L : ℝ) : EReal) ≤ petzDivergence ρ σ (1 - t / Real.log 2)) :
    (nsLaw ρ σ (hF.null_states n hn ρ hρ)
      (hF.alternative_positive n hn σ hσ)).expect
        (fun z => Real.exp (-t * (nsLikelihood ρ σ z -
          (n : ℝ) * regularizedRate F))) ≤
            Real.exp (t * ((n : ℝ) * regularizedRate F - L)) := by
  have hr := hF.null_states n hn ρ hρ
  have hs := hF.alternative_positive n hn σ hσ
  have hsup := physical_pair_supportLE hF hn hρ hσ
  have hα1 : 1 - t / Real.log 2 ≠ 1 := by
    have hpos : 0 < t / Real.log 2 := div_pos ht (Real.log_pos (by norm_num))
    linarith
  rw [petzDivergence_real_of_support ρ σ hr hs hsup hα hα1] at hL
  have hLR := EReal.coe_le_coe_iff.mp hL
  let P := nsLaw ρ σ hr hs
  have hid := nsLaw_log_laplace_eq_petzReal hr hs hsup
    ((n : ℝ) * regularizedRate F) ht hα
  have hlog : Real.log (P.expect (fun z => Real.exp (-t *
      (nsLikelihood ρ σ z - (n : ℝ) * regularizedRate F)))) ≤
        t * ((n : ℝ) * regularizedRate F - L) := by
    rw [hid]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hLR _) ht.le
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (P.expect_pos (fun z => Real.exp_pos _))] at he
  exact he

def measuredEntropyRates {d : ℕ} (F : QuantumFamilies d) (α : ℝ) : Set ℝ :=
  ScalarRate.rateSet (fun n => (setMeasuredDivergence F n α).toReal)

def measuredRateSupremum {d : ℕ} (F : QuantumFamilies d) (α : ℝ) : ℝ :=
  sSup (measuredEntropyRates F α)

theorem measuredEntropyRates_nonempty {d : ℕ} (F : QuantumFamilies d) (α : ℝ) :
    (measuredEntropyRates F α).Nonempty :=
  ScalarRate.rateSet_nonempty _

theorem physical_linear_pair_measured_bounds {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n, ∀ α : ℝ, 0 < α → α < 1 →
        ((-C * (n : ℝ) : ℝ) : EReal) ≤ measuredDivergence ρ σ α ∧
          measuredDivergence ρ σ α ≤ ((C * (n : ℝ) : ℝ) : EReal) := by
  obtain ⟨C, hC, hgrowth⟩ := physical_linear_growth_nonneg hF
  refine ⟨C, hC, ?_⟩
  intro n hn ρ hρ σ hσ α hα hα1
  have hr := hF.null_states n hn ρ hρ
  have hs := hF.alternative_positive n hn σ hσ
  obtain ⟨hd, hl⟩ := hgrowth n hn ρ hρ σ hσ
  have ha : 0 < Real.rpow 2 (C * (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · have hlow := Testing.measuredDivergence_ge_neg_log_trace_of_domination hr ha hd α
    have hcost : ((-C * (n : ℝ) : ℝ) : EReal) ≤
        (-logTwo (Matrix.trace σ).re : EReal) := by
      exact EReal.coe_le_coe (by simpa only [neg_mul] using neg_le_neg hl)
    exact hcost.trans hlow
  · simpa only [converse_logTwo_two_rpow] using
      Testing.measuredDivergence_le_log_of_domination hr hs ha hd hα hα1

theorem physical_linear_setMeasuredDivergence_bounds {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      ∀ α : ℝ, 0 < α → α < 1 →
        ((-C * (n : ℝ) : ℝ) : EReal) ≤ setMeasuredDivergence F n α ∧
          setMeasuredDivergence F n α ≤ ((C * (n : ℝ) : ℝ) : EReal) := by
  obtain ⟨C, hC, hp⟩ := physical_linear_pair_measured_bounds hF
  refine ⟨C, hC, ?_⟩
  intro n hn α hα hα1
  constructor
  · unfold setMeasuredDivergence
    apply le_sInf
    rintro x ⟨ρ, hρ, σ, hσ, rfl⟩
    exact (hp n hn ρ hρ σ hσ α hα hα1).1
  · obtain ⟨ρ, hρ⟩ := hF.null_nonempty n hn
    obtain ⟨σ, hσ⟩ := hF.alternative_nonempty n hn
    have hset : setMeasuredDivergence F n α ≤ measuredDivergence ρ σ α :=
      sInf_le ⟨ρ, hρ, σ, hσ, rfl⟩
    exact hset.trans (hp n hn ρ hρ σ hσ α hα hα1).2

theorem physical_setMeasuredDivergence_finite {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {n : ℕ} (hn : 0 < n)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    setMeasuredDivergence F n α ≠ ⊤ ∧ setMeasuredDivergence F n α ≠ ⊥ := by
  obtain ⟨C, _, hb⟩ := physical_linear_setMeasuredDivergence_bounds hF
  have hl := (hb n hn α hα hα1).1
  have hu := (hb n hn α hα hα1).2
  constructor
  · intro htop
    have he : ((C * (n : ℝ) : ℝ) : EReal) = ⊤ :=
      le_antisymm le_top (by simpa only [htop] using hu)
    exact EReal.coe_ne_top _ he
  · intro hbot
    have he : ((-C * (n : ℝ) : ℝ) : EReal) = ⊥ :=
      le_antisymm (by simpa only [hbot] using hl) bot_le
    exact EReal.coe_ne_bot _ he

theorem physical_measuredEntropyRates_bounded {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ α : ℝ, 0 < α → α < 1 →
      BddBelow (measuredEntropyRates F α) ∧ BddAbove (measuredEntropyRates F α) ∧
        |measuredRateSupremum F α| ≤ C := by
  obtain ⟨C, hC, hb⟩ := physical_linear_setMeasuredDivergence_bounds hF
  refine ⟨C, hC, ?_⟩
  intro α hα hα1
  have hnorm : ∀ x ∈ measuredEntropyRates F α, -C ≤ x ∧ x ≤ C := by
    rintro x ⟨n, hn, rfl⟩
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hf := physical_setMeasuredDivergence_finite hF hn hα hα1
    have hl : -C * (n : ℝ) ≤ (setMeasuredDivergence F n α).toReal := by
      simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal
        (hb n hn α hα hα1).1 (EReal.coe_ne_bot _) hf.1
    have hu : (setMeasuredDivergence F n α).toReal ≤ C * (n : ℝ) := by
      simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal
        (hb n hn α hα hα1).2 hf.2 (EReal.coe_ne_top _)
    exact ⟨(le_div_iff₀ hnR).mpr hl, (div_le_iff₀ hnR).mpr hu⟩
  have hlo : BddBelow (measuredEntropyRates F α) := ⟨-C, fun x hx => (hnorm x hx).1⟩
  have hhi : BddAbove (measuredEntropyRates F α) := ⟨C, fun x hx => (hnorm x hx).2⟩
  obtain ⟨x, hx⟩ := measuredEntropyRates_nonempty F α
  have hsupLo : -C ≤ measuredRateSupremum F α :=
    (hnorm x hx).1.trans (le_csSup hhi hx)
  have hsupHi : measuredRateSupremum F α ≤ C :=
    csSup_le (measuredEntropyRates_nonempty F α) (fun x hx => (hnorm x hx).2)
  exact ⟨hlo, hhi, abs_le.mpr ⟨hsupLo, hsupHi⟩⟩

theorem physical_measured_block_le_supremum {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {n : ℕ} (hn : 0 < n)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    (setMeasuredDivergence F n α).toReal / (n : ℝ) ≤ measuredRateSupremum F α := by
  obtain ⟨C, _, hb⟩ := physical_measuredEntropyRates_bounded hF
  exact le_csSup (hb α hα hα1).2.1 ⟨n, hn, rfl⟩

theorem umegaki_lowerSemicontinuousOn_density {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    LowerSemicontinuousOn (fun p : CMat ι × CMat ι => umegaki p.1 p.2)
      {p | IsState p.1 ∧ p.2.PosSemidef} := by
  simpa only [umegaki_eq_shared_relativeEntropyBits, IsState,
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.IsDensity] using
    (QuantumProver.QuantumRelativeEntropyContinuity.lowerSemicontinuousOn_relativeEntropyBits_density
      (I := ι))

theorem physical_exists_exactMinimizer {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {n : ℕ} (hn : 0 < n) :
    ∃ ρ σ : QMat d n, IsExactMinimizer F ρ σ := by
  obtain ⟨ρ, hρ, σ, hσ, heq⟩ :=
    QuantumProver.QuantumRelativeEntropyContinuity.exists_minimizing_pair_density
      (hF.null_nonempty n hn) (hF.alternative_nonempty n hn)
      (hF.null_compact n hn) (hF.alternative_compact n hn)
      (hF.null_states n hn) (hF.alternative_positive n hn)
  refine ⟨ρ, σ, hρ, hσ, ?_⟩
  simpa only [setUmegaki, umegaki_eq_shared_relativeEntropyBits] using heq

theorem physical_exactMinimizer_support_finite {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {ρ σ : QMat d n}
    (hmin : IsExactMinimizer F ρ σ) :
    SupportLE ρ σ ∧ umegaki ρ σ ≠ ⊤ ∧ umegaki ρ σ ≠ ⊥ ∧
      umegakiReal ρ σ = (setUmegaki F n).toReal := by
  have hs := physical_pair_supportLE hF hn hmin.1 hmin.2.1
  have hf := physical_pair_umegaki_finite hF hn hmin.1 hmin.2.1
  refine ⟨hs, hf.1, hf.2, ?_⟩
  have h := congrArg EReal.toReal hmin.2.2
  simpa only [umegaki_of_support hs, EReal.toReal_coe] using h

theorem physical_pair_sandwiched_finite {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {ρ σ : QMat d n}
    (hρ : ρ ∈ F.null n) (hσ : σ ∈ F.alternative n)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    sandwichedDivergence ρ σ α ≠ ⊤ ∧ sandwichedDivergence ρ σ α ≠ ⊥ := by
  obtain ⟨C, hC⟩ := hF.linear_growth
  have hp := Testing.sandwichedTrace_pos_of_domination
    (hF.null_states n hn ρ hρ) (hF.alternative_positive n hn σ hσ)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (C * (n : ℝ)))
    (hC n hn ρ hρ σ hσ).1 hα hα1
  have he : sandwichedDivergence ρ σ α =
      ((logTwo (sandwichedTrace ρ σ α) / (α - 1) : ℝ) : EReal) := by
    simp [sandwichedDivergence, hα1.ne, not_lt.mpr hα1.le, hp.ne']
    rw [← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_div]
  rw [he]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

theorem physical_setMeasuredDivergence_le_supremum {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    setMeasuredDivergence F n α ≤ ((n : ℝ) * measuredRateSupremum F α : EReal) := by
  have hf := physical_setMeasuredDivergence_finite hF hn hα hα1
  rw [← EReal.coe_toReal hf.1 hf.2]
  apply EReal.coe_le_coe
  have h := physical_measured_block_le_supremum hF hn hα hα1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  simpa only [mul_comm] using (div_le_iff₀ hnR).mp h

theorem physical_exists_symmetric_sandwich_near_measured_supremum
    {d n : ℕ} {F : QuantumFamilies d} (hF : PhysicalAssumptions F) (hn : 0 < n)
    {α η : ℝ} (hα : 0 < α) (hα1 : α < 1) (hη : 0 < η) :
    ∃ ρ σ : QMat d n, ρ ∈ F.null n ∧ σ ∈ F.alternative n ∧
      σ ∈ PermutationSpectrum.invariantMatrices d n ∧
      (sandwichedDivergence ρ σ α).toReal <
        (n : ℝ) * measuredRateSupremum F α + pinchingOverhead d n + η := by
  have hset : setMeasuredDivergence F n α <
      (((n : ℝ) * measuredRateSupremum F α + η : ℝ) : EReal) :=
    (physical_setMeasuredDivergence_le_supremum hF hn hα hα1).trans_lt
      (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right _ hη))
  unfold setMeasuredDivergence at hset
  obtain ⟨z, ⟨ρ, hρ, σ, hσ, rfl⟩, hpair⟩ := sInf_lt_iff.mp hset
  let ρ' := PermutationSpectrum.siteAverage ρ
  let σ' := PermutationSpectrum.siteAverage σ
  have hr := PermutationSpectrum.siteAverage_mem_null hF hn hρ
  have hs := PermutationSpectrum.siteAverage_mem_alternative hF hn hσ
  have hi := PermutationSpectrum.siteAverage_invariant σ
  obtain ⟨C, hC⟩ := hF.linear_growth
  have hm := Testing.measuredDivergence_finite_of_domination
    (hF.null_states n hn ρ hρ) (hF.alternative_positive n hn σ hσ)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (C * (n : ℝ)))
    (hC n hn ρ hρ σ hσ).1 hα hα1
  have hM : (measuredDivergence ρ σ α).toReal <
      (n : ℝ) * measuredRateSupremum F α + η := by
    rw [← EReal.coe_toReal hm.1 hm.2] at hpair
    exact EReal.coe_lt_coe_iff.mp hpair
  have hp := PermutationSpectrum.physical_pair_sandwich_sub_polynomialLog_le_measured
    hF hn hr hs hi hα hα1
  have hg : (((d : ℝ) ^ 2 * blockLog n : ℝ) : EReal) ≤
      (pinchingOverhead d n : EReal) := EReal.coe_le_coe
    (PermutationSpectrum.polynomialLog_le_pinchingOverhead
      (PermutationMeasured.physical_dimension_pos hF hn))
  have hb : sandwichedDivergence ρ' σ' α - (pinchingOverhead d n : EReal) ≤
      measuredDivergence ρ σ α :=
    (EReal.sub_le_sub (le_refl _) hg).trans
      (hp.trans (PermutationMeasured.measuredDivergence_siteAverage_le ρ σ α))
  have hf := physical_pair_sandwiched_finite hF hn hr hs hα hα1
  have hbR : (sandwichedDivergence ρ' σ' α).toReal - pinchingOverhead d n ≤
      (measuredDivergence ρ σ α).toReal := by
    rw [← EReal.coe_toReal hf.1 hf.2, ← EReal.coe_toReal hm.1 hm.2,
      ← EReal.coe_sub] at hb
    exact EReal.coe_le_coe_iff.mp hb
  refine ⟨ρ', σ', hr, hs, hi, ?_⟩
  linarith

theorem physical_setSandwichedDivergence_ne_top {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) : setSandwichedDivergence F n α ≠ ⊤ := by
  obtain ⟨ρ, hρ⟩ := hF.null_nonempty n hn
  obtain ⟨σ, hσ⟩ := hF.alternative_nonempty n hn
  have hle : setSandwichedDivergence F n α ≤ sandwichedDivergence ρ σ α :=
    sInf_le ⟨ρ, hρ, σ, hσ, rfl⟩
  intro ht
  have hp : sandwichedDivergence ρ σ α = ⊤ :=
    le_antisymm le_top (by simpa only [ht] using hle)
  exact (physical_pair_sandwiched_finite hF hn hρ hσ hα hα1).1 hp

theorem classicalUmegaki_measurement_le_log_of_domination
    {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (M : FinitePOVM ι L) {ρ σ : CMat ι} (hρ : IsState ρ)
    (hσ : σ.PosSemidef) {a : ℝ} (ha : 0 < a)
    (hdom : LoewnerLE ρ ((a : ℂ) • σ)) :
    classicalUmegaki (measurementMass M ρ) (measurementMass M σ) ≤
      (logTwo a : EReal) := by
  classical
  have hsup := PinchingUmegaki.classicalSupportLE_measurement_of_domination M hρ.1 hdom
  rw [classicalUmegaki, if_pos hsup]
  apply EReal.coe_le_coe
  have hterm (i : Fin L) : measurementMass M ρ i *
      (logTwo (measurementMass M ρ i) - logTwo (measurementMass M σ i)) ≤
        measurementMass M ρ i * logTwo a := by
    have hp := Testing.measurementMass_nonneg M hρ.1 i
    have hq := Testing.measurementMass_nonneg M hσ i
    have hd := Testing.measurementMass_domination M hdom i
    by_cases hp0 : measurementMass M ρ i = 0
    · simp only [hp0, zero_mul, le_refl]
    have hp' : 0 < measurementMass M ρ i := lt_of_le_of_ne hp (Ne.symm hp0)
    have hq' : 0 < measurementMass M σ i := by
      by_contra hh
      have hzero := le_antisymm (not_lt.mp hh) hq
      rw [hzero, mul_zero] at hd
      linarith
    have hlog := Testing.logTwo_mono_pos hp' hd
    rw [Testing.logTwo_mul_pos ha hq'] at hlog
    exact mul_le_mul_of_nonneg_left (by linarith) hp
  calc
    _ ≤ ∑ i, measurementMass M ρ i * logTwo a :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = logTwo a := by rw [← Finset.sum_mul, Testing.measurementMass_sum M hρ, one_mul]

theorem measuredDivergence_one_le_log_of_domination
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ σ : CMat ι}
    (hρ : IsState ρ) (hσ : σ.PosSemidef) {a : ℝ} (ha : 0 < a)
    (hdom : LoewnerLE ρ ((a : ℂ) • σ)) :
    measuredDivergence ρ σ 1 ≤ (logTwo a : EReal) := by
  unfold measuredDivergence
  apply sSup_le
  rintro z ⟨L, M, rfl⟩
  simpa [classicalRenyiDivergence] using
    classicalUmegaki_measurement_le_log_of_domination M hρ hσ ha hdom

theorem physical_linear_setMeasuredDivergence_one_bounds {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      ((-C * (n : ℝ) : ℝ) : EReal) ≤ setMeasuredDivergence F n 1 ∧
        setMeasuredDivergence F n 1 ≤ ((C * (n : ℝ) : ℝ) : EReal) := by
  obtain ⟨C, hC, hgrowth⟩ := physical_linear_growth_nonneg hF
  have hp : ∀ n : ℕ, 0 < n → ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n,
      ((-C * (n : ℝ) : ℝ) : EReal) ≤ measuredDivergence ρ σ 1 ∧
        measuredDivergence ρ σ 1 ≤ ((C * (n : ℝ) : ℝ) : EReal) := by
    intro n hn ρ hρ σ hσ
    have hr := hF.null_states n hn ρ hρ
    have hs := hF.alternative_positive n hn σ hσ
    obtain ⟨hd, hl⟩ := hgrowth n hn ρ hρ σ hσ
    have ha : 0 < Real.rpow 2 (C * (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    constructor
    · have hb := Testing.measuredDivergence_ge_neg_log_trace_of_domination hr ha hd 1
      exact (EReal.coe_le_coe (by simpa only [neg_mul] using neg_le_neg hl)).trans hb
    · simpa only [converse_logTwo_two_rpow] using
        measuredDivergence_one_le_log_of_domination hr hs ha hd
  refine ⟨C, hC, ?_⟩
  intro n hn
  constructor
  · unfold setMeasuredDivergence
    apply le_sInf
    rintro z ⟨ρ, hρ, σ, hσ, rfl⟩
    exact (hp n hn ρ hρ σ hσ).1
  · obtain ⟨ρ, hρ⟩ := hF.null_nonempty n hn
    obtain ⟨σ, hσ⟩ := hF.alternative_nonempty n hn
    have hset : setMeasuredDivergence F n 1 ≤ measuredDivergence ρ σ 1 :=
      sInf_le ⟨ρ, hρ, σ, hσ, rfl⟩
    exact hset.trans (hp n hn ρ hρ σ hσ).2

theorem physical_setMeasuredDivergence_one_finite {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) :
    setMeasuredDivergence F n 1 ≠ ⊤ ∧ setMeasuredDivergence F n 1 ≠ ⊥ := by
  obtain ⟨C, _, hb⟩ := physical_linear_setMeasuredDivergence_one_bounds hF
  constructor
  · intro ht
    have h := (hb n hn).2
    rw [ht] at h
    exact EReal.coe_ne_top _ (le_antisymm le_top h)
  · intro hb0
    have h := (hb n hn).1
    rw [hb0] at h
    exact EReal.coe_ne_bot _ (le_antisymm h bot_le)

theorem physical_setUmegaki_one_pinching_real {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) :
    (setUmegaki F n).toReal - pinchingOverhead d n ≤
      (setMeasuredDivergence F n 1).toReal := by
  have hu := physical_setUmegaki_finite hF hn
  have hm := physical_setMeasuredDivergence_one_finite hF hn
  have hg := PinchingUmegaki.physical_set_umegaki_sub_pinchingOverhead_le_measured hF hn
  rw [← EReal.coe_toReal hu.1 hu.2, ← EReal.coe_toReal hm.1 hm.2,
    ← EReal.coe_sub] at hg
  exact EReal.coe_le_coe_iff.mp hg

theorem physical_fixed_scale_ns_moment_conversion {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {A zeta : ℝ} (hA : 0 ≤ A) (hzeta : 0 < zeta) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ (n : ℕ) (hn : 0 < n), N ≤ n →
        ∀ (ρ : QMat d n) (hρ : ρ ∈ F.null n) (σ : QMat d n) (hσ : σ ∈ F.alternative n),
        ∀ t : ℝ, 0 ≤ t → t ≤ c / (n : ℝ) →
        (nsLaw ρ σ (hF.null_states n hn ρ hρ)
          (hF.alternative_positive n hn σ hσ)).expect
          (fun z => Real.exp (-(zeta / (n : ℝ)) *
            (nsLikelihood ρ σ z - (n : ℝ) * regularizedRate F))) ≤
              Real.exp (A * (blockLog n) ^ 3 / (n : ℝ)) →
        nsWeightedMoment ρ σ ((n : ℝ) * regularizedRate F) t ≤
          K * ((n : ℝ) * (umegakiReal ρ σ - (n : ℝ) * regularizedRate F) +
            (n : ℝ) * (blockLog n) ^ 3) := by
  obtain ⟨C, hC, hr, hgrowth⟩ := physical_fixed_growth_entropy_rate_bounds hF
  obtain ⟨c, K, hc, hK, N, hN1, hmoment⟩ :=
    EndpointMoment.wider_ns_moment_of_logarithmic_laplace hC hA hzeta
  refine ⟨c, K, hc, hK, N, hN1, ?_⟩
  intro n hnp hn ρ hρ σ hσ t ht hwindow hlap
  have hdom : LoewnerLE ρ (Real.rpow 2 (C * (n : ℝ)) • σ) := by
    simpa only [complex_real_smul] using (hgrowth n hnp ρ hρ σ hσ).1
  have hcenter : -(C * (n : ℝ)) ≤ (n : ℝ) * regularizedRate F := by
    have hlo : -C ≤ regularizedRate F := (neg_le_neg hr).trans (neg_abs_le _)
    nlinarith [mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg n)]
  exact hmoment n hn ρ σ (hF.null_states n hnp ρ hρ)
    (hF.alternative_positive n hnp σ hσ) ((n : ℝ) * regularizedRate F) t
    hdom hcenter (physical_pair_mean_surplus_nonneg hF hnp hρ hσ)
    ht hwindow hlap

theorem physical_measuredEntropyRates_one_bounded {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : ∃ C : ℝ, 0 ≤ C ∧
      BddBelow (measuredEntropyRates F 1) ∧ BddAbove (measuredEntropyRates F 1) ∧
        |measuredRateSupremum F 1| ≤ C := by
  obtain ⟨C, hC, hb⟩ := physical_linear_setMeasuredDivergence_one_bounds hF
  have hnorm : ∀ x ∈ measuredEntropyRates F 1, -C ≤ x ∧ x ≤ C := by
    rintro x ⟨n, hn, rfl⟩
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hf := physical_setMeasuredDivergence_one_finite hF hn
    have hl : -C * (n : ℝ) ≤ (setMeasuredDivergence F n 1).toReal := by
      simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal
        (hb n hn).1 (EReal.coe_ne_bot _) hf.1
    have hu : (setMeasuredDivergence F n 1).toReal ≤ C * (n : ℝ) := by
      simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal
        (hb n hn).2 hf.2 (EReal.coe_ne_top _)
    exact ⟨(le_div_iff₀ hnR).mpr hl, (div_le_iff₀ hnR).mpr hu⟩
  have hlo : BddBelow (measuredEntropyRates F 1) := ⟨-C, fun x hx => (hnorm x hx).1⟩
  have hhi : BddAbove (measuredEntropyRates F 1) := ⟨C, fun x hx => (hnorm x hx).2⟩
  obtain ⟨x, hx⟩ := measuredEntropyRates_nonempty F 1
  have hslo : -C ≤ measuredRateSupremum F 1 := (hnorm x hx).1.trans (le_csSup hhi hx)
  have hshi : measuredRateSupremum F 1 ≤ C := csSup_le (measuredEntropyRates_nonempty F 1)
    (fun y hy => (hnorm y hy).2)
  exact ⟨C, hC, hlo, hhi, abs_le.mpr ⟨hslo, hshi⟩⟩

theorem physical_measured_one_block_le_supremum {d n : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) (hn : 0 < n) :
    (setMeasuredDivergence F n 1).toReal / (n : ℝ) ≤ measuredRateSupremum F 1 := by
  obtain ⟨C, _, _, hhi, _⟩ := physical_measuredEntropyRates_one_bounded hF
  exact le_csSup hhi ⟨n, hn, rfl⟩

theorem pinchingOverhead_div_tendsto_zero (d : ℕ) :
    Filter.Tendsto (fun n : ℕ => pinchingOverhead d n / (n : ℝ))
      Filter.atTop (nhds 0) := by
  have hx : Filter.Tendsto (fun n : ℕ => (n : ℝ) + (d : ℝ))
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop (d : ℝ)
      tendsto_natCast_atTop_atTop
  have h := (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (-(d : ℝ)) 1 one_ne_zero).comp hx
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + (d : ℝ)) / (n : ℝ))
      Filter.atTop (nhds 0) := by
    convert h using 1
    funext n
    simp only [Function.comp_apply, pow_one, one_mul, add_neg_cancel_right]
  have hf := (hlog.div_const (Real.log 2)).const_mul (2 * ((d : ℝ) ^ 2 + (d : ℝ)))
  convert hf using 1
  · funext n
    dsimp [pinchingOverhead, logTwo]
    ring
  · simp

theorem physical_regularizedRate_le_measured_one_supremum {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) : regularizedRate F ≤ measuredRateSupremum F 1 := by
  have hl := (physical_actual_full_rate hF).2.sub (pinchingOverhead_div_tendsto_zero d)
  have hlim : Filter.Tendsto (fun n : ℕ => (setUmegaki F n).toReal / (n : ℝ) -
      pinchingOverhead d n / (n : ℝ)) Filter.atTop (nhds (regularizedRate F)) := by
    simpa only [sub_zero] using hl
  apply le_of_tendsto hlim
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : 0 < n := Nat.zero_lt_one.trans_le hn
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hg := div_le_div_of_nonneg_right (physical_setUmegaki_one_pinching_real hF hn0) hnR
  rw [sub_div] at hg
  exact hg.trans (physical_measured_one_block_le_supremum hF hn0)

theorem physical_exactMinimizer_mean_le_actual_rate_residual
    {d n : ℕ} {F : QuantumFamilies d} (hF : PhysicalAssumptions F)
    (hn : 0 < n) {ρ σ : QMat d n} (hmin : IsExactMinimizer F ρ σ) :
    umegakiReal ρ σ - (n : ℝ) * regularizedRate F ≤
      pinchingOverhead d n + (n : ℝ) *
        (measuredRateSupremum F 1 - regularizedRate F) := by
  have he := (physical_exactMinimizer_support_finite hF hn hmin).2.2.2
  have hgap := physical_setUmegaki_one_pinching_real hF hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hb := (div_le_iff₀ hnR).mp (physical_measured_one_block_le_supremum hF hn)
  rw [he]
  nlinarith

theorem physical_all_length_fixed_scale_ns_moment
    {d : ℕ} {F : QuantumFamilies d} (hF : PhysicalAssumptions F)
    {A zeta : ℝ} (hA : 0 ≤ A) (hzeta : 0 < zeta)
    (hLap : ∃ N₀ : ℕ, ∀ (n : ℕ) (hn : 0 < n), N₀ ≤ n →
      ∀ (ρ : QMat d n) (hρ : ρ ∈ F.null n) (σ : QMat d n) (hσ : σ ∈ F.alternative n),
        (nsLaw ρ σ (hF.null_states n hn ρ hρ)
          (hF.alternative_positive n hn σ hσ)).expect
          (fun z => Real.exp (-(zeta / (n : ℝ)) *
            (nsLikelihood ρ σ z - (n : ℝ) * regularizedRate F))) ≤
              Real.exp (A * (blockLog n) ^ 3 / (n : ℝ))) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ n : ℕ, 0 < n →
      ∀ ρ ∈ F.null n, ∀ σ ∈ F.alternative n, ∀ t : ℝ,
        0 ≤ t → t ≤ c / (n : ℝ) →
          nsWeightedMoment ρ σ ((n : ℝ) * regularizedRate F) t ≤
            K * ((n : ℝ) * (umegakiReal ρ σ - (n : ℝ) * regularizedRate F) +
              (n : ℝ) * (blockLog n) ^ 3) := by
  obtain ⟨c₁, K₁, hc₁, hK₁, N₁, hN₁, hconv⟩ :=
    physical_fixed_scale_ns_moment_conversion hF hA hzeta
  obtain ⟨N₀, hLap⟩ := hLap
  let N := max N₀ N₁
  obtain ⟨K₀, c₀, hK₀, hc₀, hbase⟩ := physical_quantum_moment_finite_base hF N
  let c := min c₀ c₁
  let K := K₀ + K₁
  have hc : 0 < c := lt_min hc₀ hc₁
  have hK : 0 < K := by dsimp [K]; linarith
  refine ⟨c, K, hc, hK, ?_⟩
  intro n hn ρ hρ σ hσ t ht hwindow
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmean := physical_pair_mean_surplus_nonneg hF hn hρ hσ
  have hV : 0 ≤ (n : ℝ) * (umegakiReal ρ σ - (n : ℝ) * regularizedRate F) :=
    mul_nonneg hnR hmean
  have hW : 0 ≤ (n : ℝ) * (blockLog n) ^ 3 :=
    mul_nonneg hnR (pow_nonneg (blockLog_nonneg n) _)
  by_cases hlarge : N ≤ n
  · have hn₁ := (le_max_right N₀ N₁).trans hlarge
    have hn₀ := (le_max_left N₀ N₁).trans hlarge
    have ht₁ : t ≤ c₁ / (n : ℝ) := hwindow.trans
      (div_le_div_of_nonneg_right (min_le_right _ _) hnR)
    have hm := hconv n hn hn₁ ρ hρ σ hσ t ht ht₁ (hLap n hn hn₀ ρ hρ σ hσ)
    refine hm.trans ?_
    dsimp [K]
    nlinarith [mul_nonneg hK₀.le (add_nonneg hV hW)]
  · have hnN : n ≤ N := (not_le.mp hlarge).le
    have ht₀ : t ≤ c₀ / (n : ℝ) := hwindow.trans
      (div_le_div_of_nonneg_right (min_le_left _ _) hnR)
    have hm := hbase n hn hnN ρ hρ σ hσ t ht ht₀
    refine hm.trans ?_
    dsimp [K]
    nlinarith [mul_nonneg hK₀.le hV, mul_nonneg hK₁.le (add_nonneg hV hW)]

section MatrixMeasuredBasis

open scoped Kronecker

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem basis_submatrix_inverse (e : κ ≃ ι) (A : CMat ι) :
    (A.submatrix e e).submatrix e.symm e.symm = A := by
  ext i j
  simp [Matrix.submatrix]

theorem basis_tracePair (e : κ ≃ ι) (A B : CMat ι) :
    tracePair (A.submatrix e e) (B.submatrix e e) = tracePair A B := by
  unfold tracePair
  rw [Matrix.submatrix_mul_equiv, trace_submatrix_equiv]

def basisPOVM (e : κ ≃ ι) {L : ℕ} (M : FinitePOVM ι L) : FinitePOVM κ L where
  outcome i := (M.outcome i).submatrix e e
  positive i := (M.positive i).submatrix e
  sum_outcome := by
    change (∑ i, (PermutationSpectrum.reindexStarAlgHom e) (M.outcome i)) = 1
    rw [← map_sum, M.sum_outcome]
    exact (PermutationSpectrum.reindexStarAlgHom e).map_one

theorem basis_measurementMass (e : κ ≃ ι) {L : ℕ} (M : FinitePOVM ι L) (A : CMat ι) :
    measurementMass (basisPOVM e M) (A.submatrix e e) = measurementMass M A := by
  funext i
  exact basis_tracePair e A (M.outcome i)

theorem measuredDivergence_submatrix_le (e : κ ≃ ι) (ρ σ : CMat ι) (α : ℝ) :
    measuredDivergence (ρ.submatrix e e) (σ.submatrix e e) α ≤ measuredDivergence ρ σ α := by
  unfold measuredDivergence
  apply sSup_le
  rintro z ⟨L, M, rfl⟩
  have hρ := basis_measurementMass e.symm M (ρ.submatrix e e)
  have hσ := basis_measurementMass e.symm M (σ.submatrix e e)
  rw [basis_submatrix_inverse] at hρ hσ
  rw [← hρ, ← hσ]
  exact le_sSup ⟨L, basisPOVM e.symm M, rfl⟩

theorem measuredDivergence_submatrix_equiv (e : κ ≃ ι) (ρ σ : CMat ι) (α : ℝ) :
    measuredDivergence (ρ.submatrix e e) (σ.submatrix e e) α = measuredDivergence ρ σ α := by
  apply le_antisymm (measuredDivergence_submatrix_le e ρ σ α)
  have h := measuredDivergence_submatrix_le e.symm (ρ.submatrix e e) (σ.submatrix e e) α
  simpa only [basis_submatrix_inverse] using h

def basisMatrixSet (e : κ ≃ ι) (S : Set (CMat ι)) : Set (CMat κ) :=
  (fun A => A.submatrix e e) '' S

theorem basisMatrixSet_compact (e : κ ≃ ι) {S : Set (CMat ι)} (hS : IsCompact S) :
    IsCompact (basisMatrixSet e S) := by
  apply hS.image
  change Continuous (fun A : CMat ι => A.submatrix e e)
  fun_prop

theorem basisMatrixSet_convex (e : κ ≃ ι) {S : Set (CMat ι)} (hS : Convex ℝ S) :
    Convex ℝ (basisMatrixSet e S) := by
  exact hS.linear_image (Matrix.reindexLinearEquiv ℝ ℂ e.symm e.symm).toLinearMap

theorem basis_isState (e : κ ≃ ι) {ρ : CMat ι} (hρ : IsState ρ) :
    IsState (ρ.submatrix e e) :=
  ⟨hρ.1.submatrix e, (trace_submatrix_equiv e ρ).trans hρ.2⟩

theorem positivePolar_basisMatrixSet_iff (e : κ ≃ ι) (S : Set (CMat ι)) (X : CMat κ) :
    X ∈ positivePolar (basisMatrixSet e S) ↔
      X.submatrix e.symm e.symm ∈ positivePolar S := by
  constructor
  · intro hX
    refine ⟨hX.1.submatrix e.symm, ?_⟩
    intro A hA
    have hb := hX.2 (A.submatrix e e) ⟨A, hA, rfl⟩
    have ht := basis_tracePair e.symm (A.submatrix e e) X
    rw [basis_submatrix_inverse] at ht
    rw [ht]
    exact hb
  · intro hX
    have hinv : (X.submatrix e.symm e.symm).submatrix e e = X := by
      ext i j
      simp [Matrix.submatrix]
    refine ⟨?_, ?_⟩
    · simpa only [hinv] using hX.1.submatrix e
    · rintro B ⟨A, hA, rfl⟩
      have ht := basis_tracePair e A (X.submatrix e.symm e.symm)
      rw [hinv] at ht
      rw [ht]
      exact hX.2 A hA

theorem matrixSetMeasuredDivergence_basisMatrixSet (e : κ ≃ ι)
    (S T : Set (CMat ι)) (α : ℝ) :
    PolarTensor.matrixSetMeasuredDivergence (basisMatrixSet e S) (basisMatrixSet e T) α =
      PolarTensor.matrixSetMeasuredDivergence S T α := by
  unfold PolarTensor.matrixSetMeasuredDivergence
  apply congrArg sInf
  ext z
  constructor
  · rintro ⟨ρ, ⟨ρ₀, hρ, rfl⟩, σ, ⟨σ₀, hσ, rfl⟩, hz⟩
    exact ⟨ρ₀, hρ, σ₀, hσ, by simpa only [measuredDivergence_submatrix_equiv] using hz⟩
  · rintro ⟨ρ, hρ, σ, hσ, hz⟩
    refine ⟨ρ.submatrix e e, ⟨ρ, hρ, rfl⟩, σ.submatrix e e, ⟨σ, hσ, rfl⟩, ?_⟩
    simpa only [measuredDivergence_submatrix_equiv] using hz

end MatrixMeasuredBasis

open scoped Kronecker

theorem physical_setMeasuredDivergence_superadditive {d m n : ℕ}
    {F : QuantumFamilies d} (hF : PhysicalAssumptions F) (hm : 0 < m) (hn : 0 < n)
    {α : ℝ} (hα : (1 / 2 : ℝ) ≤ α) (hα1 : α < 1) :
    setMeasuredDivergence F m α + setMeasuredDivergence F n α ≤
      setMeasuredDivergence F (m + n) α := by
  let e := wordSplitEquiv d m n
  let S := basisMatrixSet e.symm (F.null (m + n))
  let T := basisMatrixSet e.symm (F.alternative (m + n))
  have hmn : 0 < m + n := Nat.add_pos_left hm n
  have hSs : ∀ ρ ∈ S, IsState ρ := by
    rintro ρ ⟨ρ₀, hρ, rfl⟩
    exact basis_isState e.symm (hF.null_states _ hmn ρ₀ hρ)
  have hTp : ∀ σ ∈ T, σ.PosSemidef := by
    rintro σ ⟨σ₀, hσ, rfl⟩
    exact (hF.alternative_positive _ hmn σ₀ hσ).submatrix e.symm
  have hSpolar : ∀ X ∈ positivePolar (F.null m), ∀ Y ∈ positivePolar (F.null n),
      X ⊗ₖ Y ∈ positivePolar S := by
    intro X hX Y hY
    apply (positivePolar_basisMatrixSet_iff e.symm _ _).mpr
    exact hF.null_polar_tensor m n hm hn X hX Y hY
  have hTpolar : ∀ X ∈ positivePolar (F.alternative m), ∀ Y ∈ positivePolar (F.alternative n),
      X ⊗ₖ Y ∈ positivePolar T := by
    intro X hX Y hY
    apply (positivePolar_basisMatrixSet_iff e.symm _ _).mpr
    exact hF.alternative_polar_tensor m n hm hn X hX Y hY
  have hs := PolarTensor.matrixSetMeasuredDivergence_tensor_superadditive
    (F.null m) (F.alternative m) (F.null n) (F.alternative n) S T
    (hF.null_nonempty m hm) (hF.null_nonempty n hn) ((hF.null_nonempty _ hmn).image _)
    (hF.alternative_nonempty m hm) (hF.alternative_nonempty n hn)
    ((hF.alternative_nonempty _ hmn).image _)
    (hF.null_compact m hm) (hF.null_compact n hn)
    (basisMatrixSet_compact e.symm (hF.null_compact _ hmn))
    (hF.alternative_compact m hm) (hF.alternative_compact n hn)
    (basisMatrixSet_compact e.symm (hF.alternative_compact _ hmn))
    (hF.null_convex m hm) (hF.null_convex n hn)
    (basisMatrixSet_convex e.symm (hF.null_convex _ hmn))
    (hF.alternative_convex m hm) (hF.alternative_convex n hn)
    (basisMatrixSet_convex e.symm (hF.alternative_convex _ hmn))
    (hF.null_states m hm) (hF.null_states n hn) hSs
    (hF.alternative_positive m hm) (hF.alternative_positive n hn) hTp
    hSpolar hTpolar hα hα1
    (fun A hA B hB => matrixRpow_kronecker hA.posSemidef hB.posSemidef _)
  rw [matrixSetMeasuredDivergence_basisMatrixSet] at hs
  exact hs

namespace ScalarRate

theorem matrix_superadditive_full_limit (u : ℕ → ℝ)
    (hsuper : ∀ m n : ℕ, 0 < m → 0 < n → u m + u n ≤ u (m + n))
    {C : ℝ} (hC : 0 ≤ C) (hupper : ∀ n : ℕ, 0 < n → u n ≤ C * (n : ℝ)) :
    Filter.Tendsto (fun n => u n / (n : ℝ)) Filter.atTop (nhds (supRate u)) := by
  have hsub : ∀ m n : ℕ, 0 < m → 0 < n →
      -u (m + n) ≤ -u m + -u n := by
    intro m n hm hn
    linarith [hsuper m n hm hn]
  have hlower : ∀ n : ℕ, 0 < n → -C * (n : ℝ) ≤ -u n := by
    intro n hn
    linarith [hupper n hn]
  have hhi : BddAbove (rateSet u) := by
    refine ⟨C, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    exact (div_le_iff₀ (by exact_mod_cast hn : 0 < (n : ℝ))).mpr (hupper n hn)
  have hlo : BddBelow (rateSet (fun n => -u n)) := by
    refine ⟨-C, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    exact (le_div_iff₀ (by exact_mod_cast hn : 0 < (n : ℝ))).mpr (hlower n hn)
  have hneg : infRate (fun n => -u n) = -supRate u := by
    apply le_antisymm
    · have hsup : supRate u ≤ -infRate (fun n => -u n) := by
        apply csSup_le (rateSet_nonempty u)
        rintro x ⟨n, hn, rfl⟩
        have hi : infRate (fun n => -u n) ≤ -u n / (n : ℝ) :=
          csInf_le hlo ⟨n, hn, rfl⟩
        rw [neg_div] at hi
        linarith
      linarith
    · apply le_csInf (rateSet_nonempty (fun n => -u n))
      rintro x ⟨n, hn, rfl⟩
      have hu : u n / (n : ℝ) ≤ supRate u := le_csSup hhi ⟨n, hn, rfl⟩
      simpa only [neg_div] using neg_le_neg hu
  have ht := (subadditive_full_limit (fun n => -u n) hsub hC hlower).neg
  rw [hneg] at ht
  simpa only [neg_div, neg_neg] using ht

end ScalarRate

theorem physical_setMeasuredDivergence_real_superadditive {d m n : ℕ}
    {F : QuantumFamilies d} (hF : PhysicalAssumptions F) (hm : 0 < m) (hn : 0 < n)
    {α : ℝ} (hα : (1 / 2 : ℝ) ≤ α) (hα1 : α < 1) :
    (setMeasuredDivergence F m α).toReal + (setMeasuredDivergence F n α).toReal ≤
      (setMeasuredDivergence F (m + n) α).toReal := by
  have hα0 : 0 < α := by linarith
  have hf₁ := physical_setMeasuredDivergence_finite hF hm hα0 hα1
  have hf₂ := physical_setMeasuredDivergence_finite hF hn hα0 hα1
  have hf₁₂ := physical_setMeasuredDivergence_finite hF (Nat.add_pos_left hm n) hα0 hα1
  have h := physical_setMeasuredDivergence_superadditive hF hm hn hα hα1
  rw [← EReal.coe_toReal hf₁.1 hf₁.2, ← EReal.coe_toReal hf₂.1 hf₂.2,
    ← EReal.coe_toReal hf₁₂.1 hf₁₂.2, ← EReal.coe_add] at h
  exact EReal.coe_le_coe_iff.mp h

theorem physical_actual_measured_full_rate {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) {α : ℝ} (hα : (1 / 2 : ℝ) ≤ α) (hα1 : α < 1) :
    (∀ n : ℕ, 0 < n → setMeasuredDivergence F n α ≠ ⊤ ∧
      setMeasuredDivergence F n α ≠ ⊥) ∧
    Filter.Tendsto (fun n : ℕ => (setMeasuredDivergence F n α).toReal / (n : ℝ))
      Filter.atTop (nhds (measuredRateSupremum F α)) := by
  have hα0 : 0 < α := by linarith
  constructor
  · intro n hn
    exact physical_setMeasuredDivergence_finite hF hn hα0 hα1
  · obtain ⟨C, hC, hb⟩ := physical_linear_setMeasuredDivergence_bounds hF
    apply ScalarRate.matrix_superadditive_full_limit
      (fun n => (setMeasuredDivergence F n α).toReal)
      (fun m n hm hn => physical_setMeasuredDivergence_real_superadditive hF hm hn hα hα1) hC
    intro n hn
    have hf := physical_setMeasuredDivergence_finite hF hn hα0 hα1
    simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal
      (hb n hn α hα0 hα1).2 hf.2 (EReal.coe_ne_top _)

theorem physical_setMeasuredDivergence_one_le_setUmegaki {d n : ℕ}
    {F : QuantumFamilies d} (hF : PhysicalAssumptions F) (hn : 0 < n) :
    setMeasuredDivergence F n 1 ≤ setUmegaki F n := by
  unfold setUmegaki
  apply le_sInf
  rintro z ⟨ρ, hρ, σ, hσ, rfl⟩
  have hi : setMeasuredDivergence F n 1 ≤ measuredDivergence ρ σ 1 :=
    sInf_le ⟨ρ, hρ, σ, hσ, rfl⟩
  exact hi.trans (QuantumProver.PetzMeasurementDPI.measuredDivergence_one_le_umegaki
    (hF.null_states n hn ρ hρ).1 (hF.alternative_positive n hn σ hσ))

theorem physical_actual_measured_one_full_rate {d : ℕ} {F : QuantumFamilies d}
    (hF : PhysicalAssumptions F) :
    (∀ n : ℕ, 0 < n → setMeasuredDivergence F n 1 ≠ ⊤ ∧
      setMeasuredDivergence F n 1 ≠ ⊥) ∧
    Filter.Tendsto (fun n : ℕ => (setMeasuredDivergence F n 1).toReal / (n : ℝ))
      Filter.atTop (nhds (regularizedRate F)) := by
  constructor
  · intro n hn
    exact physical_setMeasuredDivergence_one_finite hF hn
  · have hlow := (physical_actual_full_rate hF).2.sub (pinchingOverhead_div_tendsto_zero d)
    have hlow' : Filter.Tendsto (fun n : ℕ => (setUmegaki F n).toReal / (n : ℝ) -
        pinchingOverhead d n / (n : ℝ)) Filter.atTop (nhds (regularizedRate F)) := by
      simpa only [sub_zero] using hlow
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow' (physical_actual_full_rate hF).2
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
      have hnp : 0 < n := Nat.zero_lt_one.trans_le hn
      have h := div_le_div_of_nonneg_right (physical_setUmegaki_one_pinching_real hF hnp)
        (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
      rwa [sub_div] at h
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
      have hnp : 0 < n := Nat.zero_lt_one.trans_le hn
      have hm := physical_setMeasuredDivergence_one_finite hF hnp
      have hu := physical_setUmegaki_finite hF hnp
      have h := EReal.toReal_le_toReal (physical_setMeasuredDivergence_one_le_setUmegaki hF hnp)
        hm.2 hu.1
      exact div_le_div_of_nonneg_right h (Nat.cast_nonneg n)

def UniversalLogarithmicEndpoint : Prop :=
  ∀ (d : ℕ) (F : QuantumFamilies d), PhysicalAssumptions F →
    FullRateConclusion F ∧ UniversalLogarithmicConclusion F

end QuantumProver.Equipartition.FiniteModel
