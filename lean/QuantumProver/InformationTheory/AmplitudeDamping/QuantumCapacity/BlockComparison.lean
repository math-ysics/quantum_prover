import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.BlockConverse
import QuantumProver.InformationTheory.AmplitudeDamping.QuantumCapacity.ComparisonInequalities

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker

namespace QuantumProver.AmplitudeDamping.FiniteModel

variable {I J O P Z : Type*} [Fintype I] [Fintype J]
  [Fintype O] [Fintype P] [Fintype Z]

def SepPositive (ρ : Matrix (I × J) (I × J) ℂ) : Prop :=
  ∃ (k : ℕ) (A : Fin k → Matrix I I ℂ) (B : Fin k → Matrix J J ℂ),
    (∀ z, (A z).PosSemidef) ∧ (∀ z, (B z).PosSemidef) ∧
      ρ = ∑ z, A z ⊗ₖ B z

omit [Fintype I] [Fintype J] in
theorem sepPositive_finite_products
    (A : Z → Matrix I I ℂ) (B : Z → Matrix J J ℂ)
    (hA : ∀ z, (A z).PosSemidef) (hB : ∀ z, (B z).PosSemidef) :
    SepPositive (∑ z, A z ⊗ₖ B z) := by
  classical
  let e : Fin (Fintype.card Z) ≃ Z := (Fintype.equivFin Z).symm
  refine ⟨Fintype.card Z, A ∘ e, B ∘ e, fun z => hA (e z),
    fun z => hB (e z), ?_⟩
  exact (e.sum_comp (fun z => A z ⊗ₖ B z)).symm

theorem SepPositive.posSemidef {ρ : Matrix (I × J) (I × J) ℂ}
    (hρ : SepPositive ρ) : ρ.PosSemidef := by
  rcases hρ with ⟨k, A, B, hA, hB, rfl⟩
  exact Matrix.posSemidef_sum _ fun z _ => (hA z).kronecker (hB z)

omit [Fintype I] [Fintype J] in
theorem SepPositive.product {A : Matrix I I ℂ} {B : Matrix J J ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : SepPositive (A ⊗ₖ B) := by
  refine ⟨1, fun _ => A, fun _ => B, fun _ => hA, fun _ => hB, ?_⟩
  simp

omit [Fintype I] [Fintype J] in
theorem SepPositive.zero : SepPositive (0 : Matrix (I × J) (I × J) ℂ) := by
  refine ⟨0, fun z => Fin.elim0 z, fun z => Fin.elim0 z,
    fun z => Fin.elim0 z, fun z => Fin.elim0 z, ?_⟩
  simp

omit [Fintype I] [Fintype J] in
theorem SepPositive.smul {ρ : Matrix (I × J) (I × J) ℂ}
    (hρ : SepPositive ρ) {t : ℝ} (ht : 0 ≤ t) : SepPositive (t • ρ) := by
  rcases hρ with ⟨k, A, B, hA, hB, rfl⟩
  refine ⟨k, fun z => t • A z, B, fun z => (hA z).smul ht, hB, ?_⟩
  simp only [Matrix.smul_kronecker, Finset.smul_sum]

omit [Fintype I] [Fintype J] in
theorem SepPositive.sum (ρ : Z → Matrix (I × J) (I × J) ℂ)
    (hρ : ∀ z, SepPositive (ρ z)) : SepPositive (∑ z, ρ z) := by
  classical
  choose k A B hA hB heq using hρ
  have h := sepPositive_finite_products
    (fun z : Σ z : Z, Fin (k z) => A z.1 z.2)
    (fun z : Σ z : Z, Fin (k z) => B z.1 z.2)
    (fun z => hA z.1 z.2) (fun z => hB z.1 z.2)
  simpa only [Fintype.sum_sigma, ← heq] using h

theorem SepPositive.local_conjugation [DecidableEq I] [DecidableEq J]
    {ρ : Matrix (I × J) (I × J) ℂ} (hρ : SepPositive ρ)
    (K : Matrix O I ℂ) (L : Matrix P J ℂ) :
    SepPositive ((K ⊗ₖ L) * ρ * (K ⊗ₖ L)ᴴ) := by
  rcases hρ with ⟨k, A, B, hA, hB, rfl⟩
  refine ⟨k, fun z => K * A z * Kᴴ, fun z => L * B z * Lᴴ,
    fun z => (hA z).mul_mul_conjTranspose_same K,
    fun z => (hB z).mul_mul_conjTranspose_same L, ?_⟩
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_kronecker,
    Matrix.mul_kronecker_mul]

theorem SepPositive.local_kraus [DecidableEq I] [DecidableEq J]
    {ρ : Matrix (I × J) (I × J) ℂ} (hρ : SepPositive ρ)
    (K : Z → Matrix O I ℂ) (L : Z → Matrix P J ℂ) :
    SepPositive (∑ z, (K z ⊗ₖ L z) * ρ * (K z ⊗ₖ L z)ᴴ) :=
  SepPositive.sum _ fun z => hρ.local_conjugation (K z) (L z)

omit [Fintype I] [Fintype J] [Fintype O] [Fintype P] in
theorem SepPositive.submatrix_local_equiv
    {ρ : Matrix (I × J) (I × J) ℂ} (hρ : SepPositive ρ)
    (e : O ≃ I) (f : P ≃ J) :
    SepPositive (ρ.submatrix (e.prodCongr f) (e.prodCongr f)) := by
  rcases hρ with ⟨k, A, B, hA, hB, rfl⟩
  refine ⟨k, fun z => (A z).submatrix e e,
    fun z => (B z).submatrix f f, fun z => (hA z).submatrix e,
    fun z => (hB z).submatrix f, ?_⟩
  ext i j
  simp [Matrix.submatrix_apply, Matrix.sum_apply]

theorem IsSeparable.sepPositive {a b : ℕ} {ρ : BipartiteMatrix a b}
    (hρ : IsSeparable a b ρ) : SepPositive ρ := by
  rcases hρ with ⟨k, t, A, B, ht, hsum, hAB, rfl⟩
  refine ⟨k, fun z => t z • A z, B, fun z => ((hAB z).1.1).smul (ht z),
    fun z => (hAB z).2.1, ?_⟩
  simp only [Matrix.smul_kronecker, Complex.coe_smul]

private theorem positive_trace_eq_ofReal {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    A.trace = (A.trace.re : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm

def normalizeLocalPSD {a : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) :
    Matrix (Fin a) (Fin a) ℂ :=
  if A.trace.re = 0 then maximallyMixed a else A.trace.re⁻¹ • A

theorem normalizeLocalPSD_isDensity {a : ℕ} (ha : 0 < a)
    {A : Matrix (Fin a) (Fin a) ℂ} (hA : A.PosSemidef) :
    IsDensity (normalizeLocalPSD A) := by
  classical
  unfold normalizeLocalPSD
  split_ifs with ht
  · exact maximallyMixed_isDensity ha
  · refine ⟨hA.smul (inv_nonneg.mpr (Complex.nonneg_iff.mp hA.trace_nonneg).1), ?_⟩
    rw [Matrix.trace_smul, positive_trace_eq_ofReal hA]
    simp [Complex.real_smul, ht]

theorem trace_smul_normalizeLocalPSD {a : ℕ}
    {A : Matrix (Fin a) (Fin a) ℂ} (hA : A.PosSemidef) :
    A.trace.re • normalizeLocalPSD A = A := by
  classical
  unfold normalizeLocalPSD
  split_ifs with ht
  · have hzero : A = 0 := hA.trace_eq_zero_iff.mp (by
      rw [positive_trace_eq_ofReal hA, ht]; rfl)
    simp [hzero]
  · rw [smul_smul, mul_inv_cancel₀ ht, one_smul]

theorem SepPositive.isSeparable {a b : ℕ} {ρ : BipartiteMatrix a b}
    (hρ : SepPositive ρ) (htrace : ρ.trace = 1) : IsSeparable a b ρ := by
  have hdensity : IsDensity ρ := ⟨hρ.posSemidef, htrace⟩
  obtain ⟨ha, hb⟩ := hdensity.laboratory_dimensions_pos
  rcases hρ with ⟨k, A, B, hA, hB, heq⟩
  refine ⟨k, fun z => (A z).trace.re * (B z).trace.re,
    fun z => normalizeLocalPSD (A z), fun z => normalizeLocalPSD (B z),
    ?_, ?_, ?_, ?_⟩
  · intro z
    exact mul_nonneg (Complex.nonneg_iff.mp (hA z).trace_nonneg).1
      (Complex.nonneg_iff.mp (hB z).trace_nonneg).1
  · have ht := congrArg Complex.re htrace
    rw [heq, Matrix.trace_sum, Complex.re_sum] at ht
    simpa only [TensorPower.trace_kronecker_re_of_posSemidef (hA _) (hB _),
      Complex.one_re] using ht
  · intro z
    exact ⟨normalizeLocalPSD_isDensity ha (hA z), normalizeLocalPSD_isDensity hb (hB z)⟩
  · rw [heq]
    apply Finset.sum_congr rfl
    intro z hz
    rw [Complex.coe_smul, mul_smul, ← Matrix.kronecker_smul, ← Matrix.smul_kronecker,
      trace_smul_normalizeLocalPSD (hA z), trace_smul_normalizeLocalPSD (hB z)]

theorem isSeparable_iff_sepPositive_trace {a b : ℕ} (ρ : BipartiteMatrix a b) :
    IsSeparable a b ρ ↔ SepPositive ρ ∧ ρ.trace = 1 :=
  ⟨fun h => ⟨h.sepPositive, h.isDensity.2⟩,
    fun h => h.1.isSeparable h.2⟩

theorem IsSeparable.convex_sum {a b : ℕ} (ρ : Z → BipartiteMatrix a b)
    (hρ : ∀ z, IsSeparable a b (ρ z)) (t : Z → ℝ)
    (ht : ∀ z, 0 ≤ t z) (hsum : ∑ z, t z = 1) :
    IsSeparable a b (∑ z, (t z : ℂ) • ρ z) := by
  apply SepPositive.isSeparable
  · apply SepPositive.sum
    intro z
    simpa only [Complex.coe_smul] using (hρ z).sepPositive.smul (ht z)
  · rw [Matrix.trace_sum]
    simp_rw [Matrix.trace_smul, (hρ _).isDensity.2, smul_eq_mul, mul_one]
    simpa using congrArg Complex.ofReal hsum

theorem IsSeparable.local_kraus_of_trace {a b ao bo : ℕ}
    {ρ : BipartiteMatrix a b} (hρ : IsSeparable a b ρ)
    (K : Z → Matrix (Fin ao) (Fin a) ℂ)
    (L : Z → Matrix (Fin bo) (Fin b) ℂ)
    (htrace : (∑ z, (K z ⊗ₖ L z) * ρ * (K z ⊗ₖ L z)ᴴ).trace = 1) :
    IsSeparable ao bo (∑ z, (K z ⊗ₖ L z) * ρ * (K z ⊗ₖ L z)ᴴ) :=
  (hρ.sepPositive.local_kraus K L).isSeparable htrace

theorem IsSeparable.alice_instrument {a b ao k : ℕ}
    {ρ : BipartiteMatrix a b} (hρ : IsSeparable a b ρ)
    (K : KrausInstrument a ao k) :
    IsSeparable ao b (∑ z, aliceOperator (b := b) (K.operator z) * ρ *
      (aliceOperator (b := b) (K.operator z))ᴴ) := by
  apply hρ.local_kraus_of_trace K.operator (fun _ => 1)
  simpa only [aliceOperator] using
    (krausSum_trace _ (aliceOperator_gram (b := b) K) ρ).trans hρ.isDensity.2

theorem IsSeparable.bob_instrument {a b bo k : ℕ}
    {ρ : BipartiteMatrix a b} (hρ : IsSeparable a b ρ)
    (K : KrausInstrument b bo k) :
    IsSeparable a bo (∑ z, bobOperator (a := a) (K.operator z) * ρ *
      (bobOperator (a := a) (K.operator z))ᴴ) := by
  apply hρ.local_kraus_of_trace (fun _ => 1) K.operator
  simpa only [bobOperator] using
    (krausSum_trace _ (bobOperator_gram (a := a) K) ρ).trans hρ.isDensity.2

theorem SepPositive.normalize_of_trace_pos {a b : ℕ} {ρ : BipartiteMatrix a b}
    (hρ : SepPositive ρ) (ht : 0 < ρ.trace.re) :
    IsSeparable a b (ρ.trace.re⁻¹ • ρ) := by
  apply (hρ.smul (inv_nonneg.mpr ht.le)).isSeparable
  rw [Matrix.trace_smul, positive_trace_eq_ofReal hρ.posSemidef]
  simp [Complex.real_smul, ht.ne']

theorem FiniteProtocol.output_sepPositive_of_calls_zero {p : ℝ} {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) : P.calls = 0 →
    ∀ ρ : BipartiteMatrix a b, SepPositive ρ → SepPositive (P.output ρ) := by
  induction P with
  | done a b => intro _ ρ hρ; exact hρ
  | @alice a b ao af bf k K next ih =>
    intro hc ρ hρ
    change SepPositive (∑ z, (next z).output
      (aliceOperator (b := b) (K.operator z) * ρ *
        (aliceOperator (b := b) (K.operator z))ᴴ))
    apply SepPositive.sum
    intro z
    have hn : (next z).calls = 0 := Nat.le_zero.mp
      ((Finset.le_sup (Finset.mem_univ z)).trans (le_of_eq hc))
    exact ih z hn _ (hρ.local_conjugation (K.operator z) 1)
  | @bob a b bo af bf k K next ih =>
    intro hc ρ hρ
    change SepPositive (∑ z, (next z).output
      (bobOperator (a := a) (K.operator z) * ρ *
        (bobOperator (a := a) (K.operator z))ᴴ))
    apply SepPositive.sum
    intro z
    have hn : (next z).calls = 0 := Nat.le_zero.mp
      ((Finset.le_sup (Finset.mem_univ z)).trans (le_of_eq hc))
    exact ih z hn _ (hρ.local_conjugation 1 (K.operator z))
  | call next ih =>
    intro hc
    change next.calls + 1 = 0 at hc
    omega

theorem FiniteProtocol.output_isSeparable_of_calls_zero {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {a b af bf : ℕ}
    (P : FiniteProtocol p a b af bf) (hc : P.calls = 0)
    {ρ : BipartiteMatrix a b} (hρ : IsSeparable a b ρ) :
    IsSeparable af bf (P.output ρ) :=
  (P.output_sepPositive_of_calls_zero hc ρ hρ.sepPositive).isSeparable
    ((P.output_trace hp0 hp1 ρ).trans hρ.isDensity.2)

section MeasurePrepare

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B] [DecidableEq I] [DecidableEq O]

def portMeasurementBra (χ : I → ℂ) : Matrix A (A × I) ℂ :=
  fun a x => (1 : Matrix A A ℂ) a x.1 * star (χ x.2)

def portPreparation (v : O → ℂ) : Matrix (O × B) B ℂ :=
  fun x b => v x.1 * (1 : Matrix B B ℂ) x.2 b

def measurePrepareTransferKraus (χ : Z → I → ℂ) (v : Z → O → ℂ) :
    Z → Matrix (A × (O × B)) ((A × I) × B) ℂ :=
  fun z => portMeasurementBra (A := A) (χ z) ⊗ₖ portPreparation (B := B) (v z)

omit [Fintype I] [Fintype O] [Fintype Z] [DecidableEq I] [DecidableEq O] in
theorem measurePrepareTransferKraus_eq_reference (χ : Z → I → ℂ)
    (v : Z → O → ℂ) (z : Z) :
    measurePrepareTransferKraus (A := A) (B := B) χ v z =
      (referenceKrausB (fun z => QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus (χ z) (v z))
        (A × B) z).submatrix (outputPortMemoryEquivB O A B) (inputPortMemoryEquivB I A B) := by
  ext ⟨a, o, b⟩ ⟨⟨a', i⟩, b'⟩
  simp [measurePrepareTransferKraus, portMeasurementBra, portPreparation,
    referenceKrausB, QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus,
    Matrix.vecMulVec_apply, Matrix.one_apply,
    inputPortMemoryEquivB, outputPortMemoryEquivB, Prod.mk.injEq, mul_ite, ite_mul]
  by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [ha, hb, mul_comm]

theorem measurePrepareTransfer_output_eq_reference (χ : Z → I → ℂ)
    (v : Z → O → ℂ) (ρ : Matrix ((A × I) × B) ((A × I) × B) ℂ) :
    krausSumB (measurePrepareTransferKraus χ v) ρ =
      (krausSumB (referenceKrausB
        (fun z => QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus (χ z) (v z)) (A × B))
        (ρ.submatrix (inputPortMemoryEquivB I A B).symm
          (inputPortMemoryEquivB I A B).symm)).submatrix
            (outputPortMemoryEquivB O A B) (outputPortMemoryEquivB O A B) := by
  have hfamily : measurePrepareTransferKraus (A := A) (B := B) χ v =
      fun z => (referenceKrausB
        (fun z => QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus (χ z) (v z)) (A × B) z).submatrix
          (outputPortMemoryEquivB O A B) (inputPortMemoryEquivB I A B) :=
    funext (measurePrepareTransferKraus_eq_reference χ v)
  rw [hfamily]
  simpa only [Matrix.submatrix_submatrix, Equiv.symm_comp_self,
    Matrix.submatrix_id_id, Equiv.refl_apply] using
    krausSumB_submatrix_equiv (inputPortMemoryEquivB I A B)
      (outputPortMemoryEquivB O A B) (Equiv.refl Z)
      (referenceKrausB
        (fun z => QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus (χ z) (v z)) (A × B))
      (ρ.submatrix (inputPortMemoryEquivB I A B).symm
        (inputPortMemoryEquivB I A B).symm)

private theorem trace_submatrix_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (M : Matrix X X ℂ) (e : Y ≃ X) : (M.submatrix e e).trace = M.trace :=
  e.sum_comp (fun x => M x x)

theorem measurePrepareTransferKraus_complete (χ : Z → I → ℂ) (v : Z → O → ℂ)
    (hχ : ∑ z, Matrix.vecMulVec (χ z) (star (χ z)) = 1)
    (hv : ∀ z, ∑ o, star (v z o) * v z o = 1) :
    ∑ z, (measurePrepareTransferKraus (A := A) (B := B) χ v z)ᴴ *
      measurePrepareTransferKraus χ v z = 1 := by
  apply krausSumB_complete_of_trace
  intro ρ
  rw [measurePrepareTransfer_output_eq_reference, trace_submatrix_equiv,
    krausSumB_trace_preserving _ (referenceKrausB_complete _
      (QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus_complete χ v hχ hv) (A × B)),
    trace_submatrix_equiv]

omit [DecidableEq O] in
theorem SepPositive.measurePrepareTransfer
    {ρ : Matrix ((A × I) × B) ((A × I) × B) ℂ} (hρ : SepPositive ρ)
    (χ : Z → I → ℂ) (v : Z → O → ℂ) :
    SepPositive (krausSumB (measurePrepareTransferKraus χ v) ρ) :=
  hρ.local_kraus (fun z => portMeasurementBra (χ z)) (fun z => portPreparation (v z))

theorem measurePrepareTransfer_isDensity
    {ρ : Matrix ((A × I) × B) ((A × I) × B) ℂ} (hρ : IsDensity ρ)
    (χ : Z → I → ℂ) (v : Z → O → ℂ)
    (hχ : ∑ z, Matrix.vecMulVec (χ z) (star (χ z)) = 1)
    (hv : ∀ z, ∑ o, star (v z o) * v z o = 1) :
    IsDensity (krausSumB (measurePrepareTransferKraus χ v) ρ) := by
  refine ⟨krausSumB_posSemidef _ hρ.1, ?_⟩
  rw [krausSumB_trace_preserving _ (measurePrepareTransferKraus_complete χ v hχ hv), hρ.2]

theorem measurePrepareTransfer_isSeparable
    {ρ : Matrix ((A × I) × B) ((A × I) × B) ℂ}
    (hρ : SepPositive ρ) (htrace : ρ.trace = 1)
    (χ : Z → I → ℂ) (v : Z → O → ℂ)
    (hχ : ∑ z, Matrix.vecMulVec (χ z) (star (χ z)) = 1)
    (hv : ∀ z, ∑ o, star (v z o) * v z o = 1) :
    IsSeparable (Fintype.card A) (Fintype.card (O × B))
      ((krausSumB (measurePrepareTransferKraus χ v) ρ).submatrix
        ((finiteIndexB A).prodCongr (finiteIndexB (O × B)))
        ((finiteIndexB A).prodCongr (finiteIndexB (O × B)))) := by
  apply ((hρ.measurePrepareTransfer χ v).submatrix_local_equiv
    (finiteIndexB A) (finiteIndexB (O × B))).isSeparable
  exact ((measurePrepareTransfer_isDensity ⟨hρ.posSemidef, htrace⟩ χ v hχ hv).submatrix_equiv
    ((finiteIndexB A).prodCongr (finiteIndexB (O × B)))).2

end MeasurePrepare

theorem measurePhaseChannelB_whole_cut_separable (n w r : ℕ) (hr : r ≤ n)
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {ρ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hρ : SepPositive ρ) (htrace : ρ.trace = 1) :
    IsSeparable (Fintype.card A) (Fintype.card (Finset (Fin n) × B))
      (((krausSumB (referenceKrausB (measurePhaseKrausB n w r) (A × B))
        (ρ.submatrix (inputPortMemoryEquivB (WeightBasisB n w) A B).symm
          (inputPortMemoryEquivB (WeightBasisB n w) A B).symm)).submatrix
            (outputPortMemoryEquivB (Finset (Fin n)) A B)
            (outputPortMemoryEquivB (Finset (Fin n)) A B)).submatrix
              ((finiteIndexB A).prodCongr (finiteIndexB (Finset (Fin n) × B)))
              ((finiteIndexB A).prodCongr (finiteIndexB (Finset (Fin n) × B)))) := by
  classical
  have hfamily : measurePhaseKrausB n w r = fun z =>
      QuantumProver.AmplitudeDamping.SecretKey.KrausAlgebra.rankOneKraus (phaseInputVectorB n w z)
        (phaseOutputVectorB n r z) := funext (measurePhaseKrausB_rankOne n w r)
  rw [hfamily, ← measurePrepareTransfer_output_eq_reference]
  exact measurePrepareTransfer_isSeparable hρ htrace
    (phaseInputVectorB n w) (phaseOutputVectorB n r)
    (phaseInputVectorB_complete n w) (phaseOutputVectorB_normalized n r hr)

theorem sandwichedTrace_zero_input [DecidableEq I] (σ : Matrix I I ℂ)
    {α : ℝ} (hα : 0 < α) : sandwichedTrace α 0 σ = 0 := by
  simp only [sandwichedTrace, Matrix.mul_zero, Matrix.zero_mul,
    CFC.zero_rpow hα.ne', Matrix.trace_zero, Complex.zero_re]

theorem sandwichedTrace_matched_flag_scalars [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α ell u v : ℝ} (hα : 1 ≤ α) (hell : 0 ≤ ell) (hu : 0 ≤ u) (hv : 0 < v) :
    sandwichedTrace α ((ell * u) • ρ) ((ell * v) • σ) =
      ell * u ^ α * v ^ (1 - α) * sandwichedTrace α ρ σ := by
  by_cases hellzero : ell = 0
  · subst ell
    simp only [zero_mul, zero_smul, sandwichedTrace_zero_input _ (by linarith : 0 < α)]
  · have hellpos : 0 < ell := lt_of_le_of_ne hell (Ne.symm hellzero)
    rw [sandwichedTrace_smul_input hρ ((ell * v) • σ) (mul_nonneg hell hu) hα,
      sandwichedTrace_smul_comparison hρ hσ (mul_pos hellpos hv) hα,
      Real.mul_rpow hell hu, Real.mul_rpow hell hv.le]
    have hp : ell ^ α * ell ^ (1 - α) = ell := by
      rw [← Real.rpow_add hellpos]
      simp
    calc
      _ = (ell ^ α * ell ^ (1 - α)) * u ^ α * v ^ (1 - α) *
          sandwichedTrace α ρ σ := by ring
      _ = _ := by rw [hp]

def appendFlagKraus {f a : ℕ} (w : Fin f) : Matrix (Fin (f * a)) (Fin a) ℂ :=
  fun x i => if ((finProdFinEquiv : Fin f × Fin a ≃ Fin (f * a)).symm x).1 = w ∧
    ((finProdFinEquiv : Fin f × Fin a ≃ Fin (f * a)).symm x).2 = i then 1 else 0

theorem appendFlagKraus_complete {f a : ℕ} (w : Fin f) :
    (appendFlagKraus (a := a) w)ᴴ * appendFlagKraus (a := a) w =
      (1 : Matrix (Fin a) (Fin a) ℂ) := by
  classical
  let e : Fin (f * a) ≃ Fin f × Fin a := finProdFinEquiv.symm
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, appendFlagKraus]
  rw [e.sum_comp (fun x => star (if x.1 = w ∧ x.2 = i then (1 : ℂ) else 0) *
    (if x.1 = w ∧ x.2 = j then (1 : ℂ) else 0))]
  simp [Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_and, eq_comm]

def labFlagBlock {f g a b : ℕ} (w : Fin f) (r : Fin g) (ρ : BipartiteMatrix a b) :
    BipartiteMatrix (f * a) (g * b) :=
  (appendFlagKraus (a := a) w ⊗ₖ appendFlagKraus (a := b) r) * ρ *
    (appendFlagKraus (a := a) w ⊗ₖ appendFlagKraus (a := b) r)ᴴ

theorem labFlagBlock_trace {f g a b : ℕ} (w : Fin f) (r : Fin g)
    (ρ : BipartiteMatrix a b) : (labFlagBlock w r ρ).trace = ρ.trace := by
  unfold labFlagBlock
  rw [Matrix.trace_mul_cycle, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, appendFlagKraus_complete,
    appendFlagKraus_complete, Matrix.one_kronecker_one, Matrix.one_mul]

theorem IsSeparable.labFlagBlock {f g a b : ℕ} (w : Fin f) (r : Fin g)
    {ρ : BipartiteMatrix a b} (hρ : IsSeparable a b ρ) :
    IsSeparable (f * a) (g * b) (labFlagBlock w r ρ) :=
  (hρ.sepPositive.local_conjugation (appendFlagKraus w) (appendFlagKraus r)).isSeparable
    ((labFlagBlock_trace w r ρ).trans hρ.isDensity.2)

def labFlagComparator {f g a b : ℕ} (t : Fin f × Fin g → ℝ)
    (σ : Fin f × Fin g → BipartiteMatrix a b) : BipartiteMatrix (f * a) (g * b) :=
  ∑ z, (t z : ℂ) • labFlagBlock z.1 z.2 (σ z)

theorem labFlagComparator_isSeparable {f g a b : ℕ}
    (t : Fin f × Fin g → ℝ) (σ : Fin f × Fin g → BipartiteMatrix a b)
    (ht : ∀ z, 0 ≤ t z) (hsum : ∑ z, t z = 1)
    (hσ : ∀ z, IsSeparable a b (σ z)) :
    IsSeparable (f * a) (g * b) (labFlagComparator t σ) := by
  change IsSeparable (f * a) (g * b)
    (∑ z : Fin f × Fin g, (t z : ℂ) • labFlagBlock z.1 z.2 (σ z))
  exact IsSeparable.convex_sum (Z := Fin f × Fin g)
    (a := f * a) (b := g * b) (fun z => labFlagBlock z.1 z.2 (σ z))
    (fun z => IsSeparable.labFlagBlock (a := a) (b := b) z.1 z.2 (hσ z)) t ht hsum

theorem labFlagComparator_isDensity {f g a b : ℕ}
    (t : Fin f × Fin g → ℝ) (σ : Fin f × Fin g → BipartiteMatrix a b)
    (ht : ∀ z, 0 ≤ t z) (hsum : ∑ z, t z = 1)
    (hσ : ∀ z, IsSeparable a b (σ z)) :
    IsDensity (labFlagComparator t σ) :=
  (labFlagComparator_isSeparable t σ ht hsum hσ).isDensity

end QuantumProver.AmplitudeDamping.FiniteModel

namespace QuantumProver.AmplitudeDamping.FiniteModel

def labFlagEquiv (f g a b : ℕ) :
    (Fin (f * a) × Fin (g * b)) ≃ (Σ _ : Fin f × Fin g, Fin a × Fin b) :=
  (tensorLabEquiv f g a b).trans
    (Equiv.sigmaEquivProd (Fin f × Fin g) (Fin a × Fin b)).symm

theorem labFlagBlock_apply {f g a b : ℕ} (w : Fin f) (r : Fin g)
    (ρ : BipartiteMatrix a b) (x y : Fin (f * a) × Fin (g * b)) :
    labFlagBlock w r ρ x y =
      if (labFlagEquiv f g a b x).1 = (w, r) ∧
          (labFlagEquiv f g a b y).1 = (w, r) then
        ρ (labFlagEquiv f g a b x).2 (labFlagEquiv f g a b y).2 else 0 := by
  classical
  by_cases hxA : x.1.divNat = w <;> by_cases hyA : y.1.divNat = w <;>
    by_cases hxB : x.2.divNat = r <;> by_cases hyB : y.2.divNat = r <;>
    simp [labFlagBlock, appendFlagKraus, labFlagEquiv, tensorLabEquiv,
      Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, hxA, hyA, hxB, hyB,
      ite_mul, apply_ite, Prod.mk.injEq]

theorem labFlagComparator_eq_blockDiagonal' {f g a b : ℕ}
    (t : Fin f × Fin g → ℝ) (σ : Fin f × Fin g → BipartiteMatrix a b) :
    labFlagComparator t σ =
      (Matrix.blockDiagonal' (fun z => (t z : ℂ) • σ z)).submatrix
        (labFlagEquiv f g a b) (labFlagEquiv f g a b) := by
  classical
  ext x y
  let tx := (labFlagEquiv f g a b x).1
  let ty := (labFlagEquiv f g a b y).1
  let ix := (labFlagEquiv f g a b x).2
  let iy := (labFlagEquiv f g a b y).2
  simp only [labFlagComparator, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, labFlagBlock_apply, Matrix.submatrix_apply]
  change (∑ z, (t z : ℂ) * (if tx = z ∧ ty = z then σ z ix iy else 0)) =
    if tx = ty then (t tx : ℂ) * σ tx ix iy else 0
  by_cases h : tx = ty
  · simp [← h, eq_comm, mul_ite]
  · have hz : ∀ z, ¬(tx = z ∧ ty = z) := by
      rintro z ⟨hx, hy⟩
      exact h (hx.trans hy.symm)
    simp [h, hz]

theorem sandwichedTrace_matched_flag_scalars_nonneg {I : Type*}
    [Fintype I] [DecidableEq I] {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    {α ell u v : ℝ} (hα : 1 ≤ α) (hell : 0 ≤ ell) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (hzero : v = 0 → u = 0) :
    sandwichedTrace α ((ell * u) • ρ) ((ell * v) • σ) =
      ell * u ^ α * v ^ (1 - α) * sandwichedTrace α ρ σ := by
  by_cases hvzero : v = 0
  · rw [hzero hvzero]
    simp [sandwichedTrace_zero_input _ (by linarith : 0 < α),
      Real.zero_rpow (by linarith : α ≠ 0)]
  · exact sandwichedTrace_matched_flag_scalars hρ hσ hα hell hu
      (lt_of_le_of_ne hv (Ne.symm hvzero))

theorem labFlagComparator_sandwichedTrace_sum {f g a b : ℕ}
    (u v : Fin f × Fin g → ℝ) (ρ σ : Fin f × Fin g → BipartiteMatrix a b)
    (hu : ∀ z, 0 ≤ u z) (hv : ∀ z, 0 ≤ v z)
    (hρ : ∀ z, (ρ z).PosSemidef) (hσ : ∀ z, (σ z).PosSemidef) (α : ℝ) :
    sandwichedTrace α (labFlagComparator u ρ) (labFlagComparator v σ) =
      ∑ z, sandwichedTrace α ((u z : ℂ) • ρ z) ((v z : ℂ) • σ z) := by
  have hU : ∀ z, ((u z : ℂ) • ρ z).PosSemidef := by
    intro z
    rw [Complex.coe_smul]
    exact (hρ z).smul (hu z)
  have hV : ∀ z, ((v z : ℂ) • σ z).PosSemidef := by
    intro z
    rw [Complex.coe_smul]
    exact (hσ z).smul (hv z)
  rw [labFlagComparator_eq_blockDiagonal', labFlagComparator_eq_blockDiagonal',
    TensorPower.sandwichedTrace_submatrix_equiv
      (FlagPower.posSemidef_blockDiagonal' hU) (FlagPower.posSemidef_blockDiagonal' hV)]
  exact FlagPower.sandwichedTrace_blockDiagonal' hU hV α

theorem labFlagComparator_sandwichedTrace_matched {f g a b : ℕ}
    (ell u v : Fin f × Fin g → ℝ) (ρ σ : Fin f × Fin g → BipartiteMatrix a b)
    (hell : ∀ z, 0 ≤ ell z) (hu : ∀ z, 0 ≤ u z) (hv : ∀ z, 0 ≤ v z)
    (hzero : ∀ z, v z = 0 → u z = 0)
    (hρ : ∀ z, (ρ z).PosSemidef) (hσ : ∀ z, (σ z).PosSemidef)
    {α : ℝ} (hα : 1 ≤ α) :
    sandwichedTrace α (labFlagComparator (fun z => ell z * u z) ρ)
      (labFlagComparator (fun z => ell z * v z) σ) =
      ∑ z, ell z * (u z) ^ α * (v z) ^ (1 - α) * sandwichedTrace α (ρ z) (σ z) := by
  rw [labFlagComparator_sandwichedTrace_sum _ _ _ _
    (fun z => mul_nonneg (hell z) (hu z)) (fun z => mul_nonneg (hell z) (hv z)) hρ hσ]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Complex.coe_smul, Complex.coe_smul]
  exact sandwichedTrace_matched_flag_scalars_nonneg (hρ z) (hσ z) hα
    (hell z) (hu z) (hv z) (hzero z)

theorem labFlagBlock_isDensity {f g a b : ℕ} (w : Fin f) (r : Fin g)
    {ρ : BipartiteMatrix a b} (hρ : IsDensity ρ) :
    IsDensity (labFlagBlock w r ρ) :=
  ⟨hρ.1.mul_mul_conjTranspose_same (appendFlagKraus w ⊗ₖ appendFlagKraus r),
    (labFlagBlock_trace w r ρ).trans hρ.2⟩

theorem labFlagComparator_isDensity_of_density {f g a b : ℕ}
    (t : Fin f × Fin g → ℝ) (ρ : Fin f × Fin g → BipartiteMatrix a b)
    (ht : ∀ z, 0 ≤ t z) (hsum : ∑ z, t z = 1)
    (hρ : ∀ z, IsDensity (ρ z)) : IsDensity (labFlagComparator t ρ) := by
  refine ⟨?_, ?_⟩
  · apply Matrix.posSemidef_sum
    intro z hz
    rw [Complex.coe_smul]
    exact (labFlagBlock_isDensity z.1 z.2 (hρ z)).1.smul (ht z)
  · rw [labFlagComparator, Matrix.trace_sum]
    simp_rw [Matrix.trace_smul, labFlagBlock_trace, (hρ _).2, smul_eq_mul, mul_one]
    simpa using congrArg Complex.ofReal hsum

theorem SupportLE.smul_input {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (h : SupportLE ρ σ) (c : ℝ) : SupportLE (c • ρ) σ := by
  obtain ⟨F, hF⟩ := h.exists_right_factor
  apply supportLE_of_eq_mul (F := c • F)
  rw [hF, Matrix.mul_smul]

theorem labFlagComparator_supportLE {f g a b : ℕ}
    (u v : Fin f × Fin g → ℝ) (ρ σ : Fin f × Fin g → BipartiteMatrix a b)
    (hu : ∀ z, 0 ≤ u z) (hv : ∀ z, 0 ≤ v z)
    (hzero : ∀ z, v z = 0 → u z = 0)
    (hρ : ∀ z, (ρ z).PosSemidef) (hσ : ∀ z, (σ z).PosSemidef)
    (hSupport : ∀ z, u z ≠ 0 → SupportLE (ρ z) (σ z)) :
    SupportLE (labFlagComparator u ρ) (labFlagComparator v σ) := by
  rw [labFlagComparator_eq_blockDiagonal', labFlagComparator_eq_blockDiagonal']
  apply SupportLE.submatrix_equiv
  apply SupportLE.blockDiagonal'
  intro z
  rw [Complex.coe_smul, Complex.coe_smul]
  by_cases huzero : u z = 0
  · rw [huzero, zero_smul]
    exact supportLE_of_eq_mul (F := 0) (by simp)
  by_cases hvzero : v z = 0
  · rw [hvzero, hzero z hvzero, zero_smul, zero_smul]
    exact supportLE_of_eq_mul (F := 0) (by simp)
  · exact (supportLE_smul_comparison_iff ((hρ z).smul (hu z)).1 (hσ z)
      (lt_of_le_of_ne (hv z) (Ne.symm hvzero))).2 ((hSupport z huzero).smul_input (u z))

theorem labFlagComparator_divergence_matched {f g a b : ℕ}
    (ell u v : Fin f × Fin g → ℝ) (ρ σ : Fin f × Fin g → BipartiteMatrix a b)
    (hell : ∀ z, 0 ≤ ell z) (hu : ∀ z, 0 ≤ u z) (hv : ∀ z, 0 ≤ v z)
    (hzero : ∀ z, v z = 0 → u z = 0)
    (hρ : ∀ z, (ρ z).PosSemidef) (hσ : ∀ z, (σ z).PosSemidef)
    (hSupport : ∀ z, u z ≠ 0 → SupportLE (ρ z) (σ z)) {α : ℝ} (hα : 1 ≤ α) :
    sandwichedDivergence α (labFlagComparator (fun z => ell z * u z) ρ)
      (labFlagComparator (fun z => ell z * v z) σ) =
      ((Real.log (∑ z, ell z * (u z) ^ α * (v z) ^ (1 - α) *
          sandwichedTrace α (ρ z) (σ z)) / ((α - 1) * Real.log 2) : ℝ) : EReal) := by
  have hweightzero : ∀ z, ell z * v z = 0 → ell z * u z = 0 := by
    intro z hz
    rcases mul_eq_zero.mp hz with h | h
    · simp [h]
    · simp [hzero z h]
  have hs := labFlagComparator_supportLE (fun z => ell z * u z) (fun z => ell z * v z)
    ρ σ (fun z => mul_nonneg (hell z) (hu z)) (fun z => mul_nonneg (hell z) (hv z))
    hweightzero hρ hσ (fun z hz => hSupport z (mul_ne_zero_iff.mp hz).2)
  simp only [sandwichedDivergence, hs, ↓reduceIte]
  rw [labFlagComparator_sandwichedTrace_matched ell u v ρ σ hell hu hv hzero hρ hσ hα]

end QuantumProver.AmplitudeDamping.FiniteModel

namespace QuantumProver.AmplitudeDamping.FiniteModel

section MatrixSectorComparison

variable {I O Z A B : Type*} [Fintype I] [Fintype O] [Fintype Z]
  [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq O]
  [DecidableEq A] [DecidableEq B]

def labTransferOutputEquiv (O A B : Type*) [Fintype O] [Fintype A] [Fintype B] :
    (Fin (Fintype.card A) × Fin (Fintype.card (O × B))) ≃ (O × (A × B)) :=
  ((finiteIndexB A).prodCongr (finiteIndexB (O × B))).trans
    (outputPortMemoryEquivB O A B)

def labTransferKraus (K : Z → Matrix O I ℂ) :
    Z → Matrix (Fin (Fintype.card A) × Fin (Fintype.card (O × B))) ((A × I) × B) ℂ :=
  fun z => (referenceKrausB K (A × B) z).submatrix
    (labTransferOutputEquiv O A B) (inputPortMemoryEquivB I A B)

def labTransferOutput (K : Z → Matrix O I ℂ)
    (ρ : Matrix ((A × I) × B) ((A × I) × B) ℂ) :
    BipartiteMatrix (Fintype.card A) (Fintype.card (O × B)) :=
  krausSumB (labTransferKraus K) ρ

theorem labTransferOutput_eq_reference (K : Z → Matrix O I ℂ)
    (ρ : Matrix ((A × I) × B) ((A × I) × B) ℂ) :
    labTransferOutput K ρ =
      (krausSumB (referenceKrausB K (A × B))
        (ρ.submatrix (inputPortMemoryEquivB I A B).symm
          (inputPortMemoryEquivB I A B).symm)).submatrix
            (labTransferOutputEquiv O A B) (labTransferOutputEquiv O A B) := by
  unfold labTransferOutput
  change krausSumB (fun z => (referenceKrausB K (A × B) z).submatrix
    (labTransferOutputEquiv O A B) (inputPortMemoryEquivB I A B)) ρ = _
  simpa only [Equiv.refl_apply,
    Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] using
    krausSumB_submatrix_equiv (inputPortMemoryEquivB I A B)
      (labTransferOutputEquiv O A B) (Equiv.refl Z) (referenceKrausB K (A × B))
      (ρ.submatrix (inputPortMemoryEquivB I A B).symm
        (inputPortMemoryEquivB I A B).symm)

theorem labTransferOutput_isDensity (K : Z → Matrix O I ℂ)
    (hK : ∑ z, (K z)ᴴ * K z = 1)
    {ρ : Matrix ((A × I) × B) ((A × I) × B) ℂ} (hρ : IsDensity ρ) :
    IsDensity (labTransferOutput K ρ) := by
  refine ⟨krausSumB_posSemidef _ hρ.1, ?_⟩
  rw [labTransferOutput_eq_reference, trace_submatrix_equiv,
    krausSumB_trace_preserving _ (referenceKrausB_complete K hK (A × B)),
    trace_submatrix_equiv, hρ.2]

omit [DecidableEq O] in
theorem labTransferOutput_supportLE (K : Z → Matrix O I ℂ)
    {ρ σ : Matrix ((A × I) × B) ((A × I) × B) ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hSupport : SupportLE ρ σ) :
    SupportLE (labTransferOutput K ρ) (labTransferOutput K σ) :=
  QuantumProver.SandwichedDPI.supportLE_kraus_sum (labTransferKraus K) hρ hσ hSupport

end MatrixSectorComparison

theorem labTransferOutput_phase_isSeparable (n w r : ℕ) (hrn : r ≤ n)
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hσ : SepPositive σ) (htrace : σ.trace = 1) :
    IsSeparable (Fintype.card A) (Fintype.card (Finset (Fin n) × B))
      (labTransferOutput (measurePhaseKrausB n w r) σ) := by
  rw [labTransferOutput_eq_reference]
  change IsSeparable (Fintype.card A) (Fintype.card (Finset (Fin n) × B))
    (((krausSumB (referenceKrausB (measurePhaseKrausB n w r) (A × B))
      (σ.submatrix (inputPortMemoryEquivB (WeightBasisB n w) A B).symm
        (inputPortMemoryEquivB (WeightBasisB n w) A B).symm)).submatrix
          (outputPortMemoryEquivB (Finset (Fin n)) A B)
          (outputPortMemoryEquivB (Finset (Fin n)) A B)).submatrix
            ((finiteIndexB A).prodCongr (finiteIndexB (Finset (Fin n) × B)))
            ((finiteIndexB A).prodCongr (finiteIndexB (Finset (Fin n) × B))))
  exact measurePhaseChannelB_whole_cut_separable n w r hrn A B hσ htrace

theorem labTransferOutput_loss_phase_domination (n w r : ℕ)
    (hrw : r ≤ w) (hrn : r ≤ n)
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hσ : σ.PosSemidef) :
    labTransferOutput (lossKrausB n w r) σ ≤
      (phaseComparisonConstantB n w r) • labTransferOutput (measurePhaseKrausB n w r) σ := by
  apply Matrix.le_iff.mpr
  have h := measurePhaseChannelB_reference_loss_domination n w r hrw hrn (A × B)
    (hσ.submatrix (inputPortMemoryEquivB (WeightBasisB n w) A B).symm)
  rw [labTransferOutput_eq_reference, labTransferOutput_eq_reference]
  convert h.submatrix (labTransferOutputEquiv (Finset (Fin n)) A B) using 1
  ext x y
  rfl

theorem fixedWeight_entanglement_le_loss_divergence (n w r : ℕ)
    (hrw : r ≤ w) (hrn : r ≤ n)
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {ρ σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hρ : IsDensity ρ) (hσ : SepPositive σ) (htrace : σ.trace = 1)
    (hSupport : SupportLE ρ σ) {α : ℝ} (hα : 1 < α) :
    sandwichedEntanglement α (Fintype.card A) (Fintype.card (Finset (Fin n) × B))
      (labTransferOutput (lossKrausB n w r) ρ) ≤
      sandwichedDivergence α (labTransferOutput (lossKrausB n w r) ρ)
        (labTransferOutput (lossKrausB n w r) σ) +
          (logTwo (phaseComparisonConstantB n w r) : EReal) := by
  have hρN := labTransferOutput_isDensity (lossKrausB n w r) (lossKrausB_complete n w r hrw) hρ
  have hσN := labTransferOutput_isDensity (lossKrausB n w r) (lossKrausB_complete n w r hrw)
    (show IsDensity σ from ⟨hσ.posSemidef, htrace⟩)
  have hσS := labTransferOutput_phase_isSeparable n w r hrn A B hσ htrace
  have hs := labTransferOutput_supportLE (lossKrausB n w r) hρ.1 hσ.posSemidef hSupport
  have horder := labTransferOutput_loss_phase_domination n w r hrw hrn A B hσ.posSemidef
  exact (sandwichedEntanglement_le_comparison
    (labTransferOutput (lossKrausB n w r) ρ) hσS.isDensity hσS α).trans
    (sandwichedDivergence_comparison_order hρN hσN hσS.isDensity hs
      (phaseComparisonConstantB_pos n w r hrw hrn) horder hα)

theorem fixedWeight_sandwichedTrace_phase_le_loss (n w r : ℕ)
    (hrw : r ≤ w) (hrn : r ≤ n)
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {ρ σ : Matrix ((A × WeightBasisB n w) × B) ((A × WeightBasisB n w) × B) ℂ}
    (hρ : IsDensity ρ) (hσ : SepPositive σ) (htrace : σ.trace = 1)
    (hSupport : SupportLE ρ σ) {α : ℝ} (hα : 1 < α) :
    sandwichedTrace α (labTransferOutput (lossKrausB n w r) ρ)
      (labTransferOutput (measurePhaseKrausB n w r) σ) ≤
      (phaseComparisonConstantB n w r) ^ (α - 1) *
        sandwichedTrace α (labTransferOutput (lossKrausB n w r) ρ)
          (labTransferOutput (lossKrausB n w r) σ) := by
  have hρN := labTransferOutput_isDensity (lossKrausB n w r) (lossKrausB_complete n w r hrw) hρ
  have hσN := labTransferOutput_isDensity (lossKrausB n w r) (lossKrausB_complete n w r hrw)
    (show IsDensity σ from ⟨hσ.posSemidef, htrace⟩)
  have hσS := (labTransferOutput_phase_isSeparable n w r hrn A B hσ htrace).isDensity
  have hs := labTransferOutput_supportLE (lossKrausB n w r) hρ.1 hσ.posSemidef hSupport
  have horder := labTransferOutput_loss_phase_domination n w r hrw hrn A B hσ.posSemidef
  have hc := phaseComparisonConstantB_pos n w r hrw hrn
  obtain ⟨ha, hb⟩ := hρN.laboratory_dimensions_pos
  have hQ := sandwichedTrace_antitone_comparison_of_support hρN.1 hσN.1
    (hσS.1.smul hc.le) horder hs ha hb hα.le
  rw [sandwichedTrace_smul_comparison hρN.1 hσS.1 hc hα.le] at hQ
  have hm := mul_le_mul_of_nonneg_left hQ
    (Real.rpow_nonneg hc.le (α - 1))
  have hpow : (phaseComparisonConstantB n w r) ^ (α - 1) *
      (phaseComparisonConstantB n w r) ^ (1 - α) = 1 := by
    rw [← Real.rpow_add hc]
    simp
  rw [← mul_assoc, hpow, one_mul] at hm
  exact hm

theorem SupportLE.trace_re_zero_of_comparison {I : Type*} [Fintype I] [DecidableEq I]
    {ρ σ : Matrix I I ℂ} (hSupport : SupportLE ρ σ) (hσ : σ.PosSemidef)
    (hzero : σ.trace.re = 0) : ρ.trace.re = 0 := by
  have htrace : σ.trace = 0 := by
    rw [positive_trace_eq_ofReal hσ, hzero]
    rfl
  have hσzero := hσ.trace_eq_zero_iff.mp htrace
  obtain ⟨F, hF⟩ := hSupport.exists_right_factor
  rw [hσzero, Matrix.zero_mul] at hF
  simp [hF]

theorem krausTrace_re_zero_of_comparison {I O Z : Type*}
    [Fintype I] [Fintype O] [Fintype Z] [DecidableEq I] [DecidableEq O]
    (K : Z → Matrix O I ℂ) {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hSupport : SupportLE ρ σ)
    (hzero : (krausSumB K σ).trace.re = 0) : (krausSumB K ρ).trace.re = 0 :=
  (QuantumProver.SandwichedDPI.supportLE_kraus_sum K hρ hσ hSupport).trace_re_zero_of_comparison
    (krausSumB_posSemidef K hσ) hzero

theorem krausTrace_re_pos_of_honest {I O Z : Type*}
    [Fintype I] [Fintype O] [Fintype Z] [DecidableEq I] [DecidableEq O]
    (K : Z → Matrix O I ℂ) {ρ σ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hSupport : SupportLE ρ σ)
    (hpos : 0 < (krausSumB K ρ).trace.re) : 0 < (krausSumB K σ).trace.re := by
  by_contra h
  have hzero : (krausSumB K σ).trace.re = 0 := le_antisymm (le_of_not_gt h)
    (Complex.nonneg_iff.mp (krausSumB_posSemidef K hσ).trace_nonneg).1
  have hrzero := krausTrace_re_zero_of_comparison K hρ hσ hSupport hzero
  linarith

end QuantumProver.AmplitudeDamping.FiniteModel
