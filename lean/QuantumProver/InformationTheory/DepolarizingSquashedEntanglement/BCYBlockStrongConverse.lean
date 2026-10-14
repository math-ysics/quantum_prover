import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BCYTensorRegularization
import QuantumProver.InformationTheory.QuantumSteinStrongConverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

noncomputable section

open Matrix Set Filter
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace QuantumProver.DepolarizingSquashedEntanglement.BCYBlockStrongConverse

open BCYRelativeEntropy
open QuantumProver.SuperchannelDiscrimination
open FlaggedStates TensorEntropy

variable {A B I J : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype J]
  [DecidableEq A] [DecidableEq B] [DecidableEq I] [DecidableEq J]

def copyBlocks (A : Type*) (m : ℕ) : (q : ℕ) →
    CopyIndex A (m * q) ≃ CopyIndex (CopyIndex A m) q
  | 0 => Equiv.refl PUnit
  | q + 1 => (copyConcat A (m * q) m).trans
      (Equiv.prodCongr (copyBlocks A m q) (Equiv.refl (CopyIndex A m)))

theorem tensorCopies_blocks_apply (ρ : Density (A × B)) (m q : ℕ) :
    ∀ (a a' : CopyIndex (CopyIndex A m) q) (b b' : CopyIndex (CopyIndex B m) q),
      (tensorCopies ρ (m * q)).matrix
        ((copyBlocks A m q).symm a, (copyBlocks B m q).symm b)
        ((copyBlocks A m q).symm a', (copyBlocks B m q).symm b') =
      (tensorCopies (tensorCopies ρ m) q).matrix (a,b) (a',b') := by
  induction q with
  | zero =>
      intro a a' b b'
      cases a
      cases a'
      cases b
      cases b'
      rfl
  | succ q ih =>
      rintro ⟨a,i⟩ ⟨a',i'⟩ ⟨b,j⟩ ⟨b',j'⟩
      change (tensorCopies ρ (m * q + m)).matrix
        ((copyConcat A (m * q) m).symm ((copyBlocks A m q).symm a,i),
          (copyConcat B (m * q) m).symm ((copyBlocks B m q).symm b,j))
        ((copyConcat A (m * q) m).symm ((copyBlocks A m q).symm a',i'),
          (copyConcat B (m * q) m).symm ((copyBlocks B m q).symm b',j')) =
        (tensorCopies (tensorCopies ρ m) q).matrix (a,b) (a',b') *
          (tensorCopies ρ m).matrix (i,j) (i',j')
      rw [tensorCopies_add_apply, ih]

theorem tensorCopies_blocks_matrix (ρ : Density (A × B)) (m q : ℕ) :
    Matrix.reindex (Equiv.prodCongr (copyBlocks A m q) (copyBlocks B m q))
      (Equiv.prodCongr (copyBlocks A m q) (copyBlocks B m q))
      (tensorCopies ρ (m * q)).matrix = (tensorCopies (tensorCopies ρ m) q).matrix := by
  ext x y
  exact tensorCopies_blocks_apply ρ m q x.1 y.1 x.2 y.2

def paddedLocalChart (A : Type*) (m q r : ℕ) :
    (CopyIndex (CopyIndex A m) q × CopyIndex A r) ≃ CopyIndex A (m * q + r) :=
  (Equiv.prodCongr (copyBlocks A m q).symm (Equiv.refl (CopyIndex A r))).trans
    (copyConcat A (m * q) r).symm

def paddedBlockComparisonAt (m q r : ℕ)
    (σ : SeparableDensity (CopyIndex A m) (CopyIndex B m))
    (ω : SeparableDensity A B) :
    SeparableDensity (CopyIndex A (m * q + r)) (CopyIndex B (m * q + r)) :=
  ⟨densityReindex (Equiv.prodCongr (paddedLocalChart A m q r) (paddedLocalChart B m q r))
      (bipartiteTensorDensity (tensorCopies σ.val q) (tensorCopies ω.val r)),
    isSeparable_reindex _ _
      (bipartiteTensorMatrix_separable (tensorCopies_separable σ.val σ.property q)
        (tensorCopies_separable ω.val ω.property r))⟩

theorem tensorCopies_posDef (ρ : Density (A × B)) (hρ : ρ.matrix.PosDef) (n : ℕ) :
    (tensorCopies ρ n).matrix.PosDef :=
  (TensorEntropy.tensorPower_posDef hρ n).submatrix (copyGrouping A B n).symm.injective

theorem paddedBlockComparisonAt_posDef (m q r : ℕ)
    (σ : SeparableDensity (CopyIndex A m) (CopyIndex B m))
    (ω : SeparableDensity A B) (hσ : σ.val.matrix.PosDef) (hω : ω.val.matrix.PosDef) :
    (paddedBlockComparisonAt m q r σ ω).val.matrix.PosDef :=
  (((tensorCopies_posDef σ.val hσ q).kronecker (tensorCopies_posDef ω.val hω r)).submatrix
    (Equiv.prodProdProdComm (CopyIndex (CopyIndex A m) q)
      (CopyIndex (CopyIndex B m) q) (CopyIndex A r) (CopyIndex B r)).symm.injective).submatrix
    (Equiv.prodCongr (paddedLocalChart A m q r) (paddedLocalChart B m q r)).symm.injective

def blockGlobalChartAt (A B : Type*) (m q r : ℕ) :
    (CopyIndex A (m * q + r) × CopyIndex B (m * q + r)) ≃
      (TensorIndex (CopyIndex A m × CopyIndex B m) q ×
        (CopyIndex A r × CopyIndex B r)) :=
  (Equiv.prodCongr (paddedLocalChart A m q r).symm (paddedLocalChart B m q r).symm).trans
    ((Equiv.prodProdProdComm (CopyIndex (CopyIndex A m) q)
      (CopyIndex (CopyIndex B m) q) (CopyIndex A r) (CopyIndex B r)).symm.trans
        (Equiv.prodCongr (copyGrouping (CopyIndex A m) (CopyIndex B m) q).symm
          (Equiv.refl (CopyIndex A r × CopyIndex B r))))

theorem paddedBlockComparisonAt_raw (m q r : ℕ)
    (σ : SeparableDensity (CopyIndex A m) (CopyIndex B m))
    (ω : SeparableDensity A B) :
    Matrix.reindex (blockGlobalChartAt A B m q r) (blockGlobalChartAt A B m q r)
      (paddedBlockComparisonAt m q r σ ω).val.matrix =
        TensorEntropy.tensorPower σ.val.matrix q ⊗ₖ (tensorCopies ω.val r).matrix := by
  ext x y
  simp [blockGlobalChartAt, paddedBlockComparisonAt, bipartiteTensorDensity,
    productDensity, densityReindex, tensorCopies_matrix, Matrix.reindex,
    Matrix.submatrix, Equiv.prodCongr_apply]

theorem tensorCopies_block_raw (ρ : Density (A × B)) (m q r : ℕ) :
    Matrix.reindex (blockGlobalChartAt A B m q r) (blockGlobalChartAt A B m q r)
      (tensorCopies ρ (m * q + r)).matrix =
        TensorEntropy.tensorPower (tensorCopies ρ m).matrix q ⊗ₖ (tensorCopies ρ r).matrix := by
  ext x y
  rcases x with ⟨x,u⟩
  rcases y with ⟨y,v⟩
  let gx := copyGrouping (CopyIndex A m) (CopyIndex B m) q x
  let gy := copyGrouping (CopyIndex A m) (CopyIndex B m) q y
  change (tensorCopies ρ (m * q + r)).matrix
      ((copyConcat A (m * q) r).symm ((copyBlocks A m q).symm gx.1,u.1),
        (copyConcat B (m * q) r).symm ((copyBlocks B m q).symm gx.2,u.2))
      ((copyConcat A (m * q) r).symm ((copyBlocks A m q).symm gy.1,v.1),
        (copyConcat B (m * q) r).symm ((copyBlocks B m q).symm gy.2,v.2)) = _
  rw [tensorCopies_add_apply, tensorCopies_blocks_apply]
  change (TensorEntropy.tensorPower (tensorCopies ρ m).matrix q)
      ((copyGrouping (CopyIndex A m) (CopyIndex B m) q).symm gx)
      ((copyGrouping (CopyIndex A m) (CopyIndex B m) q).symm gy) *
        (tensorCopies ρ r).matrix u v = _
  simp only [gx, gy, Equiv.symm_apply_apply, Matrix.kronecker_apply]

theorem exists_faithful_domination {R S : Matrix I I ℂ}
    (hR : R.PosSemidef) (hS : S.PosDef) :
    ∃ c : ℝ, 1 ≤ c ∧ (c • S - R).PosSemidef := by
  let U := CFC.sqrt S
  let V := CFC.sqrt R
  have hU : U.PosSemidef := (CFC.sqrt_nonneg S).posSemidef
  have hV : V.PosSemidef := (CFC.sqrt_nonneg R).posSemidef
  have hUU : U * Uᴴ = S := by
    rw [hU.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hVV : V * Vᴴ = R := by
    rw [hV.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self R hR.nonneg
  have hs : HasSupportIn (V * Vᴴ) (U * Uᴴ) := by
    rw [hVV, hUU]
    exact hasSupportIn_of_posDef R hS
  obtain ⟨c,hc,hdom⟩ := GlobalMatrixSplit.exists_finite_gram_domination_of_support U V hs
  rw [hUU, hVV] at hdom
  exact ⟨c,hc,hdom⟩

theorem tensorPower_domination {R S : Matrix I I ℂ} {c : ℝ}
    (hR : R.PosSemidef) (hS : S.PosSemidef) (hc : 0 ≤ c)
    (hcap : (c • S - R).PosSemidef) (n : ℕ) :
    (c ^ n • TensorEntropy.tensorPower S n - TensorEntropy.tensorPower R n).PosSemidef := by
  induction n with
  | zero => simpa [TensorEntropy.tensorPower] using
      (Matrix.PosSemidef.zero : (0 : Matrix PUnit PUnit ℂ).PosSemidef)
  | succ n ih =>
      have hRn := TensorEntropy.tensorPower_posSemidef hR n
      have h := (ih.kronecker (hS.smul hc)).add (hRn.kronecker hcap)
      change (c ^ (n + 1) • (TensorEntropy.tensorPower S n ⊗ₖ S) -
        TensorEntropy.tensorPower R n ⊗ₖ R).PosSemidef
      have heq : c ^ (n + 1) • (TensorEntropy.tensorPower S n ⊗ₖ S) -
          TensorEntropy.tensorPower R n ⊗ₖ R =
        (c ^ n • TensorEntropy.tensorPower S n - TensorEntropy.tensorPower R n) ⊗ₖ
          (c • S) + TensorEntropy.tensorPower R n ⊗ₖ (c • S - R) := by
        ext x y
        rcases x with ⟨i,j⟩
        rcases y with ⟨i',j'⟩
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
          Matrix.kronecker_apply, pow_succ, Complex.ofReal_mul,
          Complex.real_smul]
        ring
      rw [heq]
      exact h

theorem tensorCopies_remainder_domination (ρ : Density (A × B))
    (ω : Density (A × B)) (hω : ω.matrix.PosDef) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r < m,
      (C • (tensorCopies ω r).matrix - (tensorCopies ρ r).matrix).PosSemidef := by
  obtain ⟨c,hc,hcap⟩ := exists_faithful_domination ρ.positive hω
  refine ⟨c ^ m, one_le_pow₀ hc, ?_⟩
  intro r hr
  have hcr : c ^ r ≤ c ^ m := pow_le_pow_right₀ hc hr.le
  have h := (tensorPower_domination ρ.positive ω.positive (zero_le_one.trans hc) hcap r).submatrix
    (copyGrouping A B r).symm
  change (c ^ r • (tensorCopies ω r).matrix - (tensorCopies ρ r).matrix).PosSemidef at h
  have hExtra := (tensorCopies ω r).positive.smul (sub_nonneg.mpr hcr)
  convert h.add hExtra using 1
  module

theorem tensorCopies_cast (ρ : Density (A × B)) {m n : ℕ} (h : m = n) :
    Matrix.reindex (Equiv.prodCongr (Equiv.cast (congrArg (CopyIndex A) h))
        (Equiv.cast (congrArg (CopyIndex B) h)))
      (Equiv.prodCongr (Equiv.cast (congrArg (CopyIndex A) h))
        (Equiv.cast (congrArg (CopyIndex B) h))) (tensorCopies ρ m).matrix =
      (tensorCopies ρ n).matrix := by
  cases h
  rfl

def physicalCopyCast (A : Type*) (m n : ℕ) :
    CopyIndex A n ≃ CopyIndex A (m * (n / m) + n % m) :=
  Equiv.cast (congrArg (CopyIndex A) (Nat.div_add_mod n m).symm)

def paddedBlockComparison (m : ℕ)
    (σ : SeparableDensity (CopyIndex A m) (CopyIndex B m))
    (ω : SeparableDensity A B) (n : ℕ) :
    SeparableDensity (CopyIndex A n) (CopyIndex B n) :=
  ⟨densityReindex (Equiv.prodCongr (physicalCopyCast A m n).symm (physicalCopyCast B m n).symm)
      (paddedBlockComparisonAt m (n / m) (n % m) σ ω).val,
    isSeparable_reindex _ _ (paddedBlockComparisonAt m (n / m) (n % m) σ ω).property⟩

theorem paddedBlockComparison_posDef (m : ℕ)
    (σ : SeparableDensity (CopyIndex A m) (CopyIndex B m))
    (ω : SeparableDensity A B) (hσ : σ.val.matrix.PosDef) (hω : ω.val.matrix.PosDef)
    (n : ℕ) : (paddedBlockComparison m σ ω n).val.matrix.PosDef :=
  (paddedBlockComparisonAt_posDef m (n / m) (n % m) σ ω hσ hω).submatrix
    (Equiv.prodCongr (physicalCopyCast A m n).symm (physicalCopyCast B m n).symm).symm.injective

def blockGlobalChart (A B : Type*) (m n : ℕ) :
    (CopyIndex A n × CopyIndex B n) ≃
      (TensorIndex (CopyIndex A m × CopyIndex B m) (n / m) ×
        (CopyIndex A (n % m) × CopyIndex B (n % m))) :=
  (Equiv.prodCongr (physicalCopyCast A m n) (physicalCopyCast B m n)).trans
    (blockGlobalChartAt A B m (n / m) (n % m))

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem reindex_trans_matrix {K : Type*} [Fintype K] [DecidableEq K]
    (e : I ≃ J) (f : J ≃ K) (X : Matrix I I ℂ) :
    Matrix.reindex (e.trans f) (e.trans f) X =
      Matrix.reindex f f (Matrix.reindex e e X) := by
  ext x y
  rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem reindex_inverse_matrix (e : I ≃ J) (X : Matrix J J ℂ) :
    Matrix.reindex e e (Matrix.reindex e.symm e.symm X) = X := by
  ext x y
  simp [Matrix.reindex, Matrix.submatrix]

theorem paddedBlockComparison_raw (m : ℕ)
    (σ : SeparableDensity (CopyIndex A m) (CopyIndex B m))
    (ω : SeparableDensity A B) (n : ℕ) :
    Matrix.reindex (blockGlobalChart A B m n) (blockGlobalChart A B m n)
      (paddedBlockComparison m σ ω n).val.matrix =
        TensorEntropy.tensorPower σ.val.matrix (n / m) ⊗ₖ (tensorCopies ω.val (n % m)).matrix := by
  change Matrix.reindex
    ((Equiv.prodCongr (physicalCopyCast A m n) (physicalCopyCast B m n)).trans
      (blockGlobalChartAt A B m (n / m) (n % m)))
    ((Equiv.prodCongr (physicalCopyCast A m n) (physicalCopyCast B m n)).trans
      (blockGlobalChartAt A B m (n / m) (n % m)))
    (Matrix.reindex
      (Equiv.prodCongr (physicalCopyCast A m n) (physicalCopyCast B m n)).symm
      (Equiv.prodCongr (physicalCopyCast A m n) (physicalCopyCast B m n)).symm
      (paddedBlockComparisonAt m (n / m) (n % m) σ ω).val.matrix) = _
  rw [reindex_trans_matrix, reindex_inverse_matrix, paddedBlockComparisonAt_raw]

theorem tensorCopies_physical_block_raw (ρ : Density (A × B)) (m n : ℕ) :
    Matrix.reindex (blockGlobalChart A B m n) (blockGlobalChart A B m n)
      (tensorCopies ρ n).matrix =
        TensorEntropy.tensorPower (tensorCopies ρ m).matrix (n / m) ⊗ₖ
          (tensorCopies ρ (n % m)).matrix := by
  unfold blockGlobalChart
  rw [reindex_trans_matrix]
  rw [show Matrix.reindex (Equiv.prodCongr (physicalCopyCast A m n) (physicalCopyCast B m n))
      (Equiv.prodCongr (physicalCopyCast A m n) (physicalCopyCast B m n))
        (tensorCopies ρ n).matrix = (tensorCopies ρ (m * (n / m) + n % m)).matrix from
    tensorCopies_cast ρ (Nat.div_add_mod n m).symm]
  exact tensorCopies_block_raw ρ m (n / m) (n % m)

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem partialTrace_kronecker (X : Matrix I I ℂ) (Y : Matrix J J ℂ) :
    QuantumProver.QuantumEntropy.partialTrace_right (X ⊗ₖ Y) = Y.trace • X := by
  ext i j
  simp [QuantumProver.QuantumEntropy.partialTrace_right,
    Matrix.smul_apply, Matrix.trace, Finset.mul_sum, mul_comm]

def weightedTailEffect (τ : Density J) (T : Matrix (I × J) (I × J) ℂ) : Matrix I I ℂ :=
  let U := (1 : Matrix I I ℂ) ⊗ₖ CFC.sqrt τ.matrix
  QuantumProver.QuantumEntropy.partialTrace_right (U * T * U)

theorem weightedTailEffect_posSemidef (τ : Density J)
    {T : Matrix (I × J) (I × J) ℂ} (hT : T.PosSemidef) :
    (weightedTailEffect τ T).PosSemidef := by
  let U := (1 : Matrix I I ℂ) ⊗ₖ CFC.sqrt τ.matrix
  have hU : U.PosSemidef := Matrix.PosSemidef.one.kronecker (CFC.sqrt_nonneg τ.matrix).posSemidef
  exact QuantumProver.QuantumEntropy.partialTraceRight_posSemidef
    (by simpa only [hU.isHermitian.eq] using hT.mul_mul_conjTranspose_same U)

theorem weightedTailEffect_one (τ : Density J) :
    weightedTailEffect (I := I) τ 1 = 1 := by
  dsimp only [weightedTailEffect]
  rw [Matrix.mul_one, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    CFC.sqrt_mul_sqrt_self τ.matrix τ.positive.nonneg, partialTrace_kronecker,
    τ.trace_one, one_smul]

theorem weightedTailEffect_sub (τ : Density J) (T S : Matrix (I × J) (I × J) ℂ) :
    weightedTailEffect τ (T - S) = weightedTailEffect τ T - weightedTailEffect τ S := by
  ext i j
  simp [weightedTailEffect, Matrix.mul_sub, Matrix.sub_mul,
    QuantumProver.QuantumEntropy.partialTrace_right, Matrix.sub_apply, Finset.sum_sub_distrib]

theorem weightedTailEffect_isEffect (τ : Density J)
    {T : Matrix (I × J) (I × J) ℂ} (hT : IsEffect T) :
    IsEffect (weightedTailEffect τ T) := by
  refine ⟨weightedTailEffect_posSemidef τ hT.1, ?_⟩
  have h := weightedTailEffect_posSemidef τ hT.2
  rwa [weightedTailEffect_sub, weightedTailEffect_one] at h

theorem weightedTailEffect_trace_pairing (τ : Density J)
    (X : Matrix I I ℂ) (T : Matrix (I × J) (I × J) ℂ) :
    (X * weightedTailEffect τ T).trace = ((X ⊗ₖ τ.matrix) * T).trace := by
  let U := (1 : Matrix I I ℂ) ⊗ₖ CFC.sqrt τ.matrix
  have hUXU : U * (X ⊗ₖ (1 : Matrix J J ℂ)) * U = X ⊗ₖ τ.matrix := by
    dsimp [U]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      CFC.sqrt_mul_sqrt_self τ.matrix τ.positive.nonneg]
  calc
    _ = (weightedTailEffect τ T * X).trace := Matrix.trace_mul_comm _ _
    _ = (U * T * U * (X ⊗ₖ (1 : Matrix J J ℂ))).trace :=
      (QuantumProver.QuantumEntropy.partialTrace_right_mul_trace (U * T * U) X).symm
    _ = (U * (T * (U * (X ⊗ₖ (1 : Matrix J J ℂ))))).trace := by
      congr 1
      noncomm_ring
    _ = ((T * (U * (X ⊗ₖ (1 : Matrix J J ℂ)))) * U).trace := Matrix.trace_mul_comm _ _
    _ = (T * (U * (X ⊗ₖ (1 : Matrix J J ℂ)) * U)).trace := by
      congr 1
      noncomm_ring
    _ = (T * (X ⊗ₖ τ.matrix)).trace := by rw [hUXU]
    _ = _ := Matrix.trace_mul_comm _ _

theorem weightedTailEffect_acceptance (τ : Density J)
    (X : Matrix I I ℂ) (T : Matrix (I × J) (I × J) ℂ) :
    acceptanceProbability X (weightedTailEffect τ T) =
      acceptanceProbability (X ⊗ₖ τ.matrix) T :=
  congrArg Complex.re (weightedTailEffect_trace_pairing τ X T)

omit [Fintype I] [Fintype J] in
theorem isEffect_reindex (e : I ≃ J) {T : Matrix I I ℂ} (hT : IsEffect T) :
    IsEffect (Matrix.reindex e e T) := by
  refine ⟨hT.1.submatrix e.symm, ?_⟩
  have h := hT.2.submatrix e.symm
  have heq : (1 - T).submatrix e.symm e.symm = 1 - Matrix.reindex e e T := by
    ext i j
    simp [Matrix.reindex, Matrix.submatrix, Matrix.one_apply]
  rwa [heq] at h

theorem acceptance_reindex (e : I ≃ J) (X T : Matrix I I ℂ) :
    acceptanceProbability (Matrix.reindex e e X) (Matrix.reindex e e T) =
      acceptanceProbability X T := by
  unfold acceptanceProbability
  have hmul : Matrix.reindex e e X * Matrix.reindex e e T = Matrix.reindex e e (X * T) :=
    ((Matrix.reindexAlgEquiv ℂ ℂ e).map_mul X T).symm
  rw [hmul]
  exact congrArg Complex.re (QuantumProver.QuantumSteinStrongConverse.trace_reindex e (X * T))

theorem tensor_tail_acceptance_le {X : Matrix I I ℂ} {R S : Matrix J J ℂ} {C : ℝ}
    (hX : X.PosSemidef) (hcap : (C • S - R).PosSemidef)
    {T : Matrix (I × J) (I × J) ℂ} (hT : T.PosSemidef) :
    acceptanceProbability (X ⊗ₖ R) T ≤ C * acceptanceProbability (X ⊗ₖ S) T := by
  have hTensor : (C • (X ⊗ₖ S) - X ⊗ₖ R).PosSemidef := by
    have heq : C • (X ⊗ₖ S) - X ⊗ₖ R = X ⊗ₖ (C • S - R) := by
      ext ⟨i,j⟩ ⟨i',j'⟩
      simp [Matrix.smul_apply, Matrix.sub_apply, mul_sub,
        Complex.real_smul]
      ring
    rw [heq]
    exact hX.kronecker hcap
  have h := trace_mul_re_nonneg hTensor hT
  change 0 ≤ ((C • (X ⊗ₖ S) - X ⊗ₖ R) * T).trace.re at h
  simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.smul_re, smul_eq_mul] at h
  unfold acceptanceProbability
  linarith

theorem tendsto_copy_quotient {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => n / m) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b * m)] with n hn
  exact (Nat.le_div_iff_mul_le hm).mpr hn

theorem exists_uniform_block_acceptance_envelope (ρ : Density (A × B))
    (m : ℕ) (hm : 0 < m)
    (σ : SeparableDensity (CopyIndex A m) (CopyIndex B m))
    (ω : SeparableDensity A B) (hσ : σ.val.matrix.PosDef) (hω : ω.val.matrix.PosDef)
    {rRate : ℝ}
    (hr : PetzMoments.relativeEntropyNats (tensorCopies ρ m).matrix σ.val.matrix / (m : ℝ) < rRate) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ T : Matrix (CopyIndex A n × CopyIndex B n)
          (CopyIndex A n × CopyIndex B n) ℂ,
        IsEffect T →
        acceptanceProbability (paddedBlockComparison m σ ω n).val.matrix T ≤
          Real.exp (-(n : ℝ) * rRate) →
        acceptanceProbability (tensorCopies ρ n).matrix T ≤ ε n := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hD0 : 0 ≤ PetzMoments.relativeEntropyNats (tensorCopies ρ m).matrix σ.val.matrix := by
    have h := umegakiNats_nonneg (tensorCopies ρ m) σ.val
    rw [umegakiNats_of_support _ _ (hasSupportIn_of_posDef _ hσ)] at h
    exact EReal.coe_nonneg.mp h
  have hr0 : 0 < rRate := (div_nonneg hD0 hmR.le).trans_lt hr
  have hrBlock : PetzMoments.relativeEntropyNats (tensorCopies ρ m).matrix σ.val.matrix <
      (m : ℝ) * rRate := by
    have h := (div_lt_iff₀ hmR).mp hr
    simpa only [mul_comm] using h
  obtain ⟨ε,hε,ht,hbound⟩ := QuantumProver.QuantumSteinStrongConverse.exists_uniform_acceptance_envelope
    (density_matrix (tensorCopies ρ m)) (density_matrix σ.val) hσ hrBlock
  obtain ⟨C,hC,hcap⟩ := tensorCopies_remainder_domination ρ ω.val hω m
  have hdiv := tendsto_copy_quotient hm
  refine ⟨fun n => C * ε (n / m),
    (fun n => mul_nonneg (zero_le_one.trans hC) (hε _)),
    (by simpa using (ht.comp hdiv).const_mul C), ?_⟩
  filter_upwards [hdiv.eventually hbound] with n hn
  intro T hT hβ
  let e := blockGlobalChart A B m n
  let S := Matrix.reindex e e T
  let W := weightedTailEffect (tensorCopies ω.val (n % m)) S
  have hS : IsEffect S := isEffect_reindex e hT
  have hW : IsEffect W := weightedTailEffect_isEffect _ hS
  have hβW : acceptanceProbability (TensorEntropy.tensorPower σ.val.matrix (n / m)) W ≤
      Real.exp (-((n / m : ℕ) : ℝ) * ((m : ℝ) * rRate)) := by
    calc
      _ = acceptanceProbability
          (TensorEntropy.tensorPower σ.val.matrix (n / m) ⊗ₖ (tensorCopies ω.val (n % m)).matrix) S :=
        weightedTailEffect_acceptance _ _ _
      _ = acceptanceProbability (paddedBlockComparison m σ ω n).val.matrix T := by
        rw [← paddedBlockComparison_raw m σ ω n]
        exact acceptance_reindex e _ T
      _ ≤ Real.exp (-(n : ℝ) * rRate) := hβ
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hNat : m * (n / m) ≤ n := by
          have h := Nat.div_add_mod n m
          omega
        have hReal : (m : ℝ) * ((n / m : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNat
        nlinarith [mul_le_mul_of_nonneg_right hReal hr0.le]
  have hAccept := hn W hW hβW
  have hTail := hcap (n % m) (Nat.mod_lt n hm)
  calc
    acceptanceProbability (tensorCopies ρ n).matrix T =
        acceptanceProbability
          (TensorEntropy.tensorPower (tensorCopies ρ m).matrix (n / m) ⊗ₖ
            (tensorCopies ρ (n % m)).matrix) S := by
      rw [← tensorCopies_physical_block_raw ρ m n]
      exact (acceptance_reindex e _ T).symm
    _ ≤ C * acceptanceProbability
        (TensorEntropy.tensorPower (tensorCopies ρ m).matrix (n / m) ⊗ₖ
          (tensorCopies ω.val (n % m)).matrix) S :=
      tensor_tail_acceptance_le (TensorEntropy.tensorPower_posSemidef (tensorCopies ρ m).positive _)
        hTail hS.1
    _ = C * acceptanceProbability (TensorEntropy.tensorPower (tensorCopies ρ m).matrix (n / m)) W :=
      congrArg (fun x : ℝ => C * x) (weightedTailEffect_acceptance _ _ _).symm
    _ ≤ C * ε (n / m) := mul_le_mul_of_nonneg_left hAccept (zero_le_one.trans hC)

theorem block_strong_converse_nats (ρ : Density (A × B)) (m : ℕ) (hm : 0 < m)
    (σ : SeparableDensity (CopyIndex A m) (CopyIndex B m))
    (ω : SeparableDensity A B) (hσ : σ.val.matrix.PosDef) (hω : ω.val.matrix.PosDef)
    {rRate : ℝ}
    (hr : PetzMoments.relativeEntropyNats (tensorCopies ρ m).matrix σ.val.matrix / (m : ℝ) < rRate)
    (T : (n : ℕ) → Matrix (CopyIndex A n × CopyIndex B n) (CopyIndex A n × CopyIndex B n) ℂ)
    (hT : ∀ n, IsEffect (T n))
    (hβ : ∀ᶠ n : ℕ in atTop,
      acceptanceProbability (paddedBlockComparison m σ ω n).val.matrix (T n) ≤
        Real.exp (-(n : ℝ) * rRate)) :
    Tendsto (fun n => acceptanceProbability (tensorCopies ρ n).matrix (T n)) atTop (𝓝 0) := by
  obtain ⟨ε,hε,ht,hbound⟩ := exists_uniform_block_acceptance_envelope ρ m hm σ ω hσ hω hr
  apply squeeze_zero' (Eventually.of_forall (fun n =>
    trace_mul_re_nonneg (tensorCopies ρ n).positive (hT n).1)) _ ht
  filter_upwards [hbound,hβ] with n hn hβn
  exact hn (T n) (hT n) hβn

end QuantumProver.DepolarizingSquashedEntanglement.BCYBlockStrongConverse
