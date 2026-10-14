import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ProtocolReadout
import QuantumProver.InformationTheory.AmplitudeDamping.SecretKey.ParallelLanes

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable section

namespace QuantumProver.AmplitudeDamping.SecretKey.ProductPrivacyTest

open Matrix PrivateTest IndependentLanes
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] Classical.decEq

variable {K A B I : Type*} [Fintype K] [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq K] [DecidableEq A] [DecidableEq B] [DecidableEq I]

theorem gram_one_norm_map (W : Matrix I I ℂ) (hW : Wᴴ * W = 1)
    (v : EuclideanSpace ℂ I) : ‖W.toEuclideanLin v‖ = ‖v‖ := by
  have hn : ‖W.toEuclideanLin v‖ ^ 2 = ‖v‖ ^ 2 := by
    calc
      _ = (W * Matrix.vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)) * Wᴴ).trace.re := by
        simpa only [WithLp.toLp_ofLp] using (congruence_Gram_trace W (WithLp.ofLp v)).symm
      _ = ‖v‖ ^ 2 := by
        rw [Matrix.trace_mul_cycle, hW, Matrix.one_mul, traceGram_norm]
  nlinarith [norm_nonneg (W.toEuclideanLin v), norm_nonneg v]

def rawPrivacyMatrix (W : K → Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) ((K × A) × (K × B)) ℂ :=
  fun s r => if r.1.1 = r.2.1 then W r.1.1 s (r.1.2, r.2.2) else 0

def rawPrivacyAcceptance (W : K → Matrix (A × B) (A × B) ℂ)
    (M : Matrix ((K × A) × (K × B)) ((K × A) × (K × B)) ℂ) : ℝ :=
  (rawPrivacyMatrix W * M * (rawPrivacyMatrix W)ᴴ).trace.re / (Fintype.card K : ℝ)

def rawPrivacyEffect (W : K → Matrix (A × B) (A × B) ℂ) :
    Matrix ((K × A) × (K × B)) ((K × A) × (K × B)) ℂ :=
  (1 / (Fintype.card K : ℝ)) • ((rawPrivacyMatrix W)ᴴ * rawPrivacyMatrix W)

theorem rawPrivacyMatrix_product (W : K → Matrix (A × B) (A × B) ℂ)
    (x : EuclideanSpace ℂ (K × A)) (y : EuclideanSpace ℂ (K × B)) :
    (rawPrivacyMatrix W).toEuclideanLin (productVector x y) =
      ∑ k, (W k).toEuclideanLin (productVector (keyBlock x k) (keyBlock y k)) := by
  ext s
  simp [rawPrivacyMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, productVector, keyBlock, WithLp.ofLp_sum,
    Finset.sum_apply, ite_mul, mul_assoc]

theorem rawPrivacyAmplitude_norm_sq_le
    (W : K → Matrix (A × B) (A × B) ℂ) (hW : ∀ k, (W k)ᴴ * W k = 1)
    (x : EuclideanSpace ℂ (K × A)) (y : EuclideanSpace ℂ (K × B)) :
    ‖(rawPrivacyMatrix W).toEuclideanLin (productVector x y)‖ ^ 2 ≤
      ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have ht : ‖(rawPrivacyMatrix W).toEuclideanLin (productVector x y)‖ ≤
      ∑ k, ‖keyBlock x k‖ * ‖keyBlock y k‖ := by
    rw [rawPrivacyMatrix_product]
    simpa only [gram_one_norm_map _ (hW _), norm_productVector] using
      norm_sum_le Finset.univ (fun k => (W k).toEuclideanLin
        (productVector (keyBlock x k) (keyBlock y k)))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k => ‖keyBlock x k‖) (fun k => ‖keyBlock y k‖)
  rw [sum_keyBlock_norm_sq x, sum_keyBlock_norm_sq y] at hc
  have hp : 0 ≤ ∑ k, ‖keyBlock x k‖ * ‖keyBlock y k‖ := by positivity
  nlinarith [norm_nonneg ((rawPrivacyMatrix W).toEuclideanLin (productVector x y))]

theorem rawPrivacyAcceptance_sum {Z : Type*} [Fintype Z]
    (W : K → Matrix (A × B) (A × B) ℂ)
    (M : Z → Matrix ((K × A) × (K × B)) ((K × A) × (K × B)) ℂ) :
    rawPrivacyAcceptance W (∑ z, M z) = ∑ z, rawPrivacyAcceptance W (M z) := by
  simp [rawPrivacyAcceptance, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum,
    Complex.re_sum, Finset.sum_div]

theorem rawPrivacyAcceptance_Gram_product_le
    (W : K → Matrix (A × B) (A × B) ℂ) (hW : ∀ k, (W k)ᴴ * W k = 1)
    (u : K × A → ℂ) (v : K × B → ℂ) :
    rawPrivacyAcceptance W (Matrix.vecMulVec u (star u) ⊗ₖ Matrix.vecMulVec v (star v)) ≤
      ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (K × A))‖ ^ 2 *
        ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (K × B))‖ ^ 2 / (Fintype.card K : ℝ) := by
  rw [Gram_product_matrix, rawPrivacyAcceptance, congruence_Gram_trace]
  change ‖(rawPrivacyMatrix W).toEuclideanLin
    (productVector (WithLp.toLp 2 u) (WithLp.toLp 2 v))‖ ^ 2 / (Fintype.card K : ℝ) ≤ _
  exact div_le_div_of_nonneg_right
    (rawPrivacyAmplitude_norm_sq_le W hW (WithLp.toLp 2 u) (WithLp.toLp 2 v))
    (Nat.cast_nonneg _)

theorem rawPrivacyAcceptance_product_psd_le
    (W : K → Matrix (A × B) (A × B) ℂ) (hW : ∀ k, (W k)ᴴ * W k = 1)
    {M : Matrix (K × A) (K × A) ℂ} {N : Matrix (K × B) (K × B) ℂ}
    (hM : M.PosSemidef) (hN : N.PosSemidef) :
    rawPrivacyAcceptance W (M ⊗ₖ N) ≤ M.trace.re * N.trace.re / (Fintype.card K : ℝ) := by
  obtain ⟨m, u, hu⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM
  obtain ⟨n, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hN
  have hnu : (∑ i : Fin m,
      ‖(WithLp.toLp 2 (u i) : EuclideanSpace ℂ (K × A))‖ ^ 2) = M.trace.re := by
    rw [hu, Matrix.trace_sum, Complex.re_sum]
    simp only [traceGram_norm]
  have hnv : (∑ j : Fin n,
      ‖(WithLp.toLp 2 (v j) : EuclideanSpace ℂ (K × B))‖ ^ 2) = N.trace.re := by
    rw [hv, Matrix.trace_sum, Complex.re_sum]
    simp only [traceGram_norm]
  have hp : M ⊗ₖ N = ∑ i : Fin m, ∑ j : Fin n,
      Matrix.vecMulVec (u i) (star (u i)) ⊗ₖ Matrix.vecMulVec (v j) (star (v j)) := by
    rw [hu, hv]
    ext x y
    simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm
  rw [hp, rawPrivacyAcceptance_sum]
  simp_rw [rawPrivacyAcceptance_sum]
  calc
    _ ≤ ∑ i : Fin m, ∑ j : Fin n,
        ‖(WithLp.toLp 2 (u i) : EuclideanSpace ℂ (K × A))‖ ^ 2 *
          ‖(WithLp.toLp 2 (v j) : EuclideanSpace ℂ (K × B))‖ ^ 2 / (Fintype.card K : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact rawPrivacyAcceptance_Gram_product_le W hW (u i) (v j)
    _ = M.trace.re * N.trace.re / (Fintype.card K : ℝ) := by
      simp only [← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul, hnu, hnv]

theorem rawPrivacyAcceptance_separableCone_le
    (W : K → Matrix (A × B) (A × B) ℂ) (hW : ∀ k, (W k)ᴴ * W k = 1)
    {M : Matrix ((K × A) × (K × B)) ((K × A) × (K × B)) ℂ}
    (hM : InSeparableCone M) :
    rawPrivacyAcceptance W M ≤ M.trace.re / (Fintype.card K : ℝ) := by
  obtain ⟨k, left, right, hl, hr, rfl⟩ := hM
  rw [rawPrivacyAcceptance_sum]
  have ht : (∑ j : Fin k, left j ⊗ₖ right j).trace.re =
      ∑ j : Fin k, (left j).trace.re * (right j).trace.re := by
    rw [Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact psd_trace_kronecker_re (hl j) (hr j)
  rw [ht, Finset.sum_div]
  exact Finset.sum_le_sum (fun j hj => rawPrivacyAcceptance_product_psd_le W hW (hl j) (hr j))

theorem rawPrivacyEffect_trace (W : K → Matrix (A × B) (A × B) ℂ)
    (M : Matrix ((K × A) × (K × B)) ((K × A) × (K × B)) ℂ) :
    (rawPrivacyEffect W * M).trace.re = rawPrivacyAcceptance W M := by
  rw [rawPrivacyEffect, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re,
    Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  simp only [rawPrivacyAcceptance, one_div, div_eq_mul_inv, mul_comm, mul_one, smul_eq_mul]

theorem rawPrivacyEffect_separable_le
    (W : K → Matrix (A × B) (A × B) ℂ) (hW : ∀ k, (W k)ᴴ * W k = 1)
    (ρ : Density ((K × A) × (K × B))) (hρ : IsSeparable ρ) :
    (rawPrivacyEffect W * ρ.mat).trace.re ≤ 1 / (Fintype.card K : ℝ) := by
  rw [rawPrivacyEffect_trace]
  simpa only [ρ.normalized, Complex.one_re] using rawPrivacyAcceptance_separableCone_le W hW hρ

def registerFunctionEquiv (I : Type*) : (n : ℕ) → Register I n ≃ (Fin n → I)
  | 0 =>
      { toFun := fun _ i => Fin.elim0 i
        invFun := fun _ => PUnit.unit
        left_inv := by intro x; cases x; rfl
        right_inv := by intro f; funext i; exact Fin.elim0 i }
  | n + 1 => (Equiv.prodCongr (Equiv.refl I) (registerFunctionEquiv I n)).trans
      (Fin.consEquiv (fun _ : Fin (n + 1) => I))

theorem registerFunctionEquiv_head (n : ℕ) (x : I) (r : Register I n) :
    registerFunctionEquiv I (n + 1) (x, r) 0 = x := rfl

theorem registerFunctionEquiv_tail (n : ℕ) (x : I) (r : Register I n) (i : Fin n) :
    registerFunctionEquiv I (n + 1) (x, r) i.succ = registerFunctionEquiv I n r i := rfl

theorem matrix_entries (M : Matrix I I ℂ) (n : ℕ) (r s : Register I n) :
    IndependentLanes.matrix M n r s =
      ∏ i : Fin n, M (registerFunctionEquiv I n r i) (registerFunctionEquiv I n s i) := by
  induction n with
  | zero => cases r; cases s; simp [IndependentLanes.matrix, Register]
  | succ n ih =>
      rcases r with ⟨x, r⟩
      rcases s with ⟨y, s⟩
      rw [Fin.prod_univ_succ]
      change M x y * IndependentLanes.matrix M n r s =
        M x y * ∏ i : Fin n, M (registerFunctionEquiv I n r i) (registerFunctionEquiv I n s i)
      rw [ih]

def piMatrix {L X Y : Type*} [Fintype L]
    (M : L → Matrix X Y ℂ) : Matrix (L → X) (L → Y) ℂ :=
  fun r s => ∏ i, M i (r i) (s i)

theorem piMatrix_mul {L X Y Z : Type*} [Fintype L] [DecidableEq L]
    [Fintype Y] (M : L → Matrix X Y ℂ) (N : L → Matrix Y Z ℂ) :
    piMatrix M * piMatrix N = piMatrix (fun i => M i * N i) := by
  ext r s
  simp only [piMatrix, Matrix.mul_apply]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i : L => fun j : Y => M i (r i) j * N i j (s i))).symm

theorem piMatrix_conjTranspose {L X Y : Type*} [Fintype L]
    (M : L → Matrix X Y ℂ) :
    (piMatrix M)ᴴ = piMatrix (fun i => (M i)ᴴ) := by
  ext r s
  simp [piMatrix, Matrix.conjTranspose_apply]

theorem piMatrix_one {L X : Type*} [Fintype L] [DecidableEq X] :
    piMatrix (fun _ : L => (1 : Matrix X X ℂ)) = 1 := by
  ext r s
  simp [piMatrix, Matrix.one_apply, Fintype.prod_ite_zero, ← funext_iff]

theorem piMatrix_gram {L X : Type*} [Fintype L] [DecidableEq L]
    [Fintype X] [DecidableEq X] (M : L → Matrix X X ℂ)
    (hM : ∀ i, (M i)ᴴ * M i = 1) : (piMatrix M)ᴴ * piMatrix M = 1 := by
  rw [piMatrix_conjTranspose, piMatrix_mul]
  simp only [hM, piMatrix_one]

theorem local_submatrix_separable {A₁ B₁ A₂ B₂ : Type*}
    [Fintype A₁] [Fintype B₁] [Fintype A₂] [Fintype B₂]
    (eA : A₂ ≃ A₁) (eB : B₂ ≃ B₁)
    {M : Matrix (A₁ × B₁) (A₁ × B₁) ℂ} (hM : InSeparableCone M) :
    InSeparableCone (M.submatrix (Equiv.prodCongr eA eB) (Equiv.prodCongr eA eB)) := by
  obtain ⟨k, left, right, hl, hr, rfl⟩ := hM
  refine ⟨k, (fun i => (left i).submatrix eA eA),
    (fun i => (right i).submatrix eB eB), (fun i => (hl i).submatrix eA),
    (fun i => (hr i).submatrix eB), ?_⟩
  ext r s
  simp [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.kronecker_apply]

def functionProdEquiv (L X Y : Type*) : (L → X × Y) ≃ (L → X) × (L → Y) where
  toFun f := (fun i => (f i).1, fun i => (f i).2)
  invFun f i := (f.1 i, f.2 i)
  left_inv := by intro f; rfl
  right_inv := by rintro ⟨f, g⟩; rfl

variable {L : Type*} [Fintype L] [DecidableEq L] {d : ℕ}

def selectedLocalEquiv (X : Type*) (S : Finset L) :
    (L → Fin d × X) ≃ ((S → Fin d) × ((S → X) × ({i : L // i ∉ S} → Fin d × X))) :=
  (Equiv.piEquivPiSubtypeProd (fun i : L => i ∈ S) (fun _ => Fin d × X)).trans
    ((Equiv.prodCongr (functionProdEquiv S (Fin d) X) (Equiv.refl _)).trans
      (Equiv.prodAssoc _ _ _))

def aggregateShieldEquiv (S : Finset L) :
    (((S → A) × ({i : L // i ∉ S} → Fin d × A)) ×
      ((S → B) × ({i : L // i ∉ S} → Fin d × B))) ≃
      ((S → A × B) × (({i : L // i ∉ S} → Fin d × A) ×
        ({i : L // i ∉ S} → Fin d × B))) :=
  (Equiv.prodProdProdComm _ _ _ _).trans
    (Equiv.prodCongr (functionProdEquiv S A B).symm (Equiv.refl _))

def aggregateInputEquiv (S : Finset L) :
    (((S → Fin d) × ((S → A) × ({i : L // i ∉ S} → Fin d × A))) ×
      ((S → Fin d) × ((S → B) × ({i : L // i ∉ S} → Fin d × B)))) ≃
      ((S → (Fin d × A) × (Fin d × B)) ×
        (({i : L // i ∉ S} → Fin d × A) × ({i : L // i ∉ S} → Fin d × B))) where
  toFun r := (fun i => ((r.1.1 i, r.1.2.1 i), (r.2.1 i, r.2.2.1 i)), (r.1.2.2, r.2.2.2))
  invFun r := ((fun i => (r.1 i).1.1, (fun i => (r.1 i).1.2, r.2.1)),
    (fun i => (r.1 i).2.1, (fun i => (r.1 i).2.2, r.2.2)))
  left_inv := by rintro ⟨⟨k, a, r⟩, ⟨k', b, s⟩⟩; rfl
  right_inv := by rintro ⟨f, r, s⟩; rfl

def aggregateShieldUnitary
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (S : Finset L) (k : S → Fin d) :=
  (piMatrix (fun i : S => unitaryMatrix (U (k i))) ⊗ₖ
    (1 : Matrix (({i : L // i ∉ S} → Fin d × A) × ({i : L // i ∉ S} → Fin d × B))
      (({i : L // i ∉ S} → Fin d × A) × ({i : L // i ∉ S} → Fin d × B)) ℂ)).submatrix
        (aggregateShieldEquiv (A := A) (B := B) S) (aggregateShieldEquiv (A := A) (B := B) S)

theorem aggregateShieldUnitary_gram
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (S : Finset L) (k : S → Fin d) :
    (aggregateShieldUnitary U S k)ᴴ * aggregateShieldUnitary U S k = 1 := by
  have hg : (piMatrix (fun i : S => unitaryMatrix (U (k i))))ᴴ *
      piMatrix (fun i : S => unitaryMatrix (U (k i))) = 1 :=
    piMatrix_gram _ (fun i => Matrix.mem_unitaryGroup_iff'.mp (unitaryMatrix_mem_unitary (U (k i))))
  simp only [aggregateShieldUnitary, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, hg, Matrix.conjTranspose_one, Matrix.one_mul,
    Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

theorem piMatrix_smul_const {L X Y : Type*} [Fintype L]
    (c : ℝ) (M : L → Matrix X Y ℂ) :
    piMatrix (fun i => c • M i) = c ^ Fintype.card L • piMatrix M := by
  ext r s
  simp [piMatrix, Finset.prod_mul_distrib, smul_eq_mul]

theorem rawPrivacyMatrix_aggregate
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (S : Finset L) :
    rawPrivacyMatrix (aggregateShieldUnitary U S) =
      (piMatrix (fun _ : S => privacyMatrix U) ⊗ₖ
        (1 : Matrix (({i : L // i ∉ S} → Fin d × A) × ({i : L // i ∉ S} → Fin d × B))
          (({i : L // i ∉ S} → Fin d × A) × ({i : L // i ∉ S} → Fin d × B)) ℂ)).submatrix
            (aggregateShieldEquiv (A := A) (B := B) S) (aggregateInputEquiv (A := A) (B := B) S) := by
  ext s r
  change (if r.1.1 = r.2.1 then
      (∏ i : S, unitaryMatrix (U (r.1.1 i)) (s.1.1 i, s.2.1 i) (r.1.2.1 i, r.2.2.1 i)) *
        (1 : Matrix _ _ ℂ) (s.1.2, s.2.2) (r.1.2.2, r.2.2.2) else 0) =
    (∏ i : S, privacyMatrix U (s.1.1 i, s.2.1 i)
      ((r.1.1 i, r.1.2.1 i), (r.2.1 i, r.2.2.1 i))) *
        (1 : Matrix _ _ ℂ) (s.1.2, s.2.2) (r.1.2.2, r.2.2.2)
  simp only [privacyMatrix_eq_entries, privacyMatrixByEntries, Matrix.of_apply]
  rw [Fintype.prod_ite_zero]
  by_cases h : r.1.1 = r.2.1
  · have hh : ∀ i : S, r.1.1 i = r.2.1 i := congrFun h
    rw [if_pos h, if_pos hh]
  · have hh : ¬ ∀ i : S, r.1.1 i = r.2.1 i := fun hh => h (funext hh)
    rw [if_neg h, if_neg hh, zero_mul]

theorem aggregate_key_factor (S : Finset L) :
    1 / (Fintype.card (S → Fin d) : ℝ) = (1 / (d : ℝ)) ^ S.card := by
  simp [Fintype.card_fun, Nat.cast_pow, one_div, inv_pow]

theorem rawPrivacyEffect_aggregate
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (S : Finset L) :
    rawPrivacyEffect (aggregateShieldUnitary U S) =
      (piMatrix (fun _ : S => privacyEffect U) ⊗ₖ
        (1 : Matrix (({i : L // i ∉ S} → Fin d × A) × ({i : L // i ∉ S} → Fin d × B))
          (({i : L // i ∉ S} → Fin d × A) × ({i : L // i ∉ S} → Fin d × B)) ℂ)).submatrix
            (aggregateInputEquiv (A := A) (B := B) S) (aggregateInputEquiv (A := A) (B := B) S) := by
  rw [rawPrivacyEffect, rawPrivacyMatrix_aggregate, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, piMatrix_conjTranspose, piMatrix_mul,
    aggregate_key_factor]
  simp only [privacyEffect, piMatrix_smul_const, Fintype.card_coe, Matrix.smul_kronecker]
  rfl

def functionSubsetEffect
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (S : Finset L) : Matrix (L → (Fin d × A) × (Fin d × B))
      (L → (Fin d × A) × (Fin d × B)) ℂ :=
  piMatrix (fun i : L => if i ∈ S then privacyEffect U else 1)

def splitLaneEquiv (S : Finset L) :
    (L → (Fin d × A) × (Fin d × B)) ≃
      ((S → (Fin d × A) × (Fin d × B)) ×
        (({i : L // i ∉ S} → Fin d × A) × ({i : L // i ∉ S} → Fin d × B))) :=
  (Equiv.piEquivPiSubtypeProd (fun i : L => i ∈ S)
    (fun _ => (Fin d × A) × (Fin d × B))).trans
      (Equiv.prodCongr (Equiv.refl _) (functionProdEquiv _ _ _))

theorem functionSubsetEffect_factor
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (S : Finset L) :
    functionSubsetEffect U S =
      (piMatrix (fun _ : S => privacyEffect U) ⊗ₖ
        (1 : Matrix (({i : L // i ∉ S} → Fin d × A) × ({i : L // i ∉ S} → Fin d × B))
          (({i : L // i ∉ S} → Fin d × A) × ({i : L // i ∉ S} → Fin d × B)) ℂ)).submatrix
            (splitLaneEquiv (A := A) (B := B) S) (splitLaneEquiv (A := A) (B := B) S) := by
  ext r s
  have hI : (1 : Matrix _ _ ℂ)
      ((fun i : {i : L // i ∉ S} => (r i).1), (fun i : {i : L // i ∉ S} => (r i).2))
      ((fun i : {i : L // i ∉ S} => (s i).1), (fun i : {i : L // i ∉ S} => (s i).2)) =
        ∏ i : {i : L // i ∉ S}, (1 : Matrix ((Fin d × A) × (Fin d × B)) _ ℂ) (r i) (s i) := by
    have he := Matrix.submatrix_one_equiv
      (functionProdEquiv {i : L // i ∉ S} (Fin d × A) (Fin d × B)) (α := ℂ)
    rw [← piMatrix_one] at he
    exact congrArg (fun M => M (fun i => r i) (fun i => s i)) he
  change (∏ i : L, (if i ∈ S then privacyEffect U else 1) (r i) (s i)) =
    (∏ i : S, privacyEffect U (r i) (s i)) * (1 : Matrix _ _ ℂ)
      ((fun i : {i : L // i ∉ S} => (r i).1), (fun i : {i : L // i ∉ S} => (r i).2))
      ((fun i : {i : L // i ∉ S} => (s i).1), (fun i : {i : L // i ∉ S} => (s i).2))
  rw [hI]
  have hp := Fintype.prod_subtype_mul_prod_subtype (fun i : L => i ∈ S)
    (fun i => (if i ∈ S then privacyEffect U else 1) (r i) (s i))
  have hs : (∏ i ∈ @Finset.univ {i : L // i ∈ S} (Subtype.fintype (fun i : L => i ∈ S)),
      (if (i : L) ∈ S then privacyEffect U else 1) (r i) (s i)) =
      ∏ i : S, privacyEffect U (r i) (s i) := by
    apply Finset.prod_congr
    · ext i; simp
    · intro i hi
      rw [if_pos i.property]
  have ht : (∏ i ∈ @Finset.univ {i : L // i ∉ S} (Subtype.fintype (fun i : L => i ∉ S)),
      (if (i : L) ∈ S then privacyEffect U else 1) (r i) (s i)) =
      ∏ i : {i : L // i ∉ S}, (1 : Matrix ((Fin d × A) × (Fin d × B)) _ ℂ) (r i) (s i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [if_neg i.property]
  exact hp.symm.trans (congrArg₂ (fun x y : ℂ => x * y) hs ht)

theorem functionSubsetEffect_local_aggregate
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (S : Finset L) :
    (functionSubsetEffect U S).submatrix
      (functionProdEquiv L (Fin d × A) (Fin d × B)).symm
      (functionProdEquiv L (Fin d × A) (Fin d × B)).symm =
      (rawPrivacyEffect (aggregateShieldUnitary U S)).submatrix
        (Equiv.prodCongr (selectedLocalEquiv (d := d) A S) (selectedLocalEquiv (d := d) B S))
        (Equiv.prodCongr (selectedLocalEquiv (d := d) A S) (selectedLocalEquiv (d := d) B S)) := by
  rw [functionSubsetEffect_factor, rawPrivacyEffect_aggregate]
  rfl

theorem trace_submatrix_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (M : Matrix X X ℂ) (e : Y ≃ X) : (M.submatrix e e).trace = M.trace := by
  exact e.sum_comp (fun i => M i i)

theorem trace_submatrix_mul_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (M N : Matrix X X ℂ) (e : Y ≃ X) :
    (M.submatrix e e * N.submatrix e e).trace = (M * N).trace := by
  rw [Matrix.submatrix_mul_equiv]
  exact trace_submatrix_equiv _ e

theorem functionSubsetEffect_separable_le
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (S : Finset L) {M : Matrix ((L → Fin d × A) × (L → Fin d × B))
      ((L → Fin d × A) × (L → Fin d × B)) ℂ}
    (hM : InSeparableCone M) (hTr : M.trace = 1) :
    ((functionSubsetEffect U S).submatrix
      (functionProdEquiv L (Fin d × A) (Fin d × B)).symm
      (functionProdEquiv L (Fin d × A) (Fin d × B)).symm * M).trace.re ≤
        (1 / (d : ℝ)) ^ S.card := by
  let eA := (selectedLocalEquiv (d := d) A S).symm
  let eB := (selectedLocalEquiv (d := d) B S).symm
  let e := Equiv.prodCongr eA eB
  let E := (functionSubsetEffect U S).submatrix
    (functionProdEquiv L (Fin d × A) (Fin d × B)).symm
    (functionProdEquiv L (Fin d × A) (Fin d × B)).symm
  have he : E.submatrix e e = rawPrivacyEffect (aggregateShieldUnitary U S) := by
    dsimp only [E]
    rw [functionSubsetEffect_local_aggregate]
    ext r s
    rcases r with ⟨rA, rB⟩
    rcases s with ⟨sA, sB⟩
    simp [Matrix.submatrix_apply, e, eA, eB]
  have hb := rawPrivacyAcceptance_separableCone_le (aggregateShieldUnitary U S)
    (fun k => (aggregateShieldUnitary_gram U S k).trans (by
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h])) (local_submatrix_separable eA eB hM)
  rw [← rawPrivacyEffect_trace, trace_submatrix_equiv M e, hTr, Complex.one_re,
    aggregate_key_factor] at hb
  have hp := trace_submatrix_mul_equiv E M e
  rw [he] at hp
  exact (congrArg Complex.re hp).symm.le.trans hb

theorem registerFunctionEquiv_pair (n : ℕ)
    (a : Register A n) (b : Register B n) :
    registerFunctionEquiv (A × B) n ((pairEquiv A B n).symm (a, b)) =
      (functionProdEquiv (Fin n) A B).symm
        (registerFunctionEquiv A n a, registerFunctionEquiv B n b) := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      rcases a with ⟨x, a⟩
      rcases b with ⟨y, b⟩
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact congrFun (ih a b) j

def privacySubsetEffect
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (N : ℕ) (S : Finset (Fin N)) :
    Matrix (Register ((Fin d × A) × (Fin d × B)) N)
      (Register ((Fin d × A) × (Fin d × B)) N) ℂ :=
  (functionSubsetEffect U S).submatrix
    (registerFunctionEquiv ((Fin d × A) × (Fin d × B)) N)
    (registerFunctionEquiv ((Fin d × A) × (Fin d × B)) N)

def collectiveSubsetEffect
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (N : ℕ) (S : Finset (Fin N)) :=
  (privacySubsetEffect U N S).submatrix
    (pairEquiv (Fin d × A) (Fin d × B) N).symm
    (pairEquiv (Fin d × A) (Fin d × B) N).symm

theorem collectiveSubsetEffect_function_chart
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (N : ℕ) (S : Finset (Fin N)) :
    collectiveSubsetEffect U N S =
      ((functionSubsetEffect U S).submatrix
        (functionProdEquiv (Fin N) (Fin d × A) (Fin d × B)).symm
        (functionProdEquiv (Fin N) (Fin d × A) (Fin d × B)).symm).submatrix
          (Equiv.prodCongr (registerFunctionEquiv (Fin d × A) N)
            (registerFunctionEquiv (Fin d × B) N))
          (Equiv.prodCongr (registerFunctionEquiv (Fin d × A) N)
            (registerFunctionEquiv (Fin d × B) N)) := by
  ext r s
  rcases r with ⟨rA, rB⟩
  rcases s with ⟨sA, sB⟩
  simp only [collectiveSubsetEffect, privacySubsetEffect, Matrix.submatrix_apply,
    registerFunctionEquiv_pair, Equiv.prodCongr_apply]
  rfl

theorem privacySubsetEffect_separable_le
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (N : ℕ) (S : Finset (Fin N))
    (ρ : Density (Register (Fin d × A) N × Register (Fin d × B) N))
    (hρ : IsSeparable ρ) :
    (collectiveSubsetEffect U N S * ρ.mat).trace.re ≤ (1 / (d : ℝ)) ^ S.card := by
  let eA := (registerFunctionEquiv (Fin d × A) N).symm
  let eB := (registerFunctionEquiv (Fin d × B) N).symm
  let e := Equiv.prodCongr eA eB
  have hcone := local_submatrix_separable eA eB hρ
  have htr : (ρ.mat.submatrix e e).trace = 1 :=
    (trace_submatrix_equiv ρ.mat e).trans ρ.normalized
  have hb := functionSubsetEffect_separable_le U S hcone htr
  have he : (collectiveSubsetEffect U N S).submatrix e e =
      (functionSubsetEffect U S).submatrix
        (functionProdEquiv (Fin N) (Fin d × A) (Fin d × B)).symm
        (functionProdEquiv (Fin N) (Fin d × A) (Fin d × B)).symm := by
    rw [collectiveSubsetEffect_function_chart]
    ext r s
    rcases r with ⟨rA, rB⟩
    rcases s with ⟨sA, sB⟩
    simp [Matrix.submatrix_apply, e, eA, eB]
  have hp := trace_submatrix_mul_equiv (collectiveSubsetEffect U N S) ρ.mat e
  rw [he] at hp
  exact (congrArg Complex.re hp).symm.le.trans hb

theorem functionSubsetEffect_entries
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (S : Finset L) (r s : L → (Fin d × A) × (Fin d × B)) :
    functionSubsetEffect U S r s =
      (∏ i ∈ S, privacyEffect U (r i) (s i)) *
        ∏ i ∈ Sᶜ, (1 : Matrix ((Fin d × A) × (Fin d × B)) _ ℂ) (r i) (s i) := by
  simp only [functionSubsetEffect, piMatrix, ite_apply]
  have hi (i : L) : (if i ∈ S then privacyEffect U else 1) (r i) (s i) =
      if i ∈ S then privacyEffect U (r i) (s i) else
        (1 : Matrix ((Fin d × A) × (Fin d × B)) _ ℂ) (r i) (s i) := by
    by_cases h : i ∈ S <;> simp [h]
  simp_rw [hi]
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_notMem_eq_sdiff,
    ← Finset.compl_eq_univ_sdiff]

theorem piMatrix_affine_expansion
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (t : ℝ) :
    piMatrix (fun _ : L => (1 : Matrix ((Fin d × A) × (Fin d × B)) _ ℂ) + t • privacyEffect U) =
      ∑ S : Finset L, t ^ S.card • functionSubsetEffect U S := by
  ext r s
  simp only [piMatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply]
  have hi (i : L) : (1 : Matrix ((Fin d × A) × (Fin d × B)) _ ℂ) (r i) (s i) +
      t • privacyEffect U (r i) (s i) = t • privacyEffect U (r i) (s i) +
        (1 : Matrix ((Fin d × A) × (Fin d × B)) _ ℂ) (r i) (s i) := add_comm _ _
  simp_rw [hi]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro S hS
  rw [functionSubsetEffect_entries]
  simp [Finset.prod_mul_distrib, mul_assoc, mul_comm, mul_left_comm]

theorem matrix_affine_expansion
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (N : ℕ) (t : ℝ) :
    IndependentLanes.matrix (1 + t • privacyEffect U) N =
      ∑ S : Finset (Fin N), t ^ S.card • privacySubsetEffect U N S := by
  ext r s
  rw [matrix_entries]
  simpa only [piMatrix, Matrix.sum_apply, Matrix.smul_apply, privacySubsetEffect,
    Matrix.submatrix_apply] using congrArg
      (fun M => M (registerFunctionEquiv ((Fin d × A) × (Fin d × B)) N r)
        (registerFunctionEquiv ((Fin d × A) × (Fin d × B)) N s))
      (piMatrix_affine_expansion (L := Fin N) U t)

theorem privacy_mgf_separable_le
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (N : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (ρ : Density (Register (Fin d × A) N × Register (Fin d × B) N))
    (hρ : IsSeparable ρ) :
    ((IndependentLanes.matrix (1 + t • privacyEffect U) N).submatrix
      (pairEquiv (Fin d × A) (Fin d × B) N).symm
      (pairEquiv (Fin d × A) (Fin d × B) N).symm * ρ.mat).trace.re ≤
        (1 + t / (d : ℝ)) ^ N := by
  have hexp : (IndependentLanes.matrix (1 + t • privacyEffect U) N).submatrix
      (pairEquiv (Fin d × A) (Fin d × B) N).symm
      (pairEquiv (Fin d × A) (Fin d × B) N).symm =
        ∑ S : Finset (Fin N), t ^ S.card • collectiveSubsetEffect U N S := by
    rw [matrix_affine_expansion]
    ext r s
    simp [collectiveSubsetEffect, Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply]
  rw [hexp]
  simp only [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum, Matrix.smul_mul,
    Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  calc
    _ ≤ ∑ S : Finset (Fin N), t ^ S.card * (1 / (d : ℝ)) ^ S.card := by
      exact Finset.sum_le_sum (fun S hS => mul_le_mul_of_nonneg_left
        (privacySubsetEffect_separable_le U N S ρ hρ) (pow_nonneg ht _))
    _ = (1 + t / (d : ℝ)) ^ N := by
      have hc := Fintype.prod_add (fun _ : Fin N => t / (d : ℝ)) (fun _ => (1 : ℝ))
      simpa [mul_pow, div_eq_mul_inv, add_comm] using hc.symm

theorem functionSubsetEffect_mul
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (S T : Finset L) :
    functionSubsetEffect U S * functionSubsetEffect U T = functionSubsetEffect U (S ∪ T) := by
  rw [functionSubsetEffect, functionSubsetEffect, piMatrix_mul]
  congr 1
  funext i
  by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
    simp [functionSubsetEffect, hs, ht, privacyEffect_projection U hd]

theorem privacySubsetEffect_mul
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (N : ℕ) (S T : Finset (Fin N)) :
    privacySubsetEffect U N S * privacySubsetEffect U N T = privacySubsetEffect U N (S ∪ T) := by
  simp only [privacySubsetEffect, Matrix.submatrix_mul_equiv, functionSubsetEffect_mul U hd]

theorem privacySubsetEffect_commute
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (hd : 0 < d) (N : ℕ) (S T : Finset (Fin N)) :
    Commute (privacySubsetEffect U N S) (privacySubsetEffect U N T) := by
  show _ * _ = _ * _
  simp only [privacySubsetEffect_mul U hd, Finset.union_comm]

theorem privacySubsetEffect_empty
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B)) (N : ℕ) :
    privacySubsetEffect U N ∅ = 1 := by
  simp only [privacySubsetEffect, functionSubsetEffect, Finset.notMem_empty,
    if_false, piMatrix_one, Matrix.submatrix_one_equiv]

theorem privacy_mgf_separable_le_complex
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (N : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (ρ : Density (Register (Fin d × A) N × Register (Fin d × B) N))
    (hρ : IsSeparable ρ) :
    ((IndependentLanes.matrix (1 + (t : ℂ) • privacyEffect U) N).submatrix
      (pairEquiv (Fin d × A) (Fin d × B) N).symm
      (pairEquiv (Fin d × A) (Fin d × B) N).symm * ρ.mat).trace.re ≤
        (1 + t / (d : ℝ)) ^ N := by
  have hc : (t : ℂ) • privacyEffect U = t • privacyEffect U := by
    ext r s
    simp [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [hc]
  exact privacy_mgf_separable_le U N t ht ρ hρ

theorem rawPrivacyMatrix_coisometry
    (W : K → Matrix (A × B) (A × B) ℂ) (hW : ∀ k, (W k)ᴴ * W k = 1) :
    rawPrivacyMatrix W * (rawPrivacyMatrix W)ᴴ =
      (Fintype.card K : ℂ) • (1 : Matrix (A × B) (A × B) ℂ) := by
  have hu (k : K) : W k * (W k)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_unitaryGroup_iff'.mpr (hW k))
  ext s t
  have hs : (rawPrivacyMatrix W * (rawPrivacyMatrix W)ᴴ) s t =
      ∑ k : K, (W k * (W k)ᴴ) s t := by
    simp [rawPrivacyMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, apply_ite, ite_mul, mul_ite]
  rw [hs]
  simp [hu, Matrix.smul_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

def rawPrivateEmbedding (W : K → Matrix (A × B) (A × B) ℂ) :=
  ((Real.sqrt (Fintype.card K : ℝ))⁻¹ : ℂ) • (rawPrivacyMatrix W)ᴴ

theorem rawPrivateEmbedding_isometry
    (W : K → Matrix (A × B) (A × B) ℂ) (hW : ∀ k, (W k)ᴴ * W k = 1)
    (hK : 0 < Fintype.card K) :
    (rawPrivateEmbedding W)ᴴ * rawPrivateEmbedding W = 1 := by
  have hkp : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr hK
  have hsq : (Real.sqrt (Fintype.card K : ℝ) : ℂ) *
      (Real.sqrt (Fintype.card K : ℝ) : ℂ) = (Fintype.card K : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hkp.le]
    norm_cast
  have hsz : (Real.sqrt (Fintype.card K : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hkp).ne'
  have hc : ((Real.sqrt (Fintype.card K : ℝ))⁻¹ : ℂ) *
      ((Real.sqrt (Fintype.card K : ℝ))⁻¹ : ℂ) * (Fintype.card K : ℂ) = 1 := by
    push_cast
    rw [← hsq]
    field_simp
  rw [rawPrivateEmbedding, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul, rawPrivacyMatrix_coisometry W hW]
  simp [Complex.real_smul, smul_smul, ← mul_assoc, hc]

theorem rawPrivacyEffect_eq_embedding_range
    (W : K → Matrix (A × B) (A × B) ℂ) :
    rawPrivacyEffect W = rawPrivateEmbedding W * (rawPrivateEmbedding W)ᴴ := by
  have hc : ((Real.sqrt (Fintype.card K : ℝ))⁻¹ : ℂ) *
      ((Real.sqrt (Fintype.card K : ℝ))⁻¹ : ℂ) = (1 / (Fintype.card K : ℝ) : ℂ) := by
    have hr : (Real.sqrt (Fintype.card K : ℝ))⁻¹ * (Real.sqrt (Fintype.card K : ℝ))⁻¹ =
        1 / (Fintype.card K : ℝ) := by
      rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _), one_div]
    exact_mod_cast hr
  rw [rawPrivateEmbedding, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose,
    Matrix.smul_mul, Matrix.mul_smul]
  ext r s
  simp [rawPrivacyEffect, Matrix.smul_apply, smul_smul, Complex.real_smul,
    ← mul_assoc, hc]

theorem privacy_dyadic_mgf_separable_le
    (U : Fin d → EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B))
    (N : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (ρ : Density (Register (Fin d × A) N × Register (Fin d × B) N))
    (hρ : IsSeparable ρ) :
    ((IndependentLanes.matrix (1 + (((2 : ℝ) ^ s - 1 : ℝ) : ℂ) • privacyEffect U) N).submatrix
      (pairEquiv (Fin d × A) (Fin d × B) N).symm
      (pairEquiv (Fin d × A) (Fin d × B) N).symm * ρ.mat).trace.re ≤
        (1 + ((2 : ℝ) ^ s - 1) / (d : ℝ)) ^ N := by
  exact privacy_mgf_separable_le_complex U N ((2 : ℝ) ^ s - 1)
    (sub_nonneg.mpr (Real.one_le_rpow (by norm_num) hs)) ρ hρ

end QuantumProver.AmplitudeDamping.SecretKey.ProductPrivacyTest
