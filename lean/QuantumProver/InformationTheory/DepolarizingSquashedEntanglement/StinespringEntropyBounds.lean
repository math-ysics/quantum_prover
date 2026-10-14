import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.Definitions
import QuantumProver.InformationTheory.DepolarizingSquashedEntanglement.BoundaryEntropyBounds
import QuantumProver.InformationTheory.SuperchannelDiscrimination.TestingTheorems

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

noncomputable section

open Matrix Filter
open scoped BigOperators ComplexOrder Matrix Kronecker Matrix.Norms.L2Operator
  ContinuousFunctionalCalculus

namespace QuantumProver.DepolarizingSquashedEntanglement

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem hsSq_eq_c1HsMass (M : Matrix I J ℂ) : hsSq M = c1HsMass M :=
  c1_trace_gram M

theorem hsSq_nonneg (M : Matrix I J ℂ) : 0 ≤ hsSq M := by
  rw [hsSq_eq_c1HsMass]
  exact c1HsMass_nonneg M

theorem hsSq_eq_zero_iff (M : Matrix I J ℂ) : hsSq M = 0 ↔ M = 0 := by
  constructor
  · intro h
    rw [hsSq_eq_c1HsMass, c1HsMass] at h
    have hrows := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg (M i j)))).mp h
    ext i j
    have hr : (∑ j, Complex.normSq (M i j)) = 0 := hrows i (Finset.mem_univ i)
    have hcols := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (M i j))).mp hr
    exact Complex.normSq_eq_zero.mp (hcols j (Finset.mem_univ j))
  · intro h
    simp [h, hsSq]

theorem binaryPinch_fromBlocks (A : Matrix I I ℂ) (B : Matrix J J ℂ)
    (X : Matrix I J ℂ) (Y : Matrix J I ℂ) :
    binaryPinch (Matrix.fromBlocks A X Y B) = Matrix.fromBlocks A 0 0 B := by
  ext x y
  cases x <;> cases y <;> rfl

theorem binaryPinch_trace (ρ : QMatrix (I ⊕ J)) :
    Matrix.trace (binaryPinch ρ) = Matrix.trace ρ := by
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro x hx
  cases x <;> rfl

@[simp] theorem binaryCoherenceNat_diagonal (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    binaryCoherenceNat (Matrix.fromBlocks A 0 0 B) = 0 := by
  unfold binaryCoherenceNat
  rw [binaryPinch_fromBlocks]
  exact sub_self _

theorem binaryCoherenceNat_square_zero_noise
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) (Z : Matrix J I ℂ)
    (hZ : hsSq Z = 0) :
    binaryCoherenceNat (c1Binary A B Z * c1Binary A B Z) = 0 := by
  have hz : Z = 0 := (hsSq_eq_zero_iff Z).mp hZ
  subst Z
  rw [c1Binary_square_blocks]
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  exact binaryCoherenceNat_diagonal _ _

theorem hermitian_eq_c1Binary {H : QMatrix (I ⊕ J)} (hH : H.IsHermitian) :
    H = c1Binary (H.submatrix Sum.inl Sum.inl) (H.submatrix Sum.inr Sum.inr)
      (H.submatrix Sum.inr Sum.inl) := by
  ext x y
  cases x with
  | inl i =>
    cases y with
    | inl k => rfl
    | inr j => exact (hH.apply (Sum.inl i) (Sum.inr j)).symm
  | inr j => cases y <;> rfl

theorem hermitian_two_noise_le_trace {H : QMatrix (I ⊕ J)} (hH : H.IsHermitian) :
    2*hsSq (H.submatrix Sum.inr Sum.inl) ≤ (Matrix.trace (H*H)).re := by
  have hA := hH.submatrix (Sum.inl : I → I ⊕ J)
  have hB := hH.submatrix (Sum.inr : J → I ⊕ J)
  have h := c1_two_noise_le_trace (H.submatrix Sum.inr Sum.inl) hA hB
  change 2*hsSq (H.submatrix Sum.inr Sum.inl) ≤ _ at h
  rw [← hermitian_eq_c1Binary hH] at h
  exact h

theorem binaryCoherenceNat_square_at_two_noise
    {A : Matrix I I ℂ} {B : Matrix J J ℂ} (Z : Matrix J I ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (ht : (Matrix.trace (c1Binary A B Z * c1Binary A B Z)).re = 2*hsSq Z) :
    binaryCoherenceNat (c1Binary A B Z * c1Binary A B Z) = 0 := by
  have hH := c1Binary_isHermitian Z hA hB
  have hmass : c1HsMass A + c1HsMass B = 0 := by
    have htrace := c1_trace_gram (c1Binary A B Z)
    rw [hH.eq, c1Binary_hs_mass] at htrace
    rw [ht, hsSq_eq_c1HsMass] at htrace
    linarith
  have ha : hsSq A = 0 := by
    rw [hsSq_eq_c1HsMass]
    linarith [c1HsMass_nonneg A, c1HsMass_nonneg B]
  have hb : hsSq B = 0 := by
    rw [hsSq_eq_c1HsMass]
    linarith [c1HsMass_nonneg A, c1HsMass_nonneg B]
  have ha0 := (hsSq_eq_zero_iff A).mp ha
  have hb0 := (hsSq_eq_zero_iff B).mp hb
  subst A
  subst B
  rw [c1Binary_square_blocks]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  exact binaryCoherenceNat_diagonal _ _

theorem c1_uniform_remainder_identity {t u : ℝ} (hu : 0 < u) (htu : u < t) :
    u*(Real.log (t/u) + 4 + 2*Real.log (t/u)/(t/u-1)) =
      u*Real.log (t/u) + 4*u + 2*u^2/(t-u)*Real.log (t/u) := by
  have hun : u ≠ 0 := ne_of_gt hu
  have htn : t-u ≠ 0 := ne_of_gt (sub_pos.mpr htu)
  have hrn : t/u-1 ≠ 0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    apply (lt_div_iff₀ hu).2
    simpa using htu
  field_simp

theorem c1_uniform_remainder_bound {t u : ℝ} (hu : 0 < u) (htu : 2*u ≤ t) :
    2*u^2/(t-u)*Real.log (t/u) ≤ 4*(u^2/t)*Real.log (t/u) := by
  have ht : 0 < t := by linarith
  have htu' : 0 < t-u := by linarith
  have hm : 1 ≤ t/u := (le_div_iff₀ hu).2 (by linarith)
  have hlog : 0 ≤ Real.log (t/u) := Real.log_nonneg hm
  have hratio : 2*u^2/(t-u) ≤ 4*u^2/t := by
    apply (div_le_div_iff₀ htu' ht).2
    nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr htu)]
  have h := mul_le_mul_of_nonneg_right hratio hlog
  convert h using 1 <;> ring

theorem c1_hermitian_square_posSemidef {H : QMatrix I} (hH : H.IsHermitian) :
    (H*H).PosSemidef := by
  simpa only [hH.eq] using Matrix.posSemidef_conjTranspose_mul_self H

theorem c1_square_diagonal_posSemidef {A : QMatrix I} {B : QMatrix J}
    (Z : Matrix J I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A*A + Zᴴ*Z).PosSemidef ∧ (Z*Zᴴ + B*B).PosSemidef := by
  exact ⟨(c1_hermitian_square_posSemidef hA).add
      (Matrix.posSemidef_conjTranspose_mul_self Z),
    (Matrix.posSemidef_self_mul_conjTranspose Z).add
      (c1_hermitian_square_posSemidef hB)⟩

theorem c1_regularized_posDef {X : QMatrix I} (hX : X.PosSemidef)
    {x : ℝ} (hx : 0 < x) : (X + x • (1 : QMatrix I)).PosDef := by
  exact Matrix.PosDef.posSemidef_add hX (Matrix.PosDef.one.smul hx)

theorem c1_weighted_cross_square {H W : QMatrix I}
    (hH : H.IsHermitian) (hW : W.IsHermitian) {v : ℝ} (hv : v ≠ 0) :
    (v^2 • (H*H) + (v⁻¹)^2 • (W*W) + H*W + W*H).PosSemidef := by
  let T : QMatrix I := v • H + v⁻¹ • W
  have hT : T.IsHermitian :=
    (hH.smul (IsSelfAdjoint.all v)).add (hW.smul (IsSelfAdjoint.all v⁻¹))
  have heq : T*T = v^2 • (H*H) + (v⁻¹)^2 • (W*W) + H*W + W*H := by
    dsimp [T]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_smul, mul_inv_cancel₀ hv, inv_mul_cancel₀ hv, one_smul, pow_two]
    abel
  rw [← heq]
  exact c1_hermitian_square_posSemidef hT

theorem c1_young_difference_posSemidef {H W : QMatrix I}
    (hH : H.IsHermitian) (hW : W.IsHermitian) {v : ℝ} (hv : v ≠ 0) :
    ((1+v^2) • (H*H) + (2+(v⁻¹)^2) • (W*W) -
      ((H-W)*(H-W) + W*W)).PosSemidef := by
  have heq : (1+v^2) • (H*H) + (2+(v⁻¹)^2) • (W*W) -
      ((H-W)*(H-W) + W*W) =
      v^2 • (H*H) + (v⁻¹)^2 • (W*W) + H*W + W*H := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, add_smul, one_smul, two_smul]
    abel
  rw [heq]
  exact c1_weighted_cross_square hH hW hv

theorem entropyNat_eq_neg_entropyTrace (R : QMatrix I) :
    entropyNat R = -QuantumProver.SuperchannelDiscrimination.EntropyContinuity.entropyTrace R := by
  simp only [entropyNat, QuantumProver.SuperchannelDiscrimination.EntropyContinuity.entropyTrace,
    Real.negMulLog_eq_neg, cfc_neg, Matrix.trace_neg, Complex.neg_re]

theorem entropyNat_spectral {R : QMatrix I} (hR : R.IsHermitian) :
    entropyNat R = ∑ i, Real.negMulLog (hR.eigenvalues i) :=
  QuantumProver.SuperchannelDiscrimination.Klein.trace_cfc_eq_sum Real.negMulLog hR

theorem tendsto_entropyNat {α : Type*} {l : Filter α} {X : α → QMatrix I}
    {A : QMatrix I} (hX : Filter.Tendsto X l (nhds A))
    (hHerm : ∀ᶠ x in l, (X x).IsHermitian) (hA : A.IsHermitian) :
    Filter.Tendsto (fun x => entropyNat (X x)) l (nhds (entropyNat A)) := by
  simp_rw [entropyNat_eq_neg_entropyTrace]
  exact (QuantumProver.SuperchannelDiscrimination.EntropyContinuity.tendsto_entropyTrace
    hX hHerm hA).neg

theorem c1_entropy_regularization_limit {X : QMatrix I} (hX : X.IsHermitian) :
    Filter.Tendsto (fun x : ℝ => entropyNat (X + x • (1 : QMatrix I)))
      (nhds 0) (nhds (entropyNat X)) := by
  have hlim : Filter.Tendsto (fun x : ℝ => X + x • (1 : QMatrix I))
      (nhds 0) (nhds X) := by
    have hc : Continuous (fun x : ℝ => X + x • (1 : QMatrix I)) := by fun_prop
    simpa using hc.tendsto (0 : ℝ)
  have hHerm : ∀ x : ℝ, (X + x • (1 : QMatrix I)).IsHermitian := by
    intro x
    exact hX.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all x))
  exact tendsto_entropyNat hlim (Filter.Eventually.of_forall hHerm) hX

def c1PauliAxis (k : Fin 3) : QMatrix Qubit :=
  pauli ⟨k.val + 1, by omega⟩

def c1PauliEffect (k : Fin 3) (b : Fin 2) : QMatrix Qubit :=
  (1/2 : ℝ) • ((1 : QMatrix Qubit) +
    (if b = 0 then (1 : ℝ) else -1) • c1PauliAxis k)

theorem c1PauliEffect_isHermitian (k : Fin 3) (b : Fin 2) :
    (c1PauliEffect k b).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases k <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [c1PauliEffect, c1PauliAxis, pauli, Matrix.conjTranspose_apply,
      Matrix.smul_apply, Complex.star_def]

theorem c1PauliEffect_idempotent (k : Fin 3) (b : Fin 2) :
    c1PauliEffect k b * c1PauliEffect k b = c1PauliEffect k b := by
  ext i j
  fin_cases k <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [c1PauliEffect, c1PauliAxis, pauli, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_succ, Matrix.smul_apply, Matrix.one_apply,
      Complex.I_mul_I] <;> ring_nf <;> norm_num [pow_two, Complex.I_mul_I]

theorem c1PauliEffect_posSemidef (k : Fin 3) (b : Fin 2) :
    (c1PauliEffect k b).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (c1PauliEffect k b)
  simpa only [(c1PauliEffect_isHermitian k b).eq,
    c1PauliEffect_idempotent k b] using h

theorem c1PauliEffect_complete (k : Fin 3) :
    (∑ b : Fin 2, c1PauliEffect k b) = (1 : QMatrix Qubit) := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [c1PauliEffect, c1PauliAxis, pauli, Fin.sum_univ_succ,
      Matrix.smul_apply, Finset.sum_apply]

def c1OneWayAliceEffect (x : Fin 3 × Fin 2) : QMatrix Qubit :=
  (1/3 : ℝ) • (c1PauliEffect x.1 x.2).transpose

def c1OneWayBobEffect (x : Fin 3 × Fin 2) (y : Fin 2) : QMatrix Qubit :=
  c1PauliEffect x.1 y

theorem c1OneWayAliceEffect_posSemidef (x : Fin 3 × Fin 2) :
    (c1OneWayAliceEffect x).PosSemidef :=
  ((c1PauliEffect_posSemidef x.1 x.2).transpose).smul (by norm_num)

theorem c1OneWayBobEffect_complete (x : Fin 3 × Fin 2) :
    (∑ y : Fin 2, c1OneWayBobEffect x y) = (1 : QMatrix Qubit) :=
  c1PauliEffect_complete x.1

def c1OneWayAccept : QMatrix (Qubit × Qubit) :=
  ∑ x : Fin 3 × Fin 2,
    c1OneWayAliceEffect x ⊗ₖ c1OneWayBobEffect x x.2

theorem c1OneWayAccept_posSemidef : c1OneWayAccept.PosSemidef := by
  unfold c1OneWayAccept
  exact Matrix.posSemidef_sum Finset.univ (fun x _ =>
    (c1OneWayAliceEffect_posSemidef x).kronecker
      (c1PauliEffect_posSemidef x.1 x.2))

theorem c1OneWayAliceEffect_complete :
    (∑ x : Fin 3 × Fin 2, c1OneWayAliceEffect x) = (1 : QMatrix Qubit) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [c1OneWayAliceEffect, c1PauliEffect, c1PauliAxis, pauli,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.smul_apply,
      Matrix.transpose_apply, Finset.sum_apply]

def c1BellProjector : QMatrix (Qubit × Qubit) :=
  (1/2 : ℝ) • pureDensity (fun x : Qubit × Qubit =>
    if x.1 = x.2 then (1 : ℂ) else 0)

theorem c1BellProjector_posSemidef : c1BellProjector.PosSemidef := by
  exact (QuantumProver.WernerEndpoint.pureDensity_posSemidef _).smul (by norm_num)

theorem c1BellProjector_trace : Matrix.trace c1BellProjector = 1 := by
  norm_num [c1BellProjector, pureDensity, QuantumProver.WernerEndpoint.pureDensity,
    QuantumProver.WernerEndpoint.crossDensity, Matrix.trace, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Matrix.smul_apply]

theorem c1OneWayAccept_eq :
    c1OneWayAccept = (1/3 : ℝ) •
      ((1 : QMatrix (Qubit × Qubit)) + (2 : ℝ) • c1BellProjector) := by
  ext i j
  rcases i with ⟨i₁,i₂⟩
  rcases j with ⟨j₁,j₂⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    norm_num [c1OneWayAccept, c1OneWayAliceEffect, c1OneWayBobEffect,
      c1PauliEffect, c1PauliAxis, pauli, c1BellProjector, pureDensity,
      QuantumProver.WernerEndpoint.pureDensity, QuantumProver.WernerEndpoint.crossDensity,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.kroneckerMap_apply,
      Matrix.smul_apply, Matrix.transpose_apply, Finset.sum_apply,
      Complex.I_mul_I] <;> ring_nf <;> norm_num [pow_two, Complex.I_mul_I]

theorem c1_qubit_complement_posSemidef {A : QMatrix Qubit}
    (hA : A.PosSemidef) (ht : Matrix.trace A = 1) :
    ((1 : QMatrix Qubit) - A).PosSemidef := by
  let K : QMatrix Qubit := !![0,-1;1,0]
  have htrace : A 0 0 + A 1 1 = 1 := by
    simpa only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] using ht
  have heq : (1 : QMatrix Qubit) - A = K * A.transpose * Kᴴ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [K, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.vecMul, dotProduct] <;>
      linear_combination -htrace
  rw [heq]
  exact hA.transpose.mul_mul_conjTranspose_same K

theorem c1Bell_product_overlap (A B : QMatrix Qubit) :
    (Matrix.trace (c1BellProjector * (A ⊗ₖ B))).re =
      (1/2 : ℝ) * (Matrix.trace (A.transpose * B)).re := by
  have h : Matrix.trace (c1BellProjector * (A ⊗ₖ B)) =
      (1/2 : ℂ) * Matrix.trace (A.transpose * B) := by
    simp [c1BellProjector, pureDensity, QuantumProver.WernerEndpoint.pureDensity,
      QuantumProver.WernerEndpoint.crossDensity, Matrix.trace, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply,
      Matrix.transpose_apply, Matrix.smul_apply, Complex.real_smul]
    ring
  rw [h]
  simp [Complex.mul_re]

theorem c1Bell_product_overlap_le_half (A B : Density Qubit) :
    (Matrix.trace (c1BellProjector * (A.matrix ⊗ₖ B.matrix))).re ≤ (1/2 : ℝ) := by
  have hc := c1_qubit_complement_posSemidef A.positive.transpose
    (by simpa only [Matrix.trace_transpose] using A.trace_one)
  have hn := QuantumProver.SuperchannelDiscrimination.KrausCompletion.trace_mul_nonneg_of_posSemidef
    hc B.positive
  have hr := (Complex.le_def.mp hn).1
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub,
    Complex.sub_re, B.trace_one, Complex.one_re, Complex.zero_re] at hr
  rw [c1Bell_product_overlap]
  linarith

theorem c1OneWayAccept_product_le (A B : Density Qubit) :
    (Matrix.trace (c1OneWayAccept * (A.matrix ⊗ₖ B.matrix))).re ≤ (2/3 : ℝ) := by
  have hbell := c1Bell_product_overlap_le_half A B
  rw [c1OneWayAccept_eq]
  simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_smul,
    Matrix.trace_add, Complex.add_re, Complex.smul_re, smul_eq_mul]
  rw [Matrix.trace_kronecker, A.trace_one, B.trace_one]
  norm_num
  linarith

def c1OneWayPOVM : OneWayPOVM Qubit Qubit (Fin 3 × Fin 2) (Fin 2) where
  alice := c1OneWayAliceEffect
  alice_positive := c1OneWayAliceEffect_posSemidef
  alice_complete := c1OneWayAliceEffect_complete
  bob := c1OneWayBobEffect
  bob_positive x y := c1PauliEffect_posSemidef x.1 y
  bob_complete := c1OneWayBobEffect_complete

def c1OutcomeEquiv : Fin 6 ≃ (Fin 3 × Fin 2) :=
  (finProdFinEquiv (m := 3) (n := 2)).symm

def c1OneWayFinPOVM : OneWayPOVM Qubit Qubit (Fin 6) (Fin 2) where
  alice x := c1OneWayAliceEffect (c1OutcomeEquiv x)
  alice_positive x := c1OneWayAliceEffect_posSemidef _
  alice_complete := by
    calc
      ∑ x : Fin 6, c1OneWayAliceEffect (c1OutcomeEquiv x) =
          ∑ x : Fin 3 × Fin 2, c1OneWayAliceEffect x :=
        Equiv.sum_comp c1OutcomeEquiv c1OneWayAliceEffect
      _ = 1 := c1OneWayAliceEffect_complete
  bob x y := c1OneWayBobEffect (c1OutcomeEquiv x) y
  bob_positive x y := c1PauliEffect_posSemidef _ _
  bob_complete x := c1OneWayBobEffect_complete _

theorem c1_oneWay_effects_complete {A B X Y : Type*}
    [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
    [DecidableEq A] [DecidableEq B] (M : OneWayPOVM A B X Y) :
    (∑ x, ∑ y, M.alice x ⊗ₖ M.bob x y) = (1 : QMatrix (A × B)) := by
  have heq : (∑ x, ∑ y, M.alice x ⊗ₖ M.bob x y) =
      (∑ x, M.alice x) ⊗ₖ (1 : QMatrix B) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
    have hb (x : X) : (∑ y, M.bob x y i.2 j.2) = (1 : QMatrix B) i.2 j.2 := by
      simpa only [Matrix.sum_apply] using congrArg (fun T : QMatrix B => T i.2 j.2)
        (M.bob_complete x)
    simp_rw [← Finset.mul_sum, hb]
    rw [← Finset.sum_mul]
  rw [heq, M.alice_complete, Matrix.one_kronecker_one]

theorem c1_oneWayOutcome_nonneg {A B X Y : Type*}
    [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
    [DecidableEq A] [DecidableEq B] (M : OneWayPOVM A B X Y)
    (ρ : Density (A × B)) (x : X) (y : Y) :
    0 ≤ oneWayOutcome M ρ.matrix x y := by
  exact (Complex.le_def.mp
    (QuantumProver.SuperchannelDiscrimination.KrausCompletion.trace_mul_nonneg_of_posSemidef
      ρ.positive ((M.alice_positive x).kronecker (M.bob_positive x y)))).1

theorem c1_oneWayOutcome_sum {A B X Y : Type*}
    [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
    [DecidableEq A] [DecidableEq B] (M : OneWayPOVM A B X Y)
    (R : QMatrix (A × B)) :
    (∑ x, ∑ y, oneWayOutcome M R x y) = (Matrix.trace R).re := by
  have hc : (∑ x, ∑ y, Matrix.trace (R * (M.alice x ⊗ₖ M.bob x y))) =
      Matrix.trace R := by
    simp_rw [← Matrix.trace_sum, ← Matrix.mul_sum]
    rw [c1_oneWay_effects_complete, Matrix.mul_one]
  simpa only [Complex.re_sum, oneWayOutcome] using congrArg Complex.re hc

theorem c1_oneWayOutcome_density_sum {A B X Y : Type*}
    [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
    [DecidableEq A] [DecidableEq B] (M : OneWayPOVM A B X Y)
    (ρ : Density (A × B)) :
    (∑ x, ∑ y, oneWayOutcome M ρ.matrix x y) = 1 := by
  rw [c1_oneWayOutcome_sum, ρ.trace_one, Complex.one_re]

theorem c1_oneWay_difference_variation_le_two {A B X Y : Type*}
    [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
    [DecidableEq A] [DecidableEq B] (M : OneWayPOVM A B X Y)
    (ρ σ : Density (A × B)) :
    (∑ x, ∑ y, |oneWayOutcome M (ρ.matrix - σ.matrix) x y|) ≤ 2 := by
  have hd (x : X) (y : Y) : oneWayOutcome M (ρ.matrix - σ.matrix) x y =
      oneWayOutcome M ρ.matrix x y - oneWayOutcome M σ.matrix x y := by
    simp only [oneWayOutcome, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
  calc
    _ ≤ ∑ x, ∑ y, (oneWayOutcome M ρ.matrix x y + oneWayOutcome M σ.matrix x y) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      rw [hd]
      exact abs_le.mpr ⟨by linarith [c1_oneWayOutcome_nonneg M ρ x y,
        c1_oneWayOutcome_nonneg M σ x y],
        by linarith [c1_oneWayOutcome_nonneg M ρ x y,
          c1_oneWayOutcome_nonneg M σ x y]⟩
    _ = 2 := by
      simp only [Finset.sum_add_distrib, c1_oneWayOutcome_density_sum]
      norm_num

theorem c1_oneWayNorm_set_bddAbove {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (ρ σ : Density (A × B)) :
    BddAbove {v : ℝ | ∃ m n : ℕ, ∃ M : OneWayPOVM A B (Fin m) (Fin n),
      v = ∑ x, ∑ y, |oneWayOutcome M (ρ.matrix - σ.matrix) x y|} := by
  refine ⟨2, ?_⟩
  rintro v ⟨m,n,M,rfl⟩
  exact c1_oneWay_difference_variation_le_two M ρ σ

theorem c1_oneWayNorm_ge_measurement {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (ρ σ : Density (A × B)) {m n : ℕ}
    (M : OneWayPOVM A B (Fin m) (Fin n)) :
    (∑ x, ∑ y, |oneWayOutcome M (ρ.matrix - σ.matrix) x y|) ≤
      oneWayNorm (ρ.matrix - σ.matrix) := by
  exact le_csSup (c1_oneWayNorm_set_bddAbove ρ σ) ⟨m,n,M,rfl⟩

theorem c1OneWayAccept_separable_le {σ : QMatrix (Qubit × Qubit)}
    (hσ : IsSeparable σ) : (Matrix.trace (c1OneWayAccept * σ)).re ≤ (2/3 : ℝ) := by
  let T : Set (QMatrix (Qubit × Qubit)) :=
    {R | (Matrix.trace (c1OneWayAccept * R)).re ≤ (2/3 : ℝ)}
  have hconv : Convex ℝ T := by
    intro X hX Y hY a b ha hb hab
    change (Matrix.trace (c1OneWayAccept * (a • X + b • Y))).re ≤ (2/3 : ℝ)
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
      Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
    change (Matrix.trace (c1OneWayAccept * X)).re ≤ (2/3 : ℝ) at hX
    change (Matrix.trace (c1OneWayAccept * Y)).re ≤ (2/3 : ℝ) at hY
    calc
      _ ≤ a*(2/3) + b*(2/3) := add_le_add
        (mul_le_mul_of_nonneg_left hX ha) (mul_le_mul_of_nonneg_left hY hb)
      _ = 2/3 := by nlinarith
  have hbase : {R : QMatrix (Qubit × Qubit) |
      ∃ A : Density Qubit, ∃ B : Density Qubit, R = A.matrix ⊗ₖ B.matrix} ⊆ T := by
    rintro R ⟨A,B,rfl⟩
    exact c1OneWayAccept_product_le A B
  exact (convexHull_min hbase hconv) hσ

theorem c1_regularized_schur_residual {D₀ : QMatrix I} {D₁ : QMatrix J}
    (Y : Matrix J I ℂ)
    (hρ : (Matrix.fromBlocks D₀ Yᴴ Y D₁).PosSemidef)
    {x : ℝ} (hx : 0 < x) :
    (D₁ + x • (1 : QMatrix J) -
      Y * (D₀ + x • (1 : QMatrix I))⁻¹ * Yᴴ).PosSemidef := by
  have hD₀ : D₀.PosSemidef := by
    have hs := hρ.submatrix (Sum.inl : I → I ⊕ J)
    have heq : (Matrix.fromBlocks D₀ Yᴴ Y D₁).submatrix Sum.inl Sum.inl = D₀ := by
      ext i j
      rfl
    rw [heq] at hs
    exact hs
  have hpivot := c1_regularized_posDef hD₀ hx
  letI : Invertible (D₀ + x • (1 : QMatrix I)) := hpivot.isUnit.invertible
  have hregular : (Matrix.fromBlocks (D₀ + x • (1 : QMatrix I)) Yᴴ Y
      (D₁ + x • (1 : QMatrix J))).PosSemidef := by
    have heq : Matrix.fromBlocks (D₀ + x • (1 : QMatrix I)) Yᴴ Y
        (D₁ + x • (1 : QMatrix J)) =
        Matrix.fromBlocks D₀ Yᴴ Y D₁ + x • (1 : QMatrix (I ⊕ J)) := by
      ext i j
      cases i <;> cases j <;>
        simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
          Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    rw [heq]
    exact hρ.add (Matrix.PosSemidef.one.smul hx.le)
  have hs := (Matrix.PosDef.fromBlocks₁₁ Yᴴ (D₁ + x • (1 : QMatrix J)) hpivot).mp
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hregular)
  simpa only [Matrix.conjTranspose_conjTranspose] using hs

theorem c1_binary_selector_variation {X : Type*} [Fintype X]
    (d : X → Fin 2 → ℝ) (f : X → Fin 2) :
    2*(∑ x, d x (f x)) - (∑ x, ∑ y, d x y) ≤ ∑ x, ∑ y, |d x y| := by
  have hp (x : X) : 2*d x (f x) - (∑ y, d x y) ≤ ∑ y, |d x y| := by
    have heq : f x = 0 ∨ f x = 1 := by omega
    obtain hf | hf := heq
    · rw [hf, Fin.sum_univ_two, Fin.sum_univ_two]
      linarith [le_abs_self (d x 0), neg_le_abs (d x 1)]
    · rw [hf, Fin.sum_univ_two, Fin.sum_univ_two]
      linarith [le_abs_self (d x 1), neg_le_abs (d x 0)]
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hp x)
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum] using hs

theorem c1OneWayFinPOVM_accepted_sum (R : QMatrix (Qubit × Qubit)) :
    (∑ x : Fin 6, oneWayOutcome c1OneWayFinPOVM R x
      (c1OutcomeEquiv x).2) = (Matrix.trace (c1OneWayAccept * R)).re := by
  calc
    _ = ∑ x : Fin 3 × Fin 2,
        (Matrix.trace (R * (c1OneWayAliceEffect x ⊗ₖ c1OneWayBobEffect x x.2))).re :=
      Equiv.sum_comp c1OutcomeEquiv (fun x : Fin 3 × Fin 2 =>
        (Matrix.trace (R * (c1OneWayAliceEffect x ⊗ₖ c1OneWayBobEffect x x.2))).re)
    _ = (Matrix.trace (R * c1OneWayAccept)).re := by
      simp only [c1OneWayAccept, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    _ = (Matrix.trace (c1OneWayAccept * R)).re := by rw [Matrix.trace_mul_comm]

theorem c1_oneWayNorm_ge_twice_acceptance (ρ σ : Density (Qubit × Qubit)) :
    2*(Matrix.trace (c1OneWayAccept * (ρ.matrix - σ.matrix))).re ≤
      oneWayNorm (ρ.matrix - σ.matrix) := by
  have hs := c1_binary_selector_variation
    (oneWayOutcome c1OneWayFinPOVM (ρ.matrix - σ.matrix))
    (fun x : Fin 6 => (c1OutcomeEquiv x).2)
  have ht : (∑ x, ∑ y, oneWayOutcome c1OneWayFinPOVM
      (ρ.matrix - σ.matrix) x y) = 0 := by
    rw [c1_oneWayOutcome_sum, Matrix.trace_sub, ρ.trace_one, σ.trace_one]
    norm_num
  rw [ht, sub_zero, c1OneWayFinPOVM_accepted_sum] at hs
  exact hs.trans (c1_oneWayNorm_ge_measurement ρ σ c1OneWayFinPOVM)

theorem c1OneWayAccept_eq_fidelity (ρ : Density (Qubit × Qubit)) :
    (Matrix.trace (c1OneWayAccept * ρ.matrix)).re =
      (1/3 : ℝ) + (2/3 : ℝ)*(Matrix.trace (c1BellProjector * ρ.matrix)).re := by
  rw [c1OneWayAccept_eq]
  simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.trace_smul,
    Matrix.trace_add, Complex.add_re, Complex.smul_re, smul_eq_mul,
    ρ.trace_one, Complex.one_re]
  ring

theorem c1_oneWay_distance_boundary_witness
    (ρ σ : Density (Qubit × Qubit)) (hσ : IsSeparable σ.matrix) (δ : ℝ)
    (hF : (Matrix.trace (c1BellProjector * ρ.matrix)).re = (1/2 : ℝ) + δ) :
    4*δ/3 ≤ oneWayNorm (ρ.matrix - σ.matrix) := by
  have hρ := c1OneWayAccept_eq_fidelity ρ
  rw [hF] at hρ
  have hsep := c1OneWayAccept_separable_le hσ
  have hgap : 4*δ/3 ≤
      2*(Matrix.trace (c1OneWayAccept * (ρ.matrix - σ.matrix))).re := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    linarith
  exact hgap.trans (c1_oneWayNorm_ge_twice_acceptance ρ σ)

def c1LeftProjection : QMatrix (I ⊕ J) := Matrix.fromBlocks 1 0 0 0

theorem c1LeftProjection_posSemidef :
    (c1LeftProjection (I := I) (J := J)).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self
    (c1LeftProjection (I := I) (J := J))
  simpa [c1LeftProjection, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply] using h

theorem c1_inverse_noise_contraction {A : QMatrix I} (hA : A.IsHermitian)
    (Z : Matrix J I ℂ) {x : ℝ} (hx : 0 < x) :
    ((1 : QMatrix J) -
      Z * (A*A + Zᴴ*Z + x • (1 : QMatrix I))⁻¹ * Zᴴ).PosSemidef := by
  let K : QMatrix (I ⊕ J) := Matrix.fromBlocks A 0 Z 1
  have hbase : (Matrix.fromBlocks (A*A + Zᴴ*Z) Zᴴ Z (1 : QMatrix J)).PosSemidef := by
    simpa [K, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hA.eq]
      using Matrix.posSemidef_conjTranspose_mul_self K
  have hp : (A*A + Zᴴ*Z + x • (1 : QMatrix I)).PosDef :=
    c1_regularized_posDef ((c1_hermitian_square_posSemidef hA).add
      (Matrix.posSemidef_conjTranspose_mul_self Z)) hx
  letI : Invertible (A*A + Zᴴ*Z + x • (1 : QMatrix I)) := hp.isUnit.invertible
  have hblock : (Matrix.fromBlocks (A*A + Zᴴ*Z + x • (1 : QMatrix I))
      Zᴴ Z (1 : QMatrix J)).PosSemidef := by
    have h := hbase.add ((c1LeftProjection_posSemidef (I := I) (J := J)).smul hx.le)
    convert h using 1
    ext i j
    cases i <;> cases j <;>
      simp [c1LeftProjection, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.add_apply, Matrix.smul_apply]
  have hs := (Matrix.PosDef.fromBlocks₁₁ Zᴴ (1 : QMatrix J) hp).mp
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hblock)
  simpa only [Matrix.conjTranspose_conjTranspose] using hs

theorem c1_partner_inverse_noise_contraction {B : QMatrix J} (hB : B.IsHermitian)
    (Z : Matrix J I ℂ) {x : ℝ} (hx : 0 < x) :
    ((1 : QMatrix I) -
      Zᴴ * (B*B + Z*Zᴴ + x • (1 : QMatrix J))⁻¹ * Z).PosSemidef := by
  simpa only [Matrix.conjTranspose_conjTranspose] using
    c1_inverse_noise_contraction hB Zᴴ hx

def c1KernelRatio (β r : ℝ) : ℝ := (1+r)/(1+β*r)

def c1CoshKernel (β r : ℝ) : ℝ := Real.sqrt (c1KernelRatio β r)

theorem c1KernelRatio_nonneg {β r : ℝ} (hβ : 0 ≤ β) (hr : 0 ≤ r) :
    0 ≤ c1KernelRatio β r := by
  unfold c1KernelRatio
  positivity

theorem c1KernelRatio_jensen_slack {β r s a b : ℝ}
    (hβ : 0 ≤ β) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    c1KernelRatio β (a*r+b*s) - a*c1KernelRatio β r - b*c1KernelRatio β s =
      a*b*β*(1-β)*(r-s)^2 /
        ((1+β*r)*(1+β*s)*(1+β*(a*r+b*s))) := by
  have hR : 0 < 1+β*r := by positivity
  have hS : 0 < 1+β*s := by positivity
  have hM : 0 < 1+β*(a*r+b*s) := by positivity
  have hbeq : b=1-a := by linarith
  subst b
  unfold c1KernelRatio
  field_simp [ne_of_gt hR, ne_of_gt hS, ne_of_gt hM]
  ring

theorem c1KernelRatio_concaveOn {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    ConcaveOn ℝ (Set.Ici 0) (c1KernelRatio β) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro r hr s hs a b ha hb hab
  change 0 ≤ r at hr
  change 0 ≤ s at hs
  change a*c1KernelRatio β r + b*c1KernelRatio β s ≤
    c1KernelRatio β (a*r+b*s)
  have hid := c1KernelRatio_jensen_slack hβ hr hs ha hb hab
  have hn : 0 ≤ a*b*β*(1-β)*(r-s)^2 /
      ((1+β*r)*(1+β*s)*(1+β*(a*r+b*s))) := by
    have hβdiff : 0 ≤ 1-β := sub_nonneg.mpr hβ1
    positivity
  linarith

theorem c1CoshKernel_concaveOn {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    ConcaveOn ℝ (Set.Ici 0) (c1CoshKernel β) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro r hr s hs a b ha hb hab
  have hqr := c1KernelRatio_nonneg hβ hr
  have hqs := c1KernelRatio_nonneg hβ hs
  let v := Real.sqrt (c1KernelRatio β r)
  let w := Real.sqrt (c1KernelRatio β s)
  have hv : v^2 = c1KernelRatio β r := Real.sq_sqrt hqr
  have hw : w^2 = c1KernelRatio β s := Real.sq_sqrt hqs
  have hgap : 0 ≤ a*b*(v-w)^2 :=
    mul_nonneg (mul_nonneg ha hb) (sq_nonneg (v-w))
  have heq : (a*v+b*w)^2 + a*b*(v-w)^2 =
      a*c1KernelRatio β r + b*c1KernelRatio β s := by
    rw [← hv, ← hw]
    have hbeq : b=1-a := by linarith
    subst b
    ring
  have hsq : (a*v+b*w)^2 ≤ a*c1KernelRatio β r + b*c1KernelRatio β s := by
    linarith only [heq, hgap]
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  have hratio := (c1KernelRatio_concaveOn hβ hβ1).2 hr hs ha hb hab
  change a*c1KernelRatio β r + b*c1KernelRatio β s ≤
    c1KernelRatio β (a*r+b*s) at hratio
  exact hsqrt.trans (Real.sqrt_le_sqrt hratio)

theorem c1CoshKernel_monotoneOn {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    MonotoneOn (c1CoshKernel β) (Set.Ici 0) := by
  intro r hr s hs hrs
  change 0 ≤ r at hr
  change 0 ≤ s at hs
  apply Real.sqrt_le_sqrt
  unfold c1KernelRatio
  have hR : 0 < 1+β*r := by positivity
  have hS : 0 < 1+β*s := by positivity
  apply (div_le_div_iff₀ hR hS).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hβ1) (sub_nonneg.mpr hrs)]

@[simp] theorem c1CoshKernel_zero (β : ℝ) : c1CoshKernel β 0 = 1 := by
  simp [c1CoshKernel, c1KernelRatio]

theorem c1CoshKernel_finite_jensen {K : Type*} [Fintype K] {β R : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (w r : K → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hweight : ∑ i, w i = 1) (hr : ∀ i, 0 ≤ r i)
    (hR : (∑ i, w i*r i) ≤ R) :
    (∑ i, w i*c1CoshKernel β (r i)) ≤ c1CoshKernel β R := by
  have hj : (∑ i, w i*c1CoshKernel β (r i)) ≤
      c1CoshKernel β (∑ i, w i*r i) := by
    simpa only [smul_eq_mul] using
      (c1CoshKernel_concaveOn hβ hβ1).le_map_sum (t := Finset.univ)
        (fun i _ => hw i) hweight (fun i _ => hr i)
  have hmean : 0 ≤ ∑ i, w i*r i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hr i))
  exact hj.trans ((c1CoshKernel_monotoneOn hβ hβ1) hmean (hmean.trans hR) hR)

theorem c1CoshKernel_finite_jensen_square {K : Type*} [Fintype K]
    {v R : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (w r : K → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hweight : ∑ i, w i = 1) (hr : ∀ i, 0 ≤ r i)
    (hR : (∑ i, w i*r i) ≤ R) :
    (∑ i, w i*c1CoshKernel (v^2) (r i)) ≤ c1CoshKernel (v^2) R := by
  exact c1CoshKernel_finite_jensen (sq_nonneg v) (by nlinarith) w r hw hweight hr hR

theorem c1_trace_log_eq_log_det {I : Type*} [Fintype I] [DecidableEq I]
    {X : QMatrix I} (hX : X.PosDef) :
    (Matrix.trace (cfc Real.log X)).re = Real.log (Matrix.det X).re := by
  have hp : ((∏ i, hX.1.eigenvalues i : ℝ) : ℂ) =
      ∏ i, (hX.1.eigenvalues i : ℂ) := by
    simpa using Complex.ofReal_prod Finset.univ (fun i : I => hX.1.eigenvalues i)
  have hd : (Matrix.det X).re = ∏ i, hX.1.eigenvalues i := by
    calc
      (Matrix.det X).re = (∏ i, (hX.1.eigenvalues i : ℂ)).re :=
        congrArg Complex.re hX.1.det_eq_prod_eigenvalues
      _ = ∏ i, hX.1.eigenvalues i := by rw [← hp]; rfl
  rw [QuantumProver.SuperchannelDiscrimination.Klein.trace_cfc_eq_sum Real.log hX.1, hd]
  exact (Real.log_prod (fun i _ => ne_of_gt (hX.eigenvalues_pos i))).symm

theorem c1_integral_shifted_log (a ε T : ℝ) :
    (∫ x in ε..T, Real.log (x+a)) =
      (T+a)*Real.log (T+a) - (ε+a)*Real.log (ε+a) - T + ε := by
  rw [intervalIntegral.integral_comp_add_right, integral_log]
  ring

def c1CoshMoment (r : ℝ) : ℝ :=
  2*(∫ v : ℝ in 0..1, c1CoshKernel (v^2) r)

theorem c1CoshKernel_continuous_parameter {r : ℝ} (hr : 0 ≤ r) :
    Continuous (fun v : ℝ => c1CoshKernel (v^2) r) := by
  unfold c1CoshKernel c1KernelRatio
  apply Real.continuous_sqrt.comp
  exact continuous_const.div
    (continuous_const.add ((continuous_id.pow 2).mul_const r))
    (fun v => ne_of_gt (by positivity : 0 < 1+v^2*r))

theorem c1CoshMoment_finite_jensen {K : Type*} [Fintype K] {R : ℝ}
    (w r : K → ℝ) (hw : ∀ i, 0 ≤ w i) (hweight : ∑ i, w i = 1)
    (hr : ∀ i, 0 ≤ r i) (hR : (∑ i, w i*r i) ≤ R) :
    (∑ i, w i*c1CoshMoment (r i)) ≤ c1CoshMoment R := by
  have hmean : 0 ≤ ∑ i, w i*r i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hr i))
  have hR0 := hmean.trans hR
  have hi (i : K) : IntervalIntegrable
      (fun v : ℝ => w i*c1CoshKernel (v^2) (r i)) MeasureTheory.volume 0 1 :=
    ((c1CoshKernel_continuous_parameter (hr i)).const_mul (w i)).intervalIntegrable 0 1
  have hleft : IntervalIntegrable
      (fun v : ℝ => ∑ i, w i*c1CoshKernel (v^2) (r i)) MeasureTheory.volume 0 1 :=
    (continuous_finsetSum Finset.univ (fun i _ =>
      (c1CoshKernel_continuous_parameter (hr i)).const_mul (w i))).intervalIntegrable 0 1
  have hright : IntervalIntegrable
      (fun v : ℝ => c1CoshKernel (v^2) R) MeasureTheory.volume 0 1 :=
    (c1CoshKernel_continuous_parameter hR0).intervalIntegrable 0 1
  have hm := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    hleft hright (fun v hv => c1CoshKernel_finite_jensen_square hv.1 hv.2
      w r hw hweight hr hR)
  have hswap : (∫ v : ℝ in 0..1, ∑ i, w i*c1CoshKernel (v^2) (r i)) =
      ∑ i, w i*(∫ v : ℝ in 0..1, c1CoshKernel (v^2) (r i)) := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
    simp only [intervalIntegral.integral_const_mul]
  rw [hswap] at hm
  have ht := mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ 2)
  unfold c1CoshMoment
  convert ht using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi'
  ring

@[simp] theorem c1CoshMoment_zero : c1CoshMoment 0 = 2 := by
  simp [c1CoshMoment, c1CoshKernel, c1KernelRatio, intervalIntegral.integral_const]

theorem c1CoshMoment_eq_arsinh {r : ℝ} (hr : 0 < r) :
    c1CoshMoment r =
      2 * Real.sqrt (1+r) * Real.arsinh (Real.sqrt r) / Real.sqrt r := by
  have hk : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hkn : Real.sqrt r ≠ 0 := ne_of_gt hk
  have hksq : (Real.sqrt r)^2 = r := Real.sq_sqrt hr.le
  have h1 : 0 ≤ 1+r := by linarith
  have hd (v : ℝ) : HasDerivAt
      (fun v : ℝ => Real.sqrt (1+r) *
        (Real.arsinh (Real.sqrt r*v) / Real.sqrt r))
      (c1CoshKernel (v^2) r) v := by
    have harg : (Real.sqrt r*v)^2 = v^2*r := by
      rw [mul_pow, hksq]
      ring
    have hbase := ((hasDerivAt_const_mul (x := v) (Real.sqrt r)).arsinh).div_const
      (Real.sqrt r)
    have hc : (Real.sqrt (1+(Real.sqrt r*v)^2))⁻¹ * Real.sqrt r /
        Real.sqrt r = (Real.sqrt (1+v^2*r))⁻¹ := by
      rw [harg, mul_div_cancel_right₀ _ hkn]
    have hbase' : HasDerivAt
        (fun v : ℝ => Real.arsinh (Real.sqrt r*v)/Real.sqrt r)
        (Real.sqrt (1+v^2*r))⁻¹ v := by
      simpa only [smul_eq_mul, hc] using hbase
    convert hbase'.const_mul (Real.sqrt (1+r)) using 1
    unfold c1CoshKernel c1KernelRatio
    rw [Real.sqrt_div h1, div_eq_mul_inv]
  have hi : IntervalIntegrable (fun v : ℝ => c1CoshKernel (v^2) r)
      MeasureTheory.volume 0 1 :=
    (c1CoshKernel_continuous_parameter hr.le).intervalIntegrable 0 1
  have ht : (∫ v : ℝ in 0..1, c1CoshKernel (v^2) r) =
      Real.sqrt (1+r)*(Real.arsinh (Real.sqrt r*1)/Real.sqrt r) -
      Real.sqrt (1+r)*(Real.arsinh (Real.sqrt r*0)/Real.sqrt r) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v) hi
  unfold c1CoshMoment
  rw [ht]
  simp only [mul_one, mul_zero, Real.arsinh_zero, zero_div, sub_zero]
  ring

theorem c1_arcosh_one_add_two {r : ℝ} (hr : 0 ≤ r) :
    Real.arcosh (1+2*r) = 2*Real.arsinh (Real.sqrt r) := by
  have hy : 0 ≤ 2*Real.arsinh (Real.sqrt r) :=
    mul_nonneg (by norm_num) (Real.arsinh_nonneg_iff.2 (Real.sqrt_nonneg r))
  have hc : Real.cosh (2*Real.arsinh (Real.sqrt r)) = 1+2*r := by
    rw [Real.cosh_two_mul, Real.cosh_arsinh, Real.sinh_arsinh,
      Real.sq_sqrt (by positivity : 0 ≤ 1+(Real.sqrt r)^2), Real.sq_sqrt hr]
    ring
  rw [← hc]
  exact Real.arcosh_cosh hy

theorem c1CoshMoment_eq_Fcal {m : ℝ} (hm : 2 ≤ m) :
    c1CoshMoment ((m-2)/4) = Fcal m := by
  by_cases heq : m=2
  · subst m
    simp [Fcal]
  · have hgt : 2 < m := lt_of_le_of_ne hm (Ne.symm heq)
    have hr : 0 < (m-2)/4 := by linarith
    have hs : Real.sqrt ((m-2)/4) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
    rw [c1CoshMoment_eq_arsinh hr]
    unfold Fcal
    rw [if_neg heq]
    have hx : m/2 = 1+2*((m-2)/4) := by ring
    rw [hx, c1_arcosh_one_add_two hr.le]
    have hmne : m-2 ≠ 0 := ne_of_gt (by linarith : 0 < m-2)
    have hquot : (m+2)/(m-2) =
        (1+(m-2)/4)/((m-2)/4) := by field_simp [hmne]; ring
    rw [hquot, Real.sqrt_div (by linarith : 0 ≤ 1+(m-2)/4)]
    ring

theorem c1_trace_shifted_log_spectral {I : Type*} [Fintype I] [DecidableEq I]
    {X : QMatrix I} (hX : X.IsHermitian) (x : ℝ) :
    (Matrix.trace (cfc Real.log (X+x • (1 : QMatrix I)))).re =
      ∑ i, Real.log (x+hX.eigenvalues i) := by
  rw [QuantumProver.SuperchannelDiscrimination.LogCompression.shifted_log_cfc hX x,
    QuantumProver.SuperchannelDiscrimination.Klein.trace_cfc_eq_sum _ hX]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm]

theorem c1_trace_shifted_log_intervalIntegrable
    {I : Type*} [Fintype I] [DecidableEq I]
    {X : QMatrix I} (hX : X.IsHermitian) (a b : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => (Matrix.trace (cfc Real.log (X+x • (1 : QMatrix I)))).re)
      MeasureTheory.volume a b := by
  have hi (i : I) : IntervalIntegrable
      (fun x : ℝ => Real.log (x+hX.eigenvalues i)) MeasureTheory.volume a b :=
    (IntervalIntegrable.comp_add_right_iff (f := Real.log) (c := hX.eigenvalues i)).2
      intervalIntegral.intervalIntegrable_log'
  simp_rw [c1_trace_shifted_log_spectral hX]
  have hs := IntervalIntegrable.sum Finset.univ (fun i _ => hi i)
  have heq : (∑ i, (fun x : ℝ => Real.log (x+hX.eigenvalues i))) =
      (fun x : ℝ => ∑ i, Real.log (x+hX.eigenvalues i)) := by
    funext x
    simp only [Finset.sum_apply]
  rw [heq] at hs
  exact hs

theorem c1_integral_trace_shifted_log
    {I : Type*} [Fintype I] [DecidableEq I]
    {X : QMatrix I} (hX : X.IsHermitian) (a b : ℝ) :
    (∫ x in a..b, (Matrix.trace (cfc Real.log (X+x • (1 : QMatrix I)))).re) =
      ∑ i, ((b+hX.eigenvalues i)*Real.log (b+hX.eigenvalues i) -
        (a+hX.eigenvalues i)*Real.log (a+hX.eigenvalues i) - b+a) := by
  have hi (i : I) : IntervalIntegrable
      (fun x : ℝ => Real.log (x+hX.eigenvalues i)) MeasureTheory.volume a b :=
    (IntervalIntegrable.comp_add_right_iff (f := Real.log) (c := hX.eigenvalues i)).2
      intervalIntegral.intervalIntegrable_log'
  simp_rw [c1_trace_shifted_log_spectral hX]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  exact c1_integral_shifted_log (hX.eigenvalues i) a b

theorem c1_integral_trace_shifted_log_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    {X : QMatrix I} (hX : X.IsHermitian) (T : ℝ) :
    (∫ x in 0..T, (Matrix.trace (cfc Real.log (X+x • (1 : QMatrix I)))).re) =
      (∑ i, (T+hX.eigenvalues i)*Real.log (T+hX.eigenvalues i)) +
        entropyNat X - (Fintype.card I : ℝ)*T := by
  rw [c1_integral_trace_shifted_log hX, entropyNat_spectral hX]
  simp only [zero_add, add_zero, Real.negMulLog_def]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, neg_mul]
  ring

theorem c1_scalar_phi_remainder {T a : ℝ} (hT : 0 < T) (ha : 0 ≤ a) :
    0 ≤ (T+a)*Real.log (T+a) - T*Real.log T - a*(Real.log T+1) ∧
    (T+a)*Real.log (T+a) - T*Real.log T - a*(Real.log T+1) ≤ a^2/T := by
  let q : ℝ := a/T
  have hq : 0 ≤ q := div_nonneg ha hT.le
  have hq1 : 0 < 1+q := by linarith
  have haeq : a=T*q := by dsimp [q]; field_simp [ne_of_gt hT]
  have hfact : T+a=T*(1+q) := by rw [haeq]; ring
  have hl : Real.log (T+a)=Real.log T+Real.log (1+q) := by
    rw [hfact, Real.log_mul (ne_of_gt hT) (ne_of_gt hq1)]
  have hrem : (T+a)*Real.log (T+a)-T*Real.log T-a*(Real.log T+1) =
      T*((1+q)*Real.log (1+q)-q) := by rw [hl,haeq]; ring
  have hlo := mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos hq1) hq1.le
  have hhi := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos hq1) hq1.le
  have hinv : (1+q)*(1+q)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hq1)
  have hlow : 0 ≤ (1+q)*Real.log (1+q)-q := by nlinarith [hinv]
  have hupp : (1+q)*Real.log (1+q)-q ≤ q^2 := by nlinarith
  have hratio : T*q^2=a^2/T := by dsimp [q]; field_simp [ne_of_gt hT]
  rw [hrem]
  refine ⟨mul_nonneg hT.le hlow, ?_⟩
  exact (mul_le_mul_of_nonneg_left hupp hT.le).trans_eq hratio

theorem c1_finite_phi_tail_bound {K : Type*} [Fintype K]
    (a : K → ℝ) (ha : ∀ i, 0 ≤ a i) {T : ℝ} (hT : 0 < T) :
    0 ≤ (∑ i, ((T+a i)*Real.log (T+a i)-T*Real.log T-a i*(Real.log T+1))) ∧
    (∑ i, ((T+a i)*Real.log (T+a i)-T*Real.log T-a i*(Real.log T+1))) ≤
      (∑ i, a i)^2/T := by
  refine ⟨Finset.sum_nonneg (fun i _ => (c1_scalar_phi_remainder hT (ha i)).1), ?_⟩
  calc
    (∑ i, ((T+a i)*Real.log (T+a i)-T*Real.log T-a i*(Real.log T+1))) ≤
        ∑ i, (a i)^2/T :=
      Finset.sum_le_sum (fun i _ => (c1_scalar_phi_remainder hT (ha i)).2)
    _ = (∑ i, (a i)^2)/T := by rw [Finset.sum_div]
    _ ≤ (∑ i, a i)^2/T :=
      div_le_div_of_nonneg_right
        (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => ha i)) hT.le

theorem c1_entropy_difference_integral_tail
    {I : Type*} [Fintype I] [DecidableEq I]
    {X Y : QMatrix I} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htrace : (Matrix.trace Y).re = (Matrix.trace X).re)
    {T : ℝ} (hT : 0 < T) :
    |(∫ x in 0..T,
        (Matrix.trace (cfc Real.log (Y+x • (1 : QMatrix I)))).re -
        (Matrix.trace (cfc Real.log (X+x • (1 : QMatrix I)))).re) -
      (entropyNat Y-entropyNat X)| ≤ (Matrix.trace X).re^2/T := by
  let RX : ℝ := ∑ i, ((T+hX.1.eigenvalues i)*Real.log (T+hX.1.eigenvalues i)-
    T*Real.log T-hX.1.eigenvalues i*(Real.log T+1))
  let RY : ℝ := ∑ i, ((T+hY.1.eigenvalues i)*Real.log (T+hY.1.eigenvalues i)-
    T*Real.log T-hY.1.eigenvalues i*(Real.log T+1))
  have hxmass := QuantumProver.SuperchannelDiscrimination.Klein.trace_eq_sum_eigenvalues_re hX.1
  have hymass := QuantumProver.SuperchannelDiscrimination.Klein.trace_eq_sum_eigenvalues_re hY.1
  have hbx : 0 ≤ RX ∧ RX ≤ (Matrix.trace X).re^2/T := by
    simpa only [RX, ← hxmass] using
      c1_finite_phi_tail_bound hX.1.eigenvalues hX.eigenvalues_nonneg hT
  have hby : 0 ≤ RY ∧ RY ≤ (Matrix.trace X).re^2/T := by
    simpa only [RY, ← hymass, htrace] using
      c1_finite_phi_tail_bound hY.1.eigenvalues hY.eigenvalues_nonneg hT
  have hid : (∫ x in 0..T,
        (Matrix.trace (cfc Real.log (Y+x • (1 : QMatrix I)))).re -
        (Matrix.trace (cfc Real.log (X+x • (1 : QMatrix I)))).re) -
      (entropyNat Y-entropyNat X) = RY-RX := by
    rw [intervalIntegral.integral_sub
      (c1_trace_shifted_log_intervalIntegrable hY.1 0 T)
      (c1_trace_shifted_log_intervalIntegrable hX.1 0 T),
      c1_integral_trace_shifted_log_zero hY.1,
      c1_integral_trace_shifted_log_zero hX.1]
    dsimp [RX, RY]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← hxmass, ← hymass, htrace]
    ring
  rw [hid]
  exact abs_le.2 ⟨by linarith [hbx.2,hby.1], by linarith [hby.2,hbx.1]⟩

theorem c1_entropy_difference_integral_limit
    {I : Type*} [Fintype I] [DecidableEq I]
    {X Y : QMatrix I} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htrace : (Matrix.trace Y).re = (Matrix.trace X).re) :
    Filter.Tendsto
      (fun T : ℝ => ∫ x in 0..T,
        (Matrix.trace (cfc Real.log (Y+x • (1 : QMatrix I)))).re -
        (Matrix.trace (cfc Real.log (X+x • (1 : QMatrix I)))).re)
      Filter.atTop (nhds (entropyNat Y-entropyNat X)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hlim : Filter.Tendsto (fun T : ℝ => (Matrix.trace X).re^2/T)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun T : ℝ => T⁻¹) Filter.atTop (nhds (0 : ℝ))))
  refine squeeze_zero' (Filter.Eventually.of_forall (fun T => norm_nonneg _)) ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  simpa only [Real.norm_eq_abs] using c1_entropy_difference_integral_tail hX hY htrace hT

theorem c1_schur_posDef {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {P0 : QMatrix I} {P1 : QMatrix J}
    (Y : Matrix J I ℂ) (hP0 : P0.PosDef)
    (hblock : (Matrix.fromBlocks P0 Yᴴ Y P1).PosDef) :
    (P1-Y*P0⁻¹*Yᴴ).PosDef := by
  letI : Invertible P0 := hP0.isUnit.invertible
  have hh : (P1-Y*P0⁻¹*Yᴴ).IsHermitian := by
    have hs := (Matrix.IsHermitian.fromBlocks₁₁ Yᴴ P1 hP0.1).mp
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hblock.1)
    simpa only [Matrix.conjTranspose_conjTranspose] using hs
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hh
  intro v hv
  have hvec : (-((P0⁻¹*Yᴴ)*ᵥ v) ⊕ᵥ v) ≠ 0 := by
    intro hz
    apply hv
    funext j
    have hj := congrFun hz (Sum.inr j)
    simpa using hj
  have hblock' : (Matrix.fromBlocks P0 Yᴴ (Yᴴ)ᴴ P1).PosDef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hblock
  have hq := hblock'.dotProduct_mulVec_pos hvec
  rwa [Matrix.dotProduct_mulVec,
    Matrix.schur_complement_eq₁₁ Yᴴ P1 _ _ hP0.1,
    neg_add_cancel, dotProduct_zero, zero_add, ← Matrix.dotProduct_mulVec,
    Matrix.conjTranspose_conjTranspose] at hq

theorem c1_schur_det {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {P0 : QMatrix I} (P1 : QMatrix J)
    (Y : Matrix J I ℂ) (hP0 : P0.PosDef) :
    Matrix.det (Matrix.fromBlocks P0 Yᴴ Y P1) =
      Matrix.det P0 * Matrix.det (P1-Y*P0⁻¹*Yᴴ) := by
  letI : Invertible P0 := hP0.isUnit.invertible
  simpa only [Matrix.invOf_eq_nonsing_inv] using
    Matrix.det_fromBlocks₁₁ P0 Yᴴ Y P1

theorem c1_trace_log_schur {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {P0 : QMatrix I} {P1 : QMatrix J}
    (Y : Matrix J I ℂ) (hP0 : P0.PosDef) (hP1 : P1.PosDef)
    (hblock : (Matrix.fromBlocks P0 Yᴴ Y P1).PosDef) :
    (Matrix.trace (cfc Real.log P0)).re +
      (Matrix.trace (cfc Real.log P1)).re -
      (Matrix.trace (cfc Real.log (Matrix.fromBlocks P0 Yᴴ Y P1))).re =
    (Matrix.trace (cfc Real.log P1)).re -
      (Matrix.trace (cfc Real.log (P1-Y*P0⁻¹*Yᴴ))).re := by
  have hs := c1_schur_posDef Y hP0 hblock
  have hd0 := Complex.pos_iff.mp hP0.det_pos
  have hds := Complex.pos_iff.mp hs.det_pos
  have hdre : (Matrix.det (Matrix.fromBlocks P0 Yᴴ Y P1)).re =
      (Matrix.det P0).re * (Matrix.det (P1-Y*P0⁻¹*Yᴴ)).re := by
    rw [c1_schur_det P1 Y hP0, Complex.mul_re, ← hd0.2]
    simp
  rw [c1_trace_log_eq_log_det hP0, c1_trace_log_eq_log_det hP1,
    c1_trace_log_eq_log_det hblock, c1_trace_log_eq_log_det hs, hdre,
    Real.log_mul (ne_of_gt hd0.1) (ne_of_gt hds.1)]
  ring

theorem c1_psd_sum_kernel_iff {I : Type*} [Fintype I]
    {P Q : QMatrix I} (hP : P.PosSemidef) (hQ : Q.PosSemidef) (v : I → ℂ) :
    (P+Q)*ᵥ v=0 ↔ P*ᵥ v=0 ∧ Q*ᵥ v=0 := by
  constructor
  · intro hv
    have hz : star v ⬝ᵥ (P*ᵥ v) + star v ⬝ᵥ (Q*ᵥ v) = 0 := by
      rw [← dotProduct_add, ← Matrix.add_mulVec, hv, dotProduct_zero]
    have hp := hP.dotProduct_mulVec_nonneg v
    have hq := hQ.dotProduct_mulVec_nonneg v
    have hple : star v ⬝ᵥ (P*ᵥ v) ≤ 0 := by
      calc
        _ ≤ star v ⬝ᵥ (P*ᵥ v)+star v ⬝ᵥ (Q*ᵥ v) := le_add_of_nonneg_right hq
        _ = 0 := hz
    have hqle : star v ⬝ᵥ (Q*ᵥ v) ≤ 0 := by
      calc
        _ ≤ star v ⬝ᵥ (P*ᵥ v)+star v ⬝ᵥ (Q*ᵥ v) := le_add_of_nonneg_left hp
        _ = 0 := hz
    exact ⟨hP.dotProduct_mulVec_zero_iff.mp (le_antisymm hple hp),
      hQ.dotProduct_mulVec_zero_iff.mp (le_antisymm hqle hq)⟩
  · rintro ⟨hp,hq⟩
    rw [Matrix.add_mulVec,hp,hq,add_zero]

theorem c1_gram_kernel_iff {I J : Type*} [Fintype I] [Fintype J]
    (Z : Matrix J I ℂ) (v : I → ℂ) :
    (Zᴴ*Z)*ᵥ v=0 ↔ Z*ᵥ v=0 := by
  constructor
  · intro hv
    apply dotProduct_star_self_eq_zero.mp
    calc
      star (Z*ᵥ v) ⬝ᵥ (Z*ᵥ v) = star v ⬝ᵥ ((Zᴴ*Z)*ᵥ v) := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
      _ = 0 := by rw [hv,dotProduct_zero]
  · intro hv
    rw [← Matrix.mulVec_mulVec,hv,Matrix.mulVec_zero]

theorem c1_binary_left_kernel_iff {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] {A : QMatrix I} (hA : A.IsHermitian)
    (Z : Matrix J I ℂ) (v : I → ℂ) :
    (A*A+Zᴴ*Z)*ᵥ v=0 ↔ A*ᵥ v=0 ∧ Z*ᵥ v=0 := by
  rw [c1_psd_sum_kernel_iff (c1_hermitian_square_posSemidef hA)
    (Matrix.posSemidef_conjTranspose_mul_self Z) v]
  have hAk : (A*A)*ᵥ v=0 ↔ A*ᵥ v=0 := by
    simpa only [hA.eq] using c1_gram_kernel_iff A v
  rw [hAk,c1_gram_kernel_iff Z v]

theorem c1_binary_right_kernel_iff {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] {B : QMatrix J} (hB : B.IsHermitian)
    (Z : Matrix J I ℂ) (v : J → ℂ) :
    (B*B+Z*Zᴴ)*ᵥ v=0 ↔ B*ᵥ v=0 ∧ Zᴴ*ᵥ v=0 := by
  simpa only [Matrix.conjTranspose_conjTranspose] using
    c1_binary_left_kernel_iff hB Zᴴ v

theorem c1_integral_shifted_inv {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    (∫ x in 0..T, (x+a)⁻¹) = Real.log (T+a)-Real.log a := by
  rw [intervalIntegral.integral_comp_add_right]
  simp only [zero_add]
  rw [integral_inv_of_pos ha (by linarith),
    Real.log_div (ne_of_gt (by linarith : 0 < T+a)) (ne_of_gt ha)]

theorem c1_pair_resolvent_partial_fraction {a b x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x) (hab : a ≠ b) :
    (x+a)⁻¹*(x+b)⁻¹ = ((x+a)⁻¹-(x+b)⁻¹)/(b-a) := by
  have hxa : x+a ≠ 0 := ne_of_gt (by linarith : 0 < x+a)
  have hxb : x+b ≠ 0 := ne_of_gt (by linarith : 0 < x+b)
  have hba : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  field_simp [hxa,hxb,hba]
  ring

theorem c1_pair_resolvent_integral_ne {a b T : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hT : 0 ≤ T) (hab : a ≠ b) :
    (∫ x in 0..T, (x+a)⁻¹*(x+b)⁻¹) =
      ((Real.log (T+a)-Real.log a)-(Real.log (T+b)-Real.log b))/(b-a) := by
  have hi (c : ℝ) (hc : 0 < c) : IntervalIntegrable
      (fun x : ℝ => (x+c)⁻¹) MeasureTheory.volume 0 T := by
    have hz (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) T) : x+c ≠ 0 := by
      have hx0 : 0 ≤ x := (by simpa only [Set.uIcc_of_le hT] using hx :
        x ∈ Set.Icc (0 : ℝ) T).1
      exact ne_of_gt (by linarith)
    have hc' : ContinuousOn (fun x : ℝ => x+c) (Set.uIcc (0 : ℝ) T) :=
      (continuous_id.add continuous_const : Continuous (fun x : ℝ => x+c)).continuousOn
    exact (hc'.inv₀ hz).intervalIntegrable
  have heq : (∫ x in 0..T, (x+a)⁻¹*(x+b)⁻¹) =
      (∫ x in 0..T, ((x+a)⁻¹-(x+b)⁻¹)/(b-a)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 ≤ x := (by simpa only [Set.uIcc_of_le hT] using hx :
      x ∈ Set.Icc (0 : ℝ) T).1
    exact c1_pair_resolvent_partial_fraction ha hb hx0 hab
  rw [heq, intervalIntegral.integral_div,
    intervalIntegral.integral_sub (hi a ha) (hi b hb),
    c1_integral_shifted_inv ha hT,c1_integral_shifted_inv hb hT]

theorem c1_pair_resolvent_integral_eq {a T : ℝ}
    (ha : 0 < a) (hT : 0 ≤ T) :
    (∫ x in 0..T, (x+a)⁻¹*(x+a)⁻¹) = a⁻¹-(T+a)⁻¹ := by
  have hz (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) T) : x+a ≠ 0 := by
    have hx0 : 0 ≤ x := (by simpa only [Set.uIcc_of_le hT] using hx :
      x ∈ Set.Icc (0 : ℝ) T).1
    exact ne_of_gt (by linarith)
  have hcont : ContinuousOn (fun x : ℝ => (x+a)⁻¹) (Set.uIcc (0 : ℝ) T) :=
    (continuous_id.add continuous_const : Continuous (fun x : ℝ => x+a)).continuousOn.inv₀ hz
  have hi : IntervalIntegrable (fun x : ℝ => (x+a)⁻¹*(x+a)⁻¹)
      MeasureTheory.volume 0 T := (hcont.mul hcont).intervalIntegrable
  have hd (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) T) :
      HasDerivAt (fun x : ℝ => -(x+a)⁻¹) ((x+a)⁻¹*(x+a)⁻¹) x := by
    have hd0 := (((hasDerivAt_id x).add_const a).inv (hz x hx)).neg
    change HasDerivAt (fun y : ℝ => -(y+a)⁻¹) (-(-1/(x+a)^2)) x at hd0
    simpa only [neg_div,neg_neg,one_div,pow_two,_root_.mul_inv_rev] using hd0
  have ht : (∫ x in 0..T, (x+a)⁻¹*(x+a)⁻¹) = -(T+a)⁻¹-(-(0+a)⁻¹) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [ht,zero_add]
  ring

theorem c1_pair_halfangle_identity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a-b)^2/(4*a*b) = (a/b+b/a-2)/4 := by
  field_simp [ne_of_gt ha,ne_of_gt hb]
  ring

theorem c1CoshMoment_pair_jensen {K : Type*} [Fintype K] {m : ℝ}
    (w a b : K → ℝ) (hw : ∀ i, 0 ≤ w i) (hweight : ∑ i, w i=1)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hbudget : (∑ i, w i*(a i/b i+b i/a i)) ≤ m) :
    (∑ i, w i*c1CoshMoment ((a i-b i)^2/(4*a i*b i))) ≤ Fcal m := by
  let r : K → ℝ := fun i => (a i-b i)^2/(4*a i*b i)
  have hr (i : K) : 0 ≤ r i :=
    div_nonneg (sq_nonneg _) (mul_pos (mul_pos (by norm_num) (ha i)) (hb i)).le
  have heq (i : K) : r i=(a i/b i+b i/a i-2)/4 :=
    c1_pair_halfangle_identity (ha i) (hb i)
  have hpair (i : K) : 2 ≤ a i/b i+b i/a i := by
    have hi := hr i
    rw [heq] at hi
    linarith
  have hm : 2 ≤ m := by
    calc
      2 = ∑ i, w i*2 := by rw [← Finset.sum_mul,hweight]; ring
      _ ≤ ∑ i, w i*(a i/b i+b i/a i) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpair i) (hw i))
      _ ≤ m := hbudget
  have hmean : (∑ i, w i*r i) ≤ (m-2)/4 := by
    have hid : (∑ i, w i*r i) =
        ((∑ i, w i*(a i/b i+b i/a i))-2)/4 := by
      simp only [heq,← mul_div_assoc,mul_sub,← Finset.sum_div,
        Finset.sum_sub_distrib,← Finset.sum_mul,hweight,one_mul]
    rw [hid]
    linarith
  have hj := c1CoshMoment_finite_jensen w r hw hweight hr hmean
  rw [c1CoshMoment_eq_Fcal hm] at hj
  exact hj

theorem c1_commute_nonsing_inv {I : Type*} [Fintype I] [DecidableEq I]
    (A K : QMatrix I) [Invertible K] (hKA : K*A=A*K) :
    A*K⁻¹=K⁻¹*A := by
  calc
    A*K⁻¹ = (K⁻¹*K)*(A*K⁻¹) := by rw [Matrix.inv_mul_of_invertible,Matrix.one_mul]
    _ = K⁻¹*(K*A)*K⁻¹ := by simp only [Matrix.mul_assoc]
    _ = K⁻¹*(A*K)*K⁻¹ := by rw [hKA]
    _ = (K⁻¹*A)*(K*K⁻¹) := by simp only [Matrix.mul_assoc]
    _ = K⁻¹*A := by rw [Matrix.mul_inv_of_invertible,Matrix.mul_one]

theorem c1_regularized_product_identity {I : Type*} [Fintype I] [DecidableEq I]
    {D : QMatrix I} (hD : D.PosSemidef) {x : ℝ} (hx : 0 < x) :
    D*(D+x • (1 : QMatrix I))⁻¹ =
      (1 : QMatrix I)-x • (D+x • (1 : QMatrix I))⁻¹ := by
  have hp := c1_regularized_posDef hD hx
  letI : Invertible (D+x • (1 : QMatrix I)) := hp.isUnit.invertible
  have hd : D=(D+x • (1 : QMatrix I))-x • (1 : QMatrix I) := by abel
  calc
    D*(D+x • (1 : QMatrix I))⁻¹ =
      ((D+x • (1 : QMatrix I))-x • (1 : QMatrix I))*
        (D+x • (1 : QMatrix I))⁻¹ := by rw [← hd]
    _ = _ := by rw [Matrix.sub_mul,Matrix.mul_inv_of_invertible,
      Matrix.smul_mul,Matrix.one_mul]

theorem c1_self_resolvent_comparison {I : Type*} [Fintype I] [DecidableEq I]
    {A D : QMatrix I} (hA : A.IsHermitian) (hD : D.PosSemidef)
    (hDA : (D-A*A).PosSemidef) {x : ℝ} (hx : 0 < x) :
    (D*(D+x • (1 : QMatrix I))⁻¹ -
      A*(D+x • (1 : QMatrix I))⁻¹*A).PosSemidef := by
  let K : QMatrix I := A*A+x • (1 : QMatrix I)
  have hK : K.PosDef := c1_regularized_posDef (c1_hermitian_square_posSemidef hA) hx
  letI : Invertible K := hK.isUnit.invertible
  have hKA : K*A=A*K := by
    dsimp [K]
    simp only [Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,
      Matrix.one_mul,Matrix.mul_one]
    noncomm_ring
  have hcomm := c1_commute_nonsing_inv A K hKA
  have hAid : A*K⁻¹*A=(1 : QMatrix I)-x • K⁻¹ := by
    rw [Matrix.mul_assoc,← hcomm,← Matrix.mul_assoc]
    simpa only [K] using
      c1_regularized_product_identity (c1_hermitian_square_posSemidef hA) hx
  have horder : (K⁻¹-(D+x • (1 : QMatrix I))⁻¹).PosSemidef := by
    apply QuantumProver.SuperchannelDiscrimination.MatrixLog.inverse_order hK
    simpa only [K,add_sub_add_right_eq_sub] using hDA
  have hcon := horder.mul_mul_conjTranspose_same A
  rw [hA.eq,Matrix.mul_sub,Matrix.sub_mul] at hcon
  have hsum := hcon.add (horder.smul hx.le)
  have heq : A*K⁻¹*A-A*(D+x • (1 : QMatrix I))⁻¹*A +
      x • (K⁻¹-(D+x • (1 : QMatrix I))⁻¹) =
      D*(D+x • (1 : QMatrix I))⁻¹-A*(D+x • (1 : QMatrix I))⁻¹*A := by
    rw [hAid,c1_regularized_product_identity hD hx,smul_sub]
    abel
  rwa [heq] at hsum

theorem c1_binary_self_resolvent_comparison {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] {A : QMatrix I} (hA : A.IsHermitian) (Z : Matrix J I ℂ)
    {x : ℝ} (hx : 0 < x) :
    ((A*A+Zᴴ*Z)*(A*A+Zᴴ*Z+x • (1 : QMatrix I))⁻¹ -
      A*(A*A+Zᴴ*Z+x • (1 : QMatrix I))⁻¹*A).PosSemidef := by
  apply c1_self_resolvent_comparison hA
    ((c1_hermitian_square_posSemidef hA).add (Matrix.posSemidef_conjTranspose_mul_self Z))
    _ hx
  have heq : (A*A+Zᴴ*Z)-A*A=Zᴴ*Z := by abel
  rw [heq]
  exact Matrix.posSemidef_conjTranspose_mul_self Z

theorem c1_self_resolvent_trace_comparison {I : Type*} [Fintype I] [DecidableEq I]
    {A D M : QMatrix I} (hA : A.IsHermitian) (hD : D.PosSemidef)
    (hDA : (D-A*A).PosSemidef) (hM : M.PosSemidef) {x : ℝ} (hx : 0 < x) :
    (Matrix.trace ((A*(D+x • (1 : QMatrix I))⁻¹*A)*M)).re ≤
      (Matrix.trace ((D*(D+x • (1 : QMatrix I))⁻¹)*M)).re := by
  exact (Complex.le_def.mp
    (QuantumProver.SuperchannelDiscrimination.KrausCompletion.trace_mul_mono_of_posSemidef
      (c1_self_resolvent_comparison hA hD hDA hx) hM)).1

theorem c1_left_self_integrand_comparison {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] {A D : QMatrix I} {R : QMatrix J}
    (hA : A.IsHermitian) (hD : D.PosSemidef) (hDA : (D-A*A).PosSemidef)
    (hR : R.PosSemidef) (Z : Matrix J I ℂ) {x : ℝ} (hx : 0 < x) :
    (Matrix.trace ((Z*A)ᴴ*R*(Z*A)*(D+x • (1 : QMatrix I))⁻¹)).re ≤
      (Matrix.trace ((Zᴴ*R*Z)*(D*(D+x • (1 : QMatrix I))⁻¹))).re := by
  have h := c1_self_resolvent_trace_comparison hA hD hDA
    (hR.conjTranspose_mul_mul_same Z) hx
  have heq : Matrix.trace ((Z*A)ᴴ*R*(Z*A)*(D+x • (1 : QMatrix I))⁻¹) =
      Matrix.trace ((A*(D+x • (1 : QMatrix I))⁻¹*A)*(Zᴴ*R*Z)) := by
    rw [Matrix.conjTranspose_mul,hA.eq]
    calc
      _ = Matrix.trace (A*((Zᴴ*R*Z)*A*(D+x • (1 : QMatrix I))⁻¹)) := by
        congr 1
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (((Zᴴ*R*Z)*A*(D+x • (1 : QMatrix I))⁻¹)*A) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Zᴴ*R*Z)*(A*(D+x • (1 : QMatrix I))⁻¹*A)) := by
        congr 1
        simp only [Matrix.mul_assoc]
      _ = _ := Matrix.trace_mul_comm _ _
  rw [heq,Matrix.trace_mul_comm (Zᴴ*R*Z) (D*(D+x • (1 : QMatrix I))⁻¹)]
  exact h

theorem c1_nonlinear_scalar_integral {w T : ℝ} (hw : 0 < w) (hT : 0 < T) :
    (∫ x in 0..T, Real.log (x+w)-Real.log x-w*(x+w)⁻¹) =
      T*Real.log (1+w/T) := by
  have hl : IntervalIntegrable Real.log MeasureTheory.volume 0 T :=
    intervalIntegral.intervalIntegrable_log'
  have hlw : IntervalIntegrable (fun x : ℝ => Real.log (x+w))
      MeasureTheory.volume 0 T :=
    (IntervalIntegrable.comp_add_right_iff (f := Real.log) (c := w)).2
      intervalIntegral.intervalIntegrable_log'
  have hinv : IntervalIntegrable (fun x : ℝ => (x+w)⁻¹)
      MeasureTheory.volume 0 T := by
    have hz (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) T) : x+w ≠ 0 := by
      have hx0 : 0 ≤ x := (by simpa only [Set.uIcc_of_le hT.le] using hx :
        x ∈ Set.Icc (0 : ℝ) T).1
      exact ne_of_gt (by linarith)
    exact ((continuous_id.add continuous_const :
      Continuous (fun x : ℝ => x+w)).continuousOn.inv₀ hz).intervalIntegrable
  rw [intervalIntegral.integral_sub (hlw.sub hl) (hinv.const_mul w),
    intervalIntegral.integral_sub hlw hl,intervalIntegral.integral_const_mul,
    c1_integral_shifted_log w 0 T,integral_log,c1_integral_shifted_inv hw hT.le]
  have hratio : 1+w/T=(T+w)/T := by field_simp [ne_of_gt hT]
  rw [hratio,Real.log_div (ne_of_gt (by linarith : 0 < T+w)) (ne_of_gt hT)]
  simp only [zero_add,zero_mul,add_zero]
  ring

theorem c1_nonlinear_scalar_primitive_bounds {w T : ℝ}
    (hw : 0 ≤ w) (hT : 0 < T) :
    0 ≤ T*Real.log (1+w/T) ∧ T*Real.log (1+w/T) ≤ w := by
  have hratio : 0 ≤ w/T := div_nonneg hw hT.le
  constructor
  · exact mul_nonneg hT.le (Real.log_nonneg (by linarith))
  · have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+w/T)
    have hm := mul_le_mul_of_nonneg_left hl hT.le
    have heq : T*((1+w/T)-1)=w := by field_simp [ne_of_gt hT]; ring
    rwa [heq] at hm

theorem c1_nonlinear_finite_primitive_bound {K : Type*} [Fintype K]
    (w : K → ℝ) (hw : ∀ i, 0 ≤ w i) {T : ℝ} (hT : 0 < T) :
    (∑ i, T*Real.log (1+w i/T)) ≤ ∑ i, w i :=
  Finset.sum_le_sum (fun i _ => (c1_nonlinear_scalar_primitive_bounds (hw i) hT).2)

theorem c1_binary_diagonal_trace (A : QMatrix I) (B : QMatrix J)
    (Z : Matrix J I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A*A+Zᴴ*Z)).re+(Matrix.trace (B*B+Z*Zᴴ)).re =
      (Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re := by
  have hAA : (Matrix.trace (A*A)).re=c1HsMass A := by
    simpa only [hA.eq] using c1_trace_gram A
  have hBB : (Matrix.trace (B*B)).re=c1HsMass B := by
    simpa only [hB.eq] using c1_trace_gram B
  have hZZ : (Matrix.trace (Z*Zᴴ)).re=c1HsMass Z := by
    simpa only [Matrix.conjTranspose_conjTranspose,c1HsMass_conjTranspose] using
      c1_trace_gram Zᴴ
  have hH := c1Binary_isHermitian Z hA hB
  have ht : (Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re =
      c1HsMass (c1Binary A B Z) := by
    simpa only [hH.eq] using c1_trace_gram (c1Binary A B Z)
  rw [Matrix.trace_add,Matrix.trace_add,Complex.add_re,Complex.add_re,
    hAA,hBB,c1_trace_gram,hZZ,ht,c1Binary_hs_mass]
  ring

theorem c1_binary_modular_trace_budget (A : QMatrix I) (B : QMatrix J)
    (Z : Matrix J I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    {x : ℝ} (hx : 0 < x) :
    (Matrix.trace ((B*B+Z*Zᴴ)*(Z*(A*A+Zᴴ*Z+x • (1 : QMatrix I))⁻¹*Zᴴ))).re +
      (Matrix.trace ((A*A+Zᴴ*Z)*(Zᴴ*(B*B+Z*Zᴴ+x • (1 : QMatrix J))⁻¹*Z))).re ≤
      (Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re := by
  have hD0 : (A*A+Zᴴ*Z).PosSemidef :=
    (c1_hermitian_square_posSemidef hA).add (Matrix.posSemidef_conjTranspose_mul_self Z)
  have hD1 : (B*B+Z*Zᴴ).PosSemidef :=
    (c1_hermitian_square_posSemidef hB).add (Matrix.posSemidef_self_mul_conjTranspose Z)
  have hl := (Complex.le_def.mp
    (QuantumProver.SuperchannelDiscrimination.KrausCompletion.trace_mul_mono_of_posSemidef
      (c1_inverse_noise_contraction hA Z hx) hD1)).1
  have hr := (Complex.le_def.mp
    (QuantumProver.SuperchannelDiscrimination.KrausCompletion.trace_mul_mono_of_posSemidef
      (c1_partner_inverse_noise_contraction hB Z hx) hD0)).1
  rw [Matrix.one_mul] at hl hr
  have hl' :
      (Matrix.trace ((B*B+Z*Zᴴ)*(Z*(A*A+Zᴴ*Z+x • (1 : QMatrix I))⁻¹*Zᴴ))).re ≤
        (Matrix.trace (B*B+Z*Zᴴ)).re := by
    rw [Matrix.trace_mul_comm]
    exact hl
  have hr' :
      (Matrix.trace ((A*A+Zᴴ*Z)*(Zᴴ*(B*B+Z*Zᴴ+x • (1 : QMatrix J))⁻¹*Z))).re ≤
        (Matrix.trace (A*A+Zᴴ*Z)).re := by
    rw [Matrix.trace_mul_comm]
    exact hr
  have hs := add_le_add hr' hl'
  rw [c1_binary_diagonal_trace A B Z hA hB] at hs
  simpa only [add_comm] using hs

theorem c1_trace_cross_real_comm (F G : Matrix J I ℂ) :
    (Matrix.trace (Gᴴ*F)).re=(Matrix.trace (Fᴴ*G)).re := by
  have h : Matrix.trace (Gᴴ*F)=star (Matrix.trace (Fᴴ*G)) := by
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose] using
      Matrix.trace_conjTranspose (Fᴴ*G)
  rw [h]
  simp

theorem c1_hsSq_add (F G : Matrix J I ℂ) :
    hsSq (F+G)=hsSq F+hsSq G+2*(Matrix.trace (Fᴴ*G)).re := by
  unfold hsSq
  rw [Matrix.conjTranspose_add,Matrix.add_mul,Matrix.mul_add,Matrix.mul_add]
  simp only [Matrix.trace_add,Complex.add_re]
  rw [c1_trace_cross_real_comm F G]
  ring

theorem c1_hsSq_sub (F G : Matrix J I ℂ) :
    hsSq (F-G)=hsSq F+hsSq G-2*(Matrix.trace (Fᴴ*G)).re := by
  unfold hsSq
  rw [Matrix.conjTranspose_sub,Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub]
  simp only [Matrix.trace_sub,Complex.sub_re]
  rw [c1_trace_cross_real_comm F G]
  ring

theorem c1_mixed_trace_young (F G : Matrix J I ℂ) :
    |(Matrix.trace (Fᴴ*G)).re| ≤ (hsSq F+hsSq G)/2 := by
  have hp := hsSq_nonneg (F+G)
  have hm := hsSq_nonneg (F-G)
  rw [c1_hsSq_add] at hp
  rw [c1_hsSq_sub] at hm
  exact abs_le.2 ⟨by linarith,by linarith⟩

theorem c1_hsSq_conjTranspose (F : Matrix J I ℂ) : hsSq Fᴴ=hsSq F := by
  rw [hsSq_eq_c1HsMass,hsSq_eq_c1HsMass,c1HsMass_conjTranspose]

theorem c1_mixed_left_norm_comparison {B D R : QMatrix J}
    (hB : B.IsHermitian) (hR : R.IsHermitian)
    (hDB : (D-B*B).PosSemidef) (Z : Matrix J I ℂ) :
    hsSq (B*R*Z) ≤ (Matrix.trace (Zᴴ*R*D*R*Z)).re := by
  have h := (Complex.le_def.mp
    (hDB.conjTranspose_mul_mul_same (R*Z)).trace_nonneg).1
  have heq : Matrix.trace ((R*Z)ᴴ*(D-B*B)*(R*Z)) =
      Matrix.trace (Zᴴ*R*D*R*Z)-Matrix.trace ((B*R*Z)ᴴ*(B*R*Z)) := by
    simp only [Matrix.conjTranspose_mul,hR.eq,hB.eq,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.trace_sub,Matrix.mul_assoc]
  rw [heq,Complex.sub_re] at h
  exact sub_nonneg.mp h

theorem c1_mixed_right_norm_comparison {A D R : QMatrix I}
    (hA : A.IsHermitian) (hR : R.IsHermitian)
    (hDA : (D-A*A).PosSemidef) (Z : Matrix J I ℂ) :
    hsSq (Z*R*A) ≤ (Matrix.trace (Z*R*D*R*Zᴴ)).re := by
  have h := c1_mixed_left_norm_comparison hA hR hDA Zᴴ
  have heq : A*R*Zᴴ=(Z*R*A)ᴴ := by
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,hA.eq,hR.eq]
    simp only [Matrix.mul_assoc]
  rw [heq,c1_hsSq_conjTranspose,Matrix.conjTranspose_conjTranspose] at h
  exact h

theorem c1_mixed_integrand_payment {A R0 : QMatrix I} {B R1 : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hR0 : R0.IsHermitian) (hR1 : R1.IsHermitian) (Z : Matrix J I ℂ) :
    |(Matrix.trace (Zᴴ*R1*B*Z*R0*A)).re| ≤
      (hsSq (B*R1*Z)+hsSq (Z*R0*A))/2 := by
  have h := c1_mixed_trace_young (B*R1*Z) (Z*R0*A)
  simpa only [Matrix.conjTranspose_mul,hR1.eq,hB.eq,Matrix.mul_assoc] using h

theorem c1_psd_shifted_inverse_cfc {D : QMatrix I} (hD : D.PosSemidef)
    {x : ℝ} (hx : 0 < x) :
    (D+x • (1 : QMatrix I))⁻¹=cfc (fun d : ℝ => (d+x)⁻¹) D := by
  have hspec : ∀ d ∈ spectrum ℝ D, d+x ≠ 0 := by
    intro d hd
    rw [hD.1.spectrum_real_eq_range_eigenvalues] at hd
    obtain ⟨i,rfl⟩ := hd
    exact ne_of_gt (add_pos_of_nonneg_of_pos (hD.eigenvalues_nonneg i) hx)
  have hshift : cfc (fun d : ℝ => d+x) D=D+x • (1 : QMatrix I) := by
    rw [cfc_add_const (p := IsSelfAdjoint) x (fun d : ℝ => d) D
      (D.finite_real_spectrum.continuousOn _) hD.1,
      cfc_id' (p := IsSelfAdjoint) ℝ D hD.1]
    rw [Algebra.algebraMap_eq_smul_one]
  have h := cfc_inv (p := IsSelfAdjoint) (f := fun d : ℝ => d+x)
    (a := D) hspec (D.finite_real_spectrum.continuousOn _) hD.1
  rw [hshift,← Matrix.nonsing_inv_eq_ringInverse] at h
  exact h.symm

theorem c1_weighted_resolvent_cfc {D : QMatrix I} (hD : D.PosSemidef)
    {x : ℝ} (hx : 0 < x) :
    (D+x • (1 : QMatrix I))⁻¹*D*(D+x • (1 : QMatrix I))⁻¹ =
      cfc (fun d : ℝ => d*(d+x)⁻¹*(d+x)⁻¹) D := by
  have hid : cfc (fun d : ℝ => d) D=D :=
    cfc_id' (p := IsSelfAdjoint) ℝ D hD.1
  have hf : (fun d : ℝ => d*(d+x)⁻¹*(d+x)⁻¹) =
      (fun d : ℝ => ((d+x)⁻¹*d)*(d+x)⁻¹) := by
    funext d
    ring
  rw [hf,cfc_mul (p := IsSelfAdjoint) (fun d : ℝ => (d+x)⁻¹*d)
      (fun d : ℝ => (d+x)⁻¹) D (D.finite_real_spectrum.continuousOn _)
      (D.finite_real_spectrum.continuousOn _),
    cfc_mul (p := IsSelfAdjoint) (fun d : ℝ => (d+x)⁻¹)
      (fun d : ℝ => d) D (D.finite_real_spectrum.continuousOn _)
      (D.finite_real_spectrum.continuousOn _),
    hid,← c1_psd_shifted_inverse_cfc hD hx]

theorem c1_weighted_resolvent_scalar_integral {d ε T : ℝ}
    (hd : 0 ≤ d) (hε : 0 < ε) (hT : ε ≤ T) :
    (∫ x in ε..T, d*(x+d)⁻¹*(x+d)⁻¹) =
      d*(ε+d)⁻¹-d*(T+d)⁻¹ := by
  have ha : 0 < ε+d := by linarith
  have ht : 0 ≤ T-ε := by linarith
  have heq : (∫ x in ε..T, d*(x+d)⁻¹*(x+d)⁻¹) =
      d*(∫ y in 0..(T-ε), (y+(ε+d))⁻¹*(y+(ε+d))⁻¹) := by
    rw [← intervalIntegral.integral_const_mul]
    have hf : (fun y : ℝ => d*((y+ε)+d)⁻¹*((y+ε)+d)⁻¹) =
        (fun y : ℝ => d*((y+(ε+d))⁻¹*(y+(ε+d))⁻¹)) := by
      funext y
      simp only [add_assoc,mul_assoc]
    have hs := intervalIntegral.integral_comp_add_right
      (fun x : ℝ => d*(x+d)⁻¹*(x+d)⁻¹) ε (a := 0) (b := T-ε)
    rw [hf] at hs
    simpa only [zero_add,sub_add_cancel] using hs.symm
  rw [heq,c1_pair_resolvent_integral_eq ha ht]
  have hsum : T-ε+(ε+d)=T+d := by ring
  rw [hsum]
  ring

theorem c1_weighted_resolvent_scalar_payment {d ε T : ℝ}
    (hd : 0 ≤ d) (hε : 0 < ε) (hT : ε ≤ T) :
    0 ≤ d*(ε+d)⁻¹-d*(T+d)⁻¹ ∧
      d*(ε+d)⁻¹-d*(T+d)⁻¹ ≤ 1 := by
  have hεd : 0 < ε+d := by linarith
  have hTd : 0 < T+d := by linarith
  have hmon : (T+d)⁻¹ ≤ (ε+d)⁻¹ :=
    (inv_le_inv₀ hTd hεd).2 (by linarith)
  have hle : d*(ε+d)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    apply (div_le_one hεd).2
    linarith
  exact ⟨sub_nonneg.mpr (mul_le_mul_of_nonneg_left hmon hd),
    (sub_le_self _ (mul_nonneg hd (inv_nonneg.mpr hTd.le))).trans hle⟩

theorem c1_weighted_cfc_trace_spectral {D : QMatrix J} (hD : D.IsHermitian)
    (f : ℝ → ℝ) (Z : Matrix J I ℂ) :
    (Matrix.trace (Zᴴ*cfc f D*Z)).re =
      ∑ a : I, ∑ b : J, f (hD.eigenvalues b)*
        Complex.normSq (((hD.eigenvectorUnitary : QMatrix J)ᴴ*Z) b a) := by
  let Y : Matrix J I ℂ := (hD.eigenvectorUnitary : QMatrix J)ᴴ*Z
  rw [hD.cfc_eq f]
  change (Matrix.trace (Zᴴ*((hD.eigenvectorUnitary : QMatrix J)*
    Matrix.diagonal (fun b => (f (hD.eigenvalues b) : ℂ))*
    (hD.eigenvectorUnitary : QMatrix J)ᴴ)*Z)).re = _
  have heq : Zᴴ*((hD.eigenvectorUnitary : QMatrix J)*
      Matrix.diagonal (fun b => (f (hD.eigenvalues b) : ℂ))*
      (hD.eigenvectorUnitary : QMatrix J)ᴴ)*Z =
      Yᴴ*Matrix.diagonal (fun b => (f (hD.eigenvalues b) : ℂ))*Y := by
    dsimp [Y]
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
  rw [heq]
  have hdiag : Matrix.diagonal (fun b => (f (hD.eigenvalues b) : ℂ))*Y =
      (fun b a => (f (hD.eigenvalues b) : ℂ)*Y b a) := by
    ext b a
    simp [Matrix.mul_apply,Matrix.diagonal_apply]
  rw [Matrix.mul_assoc,hdiag]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,
    Complex.star_def]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ b : J, star (Y b a)*((f (hD.eigenvalues b) : ℂ)*Y b a)).re =
    ∑ b : J, f (hD.eigenvalues b)*Complex.normSq (Y b a)
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Complex.star_def]
  have hp : starRingEnd ℂ (Y b a)*((f (hD.eigenvalues b) : ℂ)*Y b a) =
      (f (hD.eigenvalues b) : ℂ)*(starRingEnd ℂ (Y b a)*Y b a) := by ring
  rw [hp,← Complex.normSq_eq_conj_mul_self,Complex.re_ofReal_mul,Complex.ofReal_re]

theorem c1_weighted_spectral_mass {D : QMatrix J} (hD : D.IsHermitian)
    (Z : Matrix J I ℂ) :
    (∑ a : I, ∑ b : J,
      Complex.normSq (((hD.eigenvectorUnitary : QMatrix J)ᴴ*Z) b a))=hsSq Z := by
  have h := c1_weighted_cfc_trace_spectral hD (fun _ : ℝ => 1) Z
  rw [cfc_const_one (p := IsSelfAdjoint) ℝ D hD,Matrix.mul_one] at h
  simpa only [one_mul,hsSq] using h.symm

theorem c1_weighted_resolvent_integral_bound {D : QMatrix J}
    (hD : D.PosSemidef) (Z : Matrix J I ℂ) {ε T : ℝ}
    (hε : 0 < ε) (hT : ε ≤ T) :
    (∫ x in ε..T, (Matrix.trace (Zᴴ*
      ((D+x • (1 : QMatrix J))⁻¹*D*(D+x • (1 : QMatrix J))⁻¹)*Z)).re) ≤ hsSq Z := by
  let e : J → ℝ := hD.1.eigenvalues
  let w : I → J → ℝ := fun a b =>
    Complex.normSq (((hD.1.eigenvectorUnitary : QMatrix J)ᴴ*Z) b a)
  let p : I → J → ℝ → ℝ := fun a b x => e b*(e b+x)⁻¹*(e b+x)⁻¹*w a b
  have he (b : J) : 0 ≤ e b := hD.eigenvalues_nonneg b
  have hw (a : I) (b : J) : 0 ≤ w a b := Complex.normSq_nonneg _
  have hi (a : I) (b : J) : IntervalIntegrable (p a b)
      MeasureTheory.volume ε T := by
    have hz (x : ℝ) (hx : x ∈ Set.uIcc ε T) : e b+x ≠ 0 := by
      have hxε : ε ≤ x := (by simpa only [Set.uIcc_of_le hT] using hx :
        x ∈ Set.Icc ε T).1
      exact ne_of_gt (by linarith [he b])
    have hc : ContinuousOn (fun x : ℝ => (e b+x)⁻¹) (Set.uIcc ε T) :=
      (continuous_const.add continuous_id :
        Continuous (fun x : ℝ => e b+x)).continuousOn.inv₀ hz
    exact (((hc.const_mul (e b)).mul hc).mul_const (w a b)).intervalIntegrable
  have hai (a : I) : IntervalIntegrable (fun x : ℝ => ∑ b, p a b x)
      MeasureTheory.volume ε T := by
    have h := IntervalIntegrable.sum Finset.univ (fun b _ => hi a b)
    have hfun : (∑ b, p a b)=(fun x : ℝ => ∑ b, p a b x) := by
      funext x
      simp only [Finset.sum_apply]
    rw [hfun] at h
    exact h
  have hp (a : I) (b : J) :
      (∫ x in ε..T, p a b x)=
        (e b*(ε+e b)⁻¹-e b*(T+e b)⁻¹)*w a b := by
    dsimp [p]
    rw [intervalIntegral.integral_mul_const]
    have hfun : (fun x : ℝ => e b*(e b+x)⁻¹*(e b+x)⁻¹) =
        (fun x : ℝ => e b*(x+e b)⁻¹*(x+e b)⁻¹) := by
      funext x
      rw [add_comm (e b) x]
    rw [hfun,c1_weighted_resolvent_scalar_integral (he b) hε hT]
  have hbridge (x : ℝ) (hx : 0 < x) :
      (Matrix.trace (Zᴴ*((D+x • (1 : QMatrix J))⁻¹*D*
        (D+x • (1 : QMatrix J))⁻¹)*Z)).re = ∑ a, ∑ b, p a b x := by
    rw [c1_weighted_resolvent_cfc hD hx,c1_weighted_cfc_trace_spectral hD.1]
  have hint :
      (∫ x in ε..T, (Matrix.trace (Zᴴ*((D+x • (1 : QMatrix J))⁻¹*D*
        (D+x • (1 : QMatrix J))⁻¹)*Z)).re) =
      ∑ a, ∑ b, (e b*(ε+e b)⁻¹-e b*(T+e b)⁻¹)*w a b := by
    calc
      _ = ∫ x in ε..T, ∑ a, ∑ b, p a b x := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hxε : ε ≤ x := (by simpa only [Set.uIcc_of_le hT] using hx :
          x ∈ Set.Icc ε T).1
        exact hbridge x (hε.trans_le hxε)
      _ = ∑ a, ∫ x in ε..T, ∑ b, p a b x :=
        intervalIntegral.integral_finsetSum (fun a _ => hai a)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [intervalIntegral.integral_finsetSum (fun b _ => hi a b)]
        exact Finset.sum_congr rfl (fun b _ => hp a b)
  rw [hint]
  calc
    _ ≤ ∑ a, ∑ b, w a b := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (c1_weighted_resolvent_scalar_payment (he b) hε hT).2 (hw a b)
    _ = hsSq Z := c1_weighted_spectral_mass hD.1 Z

theorem c1_psd_resolvent_continuousOn {D : QMatrix I} (hD : D.PosSemidef)
    {ε T : ℝ} (hε : 0 < ε) (hT : ε ≤ T) :
    ContinuousOn (fun x : ℝ => (D+x • (1 : QMatrix I))⁻¹)
      (Set.uIcc ε T) := by
  have hf : (fun x : ℝ => (D+x • (1 : QMatrix I))⁻¹) =
      (fun x : ℝ => Ring.inverse (D+x • (1 : QMatrix I))) := by
    funext x
    exact Matrix.nonsing_inv_eq_ringInverse _
  rw [hf]
  intro x hx
  have hxε : ε ≤ x := (by simpa only [Set.uIcc_of_le hT] using hx :
    x ∈ Set.Icc ε T).1
  have hp := c1_regularized_posDef hD (hε.trans_le hxε)
  have hc : ContinuousAt Ring.inverse (D+x • (1 : QMatrix I)) := by
    obtain ⟨u,hu⟩ := hp.isUnit
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have hs : Continuous (fun y : ℝ => D+y • (1 : QMatrix I)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  exact (hc.comp (f := fun y : ℝ => D+y • (1 : QMatrix I)) hs.continuousAt).continuousWithinAt

theorem c1_mixed_trace_continuous (A : QMatrix I) (B : QMatrix J)
    (Z : Matrix J I ℂ) :
    Continuous (fun q : QMatrix I × QMatrix J =>
      (Matrix.trace (Zᴴ*q.2*B*Z*q.1*A)).re) := by
  have h1 : Continuous (fun q : QMatrix I × QMatrix J => Zᴴ*q.2) :=
    (continuous_const : Continuous (fun _ : QMatrix I × QMatrix J => Zᴴ)).matrix_mul
      (continuous_snd : Continuous (fun q : QMatrix I × QMatrix J => q.2))
  have h2 : Continuous (fun q : QMatrix I × QMatrix J => Zᴴ*q.2*B) :=
    h1.matrix_mul (continuous_const : Continuous (fun _ : QMatrix I × QMatrix J => B))
  have h3 : Continuous (fun q : QMatrix I × QMatrix J => Zᴴ*q.2*B*Z) :=
    h2.matrix_mul (continuous_const : Continuous (fun _ : QMatrix I × QMatrix J => Z))
  have h4 : Continuous (fun q : QMatrix I × QMatrix J => Zᴴ*q.2*B*Z*q.1) :=
    h3.matrix_mul (continuous_fst : Continuous (fun q : QMatrix I × QMatrix J => q.1))
  have hmat : Continuous (fun q : QMatrix I × QMatrix J => Zᴴ*q.2*B*Z*q.1*A) :=
    h4.matrix_mul (continuous_const : Continuous (fun _ : QMatrix I × QMatrix J => A))
  exact Complex.continuous_re.comp hmat.matrix_trace

theorem c1_weighted_trace_continuous (D : QMatrix J) (Z : Matrix J I ℂ) :
    Continuous (fun R : QMatrix J => (Matrix.trace (Zᴴ*(R*D*R)*Z)).re) := by
  have h1 : Continuous (fun R : QMatrix J => R*D) :=
    (continuous_id : Continuous (fun R : QMatrix J => R)).matrix_mul
      (continuous_const : Continuous (fun _ : QMatrix J => D))
  have h2 : Continuous (fun R : QMatrix J => R*D*R) :=
    h1.matrix_mul (continuous_id : Continuous (fun R : QMatrix J => R))
  have h3 : Continuous (fun R : QMatrix J => Zᴴ*(R*D*R)) :=
    (continuous_const : Continuous (fun _ : QMatrix J => Zᴴ)).matrix_mul h2
  have hmat : Continuous (fun R : QMatrix J => Zᴴ*(R*D*R)*Z) :=
    h3.matrix_mul (continuous_const : Continuous (fun _ : QMatrix J => Z))
  exact Complex.continuous_re.comp hmat.matrix_trace

theorem c1_mixed_endpoint_integrand_payment {A D0 R0 : QMatrix I}
    {B D1 R1 : QMatrix J} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hR0 : R0.IsHermitian) (hR1 : R1.IsHermitian)
    (hDA : (D0-A*A).PosSemidef) (hDB : (D1-B*B).PosSemidef)
    (Z : Matrix J I ℂ) :
    |(Matrix.trace (Zᴴ*R1*B*Z*R0*A)).re| ≤
      ((Matrix.trace (Z*(R0*D0*R0)*Zᴴ)).re+
        (Matrix.trace (Zᴴ*(R1*D1*R1)*Z)).re)/2 := by
  have hy := c1_mixed_integrand_payment hA hB hR0 hR1 Z
  have hl := c1_mixed_left_norm_comparison hB hR1 hDB Z
  have hr := c1_mixed_right_norm_comparison hA hR0 hDA Z
  have hl' : hsSq (B*R1*Z) ≤ (Matrix.trace (Zᴴ*(R1*D1*R1)*Z)).re := by
    simpa only [Matrix.mul_assoc] using hl
  have hr' : hsSq (Z*R0*A) ≤ (Matrix.trace (Z*(R0*D0*R0)*Zᴴ)).re := by
    simpa only [Matrix.mul_assoc] using hr
  exact hy.trans (by linarith)

theorem c1_integral_abs_two_payments {f p0 p1 : ℝ → ℝ} {ε T u : ℝ}
    (hT : ε ≤ T) (hf : IntervalIntegrable f MeasureTheory.volume ε T)
    (hi0 : IntervalIntegrable p0 MeasureTheory.volume ε T)
    (hi1 : IntervalIntegrable p1 MeasureTheory.volume ε T)
    (hpayment : ∀ x ∈ Set.Icc ε T, |f x| ≤ (p0 x+p1 x)/2)
    (hb0 : (∫ x in ε..T, p0 x) ≤ u) (hb1 : (∫ x in ε..T, p1 x) ≤ u) :
    |∫ x in ε..T, f x| ≤ u := by
  calc
    _ ≤ ∫ x in ε..T, |f x| := intervalIntegral.abs_integral_le_integral_abs hT
    _ ≤ ∫ x in ε..T, (p0 x+p1 x)/2 :=
      intervalIntegral.integral_mono_on hT hf.abs ((hi0.add hi1).div_const 2) hpayment
    _ = ((∫ x in ε..T, p0 x)+(∫ x in ε..T, p1 x))/2 := by
      rw [intervalIntegral.integral_div,intervalIntegral.integral_add hi0 hi1]
    _ ≤ u := by linarith

theorem c1_mixed_resolvent_integral_bound {A D0 : QMatrix I} {B D1 : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hD0 : D0.PosSemidef) (hD1 : D1.PosSemidef)
    (hDA : (D0-A*A).PosSemidef) (hDB : (D1-B*B).PosSemidef)
    (Z : Matrix J I ℂ) {ε T : ℝ} (hε : 0 < ε) (hT : ε ≤ T) :
    |∫ x in ε..T, (Matrix.trace
      (Zᴴ*(D1+x • (1 : QMatrix J))⁻¹*B*Z*
        (D0+x • (1 : QMatrix I))⁻¹*A)).re| ≤ hsSq Z := by
  let R0 : ℝ → QMatrix I := fun x => (D0+x • (1 : QMatrix I))⁻¹
  let R1 : ℝ → QMatrix J := fun x => (D1+x • (1 : QMatrix J))⁻¹
  let f : ℝ → ℝ := fun x => (Matrix.trace (Zᴴ*R1 x*B*Z*R0 x*A)).re
  let p0 : ℝ → ℝ := fun x => (Matrix.trace (Z*(R0 x*D0*R0 x)*Zᴴ)).re
  let p1 : ℝ → ℝ := fun x => (Matrix.trace (Zᴴ*(R1 x*D1*R1 x)*Z)).re
  have hc0 : ContinuousOn R0 (Set.uIcc ε T) :=
    c1_psd_resolvent_continuousOn hD0 hε hT
  have hc1 : ContinuousOn R1 (Set.uIcc ε T) :=
    c1_psd_resolvent_continuousOn hD1 hε hT
  have hpair : ContinuousOn (fun x : ℝ => (R0 x,R1 x)) (Set.uIcc ε T) :=
    hc0.prodMk hc1
  have hf := (c1_mixed_trace_continuous A B Z).comp_continuousOn hpair
  change ContinuousOn f (Set.uIcc ε T) at hf
  have hp0_fun : Continuous (fun R : QMatrix I =>
      (Matrix.trace (Z*(R*D0*R)*Zᴴ)).re) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      c1_weighted_trace_continuous D0 Zᴴ
  have hp0 : ContinuousOn p0 (Set.uIcc ε T) := hp0_fun.comp_continuousOn hc0
  have hp1 : ContinuousOn p1 (Set.uIcc ε T) :=
    (c1_weighted_trace_continuous D1 Z).comp_continuousOn hc1
  have hi0 : IntervalIntegrable p0 MeasureTheory.volume ε T := hp0.intervalIntegrable
  have hi1 : IntervalIntegrable p1 MeasureTheory.volume ε T := hp1.intervalIntegrable
  have hpayment (x : ℝ) (hx : x ∈ Set.Icc ε T) :
      |f x| ≤ (p0 x+p1 x)/2 := by
    have hx0 : 0 < x := hε.trans_le hx.1
    have hR0 : (R0 x).IsHermitian := (c1_regularized_posDef hD0 hx0).inv.1
    have hR1 : (R1 x).IsHermitian := (c1_regularized_posDef hD1 hx0).inv.1
    exact c1_mixed_endpoint_integrand_payment hA hB hR0 hR1 hDA hDB Z
  have hb0 : (∫ x in ε..T, p0 x) ≤ hsSq Z := by
    have h := c1_weighted_resolvent_integral_bound hD0 Zᴴ hε hT
    simpa only [p0,R0,Matrix.conjTranspose_conjTranspose,c1_hsSq_conjTranspose] using h
  have hb1 : (∫ x in ε..T, p1 x) ≤ hsSq Z :=
    c1_weighted_resolvent_integral_bound hD1 Z hε hT
  change |∫ x in ε..T, f x| ≤ hsSq Z
  exact c1_integral_abs_two_payments hT hf.intervalIntegrable hi0 hi1 hpayment hb0 hb1

theorem c1_binary_mixed_resolvent_integral_bound
    {A : QMatrix I} {B : QMatrix J} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (Z : Matrix J I ℂ) {ε T : ℝ} (hε : 0 < ε) (hT : ε ≤ T) :
    |∫ x in ε..T, (Matrix.trace
      (Zᴴ*(B*B+Z*Zᴴ+x • (1 : QMatrix J))⁻¹*B*Z*
        (A*A+Zᴴ*Z+x • (1 : QMatrix I))⁻¹*A)).re| ≤ hsSq Z := by
  have hD0 : (A*A+Zᴴ*Z).PosSemidef :=
    (c1_hermitian_square_posSemidef hA).add (Matrix.posSemidef_conjTranspose_mul_self Z)
  have hD1 : (B*B+Z*Zᴴ).PosSemidef :=
    (c1_hermitian_square_posSemidef hB).add (Matrix.posSemidef_self_mul_conjTranspose Z)
  have hDA : ((A*A+Zᴴ*Z)-A*A).PosSemidef := by
    simpa only [add_sub_cancel_left] using Matrix.posSemidef_conjTranspose_mul_self Z
  have hDB : ((B*B+Z*Zᴴ)-B*B).PosSemidef := by
    simpa only [add_sub_cancel_left] using Matrix.posSemidef_self_mul_conjTranspose Z
  exact c1_mixed_resolvent_integral_bound hA hB hD0 hD1 hDA hDB Z hε hT

theorem c1_two_endpoint_cfc_trace_spectral {D0 : QMatrix I} {D1 : QMatrix J}
    (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian)
    (f g : ℝ → ℝ) (Z : Matrix J I ℂ) :
    (Matrix.trace (Zᴴ*cfc f D1*Z*cfc g D0)).re =
      ∑ a : I, ∑ b : J,
        f (hD1.eigenvalues b)*g (hD0.eigenvalues a)*
          Complex.normSq (((hD1.eigenvectorUnitary : QMatrix J)ᴴ*Z*
            (hD0.eigenvectorUnitary : QMatrix I)) b a) := by
  let U0 : QMatrix I := hD0.eigenvectorUnitary
  let U1 : QMatrix J := hD1.eigenvectorUnitary
  let Y : Matrix J I ℂ := U1ᴴ*Z*U0
  let F : QMatrix J := Matrix.diagonal (fun b => (f (hD1.eigenvalues b) : ℂ))
  let G : QMatrix I := Matrix.diagonal (fun a => (g (hD0.eigenvalues a) : ℂ))
  rw [hD1.cfc_eq f,hD0.cfc_eq g]
  change (Matrix.trace (Zᴴ*(U1*F*U1ᴴ)*Z*(U0*G*U0ᴴ))).re = _
  have heq : Matrix.trace (Zᴴ*(U1*F*U1ᴴ)*Z*(U0*G*U0ᴴ)) =
      Matrix.trace (Yᴴ*F*Y*G) := by
    calc
      _ = Matrix.trace ((Zᴴ*U1*F*U1ᴴ*Z*U0*G)*U0ᴴ) := by
        congr 1
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (U0ᴴ*(Zᴴ*U1*F*U1ᴴ*Z*U0*G)) := Matrix.trace_mul_comm _ _
      _ = _ := by
        dsimp [Y]
        congr 1
        simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
  rw [heq]
  change (Matrix.trace (Yᴴ*F*Y*G)).re =
    ∑ a : I, ∑ b : J,
      f (hD1.eigenvalues b)*g (hD0.eigenvalues a)*Complex.normSq (Y b a)
  change (∑ a : I, (Yᴴ*F*Y*G) a a).re = _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hentry : (Yᴴ*F*Y) a a =
      ∑ b : J, star (Y b a)*(f (hD1.eigenvalues b) : ℂ)*Y b a := by
    change (Yᴴ*Matrix.diagonal (fun b => (f (hD1.eigenvalues b) : ℂ))*Y) a a = _
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro b _
    rw [Matrix.mul_diagonal,Matrix.conjTranspose_apply]
  change (((Yᴴ*F*Y)*Matrix.diagonal (fun a => (g (hD0.eigenvalues a) : ℂ))) a a).re = _
  rw [Matrix.mul_diagonal,hentry,Finset.sum_mul,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro b _
  have he : (star (Y b a)*(f (hD1.eigenvalues b) : ℂ)*Y b a)*
      (g (hD0.eigenvalues a) : ℂ) =
      ((f (hD1.eigenvalues b)*g (hD0.eigenvalues a) : ℝ) : ℂ)*
        (star (Y b a)*Y b a) := by
    rw [Complex.ofReal_mul]
    ring
  rw [he]
  simp only [Complex.re_ofReal_mul,c1_star_mul_re_normSq]

theorem c1_two_endpoint_spectral_mass {D0 : QMatrix I} {D1 : QMatrix J}
    (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian) (Z : Matrix J I ℂ) :
    (∑ a : I, ∑ b : J,
      Complex.normSq (((hD1.eigenvectorUnitary : QMatrix J)ᴴ*Z*
        (hD0.eigenvectorUnitary : QMatrix I)) b a)) = hsSq Z := by
  have h := c1_two_endpoint_cfc_trace_spectral hD0 hD1 (fun _ => 1) (fun _ => 1) Z
  rw [cfc_const_one (p := IsSelfAdjoint) ℝ D0 hD0,
    cfc_const_one (p := IsSelfAdjoint) ℝ D1 hD1,Matrix.mul_one,Matrix.mul_one] at h
  simpa only [one_mul,hsSq] using h.symm

theorem c1_matrix_eigenbasis_column {D : QMatrix I} (hD : D.IsHermitian)
    (M : Matrix J I ℂ) (j : J) (a : I) :
    (M*(hD.eigenvectorUnitary : QMatrix I)) j a =
      (M*ᵥ ⇑(hD.eigenvectorBasis a)) j := by
  simp only [Matrix.mul_apply,Matrix.mulVec,dotProduct,hD.eigenvectorUnitary_apply]

theorem c1_binary_spectral_left_zero {A : QMatrix I} (hA : A.IsHermitian)
    (Z : Matrix J I ℂ) (hD0 : (A*A+Zᴴ*Z).PosSemidef)
    (a : I) (he : hD0.1.eigenvalues a=0) :
    ∀ j : J, (Z*(hD0.1.eigenvectorUnitary : QMatrix I)) j a=0 := by
  have hmul : (A*A+Zᴴ*Z)*ᵥ ⇑(hD0.1.eigenvectorBasis a)=0 := by
    simpa only [he,zero_smul] using hD0.1.mulVec_eigenvectorBasis a
  have hz := ((c1_binary_left_kernel_iff hA Z
    ⇑(hD0.1.eigenvectorBasis a)).mp hmul).2
  intro j
  rw [c1_matrix_eigenbasis_column]
  exact congrFun hz j

theorem c1_binary_spectral_right_zero {B : QMatrix J} (hB : B.IsHermitian)
    (Z : Matrix J I ℂ) (hD1 : (B*B+Z*Zᴴ).PosSemidef)
    (b : J) (he : hD1.1.eigenvalues b=0) :
    ∀ i : I, (Zᴴ*(hD1.1.eigenvectorUnitary : QMatrix J)) i b=0 := by
  have hmul : (B*B+Z*Zᴴ)*ᵥ ⇑(hD1.1.eigenvectorBasis b)=0 := by
    simpa only [he,zero_smul] using hD1.1.mulVec_eigenvectorBasis b
  have hz := ((c1_binary_right_kernel_iff hB Z
    ⇑(hD1.1.eigenvectorBasis b)).mp hmul).2
  intro i
  rw [c1_matrix_eigenbasis_column]
  exact congrFun hz i

theorem c1_binary_spectral_entry_zero
    {A : QMatrix I} {B : QMatrix J} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (Z : Matrix J I ℂ) (hD0 : (A*A+Zᴴ*Z).PosSemidef)
    (hD1 : (B*B+Z*Zᴴ).PosSemidef) (a : I) (b : J)
    (he : hD0.1.eigenvalues a=0 ∨ hD1.1.eigenvalues b=0) :
    ((hD1.1.eigenvectorUnitary : QMatrix J)ᴴ*Z*
      (hD0.1.eigenvectorUnitary : QMatrix I)) b a=0 := by
  rcases he with he | he
  · have hz := c1_binary_spectral_left_zero hA Z hD0 a he
    rw [Matrix.mul_assoc,Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j _
    rw [hz j,mul_zero]
  · have hz := c1_binary_spectral_right_zero hB Z hD1 b he
    have hrow (i : I) : ((hD1.1.eigenvectorUnitary : QMatrix J)ᴴ*Z) b i=0 := by
      have hc : (hD1.1.eigenvectorUnitary : QMatrix J)ᴴ*Z =
          (Zᴴ*(hD1.1.eigenvectorUnitary : QMatrix J))ᴴ := by
        simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
      rw [hc,Matrix.conjTranspose_apply,hz i,star_zero]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [hrow i,zero_mul]

theorem c1_binary_spectral_cutoff_modular_budget
    {A : QMatrix I} {B : QMatrix J} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (Z : Matrix J I ℂ) (hD0 : (A*A+Zᴴ*Z).PosSemidef)
    (hD1 : (B*B+Z*Zᴴ).PosSemidef) {x : ℝ} (hx : 0 < x) :
    (∑ a : I, ∑ b : J,
      (hD1.1.eigenvalues b*(hD0.1.eigenvalues a+x)⁻¹ +
        (hD1.1.eigenvalues b+x)⁻¹*hD0.1.eigenvalues a)*
      Complex.normSq (((hD1.1.eigenvectorUnitary : QMatrix J)ᴴ*Z*
        (hD0.1.eigenvectorUnitary : QMatrix I)) b a)) ≤
      (Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re := by
  let D0 : QMatrix I := A*A+Zᴴ*Z
  let D1 : QMatrix J := B*B+Z*Zᴴ
  let R0 : QMatrix I := (D0+x • (1 : QMatrix I))⁻¹
  let R1 : QMatrix J := (D1+x • (1 : QMatrix J))⁻¹
  have hl : Matrix.trace (D1*(Z*R0*Zᴴ)) = Matrix.trace (Zᴴ*D1*Z*R0) := by
    calc
      _ = Matrix.trace ((D1*Z*R0)*Zᴴ) := by
        congr 1
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Zᴴ*(D1*Z*R0)) := Matrix.trace_mul_comm _ _
      _ = _ := by
        congr 1
        simp only [Matrix.mul_assoc]
  have hr : Matrix.trace (D0*(Zᴴ*R1*Z)) = Matrix.trace (Zᴴ*R1*Z*D0) :=
    Matrix.trace_mul_comm _ _
  have hid0 : cfc (fun d : ℝ => d) D0=D0 :=
    cfc_id' (p := IsSelfAdjoint) ℝ D0 hD0.1
  have hid1 : cfc (fun d : ℝ => d) D1=D1 :=
    cfc_id' (p := IsSelfAdjoint) ℝ D1 hD1.1
  have hleft := c1_two_endpoint_cfc_trace_spectral hD0.1 hD1.1
    (fun d : ℝ => d) (fun d : ℝ => (d+x)⁻¹) Z
  rw [hid1,← c1_psd_shifted_inverse_cfc hD0 hx] at hleft
  have hright := c1_two_endpoint_cfc_trace_spectral hD0.1 hD1.1
    (fun d : ℝ => (d+x)⁻¹) (fun d : ℝ => d) Z
  rw [hid0,← c1_psd_shifted_inverse_cfc hD1 hx] at hright
  have h := c1_binary_modular_trace_budget A B Z hA hB hx
  change (Matrix.trace (D1*(Z*R0*Zᴴ))).re+
    (Matrix.trace (D0*(Zᴴ*R1*Z))).re ≤ _ at h
  rw [hl,hr,hleft,hright] at h
  convert h using 1
  simp only [← Finset.sum_add_distrib,← add_mul]

theorem c1_binary_spectral_modular_budget
    {A : QMatrix I} {B : QMatrix J} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (Z : Matrix J I ℂ) (hD0 : (A*A+Zᴴ*Z).PosSemidef)
    (hD1 : (B*B+Z*Zᴴ).PosSemidef) :
    (∑ a : I, ∑ b : J,
      Complex.normSq (((hD1.1.eigenvectorUnitary : QMatrix J)ᴴ*Z*
        (hD0.1.eigenvectorUnitary : QMatrix I)) b a)*
      (hD0.1.eigenvalues a/hD1.1.eigenvalues b+
        hD1.1.eigenvalues b/hD0.1.eigenvalues a)) ≤
      (Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re := by
  let e0 : I → ℝ := hD0.1.eigenvalues
  let e1 : J → ℝ := hD1.1.eigenvalues
  let w : I → J → ℝ := fun a b => Complex.normSq
    (((hD1.1.eigenvectorUnitary : QMatrix J)ᴴ*Z*
      (hD0.1.eigenvectorUnitary : QMatrix I)) b a)
  let f : ℝ → ℝ := fun x => ∑ a : I, ∑ b : J,
    (e1 b*(e0 a+x)⁻¹+(e1 b+x)⁻¹*e0 a)*w a b
  have hc (a : I) (b : J) : ContinuousAt
      (fun x : ℝ => (e1 b*(e0 a+x)⁻¹+(e1 b+x)⁻¹*e0 a)*w a b) 0 := by
    by_cases hw : w a b=0
    · have heq : (fun x : ℝ => (e1 b*(e0 a+x)⁻¹+(e1 b+x)⁻¹*e0 a)*w a b) =
          (fun _ : ℝ => 0) := by
        funext x
        rw [hw,mul_zero]
      rw [heq]
      exact continuousAt_const
    · have hn0 : e0 a ≠ 0 := by
        intro hn
        have hz := c1_binary_spectral_entry_zero hA hB Z hD0 hD1 a b (Or.inl hn)
        exact hw (by dsimp [w]; rw [hz]; simp)
      have hn1 : e1 b ≠ 0 := by
        intro hn
        have hz := c1_binary_spectral_entry_zero hA hB Z hD0 hD1 a b (Or.inr hn)
        exact hw (by dsimp [w]; rw [hz]; simp)
      have h0 : ContinuousAt (fun x : ℝ => (e0 a+x)⁻¹) 0 :=
        (continuousAt_const.add continuousAt_id).inv₀
          (by change e0 a+0 ≠ 0; simpa only [add_zero] using hn0)
      have h1 : ContinuousAt (fun x : ℝ => (e1 b+x)⁻¹) 0 :=
        (continuousAt_const.add continuousAt_id).inv₀
          (by change e1 b+0 ≠ 0; simpa only [add_zero] using hn1)
      exact ((h0.const_mul (e1 b)).add (h1.mul_const (e0 a))).mul_const (w a b)
  have hf : ContinuousAt f 0 :=
    tendsto_finsetSum Finset.univ (fun a _ =>
      tendsto_finsetSum Finset.univ (fun b _ => hc a b))
  have hxmem : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), x ∈ Set.Ioi 0 :=
    self_mem_nhdsWithin
  have hbound : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      f x ≤ (Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re :=
    hxmem.mono (fun x hx =>
      c1_binary_spectral_cutoff_modular_budget hA hB Z hD0 hD1 hx)
  have h := le_of_tendsto hf.continuousWithinAt hbound
  convert h using 1
  dsimp only [f]
  simp only [add_zero,div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem c1CoshMoment_pair_jensen_supported {K : Type*} [Fintype K] {m : ℝ}
    (w a b : K → ℝ) (hw : ∀ i, 0 ≤ w i) (hweight : ∑ i, w i=1)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hzero : ∀ i, a i=0 ∨ b i=0 → w i=0)
    (hbudget : (∑ i, w i*(a i/b i+b i/a i)) ≤ m) :
    (∑ i, w i*c1CoshMoment ((a i-b i)^2/(4*a i*b i))) ≤ Fcal m := by
  let ap : K → ℝ := fun i => if a i=0 then 1 else a i
  let bp : K → ℝ := fun i => if b i=0 then 1 else b i
  have hap (i : K) : 0 < ap i := by
    dsimp only [ap]
    split_ifs with h
    · norm_num
    · exact lt_of_le_of_ne (ha i) (Ne.symm h)
  have hbp (i : K) : 0 < bp i := by
    dsimp only [bp]
    split_ifs with h
    · norm_num
    · exact lt_of_le_of_ne (hb i) (Ne.symm h)
  have heq (i : K) :
      w i*(ap i/bp i+bp i/ap i)=w i*(a i/b i+b i/a i) ∧
      w i*c1CoshMoment ((ap i-bp i)^2/(4*ap i*bp i))=
        w i*c1CoshMoment ((a i-b i)^2/(4*a i*b i)) := by
    by_cases ha0 : a i=0
    · rw [hzero i (Or.inl ha0)]
      simp only [zero_mul,and_self]
    by_cases hb0 : b i=0
    · rw [hzero i (Or.inr hb0)]
      simp only [zero_mul,and_self]
    simp only [ap,bp,if_neg ha0,if_neg hb0,and_self]
  have hbp' : (∑ i, w i*(ap i/bp i+bp i/ap i)) ≤ m := by
    have hs : (∑ i, w i*(ap i/bp i+bp i/ap i))=
        ∑ i, w i*(a i/b i+b i/a i) :=
      Finset.sum_congr rfl (fun i _ => (heq i).1)
    rw [hs]
    exact hbudget
  have h := c1CoshMoment_pair_jensen w ap bp hw hweight hap hbp hbp'
  have hs : (∑ i, w i*c1CoshMoment ((ap i-bp i)^2/(4*ap i*bp i)))=
      ∑ i, w i*c1CoshMoment ((a i-b i)^2/(4*a i*b i)) :=
    Finset.sum_congr rfl (fun i _ => (heq i).2)
  rw [hs] at h
  exact h

theorem c1CoshMoment_pair_payment_supported {K : Type*} [Fintype K]
    (w a b : K → ℝ) {u t : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i=u) (hu : 0 < u)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hzero : ∀ i, a i=0 ∨ b i=0 → w i=0)
    (hbudget : (∑ i, w i*(a i/b i+b i/a i)) ≤ t) :
    (∑ i, w i*c1CoshMoment ((a i-b i)^2/(4*a i*b i))) ≤ u*Fcal (t/u) := by
  let v : K → ℝ := fun i => w i/u
  have hv (i : K) : 0 ≤ v i := div_nonneg (hw i) hu.le
  have hv_sum : (∑ i, v i)=1 := by
    dsimp only [v]
    rw [← Finset.sum_div,hmass,div_self (ne_of_gt hu)]
  have hz (i : K) (he : a i=0 ∨ b i=0) : v i=0 := by
    dsimp only [v]
    rw [hzero i he,zero_div]
  have hv_budget : (∑ i, v i*(a i/b i+b i/a i)) ≤ t/u := by
    have heq : (∑ i, v i*(a i/b i+b i/a i))=
        (∑ i, w i*(a i/b i+b i/a i))/u := by
      simp only [v,div_mul_eq_mul_div,← Finset.sum_div]
    rw [heq]
    exact div_le_div_of_nonneg_right hbudget hu.le
  have h := c1CoshMoment_pair_jensen_supported v a b hv hv_sum ha hb hz hv_budget
  have hs : (∑ i, v i*c1CoshMoment ((a i-b i)^2/(4*a i*b i)))=
      (∑ i, w i*c1CoshMoment ((a i-b i)^2/(4*a i*b i)))/u := by
    simp only [v,div_mul_eq_mul_div,← Finset.sum_div]
  rw [hs] at h
  have h' := (div_le_iff₀ hu).mp h
  simpa only [mul_comm] using h'

theorem c1_binary_spectral_cosh_payment
    {A : QMatrix I} {B : QMatrix J} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (Z : Matrix J I ℂ) (hD0 : (A*A+Zᴴ*Z).PosSemidef)
    (hD1 : (B*B+Z*Zᴴ).PosSemidef) (hu : 0 < hsSq Z) :
    (∑ a : I, ∑ b : J,
      Complex.normSq (((hD1.1.eigenvectorUnitary : QMatrix J)ᴴ*Z*
        (hD0.1.eigenvectorUnitary : QMatrix I)) b a)*
      c1CoshMoment ((hD0.1.eigenvalues a-hD1.1.eigenvalues b)^2/
        (4*hD0.1.eigenvalues a*hD1.1.eigenvalues b))) ≤
      hsSq Z*Fcal ((Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re/hsSq Z) := by
  let a : I × J → ℝ := fun k => hD0.1.eigenvalues k.1
  let b : I × J → ℝ := fun k => hD1.1.eigenvalues k.2
  let raw : I × J → ℝ := fun k => Complex.normSq
    (((hD1.1.eigenvectorUnitary : QMatrix J)ᴴ*Z*
      (hD0.1.eigenvectorUnitary : QMatrix I)) k.2 k.1)
  have hmass : (∑ k : I × J, raw k)=hsSq Z := by
    rw [Fintype.sum_prod_type]
    exact c1_two_endpoint_spectral_mass hD0.1 hD1.1 Z
  have hw (k : I × J) : 0 ≤ raw k := Complex.normSq_nonneg _
  have ha (k : I × J) : 0 ≤ a k := hD0.eigenvalues_nonneg k.1
  have hb (k : I × J) : 0 ≤ b k := hD1.eigenvalues_nonneg k.2
  have hz (k : I × J) (he : a k=0 ∨ b k=0) : raw k=0 := by
    have he' := c1_binary_spectral_entry_zero hA hB Z hD0 hD1 k.1 k.2 he
    dsimp only [raw]
    rw [he']
    simp
  have hraw : (∑ k : I × J, raw k*(a k/b k+b k/a k)) ≤
      (Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re := by
    rw [Fintype.sum_prod_type]
    exact c1_binary_spectral_modular_budget hA hB Z hD0 hD1
  have h := c1CoshMoment_pair_payment_supported raw a b hw hmass hu ha hb hz hraw
  rw [Fintype.sum_prod_type] at h
  exact h

theorem c1CoshMoment_pair_gt {a b : ℝ} (hb : 0 < b) (hab : b < a) :
    c1CoshMoment ((a-b)^2/(4*a*b))=(a+b)*(Real.log a-Real.log b)/(a-b) := by
  have ha : 0 < a := hb.trans hab
  have hd : 0 < a-b := sub_pos.mpr hab
  let r : ℝ := (a-b)^2/(4*a*b)
  let s : ℝ := Real.sqrt (a*b)
  have hr : 0 < r := div_pos (sq_pos_of_pos hd) (by positivity)
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hns : s ≠ 0 := ne_of_gt hs
  have hs_sq : s^2=a*b := Real.sq_sqrt (mul_pos ha hb).le
  have hsr : Real.sqrt r=(a-b)/(2*s) := by
    apply (Real.sqrt_eq_iff_eq_sq hr.le (by positivity)).mpr
    dsimp only [r]
    rw [div_pow,mul_pow,hs_sq]
    norm_num
    ring
  have hs1 : Real.sqrt (1+r)=(a+b)/(2*s) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    dsimp only [r]
    rw [div_pow,mul_pow,hs_sq]
    field_simp [ne_of_gt ha,ne_of_gt hb]
    ring
  have hlog : Real.arsinh (Real.sqrt r)=(Real.log a-Real.log b)/2 := by
    rw [Real.arsinh,Real.sq_sqrt hr.le,hsr,hs1]
    have hadd : (a-b)/(2*s)+(a+b)/(2*s)=a/s := by ring
    rw [hadd,Real.log_div (ne_of_gt ha) hns]
    dsimp only [s]
    rw [Real.log_sqrt (mul_pos ha hb).le,Real.log_mul (ne_of_gt ha) (ne_of_gt hb)]
    ring
  change c1CoshMoment r=_
  rw [c1CoshMoment_eq_arsinh hr,hlog,hsr,hs1]
  field_simp [hns,ne_of_gt hd] <;> ring

theorem c1CoshMoment_pair_coefficient {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    c1CoshMoment ((a-b)^2/(4*a*b))=
      if a=b then 2 else (a+b)*(Real.log b-Real.log a)/(b-a) := by
  by_cases heq : a=b
  · subst a
    simp
  rw [if_neg heq]
  rcases lt_or_gt_of_ne heq with hab | hba
  · have hr : (a-b)^2/(4*a*b)=(b-a)^2/(4*b*a) := by
      field_simp [ne_of_gt ha,ne_of_gt hb]
      ring
    rw [hr,c1CoshMoment_pair_gt ha hab]
    ring
  · rw [c1CoshMoment_pair_gt hb hba]
    have hne : a-b ≠ 0 := sub_ne_zero.mpr heq
    field_simp [hne]
    ring

theorem c1_pair_self_integral_bound_le {a b T : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hT : 0 ≤ T) (hab : a ≤ b) :
    (∫ x in 0..T, (a+b)*((x+a)⁻¹*(x+b)⁻¹)) ≤
      c1CoshMoment ((a-b)^2/(4*a*b)) := by
  rw [intervalIntegral.integral_const_mul,c1CoshMoment_pair_coefficient ha hb]
  by_cases heq : a=b
  · subst b
    rw [if_pos rfl,c1_pair_resolvent_integral_eq ha hT]
    calc
      (a+a)*(a⁻¹-(T+a)⁻¹) ≤ (a+a)*a⁻¹ :=
        mul_le_mul_of_nonneg_left (sub_le_self _ (inv_nonneg.mpr (by linarith)))
          (by positivity)
      _ = 2 := by field_simp [ne_of_gt ha]; ring
  · rw [if_neg heq,c1_pair_resolvent_integral_ne ha hb hT heq]
    have hba : 0 < b-a := sub_pos.mpr (lt_of_le_of_ne hab heq)
    have hl : Real.log (T+a) ≤ Real.log (T+b) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hba).mpr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith

theorem c1_pair_self_integral_bound {a b T : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hT : 0 ≤ T) :
    (∫ x in 0..T, (a+b)*((x+a)⁻¹*(x+b)⁻¹)) ≤
      c1CoshMoment ((a-b)^2/(4*a*b)) := by
  by_cases hab : a ≤ b
  · exact c1_pair_self_integral_bound_le ha hb hT hab
  · have h := c1_pair_self_integral_bound_le hb ha hT (le_of_not_ge hab)
    have hf : (fun x : ℝ => (a+b)*((x+a)⁻¹*(x+b)⁻¹))=
        (fun x : ℝ => (b+a)*((x+b)⁻¹*(x+a)⁻¹)) := by
      funext x
      ring
    have hr : (a-b)^2/(4*a*b)=(b-a)^2/(4*b*a) := by
      field_simp [ne_of_gt ha,ne_of_gt hb]
      ring
    rw [← hf,← hr] at h
    exact h

theorem c1_pair_self_intervalIntegrable {a b l r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hl : 0 ≤ l) (hlr : l ≤ r) :
    IntervalIntegrable (fun x : ℝ => (a+b)*((x+a)⁻¹*(x+b)⁻¹))
      MeasureTheory.volume l r := by
  have hinv {c : ℝ} (hc : 0 < c) :
      ContinuousOn (fun x : ℝ => (x+c)⁻¹) (Set.uIcc l r) := by
    have hz (x : ℝ) (hx : x ∈ Set.uIcc l r) : x+c ≠ 0 := by
      have hxl : l ≤ x := (by simpa only [Set.uIcc_of_le hlr] using hx :
        x ∈ Set.Icc l r).1
      exact ne_of_gt (by linarith)
    exact (continuous_id.add continuous_const :
      Continuous (fun x : ℝ => x+c)).continuousOn.inv₀ hz
  exact ((hinv ha).mul (hinv hb)).const_mul (a+b) |>.intervalIntegrable

theorem c1_pair_self_integral_bound_cutoff {a b ε T : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hε : 0 ≤ ε) (hT : ε ≤ T) :
    (∫ x in ε..T, (a+b)*((x+a)⁻¹*(x+b)⁻¹)) ≤
      c1CoshMoment ((a-b)^2/(4*a*b)) := by
  have hi0 := c1_pair_self_intervalIntegrable ha hb (le_refl (0 : ℝ)) hε
  have hi1 := c1_pair_self_intervalIntegrable ha hb hε hT
  have hsum := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  have hn : 0 ≤ ∫ x in 0..ε, (a+b)*((x+a)⁻¹*(x+b)⁻¹) := by
    apply intervalIntegral.integral_nonneg hε
    intro x hx
    exact mul_nonneg (by positivity)
      (mul_nonneg (inv_nonneg.mpr (by linarith [hx.1]))
        (inv_nonneg.mpr (by linarith [hx.1])))
  have hbnd := c1_pair_self_integral_bound ha hb (hε.trans hT)
  linarith

theorem c1_supported_pair_self_integral_bound {a b w ε T : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w)
    (hzero : a=0 ∨ b=0 → w=0) (hε : 0 ≤ ε) (hT : ε ≤ T) :
    (∫ x in ε..T, w*((a+b)*((x+a)⁻¹*(x+b)⁻¹))) ≤
      w*c1CoshMoment ((a-b)^2/(4*a*b)) := by
  by_cases hw0 : w=0
  · simp only [hw0,zero_mul,intervalIntegral.integral_zero,le_refl]
  have ha0 : a ≠ 0 := fun h => hw0 (hzero (Or.inl h))
  have hb0 : b ≠ 0 := fun h => hw0 (hzero (Or.inr h))
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (c1_pair_self_integral_bound_cutoff hap hbp hε hT) hw

theorem c1_psd_pair_self_intervalIntegrable {a b w ε T : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) (hT : ε ≤ T) :
    IntervalIntegrable (fun x : ℝ => w*((a+b)*((x+a)⁻¹*(x+b)⁻¹)))
      MeasureTheory.volume ε T := by
  have hinv {c : ℝ} (hc : 0 ≤ c) :
      ContinuousOn (fun x : ℝ => (x+c)⁻¹) (Set.uIcc ε T) := by
    have hz (x : ℝ) (hx : x ∈ Set.uIcc ε T) : x+c ≠ 0 := by
      have hxε : ε ≤ x := (by simpa only [Set.uIcc_of_le hT] using hx :
        x ∈ Set.Icc ε T).1
      exact ne_of_gt (by linarith)
    exact (continuous_id.add continuous_const :
      Continuous (fun x : ℝ => x+c)).continuousOn.inv₀ hz
  exact (((hinv ha).mul (hinv hb)).const_mul (a+b)).const_mul w |>.intervalIntegrable

theorem c1_supported_finite_self_integral_bound {K : Type*} [Fintype K]
    (w a b : K → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hw : ∀ i, 0 ≤ w i) (hzero : ∀ i, a i=0 ∨ b i=0 → w i=0)
    {ε T : ℝ} (hε : 0 < ε) (hT : ε ≤ T) :
    (∫ x in ε..T, ∑ i, w i*((a i+b i)*((x+a i)⁻¹*(x+b i)⁻¹))) ≤
      ∑ i, w i*c1CoshMoment ((a i-b i)^2/(4*a i*b i)) := by
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    c1_psd_pair_self_intervalIntegrable (ha i) (hb i) hε hT)]
  exact Finset.sum_le_sum (fun i _ =>
    c1_supported_pair_self_integral_bound (ha i) (hb i) (hw i) (hzero i) hε.le hT)

theorem c1_psd_linear_resolvent_cfc {D : QMatrix I} (hD : D.PosSemidef)
    {x : ℝ} (hx : 0 < x) :
    D*(D+x • (1 : QMatrix I))⁻¹=cfc (fun d : ℝ => d*(d+x)⁻¹) D := by
  rw [cfc_mul (p := IsSelfAdjoint) (fun d : ℝ => d) (fun d : ℝ => (d+x)⁻¹)
    D (D.finite_real_spectrum.continuousOn _) (D.finite_real_spectrum.continuousOn _),
    cfc_id' (p := IsSelfAdjoint) ℝ D hD.1,← c1_psd_shifted_inverse_cfc hD hx]

theorem c1_endpoint_self_trace_spectral {D0 : QMatrix I} {D1 : QMatrix J}
    (hD0 : D0.PosSemidef) (hD1 : D1.PosSemidef) (Z : Matrix J I ℂ)
    {x : ℝ} (hx : 0 < x) :
    (Matrix.trace (Zᴴ*(D1+x • (1 : QMatrix J))⁻¹*Z*
      (D0*(D0+x • (1 : QMatrix I))⁻¹))).re+
    (Matrix.trace (Zᴴ*(D1*(D1+x • (1 : QMatrix J))⁻¹)*Z*
      (D0+x • (1 : QMatrix I))⁻¹)).re =
      ∑ a : I, ∑ b : J,
        Complex.normSq (((hD1.1.eigenvectorUnitary : QMatrix J)ᴴ*Z*
          (hD0.1.eigenvectorUnitary : QMatrix I)) b a)*
        ((hD0.1.eigenvalues a+hD1.1.eigenvalues b)*
          ((x+hD0.1.eigenvalues a)⁻¹*(x+hD1.1.eigenvalues b)⁻¹)) := by
  have h0 := c1_two_endpoint_cfc_trace_spectral hD0.1 hD1.1
    (fun d : ℝ => (d+x)⁻¹) (fun d : ℝ => d*(d+x)⁻¹) Z
  rw [← c1_psd_shifted_inverse_cfc hD1 hx,← c1_psd_linear_resolvent_cfc hD0 hx] at h0
  have h1 := c1_two_endpoint_cfc_trace_spectral hD0.1 hD1.1
    (fun d : ℝ => d*(d+x)⁻¹) (fun d : ℝ => (d+x)⁻¹) Z
  rw [← c1_psd_linear_resolvent_cfc hD1 hx,← c1_psd_shifted_inverse_cfc hD0 hx] at h1
  rw [h0,h1]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [add_comm x (hD0.1.eigenvalues a),add_comm x (hD1.1.eigenvalues b)]
  ring

theorem c1_binary_endpoint_self_integral_bound
    {A : QMatrix I} {B : QMatrix J} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (Z : Matrix J I ℂ) (hu : 0 < hsSq Z) {ε T : ℝ}
    (hε : 0 < ε) (hT : ε ≤ T) :
    (∫ x in ε..T,
      (Matrix.trace (Zᴴ*(B*B+Z*Zᴴ+x • (1 : QMatrix J))⁻¹*Z*
        ((A*A+Zᴴ*Z)*(A*A+Zᴴ*Z+x • (1 : QMatrix I))⁻¹))).re+
      (Matrix.trace (Zᴴ*((B*B+Z*Zᴴ)*(B*B+Z*Zᴴ+x • (1 : QMatrix J))⁻¹)*Z*
        (A*A+Zᴴ*Z+x • (1 : QMatrix I))⁻¹)).re) ≤
      hsSq Z*Fcal ((Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re/hsSq Z) := by
  let D0 : QMatrix I := A*A+Zᴴ*Z
  let D1 : QMatrix J := B*B+Z*Zᴴ
  have hD0 : D0.PosSemidef :=
    (c1_hermitian_square_posSemidef hA).add (Matrix.posSemidef_conjTranspose_mul_self Z)
  have hD1 : D1.PosSemidef :=
    (c1_hermitian_square_posSemidef hB).add (Matrix.posSemidef_self_mul_conjTranspose Z)
  let a : I × J → ℝ := fun k => hD0.1.eigenvalues k.1
  let b : I × J → ℝ := fun k => hD1.1.eigenvalues k.2
  let w : I × J → ℝ := fun k => Complex.normSq
    (((hD1.1.eigenvectorUnitary : QMatrix J)ᴴ*Z*
      (hD0.1.eigenvectorUnitary : QMatrix I)) k.2 k.1)
  have ha (k : I × J) : 0 ≤ a k := hD0.eigenvalues_nonneg k.1
  have hb (k : I × J) : 0 ≤ b k := hD1.eigenvalues_nonneg k.2
  have hw (k : I × J) : 0 ≤ w k := Complex.normSq_nonneg _
  have hz (k : I × J) (he : a k=0 ∨ b k=0) : w k=0 := by
    have he' := c1_binary_spectral_entry_zero hA hB Z hD0 hD1 k.1 k.2 he
    dsimp only [w]
    rw [he']
    simp
  have hint :
      (∫ x in ε..T,
        (Matrix.trace (Zᴴ*(D1+x • (1 : QMatrix J))⁻¹*Z*
          (D0*(D0+x • (1 : QMatrix I))⁻¹))).re+
        (Matrix.trace (Zᴴ*(D1*(D1+x • (1 : QMatrix J))⁻¹)*Z*
          (D0+x • (1 : QMatrix I))⁻¹)).re) =
        ∫ x in ε..T, ∑ k : I × J, w k*((a k+b k)*((x+a k)⁻¹*(x+b k)⁻¹)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxε : ε ≤ x := (by simpa only [Set.uIcc_of_le hT] using hx :
      x ∈ Set.Icc ε T).1
    dsimp only
    rw [Fintype.sum_prod_type]
    exact c1_endpoint_self_trace_spectral hD0 hD1 Z (hε.trans_le hxε)
  change (∫ x in ε..T,
    (Matrix.trace (Zᴴ*(D1+x • (1 : QMatrix J))⁻¹*Z*
      (D0*(D0+x • (1 : QMatrix I))⁻¹))).re+
    (Matrix.trace (Zᴴ*(D1*(D1+x • (1 : QMatrix J))⁻¹)*Z*
      (D0+x • (1 : QMatrix I))⁻¹)).re) ≤ _
  rw [hint]
  calc
    _ ≤ ∑ k : I × J, w k*c1CoshMoment ((a k-b k)^2/(4*a k*b k)) :=
      c1_supported_finite_self_integral_bound w a b ha hb hw hz hε hT
    _ = ∑ i : I, ∑ j : J,
      Complex.normSq (((hD1.1.eigenvectorUnitary : QMatrix J)ᴴ*Z*
        (hD0.1.eigenvectorUnitary : QMatrix I)) j i)*
        c1CoshMoment ((hD0.1.eigenvalues i-hD1.1.eigenvalues j)^2/
          (4*hD0.1.eigenvalues i*hD1.1.eigenvalues j)) := by
      rw [Fintype.sum_prod_type]
    _ ≤ _ := c1_binary_spectral_cosh_payment hA hB Z hD0 hD1 hu

theorem c1_right_self_integrand_comparison {B D : QMatrix J} {R : QMatrix I}
    (hB : B.IsHermitian) (hD : D.PosSemidef) (hDB : (D-B*B).PosSemidef)
    (hR : R.PosSemidef) (Z : Matrix J I ℂ) {x : ℝ} (hx : 0 < x) :
    (Matrix.trace ((B*Z)ᴴ*(D+x • (1 : QMatrix J))⁻¹*(B*Z)*R)).re ≤
      (Matrix.trace (Zᴴ*(D*(D+x • (1 : QMatrix J))⁻¹)*Z*R)).re := by
  have hM : (Z*R*Zᴴ).PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      hR.conjTranspose_mul_mul_same Zᴴ
  have h := c1_self_resolvent_trace_comparison hB hD hDB hM hx
  have hcycle (K : QMatrix J) :
      Matrix.trace (K*(Z*R*Zᴴ))=Matrix.trace (Zᴴ*K*Z*R) := by
    calc
      _ = Matrix.trace ((K*Z*R)*Zᴴ) := by
        congr 1
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Zᴴ*(K*Z*R)) := Matrix.trace_mul_comm _ _
      _ = _ := by
        congr 1
        simp only [Matrix.mul_assoc]
  rw [hcycle,hcycle] at h
  simpa only [Matrix.conjTranspose_mul,hB.eq,Matrix.mul_assoc] using h

theorem c1_metric_trace_cross_symm {R0 : QMatrix I} {R1 : QMatrix J}
    (hR0 : R0.IsHermitian) (hR1 : R1.IsHermitian) (V W : Matrix J I ℂ) :
    (Matrix.trace (Vᴴ*R1*W*R0)).re=(Matrix.trace (Wᴴ*R1*V*R0)).re := by
  have heq : R0*(Vᴴ*R1*W)=(Wᴴ*R1*V*R0)ᴴ := by
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      hR0.eq,hR1.eq,Matrix.mul_assoc]
  calc
    _ = (Matrix.trace (R0*(Vᴴ*R1*W))).re :=
      congrArg Complex.re (Matrix.trace_mul_comm _ _)
    _ = (Matrix.trace (Wᴴ*R1*V*R0)ᴴ).re := by rw [heq]
    _ = (star (Matrix.trace (Wᴴ*R1*V*R0))).re := by rw [Matrix.trace_conjTranspose]
    _ = _ := by simp only [Complex.star_def,Complex.conj_re]

theorem c1_metric_trace_add {R0 : QMatrix I} {R1 : QMatrix J}
    (hR0 : R0.IsHermitian) (hR1 : R1.IsHermitian) (V W : Matrix J I ℂ) :
    (Matrix.trace ((V+W)ᴴ*R1*(V+W)*R0)).re =
      (Matrix.trace (Vᴴ*R1*V*R0)).re+(Matrix.trace (Wᴴ*R1*W*R0)).re+
        2*(Matrix.trace (Vᴴ*R1*W*R0)).re := by
  have h := c1_metric_trace_cross_symm hR0 hR1 V W
  simp only [Matrix.conjTranspose_add,Matrix.add_mul,Matrix.mul_add,
    Matrix.trace_add,Complex.add_re]
  linarith

theorem c1_binary_linear_resolvent_pointwise
    {A : QMatrix I} {B : QMatrix J} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (Z : Matrix J I ℂ) {x : ℝ} (hx : 0 < x) :
    (Matrix.trace ((Z*A+B*Z)ᴴ*(B*B+Z*Zᴴ+x • (1 : QMatrix J))⁻¹*
      (Z*A+B*Z)*(A*A+Zᴴ*Z+x • (1 : QMatrix I))⁻¹)).re ≤
      (Matrix.trace (Zᴴ*(B*B+Z*Zᴴ+x • (1 : QMatrix J))⁻¹*Z*
        ((A*A+Zᴴ*Z)*(A*A+Zᴴ*Z+x • (1 : QMatrix I))⁻¹))).re+
      (Matrix.trace (Zᴴ*((B*B+Z*Zᴴ)*(B*B+Z*Zᴴ+x • (1 : QMatrix J))⁻¹)*Z*
        (A*A+Zᴴ*Z+x • (1 : QMatrix I))⁻¹)).re+
      2*(Matrix.trace (Zᴴ*(B*B+Z*Zᴴ+x • (1 : QMatrix J))⁻¹*B*Z*
        (A*A+Zᴴ*Z+x • (1 : QMatrix I))⁻¹*A)).re := by
  let D0 : QMatrix I := A*A+Zᴴ*Z
  let D1 : QMatrix J := B*B+Z*Zᴴ
  let R0 : QMatrix I := (D0+x • (1 : QMatrix I))⁻¹
  let R1 : QMatrix J := (D1+x • (1 : QMatrix J))⁻¹
  have hD0 : D0.PosSemidef :=
    (c1_hermitian_square_posSemidef hA).add (Matrix.posSemidef_conjTranspose_mul_self Z)
  have hD1 : D1.PosSemidef :=
    (c1_hermitian_square_posSemidef hB).add (Matrix.posSemidef_self_mul_conjTranspose Z)
  have hDA : (D0-A*A).PosSemidef := by
    simpa only [D0,add_sub_cancel_left] using Matrix.posSemidef_conjTranspose_mul_self Z
  have hDB : (D1-B*B).PosSemidef := by
    simpa only [D1,add_sub_cancel_left] using Matrix.posSemidef_self_mul_conjTranspose Z
  have hR0 : R0.PosSemidef := (c1_regularized_posDef hD0 hx).inv.posSemidef
  have hR1 : R1.PosSemidef := (c1_regularized_posDef hD1 hx).inv.posSemidef
  have hl := c1_left_self_integrand_comparison hA hD0 hDA hR1 Z hx
  have hl' : (Matrix.trace ((Z*A)ᴴ*R1*(Z*A)*R0)).re ≤
      (Matrix.trace (Zᴴ*R1*Z*(D0*R0))).re := by
    simpa only [Matrix.mul_assoc] using hl
  have hr := c1_right_self_integrand_comparison hB hD1 hDB hR0 Z hx
  have hcross : (Matrix.trace ((Z*A)ᴴ*R1*(B*Z)*R0)).re=
      (Matrix.trace (Zᴴ*R1*B*Z*R0*A)).re := by
    rw [Matrix.conjTranspose_mul,hA.eq]
    have heq : Matrix.trace (A*Zᴴ*R1*(B*Z)*R0)=
        Matrix.trace (Zᴴ*R1*B*Z*R0*A) := by
      calc
        _ = Matrix.trace (A*(Zᴴ*R1*B*Z*R0)) := by
          congr 1
          simp only [Matrix.mul_assoc]
        _ = _ := Matrix.trace_mul_comm _ _
    rw [heq]
  have hexp := c1_metric_trace_add hR0.1 hR1.1 (Z*A) (B*Z)
  rw [hcross] at hexp
  change (Matrix.trace ((Z*A+B*Z)ᴴ*R1*(Z*A+B*Z)*R0)).re ≤
    (Matrix.trace (Zᴴ*R1*Z*(D0*R0))).re+
    (Matrix.trace (Zᴴ*(D1*R1)*Z*R0)).re+
    2*(Matrix.trace (Zᴴ*R1*B*Z*R0*A)).re
  linarith

theorem c1_metric_trace_continuous (V : Matrix J I ℂ) :
    Continuous (fun q : QMatrix I × QMatrix J =>
      (Matrix.trace (Vᴴ*q.2*V*q.1)).re) := by
  simpa only [Matrix.mul_one] using
    c1_mixed_trace_continuous (1 : QMatrix I) (1 : QMatrix J) V

theorem c1_endpoint_self_trace_continuous (D0 : QMatrix I) (D1 : QMatrix J)
    (Z : Matrix J I ℂ) :
    Continuous (fun q : QMatrix I × QMatrix J =>
      (Matrix.trace (Zᴴ*q.2*Z*(D0*q.1))).re+
      (Matrix.trace (Zᴴ*(D1*q.2)*Z*q.1)).re) := by
  have h0 : Continuous (fun q : QMatrix I × QMatrix J => D0*q.1) :=
    (continuous_const : Continuous (fun _ : QMatrix I × QMatrix J => D0)).matrix_mul
      (continuous_fst : Continuous (fun q : QMatrix I × QMatrix J => q.1))
  have h1 : Continuous (fun q : QMatrix I × QMatrix J => D1*q.2) :=
    (continuous_const : Continuous (fun _ : QMatrix I × QMatrix J => D1)).matrix_mul
      (continuous_snd : Continuous (fun q : QMatrix I × QMatrix J => q.2))
  have hmap0 : Continuous (fun q : QMatrix I × QMatrix J => (D0*q.1,q.2)) :=
    h0.prodMk continuous_snd
  have hmap1 : Continuous (fun q : QMatrix I × QMatrix J => (q.1,D1*q.2)) :=
    continuous_fst.prodMk h1
  have hc0 := (c1_metric_trace_continuous Z).comp hmap0
  have hc1 := (c1_metric_trace_continuous Z).comp hmap1
  exact hc0.add hc1

theorem c1_integral_linear_payment {m e f : ℝ → ℝ} {ε T u v : ℝ}
    (hT : ε ≤ T) (hm : IntervalIntegrable m MeasureTheory.volume ε T)
    (he : IntervalIntegrable e MeasureTheory.volume ε T)
    (hf : IntervalIntegrable f MeasureTheory.volume ε T)
    (hpoint : ∀ x ∈ Set.Icc ε T, m x ≤ e x+2*f x)
    (hbE : (∫ x in ε..T, e x) ≤ v) (hbF : |∫ x in ε..T, f x| ≤ u) :
    (∫ x in ε..T, m x) ≤ v+2*u := by
  calc
    _ ≤ ∫ x in ε..T, e x+2*f x :=
      intervalIntegral.integral_mono_on hT hm (he.add (hf.const_mul 2)) hpoint
    _ = (∫ x in ε..T, e x)+2*(∫ x in ε..T, f x) := by
      rw [intervalIntegral.integral_add he (hf.const_mul 2),
        intervalIntegral.integral_const_mul]
    _ ≤ v+2*u := by linarith [le_abs_self (∫ x in ε..T, f x)]

theorem c1_binary_linear_resolvent_integral_bound
    {A : QMatrix I} {B : QMatrix J} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (Z : Matrix J I ℂ) (hu : 0 < hsSq Z) {ε T : ℝ}
    (hε : 0 < ε) (hT : ε ≤ T) :
    (∫ x in ε..T,
      (Matrix.trace ((Z*A+B*Z)ᴴ*(B*B+Z*Zᴴ+x • (1 : QMatrix J))⁻¹*
        (Z*A+B*Z)*(A*A+Zᴴ*Z+x • (1 : QMatrix I))⁻¹)).re) ≤
      hsSq Z*Fcal ((Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re/hsSq Z)+2*hsSq Z := by
  let D0 : QMatrix I := A*A+Zᴴ*Z
  let D1 : QMatrix J := B*B+Z*Zᴴ
  let R0 : ℝ → QMatrix I := fun x => (D0+x • (1 : QMatrix I))⁻¹
  let R1 : ℝ → QMatrix J := fun x => (D1+x • (1 : QMatrix J))⁻¹
  let m : ℝ → ℝ := fun x => (Matrix.trace ((Z*A+B*Z)ᴴ*R1 x*(Z*A+B*Z)*R0 x)).re
  let e : ℝ → ℝ := fun x => (Matrix.trace (Zᴴ*R1 x*Z*(D0*R0 x))).re+
    (Matrix.trace (Zᴴ*(D1*R1 x)*Z*R0 x)).re
  let f : ℝ → ℝ := fun x => (Matrix.trace (Zᴴ*R1 x*B*Z*R0 x*A)).re
  have hD0 : D0.PosSemidef :=
    (c1_hermitian_square_posSemidef hA).add (Matrix.posSemidef_conjTranspose_mul_self Z)
  have hD1 : D1.PosSemidef :=
    (c1_hermitian_square_posSemidef hB).add (Matrix.posSemidef_self_mul_conjTranspose Z)
  have hc0 : ContinuousOn R0 (Set.uIcc ε T) :=
    c1_psd_resolvent_continuousOn hD0 hε hT
  have hc1 : ContinuousOn R1 (Set.uIcc ε T) :=
    c1_psd_resolvent_continuousOn hD1 hε hT
  have hpair : ContinuousOn (fun x : ℝ => (R0 x,R1 x)) (Set.uIcc ε T) :=
    hc0.prodMk hc1
  have hm := (c1_metric_trace_continuous (Z*A+B*Z)).comp_continuousOn hpair
  change ContinuousOn m (Set.uIcc ε T) at hm
  have he := (c1_endpoint_self_trace_continuous D0 D1 Z).comp_continuousOn hpair
  change ContinuousOn e (Set.uIcc ε T) at he
  have hf := (c1_mixed_trace_continuous A B Z).comp_continuousOn hpair
  change ContinuousOn f (Set.uIcc ε T) at hf
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc ε T) : m x ≤ e x+2*f x :=
    c1_binary_linear_resolvent_pointwise hA hB Z (hε.trans_le hx.1)
  have hbE := c1_binary_endpoint_self_integral_bound hA hB Z hu hε hT
  change (∫ x in ε..T, e x) ≤
    hsSq Z*Fcal ((Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re/hsSq Z) at hbE
  have hbF := c1_binary_mixed_resolvent_integral_bound hA hB Z hε hT
  change |∫ x in ε..T, f x| ≤ hsSq Z at hbF
  change (∫ x in ε..T, m x) ≤ _
  exact c1_integral_linear_payment hT hm.intervalIntegrable he.intervalIntegrable
    hf.intervalIntegrable hpoint hbE hbF

theorem c1_negative_diagonal_form (d : I → ℝ) (hd : ∀ i, d i < 0)
    (v : I → ℂ) (hv : v ≠ 0) :
    (star v ⬝ᵥ (Matrix.diagonal (fun i => (d i : ℂ))*ᵥ v)).re < 0 := by
  have heq : (star v ⬝ᵥ (Matrix.diagonal (fun i => (d i : ℂ))*ᵥ v)).re =
      ∑ i : I, d i*Complex.normSq (v i) := by
    change (∑ i : I, star (v i)*
      (Matrix.diagonal (fun i => (d i : ℂ))*ᵥ v) i).re = _
    simp only [Matrix.mulVec_diagonal,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hmul : star (v i)*((d i : ℂ)*v i)=(d i : ℂ)*(star (v i)*v i) := by ring
    rw [hmul,Complex.re_ofReal_mul,c1_star_mul_re_normSq]
  rw [heq]
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  have hterm : d i*Complex.normSq (v i) < 0 :=
    mul_neg_of_neg_of_pos (hd i) (Complex.normSq_pos.mpr hi)
  have hlt : (∑ j : I, d j*Complex.normSq (v j)) < ∑ _ : I, (0 : ℝ) :=
    Finset.sum_lt_sum (fun j _ =>
      mul_nonpos_of_nonpos_of_nonneg (hd j).le (Complex.normSq_nonneg _))
      ⟨i,Finset.mem_univ i,hterm⟩
  simpa only [Finset.sum_const_zero] using hlt

theorem c1_negative_diagonal_correction_injective (d : I → ℝ)
    (hd : ∀ i, d i < 0) (F : QMatrix I)
    (hP : (Matrix.diagonal (fun i => (d i : ℂ))+F).PosSemidef) :
    Function.Injective (fun v : I → ℂ => F*ᵥ v) := by
  intro v w heq
  change F*ᵥ v=F*ᵥ w at heq
  apply sub_eq_zero.mp
  by_contra hne
  have hF : F*ᵥ (v-w)=0 := by rw [Matrix.mulVec_sub,heq,sub_self]
  have hp : 0 ≤ (star (v-w) ⬝ᵥ
      ((Matrix.diagonal (fun i => (d i : ℂ))+F)*ᵥ (v-w))).re :=
    (Complex.nonneg_iff.mp (hP.dotProduct_mulVec_nonneg (v-w))).1
  rw [Matrix.add_mulVec,hF,add_zero] at hp
  exact not_le_of_gt (c1_negative_diagonal_form d hd (v-w) hne) hp

theorem c1_rank_eq_card_of_mulVec_injective (F : QMatrix I)
    (hF : Function.Injective (fun v : I → ℂ => F*ᵥ v)) :
    F.rank=Fintype.card I := by
  change Function.Injective F.mulVecLin at hF
  rw [Matrix.rank,LinearMap.finrank_range_of_inj hF,Module.finrank_pi]

theorem c1_negative_diagonal_count_le_rank (d : I → ℝ) (F : QMatrix I)
    (hP : (Matrix.diagonal (fun i => (d i : ℂ))+F).PosSemidef) :
    Fintype.card {i : I // d i < 0} ≤ F.rank := by
  classical
  let N := {i : I // d i < 0}
  let G : QMatrix N := F.submatrix (Subtype.val : N → I) (Subtype.val : N → I)
  have hD : (Matrix.diagonal (fun i : N => (d i.val : ℂ))+G).PosSemidef := by
    have h := hP.submatrix (Subtype.val : N → I)
    have heq : (Matrix.diagonal (fun i => (d i : ℂ))+F).submatrix
        (Subtype.val : N → I) (Subtype.val : N → I) =
        Matrix.diagonal (fun i : N => (d i.val : ℂ))+G := by
      ext i j
      by_cases hij : i=j
      · subst j
        simp [Matrix.submatrix,Matrix.diagonal_apply,G]
      · have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
        simp [Matrix.submatrix,Matrix.diagonal_apply,G,hij,hval]
    rw [heq] at h
    exact h
  have hinj := c1_negative_diagonal_correction_injective
    (fun i : N => d i.val) (fun i => i.property) G hD
  calc
    Fintype.card N=G.rank := (c1_rank_eq_card_of_mulVec_injective G hinj).symm
    _ ≤ F.rank := Matrix.rank_submatrix_le F _ _

theorem c1_hermitian_negative_count_le_rank {M F : QMatrix I}
    (hM : M.IsHermitian) (hP : (M+F).PosSemidef) :
    Fintype.card {i : I // hM.eigenvalues i < 0} ≤ F.rank := by
  let U : QMatrix I := hM.eigenvectorUnitary
  let G : QMatrix I := Uᴴ*F*U
  have hdiag : Uᴴ*M*U=Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ)) := by
    simpa only [U,Unitary.conjStarAlgAut_star_apply,Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal,Function.comp_def] using
        hM.conjStarAlgAut_star_eigenvectorUnitary
  have hd : (Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ))+G).PosSemidef := by
    have h := hP.conjTranspose_mul_mul_same U
    have heq : Uᴴ*(M+F)*U=Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ))+G := by
      rw [Matrix.mul_add,Matrix.add_mul,hdiag]
    rw [heq] at h
    exact h
  have h := c1_negative_diagonal_count_le_rank hM.eigenvalues G hd
  exact h.trans ((Matrix.rank_mul_le_left (Uᴴ*F) U).trans
    (Matrix.rank_mul_le_right Uᴴ F))

theorem c1_hermitian_below_count_le_rank {M F : QMatrix I}
    (hM : M.IsHermitian) {c : ℝ} (hP : (M-c • (1 : QMatrix I)+F).PosSemidef) :
    Fintype.card {i : I // hM.eigenvalues i < c} ≤ F.rank := by
  let U : QMatrix I := hM.eigenvectorUnitary
  let G : QMatrix I := Uᴴ*F*U
  have hu : Uᴴ*U=1 := by
    simpa only [U,Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hdiag : Uᴴ*M*U=Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ)) := by
    simpa only [U,Unitary.conjStarAlgAut_star_apply,Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal,Function.comp_def] using
        hM.conjStarAlgAut_star_eigenvectorUnitary
  have hshift : Matrix.diagonal (fun i => (hM.eigenvalues i : ℂ))-c • (1 : QMatrix I)=
      Matrix.diagonal (fun i => ((hM.eigenvalues i-c : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Matrix.diagonal_apply,Matrix.smul_apply,Matrix.one_apply,Complex.real_smul]
    · simp [Matrix.diagonal_apply,Matrix.smul_apply,Matrix.one_apply,Complex.real_smul,hij]
  have hd : (Matrix.diagonal (fun i => ((hM.eigenvalues i-c : ℝ) : ℂ))+G).PosSemidef := by
    have h := hP.conjTranspose_mul_mul_same U
    have heq : Uᴴ*(M-c • (1 : QMatrix I)+F)*U=
        Matrix.diagonal (fun i => ((hM.eigenvalues i-c : ℝ) : ℂ))+G := by
      simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
        Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hdiag,hu,hshift,G]
    rw [heq] at h
    exact h
  have h := c1_negative_diagonal_count_le_rank (fun i => hM.eigenvalues i-c) G hd
  have h' := h.trans ((Matrix.rank_mul_le_left (Uᴴ*F) U).trans
    (Matrix.rank_mul_le_right Uᴴ F))
  simpa only [sub_lt_zero] using h'

theorem c1_psd_spectral_truncation {X : QMatrix I} (hX : X.PosSemidef)
    {w : ℝ} (hw : 0 ≤ w) :
    ∃ F R : QMatrix I, F.PosSemidef ∧ R.PosSemidef ∧ F+R=X ∧
      (w • (1 : QMatrix I)-R).PosSemidef ∧
      F.rank ≤ Fintype.card {i : I // w < hX.1.eigenvalues i} := by
  classical
  let U : QMatrix I := hX.1.eigenvectorUnitary
  let f : I → ℝ := fun i => if w < hX.1.eigenvalues i then hX.1.eigenvalues i else 0
  let r : I → ℝ := fun i => if w < hX.1.eigenvalues i then 0 else hX.1.eigenvalues i
  let Df : QMatrix I := Matrix.diagonal (fun i => (f i : ℂ))
  let Dr : QMatrix I := Matrix.diagonal (fun i => (r i : ℂ))
  let F : QMatrix I := U*Df*Uᴴ
  let R : QMatrix I := U*Dr*Uᴴ
  have hf (i : I) : 0 ≤ f i := by
    dsimp [f]
    split_ifs
    · exact hX.eigenvalues_nonneg i
    · exact le_rfl
  have hr (i : I) : 0 ≤ r i := by
    dsimp [r]
    split_ifs
    · exact le_rfl
    · exact hX.eigenvalues_nonneg i
  have hwr (i : I) : r i ≤ w := by
    dsimp [r]
    split_ifs with hi
    · exact hw
    · exact le_of_not_gt hi
  have hDf : Df.PosSemidef := Matrix.PosSemidef.diagonal (fun i => by
    exact Complex.nonneg_iff.mpr ⟨hf i,by simp⟩)
  have hDr : Dr.PosSemidef := Matrix.PosSemidef.diagonal (fun i => by
    exact Complex.nonneg_iff.mpr ⟨hr i,by simp⟩)
  have hF : F.PosSemidef := hDf.mul_mul_conjTranspose_same U
  have hR : R.PosSemidef := hDr.mul_mul_conjTranspose_same U
  have hu : U*Uᴴ=1 := by
    simpa only [U,Unitary.coe_star,Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hX.1.eigenvectorUnitary
  have hXeq : X=U*(Matrix.diagonal (fun i => (hX.1.eigenvalues i : ℂ)))*Uᴴ := by
    simpa only [U,Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal,Function.comp_def] using hX.1.spectral_theorem
  have hsum : Df+Dr=Matrix.diagonal (fun i => (hX.1.eigenvalues i : ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      by_cases hi : w < hX.1.eigenvalues i <;>
        simp [Df,Dr,f,r,Matrix.diagonal_apply,hi]
    · simp [Df,Dr,Matrix.diagonal_apply,hij]
  have hFR : F+R=X := by
    rw [hXeq]
    simp only [F,R,← Matrix.add_mul,← Matrix.mul_add,hsum]
  have hres : (w • (1 : QMatrix I)-R).PosSemidef := by
    have hdiag : (w • (1 : QMatrix I)-Dr).PosSemidef := by
      have heq : w • (1 : QMatrix I)-Dr=
          Matrix.diagonal (fun i => ((w-r i : ℝ) : ℂ)) := by
        ext i j
        by_cases hij : i=j
        · subst j
          simp [Dr,Matrix.diagonal_apply,Matrix.smul_apply,Matrix.one_apply,
            Complex.real_smul]
        · simp [Dr,Matrix.diagonal_apply,Matrix.smul_apply,Matrix.one_apply,hij]
      rw [heq]
      exact Matrix.PosSemidef.diagonal (fun i =>
        Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr (hwr i),by simp⟩)
    have h := hdiag.mul_mul_conjTranspose_same U
    simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_one,hu,R] using h
  have hnz (i : I) : (f i : ℂ) ≠ 0 ↔ w < hX.1.eigenvalues i := by
    by_cases hi : w < hX.1.eigenvalues i
    · have hpos : 0 < hX.1.eigenvalues i := hw.trans_lt hi
      simp [f,hi,ne_of_gt hpos]
    · simp [f,hi]
  have hrank : F.rank ≤ Fintype.card {i : I // w < hX.1.eigenvalues i} := by
    have hcard := Fintype.card_congr (Equiv.subtypeEquivRight hnz)
    calc
      F.rank ≤ Df.rank := (Matrix.rank_mul_le_left (U*Df) Uᴴ).trans
        (Matrix.rank_mul_le_right U Df)
      _ = Fintype.card {i : I // (f i : ℂ) ≠ 0} := Matrix.rank_diagonal _
      _ = _ := hcard
  exact ⟨F,R,hF,hR,hFR,hres,hrank⟩

theorem c1_schur_graph_count_le_rank (S : Matrix J I ℂ)
    (F : QMatrix (I ⊕ J)) {a : ℝ} (ha : 0 < a)
    (hP : (Matrix.fromBlocks (a • (1 : QMatrix I)) Sᴴ S
      (a • (1 : QMatrix J))+F).PosSemidef) :
    Fintype.card {i : I // a^2 <
      (Matrix.isHermitian_conjTranspose_mul_self S).eigenvalues i} ≤ F.rank := by
  let Q : QMatrix I := Sᴴ*S
  have hQ : Q.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self S
  let T : Matrix (I ⊕ J) I ℂ := Matrix.fromRows 1 ((-a⁻¹) • S)
  let G : QMatrix I := Tᴴ*F*T
  have hgraph : Tᴴ*(Matrix.fromBlocks (a • (1 : QMatrix I)) Sᴴ S
      (a • (1 : QMatrix J)))*T=a • (1 : QMatrix I)-a⁻¹ • Q := by
    simp [T,Q,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromBlocks,Matrix.fromCols_mul_fromRows,
      Matrix.mul_smul,Matrix.smul_mul,smul_smul,ha.ne',neg_smul,sub_eq_add_neg]
  have hg : (a • (1 : QMatrix I)-a⁻¹ • Q+G).PosSemidef := by
    have h := hP.conjTranspose_mul_mul_same T
    simpa only [Matrix.mul_add,Matrix.add_mul,hgraph,G] using h
  let U : QMatrix I := hQ.eigenvectorUnitary
  have hu : Uᴴ*U=1 := by
    simpa only [U,Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hQ.eigenvectorUnitary
  have hdiag : Uᴴ*Q*U=Matrix.diagonal (fun i => (hQ.eigenvalues i : ℂ)) := by
    simpa only [U,Unitary.conjStarAlgAut_star_apply,Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal,Function.comp_def] using
        hQ.conjStarAlgAut_star_eigenvectorUnitary
  have hshift : a • (1 : QMatrix I)-a⁻¹ •
      Matrix.diagonal (fun i => (hQ.eigenvalues i : ℂ))=
      Matrix.diagonal (fun i => ((a-a⁻¹*hQ.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Matrix.diagonal_apply,Matrix.smul_apply,Matrix.one_apply,Complex.real_smul]
    · simp [Matrix.diagonal_apply,Matrix.smul_apply,Matrix.one_apply,hij]
  have hd : (Matrix.diagonal (fun i => ((a-a⁻¹*hQ.eigenvalues i : ℝ) : ℂ))+
      Uᴴ*G*U).PosSemidef := by
    have h := hg.conjTranspose_mul_mul_same U
    simpa only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hu,hdiag,hshift] using h
  have hn := c1_negative_diagonal_count_le_rank
    (fun i => a-a⁻¹*hQ.eigenvalues i) (Uᴴ*G*U) hd
  have hrank : (Uᴴ*G*U).rank ≤ F.rank :=
    ((Matrix.rank_mul_le_left (Uᴴ*G) U).trans (Matrix.rank_mul_le_right Uᴴ G)).trans
      ((Matrix.rank_mul_le_left (Tᴴ*F) T).trans (Matrix.rank_mul_le_right Tᴴ F))
  have hiff (i : I) : a-a⁻¹*hQ.eigenvalues i < 0 ↔ a^2 < hQ.eigenvalues i := by
    rw [sub_lt_zero,inv_mul_eq_div,lt_div_iff₀ ha,pow_two]
  have hc := Fintype.card_congr (Equiv.subtypeEquivRight hiff)
  change Fintype.card {i : I // a^2 < hQ.eigenvalues i} ≤ F.rank
  rw [← hc]
  exact hn.trans hrank

theorem c1_young_low_rank_order {H W F R : QMatrix I}
    (hH : H.IsHermitian) (hW : W.IsHermitian)
    (hFR : W*W=F+R) {v w x : ℝ} (hv : v ≠ 0)
    (hR : (w • (1 : QMatrix I)-R).PosSemidef)
    (hbalance : (2+(v⁻¹)^2)*w=v^2*x) :
    (H*H+x • (1 : QMatrix I) -
      (1+v^2)⁻¹ • ((H-W)*(H-W)+W*W+x • (1 : QMatrix I)) +
      ((2+(v⁻¹)^2)/(1+v^2)) • F).PosSemidef := by
  let D : QMatrix I := (H-W)*(H-W)+W*W
  have ha : 0 < 1+v^2 := by positivity
  have hb : 0 ≤ 2+(v⁻¹)^2 := by positivity
  have hy : ((1+v^2) • (H*H)+(2+(v⁻¹)^2) • (W*W)-D).PosSemidef :=
    c1_young_difference_posSemidef hH hW hv
  have h := hy.add (hR.smul hb)
  have heq : (1+v^2) • (H*H)+(2+(v⁻¹)^2) • (W*W)-D +
      (2+(v⁻¹)^2) • (w • (1 : QMatrix I)-R) =
      (1+v^2) • (H*H+x • (1 : QMatrix I)) -
      (D+x • (1 : QMatrix I))+(2+(v⁻¹)^2) • F := by
    rw [hFR]
    simp only [smul_add,smul_sub,smul_smul,hbalance,add_smul,one_smul]
    module
  rw [heq] at h
  have hs := h.smul (inv_nonneg.mpr ha.le)
  simpa only [smul_add,smul_sub,smul_smul,inv_mul_cancel₀ ha.ne',one_smul,
    inv_mul_eq_div,mul_div_cancel_left₀ x ha.ne',D] using hs

def c1InvSqrt (P : QMatrix I) : QMatrix I :=
  cfc (fun d : ℝ => (Real.sqrt d)⁻¹) P

theorem c1InvSqrt_isHermitian (P : QMatrix I) : (c1InvSqrt P).IsHermitian :=
  IsSelfAdjoint.cfc

theorem c1InvSqrt_normalize {P : QMatrix I} (hP : P.PosDef) :
    c1InvSqrt P*P*c1InvSqrt P=1 := by
  let f : ℝ → ℝ := fun d => (Real.sqrt d)⁻¹
  have hcont (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ P) := by
    rw [hP.1.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range hP.1.eigenvalues).continuousOn g
  have heq : c1InvSqrt P*P*c1InvSqrt P=
      cfc (fun d : ℝ => f d*d*f d) P := by
    rw [cfc_mul (p := IsSelfAdjoint) (fun d => f d*d) f P (hcont _) (hcont _),
      cfc_mul (p := IsSelfAdjoint) f (fun d : ℝ => d) P (hcont _) (hcont _),
      cfc_id' (p := IsSelfAdjoint) ℝ P hP.1]
    rfl
  rw [heq,← cfc_const_one (p := IsSelfAdjoint) ℝ P hP.1]
  apply cfc_congr
  intro d hd
  rw [hP.1.spectrum_real_eq_range_eigenvalues] at hd
  obtain ⟨i,rfl⟩ := hd
  have hi := hP.eigenvalues_pos i
  have hs : (Real.sqrt (hP.1.eigenvalues i)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hi)
  dsimp [f]
  field_simp
  nlinarith [Real.sq_sqrt hi.le]

theorem c1InvSqrt_sq {P : QMatrix I} (hP : P.PosDef) :
    c1InvSqrt P*c1InvSqrt P=P⁻¹ := by
  let K : QMatrix I := c1InvSqrt P
  have hc : Commute P K := by
    have h := cfc_commute_cfc (p := IsSelfAdjoint) (fun d : ℝ => d)
      (fun d : ℝ => (Real.sqrt d)⁻¹) P
    simpa only [cfc_id' (p := IsSelfAdjoint) ℝ P hP.1,K,c1InvSqrt] using h
  have hn : K*P*K=1 := c1InvSqrt_normalize hP
  have hprod : P*(K*K)=1 := by
    rw [← Matrix.mul_assoc,hc.eq,hn]
  letI : Invertible P := hP.isUnit.invertible
  calc
    K*K=(P⁻¹*P)*(K*K) := by rw [Matrix.inv_mul_of_invertible,Matrix.one_mul]
    _ = P⁻¹*(P*(K*K)) := Matrix.mul_assoc _ _ _
    _ = P⁻¹ := by rw [hprod,Matrix.mul_one]

theorem c1_normalized_young_schur_count {H W : QMatrix (I ⊕ J)}
    (hH : H.IsHermitian) (hW : W.IsHermitian)
    (K : QMatrix (I ⊕ J)) (S : Matrix J I ℂ)
    {v w x : ℝ} (hv : v ≠ 0) (hw : 0 ≤ w)
    (hbalance : (2+(v⁻¹)^2)*w=v^2*x)
    (hK : Kᴴ*((H-W)*(H-W)+W*W+x • (1 : QMatrix (I ⊕ J)))*K=1)
    (hM : Kᴴ*(H*H+x • (1 : QMatrix (I ⊕ J)))*K=
      Matrix.fromBlocks (1 : QMatrix I) Sᴴ S (1 : QMatrix J)) :
    Fintype.card {i : I // (1-(1+v^2)⁻¹)^2 <
      (Matrix.isHermitian_conjTranspose_mul_self S).eigenvalues i} ≤
    Fintype.card {i : I ⊕ J // w <
      (c1_hermitian_square_posSemidef hW).1.eigenvalues i} := by
  obtain ⟨F,R,hF,hR,hFR,hres,hrank⟩ :=
    c1_psd_spectral_truncation (c1_hermitian_square_posSemidef hW) hw
  let γ : ℝ := (2+(v⁻¹)^2)/(1+v^2)
  let G : QMatrix (I ⊕ J) := γ • (Kᴴ*F*K)
  let a : ℝ := 1-(1+v^2)⁻¹
  have ha : 0 < a := by
    apply sub_pos.mpr
    apply (inv_lt_one₀ (by positivity : 0 < 1+v^2)).2
    nlinarith [sq_pos_of_ne_zero hv]
  have hy := c1_young_low_rank_order hH hW hFR.symm hv hres hbalance
  have hp := hy.conjTranspose_mul_mul_same K
  have hblock : Matrix.fromBlocks (1 : QMatrix I) Sᴴ S (1 : QMatrix J)-
      (1+v^2)⁻¹ • (1 : QMatrix (I ⊕ J))=
      Matrix.fromBlocks (a • (1 : QMatrix I)) Sᴴ S (a • (1 : QMatrix J)) := by
    ext i j
    cases i <;> cases j <;>
      simp [a,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.sub_apply,
        Matrix.smul_apply,Matrix.one_apply,sub_smul]
  have hpos : (Matrix.fromBlocks (a • (1 : QMatrix I)) Sᴴ S
      (a • (1 : QMatrix J))+G).PosSemidef := by
    have heq (X D E : QMatrix (I ⊕ J)) (c d : ℝ) :
        Kᴴ*(X-c • D+d • E)*K=
        Kᴴ*X*K-c • (Kᴴ*D*K)+d • (Kᴴ*E*K) := by
      simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,
        Matrix.mul_smul,Matrix.smul_mul]
    rw [heq,hK,hM,hblock] at hp
    exact hp
  have hg : G.rank ≤ F.rank := by
    have heq : G=(γ • (1 : QMatrix (I ⊕ J)))*(Kᴴ*F*K) := by
      simp only [G,Matrix.smul_mul,Matrix.one_mul]
    rw [heq]
    exact (Matrix.rank_mul_le_right _ _).trans
      ((Matrix.rank_mul_le_left (Kᴴ*F) K).trans (Matrix.rank_mul_le_right Kᴴ F))
  exact (c1_schur_graph_count_le_rank S G ha hpos).trans (hg.trans hrank)

def c1BlockNormalizer (P0 : QMatrix I) (P1 : QMatrix J) : QMatrix (I ⊕ J) :=
  Matrix.fromBlocks (c1InvSqrt P0) 0 0 (c1InvSqrt P1)

def c1SchurFactor (P0 : QMatrix I) (P1 : QMatrix J) (Y : Matrix J I ℂ) : Matrix J I ℂ :=
  c1InvSqrt P1*Y*c1InvSqrt P0

theorem c1_block_whitening {P0 : QMatrix I} {P1 : QMatrix J}
    (hP0 : P0.PosDef) (hP1 : P1.PosDef) (Y : Matrix J I ℂ) :
    (c1BlockNormalizer P0 P1)ᴴ*(Matrix.fromBlocks P0 Yᴴ Y P1)*
      (c1BlockNormalizer P0 P1)=
      Matrix.fromBlocks (1 : QMatrix I) (c1SchurFactor P0 P1 Y)ᴴ
        (c1SchurFactor P0 P1 Y) (1 : QMatrix J) := by
  have hK0 := c1InvSqrt_isHermitian P0
  have hK1 := c1InvSqrt_isHermitian P1
  have hN0 := c1InvSqrt_normalize hP0
  have hN1 := c1InvSqrt_normalize hP1
  have hs : (c1SchurFactor P0 P1 Y)ᴴ=c1InvSqrt P0*Yᴴ*c1InvSqrt P1 := by
    simp only [c1SchurFactor,Matrix.conjTranspose_mul,hK0.eq,hK1.eq,Matrix.mul_assoc]
  rw [hs]
  simp only [c1BlockNormalizer,Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply,Matrix.conjTranspose_zero,hK0.eq,hK1.eq,
    Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,hN0,hN1,hs,c1SchurFactor]

theorem c1_block_whitening_diagonal {P0 : QMatrix I} {P1 : QMatrix J}
    (hP0 : P0.PosDef) (hP1 : P1.PosDef) :
    (c1BlockNormalizer P0 P1)ᴴ*(Matrix.fromBlocks P0 0 0 P1)*
      (c1BlockNormalizer P0 P1)=1 := by
  simpa only [c1SchurFactor,Matrix.conjTranspose_zero,Matrix.mul_zero,
    Matrix.zero_mul,Matrix.fromBlocks_one] using c1_block_whitening hP0 hP1 (0 : Matrix J I ℂ)

theorem c1_binary_square_regularized_blocks {A : QMatrix I} {B : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (Z : Matrix J I ℂ) (x : ℝ) :
    c1Binary A B Z*c1Binary A B Z+x • (1 : QMatrix (I ⊕ J))=
      Matrix.fromBlocks (A*A+Zᴴ*Z+x • (1 : QMatrix I)) (Z*A+B*Z)ᴴ
        (Z*A+B*Z) (B*B+Z*Zᴴ+x • (1 : QMatrix J)) := by
  rw [c1Binary_square_blocks]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.add_apply,
      Matrix.smul_apply,Matrix.one_apply,Matrix.conjTranspose_add,
      Matrix.conjTranspose_mul,hA.eq,hB.eq,add_comm]

theorem c1_binary_young_diagonal (A : QMatrix I) (B : QMatrix J)
    (Z : Matrix J I ℂ) (x : ℝ) :
    (c1Binary A B Z-c1Binary (0 : QMatrix I) (0 : QMatrix J) Z)*
      (c1Binary A B Z-c1Binary (0 : QMatrix I) (0 : QMatrix J) Z)+
      c1Binary (0 : QMatrix I) (0 : QMatrix J) Z*
        c1Binary (0 : QMatrix I) (0 : QMatrix J) Z+x • (1 : QMatrix (I ⊕ J))=
      Matrix.fromBlocks (A*A+Zᴴ*Z+x • (1 : QMatrix I)) 0 0
        (B*B+Z*Zᴴ+x • (1 : QMatrix J)) := by
  have hdiff : c1Binary A B Z-c1Binary (0 : QMatrix I) (0 : QMatrix J) Z=
      c1Binary A B (0 : Matrix J I ℂ) := by
    ext i j
    cases i <;> cases j <;> simp [c1Binary,Matrix.fromBlocks,Matrix.sub_apply]
  rw [hdiff,c1Binary_square_blocks,c1Binary_square_blocks]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.add_apply,
      Matrix.smul_apply,Matrix.one_apply]

theorem c1_binary_schur_count_parameter {A : QMatrix I} {B : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (Z : Matrix J I ℂ)
    {v w x : ℝ} (hv : v ≠ 0) (hw : 0 ≤ w) (hx : 0 < x)
    (hbalance : (2+(v⁻¹)^2)*w=v^2*x) :
    let P0 := A*A+Zᴴ*Z+x • (1 : QMatrix I)
    let P1 := B*B+Z*Zᴴ+x • (1 : QMatrix J)
    let S := c1SchurFactor P0 P1 (Z*A+B*Z)
    let W := c1Binary (0 : QMatrix I) (0 : QMatrix J) Z
    Fintype.card {i : I // (1-(1+v^2)⁻¹)^2 <
      (Matrix.isHermitian_conjTranspose_mul_self S).eigenvalues i} ≤
    Fintype.card {i : I ⊕ J // w <
      (c1_hermitian_square_posSemidef
        (c1Binary_isHermitian Z (Matrix.isHermitian_zero) (Matrix.isHermitian_zero))).1.eigenvalues i} := by
  let P0 : QMatrix I := A*A+Zᴴ*Z+x • (1 : QMatrix I)
  let P1 : QMatrix J := B*B+Z*Zᴴ+x • (1 : QMatrix J)
  have hp0 : P0.PosDef := c1_regularized_posDef
    ((c1_hermitian_square_posSemidef hA).add (Matrix.posSemidef_conjTranspose_mul_self Z)) hx
  have hp1 : P1.PosDef := c1_regularized_posDef
    ((c1_hermitian_square_posSemidef hB).add (Matrix.posSemidef_self_mul_conjTranspose Z)) hx
  apply c1_normalized_young_schur_count (c1Binary_isHermitian Z hA hB)
    (c1Binary_isHermitian Z Matrix.isHermitian_zero Matrix.isHermitian_zero)
    (c1BlockNormalizer P0 P1) (c1SchurFactor P0 P1 (Z*A+B*Z)) hv hw hbalance
  · rw [c1_binary_young_diagonal]
    exact c1_block_whitening_diagonal hp0 hp1
  · rw [c1_binary_square_regularized_blocks hA hB]
    exact c1_block_whitening hp0 hp1 _

theorem c1_adaptive_young_parameter {w x : ℝ} (hw : 0 < w) (hx : 0 < x) :
    ∃ v : ℝ, v ≠ 0 ∧ (2+(v⁻¹)^2)*w=v^2*x ∧
      (1-(1+v^2)⁻¹)^2=w/(x+w) := by
  let r : ℝ := Real.sqrt (1+x/w)
  have harg : 0 < 1+x/w := by positivity
  have hr : 0 < r := Real.sqrt_pos.2 harg
  have hrsq : r^2=1+x/w := Real.sq_sqrt harg.le
  have hr1 : 1 < r := by
    have hquot : 0 < x/w := div_pos hx hw
    nlinarith
  let e : ℝ := (r-1)⁻¹
  have he : 0 < e := inv_pos.mpr (sub_pos.mpr hr1)
  let v : ℝ := Real.sqrt e
  have hv : v ≠ 0 := ne_of_gt (Real.sqrt_pos.2 he)
  have hvsq : v^2=e := Real.sq_sqrt he.le
  have hvinv : (v⁻¹)^2=e⁻¹ := by rw [inv_pow,hvsq]
  have hxexpr : x=w*(r^2-1) := by
    rw [hrsq]
    field_simp [hw.ne']
    <;> ring
  have hbal : (2+e⁻¹)*w=e*x := by
    rw [hxexpr]
    dsimp [e]
    rw [inv_inv]
    field_simp [sub_ne_zero.mpr hr1.ne']
    <;> ring
  have hone : 1+e=r/(r-1) := by
    dsimp [e]
    field_simp [sub_ne_zero.mpr hr1.ne']
    <;> ring
  have ha : 1-(1+e)⁻¹=r⁻¹ := by
    rw [hone,inv_div]
    field_simp [hr.ne']
    <;> ring
  have hrden : r^2=(x+w)/w := by
    rw [hrsq]
    field_simp [hw.ne']
    <;> ring
  have hth : (r⁻¹)^2=w/(x+w) := by rw [inv_pow,hrden,inv_div]
  refine ⟨v,hv,?_,?_⟩
  · rw [hvinv,hvsq]
    exact hbal
  · rw [hvsq,ha]
    exact hth

theorem c1_binary_schur_count {A : QMatrix I} {B : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (Z : Matrix J I ℂ)
    {w x : ℝ} (hw : 0 < w) (hx : 0 < x) :
    let P0 := A*A+Zᴴ*Z+x • (1 : QMatrix I)
    let P1 := B*B+Z*Zᴴ+x • (1 : QMatrix J)
    let S := c1SchurFactor P0 P1 (Z*A+B*Z)
    Fintype.card {i : I // w/(x+w) <
      (Matrix.isHermitian_conjTranspose_mul_self S).eigenvalues i} ≤
    Fintype.card {i : I ⊕ J // w <
      (c1_hermitian_square_posSemidef
        (c1Binary_isHermitian Z (Matrix.isHermitian_zero) (Matrix.isHermitian_zero))).1.eigenvalues i} := by
  obtain ⟨v,hv,hbal,hth⟩ := c1_adaptive_young_parameter hw hx
  have h := c1_binary_schur_count_parameter hA hB Z hv hw.le hx hbal
  simpa only [hth] using h

theorem c1_ordered_head_count {n : ℕ} (a : Fin n → ℝ) (ha : Antitone a)
    (k : Fin n) {c : ℝ} (hc : c < a k) :
    k.val+1 ≤ Fintype.card {i : Fin n // c < a i} := by
  classical
  let f : Fin (k.val+1) → {i : Fin n // c < a i} := fun i =>
    ⟨⟨i.val,by omega⟩,hc.trans_le (ha (by change i.val ≤ k.val; omega))⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun z : {i : Fin n // c < a i} => z.val.val) hij
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem c1_ordered_tail_count {n : ℕ} (a : Fin n → ℝ) (ha : Antitone a)
    (k : Fin n) {c : ℝ} (hc : a k ≤ c) :
    Fintype.card {i : Fin n // c < a i} ≤ k.val := by
  classical
  let f : {i : Fin n // c < a i} → Fin k.val := fun i =>
    ⟨i.val.val,by
      by_contra hi
      have hk : k ≤ i.val := by omega
      exact not_lt_of_ge ((ha hk).trans hc) i.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin k.val => z.val) hij
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

theorem c1_hermitian_eigenvalue_count_ordered {M : QMatrix I}
    (hM : M.IsHermitian) (c : ℝ) :
    Fintype.card {i : I // c < hM.eigenvalues i}=
      Fintype.card {i : Fin (Fintype.card I) // c < hM.eigenvalues₀ i} := by
  classical
  let e : I ≃ Fin (Fintype.card I) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  exact Fintype.card_congr (e.subtypeEquiv (fun i => Iff.rfl))

theorem c1_count_resolvent_order {n m : ℕ} (hnm : n ≤ m)
    (q : Fin n → ℝ) (w : Fin m → ℝ) (hq : Antitone q) (hw : Antitone w)
    (hw0 : ∀ i, 0 ≤ w i) {x : ℝ} (hx : 0 < x)
    (hcount : ∀ s : ℝ, 0 < s →
      Fintype.card {i : Fin n // s/(x+s) < q i} ≤
      Fintype.card {i : Fin m // s < w i}) :
    ∀ k : Fin n, q k ≤ w (Fin.castLE hnm k)/(x+w (Fin.castLE hnm k)) := by
  intro k
  let j : Fin m := Fin.castLE hnm k
  by_contra hk
  have hqgt : w j/(x+w j) < q k := lt_of_not_ge hk
  by_cases hwj : w j=0
  · have hqpos : 0 < q k := by simpa only [hwj,zero_div] using hqgt
    let s : ℝ := x*q k/2
    have hs : 0 < s := by dsimp [s]; positivity
    have htest : s/(x+s) < q k := by
      apply (div_lt_iff₀ (by linarith : 0 < x+s)).2
      have hp : 0 < x*q k := mul_pos hx hqpos
      have hqs : 0 < q k*s := mul_pos hqpos hs
      dsimp [s] at *
      nlinarith
    have hhead := c1_ordered_head_count q hq k htest
    have htail := c1_ordered_tail_count w hw j (c := s) (by rw [hwj]; exact hs.le)
    have h := hhead.trans ((hcount s hs).trans htail)
    change k.val+1 ≤ k.val at h
    omega
  · have hpos : 0 < w j := lt_of_le_of_ne (hw0 j) (Ne.symm hwj)
    have hhead := c1_ordered_head_count q hq k hqgt
    have htail := c1_ordered_tail_count w hw j (le_refl (w j))
    have h := hhead.trans ((hcount (w j) hpos).trans htail)
    change k.val+1 ≤ k.val at h
    omega

theorem c1_hermitian_count_resolvent_order {Q : QMatrix I} {X : QMatrix J}
    (hQ : Q.IsHermitian) (hX : X.PosSemidef)
    (hcard : Fintype.card I ≤ Fintype.card J) {x : ℝ} (hx : 0 < x)
    (hcount : ∀ s : ℝ, 0 < s →
      Fintype.card {i : I // s/(x+s) < hQ.eigenvalues i} ≤
      Fintype.card {i : J // s < hX.1.eigenvalues i}) :
    ∀ k : Fin (Fintype.card I), hQ.eigenvalues₀ k ≤
      hX.1.eigenvalues₀ (Fin.castLE hcard k)/(x+hX.1.eigenvalues₀ (Fin.castLE hcard k)) := by
  have hw0 (k : Fin (Fintype.card J)) : 0 ≤ hX.1.eigenvalues₀ k := by
    let e : Fin (Fintype.card J) ≃ J := Fintype.equivOfCardEq (Fintype.card_fin _)
    have h := hX.eigenvalues_nonneg (e k)
    simpa only [Matrix.IsHermitian.eigenvalues,e,Equiv.symm_apply_apply] using h
  apply c1_count_resolvent_order hcard hQ.eigenvalues₀ hX.1.eigenvalues₀
    hQ.eigenvalues₀_antitone hX.1.eigenvalues₀_antitone hw0 hx
  intro s hs
  simpa only [c1_hermitian_eigenvalue_count_ordered] using hcount s hs

def c1Nonlinear (q : ℝ) : ℝ := -Real.log (1-q)-q

@[simp] theorem c1Nonlinear_zero : c1Nonlinear 0=0 := by simp [c1Nonlinear]

theorem c1Nonlinear_hasDerivAt {q : ℝ} (hq : q < 1) :
    HasDerivAt c1Nonlinear (q/(1-q)) q := by
  have hn : 1-q ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  have h := (((hasDerivAt_const q (1 : ℝ)).sub (hasDerivAt_id q)).log hn).neg.sub
    (hasDerivAt_id q)
  convert h using 1
  · rfl
  · change q/(1-q) = -((0-1)/(1-q))-1
    field_simp [hn]
    <;> ring

theorem c1Nonlinear_continuousOn : ContinuousOn c1Nonlinear (Set.Iio (1 : ℝ)) := by
  intro q hq
  exact (c1Nonlinear_hasDerivAt hq).continuousAt.continuousWithinAt

theorem c1Nonlinear_monotoneOn : MonotoneOn c1Nonlinear (Set.Ico (0 : ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun q => q/(1-q))
    (convex_Ico (0 : ℝ) 1)
    (c1Nonlinear_continuousOn.mono (fun _ h => h.2))
  · intro q hq
    exact (c1Nonlinear_hasDerivAt (interior_subset hq).2).hasDerivWithinAt
  · intro q hq
    have h := interior_subset hq
    exact div_nonneg h.1 (sub_pos.mpr h.2).le

theorem c1Nonlinear_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ c1Nonlinear q := by
  have h := c1Nonlinear_monotoneOn (by simp : (0 : ℝ) ∈ Set.Ico 0 1) ⟨hq0,hq1⟩ hq0
  simpa only [c1Nonlinear_zero] using h

theorem c1Nonlinear_resolvent_kernel {w x : ℝ} (hw : 0 ≤ w) (hx : 0 < x) :
    c1Nonlinear (w/(x+w))=Real.log (x+w)-Real.log x-w*(x+w)⁻¹ := by
  have hd : 0 < x+w := by linarith
  have heq : 1-w/(x+w)=x/(x+w) := by field_simp [hd.ne']; ring
  rw [c1Nonlinear,heq,Real.log_div hx.ne' hd.ne']
  rw [div_eq_mul_inv]
  ring

theorem c1_resolvent_threshold_mem {w x : ℝ} (hw : 0 ≤ w) (hx : 0 < x) :
    w/(x+w) ∈ Set.Ico (0 : ℝ) 1 := by
  have hd : 0 < x+w := by linarith
  exact ⟨div_nonneg hw hd.le,(div_lt_one hd).2 (by linarith)⟩

theorem c1_ordered_nonlinear_payment {n m : ℕ} (hnm : n ≤ m)
    (q : Fin n → ℝ) (w : Fin m → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (hw0 : ∀ i, 0 ≤ w i) {x : ℝ} (hx : 0 < x)
    (horder : ∀ k, q k ≤ w (Fin.castLE hnm k)/(x+w (Fin.castLE hnm k))) :
    (∑ i, c1Nonlinear (q i)) ≤ ∑ j, c1Nonlinear (w j/(x+w j)) := by
  classical
  let e : Fin n → Fin m := Fin.castLE hnm
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun k : Fin m => k.val) hij
  calc
    (∑ i, c1Nonlinear (q i)) ≤ ∑ i, c1Nonlinear (w (e i)/(x+w (e i))) := by
      apply Finset.sum_le_sum
      intro i hi
      have ht := c1_resolvent_threshold_mem (hw0 (e i)) hx
      exact c1Nonlinear_monotoneOn ⟨hq0 i,(horder i).trans_lt ht.2⟩ ht (horder i)
    _ = ∑ j ∈ Finset.univ.image e, c1Nonlinear (w j/(x+w j)) := by
      rw [Finset.sum_image (fun i _ j _ h => he h)]
    _ ≤ ∑ j, c1Nonlinear (w j/(x+w j)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ =>
        let ht := c1_resolvent_threshold_mem (hw0 j) hx
        c1Nonlinear_nonneg ht.1 ht.2)

theorem c1_hermitian_spectral_sum_ordered {M : QMatrix I}
    (hM : M.IsHermitian) (f : ℝ → ℝ) :
    (∑ i, f (hM.eigenvalues i))=∑ i : Fin (Fintype.card I), f (hM.eigenvalues₀ i) := by
  let e : I ≃ Fin (Fintype.card I) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  exact e.sum_comp (fun i => f (hM.eigenvalues₀ i))

theorem c1_psd_ordered_eigenvalues_nonneg {M : QMatrix I} (hM : M.PosSemidef)
    (k : Fin (Fintype.card I)) : 0 ≤ hM.1.eigenvalues₀ k := by
  let e : Fin (Fintype.card I) ≃ I := Fintype.equivOfCardEq (Fintype.card_fin _)
  have h := hM.eigenvalues_nonneg (e k)
  simpa only [Matrix.IsHermitian.eigenvalues,e,Equiv.symm_apply_apply] using h

theorem c1_hermitian_count_nonlinear_trace {Q : QMatrix I} {X : QMatrix J}
    (hQ : Q.PosSemidef) (hX : X.PosSemidef)
    (hcard : Fintype.card I ≤ Fintype.card J) {x : ℝ} (hx : 0 < x)
    (hcount : ∀ s : ℝ, 0 < s →
      Fintype.card {i : I // s/(x+s) < hQ.1.eigenvalues i} ≤
      Fintype.card {i : J // s < hX.1.eigenvalues i}) :
    (Matrix.trace (cfc c1Nonlinear Q)).re ≤
      ∑ j, c1Nonlinear (hX.1.eigenvalues j/(x+hX.1.eigenvalues j)) := by
  rw [QuantumProver.SuperchannelDiscrimination.Klein.trace_cfc_eq_sum _ hQ.1,
    c1_hermitian_spectral_sum_ordered hQ.1 c1Nonlinear,
    c1_hermitian_spectral_sum_ordered hX.1 (fun d => c1Nonlinear (d/(x+d)))]
  exact c1_ordered_nonlinear_payment hcard hQ.1.eigenvalues₀ hX.1.eigenvalues₀
    (c1_psd_ordered_eigenvalues_nonneg hQ) (c1_psd_ordered_eigenvalues_nonneg hX) hx
    (c1_hermitian_count_resolvent_order hQ.1 hX hcard hx hcount)

theorem c1_binary_nonlinear_trace_bound {A : QMatrix I} {B : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (Z : Matrix J I ℂ)
    {x : ℝ} (hx : 0 < x) :
    let P0 := A*A+Zᴴ*Z+x • (1 : QMatrix I)
    let P1 := B*B+Z*Zᴴ+x • (1 : QMatrix J)
    let S := c1SchurFactor P0 P1 (Z*A+B*Z)
    let hW := c1_hermitian_square_posSemidef
      (c1Binary_isHermitian Z (Matrix.isHermitian_zero) (Matrix.isHermitian_zero))
    (Matrix.trace (cfc c1Nonlinear (Sᴴ*S))).re ≤
      ∑ j, (Real.log (x+hW.1.eigenvalues j)-Real.log x-
        hW.1.eigenvalues j*(x+hW.1.eigenvalues j)⁻¹) := by
  let P0 : QMatrix I := A*A+Zᴴ*Z+x • (1 : QMatrix I)
  let P1 : QMatrix J := B*B+Z*Zᴴ+x • (1 : QMatrix J)
  let S : Matrix J I ℂ := c1SchurFactor P0 P1 (Z*A+B*Z)
  let hW := c1_hermitian_square_posSemidef
    (c1Binary_isHermitian Z (Matrix.isHermitian_zero) (Matrix.isHermitian_zero))
  have hc : Fintype.card I ≤ Fintype.card (I ⊕ J) := by simp only [Fintype.card_sum]; omega
  have h := c1_hermitian_count_nonlinear_trace
    (Matrix.posSemidef_conjTranspose_mul_self S) hW hc hx
    (fun s hs => c1_binary_schur_count hA hB Z hs hx)
  have heq : (∑ j, c1Nonlinear (hW.1.eigenvalues j/(x+hW.1.eigenvalues j)))=
      ∑ j, (Real.log (x+hW.1.eigenvalues j)-Real.log x-
        hW.1.eigenvalues j*(x+hW.1.eigenvalues j)⁻¹) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact c1Nonlinear_resolvent_kernel (hW.eigenvalues_nonneg j) hx
  rw [heq] at h
  exact h

theorem c1_mulVec_injective_of_congruence_one (K D : QMatrix I)
    (hN : Kᴴ*D*K=1) : Function.Injective (fun v : I → ℂ => K*ᵥ v) := by
  have hl : Function.LeftInverse (fun v : I → ℂ => (Kᴴ*D)*ᵥ v)
      (fun v : I → ℂ => K*ᵥ v) := by
    intro v
    change (Kᴴ*D)*ᵥ (K*ᵥ v)=v
    rw [Matrix.mulVec_mulVec,hN,Matrix.one_mulVec]
  exact hl.injective

theorem c1_unit_block_schur_posDef (S : Matrix J I ℂ)
    (hM : (Matrix.fromBlocks (1 : QMatrix I) Sᴴ S (1 : QMatrix J)).PosDef) :
    ((1 : QMatrix I)-Sᴴ*S).PosDef := by
  have hs : (Matrix.fromBlocks (1 : QMatrix J) S Sᴴ (1 : QMatrix I)).PosDef := by
    have h := hM.submatrix (Equiv.sumComm J I).injective
    simpa only [Equiv.sumComm_apply,Matrix.fromBlocks_submatrix_sum_swap_sum_swap] using h
  have h := c1_schur_posDef Sᴴ (Matrix.PosDef.one : (1 : QMatrix J).PosDef)
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hs)
  simpa only [inv_one,Matrix.mul_one,Matrix.conjTranspose_conjTranspose] using h

theorem c1_schur_normalized_log {P0 : QMatrix I} {P1 : QMatrix J}
    (hP0 : P0.PosDef) (hP1 : P1.PosDef) (Y : Matrix J I ℂ)
    (hblock : (Matrix.fromBlocks P0 Yᴴ Y P1).PosDef) :
    let S := c1SchurFactor P0 P1 Y
    ((1 : QMatrix I)-Sᴴ*S).PosDef ∧
    (Matrix.trace (cfc Real.log P0)).re+(Matrix.trace (cfc Real.log P1)).re-
      (Matrix.trace (cfc Real.log (Matrix.fromBlocks P0 Yᴴ Y P1))).re=
      -(Matrix.trace (cfc Real.log ((1 : QMatrix I)-Sᴴ*S))).re := by
  let K : QMatrix (I ⊕ J) := c1BlockNormalizer P0 P1
  let S : Matrix J I ℂ := c1SchurFactor P0 P1 Y
  have hn : Kᴴ*(Matrix.fromBlocks P0 0 0 P1)*K=1 := c1_block_whitening_diagonal hP0 hP1
  have hw : Kᴴ*(Matrix.fromBlocks P0 Yᴴ Y P1)*K=
      Matrix.fromBlocks (1 : QMatrix I) Sᴴ S (1 : QMatrix J) := c1_block_whitening hP0 hP1 Y
  have hM : (Matrix.fromBlocks (1 : QMatrix I) Sᴴ S (1 : QMatrix J)).PosDef := by
    have h := hblock.conjTranspose_mul_mul_same
      (c1_mulVec_injective_of_congruence_one K (Matrix.fromBlocks P0 0 0 P1) hn)
    rw [hw] at h
    exact h
  have hIQ := c1_unit_block_schur_posDef S hM
  have hkdet : Matrix.det Kᴴ*(Matrix.det P0*Matrix.det P1)*Matrix.det K=1 := by
    simpa only [Matrix.det_mul,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one] using
      congrArg Matrix.det hn
  have hmdet : Matrix.det (Matrix.fromBlocks (1 : QMatrix I) Sᴴ S (1 : QMatrix J))=
      Matrix.det Kᴴ*Matrix.det (Matrix.fromBlocks P0 Yᴴ Y P1)*Matrix.det K := by
    simpa only [Matrix.det_mul] using (congrArg Matrix.det hw).symm
  have hdet : Matrix.det (Matrix.fromBlocks P0 Yᴴ Y P1)=
      (Matrix.det P0*Matrix.det P1)*Matrix.det ((1 : QMatrix I)-Sᴴ*S) := by
    calc
      _ = 1*Matrix.det (Matrix.fromBlocks P0 Yᴴ Y P1) := (one_mul _).symm
      _ = (Matrix.det Kᴴ*(Matrix.det P0*Matrix.det P1)*Matrix.det K)*
          Matrix.det (Matrix.fromBlocks P0 Yᴴ Y P1) := by rw [hkdet]
      _ = (Matrix.det P0*Matrix.det P1)*
          Matrix.det (Matrix.fromBlocks (1 : QMatrix I) Sᴴ S (1 : QMatrix J)) := by
        rw [hmdet]
        ring
      _ = _ := by rw [Matrix.det_fromBlocks_one₂₂]
  have hp0 := Complex.pos_iff.mp hP0.det_pos
  have hp1 := Complex.pos_iff.mp hP1.det_pos
  have hpi := Complex.pos_iff.mp hIQ.det_pos
  have hdre : (Matrix.det (Matrix.fromBlocks P0 Yᴴ Y P1)).re=
      (Matrix.det P0).re*(Matrix.det P1).re*(Matrix.det ((1 : QMatrix I)-Sᴴ*S)).re := by
    rw [hdet]
    simp only [Complex.mul_re,Complex.mul_im,← hp0.2,← hp1.2,← hpi.2,
      zero_mul,mul_zero,sub_zero,add_zero]
  refine ⟨hIQ,?_⟩
  rw [c1_trace_log_eq_log_det hP0,c1_trace_log_eq_log_det hP1,
    c1_trace_log_eq_log_det hblock,c1_trace_log_eq_log_det hIQ,hdre,
    Real.log_mul (mul_ne_zero hp0.1.ne' hp1.1.ne') hpi.1.ne',
    Real.log_mul hp0.1.ne' hp1.1.ne']
  ring

theorem c1_nonlinear_trace_identity {Q : QMatrix I} (hQ : Q.IsHermitian) :
    (Matrix.trace (cfc c1Nonlinear Q)).re+(Matrix.trace Q).re=
      -(Matrix.trace (cfc Real.log ((1 : QMatrix I)-Q))).re := by
  have hfin : (spectrum ℝ Q).Finite := by
    rw [hQ.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ Q) := hfin.continuousOn f
  have haff : cfc (fun q : ℝ => 1-q) Q=(1 : QMatrix I)-Q := by
    rw [cfc_sub (p := IsSelfAdjoint) (fun _ : ℝ => 1) (fun q : ℝ => q) Q
      (hcont _) (hcont _),cfc_const_one (p := IsSelfAdjoint) ℝ Q hQ,
      cfc_id' (p := IsSelfAdjoint) ℝ Q hQ]
  have hlog : cfc (fun q : ℝ => Real.log (1-q)) Q=
      cfc Real.log ((1 : QMatrix I)-Q) := by
    have h := cfc_comp (p := IsSelfAdjoint) Real.log (fun q : ℝ => 1-q) Q hQ
      ((hfin.image _).continuousOn _) (hcont _)
    simpa only [Function.comp_def,haff] using h
  have hfun : cfc c1Nonlinear Q= -cfc Real.log ((1 : QMatrix I)-Q)-Q := by
    change cfc (fun q : ℝ => -Real.log (1-q)-q) Q= _
    rw [cfc_sub (p := IsSelfAdjoint) (fun q : ℝ => -Real.log (1-q))
      (fun q : ℝ => q) Q (hcont _) (hcont _),
      cfc_neg (p := IsSelfAdjoint) (fun q : ℝ => Real.log (1-q)) Q,
      hlog,cfc_id' (p := IsSelfAdjoint) ℝ Q hQ]
  rw [hfun,Matrix.trace_sub,Matrix.trace_neg,Complex.sub_re,Complex.neg_re]
  ring

theorem c1_schur_cost_decomposition {P0 : QMatrix I} {P1 : QMatrix J}
    (hP0 : P0.PosDef) (hP1 : P1.PosDef) (Y : Matrix J I ℂ)
    (hblock : (Matrix.fromBlocks P0 Yᴴ Y P1).PosDef) :
    let S := c1SchurFactor P0 P1 Y
    (Matrix.trace (cfc Real.log P0)).re+(Matrix.trace (cfc Real.log P1)).re-
      (Matrix.trace (cfc Real.log (Matrix.fromBlocks P0 Yᴴ Y P1))).re=
      (Matrix.trace (cfc c1Nonlinear (Sᴴ*S))).re+(Matrix.trace (Sᴴ*S)).re := by
  have h := c1_schur_normalized_log hP0 hP1 Y hblock
  exact h.2.trans (c1_nonlinear_trace_identity
    (Matrix.isHermitian_conjTranspose_mul_self (c1SchurFactor P0 P1 Y))).symm

theorem c1_schur_linear_trace {P0 : QMatrix I} {P1 : QMatrix J}
    (hP0 : P0.PosDef) (hP1 : P1.PosDef) (Y : Matrix J I ℂ) :
    Matrix.trace ((c1SchurFactor P0 P1 Y)ᴴ*c1SchurFactor P0 P1 Y)=
      Matrix.trace (Yᴴ*P1⁻¹*Y*P0⁻¹) := by
  let K0 : QMatrix I := c1InvSqrt P0
  let K1 : QMatrix J := c1InvSqrt P1
  have hK0 : K0ᴴ=K0 := (c1InvSqrt_isHermitian P0).eq
  have hK1 : K1ᴴ=K1 := (c1InvSqrt_isHermitian P1).eq
  have hs : (c1SchurFactor P0 P1 Y)ᴴ*c1SchurFactor P0 P1 Y=
      K0*Yᴴ*(K1*K1)*Y*K0 := by
    simp only [c1SchurFactor,Matrix.conjTranspose_mul,hK0,hK1,K0,K1,Matrix.mul_assoc]
  rw [hs,c1InvSqrt_sq hP1]
  calc
    Matrix.trace (K0*Yᴴ*P1⁻¹*Y*K0)=Matrix.trace ((Yᴴ*P1⁻¹*Y)*(K0*K0)) := by
      calc
        _ = Matrix.trace ((K0*(Yᴴ*P1⁻¹*Y))*K0) := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [Matrix.trace_mul_cycle K0 (Yᴴ*P1⁻¹*Y) K0,
            Matrix.trace_mul_comm (K0*K0) (Yᴴ*P1⁻¹*Y)]
    _ = _ := by rw [c1InvSqrt_sq hP0]

def c1NoiseKernel (w x : ℝ) : ℝ := Real.log (x+w)-Real.log x-w*(x+w)⁻¹

theorem c1NoiseKernel_intervalIntegrable {w T : ℝ} (hw : 0 ≤ w) (hT : 0 < T) :
    IntervalIntegrable (c1NoiseKernel w) MeasureTheory.volume 0 T := by
  by_cases hz : w=0
  · change IntervalIntegrable (fun x : ℝ => c1NoiseKernel w x) MeasureTheory.volume 0 T
    simpa only [hz,c1NoiseKernel,add_zero,zero_mul,sub_self,sub_zero] using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ))
        MeasureTheory.volume 0 T)
  have hp : 0 < w := lt_of_le_of_ne hw (Ne.symm hz)
  have hl : IntervalIntegrable Real.log MeasureTheory.volume 0 T :=
    intervalIntegral.intervalIntegrable_log'
  have hlw : IntervalIntegrable (fun x : ℝ => Real.log (x+w))
      MeasureTheory.volume 0 T :=
    (IntervalIntegrable.comp_add_right_iff (f := Real.log) (c := w)).2
      intervalIntegral.intervalIntegrable_log'
  have hinv : IntervalIntegrable (fun x : ℝ => (x+w)⁻¹)
      MeasureTheory.volume 0 T := by
    have hn (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) T) : x+w ≠ 0 := by
      have hx0 : 0 ≤ x := (by simpa only [Set.uIcc_of_le hT.le] using hx :
        x ∈ Set.Icc (0 : ℝ) T).1
      exact ne_of_gt (by linarith)
    exact ((continuous_id.add continuous_const :
      Continuous (fun x : ℝ => x+w)).continuousOn.inv₀ hn).intervalIntegrable
  exact (hlw.sub hl).sub (hinv.const_mul w)

theorem c1NoiseKernel_integral_le {w ε T : ℝ} (hw : 0 ≤ w)
    (hε : 0 < ε) (hT : ε ≤ T) :
    (∫ x in ε..T, c1NoiseKernel w x) ≤ w := by
  have hTp : 0 < T := hε.trans_le hT
  have hi := c1NoiseKernel_intervalIntegrable hw hTp
  have hn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) T)] c1NoiseKernel w := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    change 0 ≤ Real.log (x+w)-Real.log x-w*(x+w)⁻¹
    rw [← c1Nonlinear_resolvent_kernel hw hx.1]
    have ht := c1_resolvent_threshold_mem hw hx.1
    exact c1Nonlinear_nonneg ht.1 ht.2
  have hm := intervalIntegral.integral_mono_interval hε.le hT (le_refl T) hn hi
  by_cases hz : w=0
  · simpa only [hz,c1NoiseKernel,add_zero,zero_mul,sub_self,sub_zero,
      intervalIntegral.integral_zero] using hm
  have hp : 0 < w := lt_of_le_of_ne hw (Ne.symm hz)
  calc
    (∫ x in ε..T, c1NoiseKernel w x) ≤ ∫ x in 0..T, c1NoiseKernel w x := hm
    _ = T*Real.log (1+w/T) := c1_nonlinear_scalar_integral hp hTp
    _ ≤ w := (c1_nonlinear_scalar_primitive_bounds hw hTp).2

theorem c1_noise_spectral_intervalIntegrable {X : QMatrix I} (hX : X.PosSemidef)
    {ε T : ℝ} (hε : 0 < ε) (hT : ε ≤ T) :
    IntervalIntegrable (fun x : ℝ => ∑ i, c1NoiseKernel (hX.1.eigenvalues i) x)
      MeasureTheory.volume ε T := by
  have hi (i : I) : IntervalIntegrable (c1NoiseKernel (hX.1.eigenvalues i))
      MeasureTheory.volume ε T := by
    apply (c1NoiseKernel_intervalIntegrable (hX.eigenvalues_nonneg i) (hε.trans_le hT)).mono_set
    rw [Set.uIcc_of_le hT,Set.uIcc_of_le (hε.trans_le hT).le]
    exact Set.Icc_subset_Icc hε.le le_rfl
  convert IntervalIntegrable.sum Finset.univ (fun i _ => hi i) using 1
  funext x
  simp only [Finset.sum_apply]

theorem c1_noise_spectral_integral_bound {X : QMatrix I} (hX : X.PosSemidef)
    {ε T : ℝ} (hε : 0 < ε) (hT : ε ≤ T) :
    (∫ x in ε..T, ∑ i, c1NoiseKernel (hX.1.eigenvalues i) x) ≤ (Matrix.trace X).re := by
  have hi (i : I) : IntervalIntegrable (c1NoiseKernel (hX.1.eigenvalues i))
      MeasureTheory.volume ε T := by
    apply (c1NoiseKernel_intervalIntegrable (hX.eigenvalues_nonneg i) (hε.trans_le hT)).mono_set
    rw [Set.uIcc_of_le hT,Set.uIcc_of_le (hε.trans_le hT).le]
    exact Set.Icc_subset_Icc hε.le le_rfl
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i),
    QuantumProver.SuperchannelDiscrimination.Klein.trace_eq_sum_eigenvalues_re hX.1]
  exact Finset.sum_le_sum (fun i _ => c1NoiseKernel_integral_le (hX.eigenvalues_nonneg i) hε hT)

def c1BinaryLogCost (A : QMatrix I) (B : QMatrix J) (Z : Matrix J I ℂ) (x : ℝ) : ℝ :=
  (Matrix.trace (cfc Real.log (A*A+Zᴴ*Z+x • (1 : QMatrix I)))).re+
    (Matrix.trace (cfc Real.log (B*B+Z*Zᴴ+x • (1 : QMatrix J)))).re-
    (Matrix.trace (cfc Real.log
      (c1Binary A B Z*c1Binary A B Z+x • (1 : QMatrix (I ⊕ J))))).re

def c1BinaryLinearCost (A : QMatrix I) (B : QMatrix J) (Z : Matrix J I ℂ) (x : ℝ) : ℝ :=
  (Matrix.trace ((Z*A+B*Z)ᴴ*(B*B+Z*Zᴴ+x • (1 : QMatrix J))⁻¹*
    (Z*A+B*Z)*(A*A+Zᴴ*Z+x • (1 : QMatrix I))⁻¹)).re

theorem c1BinaryLogCost_intervalIntegrable {A : QMatrix I} {B : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (Z : Matrix J I ℂ) (a b : ℝ) :
    IntervalIntegrable (c1BinaryLogCost A B Z) MeasureTheory.volume a b := by
  have hD0 := (c1_hermitian_square_posSemidef hA).add (Matrix.posSemidef_conjTranspose_mul_self Z)
  have hD1 := (c1_hermitian_square_posSemidef hB).add (Matrix.posSemidef_self_mul_conjTranspose Z)
  have hH := c1Binary_square_posSemidef Z hA hB
  exact ((c1_trace_shifted_log_intervalIntegrable hD0.1 a b).add
    (c1_trace_shifted_log_intervalIntegrable hD1.1 a b)).sub
    (c1_trace_shifted_log_intervalIntegrable hH.1 a b)

theorem c1BinaryLinearCost_intervalIntegrable {A : QMatrix I} {B : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (Z : Matrix J I ℂ)
    {ε T : ℝ} (hε : 0 < ε) (hT : ε ≤ T) :
    IntervalIntegrable (c1BinaryLinearCost A B Z) MeasureTheory.volume ε T := by
  have hD0 := (c1_hermitian_square_posSemidef hA).add (Matrix.posSemidef_conjTranspose_mul_self Z)
  have hD1 := (c1_hermitian_square_posSemidef hB).add (Matrix.posSemidef_self_mul_conjTranspose Z)
  have hc0 := c1_psd_resolvent_continuousOn hD0 hε hT
  have hc1 := c1_psd_resolvent_continuousOn hD1 hε hT
  have hpair := hc0.prodMk hc1
  have h := (c1_metric_trace_continuous (Z*A+B*Z)).comp_continuousOn hpair
  exact h.intervalIntegrable

theorem c1BinaryLogCost_decomposition {A : QMatrix I} {B : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (Z : Matrix J I ℂ)
    {x : ℝ} (hx : 0 < x) :
    let P0 := A*A+Zᴴ*Z+x • (1 : QMatrix I)
    let P1 := B*B+Z*Zᴴ+x • (1 : QMatrix J)
    let S := c1SchurFactor P0 P1 (Z*A+B*Z)
    c1BinaryLogCost A B Z x=c1BinaryLinearCost A B Z x+
      (Matrix.trace (cfc c1Nonlinear (Sᴴ*S))).re := by
  let P0 : QMatrix I := A*A+Zᴴ*Z+x • (1 : QMatrix I)
  let P1 : QMatrix J := B*B+Z*Zᴴ+x • (1 : QMatrix J)
  have hp0 : P0.PosDef := c1_regularized_posDef
    ((c1_hermitian_square_posSemidef hA).add (Matrix.posSemidef_conjTranspose_mul_self Z)) hx
  have hp1 : P1.PosDef := c1_regularized_posDef
    ((c1_hermitian_square_posSemidef hB).add (Matrix.posSemidef_self_mul_conjTranspose Z)) hx
  have hp : (Matrix.fromBlocks P0 (Z*A+B*Z)ᴴ (Z*A+B*Z) P1).PosDef := by
    have h := c1_regularized_posDef (c1Binary_square_posSemidef Z hA hB) hx
    rw [c1_binary_square_regularized_blocks hA hB] at h
    exact h
  have h := c1_schur_cost_decomposition hp0 hp1 (Z*A+B*Z) hp
  dsimp only at h
  rw [c1_schur_linear_trace hp0 hp1] at h
  rw [← c1_binary_square_regularized_blocks hA hB] at h
  exact h.trans (add_comm _ _)

theorem c1_binary_noise_trace (Z : Matrix J I ℂ) :
    (Matrix.trace (c1Binary (0 : QMatrix I) (0 : QMatrix J) Z*
      c1Binary (0 : QMatrix I) (0 : QMatrix J) Z)).re=2*hsSq Z := by
  have hW := c1Binary_isHermitian Z Matrix.isHermitian_zero Matrix.isHermitian_zero
  calc
    _ = c1HsMass (c1Binary (0 : QMatrix I) (0 : QMatrix J) Z) := by
      simpa only [hW.eq] using c1_trace_gram (c1Binary (0 : QMatrix I) (0 : QMatrix J) Z)
    _ = 2*hsSq Z := by
      rw [c1Binary_hs_mass,← hsSq_eq_c1HsMass Z]
      simp [c1HsMass]

theorem c1_binary_log_integral_bound {A : QMatrix I} {B : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (Z : Matrix J I ℂ)
    (hu : 0 < hsSq Z) {ε T : ℝ} (hε : 0 < ε) (hT : ε ≤ T) :
    (∫ x in ε..T, c1BinaryLogCost A B Z x) ≤
      hsSq Z*Fcal ((Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re/hsSq Z)+4*hsSq Z := by
  let hW := c1_hermitian_square_posSemidef
    (c1Binary_isHermitian Z (Matrix.isHermitian_zero) (Matrix.isHermitian_zero))
  let g : ℝ → ℝ := fun x => ∑ j, c1NoiseKernel (hW.1.eigenvalues j) x
  have hiL := c1BinaryLogCost_intervalIntegrable hA hB Z ε T
  have hiJ := c1BinaryLinearCost_intervalIntegrable hA hB Z hε hT
  have hiG : IntervalIntegrable g MeasureTheory.volume ε T :=
    c1_noise_spectral_intervalIntegrable hW hε hT
  have hp (x : ℝ) (hx : x ∈ Set.Icc ε T) :
      c1BinaryLogCost A B Z x ≤ c1BinaryLinearCost A B Z x+g x := by
    have hx0 := hε.trans_le hx.1
    have hd := c1BinaryLogCost_decomposition hA hB Z hx0
    have hn := c1_binary_nonlinear_trace_bound hA hB Z hx0
    exact hd.trans_le (add_le_add le_rfl hn)
  have hm := intervalIntegral.integral_mono_on hT hiL (hiJ.add hiG) hp
  rw [intervalIntegral.integral_add hiJ hiG] at hm
  have hbJ := c1_binary_linear_resolvent_integral_bound hA hB Z hu hε hT
  have hbG := c1_noise_spectral_integral_bound hW hε hT
  rw [c1_binary_noise_trace Z] at hbG
  change (∫ x in ε..T, g x) ≤ 2*hsSq Z at hbG
  change (∫ x in ε..T, c1BinaryLinearCost A B Z x) ≤ _ at hbJ
  linarith

theorem c1_binary_log_integral_zero_bound {A : QMatrix I} {B : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (Z : Matrix J I ℂ)
    (hu : 0 < hsSq Z) {T : ℝ} (hT : 0 < T) :
    (∫ x in 0..T, c1BinaryLogCost A B Z x) ≤
      hsSq Z*Fcal ((Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re/hsSq Z)+4*hsSq Z := by
  have hc := intervalIntegral.continuous_primitive
    (c1BinaryLogCost_intervalIntegrable hA hB Z) T
  have hc' : Continuous (fun ε : ℝ => ∫ x in ε..T, c1BinaryLogCost A B Z x) := by
    convert hc.neg using 1
    funext ε
    exact intervalIntegral.integral_symm (f := c1BinaryLogCost A B Z)
      (μ := MeasureTheory.volume) T ε
  have hl : Tendsto (fun ε : ℝ => ∫ x in ε..T, c1BinaryLogCost A B Z x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x in 0..T, c1BinaryLogCost A B Z x)) :=
    hc'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hl
  have hp : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < ε := self_mem_nhdsWithin
  have ht : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), ε < T :=
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp,ht] with ε hε hεT
  exact c1_binary_log_integral_bound hA hB Z hu hε hεT.le

theorem c1_binary_pinched_square (A : QMatrix I) (B : QMatrix J) (Z : Matrix J I ℂ) :
    binaryPinch (c1Binary A B Z*c1Binary A B Z)=
      Matrix.fromBlocks (A*A+Zᴴ*Z) 0 0 (B*B+Z*Zᴴ) := by
  rw [c1Binary_square_blocks,binaryPinch_fromBlocks,add_comm (Z*Zᴴ) (B*B)]

theorem c1_trace_shifted_log_fromBlocks {D0 : QMatrix I} {D1 : QMatrix J}
    (hD0 : D0.IsHermitian) (hD1 : D1.IsHermitian) (x : ℝ) :
    (Matrix.trace (cfc Real.log
      (Matrix.fromBlocks D0 0 0 D1+x • (1 : QMatrix (I ⊕ J))))).re=
      (Matrix.trace (cfc Real.log (D0+x • (1 : QMatrix I)))).re+
      (Matrix.trace (cfc Real.log (D1+x • (1 : QMatrix J)))).re := by
  have hs : Matrix.fromBlocks D0 0 0 D1+x • (1 : QMatrix (I ⊕ J))=
      Matrix.fromBlocks (D0+x • (1 : QMatrix I)) 0 0
        (D1+x • (1 : QMatrix J)) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]
  rw [hs]
  change (Matrix.trace (cfc Real.log
      (QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock
        (D0+x • (1 : QMatrix I)) (D1+x • (1 : QMatrix J))))).re= _
  rw [QuantumProver.SuperchannelDiscrimination.FlaggedStates.cfc_flagBlock Real.log
      (hD0.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all x)))
      (hD1.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all x))),
    QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_trace,Complex.add_re]

theorem c1_binary_square_entropy_bound {A : QMatrix I} {B : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (Z : Matrix J I ℂ)
    (hu : 0 < hsSq Z) :
    binaryCoherenceNat (c1Binary A B Z*c1Binary A B Z) ≤
      hsSq Z*Fcal ((Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re/hsSq Z)+4*hsSq Z := by
  have hD0 := (c1_hermitian_square_posSemidef hA).add
    (Matrix.posSemidef_conjTranspose_mul_self Z)
  have hD1 := (c1_hermitian_square_posSemidef hB).add
    (Matrix.posSemidef_self_mul_conjTranspose Z)
  have hX := c1Binary_square_posSemidef Z hA hB
  have hY : (binaryPinch (c1Binary A B Z*c1Binary A B Z)).PosSemidef := by
    rw [c1_binary_pinched_square]
    exact QuantumProver.SuperchannelDiscrimination.FlaggedStates.flagBlock_posSemidef hD0 hD1
  have ht : (Matrix.trace (binaryPinch (c1Binary A B Z*c1Binary A B Z))).re=
      (Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re :=
    congrArg Complex.re (binaryPinch_trace _)
  have hl := c1_entropy_difference_integral_limit hX hY ht
  have hp (x : ℝ) :
      (Matrix.trace (cfc Real.log
        (binaryPinch (c1Binary A B Z*c1Binary A B Z)+
          x • (1 : QMatrix (I ⊕ J))))).re-
        (Matrix.trace (cfc Real.log
          (c1Binary A B Z*c1Binary A B Z+x • (1 : QMatrix (I ⊕ J))))).re=
        c1BinaryLogCost A B Z x := by
    rw [c1_binary_pinched_square,c1_trace_shifted_log_fromBlocks hD0.1 hD1.1]
    rfl
  simp only [hp] at hl
  change Tendsto (fun T : ℝ => ∫ x in 0..T, c1BinaryLogCost A B Z x)
    atTop (nhds (binaryCoherenceNat (c1Binary A B Z*c1Binary A B Z))) at hl
  apply le_of_tendsto hl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact c1_binary_log_integral_zero_bound hA hB Z hu hT

theorem c1_binary_square_entropy_bound_all_noise {A : QMatrix I} {B : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (Z : Matrix J I ℂ) :
    binaryCoherenceNat (c1Binary A B Z*c1Binary A B Z) ≤
      hsSq Z*Fcal ((Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re/hsSq Z)+4*hsSq Z := by
  by_cases hz : hsSq Z=0
  · rw [binaryCoherenceNat_square_zero_noise A B Z hz,hz]
    simp only [zero_mul,mul_zero,add_zero,le_refl]
  exact c1_binary_square_entropy_bound hA hB Z
    (lt_of_le_of_ne (hsSq_nonneg Z) (Ne.symm hz))

theorem c1_hermitian_square_entropy_bound {H : QMatrix (I ⊕ J)} (hH : H.IsHermitian) :
    binaryCoherenceNat (H*H) ≤
      hsSq (H.submatrix Sum.inr Sum.inl)*
        Fcal ((Matrix.trace (H*H)).re/hsSq (H.submatrix Sum.inr Sum.inl))+
      4*hsSq (H.submatrix Sum.inr Sum.inl) := by
  have h := c1_binary_square_entropy_bound_all_noise
    (hH.submatrix (Sum.inl : I → I ⊕ J))
    (hH.submatrix (Sum.inr : J → I ⊕ J))
    (H.submatrix Sum.inr Sum.inl)
  rw [← hermitian_eq_c1Binary hH] at h
  exact h

theorem c1CoshMoment_monotoneOn : MonotoneOn c1CoshMoment (Set.Ici 0) := by
  intro r hr s hs hrs
  have hj := c1CoshMoment_finite_jensen (R := s)
    (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => r)
    (fun _ => by norm_num) (by simp) (fun _ => hr)
    (by simpa using hrs)
  simpa using hj

theorem c1_Fcal_le_logCoth {m : ℝ} (hm : 2 ≤ m) : Fcal m ≤ c1LogCoth m := by
  have hp : 0 < m := by linarith
  have h1 : 1 < m := by linarith
  have hr : 0 ≤ (m-2)/4 := by positivity
  have hs : 0 ≤ (m-1)^2/(4*m) := by positivity
  have hrs : (m-2)/4 ≤ (m-1)^2/(4*m) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (by positivity : 0 < 4*m)).2
    nlinarith
  have hc := c1CoshMoment_monotoneOn hr hs hrs
  rw [c1CoshMoment_eq_Fcal hm] at hc
  calc
    Fcal m ≤ c1CoshMoment ((m-1)^2/(4*m)) := hc
    _ = c1LogCoth m := by
      have hpairs := c1CoshMoment_pair_gt (a := m) (b := 1) (by norm_num) h1
      simp only [mul_one,Real.log_one,sub_zero] at hpairs
      rw [hpairs,c1LogCoth_eq h1]
      ring

theorem c1_Fcal_uniform_log_bound {m : ℝ} (hm : 2 ≤ m) :
    Fcal m ≤ Real.log m+2*Real.log m/(m-1) := by
  exact (c1_Fcal_le_logCoth hm).trans_eq
    (c1LogCoth_decomposition (by linarith : 1 < m))

theorem c1_Fcal_log_add_two {m : ℝ} (hm : 2 ≤ m) : Fcal m ≤ Real.log m+2 :=
  (c1_Fcal_le_logCoth hm).trans (c1LogCoth_le_log_add_two (by linarith : 1 < m))

theorem c1_binary_square_entropy_uniform_remainder {A : QMatrix I} {B : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (Z : Matrix J I ℂ)
    (hu : 0 < hsSq Z) :
    let t := (Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re
    let u := hsSq Z
    binaryCoherenceNat (c1Binary A B Z*c1Binary A B Z) ≤
      u*Real.log (t/u)+4*u+2*u^2/(t-u)*Real.log (t/u) := by
  let t := (Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re
  let u := hsSq Z
  have ht : 2*u ≤ t := c1_two_noise_le_trace Z hA hB
  have htu : u < t := by dsimp only [u] at ht ⊢; linarith
  have hm : 2 ≤ t/u := (le_div_iff₀ hu).2 ht
  have hbase := c1_binary_square_entropy_bound hA hB Z hu
  have hmajor : u*Fcal (t/u)+4*u ≤
      u*(Real.log (t/u)+4+2*Real.log (t/u)/(t/u-1)) := by
    calc
      _ ≤ u*(Real.log (t/u)+2*Real.log (t/u)/(t/u-1))+4*u :=
        add_le_add (mul_le_mul_of_nonneg_left (c1_Fcal_uniform_log_bound hm) hu.le) le_rfl
      _ = _ := by ring
  exact (hbase.trans hmajor).trans_eq (c1_uniform_remainder_identity hu htu)

theorem c1_binary_square_entropy_log_bound {A : QMatrix I} {B : QMatrix J}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (Z : Matrix J I ℂ)
    (hu : 0 < hsSq Z) :
    let t := (Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re
    let u := hsSq Z
    binaryCoherenceNat (c1Binary A B Z*c1Binary A B Z) ≤ u*Real.log (t/u)+6*u := by
  let t := (Matrix.trace (c1Binary A B Z*c1Binary A B Z)).re
  let u := hsSq Z
  have ht : 2*u ≤ t := c1_two_noise_le_trace Z hA hB
  have hm : 2 ≤ t/u := (le_div_iff₀ hu).2 ht
  have hbase := c1_binary_square_entropy_bound hA hB Z hu
  have hmajor := mul_le_mul_of_nonneg_left (c1_Fcal_log_add_two hm) hu.le
  change u*Fcal (t/u) ≤ u*(Real.log (t/u)+2) at hmajor
  change binaryCoherenceNat (c1Binary A B Z*c1Binary A B Z) ≤
    u*Fcal (t/u)+4*u at hbase
  change binaryCoherenceNat (c1Binary A B Z*c1Binary A B Z) ≤ u*Real.log (t/u)+6*u
  linarith

end QuantumProver.DepolarizingSquashedEntanglement
