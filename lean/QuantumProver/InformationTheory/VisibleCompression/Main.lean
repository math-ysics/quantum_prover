import QuantumProver.InformationTheory.VisibleCompression.Definitions
import QuantumProver.InformationTheory.VisibleCompression.ScalarBounds
import QuantumProver.InformationTheory.VisibleCompression.ChoiChannel
import QuantumProver.InformationTheory.VisibleCompression.TracePairing
import QuantumProver.InformationTheory.VisibleCompression.D9Design

/-!
Operational compression lemmas and a strong converse for the finite
dimension-nine complement ensemble with free shared classical randomness.
-/

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open scoped ComplexStarModule

namespace VisibleCompression

universe u v w

namespace CPTP

variable {I : Type u} {B : Type v} [Fintype I] [Fintype B]

/-- Positivity follows from complete positivity at ancillary dimension one. -/
theorem map_positive (Φ : CPTP I B) {A : Matrix I I ℂ}
    (hA : A.PosSemidef) : (Φ.map A).PosSemidef := by
  let A' : Matrix (Fin 1 × I) (Fin 1 × I) ℂ :=
    A.submatrix Prod.snd Prod.snd
  have hA' : A'.PosSemidef := hA.submatrix Prod.snd
  have hΦ := Φ.completelyPositive 1 A' hA'
  have hsmall := hΦ.submatrix (fun b : B => ((0 : Fin 1), b))
  convert hsmall using 1
  ext b c
  rfl

theorem map_hermitian [DecidableEq I] [DecidableEq B] (Φ : CPTP I B)
    {A : Matrix I I ℂ} (hA : A.IsHermitian) : (Φ.map A).IsHermitian := by
  have hp := Φ.map_positive (Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg A))
  have hn := Φ.map_positive (Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg A))
  rw [← CFC.posPart_sub_negPart A hA.isSelfAdjoint, map_sub]
  exact hp.isHermitian.sub hn.isHermitian

/-- Positivity and complex linearity imply preservation of the adjoint. -/
theorem map_star [DecidableEq I] [DecidableEq B] (Φ : CPTP I B)
    (A : Matrix I I ℂ) : Φ.map (star A) = star (Φ.map A) := by
  have hr := Φ.map_hermitian (show (ℜ A : Matrix I I ℂ).IsHermitian from (ℜ A).2)
  have hi := Φ.map_hermitian (show (ℑ A : Matrix I I ℂ).IsHermitian from (ℑ A).2)
  calc
    Φ.map (star A) = Φ.map (star ((ℜ A : Matrix I I ℂ) + Complex.I • (ℑ A : Matrix I I ℂ))) := by
      rw [realPart_add_I_smul_imaginaryPart]
    _ = Φ.map (ℜ A : Matrix I I ℂ) - Complex.I • Φ.map (ℑ A : Matrix I I ℂ) := by
      simp [star_add, star_smul, (ℜ A).2.star_eq, (ℑ A).2.star_eq, sub_eq_add_neg]
    _ = star (Φ.map (ℜ A : Matrix I I ℂ) + Complex.I • Φ.map (ℑ A : Matrix I I ℂ)) := by
      simp [star_add, star_smul, hr.isSelfAdjoint.star_eq, hi.isSelfAdjoint.star_eq, sub_eq_add_neg]
    _ = star (Φ.map A) := by
      rw [← map_smul, ← map_add, realPart_add_I_smul_imaginaryPart]

/-- CPTP decoding maps every allowed message density operator to a state. -/
def onDensity (Φ : CPTP I B) (ρ : Density I) : Density B where
  mat := Φ.map ρ.mat
  positive := Φ.map_positive ρ.positive
  normalized := (Φ.tracePreserving _).trans ρ.normalized

end CPTP

section PartialTrace

variable {I : Type u} {B : Type v} {E : Type w}
  [Fintype I] [Fintype B] [Fintype E]

/-- Actual output partial trace, with no dimensional scaling. -/
def partialTraceLinearMap :
    Matrix (B × E) (B × E) ℂ →ₗ[ℂ] Matrix B B ℂ where
  toFun A b c := ∑ e, A (b, e) (c, e)
  map_add' A A' := by
    ext b c
    change (∑ e, (A + A') (b, e) (c, e)) =
      (∑ e, A (b, e) (c, e)) + ∑ e, A' (b, e) (c, e)
    simp only [Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' z A := by
    ext b c
    change (∑ e, (z • A) (b, e) (c, e)) = z * ∑ e, A (b, e) (c, e)
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

def CPTP.partialTrace : CPTP (B × E) B where
  map := partialTraceLinearMap
  completelyPositive k A hA := by
    have hs : (∑ e : E, A.submatrix
        (fun p : Fin k × B => (p.1, (p.2, e)))
        (fun p : Fin k × B => (p.1, (p.2, e)))).PosSemidef := by
      apply Matrix.posSemidef_sum
      intro e _
      exact hA.submatrix _
    convert hs using 1
    ext p q
    change (∑ e, A (p.1, (p.2, e)) (q.1, (q.2, e))) = _
    simp only [Matrix.sum_apply, Matrix.submatrix_apply]
  tracePreserving A := by
    change (∑ b, ∑ e, A (b, e) (b, e)) = A.trace
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

def CPTP.comp {C : Type*} [Fintype C] (Ψ : CPTP B C) (Φ : CPTP I B) : CPTP I C where
  map := Ψ.map.comp Φ.map
  completelyPositive k A hA := by
    have hp := Ψ.completelyPositive k (amplify Φ.map k A)
      (Φ.completelyPositive k A hA)
    convert hp using 1
    ext p q
    dsimp [amplify, LinearMap.comp_apply]
    congr 1
  tracePreserving A := (Ψ.tracePreserving _).trans (Φ.tracePreserving A)

/-- Indexed partial-swap contraction, valid for arbitrary complex matrices.
This is the marginal trace-product identity used before identifying a
decoder contraction with Choi purity. -/
theorem partialTrace_product_trace (X Y : Matrix (B × E) (B × E) ℂ) :
    ((partialTraceLinearMap X : Matrix B B ℂ) * partialTraceLinearMap Y).trace =
      ∑ u : B, ∑ v : B, ∑ z : E, ∑ w : E,
        X (u, z) (v, z) * Y (v, w) (u, w) := by
  change (∑ u, ∑ v, (∑ z, X (u, z) (v, z)) * (∑ w, Y (v, w) (u, w))) = _
  simp_rw [Fintype.sum_mul_sum]

end PartialTrace

namespace VisibleCode

variable {X : Type u} {B : Type v} {S : Type w}
  [Fintype X] [Fintype B] [Fintype S] {d : ℕ}

theorem branchOutput_positive (C : VisibleCode X B S d) (x : X) (s : S) :
    (C.branchOutput x s).PosSemidef :=
  (C.decode s).map_positive (C.encode x s).positive

theorem branchOutput_trace (C : VisibleCode X B S d) (x : X) (s : S) :
    (C.branchOutput x s).trace = 1 := by
  exact ((C.decode s).tracePreserving _).trans (C.encode x s).normalized

/-- The actual seed-averaged output is a positive operator. -/
theorem reproduced_positive (C : VisibleCode X B S d) (x : X) :
    (C.reproduced x).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro s _
  exact (C.branchOutput_positive x s).smul (Complex.zero_le_real.mpr (C.seed.nonneg s))

/-- Averaging a probability law preserves trace one. -/
theorem reproduced_trace (C : VisibleCode X B S d) (x : X) :
    (C.reproduced x).trace = 1 := by
  simp only [reproduced, Matrix.trace_sum, Matrix.trace_smul,
    C.branchOutput_trace, smul_eq_mul, mul_one]
  exact_mod_cast C.seed.normalized

def reproducedDensity (C : VisibleCode X B S d) (x : X) : Density B where
  mat := C.reproduced x
  positive := C.reproduced_positive x
  normalized := C.reproduced_trace x

end VisibleCode

section SupportScore

variable {X : Type u} {B : Type v} {S : Type w}
  [Fintype X] [Fintype B] [Fintype S]

theorem supportScore_sum (P : Matrix B B ℂ) (ρ : S → Matrix B B ℂ) :
    supportScore P (∑ s, ρ s) = ∑ s, supportScore P (ρ s) := by
  simp [supportScore, Finset.mul_sum, Matrix.trace_sum]

theorem supportScore_real_smul (P ρ : Matrix B B ℂ) (q : ℝ) :
    supportScore P ((q : ℂ) • ρ) = q * supportScore P ρ := by
  simp [supportScore, Matrix.mul_smul, Matrix.trace_smul]

/-- Exact seed averaging identity, before taking a trace norm. -/
theorem reproduced_supportScore {d : ℕ} (C : VisibleCode X B S d)
    (P : X → Matrix B B ℂ) (x : X) :
    supportScore (P x) (C.reproduced x) =
      ∑ s, C.seed.weight s * supportScore (P x) (C.branchOutput x s) := by
  rw [VisibleCode.reproduced, supportScore_sum]
  congr 1
  funext s
  exact supportScore_real_smul _ _ _

/-- Source-independent seeds allow the same source probability law in every
branch. This is an equality for the actual reproduced output, not an
assumption about errors of individual seeds. -/
theorem average_reproduced_supportScore {d : ℕ} (C : VisibleCode X B S d)
    (p : ProbWeights X) (P : X → Matrix B B ℂ) :
    averageSupportScore p P C.reproduced =
      ∑ s, C.seed.weight s * averageSupportScore p P (fun x => C.branchOutput x s) := by
  simp only [averageSupportScore, reproduced_supportScore, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- A uniform branch support bound persists for every finite independent seed
law. The quantum branch bound is an explicit premise and is not established
by this averaging lemma. -/
theorem average_reproduced_supportScore_le {d : ℕ} (C : VisibleCode X B S d)
    (p : ProbWeights X) (P : X → Matrix B B ℂ) (K : ℝ)
    (hbranch : ∀ s, averageSupportScore p P (fun x => C.branchOutput x s) ≤ K) :
    averageSupportScore p P C.reproduced ≤ K := by
  rw [average_reproduced_supportScore]
  calc
    ∑ s, C.seed.weight s * averageSupportScore p P (fun x => C.branchOutput x s)
        ≤ ∑ s, C.seed.weight s * K :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hbranch s) (C.seed.nonneg s))
    _ = K := by rw [← Finset.sum_mul, C.seed.normalized, one_mul]

end SupportScore

section IID

variable {X : Type u} [Fintype X] {D : ℕ}

theorem blockBasis_card (D n : ℕ) : Fintype.card (BlockBasis D n) = D ^ n := by
  simp [BlockBasis, Fintype.card_pi_const]

theorem iidWeight_nonneg (p : ProbWeights X) (n : ℕ) (x : BlockLabels X n) :
    0 ≤ iidWeight p n x :=
  Finset.prod_nonneg (fun t _ => p.nonneg (x t))

theorem iidWeight_normalized (p : ProbWeights X) (n : ℕ) :
    ∑ x : BlockLabels X n, iidWeight p n x = 1 := by
  unfold iidWeight
  rw [← Fintype.sum_pow, p.normalized, one_pow]

theorem iidWeight_pos (p : ProbWeights X) (hp : p.FullSupport)
    (n : ℕ) (x : BlockLabels X n) : 0 < iidWeight p n x :=
  Finset.prod_pos (fun t _ => hp (x t))

def iidDistribution (p : ProbWeights X) (n : ℕ) : ProbWeights (BlockLabels X n) where
  weight := iidWeight p n
  nonneg := iidWeight_nonneg p n
  normalized := iidWeight_normalized p n

theorem iidTarget_trace (W : X → Density (Fin D)) (n : ℕ) (x : BlockLabels X n) :
    (iidTarget W n x).trace = 1 := by
  change (∑ b : Fin n → Fin D, ∏ t, (W (x t)).mat (b t) (b t)) = 1
  rw [← Fintype.prod_sum (fun t (b : Fin D) => (W (x t)).mat b b)]
  apply Finset.prod_eq_one
  intro t _
  exact (W (x t)).normalized

/-- Positivity of the full tensor-product target is proved by repeated
Kronecker products, then restricting to the tensor-product basis. -/
theorem iidTarget_positive (W : X → Density (Fin D)) :
    ∀ (n : ℕ) (x : BlockLabels X n), (iidTarget W n x).PosSemidef := by
  intro n
  induction n with
  | zero =>
      intro x
      have hp := Matrix.posSemidef_vecMulVec_self_star
        (fun _ : BlockBasis D 0 => (1 : ℂ))
      convert hp using 1
      ext b c
      simp [iidTarget, Matrix.vecMulVec]
  | succ n ih =>
      intro x
      have hp := (W (x 0)).positive.kronecker (ih (fun t => x t.succ))
      have hs := hp.submatrix
        (fun b : BlockBasis D (n + 1) => (b 0, fun t : Fin n => b t.succ))
      convert hs using 1
      ext b c
      simp [iidTarget, Matrix.submatrix, Matrix.kronecker_apply,
        Fin.prod_univ_succ]

def iidState (W : X → Density (Fin D)) (n : ℕ) (x : BlockLabels X n) :
    Density (BlockBasis D n) where
  mat := iidTarget W n x
  positive := iidTarget_positive W n x
  normalized := iidTarget_trace W n x

end IID

section ErrorNonnegative

variable {X : Type u} {B : Type v} {S : Type w}
  [Fintype X] [Fintype B] [Fintype S] [DecidableEq B]

theorem traceNorm_nonneg (A : Matrix B B ℂ) : 0 ≤ traceNorm A :=
  (Complex.nonneg_iff.mp
    (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg A)).trace_nonneg).1

theorem blockError_nonneg {d : ℕ} (p : ProbWeights X)
    (target : X → Matrix B B ℂ) (C : VisibleCode X B S d) :
    0 ≤ blockError p target C := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (traceNorm_nonneg _))

theorem iidBlockError_nonneg {D : ℕ} (p : ProbWeights X)
    (W : X → Density (Fin D)) (n : ℕ) (C : BlockCode X D n) :
    0 ≤ iidBlockError p W n C := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact Finset.sum_nonneg
    (fun x _ => mul_nonneg (iidWeight_nonneg p n x) (traceNorm_nonneg _))

end ErrorNonnegative

section EffectScore

variable {B : Type v} [Fintype B] [DecidableEq B]

/-- Trace of a product of two positive matrices is real and nonnegative,
although the product itself need not be positive. -/
theorem positive_trace_mul_nonneg {P ρ : Matrix B B ℂ}
    (hP : P.PosSemidef) (hρ : ρ.PosSemidef) : 0 ≤ (P * ρ).trace.re := by
  have hs : (CFC.sqrt P).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)).isHermitian
  have htr := (hρ.conjTranspose_mul_mul_same (CFC.sqrt P)).trace_nonneg
  rw [hs.eq, Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self P hP.nonneg] at htr
  exact (Complex.nonneg_iff.mp htr).1

theorem effect_supportScore_nonneg {P : Matrix B B ℂ} (hP : P.PosSemidef)
    (ρ : Density B) : 0 ≤ supportScore P ρ.mat :=
  positive_trace_mul_nonneg hP ρ.positive

theorem effect_trace_mul_le_trace {P ρ : Matrix B B ℂ}
    (hPcomp : (1 - P).PosSemidef) (hρ : ρ.PosSemidef) :
    (P * ρ).trace.re ≤ ρ.trace.re := by
  have hc := positive_trace_mul_nonneg hPcomp hρ
  simp only [sub_mul, one_mul, Matrix.trace_sub, Complex.sub_re] at hc
  exact sub_nonneg.mp hc

theorem effect_supportScore_le_one {P : Matrix B B ℂ}
    (hPcomp : (1 - P).PosSemidef) (ρ : Density B) :
    supportScore P ρ.mat ≤ 1 := by
  have hc := positive_trace_mul_nonneg hPcomp ρ.positive
  simp only [sub_mul, one_mul, Matrix.trace_sub, ρ.normalized,
    Complex.sub_re, Complex.one_re] at hc
  exact sub_nonneg.mp hc

/-- The exact half-trace-norm effect bound for a traceless Hermitian matrix.
The positive and negative parts have equal trace; no external research result
or norm estimate is assumed. -/
theorem effect_traceless_bound {P A : Matrix B B ℂ}
    (hP : P.PosSemidef) (hPcomp : (1 - P).PosSemidef)
    (hA : A.IsHermitian) (htr : A.trace = 0) :
    |supportScore P A| ≤ (1 / 2) * traceNorm A := by
  have hpos : A⁺.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg A)
  have hneg : A⁻.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg A)
  have hdiff : A⁺.trace.re - A⁻.trace.re = 0 := by
    have he := congrArg (fun M : Matrix B B ℂ => M.trace.re)
      (CFC.posPart_sub_negPart A hA.isSelfAdjoint)
    simpa [Matrix.trace_sub, htr] using he
  have hsum : traceNorm A = A⁺.trace.re + A⁻.trace.re := by
    unfold traceNorm
    rw [← CFC.posPart_add_negPart A hA.isSelfAdjoint, Matrix.trace_add, Complex.add_re]
  have hsplit : supportScore P A = supportScore P A⁺ - supportScore P A⁻ := by
    nth_rw 1 [← CFC.posPart_sub_negPart A hA.isSelfAdjoint]
    simp [supportScore, mul_sub, Matrix.trace_sub]
  have hp0 := positive_trace_mul_nonneg hP hpos
  have hn0 := positive_trace_mul_nonneg hP hneg
  have hp1 := effect_trace_mul_le_trace hPcomp hpos
  have hn1 := effect_trace_mul_le_trace hPcomp hneg
  change 0 ≤ supportScore P A⁺ at hp0
  change 0 ≤ supportScore P A⁻ at hn0
  change supportScore P A⁺ ≤ A⁺.trace.re at hp1
  change supportScore P A⁻ ≤ A⁻.trace.re at hn1
  apply abs_le.mpr
  constructor <;> linarith

theorem effect_trace_distance {P : Matrix B B ℂ}
    (hP : P.PosSemidef) (hPcomp : (1 - P).PosSemidef) (ρ σ : Density B) :
    |supportScore P ρ.mat - supportScore P σ.mat| ≤
      (1 / 2) * traceNorm (ρ.mat - σ.mat) := by
  have hh := ρ.positive.isHermitian.sub σ.positive.isHermitian
  have ht : (ρ.mat - σ.mat).trace = 0 := by
    simp [Matrix.trace_sub, ρ.normalized, σ.normalized]
  simpa [supportScore, mul_sub, Matrix.trace_sub] using
    effect_traceless_bound hP hPcomp hh ht

end EffectScore

section ErrorBridge

variable {X : Type u} {B : Type v} {S : Type w}
  [Fintype X] [Fintype B] [Fintype S] [DecidableEq B] {d : ℕ}

/-- Testing the target support against the actual seed-averaged reproduced
state gives precisely the block-error lower bound. -/
theorem one_sub_blockError_le_supportScore (p : ProbWeights X)
    (target : X → Density B) (C : VisibleCode X B S d)
    (P : X → Matrix B B ℂ) (hP : ∀ x, (P x).PosSemidef)
    (hPcomp : ∀ x, (1 - P x).PosSemidef)
    (htarget : ∀ x, supportScore (P x) (target x).mat = 1) :
    1 - blockError p (fun x => (target x).mat) C ≤
      averageSupportScore p P C.reproduced := by
  have htest (x : X) :
      1 - supportScore (P x) (C.reproduced x) ≤
        (1 / 2) * traceNorm ((target x).mat - C.reproduced x) := by
    have hd := effect_trace_distance (hP x) (hPcomp x) (target x)
      (C.reproducedDensity x)
    rw [htarget x] at hd
    exact (le_abs_self _).trans hd
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (htest x) (p.nonneg x))
  have hrhs :
      (∑ x, p.weight x * ((1 / 2) * traceNorm ((target x).mat - C.reproduced x))) =
      blockError p (fun x => (target x).mat) C := by
    unfold blockError
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hlhs :
      (∑ x, p.weight x * (1 - supportScore (P x) (C.reproduced x))) =
      1 - averageSupportScore p P C.reproduced := by
    simp [averageSupportScore, mul_sub, Finset.sum_sub_distrib, p.normalized]
  rw [hrhs, hlhs] at hsum
  linarith

end ErrorBridge

section Purity

variable {B : Type v} [Fintype B] [DecidableEq B]

theorem trace_unitary_conjugate (U : unitary (Matrix B B ℂ))
    (A : Matrix B B ℂ) :
    (Unitary.conjStarAlgAut ℂ (Matrix B B ℂ) U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]

theorem trace_square_eq_sum_eigenvalues_sq {A : Matrix B B ℂ}
    (hA : A.IsHermitian) :
    (A * A).trace.re = ∑ i, hA.eigenvalues i ^ 2 := by
  conv_lhs => rw [hA.spectral_theorem, ← map_mul, trace_unitary_conjugate]
  simp [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Function.comp_def, pow_two]

/-- The input-dimension half of the Choi-purity bound follows from positivity
and trace alone. -/
theorem positive_purity_le_trace_sq {A : Matrix B B ℂ} (hA : A.PosSemidef) :
    (A * A).trace.re ≤ A.trace.re ^ 2 := by
  have ht := congrArg Complex.re hA.isHermitian.trace_eq_sum_eigenvalues
  change A.trace.re = (∑ i : B, (hA.isHermitian.eigenvalues i : ℂ)).re at ht
  simp only [Complex.re_sum, Complex.ofReal_re] at ht
  calc
    (A * A).trace.re = ∑ i, hA.isHermitian.eigenvalues i ^ 2 :=
      trace_square_eq_sum_eigenvalues_sq hA.isHermitian
    _ ≤ (∑ i, hA.isHermitian.eigenvalues i) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (fun i _ => hA.eigenvalues_nonneg i)
    _ = A.trace.re ^ 2 := by rw [ht]

end Purity

section EncoderSquare

variable {B : Type v} [Fintype B] [DecidableEq B]

theorem hermitian_square_trace_nonneg {A : Matrix B B ℂ} (hA : A.IsHermitian) :
    0 ≤ (A * A).trace.re := by
  have hp := Matrix.posSemidef_conjTranspose_mul_self A
  rw [hA.eq] at hp
  exact (Complex.nonneg_iff.mp hp.trace_nonneg).1

/-- Arbitrary mixed message states obey the second-moment score estimate.
The proof uses the positive square of A-b*rho, with b=Re Tr(A rho). -/
theorem hermitian_density_score_sq_le_purity {A : Matrix B B ℂ}
    (hA : A.IsHermitian) (ρ : Density B) :
    supportScore A ρ.mat ^ 2 ≤ (A * A).trace.re := by
  let b := supportScore A ρ.mat
  let H := A - (b : ℂ) • ρ.mat
  have hb : IsSelfAdjoint (b : ℂ) := by simp [isSelfAdjoint_iff]
  have hH : H.IsHermitian := hA.sub (ρ.positive.isHermitian.smul hb)
  have h0 := hermitian_square_trace_nonneg hH
  have hpair : (ρ.mat * A).trace.re = b := by
    rw [Matrix.trace_mul_comm]
    rfl
  have he : (H * H).trace.re =
      (A * A).trace.re - 2 * b ^ 2 + b ^ 2 * (ρ.mat * ρ.mat).trace.re := by
    dsimp [H]
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re]
    simp only [Complex.smul_re, smul_eq_mul]
    change (A * A).trace.re - b * (ρ.mat * A).trace.re -
      (b * b - b * b * (ρ.mat * ρ.mat).trace.re) = _
    rw [hpair]
    ring
  have hρ := positive_purity_le_trace_sq ρ.positive
  simp only [ρ.normalized, Complex.one_re, one_pow] at hρ
  have hbρ := mul_le_mul_of_nonneg_left hρ (sq_nonneg b)
  rw [he] at h0
  change b ^ 2 ≤ (A * A).trace.re
  nlinarith

end EncoderSquare

namespace CPTP

variable {I : Type u} {B : Type v} [Fintype I] [Fintype B]
  [DecidableEq I] [DecidableEq B]

theorem traceAdjoint_hermitian (Φ : CPTP I B) {P : Matrix B B ℂ}
    (hP : P.IsHermitian) : (traceAdjoint Φ.map P).IsHermitian := by
  change (traceAdjoint Φ.map P).conjTranspose = traceAdjoint Φ.map P
  ext i j
  change star ((P * Φ.map (Matrix.single i j 1)).trace) =
    (P * Φ.map (Matrix.single j i 1)).trace
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hP.eq,
    Matrix.trace_mul_comm]
  have hs : (Φ.map (Matrix.single i j 1)).conjTranspose = Φ.map (Matrix.single j i 1) := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one] using
      (Φ.map_star (Matrix.single i j 1)).symm
  rw [hs]

theorem traceAdjoint_supportScore (Φ : CPTP I B) (P : Matrix B B ℂ)
    (T : Matrix I I ℂ) :
    supportScore (traceAdjoint Φ.map P) T = supportScore P (Φ.map T) :=
  congrArg Complex.re (traceAdjoint_pairing Φ.map P T)

/-- The message state is an arbitrary density operator depending on the
entire visible label. No maximal-eigenvalue optimizer is needed. -/
theorem encoder_score_sq_le_traceAdjoint_purity (Φ : CPTP I B)
    {P : Matrix B B ℂ} (hP : P.IsHermitian) (ρ : Density I) :
    supportScore P (Φ.map ρ.mat) ^ 2 ≤
      (traceAdjoint Φ.map P * traceAdjoint Φ.map P).trace.re := by
  rw [← Φ.traceAdjoint_supportScore P ρ.mat]
  exact hermitian_density_score_sq_le_purity (Φ.traceAdjoint_hermitian hP) ρ

end CPTP

section ChannelPurity

variable {B : Type v} [Fintype B] [DecidableEq B] {d : ℕ}

theorem channelChoi_purity_le_input_dimension (Φ : CPTP (Fin d) B) :
    (channelChoi Φ * channelChoi Φ).trace.re ≤ (d : ℝ) ^ 2 := by
  have hp := positive_purity_le_trace_sq (channelChoi_posSemidef Φ)
  simpa only [channelChoi_trace, Complex.natCast_re] using hp

theorem channelChoi_purity_le_output_dimension (Φ : CPTP (Fin d) B) :
    (channelChoi Φ * channelChoi Φ).trace.re ≤ (d : ℝ) * Fintype.card B := by
  rw [trace_square_eq_sum_eigenvalues_sq (channelChoi_posSemidef Φ).isHermitian]
  simpa only [mul_comm] using channelChoi_sum_eigenvalues_sq_le_dimensions Φ

/-- Actual CPTP decoders obey both input- and output-dimension Choi bounds. -/
theorem channelChoi_purity_le_min_dimensions (Φ : CPTP (Fin d) B) :
    (channelChoi Φ * channelChoi Φ).trace.re ≤
      (d : ℝ) * min (d : ℝ) (Fintype.card B : ℝ) := by
  rcases le_total (d : ℝ) (Fintype.card B : ℝ) with h | h
  · rw [min_eq_left h]
    simpa only [pow_two] using channelChoi_purity_le_input_dimension Φ
  · rw [min_eq_right h]
    exact channelChoi_purity_le_output_dimension Φ

end ChannelPurity

section DecoderMoment

variable {X : Type u} {B : Type v} {S : Type w}
  [Fintype X] [Fintype B] [Fintype S] [DecidableEq B] {d : ℕ}

/-- Every actual visible encoder is controlled by the decoder trace-adjoint
second moment, with the given arbitrary source weights. -/
theorem branch_supportScore_sq_le_adjoint_moment (p : ProbWeights X)
    (P : X → Matrix B B ℂ) (hP : ∀ x, (P x).IsHermitian)
    (C : VisibleCode X B S d) (s : S) :
    averageSupportScore p P (fun x => C.branchOutput x s) ^ 2 ≤
      ∑ x, p.weight x *
        (traceAdjoint (C.decode s).map (P x) * traceAdjoint (C.decode s).map (P x)).trace.re := by
  calc
    averageSupportScore p P (fun x => C.branchOutput x s) ^ 2 ≤
        ∑ x, p.weight x * supportScore (P x) (C.branchOutput x s) ^ 2 :=
      weighted_average_sq_le_average_sq p.weight _ p.nonneg p.normalized
    _ ≤ ∑ x, p.weight x *
        (traceAdjoint (C.decode s).map (P x) * traceAdjoint (C.decode s).map (P x)).trace.re := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left
        ((C.decode s).encoder_score_sq_le_traceAdjoint_purity (hP x) (C.encode x s))
        (p.nonneg x)

end DecoderMoment

section PositivePartEffect

variable {B : Type v} [Fintype B] [DecidableEq B]

theorem hermitian_cfc_nonnegative {A : Matrix B B ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (hf : ∀ i, 0 ≤ f (hA.eigenvalues i)) :
    (hA.cfc f).PosSemidef := by
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply]
  apply (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
    (Unitary.isUnit_coe (U := hA.eigenvectorUnitary))).mpr
  exact Matrix.PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr (hf i))

theorem hermitian_cfc_mul {A : Matrix B B ℂ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc f * hA.cfc g = hA.cfc (fun t => f t * g t) := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp [Function.comp_def]

theorem hermitian_cfc_sub {A : Matrix B B ℂ} (hA : A.IsHermitian) (f g : ℝ → ℝ) :
    hA.cfc (fun t => f t - g t) = hA.cfc f - hA.cfc g := by
  unfold Matrix.IsHermitian.cfc
  rw [← map_sub]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Function.comp_def, hij]

theorem hermitian_cfc_one {A : Matrix B B ℂ} (hA : A.IsHermitian) :
    hA.cfc (fun _ => 1) = 1 := by
  simp [Matrix.IsHermitian.cfc, Function.comp_def]

theorem hermitian_cfc_id {A : Matrix B B ℂ} (hA : A.IsHermitian) :
    hA.cfc (fun t => t) = A := by
  simpa [Matrix.IsHermitian.cfc, Function.comp_def] using hA.spectral_theorem.symm

/-- The positive spectral support of a Hermitian matrix is an effect and
selects its positive part. This is an explicit spectral construction. -/
theorem exists_positive_part_effect {A : Matrix B B ℂ} (hA : A.IsHermitian) :
    ∃ E : Matrix B B ℂ, E.PosSemidef ∧ (1 - E).PosSemidef ∧ E * A = A⁺ := by
  let f : ℝ → ℝ := fun t => if 0 < t then 1 else 0
  let E := hA.cfc f
  have hE : E.PosSemidef := hermitian_cfc_nonnegative hA f (by
    intro i
    dsimp [f]
    split_ifs <;> norm_num)
  have hEc : (1 - E).PosSemidef := by
    have hc := hermitian_cfc_nonnegative hA (fun t => 1 - f t) (by
      intro i
      dsimp [f]
      split_ifs <;> norm_num)
    rw [hermitian_cfc_sub, hermitian_cfc_one] at hc
    exact hc
  refine ⟨E, hE, hEc, ?_⟩
  calc
    E * A = hA.cfc f * hA.cfc (fun t => t) := by rw [hermitian_cfc_id]
    _ = hA.cfc (fun t => f t * t) := hermitian_cfc_mul hA f _
    _ = A⁺ := by
      rw [CFC.posPart_def, cfcₙ_eq_cfc, hA.cfc_eq]
      congr 1
      funext t
      by_cases ht : 0 < t
      · simp [f, ht, _root_.posPart_def, max_eq_left ht.le]
      · simp [f, ht, _root_.posPart_def, max_eq_right (le_of_not_gt ht)]

/-- Trace distance between normalized states is at most one. The trace norm
bound is proved by the positive spectral support effect, rather than assumed
as a field of a code or a generic norm triangle axiom. -/
theorem traceNorm_density_sub_le_two (ρ σ : Density B) :
    traceNorm (ρ.mat - σ.mat) ≤ 2 := by
  let A := ρ.mat - σ.mat
  have hA : A.IsHermitian := ρ.positive.isHermitian.sub σ.positive.isHermitian
  have htr : A.trace = 0 := by simp [A, Matrix.trace_sub, ρ.normalized, σ.normalized]
  obtain ⟨E, hE, hEc, hEA⟩ := exists_positive_part_effect hA
  have he0 := effect_supportScore_nonneg hE σ
  have he1 := effect_supportScore_le_one hEc ρ
  have hp : A⁺.trace.re = supportScore E ρ.mat - supportScore E σ.mat := by
    rw [← hEA]
    simp [A, supportScore, mul_sub, Matrix.trace_sub]
  have hdiff : A⁺.trace.re - A⁻.trace.re = 0 := by
    have he := congrArg (fun M : Matrix B B ℂ => M.trace.re)
      (CFC.posPart_sub_negPart A hA.isSelfAdjoint)
    simpa [Matrix.trace_sub, htr] using he
  have hsum : traceNorm A = A⁺.trace.re + A⁻.trace.re := by
    unfold traceNorm
    rw [← CFC.posPart_add_negPart A hA.isSelfAdjoint, Matrix.trace_add, Complex.add_re]
  change traceNorm A ≤ 2
  linarith

end PositivePartEffect

section ErrorUpperBound

variable {X : Type u} {B : Type v} {S : Type w}
  [Fintype X] [Fintype B] [Fintype S] [DecidableEq B] {d : ℕ}

theorem blockError_le_one (p : ProbWeights X) (target : X → Density B)
    (C : VisibleCode X B S d) :
    blockError p (fun x => (target x).mat) C ≤ 1 := by
  calc
    blockError p (fun x => (target x).mat) C
        ≤ (1 / 2) * ∑ x, p.weight x * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left
        (traceNorm_density_sub_le_two (target x) (C.reproducedDensity x)) (p.nonneg x)
    _ = 1 := by rw [← Finset.sum_mul, p.normalized]; norm_num

theorem iidBlockError_le_one {D : ℕ} (p : ProbWeights X)
    (W : X → Density (Fin D)) (n : ℕ) (C : BlockCode X D n) :
    iidBlockError p W n C ≤ 1 :=
  blockError_le_one (iidDistribution p n) (iidState W n) C.code

end ErrorUpperBound

section ConditionalConverse

variable {X : Type u} {B : Type v} {S : Type w}
  [Fintype X] [Fintype B] [Fintype S] [DecidableEq B] {d : ℕ}

/-- Operational reduction with an explicit missing decoder-moment premise.
This is not the dimension-nine source theorem until that premise is derived
from the fixed finite ensemble and its iid moment. -/
theorem finite_code_bound_of_adjoint_moment (p : ProbWeights X)
    (target : X → Density B) (C : VisibleCode X B S d)
    (P : X → Matrix B B ℂ) (hP : ∀ x, (P x).PosSemidef)
    (hPcomp : ∀ x, (1 - P x).PosSemidef)
    (htarget : ∀ x, supportScore (P x) (target x).mat = 1) (n : ℕ)
    (hmoment : ∀ s,
      (∑ x, p.weight x *
        (traceAdjoint (C.decode s).map (P x) * traceAdjoint (C.decode s).map (P x)).trace.re) ≤
      Real.rpow (d : ℝ) (3 / 2) * decayD9 ^ n) :
    (1 - blockError p (fun x => (target x).mat) C) ^ 2 ≤
      Real.rpow (d : ℝ) (3 / 2) * decayD9 ^ n := by
  apply finite_seed_strong_converse C.seed.weight
    (fun s => averageSupportScore p P (fun x => C.branchOutput x s))
    (blockError p (fun x => (target x).mat) C) (d : ℝ) n
    C.seed.nonneg C.seed.normalized (blockError_le_one p target C)
  · rw [← average_reproduced_supportScore]
    exact one_sub_blockError_le_supportScore p target C P hP hPcomp htarget
  · intro s
    exact (branch_supportScore_sq_le_adjoint_moment p P
      (fun x => (hP x).isHermitian) C s).trans (hmoment s)

end ConditionalConverse

section ConditionalAsymptoticRate

variable {X : Type u} [Fintype X] {D : ℕ}

/-- A universal finite-code inequality gives the exact limsup-rate lower
bound for every actual vanishing-error code sequence, including sequences
with unbounded rates. The finite-code inequality remains an explicit premise. -/
theorem asymptoticRate_ge_of_finite_code_bound (p : ProbWeights X)
    (W : X → Density (Fin D)) (C : ∀ n, BlockCode X D n)
    (hvanish : VanishingError p W C)
    (hbound : ∀ n,
      (1 - iidBlockError p W n (C n)) ^ 2 ≤
        Real.rpow ((C n).messageDimension : ℝ) (3 / 2) * decayD9 ^ n) :
    (lowerRateD9 : EReal) ≤ asymptoticRate C := by
  let ε : ℕ → ℝ := fun n => iidBlockError p W n (C n)
  have hε : Filter.Tendsto ε Filter.atTop (nhds 0) := hvanish
  have hcorrection := finite_code_correction_tendsto_zero ε hε
  have hlimit : Filter.Tendsto
      (fun n => lowerRateD9 + ((4 / 3 : ℝ) * log2 (1 - ε n)) / (n : ℝ))
      Filter.atTop (nhds lowerRateD9) := by
    simpa using tendsto_const_nhds.add hcorrection
  have hevent : ∀ᶠ n in Filter.atTop, ε n < 1 :=
    hε.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  have hrates : ∀ᶠ n in Filter.atTop,
      ((lowerRateD9 + ((4 / 3 : ℝ) * log2 (1 - ε n)) / (n : ℝ) : ℝ) : EReal) ≤
        (blockRate (C n) : EReal) := by
    filter_upwards [hevent, Filter.eventually_gt_atTop (0 : ℕ)] with n he hn
    exact EReal.coe_le_coe (finite_code_rate_lower (ε n) ((C n).messageDimension : ℝ)
      n he (Nat.cast_pos.mpr (C n).code.messageDimension_pos) hn (hbound n))
  have hlimsup := (EReal.tendsto_coe.mpr hlimit).limsup_eq
  change (lowerRateD9 : EReal) ≤ Filter.limsup (fun n => (blockRate (C n) : EReal)) Filter.atTop
  rw [← hlimsup]
  exact Filter.limsup_le_limsup hrates

/-- The infimum is over exactly the operational code sequences in
Definitions. No bounded-rate or existence-of-an-optimal-code hypothesis is
added. This result is conditional on the all-code finite inequality. -/
theorem visibleRate_ge_of_finite_code_bound (p : ProbWeights X)
    (W : X → Density (Fin D))
    (hbound : ∀ (n : ℕ) (C : BlockCode X D n),
      (1 - iidBlockError p W n C) ^ 2 ≤
        Real.rpow (C.messageDimension : ℝ) (3 / 2) * decayD9 ^ n) :
    (lowerRateD9 : EReal) ≤ visibleRate p W := by
  unfold visibleRate
  apply le_sInf
  rintro r ⟨C, hvanish, hrate⟩
  rw [← hrate]
  exact asymptoticRate_ge_of_finite_code_bound p W C hvanish (fun n => hbound n (C n))

end ConditionalAsymptoticRate

section IIDSecondMoment

variable {X : Type u} [Fintype X] {D n : ℕ}

/-- Tensor support matrices use the fixed one-letter output basis. -/
def tensorSupportMatrix (P : X → Matrix (Fin D) (Fin D) ℂ)
    (n : ℕ) (x : BlockLabels X n) : Matrix (BlockBasis D n) (BlockBasis D n) ℂ :=
  fun b c => ∏ t, P (x t) (b t) (c t)

/-- Entry formula for swapping the two copies precisely at positions in T.
The two products retain the tensor factor order. -/
def partialSwapMatrix (D n : ℕ) (T : Finset (Fin n)) :
    Matrix (BlockBasis D n × BlockBasis D n) (BlockBasis D n × BlockBasis D n) ℂ :=
  fun r c =>
    (∏ t ∈ T, (1 : Matrix (Fin D) (Fin D) ℂ) (r.1 t) (c.2 t) *
      (1 : Matrix (Fin D) (Fin D) ℂ) (r.2 t) (c.1 t)) *
    (∏ t ∈ Tᶜ, (1 : Matrix (Fin D) (Fin D) ℂ) (r.1 t) (c.1 t) *
      (1 : Matrix (Fin D) (Fin D) ℂ) (r.2 t) (c.2 t))

theorem iid_complex_weight_sum_prod (p : ProbWeights X) (F : Fin n → X → ℂ) :
    (∑ x : BlockLabels X n, (iidWeight p n x : ℂ) * ∏ t, F t (x t)) =
      ∏ t, ∑ x : X, (p.weight x : ℂ) * F t x := by
  simp only [iidWeight, Complex.ofReal_prod]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun t x => (p.weight x : ℂ) * F t x)).symm

/-- The fixed finite source's one-copy entry moment tensorizes into the
precise iid partial-swap expansion. There is no global Haar assumption. -/
theorem tensorSupport_second_moment (p : ProbWeights X)
    (P : X → Matrix (Fin D) (Fin D) ℂ) (a b : ℂ)
    (hmoment : ∀ i j k l,
      (∑ x, (p.weight x : ℂ) * (P x i j * P x k l)) =
        a * (1 : Matrix (Fin D) (Fin D) ℂ) i j *
          (1 : Matrix (Fin D) (Fin D) ℂ) k l +
        b * (1 : Matrix (Fin D) (Fin D) ℂ) i l *
          (1 : Matrix (Fin D) (Fin D) ℂ) k j) :
    (∑ x : BlockLabels X n, (iidWeight p n x : ℂ) •
      Matrix.kronecker (tensorSupportMatrix P n x) (tensorSupportMatrix P n x)) =
      ∑ T : Finset (Fin n),
        (a ^ (n - T.card) * b ^ T.card) • partialSwapMatrix D n T := by
  ext r c
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change
    (∑ x : BlockLabels X n, (iidWeight p n x : ℂ) *
      ((∏ t, P (x t) (r.1 t) (c.1 t)) * (∏ t, P (x t) (r.2 t) (c.2 t)))) =
    ∑ T : Finset (Fin n), (a ^ (n - T.card) * b ^ T.card) * partialSwapMatrix D n T r c
  have hiid := iid_complex_weight_sum_prod p
    (fun t x => P x (r.1 t) (c.1 t) * P x (r.2 t) (c.2 t))
  simp_rw [hmoment] at hiid
  have hlhs :
      (∑ x : BlockLabels X n, (iidWeight p n x : ℂ) *
        ((∏ t, P (x t) (r.1 t) (c.1 t)) * (∏ t, P (x t) (r.2 t) (c.2 t)))) =
      ∏ t,
        (a * (1 : Matrix (Fin D) (Fin D) ℂ) (r.1 t) (c.1 t) *
          (1 : Matrix (Fin D) (Fin D) ℂ) (r.2 t) (c.2 t) +
        b * (1 : Matrix (Fin D) (Fin D) ℂ) (r.1 t) (c.2 t) *
          (1 : Matrix (Fin D) (Fin D) ℂ) (r.2 t) (c.1 t)) := by
    simpa only [Finset.prod_mul_distrib] using hiid
  rw [hlhs]
  have hexp := Fintype.prod_add
    (fun t : Fin n => b * (1 : Matrix (Fin D) (Fin D) ℂ) (r.1 t) (c.2 t) *
      (1 : Matrix (Fin D) (Fin D) ℂ) (r.2 t) (c.1 t))
    (fun t : Fin n => a * (1 : Matrix (Fin D) (Fin D) ℂ) (r.1 t) (c.1 t) *
      (1 : Matrix (Fin D) (Fin D) ℂ) (r.2 t) (c.2 t))
  calc
    _ = ∑ T : Finset (Fin n),
        (∏ t ∈ T, b * (1 : Matrix (Fin D) (Fin D) ℂ) (r.1 t) (c.2 t) *
          (1 : Matrix (Fin D) (Fin D) ℂ) (r.2 t) (c.1 t)) *
        (∏ t ∈ Tᶜ, a * (1 : Matrix (Fin D) (Fin D) ℂ) (r.1 t) (c.1 t) *
          (1 : Matrix (Fin D) (Fin D) ℂ) (r.2 t) (c.2 t)) := by
      simpa only [add_comm] using hexp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T _
      simp only [← mul_assoc, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_compl, Fintype.card_fin, partialSwapMatrix]
      ring

end IIDSecondMoment

section DecoderMarginals

variable {I : Type u} {B : Type v} {C : Type w}
  [Fintype I] [Fintype B] [Fintype C]

theorem trace_reindex (e : B ≃ C) (A : Matrix B B ℂ) :
    (Matrix.reindex e e A).trace = A.trace := by
  change (∑ c, A (e.symm c) (e.symm c)) = ∑ b, A b b
  exact e.symm.sum_comp (fun b => A b b)

/-- Changing the output basis preserves actual complete positivity and trace. -/
def CPTP.reindexOutput (Φ : CPTP I B) (e : B ≃ C) : CPTP I C where
  map := (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap.comp Φ.map
  completelyPositive k A hA := by
    have hp := (Φ.completelyPositive k A hA).submatrix
      (fun p : Fin k × C => (p.1, e.symm p.2))
    convert hp using 1
    ext p q
    rfl
  tracePreserving A := (trace_reindex e (Φ.map A)).trans (Φ.tracePreserving A)

variable (D n : ℕ) (T : Finset (Fin n))

abbrev retainedBasis := {t : Fin n // t ∈ T} → Fin D

abbrev discardedBasis := {t : Fin n // t ∉ T} → Fin D

def blockBasisSplit : BlockBasis D n ≃ retainedBasis D n T × discardedBasis D n T :=
  Equiv.piEquivPiSubtypeProd (fun t : Fin n => t ∈ T) (fun _ => Fin D)

theorem card_retainedBasis : Fintype.card (retainedBasis D n T) = D ^ T.card := by
  simp [retainedBasis, Fintype.card_pi]

/-- The marginal decoder is obtained by an output basis equivalence followed
by the actual CPTP partial trace. -/
def marginalDecoder {d : ℕ} (Φ : CPTP (Fin d) (BlockBasis D n)) :
    CPTP (Fin d) (retainedBasis D n T) :=
  CPTP.partialTrace.comp (Φ.reindexOutput (blockBasisSplit D n T))

theorem marginalDecoder_choi_purity {d : ℕ} (Φ : CPTP (Fin d) (BlockBasis D n)) :
    (channelChoi (marginalDecoder D n T Φ) *
      channelChoi (marginalDecoder D n T Φ)).trace.re ≤
      (d : ℝ) * min (d : ℝ) (D ^ T.card : ℕ) := by
  classical
  simpa only [card_retainedBasis] using
    channelChoi_purity_le_min_dimensions (marginalDecoder D n T Φ)

theorem identity_pi_entry {K : Type*} {J : Type*} [Fintype K] [DecidableEq J]
    (r c : K → J) :
    (∏ t, (1 : Matrix J J ℂ) (r t) (c t)) =
      (1 : Matrix (K → J) (K → J) ℂ) r c := by
  classical
  simp [Matrix.one_apply, Finset.prod_boole, funext_iff]

theorem retained_identity_product (r c : BlockBasis D n) :
    (∏ t ∈ T, (1 : Matrix (Fin D) (Fin D) ℂ) (r t) (c t)) =
      (1 : Matrix (retainedBasis D n T) (retainedBasis D n T) ℂ)
        ((blockBasisSplit D n T r).1) ((blockBasisSplit D n T c).1) := by
  classical
  rw [← Finset.prod_coe_sort]
  exact identity_pi_entry (fun t : T => r t) (fun t : T => c t)

theorem discarded_identity_product (r c : BlockBasis D n) :
    (∏ t ∈ Tᶜ, (1 : Matrix (Fin D) (Fin D) ℂ) (r t) (c t)) =
      (1 : Matrix (discardedBasis D n T) (discardedBasis D n T) ℂ)
        ((blockBasisSplit D n T r).2) ((blockBasisSplit D n T c).2) := by
  classical
  simp [Matrix.one_apply, Finset.prod_boole, funext_iff,
    discardedBasis, blockBasisSplit, Subtype.forall, Finset.mem_compl]

theorem partialSwapMatrix_entry (r c : BlockBasis D n × BlockBasis D n) :
    partialSwapMatrix D n T r c =
      (1 : Matrix (retainedBasis D n T) (retainedBasis D n T) ℂ)
        (blockBasisSplit D n T r.1).1 (blockBasisSplit D n T c.2).1 *
      (1 : Matrix (retainedBasis D n T) (retainedBasis D n T) ℂ)
        (blockBasisSplit D n T r.2).1 (blockBasisSplit D n T c.1).1 *
      (1 : Matrix (discardedBasis D n T) (discardedBasis D n T) ℂ)
        (blockBasisSplit D n T r.1).2 (blockBasisSplit D n T c.1).2 *
      (1 : Matrix (discardedBasis D n T) (discardedBasis D n T) ℂ)
        (blockBasisSplit D n T r.2).2 (blockBasisSplit D n T c.2).2 := by
  simp only [partialSwapMatrix, Finset.prod_mul_distrib]
  rw [retained_identity_product D n T r.1 c.2,
    retained_identity_product D n T r.2 c.1,
    discarded_identity_product D n T r.1 c.1,
    discarded_identity_product D n T r.2 c.2]
  ring

variable {R : Type*} {E : Type*} [Fintype R] [Fintype E]
  [DecidableEq R] [DecidableEq E]

def partialSwapOnProduct : Matrix ((R × E) × (R × E)) ((R × E) × (R × E)) ℂ :=
  fun r c =>
    (1 : Matrix R R ℂ) r.1.1 c.2.1 * (1 : Matrix R R ℂ) r.2.1 c.1.1 *
    (1 : Matrix E E ℂ) r.1.2 c.1.2 * (1 : Matrix E E ℂ) r.2.2 c.2.2

theorem partialSwapOnProduct_trace (X Y : Matrix (R × E) (R × E) ℂ) :
    (Matrix.kronecker X Y * partialSwapOnProduct).trace =
      ((partialTraceLinearMap X : Matrix R R ℂ) * partialTraceLinearMap Y).trace := by
  rw [partialTrace_product_trace]
  change (∑ r : (R × E) × (R × E), ∑ c : (R × E) × (R × E),
    (X r.1 c.1 * Y r.2 c.2) * partialSwapOnProduct c r) = _
  simp only [Fintype.sum_prod_type, partialSwapOnProduct]
  simp only [Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change (∑ u : R, ∑ z : E, ∑ v : R, ∑ w : E,
    X (u, z) (v, z) * Y (v, w) (u, w)) =
    ∑ u : R, ∑ v : R, ∑ z : E, ∑ w : E,
      X (u, z) (v, z) * Y (v, w) (u, w)
  apply Finset.sum_congr rfl
  intro r _
  exact Finset.sum_comm

theorem partialSwap_reindex :
    Matrix.reindex ((blockBasisSplit D n T).prodCongr (blockBasisSplit D n T))
      ((blockBasisSplit D n T).prodCongr (blockBasisSplit D n T))
      (partialSwapMatrix D n T) = partialSwapOnProduct := by
  classical
  ext r c
  change partialSwapMatrix D n T
      ((blockBasisSplit D n T).symm r.1, (blockBasisSplit D n T).symm r.2)
      ((blockBasisSplit D n T).symm c.1, (blockBasisSplit D n T).symm c.2) = _
  rw [partialSwapMatrix_entry]
  change
    (if (blockBasisSplit D n T ((blockBasisSplit D n T).symm r.1)).1 =
        (blockBasisSplit D n T ((blockBasisSplit D n T).symm c.2)).1 then (1 : ℂ) else 0) *
    (if (blockBasisSplit D n T ((blockBasisSplit D n T).symm r.2)).1 =
        (blockBasisSplit D n T ((blockBasisSplit D n T).symm c.1)).1 then (1 : ℂ) else 0) *
    (if (blockBasisSplit D n T ((blockBasisSplit D n T).symm r.1)).2 =
        (blockBasisSplit D n T ((blockBasisSplit D n T).symm c.1)).2 then (1 : ℂ) else 0) *
    (if (blockBasisSplit D n T ((blockBasisSplit D n T).symm r.2)).2 =
        (blockBasisSplit D n T ((blockBasisSplit D n T).symm c.2)).2 then (1 : ℂ) else 0) = _
  simp only [Equiv.apply_symm_apply]
  rfl

/-- Each actual iid partial swap contracts to the two output marginal
matrices, with ordinary complex trace and no normalization correction. -/
theorem partialSwap_trace_contraction
    (X Y : Matrix (BlockBasis D n) (BlockBasis D n) ℂ) :
    (Matrix.kronecker X Y * partialSwapMatrix D n T).trace =
      ((partialTraceLinearMap (Matrix.reindex (blockBasisSplit D n T)
          (blockBasisSplit D n T) X) :
          Matrix (retainedBasis D n T) (retainedBasis D n T) ℂ) *
        partialTraceLinearMap (Matrix.reindex (blockBasisSplit D n T)
          (blockBasisSplit D n T) Y)).trace := by
  classical
  let e := blockBasisSplit D n T
  have h := trace_reindex (e.prodCongr e)
    (Matrix.kronecker X Y * partialSwapMatrix D n T)
  have hm :
      Matrix.reindex (e.prodCongr e) (e.prodCongr e)
          (Matrix.kronecker X Y * partialSwapMatrix D n T) =
        Matrix.reindex (e.prodCongr e) (e.prodCongr e) (Matrix.kronecker X Y) *
          Matrix.reindex (e.prodCongr e) (e.prodCongr e) (partialSwapMatrix D n T) :=
    (Matrix.reindexRingEquiv ℂ (e.prodCongr e)).map_mul _ _
  rw [hm] at h
  have hk : Matrix.reindex (e.prodCongr e) (e.prodCongr e) (Matrix.kronecker X Y) =
      Matrix.kronecker (Matrix.reindex e e X) (Matrix.reindex e e Y) :=
    (Matrix.kroneckerMap_reindex (fun x y : ℂ => x * y) e e e e X Y).symm
  rw [hk, partialSwap_reindex] at h
  exact h.symm.trans (partialSwapOnProduct_trace (Matrix.reindex e e X) (Matrix.reindex e e Y))

end DecoderMarginals

section DecoderMoment

variable {I : Type u} {B : Type v} [Fintype I] [Fintype B] [DecidableEq I]

/-- The ordinary matrix-unit two-copy decoder contraction is linear in
the source moment. It is not a bound imposed as a field of the decoder. -/
def decoderMomentLinearMap (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix B B ℂ) :
    Matrix (B × B) (B × B) ℂ →ₗ[ℂ] ℂ where
  toFun H := ∑ i, ∑ j,
    (Matrix.kronecker (Φ (Matrix.single i j 1))
      (Φ (Matrix.single j i 1)) * H).trace
  map_add' H K := by
    simp only [Matrix.mul_add, Matrix.trace_add, Finset.sum_add_distrib]
  map_smul' z H := by
    simp only [Matrix.mul_smul, Matrix.trace_smul, ← Finset.smul_sum, RingHom.id_apply]

theorem decoderMoment_kronecker (Φ : Matrix I I ℂ →ₗ[ℂ] Matrix B B ℂ)
    (P : Matrix B B ℂ) :
    decoderMomentLinearMap Φ (Matrix.kronecker P P) =
      (traceAdjoint Φ P * traceAdjoint Φ P).trace := by
  rw [traceAdjoint_square]
  change (∑ i, ∑ j,
    (Matrix.kronecker (Φ (Matrix.single i j 1)) (Φ (Matrix.single j i 1)) *
      Matrix.kronecker P P).trace) = _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hm := Matrix.mul_kronecker_mul (Φ (Matrix.single i j 1)) P
    (Φ (Matrix.single j i 1)) P
  calc
    _ = (Matrix.kronecker (Φ (Matrix.single i j 1) * P)
        (Φ (Matrix.single j i 1) * P)).trace := congrArg Matrix.trace hm.symm
    _ = (Φ (Matrix.single i j 1) * P).trace *
        (Φ (Matrix.single j i 1) * P).trace := Matrix.trace_kronecker _ _
    _ = _ := by
      rw [
        Matrix.trace_mul_comm (Φ (Matrix.single i j 1)) P,
        Matrix.trace_mul_comm (Φ (Matrix.single j i 1)) P]

variable {X : Type w} [Fintype X] {D n d : ℕ}

theorem decoderMoment_partialSwap (Φ : CPTP (Fin d) (BlockBasis D n))
    (T : Finset (Fin n)) :
    decoderMomentLinearMap Φ.map (partialSwapMatrix D n T) =
      (channelChoi (marginalDecoder D n T Φ) *
        channelChoi (marginalDecoder D n T Φ)).trace := by
  change (∑ i, ∑ j,
    (Matrix.kronecker (Φ.map (Matrix.single i j 1))
      (Φ.map (Matrix.single j i 1)) * partialSwapMatrix D n T).trace) = _
  simp_rw [partialSwap_trace_contraction]
  change (∑ i, ∑ j,
    ((marginalDecoder D n T Φ).map (Matrix.single i j 1) *
      (marginalDecoder D n T Φ).map (Matrix.single j i 1)).trace) = _
  exact (trace_choi_square
    (fun i j => (marginalDecoder D n T Φ).map (Matrix.single i j 1))).symm

/-- Exact iid decoder adjoint moment, expressed as a sum of ordinary
unnormalized Choi purities of its actual retained-output marginal channels. -/
theorem traceAdjoint_iid_moment_eq (p : ProbWeights X)
    (P : X → Matrix (Fin D) (Fin D) ℂ) (a b : ℂ)
    (hmoment : ∀ i j k l,
      (∑ x, (p.weight x : ℂ) * (P x i j * P x k l)) =
        a * (1 : Matrix (Fin D) (Fin D) ℂ) i j *
          (1 : Matrix (Fin D) (Fin D) ℂ) k l +
        b * (1 : Matrix (Fin D) (Fin D) ℂ) i l *
          (1 : Matrix (Fin D) (Fin D) ℂ) k j)
    (Φ : CPTP (Fin d) (BlockBasis D n)) :
    (∑ x : BlockLabels X n, (iidWeight p n x : ℂ) *
      (traceAdjoint Φ.map (tensorSupportMatrix P n x) *
        traceAdjoint Φ.map (tensorSupportMatrix P n x)).trace) =
      ∑ T : Finset (Fin n), (a ^ (n - T.card) * b ^ T.card) *
        (channelChoi (marginalDecoder D n T Φ) *
          channelChoi (marginalDecoder D n T Φ)).trace := by
  have h := congrArg (decoderMomentLinearMap Φ.map)
    (tensorSupport_second_moment p P a b hmoment (n := n))
  simpa only [map_sum, map_smul, smul_eq_mul,
    decoderMoment_kronecker, decoderMoment_partialSwap] using h

theorem traceAdjoint_iid_real_moment_eq (p : ProbWeights X)
    (P : X → Matrix (Fin D) (Fin D) ℂ) (a b : ℝ)
    (hmoment : ∀ i j k l,
      (∑ x, (p.weight x : ℂ) * (P x i j * P x k l)) =
        (a : ℂ) * (1 : Matrix (Fin D) (Fin D) ℂ) i j *
          (1 : Matrix (Fin D) (Fin D) ℂ) k l +
        (b : ℂ) * (1 : Matrix (Fin D) (Fin D) ℂ) i l *
          (1 : Matrix (Fin D) (Fin D) ℂ) k j)
    (Φ : CPTP (Fin d) (BlockBasis D n)) :
    (∑ x : BlockLabels X n, iidWeight p n x *
      (traceAdjoint Φ.map (tensorSupportMatrix P n x) *
        traceAdjoint Φ.map (tensorSupportMatrix P n x)).trace.re) =
      ∑ T : Finset (Fin n), (a ^ (n - T.card) * b ^ T.card) *
        (channelChoi (marginalDecoder D n T Φ) *
          channelChoi (marginalDecoder D n T Φ)).trace.re := by
  have h := congrArg Complex.re (traceAdjoint_iid_moment_eq p P (a : ℂ) (b : ℂ) hmoment Φ)
  simpa only [← Complex.ofReal_pow, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
    ← Complex.ofReal_mul] using h

/-- A dimension-nine one-copy source entry moment implies the actual decoder
moment bound for every blocklength and arbitrary CPTP decoder. -/
theorem d9_traceAdjoint_iid_moment_bound (p : ProbWeights X)
    (P : X → Matrix (Fin 9) (Fin 9) ℂ)
    (hmoment : ∀ i j k l,
      (∑ x, (p.weight x : ℂ) * (P x i j * P x k l)) =
        ((71 / 90 : ℝ) : ℂ) * (1 : Matrix (Fin 9) (Fin 9) ℂ) i j *
          (1 : Matrix (Fin 9) (Fin 9) ℂ) k l +
        ((1 / 90 : ℝ) : ℂ) * (1 : Matrix (Fin 9) (Fin 9) ℂ) i l *
          (1 : Matrix (Fin 9) (Fin 9) ℂ) k j)
    (Φ : CPTP (Fin d) (BlockBasis 9 n)) (hd : 0 < d) :
    (∑ x : BlockLabels X n, iidWeight p n x *
      (traceAdjoint Φ.map (tensorSupportMatrix P n x) *
        traceAdjoint Φ.map (tensorSupportMatrix P n x)).trace.re) ≤
      Real.rpow (d : ℝ) (3 / 2) * decayD9 ^ n := by
  rw [traceAdjoint_iid_real_moment_eq p P (71 / 90) (1 / 90) hmoment Φ]
  apply d9_subset_purity_sum_bound (d : ℝ) n _ (Nat.cast_pos.mpr hd)
  intro T
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using marginalDecoder_choi_purity 9 n T Φ

end DecoderMoment

section TensorSupportTests

variable {X : Type u} [Fintype X] {D n : ℕ}

theorem tensorSupport_hermitian (P : X → Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ x, (P x).IsHermitian) (x : BlockLabels X n) :
    (tensorSupportMatrix P n x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro b c
  change star (∏ t, P (x t) (c t) (b t)) = ∏ t, P (x t) (b t) (c t)
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro t _
  exact (hP (x t)).apply (b t) (c t)

theorem tensorSupport_mul (P Q : X → Matrix (Fin D) (Fin D) ℂ)
    (x : BlockLabels X n) :
    tensorSupportMatrix (fun x => P x * Q x) n x =
      tensorSupportMatrix P n x * tensorSupportMatrix Q n x := by
  ext b c
  change (∏ t, ∑ j, P (x t) (b t) j * Q (x t) j (c t)) =
    ∑ f : BlockBasis D n,
      (∏ t, P (x t) (b t) (f t)) * (∏ t, Q (x t) (f t) (c t))
  simpa only [Finset.prod_mul_distrib] using
    Fintype.prod_sum (fun t j => P (x t) (b t) j * Q (x t) j (c t))

theorem tensorSupport_idempotent (P : X → Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ x, P x * P x = P x) (x : BlockLabels X n) :
    tensorSupportMatrix P n x * tensorSupportMatrix P n x = tensorSupportMatrix P n x := by
  rw [← tensorSupport_mul]
  congr 1
  funext x
  exact hP x

theorem tensorSupport_effect (P : X → Matrix (Fin D) (Fin D) ℂ)
    (hherm : ∀ x, (P x).IsHermitian) (hidem : ∀ x, P x * P x = P x)
    (x : BlockLabels X n) :
    (tensorSupportMatrix P n x).PosSemidef ∧
      (1 - tensorSupportMatrix P n x).PosSemidef := by
  classical
  have hh := tensorSupport_hermitian P hherm x
  have hi := tensorSupport_idempotent P hidem x
  constructor
  · have h := Matrix.posSemidef_conjTranspose_mul_self (tensorSupportMatrix P n x)
    rwa [hh.eq, hi] at h
  · have hh' := Matrix.isHermitian_one.sub hh
    have hi' : (1 - tensorSupportMatrix P n x) * (1 - tensorSupportMatrix P n x) =
        1 - tensorSupportMatrix P n x := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hi]
      abel
    have h := Matrix.posSemidef_conjTranspose_mul_self (1 - tensorSupportMatrix P n x)
    rwa [hh'.eq, hi'] at h

theorem tensorSupport_signal_score_one (P : X → Matrix (Fin D) (Fin D) ℂ)
    (W : X → Density (Fin D)) (hPW : ∀ x, P x * (W x).mat = (W x).mat)
    (x : BlockLabels X n) : supportScore (tensorSupportMatrix P n x) (iidTarget W n x) = 1 := by
  have h : tensorSupportMatrix P n x * iidTarget W n x = iidTarget W n x := by
    calc
      _ = tensorSupportMatrix (fun x => P x * (W x).mat) n x :=
        (tensorSupport_mul P (fun x => (W x).mat) x).symm
      _ = tensorSupportMatrix (fun x => (W x).mat) n x := by
        congr 1
        funext x
        exact hPW x
      _ = _ := rfl
  change (tensorSupportMatrix P n x * iidTarget W n x).trace.re = 1
  rw [h, iidTarget_trace]
  rfl

/-- The decoder-bound premise of the earlier operational bridge is now
derived from the genuine one-copy source moment and CPTP properties. -/
theorem d9_finite_code_bound_of_entry_moment (p : ProbWeights X)
    (P : X → Matrix (Fin 9) (Fin 9) ℂ) (W : X → Density (Fin 9))
    (hherm : ∀ x, (P x).IsHermitian) (hidem : ∀ x, P x * P x = P x)
    (hPW : ∀ x, P x * (W x).mat = (W x).mat)
    (hmoment : ∀ i j k l,
      (∑ x, (p.weight x : ℂ) * (P x i j * P x k l)) =
        ((71 / 90 : ℝ) : ℂ) * (1 : Matrix (Fin 9) (Fin 9) ℂ) i j *
          (1 : Matrix (Fin 9) (Fin 9) ℂ) k l +
        ((1 / 90 : ℝ) : ℂ) * (1 : Matrix (Fin 9) (Fin 9) ℂ) i l *
          (1 : Matrix (Fin 9) (Fin 9) ℂ) k j)
    (n : ℕ) (C : BlockCode X 9 n) :
    (1 - iidBlockError p W n C) ^ 2 ≤
      Real.rpow (C.messageDimension : ℝ) (3 / 2) * decayD9 ^ n := by
  classical
  exact finite_code_bound_of_adjoint_moment (iidDistribution p n) (iidState W n)
    C.code (tensorSupportMatrix P n)
    (fun x => (tensorSupport_effect P hherm hidem x).1)
    (fun x => (tensorSupport_effect P hherm hidem x).2)
    (fun x => tensorSupport_signal_score_one P W hPW x) n
    (fun s => d9_traceAdjoint_iid_moment_bound p P hmoment (C.code.decode s)
      C.code.messageDimension_pos)

theorem d9_visibleRate_ge_of_entry_moment (p : ProbWeights X)
    (P : X → Matrix (Fin 9) (Fin 9) ℂ) (W : X → Density (Fin 9))
    (hherm : ∀ x, (P x).IsHermitian) (hidem : ∀ x, P x * P x = P x)
    (hPW : ∀ x, P x * (W x).mat = (W x).mat)
    (hmoment : ∀ i j k l,
      (∑ x, (p.weight x : ℂ) * (P x i j * P x k l)) =
        ((71 / 90 : ℝ) : ℂ) * (1 : Matrix (Fin 9) (Fin 9) ℂ) i j *
          (1 : Matrix (Fin 9) (Fin 9) ℂ) k l +
        ((1 / 90 : ℝ) : ℂ) * (1 : Matrix (Fin 9) (Fin 9) ℂ) i l *
          (1 : Matrix (Fin 9) (Fin 9) ℂ) k j) :
    (lowerRateD9 : EReal) ≤ visibleRate p W :=
  visibleRate_ge_of_finite_code_bound p W
    (d9_finite_code_bound_of_entry_moment p P W hherm hidem hPW hmoment)

end TensorSupportTests

namespace D9

theorem P_second_moment_real_cast (i j k l : Fin 9) :
    (∑ x, (p.weight x : ℂ) * (P x i j * P x k l)) =
      ((71 / 90 : ℝ) : ℂ) * (1 : Matrix (Fin 9) (Fin 9) ℂ) i j *
        (1 : Matrix (Fin 9) (Fin 9) ℂ) k l +
      ((1 / 90 : ℝ) : ℂ) * (1 : Matrix (Fin 9) (Fin 9) ℂ) i l *
        (1 : Matrix (Fin 9) (Fin 9) ℂ) k j := by
  simpa using P_second_moment i j k l

/-- The concrete finite source satisfies the converse for every operational
code, with no source-moment or decoder-bound assumption in the statement. -/
theorem finite_code_strong_converse (n : ℕ) (C : BlockCode Label 9 n) :
    (1 - iidBlockError p W n C) ^ 2 ≤
      Real.rpow (C.messageDimension : ℝ) (3 / 2) * (37 / 45 : ℝ) ^ n := by
  simpa only [decayD9] using d9_finite_code_bound_of_entry_moment p P W
    P_hermitian P_idempotent W_support P_second_moment_real_cast n C

/-- Lower bound on the exact operational infimum, over all vanishing-error
visible codes with arbitrary independent finite shared seeds. -/
theorem operational_rate_lower : (lowerRateD9 : EReal) ≤ visibleRate p W :=
  d9_visibleRate_ge_of_entry_moment p P W
    P_hermitian P_idempotent W_support P_second_moment_real_cast

theorem holevoBits_lt_visibleRate : (holevoBits : EReal) < visibleRate p W := by
  rw [holevoBits_eq_holevoD9]
  exact lt_of_lt_of_le (EReal.coe_lt_coe holevoD9_lt_lowerRateD9) operational_rate_lower

/-- Every vanishing-error sequence has a strict rate gap over the actual
spectral Holevo quantity of the explicit finite ensemble. -/
theorem vanishing_code_rate_gap (C : ∀ n, BlockCode Label 9 n)
    (hvanish : VanishingError p W C) : (holevoBits : EReal) < asymptoticRate C := by
  have hrate := asymptoticRate_ge_of_finite_code_bound p W C hvanish
    (fun n => by simpa only [decayD9] using finite_code_strong_converse n (C n))
  rw [holevoBits_eq_holevoD9]
  exact lt_of_lt_of_le (EReal.coe_lt_coe holevoD9_lt_lowerRateD9) hrate

end D9

/-- A fully explicit finite full-support witness for the claimed Holevo-rate
equality's failure in the operational free-shared-randomness model. -/
theorem visible_compression_free_randomness_counterexample :
    Fintype.card D9.Label = 6570 ∧ D9.p.FullSupport ∧
      D9.holevoBits = log2 (9 / 8) ∧
      (D9.holevoBits : EReal) < visibleRate D9.p D9.W :=
  ⟨D9.label_card, D9.p_fullSupport, D9.holevoBits_eq, D9.holevoBits_lt_visibleRate⟩

end VisibleCompression
