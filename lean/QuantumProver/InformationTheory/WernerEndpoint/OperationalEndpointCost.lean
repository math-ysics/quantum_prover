import QuantumProver.InformationTheory.WernerEndpoint.AntisymmetricStates
import QuantumProver.InformationTheory.WernerEndpoint.SchattenSupport
import QuantumProver.InformationTheory.SuperchannelDiscrimination.EffectPerturbation
import QuantumProver.InformationTheory.SuperchannelDiscrimination.PetzMoments
import QuantumProver.LinearAlgebra.LocalInstrumentMarginals
import QuantumProver.InformationTheory.WernerEndpoint.AntisymmetricEnsembleCost

noncomputable section

namespace QuantumProver.WernerEndpoint.OperationalEndpointCost

open scoped BigOperators Kronecker ComplexOrder

structure OneWayLocalInstrument (H A₀ B₀ A₁ B₁ : Type*)
    [Fintype H] [Fintype A₀] [Fintype B₀] [Fintype A₁] [Fintype B₁]
    [DecidableEq A₀] [DecidableEq B₀] where
  alice : H → Matrix A₁ A₀ ℂ
  bob : H → Matrix B₁ B₀ ℂ
  alice_complete : ∑ h, (alice h).conjTranspose * alice h = 1
  bob_isometry : ∀ h, (bob h).conjTranspose * bob h = 1

namespace OneWayLocalInstrument

variable {H A₀ B₀ A₁ B₁ : Type*}
  [Fintype H] [Fintype A₀] [Fintype B₀] [Fintype A₁] [Fintype B₁]
  [DecidableEq A₀] [DecidableEq B₀]

def branch (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁) (h : H) :
    Matrix (A₁ × B₁) (A₀ × B₀) ℂ := I.alice h ⊗ₖ I.bob h

def apply (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁)
    (ρ : Matrix (A₀ × B₀) (A₀ × B₀) ℂ) : Matrix (A₁ × B₁) (A₁ × B₁) ℂ :=
  ∑ h, I.branch h * ρ * (I.branch h).conjTranspose

theorem branch_complete (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁) :
    ∑ h, (I.branch h).conjTranspose * I.branch h = 1 := by
  classical
  simp_rw [branch, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, I.bob_isometry]
  have hs : (∑ h, ((I.alice h).conjTranspose * I.alice h) ⊗ₖ
      (1 : Matrix B₀ B₀ ℂ)) =
      (∑ h, (I.alice h).conjTranspose * I.alice h) ⊗ₖ (1 : Matrix B₀ B₀ ℂ) := by
    ext ab cd
    simp [Matrix.kronecker_apply, Matrix.sum_apply, Finset.sum_mul]
  rw [hs, I.alice_complete, Matrix.one_kronecker_one]

theorem apply_trace (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁)
    (ρ : Matrix (A₀ × B₀) (A₀ × B₀) ℂ) :
    Matrix.trace (I.apply ρ) = Matrix.trace ρ := by
  classical
  unfold apply
  rw [Matrix.trace_sum]
  have hc : (∑ h, Matrix.trace (I.branch h * ρ * (I.branch h).conjTranspose)) =
      ∑ h, Matrix.trace ((I.branch h).conjTranspose * I.branch h * ρ) := by
    apply Finset.sum_congr rfl
    intro h _
    exact Matrix.trace_mul_cycle _ _ _
  rw [hc]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, I.branch_complete, Matrix.one_mul]

theorem apply_posSemidef (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁)
    (ρ : Matrix (A₀ × B₀) (A₀ × B₀) ℂ) (hρ : ρ.PosSemidef) :
    (I.apply ρ).PosSemidef := by
  exact Matrix.posSemidef_sum Finset.univ
    (fun h _ => hρ.mul_mul_conjTranspose_same (I.branch h))

theorem apply_pureDensity (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁)
    (v : A₀ × B₀ → ℂ) :
    I.apply (pureDensity v) = ∑ h, pureDensity ((I.branch h).mulVec v) := by
  unfold apply pureDensity
  simp_rw [sandwich_crossDensity]

end OneWayLocalInstrument

def bellVector : Fin 2 × Fin 2 → ℂ := fun pq =>
  wedgeScale * (if pq.1 = pq.2 then 1 else 0)

theorem bellVector_normSq : vectorNormSq bellVector = 1 := by
  have ht : ((vectorNormSq bellVector : ℝ) : ℂ) = 1 := by
    rw [← pureDensity_trace]
    norm_num [Matrix.trace, Matrix.diag, pureDensity, crossDensity, bellVector,
      Fintype.sum_prod_type, Fin.sum_univ_two, wedgeScale_star, wedgeScale_square]
  exact_mod_cast ht

theorem bellVector_reducedLeft :
    reducedLeft (fun p q : Fin 2 => bellVector (p, q)) =
      (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    norm_num [reducedLeft, crossLeft, bellVector, Fin.sum_univ_two,
      Matrix.smul_apply, Matrix.one_apply, wedgeScale_star, wedgeScale_square]

def aliceEmbedding {d : ℕ} (e : Edge d) : Matrix (Fin d) (Fin 2) ℂ :=
  fun i q => if q = 0 then (if i = e.val.1 then 1 else 0)
    else (if i = e.val.2 then 1 else 0)

def bobEmbedding {d : ℕ} (e : Edge d) : Matrix (Fin d) (Fin 2) ℂ :=
  fun i q => if q = 0 then (if i = e.val.2 then 1 else 0)
    else -(if i = e.val.1 then 1 else 0)

theorem aliceEmbedding_isometry {d : ℕ} (e : Edge d) :
    (aliceEmbedding e).conjTranspose * aliceEmbedding e = 1 := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [aliceEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, mul_ite, ite_mul, ne_of_lt e.property,
      (ne_of_lt e.property).symm]

theorem bobEmbedding_isometry {d : ℕ} (e : Edge d) :
    (bobEmbedding e).conjTranspose * bobEmbedding e = 1 := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [bobEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, mul_ite, ite_mul, ne_of_lt e.property,
      (ne_of_lt e.property).symm]

theorem local_embedding_bell {d : ℕ} (e : Edge d) :
    (aliceEmbedding e ⊗ₖ bobEmbedding e).mulVec bellVector =
      fun ab => wedgeInclusion d ab e := by
  ext ab
  rcases ab with ⟨i, j⟩
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.kronecker_apply, aliceEmbedding, bobEmbedding,
    bellVector, wedgeInclusion, mul_ite, ite_mul]
  split_ifs <;> simp_all

def edgeAmplitude (d : ℕ) : ℂ := (Real.sqrt ((Fintype.card (Edge d) : ℝ)⁻¹) : ℂ)

@[simp] theorem edgeAmplitude_star (d : ℕ) : star (edgeAmplitude d) = edgeAmplitude d := by
  simp [edgeAmplitude]

theorem edgeAmplitude_square (d : ℕ) :
    edgeAmplitude d * edgeAmplitude d = (Fintype.card (Edge d) : ℂ)⁻¹ := by
  have h := Real.sq_sqrt (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (Edge d))))
  simpa [edgeAmplitude, pow_two] using congrArg (fun r : ℝ => (r : ℂ)) h

theorem edgeAmplitude_normSq (d : ℕ) :
    Complex.normSq (edgeAmplitude d) = (Fintype.card (Edge d) : ℝ)⁻¹ := by
  simp [edgeAmplitude, Complex.normSq_ofReal, Real.sq_sqrt]

theorem edge_card_pos {d : ℕ} (hd : 2 ≤ d) : 0 < Fintype.card (Edge d) := by
  let e : Edge d := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by norm_num⟩
  exact Fintype.card_pos_iff.mpr ⟨e⟩

theorem weighted_alice_gram {d : ℕ} (e : Edge d) :
    (edgeAmplitude d • aliceEmbedding e).conjTranspose *
        (edgeAmplitude d • aliceEmbedding e) =
      (Fintype.card (Edge d) : ℂ)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    aliceEmbedding_isometry, smul_smul, edgeAmplitude_star, edgeAmplitude_square]

def uniformEdgeInstrument (d : ℕ) (hd : 2 ≤ d) :
    OneWayLocalInstrument (Edge d) (Fin 2) (Fin 2) (Fin d) (Fin d) where
  alice := fun e => edgeAmplitude d • aliceEmbedding e
  bob := bobEmbedding
  alice_complete := by
    simp_rw [weighted_alice_gram]
    have hn : (Fintype.card (Edge d) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (edge_card_pos hd))
    ext p q
    simp [Matrix.sum_apply, Matrix.smul_apply, nsmul_eq_mul, hn]
  bob_isometry := bobEmbedding_isometry

theorem uniformEdgeInstrument_branch_bell (d : ℕ) (hd : 2 ≤ d) (e : Edge d) :
    ((uniformEdgeInstrument d hd).branch e).mulVec bellVector =
      edgeAmplitude d • (fun ab => wedgeInclusion d ab e) := by
  unfold OneWayLocalInstrument.branch uniformEdgeInstrument
  rw [Matrix.smul_kronecker, Matrix.smul_mulVec, local_embedding_bell]

theorem sum_wedge_column_density (d : ℕ) :
    (∑ e : Edge d, pureDensity (fun ab => wedgeInclusion d ab e)) = wedgeProjector d := by
  ext ab cd
  simp [wedgeProjector, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, pureDensity, crossDensity]

theorem uniformEdgeInstrument_bell_output (d : ℕ) (hd : 2 ≤ d) :
    (uniformEdgeInstrument d hd).apply (pureDensity bellVector) =
      (Fintype.card (Edge d) : ℂ)⁻¹ • wedgeProjector d := by
  rw [OneWayLocalInstrument.apply_pureDensity]
  simp_rw [uniformEdgeInstrument_branch_bell, matrix_pureDensity_scalar,
    edgeAmplitude_normSq]
  simp only [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [← Finset.smul_sum, sum_wedge_column_density]

theorem uniformEdgeInstrument_bell_output_trace (d : ℕ) (hd : 2 ≤ d) :
    Matrix.trace ((uniformEdgeInstrument d hd).apply (pureDensity bellVector)) = 1 := by
  rw [OneWayLocalInstrument.apply_trace, pureDensity_trace, bellVector_normSq]
  norm_num

theorem uniformEdgeInstrument_bell_output_posSemidef (d : ℕ) (hd : 2 ≤ d) :
    ((uniformEdgeInstrument d hd).apply (pureDensity bellVector)).PosSemidef :=
  (uniformEdgeInstrument d hd).apply_posSemidef _ (pureDensity_posSemidef bellVector)

end QuantumProver.WernerEndpoint.OperationalEndpointCost

namespace QuantumProver.WernerEndpoint.OperationalEndpointCost

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open QuantumProver.SuperchannelDiscrimination

theorem traceNorm_eq_schattenOne {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) :
    EffectPerturbation.traceNorm M = SchattenSupport.schattenOne M := by
  rw [EffectPerturbation.traceNorm, CFC.abs]
  change (CFC.sqrt (M.conjTranspose * M)).trace.re = SchattenSupport.schattenOne M
  rw [CFC.sqrt_eq_cfc,
    cfc_nnreal_eq_real _ _ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg,
    PetzMoments.trace_cfc_eq_sum _ (SchattenSupport.gramHermitian M)]
  simp only [SchattenSupport.schattenOne, SchattenSupport.singularValue, Real.sqrt,
    Complex.re_sum, Complex.ofReal_re]

theorem projector_isEffect {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (hPH : P.IsHermitian) (hP2 : P * P = P) :
    FlaggedStates.IsEffect P := by
  have hp : P.PosSemidef := by
    simpa only [hPH.eq, hP2] using Matrix.posSemidef_conjTranspose_mul_self P
  have hCH : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hPH
  have hC2 : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP2]; abel
  have hc : (1 - P).PosSemidef := by
    have hh := Matrix.posSemidef_conjTranspose_mul_self (1 - P)
    rw [hCH.eq, hC2] at hh
    exact hh
  exact ⟨hp, hc⟩

theorem effect_expectation_schatten_distance {I : Type*} [Fintype I] [DecidableEq I]
    (P ρ σ : Matrix I I ℂ) (hP : FlaggedStates.IsEffect P)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (htrace : ρ.trace = σ.trace) :
    |(P * ρ).trace.re - (P * σ).trace.re| ≤
      SchattenSupport.schattenOne (ρ - σ) / 2 := by
  have hz : (ρ - σ).trace = 0 := by rw [Matrix.trace_sub, htrace, sub_self]
  have h := EffectPerturbation.effect_traceless_bound hP (hρ.sub hσ) hz
  rw [traceNorm_eq_schattenOne] at h
  simpa only [EffectPerturbation.effectValue, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re, one_div, div_eq_mul_inv, mul_comm, one_mul] using h

def partialTraceLeftLinearMap {A B : Type*} [Fintype B] :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix A A ℂ where
  toFun := partialTraceLeft
  map_add' := by
    intro ρ σ
    ext i j
    simp [partialTraceLeft, Finset.sum_add_distrib]
  map_smul' := by
    intro z ρ
    ext i j
    simp [partialTraceLeft, Finset.mul_sum]

def partialTraceRightLinearMap {A B : Type*} [Fintype A] :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix B B ℂ where
  toFun := partialTraceRight
  map_add' := by
    intro ρ σ
    ext i j
    simp [partialTraceRight, Finset.sum_add_distrib]
  map_smul' := by
    intro z ρ
    ext i j
    simp [partialTraceRight, Finset.mul_sum]

theorem partialTraceLeft_schatten_distance_le {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (ρ σ : Matrix (A × B) (A × B) ℂ) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    SchattenSupport.schattenOne (partialTraceLeft ρ - partialTraceLeft σ) ≤
      SchattenSupport.schattenOne (ρ - σ) := by
  have h := EffectPerturbation.traceNorm_difference_contracts
    partialTraceLeftLinearMap (fun P hP => partialTraceLeft_posSemidef P hP)
    partialTraceLeft_trace hρ hσ
  simpa only [partialTraceLeftLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    traceNorm_eq_schattenOne] using h

theorem partialTraceRight_schatten_distance_le {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (ρ σ : Matrix (A × B) (A × B) ℂ) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    SchattenSupport.schattenOne (partialTraceRight ρ - partialTraceRight σ) ≤
      SchattenSupport.schattenOne (ρ - σ) := by
  have h := EffectPerturbation.traceNorm_difference_contracts
    partialTraceRightLinearMap (fun P hP => partialTraceRight_posSemidef P hP)
    partialTraceRight_trace hρ hσ
  simpa only [partialTraceRightLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    traceNorm_eq_schattenOne] using h

def finiteKrausApply {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
    (K : H → Matrix O I ℂ) (ρ : Matrix I I ℂ) : Matrix O O ℂ :=
  ∑ h, K h * ρ * (K h).conjTranspose

theorem finiteKrausApply_posSemidef {H I O : Type*}
    [Fintype H] [Fintype I] [Fintype O]
    (K : H → Matrix O I ℂ) (ρ : Matrix I I ℂ) (hρ : ρ.PosSemidef) :
    (finiteKrausApply K ρ).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ
    (fun h _ => hρ.mul_mul_conjTranspose_same (K h))

theorem finiteKrausApply_trace {H I O : Type*}
    [Fintype H] [Fintype I] [Fintype O] [DecidableEq I]
    (K : H → Matrix O I ℂ) (hK : ∑ h, (K h).conjTranspose * K h = 1)
    (ρ : Matrix I I ℂ) : (finiteKrausApply K ρ).trace = ρ.trace := by
  classical
  unfold finiteKrausApply
  rw [Matrix.trace_sum]
  have hc : (∑ h, (K h * ρ * (K h).conjTranspose).trace) =
      ∑ h, ((K h).conjTranspose * K h * ρ).trace := by
    apply Finset.sum_congr rfl
    intro h _
    exact Matrix.trace_mul_cycle _ _ _
  rw [hc, ← Matrix.trace_sum, ← Matrix.sum_mul, hK, Matrix.one_mul]

inductive FiniteLocalProtocol (c d : ℕ) : ℕ → ℕ → Type
  | terminal {a b : ℕ}
      (LA : Matrix (Fin c) (Fin a) ℂ) (LB : Matrix (Fin d) (Fin b) ℂ)
      (hLA : LA.conjTranspose * LA = 1) (hLB : LB.conjTranspose * LB = 1) :
      FiniteLocalProtocol c d a b
  | alice {a b a' h z : ℕ}
      (K : Fin h → Fin z → Matrix (Fin a') (Fin a) ℂ)
      (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1)
      (next : Fin h → FiniteLocalProtocol c d a' b) :
      FiniteLocalProtocol c d a b
  | bob {a b b' h z : ℕ}
      (K : Fin h → Fin z → Matrix (Fin b') (Fin b) ℂ)
      (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1)
      (next : Fin h → FiniteLocalProtocol c d a b') :
      FiniteLocalProtocol c d a b

namespace FiniteLocalProtocol

def apply {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ :=
  match T with
  | .terminal LA LB _ _ => (LA ⊗ₖ LB) * ρ * (LA ⊗ₖ LB).conjTranspose
  | .alice K _ next => ∑ j, (next j).apply
      (∑ k, (K j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * ρ *
        (K j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose)
  | .bob K _ next => ∑ j, (next j).apply
      (∑ k, ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j k) * ρ *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j k).conjTranspose)

theorem alice_joint_complete {a b a' h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin a') (Fin a) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1) :
    (∑ j, ∑ k,
      (K j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)).conjTranspose *
        (K j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))) = 1 := by
  simp_rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hs : (∑ j, ∑ k, ((K j k).conjTranspose * K j k) ⊗ₖ
      (1 : Matrix (Fin b) (Fin b) ℂ)) =
      (∑ j, ∑ k, (K j k).conjTranspose * K j k) ⊗ₖ
        (1 : Matrix (Fin b) (Fin b) ℂ) := by
    ext ab xy
    simp [Matrix.kronecker_apply, Matrix.sum_apply, Finset.sum_mul]
  rw [hs, hK, Matrix.one_kronecker_one]

theorem bob_joint_complete {a b b' h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin b') (Fin b) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1) :
    (∑ j, ∑ k,
      ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j k).conjTranspose *
        ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j k)) = 1 := by
  simp_rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have hs : (∑ j, ∑ k, (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ
      ((K j k).conjTranspose * K j k)) =
      (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ
        (∑ j, ∑ k, (K j k).conjTranspose * K j k) := by
    ext ab xy
    simp [Matrix.kronecker_apply, Matrix.sum_apply, Finset.mul_sum]
  rw [hs, hK, Matrix.one_kronecker_one]

theorem apply_posSemidef {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hρ : ρ.PosSemidef) :
    (T.apply ρ).PosSemidef := by
  induction T with
  | terminal LA LB hLA hLB =>
    exact hρ.mul_mul_conjTranspose_same (LA ⊗ₖ LB)
  | alice K hK next ih =>
    apply Matrix.posSemidef_sum Finset.univ
    intro j _
    apply ih j
    exact Matrix.posSemidef_sum Finset.univ
      (fun k _ => hρ.mul_mul_conjTranspose_same (K j k ⊗ₖ 1))
  | bob K hK next ih =>
    apply Matrix.posSemidef_sum Finset.univ
    intro j _
    apply ih j
    exact Matrix.posSemidef_sum Finset.univ
      (fun k _ => hρ.mul_mul_conjTranspose_same (1 ⊗ₖ K j k))

theorem apply_trace {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (T.apply ρ).trace = ρ.trace := by
  induction T with
  | terminal LA LB hLA hLB =>
    have hc : (LA ⊗ₖ LB).conjTranspose * (LA ⊗ₖ LB) = 1 := by
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
        hLA, hLB, Matrix.one_kronecker_one]
    change ((LA ⊗ₖ LB) * ρ * (LA ⊗ₖ LB).conjTranspose).trace = ρ.trace
    rw [Matrix.trace_mul_cycle, hc, Matrix.one_mul]
  | @alice a b a' h z K hK next ih =>
    change (∑ j, (next j).apply (∑ k, (K j k ⊗ₖ 1) * ρ *
      (K j k ⊗ₖ 1).conjTranspose)).trace = ρ.trace
    rw [Matrix.trace_sum]
    simp_rw [ih]
    have ht := finiteKrausApply_trace
      (fun jk : Fin h × Fin z => K jk.1 jk.2 ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))
      (by simpa only [Fintype.sum_prod_type] using alice_joint_complete K hK) ρ
    simpa only [finiteKrausApply, Fintype.sum_prod_type, Matrix.trace_sum] using ht
  | @bob a b b' h z K hK next ih =>
    change (∑ j, (next j).apply (∑ k, (1 ⊗ₖ K j k) * ρ *
      (1 ⊗ₖ K j k).conjTranspose)).trace = ρ.trace
    rw [Matrix.trace_sum]
    simp_rw [ih]
    have ht := finiteKrausApply_trace
      (fun jk : Fin h × Fin z => (1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K jk.1 jk.2)
      (by simpa only [Fintype.sum_prod_type] using bob_joint_complete K hK) ρ
    simpa only [finiteKrausApply, Fintype.sum_prod_type, Matrix.trace_sum] using ht

theorem apply_add {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (ρ σ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    T.apply (ρ + σ) = T.apply ρ + T.apply σ := by
  induction T with
  | terminal LA LB hLA hLB =>
    simp only [apply, Matrix.mul_add, Matrix.add_mul]
  | alice K hK next ih =>
    simp only [apply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib, ih]
  | bob K hK next ih =>
    simp only [apply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib, ih]

theorem apply_smul {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (z : ℂ) (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    T.apply (z • ρ) = z • T.apply ρ := by
  induction T with
  | terminal LA LB hLA hLB =>
    simp only [apply, Matrix.mul_smul, Matrix.smul_mul]
  | alice K hK next ih =>
    simp only [apply, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum, ih]
  | bob K hK next ih =>
    simp only [apply, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum, ih]

def toLinearMap {c d a b : ℕ} (T : FiniteLocalProtocol c d a b) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ →ₗ[ℂ]
      Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ where
  toFun := T.apply
  map_add' := apply_add T
  map_smul' := apply_smul T

theorem apply_sum {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    {J : Type*} (s : Finset J)
    (ρ : J → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    T.apply (∑ j ∈ s, ρ j) = ∑ j ∈ s, T.apply (ρ j) :=
  map_sum T.toLinearMap ρ s

theorem alice_step_probability_mass {a b a' h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin a') (Fin a) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1)
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hρ : QuantumProver.QuantumEntropy.IsDensity ρ) :
    (∑ j, ∑ k, QuantumProver.LocalInstrumentMarginals.branchProbability (K j k) ρ) = 1 := by
  have hc : (∑ jk : Fin h × Fin z, (K jk.1 jk.2).conjTranspose * K jk.1 jk.2) = 1 := by
    simpa only [Fintype.sum_prod_type] using hK
  simpa only [Fintype.sum_prod_type] using
    QuantumProver.LocalInstrumentMarginals.sum_branchProbabilities_eq_one
      (fun jk : Fin h × Fin z => K jk.1 jk.2) hc hρ

theorem alice_step_weighted_untouchedMarginal {a b a' h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin a') (Fin a) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1)
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hρ : ρ.PosSemidef) :
    (∑ jk : Fin h × Fin z,
      QuantumProver.LocalInstrumentMarginals.branchProbability (K jk.1 jk.2) ρ •
        QuantumProver.LocalInstrumentMarginals.normalizedUntouchedMarginal
          (fun uv : Fin h × Fin z => K uv.1 uv.2) ρ jk) =
      QuantumProver.QuantumEntropy.partialTrace_left ρ := by
  have hc : (∑ jk : Fin h × Fin z, (K jk.1 jk.2).conjTranspose * K jk.1 jk.2) = 1 := by
    simpa only [Fintype.sum_prod_type] using hK
  exact QuantumProver.LocalInstrumentMarginals.weighted_normalizedUntouchedMarginals
    (fun jk : Fin h × Fin z => K jk.1 jk.2) hc hρ

theorem untouchedMarginal_swap {a b : ℕ}
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    QuantumProver.QuantumEntropy.partialTrace_left
      (ρ.submatrix (Equiv.prodComm (Fin b) (Fin a)) (Equiv.prodComm (Fin b) (Fin a))) =
      QuantumProver.QuantumEntropy.partialTrace_right ρ := by
  ext i j
  rfl

end FiniteLocalProtocol

end QuantumProver.WernerEndpoint.OperationalEndpointCost

namespace QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol

open scoped BigOperators Kronecker

@[reducible] def leafIndex {c d a b : ℕ} (T : FiniteLocalProtocol c d a b) : Type :=
  match T with
  | .terminal _ _ _ _ => Unit
  | @FiniteLocalProtocol.alice _ _ _ _ _ h z _ _ next =>
      Σ j : Fin h, Fin z × leafIndex (next j)
  | @FiniteLocalProtocol.bob _ _ _ _ _ h z _ _ next =>
      Σ j : Fin h, Fin z × leafIndex (next j)

instance leafFintype {c d a b : ℕ} (T : FiniteLocalProtocol c d a b) :
    Fintype (leafIndex T) := by
  induction T with
  | terminal LA LB hLA hLB => change Fintype Unit; infer_instance
  | @alice a b a' h z K hK next ih =>
    change Fintype (Σ j : Fin h, Fin z × leafIndex (next j))
    letI (j : Fin h) : Fintype (leafIndex (next j)) := ih j
    infer_instance
  | @bob a b b' h z K hK next ih =>
    change Fintype (Σ j : Fin h, Fin z × leafIndex (next j))
    letI (j : Fin h) : Fintype (leafIndex (next j)) := ih j
    infer_instance

def leafAlice {c d a b : ℕ} (T : FiniteLocalProtocol c d a b) :
    leafIndex T → Matrix (Fin c) (Fin a) ℂ :=
  match T with
  | .terminal LA _ _ _ => fun _ => LA
  | .alice K _ next => fun u => leafAlice (next u.1) u.2.2 * K u.1 u.2.1
  | .bob _ _ next => fun u => leafAlice (next u.1) u.2.2

def leafBob {c d a b : ℕ} (T : FiniteLocalProtocol c d a b) :
    leafIndex T → Matrix (Fin d) (Fin b) ℂ :=
  match T with
  | .terminal _ LB _ _ => fun _ => LB
  | .alice _ _ next => fun u => leafBob (next u.1) u.2.2
  | .bob K _ next => fun u => leafBob (next u.1) u.2.2 * K u.1 u.2.1

def leafKraus {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (u : leafIndex T) : Matrix (Fin c × Fin d) (Fin a × Fin b) ℂ :=
  leafAlice T u ⊗ₖ leafBob T u

theorem leafKraus_alice {c d a b a' h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin a') (Fin a) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1)
    (next : Fin h → FiniteLocalProtocol c d a' b)
    (j : Fin h) (k : Fin z) (u : leafIndex (next j)) :
    leafKraus (.alice K hK next) ⟨j, k, u⟩ =
      leafKraus (next j) u * (K j k ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) := by
  change (leafAlice (next j) u * K j k) ⊗ₖ leafBob (next j) u =
    (leafAlice (next j) u ⊗ₖ leafBob (next j) u) * (K j k ⊗ₖ 1)
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]

theorem leafKraus_bob {c d a b b' h z : ℕ}
    (K : Fin h → Fin z → Matrix (Fin b') (Fin b) ℂ)
    (hK : ∑ j, ∑ k, (K j k).conjTranspose * K j k = 1)
    (next : Fin h → FiniteLocalProtocol c d a b')
    (j : Fin h) (k : Fin z) (u : leafIndex (next j)) :
    leafKraus (.bob K hK next) ⟨j, k, u⟩ =
      leafKraus (next j) u * ((1 : Matrix (Fin a) (Fin a) ℂ) ⊗ₖ K j k) := by
  change leafAlice (next j) u ⊗ₖ (leafBob (next j) u * K j k) =
    (leafAlice (next j) u ⊗ₖ leafBob (next j) u) * (1 ⊗ₖ K j k)
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]

private theorem composed_gram_sum {J I M O : Type*}
    [Fintype J] [Fintype I] [Fintype M] [Fintype O] [DecidableEq M]
    (L : J → Matrix O M ℂ) (S : Matrix M I ℂ)
    (hL : ∑ u, (L u).conjTranspose * L u = 1) :
    (∑ u, (L u * S).conjTranspose * (L u * S)) = S.conjTranspose * S := by
  calc
    _ = S.conjTranspose * (∑ u, (L u).conjTranspose * L u) * S := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul,
        Matrix.mul_assoc]
    _ = _ := by rw [hL, Matrix.mul_one]

theorem leafKraus_complete {c d a b : ℕ} (T : FiniteLocalProtocol c d a b) :
    (∑ u : leafIndex T, (leafKraus T u).conjTranspose * leafKraus T u) = 1 := by
  induction T with
  | terminal LA LB hLA hLB =>
    simp only [leafIndex, leafKraus, leafAlice, leafBob, Fintype.sum_unique,
      Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hLA, hLB, Matrix.one_kronecker_one]
  | @alice a b a' h z K hK next ih =>
    change (∑ u : (Σ j : Fin h, Fin z × leafIndex (next j)),
      (leafKraus (.alice K hK next) u).conjTranspose *
        leafKraus (.alice K hK next) u) = 1
    simp only [Fintype.sum_sigma, Fintype.sum_prod_type, leafKraus_alice]
    simp_rw [composed_gram_sum (leafKraus (next _)) _ (ih _)]
    exact alice_joint_complete K hK
  | @bob a b b' h z K hK next ih =>
    change (∑ u : (Σ j : Fin h, Fin z × leafIndex (next j)),
      (leafKraus (.bob K hK next) u).conjTranspose *
        leafKraus (.bob K hK next) u) = 1
    simp only [Fintype.sum_sigma, Fintype.sum_prod_type, leafKraus_bob]
    simp_rw [composed_gram_sum (leafKraus (next _)) _ (ih _)]
    exact bob_joint_complete K hK

theorem apply_eq_leafKraus {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    T.apply ρ = ∑ u : leafIndex T,
      leafKraus T u * ρ * (leafKraus T u).conjTranspose := by
  induction T with
  | terminal LA LB hLA hLB =>
    simp only [apply, leafIndex, leafKraus, leafAlice, leafBob, Fintype.sum_unique]
  | @alice a b a' h z K hK next ih =>
    simp only [apply, leafIndex, Fintype.sum_sigma, Fintype.sum_prod_type,
      leafKraus_alice]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih j]
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro u _
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  | @bob a b b' h z K hK next ih =>
    simp only [apply, leafIndex, Fintype.sum_sigma, Fintype.sum_prod_type,
      leafKraus_bob]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih j]
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro u _
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem apply_pureDensity_leafKraus {c d a b : ℕ}
    (T : FiniteLocalProtocol c d a b) (ψ : Fin a × Fin b → ℂ) :
    T.apply (pureDensity ψ) =
      ∑ u : leafIndex T, pureDensity ((leafKraus T u).mulVec ψ) := by
  rw [apply_eq_leafKraus]
  apply Finset.sum_congr rfl
  intro u _
  exact sandwich_crossDensity (leafKraus T u) ψ ψ

end QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol

namespace QuantumProver.WernerEndpoint.OperationalEndpointCost.OneWayLocalInstrument

open scoped BigOperators Kronecker

def reindex {H H' A₀ B₀ A₁ B₁ : Type*}
    [Fintype H] [Fintype H'] [Fintype A₀] [Fintype B₀]
    [Fintype A₁] [Fintype B₁] [DecidableEq A₀] [DecidableEq B₀]
    (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁) (e : H' ≃ H) :
    OneWayLocalInstrument H' A₀ B₀ A₁ B₁ where
  alice := fun j => I.alice (e j)
  bob := fun j => I.bob (e j)
  alice_complete := by
    rw [e.sum_comp (fun h => (I.alice h).conjTranspose * I.alice h)]
    exact I.alice_complete
  bob_isometry := fun j => I.bob_isometry (e j)

theorem reindex_apply {H H' A₀ B₀ A₁ B₁ : Type*}
    [Fintype H] [Fintype H'] [Fintype A₀] [Fintype B₀]
    [Fintype A₁] [Fintype B₁] [DecidableEq A₀] [DecidableEq B₀]
    (I : OneWayLocalInstrument H A₀ B₀ A₁ B₁) (e : H' ≃ H)
    (ρ : Matrix (A₀ × B₀) (A₀ × B₀) ℂ) :
    (I.reindex e).apply ρ = I.apply ρ := by
  exact e.sum_comp (fun h => I.branch h * ρ * (I.branch h).conjTranspose)

def toFiniteLocalProtocol {h a b c d : ℕ}
    (I : OneWayLocalInstrument (Fin h) (Fin a) (Fin b) (Fin c) (Fin d)) :
    FiniteLocalProtocol c d a b :=
  .alice (fun j (_ : Fin 1) => I.alice j)
    (by simpa only [Fin.sum_univ_one] using I.alice_complete)
    (fun j => .terminal (1 : Matrix (Fin c) (Fin c) ℂ) (I.bob j)
      (by simp) (I.bob_isometry j))

theorem toFiniteLocalProtocol_apply {h a b c d : ℕ}
    (I : OneWayLocalInstrument (Fin h) (Fin a) (Fin b) (Fin c) (Fin d))
    (ρ : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    I.toFiniteLocalProtocol.apply ρ = I.apply ρ := by
  simp only [toFiniteLocalProtocol, FiniteLocalProtocol.apply, Fin.sum_univ_one,
    OneWayLocalInstrument.apply]
  apply Finset.sum_congr rfl
  intro j _
  have hk : ((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ I.bob j) *
      (I.alice j ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) = I.branch j := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    rfl
  calc
    _ = (((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ I.bob j) *
        (I.alice j ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))) * ρ *
        (((1 : Matrix (Fin c) (Fin c) ℂ) ⊗ₖ I.bob j) *
        (I.alice j ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hk]

end QuantumProver.WernerEndpoint.OperationalEndpointCost.OneWayLocalInstrument

namespace QuantumProver.WernerEndpoint.OperationalEndpointCost

open scoped Kronecker

def uniformEdgeFiniteProtocol (d : ℕ) (hd : 2 ≤ d) : FiniteLocalProtocol d d 2 2 :=
  ((uniformEdgeInstrument d hd).reindex (Fintype.equivFin (Edge d)).symm).toFiniteLocalProtocol

theorem uniformEdgeFiniteProtocol_apply (d : ℕ) (hd : 2 ≤ d)
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (uniformEdgeFiniteProtocol d hd).apply ρ = (uniformEdgeInstrument d hd).apply ρ := by
  unfold uniformEdgeFiniteProtocol
  rw [OneWayLocalInstrument.toFiniteLocalProtocol_apply, OneWayLocalInstrument.reindex_apply]

theorem uniformEdgeFiniteProtocol_bell_output (d : ℕ) (hd : 2 ≤ d) :
    (uniformEdgeFiniteProtocol d hd).apply (pureDensity bellVector) =
      (Fintype.card (Edge d) : ℂ)⁻¹ • wedgeProjector d := by
  rw [uniformEdgeFiniteProtocol_apply, uniformEdgeInstrument_bell_output]

theorem exists_finiteLocalProtocol_endpoint_preparation (d : ℕ) (hd : 2 ≤ d) :
    ∃ T : FiniteLocalProtocol d d 2 2,
      T.apply (pureDensity bellVector) =
        (Fintype.card (Edge d) : ℂ)⁻¹ • wedgeProjector d :=
  ⟨uniformEdgeFiniteProtocol d hd, uniformEdgeFiniteProtocol_bell_output d hd⟩

end QuantumProver.WernerEndpoint.OperationalEndpointCost

namespace QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol
open scoped BigOperators

def leafProbability {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (ψ : Fin a × Fin b → ℂ) (u : leafIndex T) : ℝ :=
  vectorNormSq ((leafKraus T u).mulVec ψ)

theorem leafProbability_nonneg {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (ψ : Fin a × Fin b → ℂ) (u : leafIndex T) : 0 ≤ leafProbability T ψ u :=
  matrix_vectorNormSq_nonneg _

theorem sum_leafProbability {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (ψ : Fin a × Fin b → ℂ) :
    (∑ u : leafIndex T, leafProbability T ψ u) = vectorNormSq ψ := by
  have ht := congrArg Complex.re (T.apply_trace (pureDensity ψ))
  rw [apply_pureDensity_leafKraus, Matrix.trace_sum, Complex.re_sum] at ht
  simpa only [leafProbability, pureDensity_trace, Complex.ofReal_re] using ht

theorem sum_leafProbability_eq_one {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (ψ : Fin a × Fin b → ℂ) (hψ : vectorNormSq ψ = 1) :
    (∑ u : leafIndex T, leafProbability T ψ u) = 1 := by
  rw [sum_leafProbability, hψ]

def normalizedLeafVector {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (ψ : Fin a × Fin b → ℂ) (fallback : Fin c × Fin d → ℂ) (u : leafIndex T) :
    Fin c × Fin d → ℂ :=
  if leafProbability T ψ u = 0 then fallback else
    (((Real.sqrt (leafProbability T ψ u))⁻¹ : ℝ) : ℂ) • (leafKraus T u).mulVec ψ

private theorem inverse_leaf_normSq {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (ψ : Fin a × Fin b → ℂ) (u : leafIndex T) :
    Complex.normSq (((Real.sqrt (leafProbability T ψ u))⁻¹ : ℝ) : ℂ) =
      (leafProbability T ψ u)⁻¹ := by
  simp only [Complex.normSq_ofReal, ← sq, inv_pow]
  rw [Real.sq_sqrt (leafProbability_nonneg T ψ u)]

theorem normalizedLeafVector_normSq {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (ψ : Fin a × Fin b → ℂ) (fallback : Fin c × Fin d → ℂ)
    (hf : vectorNormSq fallback = 1) (u : leafIndex T) :
    vectorNormSq (normalizedLeafVector T ψ fallback u) = 1 := by
  by_cases hz : leafProbability T ψ u = 0
  · simp only [normalizedLeafVector, if_pos hz, hf]
  · rw [normalizedLeafVector, if_neg hz, matrix_vectorNormSq_scalar,
      inverse_leaf_normSq]
    exact inv_mul_cancel₀ hz

theorem weighted_normalizedLeafDensity {c d a b : ℕ}
    (T : FiniteLocalProtocol c d a b) (ψ : Fin a × Fin b → ℂ)
    (fallback : Fin c × Fin d → ℂ) (u : leafIndex T) :
    (leafProbability T ψ u : ℂ) • pureDensity (normalizedLeafVector T ψ fallback u) =
      pureDensity ((leafKraus T u).mulVec ψ) := by
  by_cases hz : leafProbability T ψ u = 0
  · have hv : (leafKraus T u).mulVec ψ = 0 := matrix_vectorNormSq_eq_zero _ hz
    rw [hz, Complex.ofReal_zero, zero_smul, hv]
    ext i j
    simp [pureDensity, crossDensity]
  · rw [normalizedLeafVector, if_neg hz, matrix_pureDensity_scalar,
      inverse_leaf_normSq, smul_smul]
    have hp : (leafProbability T ψ u : ℂ) ≠ 0 := by exact_mod_cast hz
    rw [Complex.ofReal_inv, mul_inv_cancel₀ hp, one_smul]

theorem apply_pureDensity_weighted_normalized_leaves {c d a b : ℕ}
    (T : FiniteLocalProtocol c d a b) (ψ : Fin a × Fin b → ℂ)
    (fallback : Fin c × Fin d → ℂ) :
    T.apply (pureDensity ψ) = ∑ u : leafIndex T,
      (leafProbability T ψ u : ℂ) • pureDensity (normalizedLeafVector T ψ fallback u) := by
  rw [apply_pureDensity_leafKraus]
  apply Finset.sum_congr rfl
  intro u _
  exact (weighted_normalizedLeafDensity T ψ fallback u).symm

def outputPureEnsemble {c d a b : ℕ} (T : FiniteLocalProtocol c d a b)
    (ψ : Fin a × Fin b → ℂ) (hψ : vectorNormSq ψ = 1)
    (fallback : Fin c × Fin d → ℂ) (hf : vectorNormSq fallback = 1) :
    AntisymmetricEnsembleCost.FinitePureEnsemble (T.apply (pureDensity ψ)) where
  count := Fintype.card (leafIndex T)
  weight := fun j => leafProbability T ψ ((Fintype.equivFin (leafIndex T)).symm j)
  weight_nonneg := fun j => leafProbability_nonneg T ψ _
  weight_sum := by
    rw [(Fintype.equivFin (leafIndex T)).symm.sum_comp]
    exact sum_leafProbability_eq_one T ψ hψ
  vector := fun j => normalizedLeafVector T ψ fallback
    ((Fintype.equivFin (leafIndex T)).symm j)
  normalized := fun j => normalizedLeafVector_normSq T ψ fallback hf _
  barycenter := by
    have hs := (Fintype.equivFin (leafIndex T)).symm.sum_comp
      (fun u => (leafProbability T ψ u : ℂ) •
        pureDensity (normalizedLeafVector T ψ fallback u))
    exact (apply_pureDensity_weighted_normalized_leaves T ψ fallback).trans hs.symm

end QuantumProver.WernerEndpoint.OperationalEndpointCost.FiniteLocalProtocol
